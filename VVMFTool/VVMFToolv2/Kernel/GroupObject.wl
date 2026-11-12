(*
    :Title: Mutable finite-group registry
    :Context: VVMFTool`Private`
    :Summary: Publish verified group data behind shared live handles and atomic revisions.
    :Responsibilities: Validation receipts, property access, snapshots and controlled updates.
    :Dependencies: ResultValidation.wl; Configuration.wl.
    :See Also: VVMFArch/step1Plan.md; Schemas/GroupResult.md.
*)

(* Package-owned registries survive loader retries. Receipts are kernel-local evidence
   references; portable files never create them. No object is allocated by reading JSON. *)
If[!AssociationQ[$GroupRegistry], $GroupRegistry = <||>];
If[!AssociationQ[$GroupValidationReceipts], $GroupValidationReceipts = <||>];

(* Decoded result fields and public read-only properties. Values are string-keyed;
   internal revision, ownership and computational caches are not public properties. *)
$GroupResultKeys = {"StateID", "GeneratorIdentity", "StateGeneration", "RequestID", "Operation",
    "Status", "Construction", "Generators", "Order", "CatalogueID", "CharacterData",
    "AvailableData", "Elements", "SubgroupData", "ModularAssignment", "Representations",
    "Producer", "Binding", "LastComputation"};
$GroupPublicProperties = {"InstanceID", "Name", "Construction", "Generators", "Order",
    "CatalogueID", "CharacterData", "ModularAssignment", "AvailableData", "Elements",
    "SubgroupData", "Representations", "IrrepOrder", "GAPCachePath", "GAPCacheMetadata",
    "LastComputation", "IrrepLabels", "ClassLabels", "ClassOrder", "CatalogueLabel", "TitleTeX"};
(* Registration counter: the order in which groups entered this kernel (instance suffixes, uxUpdatePlan.md 2.3). *)
If[!IntegerQ[$GroupRegistrationCounter], $GroupRegistrationCounter = 0];
$GroupReceiptKeys = DeleteCases[$GroupResultKeys, "LastComputation"];
(* The group's own verification status (its character table, methodOptionsPlan.md 2C.6) is an optional decoded field:
   absent means "Exact", so every existing receipt digest is unchanged; when present the receipt covers it (user
   decision 2026-10-13). *)
$GroupOptionalResultKeys = {"VerificationStatus"};
groupResultKeysQ[data_Association] := resultFieldsQ[KeyDrop[data, $GroupOptionalResultKeys], $GroupResultKeys] &&
    (!KeyExistsQ[data, "VerificationStatus"] || MemberQ[{"Numerical", "Unverified"}, data["VerificationStatus"]]);
groupResultKeysQ[_] := False;
$GroupImmutableKeys = {"StateID", "GeneratorIdentity", "Construction", "Generators",
    "Order", "CatalogueID"};

(* Derived representation caches: recomputable, outside the receipt, digest and identity bindings. *)
$RepresentationCacheKinds = {"ElementMatrices", "Unitarity", "Decompositions", "DerivedIntermediates"};

(*
    Summary: An empty derived representation cache at an eviction epoch.
    Parameters: epoch — nonnegative integer.
    Options/defaults: epoch 0.
    Returns: <|"Epoch" -> epoch, "Entries" -> <|kind -> <||>|>|> for every cache kind.
    Effects: Pure.
    Failures: None.
    Example: emptyRepresentationCache[][["Epoch"]] is 0.
    See also: representationCacheQ; CleanRepresentationCache.
*)
emptyRepresentationCache[epoch_Integer : 0] := <|"Epoch" -> epoch,
    "Entries" -> AssociationThread[$RepresentationCacheKinds, ConstantArray[<||>, Length[$RepresentationCacheKinds]]]|>;

(*
    Summary: An empty Clebsch-Gordan store at an eviction epoch.
    Parameters: epoch — nonnegative integer.
    Options/defaults: epoch 0.
    Returns: <|"Epoch" -> epoch, "Entries" -> <||>|>.
    Effects: Pure.
    Failures: None.
    Example: emptyCGCache[][["Entries"]] is <||>.
    Remarks: The mathematical CG store (step4Status.md D-S4-2) is a non-receipt field like RepresentationCache:
        entries are validated target bundles keyed by cgCacheKey. Publication is one atomic commit (D-S4-8), so the
        store needs no acceptance leases.
    See also: cgCacheQ; CleanCGCache.
*)
emptyCGCache[epoch_Integer : 0] := <|"Epoch" -> epoch, "Entries" -> <||>|>;

(*
    Summary: Test the shape of a Clebsch-Gordan store.
    Parameters: cache — any value.
    Options/defaults: None.
    Returns: Boolean.
    Effects: Pure.
    Failures: None.
    Example: cgCacheQ[emptyCGCache[2]] is True.
    See also: emptyCGCache; commitGroup.
*)
cgCacheQ[cache_] := AssociationQ[cache] && Sort[Keys[cache]] === {"Entries", "Epoch"} &&
    IntegerQ[cache["Epoch"]] && cache["Epoch"] >= 0 && AssociationQ[cache["Entries"]];

(*
    Summary: Test the shape of a derived representation cache.
    Parameters: cache — any value.
    Options/defaults: None.
    Returns: Boolean.
    Effects: Pure.
    Failures: None.
    Example: representationCacheQ[emptyRepresentationCache[3]] is True.
    See also: emptyRepresentationCache; commitGroup.
*)
representationCacheQ[cache_] := AssociationQ[cache] && Sort[Keys[cache]] === {"Entries", "Epoch"} &&
    IntegerQ[cache["Epoch"]] && cache["Epoch"] >= 0 && AssociationQ[cache["Entries"]] &&
    Sort[Keys[cache["Entries"]]] === Sort[$RepresentationCacheKinds] && AllTrue[Values[cache["Entries"]], AssociationQ];

(*
    Summary: Test a presentation order of irreducible characters.
    Parameters: order — any value; characters — decoded CharacterData.
    Options/defaults: None.
    Returns: Boolean.
    Effects: Pure.
    Failures: Duplicates, foreign or missing IDs and malformed data return False.
    Example: irrepOrderQ[Reverse[ids], characters] is True for ids = characters["IrrepIDs"].
    See also: commitGroup; newGroup.
*)
irrepOrderQ[order_, characters_Association] := ListQ[order] && DuplicateFreeQ[order] &&
    ListQ[Lookup[characters, "IrrepIDs", None]] && Sort[order] === Sort[characters["IrrepIDs"]];
irrepOrderQ[___] := False;

(*
    Summary: Fingerprint decoded data whose acceptance requires mathematical provenance.
    Parameters: data — decoded result or registry snapshot with all receipt fields.
    Options/defaults: None.
    Returns: SHA256 integer digest, or InvalidGroupData Failure.
    Effects: Pure; excludes live metadata and LastComputation diagnostics.
    Failures: Missing decoded fields are rejected.
    Example: changing a character value changes the digest; changing only Name does not.
    Remarks: A digest detects change; it never establishes characterhood or producer trust.
    See also: recordValidatedGroupResult; groupValidationReceiptQ.
*)
groupResultDigest[data_Association] := If[ContainsAll[Keys[data], $GroupReceiptKeys],
    Hash[KeyTake[data, Join[$GroupReceiptKeys, $GroupOptionalResultKeys]], "SHA256"],
    makeFailure["InvalidGroupData", "Required group-result fields are missing."]
];
groupResultDigest[___] := makeFailure["InvalidGroupData", "Expected decoded group data."];

(*
    Summary: Record the caller's independently established group-result provenance.
    Parameters: data — complete decoded result from validateGroupResult; evidence —
        association with Source equal to OwnedWorker, RegisteredExport or GroupCorrespondence,
        and nonempty Reference identifying the validated job/artifact/correspondence.
    Options/defaults: None.
    Returns: Fresh opaque receipt string, or Failure.
    Effects: Adds one private kernel-local receipt without allocating a Group.
    Failures: Incomplete data, malformed evidence or missing result fields are rejected.
    Example: the coordinator records an OwnedWorker receipt only after the matching
        result, restored workspace and published manifest have all passed verification.
    Remarks: This trusted internal boundary does not itself prove the evidence.
        The coordinator/import validator must finish the indicated verification first.
        Never call it from an unvalidated portable field or merely after arithmetic checks.
    See also: groupValidationReceiptQ; newGroup; acceptCandidate in step1Plan.md.
*)
recordValidatedGroupResult[data_Association, evidence_Association] := Module[{digest, receipt},
    If[!groupResultKeysQ[data] || Lookup[data, "Status", None] =!= "Complete" ||
        !AssociationQ[Lookup[data, "CharacterData", None]] ||
        (* "Verification" (the build or import level, methodOptionsPlan.md 2C.5) is optional *)
        !resultFieldsQ[KeyDrop[evidence, "Verification"], {"Source", "Reference"}] ||
        (KeyExistsQ[evidence, "Verification"] && !verificationStatusQ[evidence["Verification"]]) ||
        (* "UnverifiedImport": ImportGroupData at "Numerical" or None of an unregistered file (2C.5), with the level in
           Evidence "Verification" *)
        !MemberQ[{"OwnedWorker", "RegisteredExport", "GroupCorrespondence", "UnverifiedImport"}, evidence["Source"]] ||
        (evidence["Source"] === "UnverifiedImport" && !MemberQ[{"Numerical", "Unverified"}, Lookup[evidence, "Verification", None]]) ||
        !StringQ[evidence["Reference"]] || StringLength[evidence["Reference"]] === 0,
        Return[makeFailure["UnboundGroupData", "Complete data and independently verified provenance are required."]]
    ];
    digest = groupResultDigest[data];
    If[FailureQ[digest], Return[digest]];
    receipt = CreateUUID["group-validation-"];
    AssociateTo[$GroupValidationReceipts, receipt -> <|"Digest" -> digest, "Evidence" -> evidence|>];
    receipt
];
recordValidatedGroupResult[___] := makeFailure["UnboundGroupData", "Expected complete data and provenance."];

(*
    Summary: Match decoded data to a previously issued kernel-local validation receipt.
    Parameters: data — decoded group data; receipt — opaque receipt string.
    Options/defaults: None.
    Returns: Boolean.
    Effects: Pure; receipts are reusable for fresh handles of the same mathematical data.
    Failures: Unknown/foreign receipts, incomplete data and modified values return False.
    Example: copying a receipt into a modified C5 table does not validate that table.
    See also: groupResultDigest; recordValidatedGroupResult.
*)
groupValidationReceiptQ[data_Association, receipt_String] := Module[{record, digest},
    record = Lookup[$GroupValidationReceipts, receipt, Missing["UnknownReceipt"]];
    If[MissingQ[record] || Lookup[data, "Status", None] =!= "Complete", Return[False]];
    digest = groupResultDigest[data];
    !FailureQ[digest] && digest === record["Digest"]
];
groupValidationReceiptQ[___] := False;

(*
    Summary: Allocate a fresh shared Group handle from independently accepted data.
    Parameters: data — complete decoded result; receipt — matching private validation receipt;
        name — display string or Automatic.
    Options/defaults: name defaults to Automatic, displayed as "Group of order n".
    Returns: Group[UUID], or UnboundGroupData/InvalidGroupName Failure.
    Effects: Adds one registry entry with revision zero, immutable identity history, empty derived
        caches (including the representation cache at epoch 0) and IrrepOrder seeded from the character
        table's canonical irrep IDs.
    Failures: Does not allocate on invalid data, provenance or display name.
    Example: two calls with the same accepted data create distinct live handles with
        the same mathematical identities and character table.
    See also: groupData; commitGroup; recordValidatedGroupResult.
*)
newGroup[data_Association, receipt_String, name_ : Automatic] := Module[{id, state, bindings},
    If[!groupResultKeysQ[data] || !groupValidationReceiptQ[data, receipt],
        Return[makeFailure["UnboundGroupData", "Group publication requires independently accepted complete data."]]];
    If[name =!= Automatic && !StringQ[name],
        Return[makeFailure["InvalidGroupName", "The display name must be a string or Automatic."]]];
    bindings = groupIdentityBindings[data]; If[FailureQ[bindings], Return[bindings]];
    id = CreateUUID["group-"];
    state = Join[data, <|"InstanceID" -> id,
        "Name" -> If[name === Automatic, "Group of order " <> ToString[data["Order"]], name],
        "GAPCachePath" -> Missing["NotStored"], "GAPCacheMetadata" -> Missing["NotStored"],
        "IrrepOrder" -> data["CharacterData"]["IrrepIDs"], "RepresentationCache" -> emptyRepresentationCache[],
        (* presentation data (uxUpdatePlan.md 1.4): labels, class order and names, catalogue label, TeX title *)
        "IrrepLabels" -> <||>, "ClassLabels" -> <||>, "ClassOrder" -> data["CharacterData"]["ClassIDs"],
        "CatalogueLabel" -> None, "TitleTeX" -> None, "RegistrationIndex" -> ++$GroupRegistrationCounter, "LibrarySource" -> None,
        "CGCache" -> emptyCGCache[],
        "Revision" -> 0, "ActiveOperation" -> None, "Models" -> <||>,
        "CacheDependencies" -> <||>, "ValidationReceipt" -> receipt,
        "NativeEnvelope" -> Missing["NotStored"], "SuccessfulAttempts" -> <||>,
        "IdentityBindings" -> bindings, "SubgroupClassWitnesses" -> subgroupClassWitnesses[data]|>];
    AssociateTo[$GroupRegistry, id -> state];
    Group[id]
];
newGroup[___] := makeFailure["UnboundGroupData", "Expected accepted group data and a validation receipt."];

(*
    Summary: Read a value snapshot of a live group registry entry.
    Parameters: group — Group[id_String].
    Options/defaults: None.
    Returns: Association including private state, or UnknownGroup/InvalidGroup Failure.
    Effects: Pure; editing the returned association does not mutate the registry.
    Failures: Unknown handles and malformed Group expressions fail explicitly.
    Example: groupData[group]["Revision"] is the expected revision for an atomic update.
    See also: groupProperty; commitGroup.
*)
groupData[Group[id_String]] := Lookup[$GroupRegistry, id,
    makeFailure["UnknownGroup", "This group handle is not registered in the current kernel.",
        <|"InstanceID" -> id|>]];
groupData[___] := makeFailure["InvalidGroup", "Expected a valid Group handle."];

(*
    Summary: Read a declared public property without starting computations.
    Parameters: group — a live Group handle; property — string key.
    Options/defaults: None.
    Returns: Stored value, Missing["UnknownProperty", key], or Failure for an invalid handle.
    Effects: Pure; lookup never starts GAP or populates missing data.
    Failures: Invalid handles take precedence over unknown-property diagnostics.
    Example: groupProperty[group, "Elements"] is Missing["NotComputed"] before computation.
    See also: Group; groupData; NumberOfRep.
*)
groupProperty[group_Group, property_String] := Module[{data = groupData[group]},
    Which[FailureQ[data], data,
        (* labels are presented by irrep index and as plain text (uxUpdatePlan.md 1.4) *)
        property === "IrrepLabels", Association[KeyValueMap[First[FirstPosition[data["IrrepOrder"], #1, {0}, {1}]] -> labelPlainText[#2] &, data["IrrepLabels"]]] // KeySort,
        property === "ClassLabels", Association[KeyValueMap[First[FirstPosition[data["ClassOrder"], #1, {0}, {1}]] -> labelPlainText[#2["Name"]] &, data["ClassLabels"]]] // KeySort,
        MemberQ[$GroupPublicProperties, property], data[property],
        True, Missing["UnknownProperty", property]]
];
groupProperty[___] := makeFailure["InvalidProperty", "Expected a group and a string property."];

(*
    Summary: Shared read-only property method for finite-group object handles.
    Status: Alpha.
    Fields: Group[id_String] references one kernel registry entry; id is a live UUID,
        independent of the stored mathematical and catalogue identities.
    Defaults: None.
    Returns: g[property_String] delegates to groupProperty; other keys fail explicitly.
    Identity/mutation: Assignment copies a handle. Validated operations update shared
        registry state; direct property definitions are prevented by protecting Group.
    Example: h = g; a successful enrichment of g is visible through h.
    See also: newGroup; groupProperty; commitGroup.
*)
Unprotect[Group];
Group[id_String][property_String] := groupProperty[Group[id], property];
Group[arguments___][property_] := makeFailure["InvalidGroupProperty",
    "A group property requires Group[id_String] and a string key."];

(*
    Summary: Atomically apply a validated patch to the expected live object revision.
    Parameters: group — registered handle; expectedRevision — nonnegative integer;
        patch — changed fields, optionally with a matching ValidationReceipt.
    Options/defaults: None. No omitted field is erased.
    Returns: The same Group on success, or Failure with accepted state unchanged.
    Effects: Replaces the registry entry once, retains previous identity bindings and advances Revision by one.
    Failures: Stale revision, unknown/read-only fields, changed immutable identities,
        invalid metadata, an IrrepOrder that is not a permutation of the irrep IDs,
        or mathematical changes without a matching receipt.
    Example: commitGroup[g, groupData[g]["Revision"], <|"Name" -> "Example"|>] returns g.
    Remarks: External jobs must publish their coherent checkpoint before this call.
        This primitive does no I/O and cannot certify a checkpoint path on its own.
        Complete character data are immutable, including their canonical row/ID order.
        Presentation order is the separate IrrepOrder, which is not mathematical data: it needs
        no receipt or generation and is outside the digest and identity bindings; so are the derived
        RepresentationCache and the CG store CGCache, whose eviction epochs never decrease.
    See also: groupData; groupValidationReceiptQ; acceptCandidate in step1Plan.md.
*)
commitGroup[group_Group, expectedRevision_Integer, patch_Association] := Module[
    {accepted, candidate, allowed, receiptChanged, bindings},
    accepted = groupData[group];
    If[FailureQ[accepted], Return[accepted]];
    If[expectedRevision < 0 || accepted["Revision"] =!= expectedRevision,
        Return[makeFailure["StateConflict", "The group changed before this update could commit."]]];
    allowed = Join[Complement[Keys[accepted], Join[$GroupImmutableKeys,
        {"InstanceID", "Revision", "IdentityBindings", "SubgroupClassWitnesses"}]], $GroupOptionalResultKeys];
    If[Complement[Keys[patch], allowed] =!= {},
        Return[makeFailure["InvalidGroupPatch", "The patch changes an immutable or unknown field."]]];
    candidate = Join[accepted, patch];
    (* the optional group status: "Exact" is its absence (a raised status removes the key, methodOptionsPlan.md 2C.6) *)
    If[Lookup[candidate, "VerificationStatus", None] === "Exact", KeyDropFrom[candidate, "VerificationStatus"]];
    If[!StringQ[candidate["Name"]] || !AssociationQ[candidate["LastComputation"]] ||
        !(candidate["GAPCachePath"] === Missing["NotStored"] ||
            absolutePathQ[candidate["GAPCachePath"]]) ||
        !(candidate["GAPCacheMetadata"] === Missing["NotStored"] ||
            AssociationQ[candidate["GAPCacheMetadata"]]) ||
        (MissingQ[candidate["GAPCachePath"]] =!= MissingQ[candidate["GAPCacheMetadata"]]) ||
        !AssociationQ[candidate["Models"]] || !AssociationQ[candidate["CacheDependencies"]] ||
        !AssociationQ[candidate["SuccessfulAttempts"]] ||
        !irrepOrderQ[candidate["IrrepOrder"], candidate["CharacterData"]] || !presentationPatchQ[candidate] ||
        !representationCacheQ[candidate["RepresentationCache"]] ||
        candidate["RepresentationCache"]["Epoch"] < accepted["RepresentationCache"]["Epoch"] ||
        !cgCacheQ[candidate["CGCache"]] || candidate["CGCache"]["Epoch"] < accepted["CGCache"]["Epoch"] ||
        !(candidate["ActiveOperation"] === None || StringQ[candidate["ActiveOperation"]]),
        Return[makeFailure["InvalidGroupPatch", "Invalid group metadata or internal state."]]];
    If[candidate["CharacterData"] =!= accepted["CharacterData"],
        Return[makeFailure["StateConflict", "Complete character data cannot change in this operation."]]];
    receiptChanged = KeyTake[candidate, Join[$GroupReceiptKeys, $GroupOptionalResultKeys]] =!= KeyTake[accepted, Join[$GroupReceiptKeys, $GroupOptionalResultKeys]];
    If[receiptChanged && (!groupValidationReceiptQ[candidate, candidate["ValidationReceipt"]] ||
        candidate["StateGeneration"] =!= accepted["StateGeneration"] + 1),
        Return[makeFailure["UnboundGroupData", "Changed mathematical data require a verified next generation."]]];
    If[!receiptChanged && candidate["ValidationReceipt"] =!= accepted["ValidationReceipt"],
        Return[makeFailure["InvalidGroupPatch", "An unchanged result cannot replace its validation receipt."]]];
    If[receiptChanged,
        bindings = groupIdentityBindings[candidate]; If[FailureQ[bindings], Return[bindings]];
        If[!compatibleIdentityBindingsQ[bindings, accepted["IdentityBindings"]],
            Return[makeFailure["StateConflict", "An update cannot reassign previously accepted mathematical identities."]]];
        candidate["IdentityBindings"] = Join[accepted["IdentityBindings"], bindings];
        candidate["SubgroupClassWitnesses"] = DeleteDuplicates[Join[accepted["SubgroupClassWitnesses"],
            subgroupClassWitnesses[candidate]]]];
    candidate["Revision"] = expectedRevision + 1;
    AssociateTo[$GroupRegistry, accepted["InstanceID"] -> candidate];
    group
];
commitGroup[___] := makeFailure["InvalidGroupPatch", "Expected a live group, revision and patch."];

(*
    Summary: Recover the inert native envelope matching an accepted group's validation receipt.
    Parameters: data — private group snapshot with NativeEnvelope and ValidationReceipt.
    Options/defaults: None.
    Returns: Exact JSON envelope, or UnboundGroupData Failure.
    Effects: Pure; validates schema and compares its decoded receipt digest with accepted data.
    Failures: Absent, altered, incomplete or unrelated envelopes cannot authorize reconstruction.
    Example: enrichment uses retained cyclotomic coefficients without guessing a number field.
    Remarks: The private receipt supplies provenance; an embedded JSON binding flag does not.
    See also: publishConstructedGroup; runGroupEnrichment; SaveGroupData.
*)
groupEnvelope[data_Association] := Module[{native, decoded},
    native = Lookup[data, "NativeEnvelope", None];
    If[!AssociationQ[native] || !groupValidationReceiptQ[data, Lookup[data, "ValidationReceipt", None]],
        Return[makeFailure["UnboundGroupData", "An accepted native envelope is required."]]];
    (* read at the group's own level (methodOptionsPlan.md 2C.6): the envelope's claims give that status (an unverified
       import stores weakened claims, unverifiedSnapshot), and variants are bounded by it where they are read *)
    decoded = Block[{$GroupAcceptanceLevel = groupStatusLevel[groupVerificationStatus[data]]}, validateGroupResult[native, KeyTake[native,
        {"requestID", "stateID", "generatorIdentity", "stateGeneration", "operation", "construction"}]]];
    If[FailureQ[decoded] || groupResultDigest[decoded] =!= groupResultDigest[data],
        makeFailure["UnboundGroupData", "The native envelope differs from the accepted group data."], native]
];
groupEnvelope[___] := makeFailure["UnboundGroupData", "Expected an accepted group snapshot."];

(*
    Summary: Compare all accepted group mathematics independently of computation bookkeeping.
    Parameters: candidate/accepted — independently verified decoded result or registry data.
    Options/defaults: Generation and every stored mathematical payload must match exactly.
    Returns: Boolean; absent fields or incomplete data return False.
    Effects: Pure; this predicate never establishes producer provenance by itself.
    Failures: Changed generators, classes, rows, embeddings or assignments return False.
    Example: a certified reconstruction may use a new request/producer while preserving the same state.
    See also: groupComputationSource; RestoreGAPState; groupResultDigest.
*)
sameGroupStateQ[candidate_Association, accepted_Association] := With[
    {keys = {"StateID", "GeneratorIdentity", "StateGeneration", "Status", "Construction", "Generators",
        "Order", "CatalogueID", "CharacterData", "AvailableData", "Elements", "SubgroupData",
        "ModularAssignment", "Representations"}},
    Lookup[candidate, "Status", None] === "Complete" && Lookup[accepted, "Status", None] === "Complete" &&
        ContainsAll[Keys[candidate], keys] && ContainsAll[Keys[accepted], keys] &&
        KeyTake[candidate, keys] === KeyTake[accepted, keys]
];
sameGroupStateQ[___] := False;

(*
    Summary: Count irreducible characters of an accepted finite group.
    Status: Alpha.
    Parameters: group — registered Group handle.
    Options/defaults: None.
    Returns: Positive integer count, or Failure for an invalid/unknown group.
    Effects: Pure; representation matrices and GAP are not needed.
    Failures: Invalid handles never produce a misleading zero.
    Example: NumberOfRep[g] is 5 for a character-only construction of A5.
    See also: Group; groupProperty.
*)
NumberOfRep[group_Group] := Module[{data = groupData[group]},
    If[FailureQ[data], data, Length[data["CharacterData"]["IrrepIDs"]]]
];
NumberOfRep[___] := makeFailure["InvalidGroup", "NumberOfRep requires a live Group handle."];

(* A group shows what it is (uxUpdatePlan.md 2.3, D1): Group[24-3I] (catalogue label; Group[24-3I$2] for a second
   build of the same label), Group[[24,3]] (GAP ID; Group[[24,3] II] when several such groups exist), Group[order n]. *)
Format[Group[id_String], StandardForm] := Interpretation[groupDisplayForm[id], Group[id]];
Format[Group[id_String], OutputForm] := "Group[" <> groupDisplayText[id] <> "]";
Protect[Group];

(*
    Summary: The display text of a group handle and the class its instance number counts in.
    Parameters: id — handle ID; state — registry state.
    Options/defaults: None.
    Returns: groupDisplayText: "24-3I", "24-3I$2", "[24,3]", "[24,3] II", "order 186" or the handle ID for a group
        that is not registered; groupDisplayClass: {"Label", label} | {"GAP", {n, k}} | {"Order", n}; groupDisplayForm: the
        Row Group[text] with a tooltip (name, order, irreps).
    Effects: Reads $GroupRegistry.
    Failures: None (never fails on a stale handle).
    Example: groupDisplayText[First[BuildModularGroup["24-3I"]]] is "24-3I".
    Remarks: The instance number is the rank by registration order among registered groups of the same class; the
        suffix is shown only when the class has more than one member.
    See also: newGroup; SetCatalogueLabel.
*)
groupDisplayClass[state_Association] := Which[
    StringQ[Lookup[state, "CatalogueLabel", None]], {"Label", state["CatalogueLabel"]},
    MatchQ[Lookup[state, "CatalogueID", None], {_Integer, _Integer}], {"GAP", state["CatalogueID"]},
    True, {"Order", state["Order"]}];
groupDisplayText[id_String] := Module[{state = Lookup[$GroupRegistry, id, None], class, members, rank, base},
    If[!AssociationQ[state], Return[id]];
    class = groupDisplayClass[state];
    members = SortBy[Select[Values[$GroupRegistry], groupDisplayClass[#] === class &], Lookup[#, "RegistrationIndex", 0] &];
    rank = First[FirstPosition[Lookup[members, "InstanceID"], id, {1}, {1}]];
    base = Switch[First[class], "Label", class[[2]], "GAP", "[" <> StringRiffle[ToString /@ class[[2]], ","] <> "]", _, "order " <> ToString[class[[2]]]];
    Which[Length[members] < 2, base,
        First[class] === "Label", If[rank === 1, base, base <> "$" <> ToString[rank]],
        True, base <> " " <> RomanNumeral[rank]]];
groupDisplayForm[id_String] := With[{state = Lookup[$GroupRegistry, id, None]},
    If[!AssociationQ[state], Row[{"Group[", id, "]"}],
        Tooltip[Row[{"Group[", Style[groupDisplayText[id], Bold], "]"}],
            Column[{state["Name"], "order " <> ToString[state["Order"]] <> If[MatchQ[state["CatalogueID"], {_, _}], ", GAP ID " <> ToString[state["CatalogueID"]], ""],
                ToString[Length[state["CharacterData"]["IrrepIDs"]]] <> " irreps", If[AssociationQ[state["ModularAssignment"]], "modular S, T assigned", "no modular assignment"], id}]]]];

(*
    Summary: Print a one-line note about a newly registered group when its display class already had a member.
    Parameters: group — Group (or a Failure, returned unchanged).
    Options/defaults: Configuration Notices (True prints; ConfigureVVMFTool[Notices -> False] silences notes).
    Returns: group.
    Effects: May Print one line; never issues a Message (uxUpdatePlan.md P6).
    Failures: None.
    Example: building 24-3I twice prints "Note: a group 24-3I already exists (Group[24-3I]); this one is Group[24-3I$2]."
    See also: groupDisplayText; notice.
*)
notice[text_String] := If[TrueQ[Lookup[$Configuration, Notices, True]], Print[Style[text, Darker[Gray]]]];
announceGroup[group : Group[id_String]] := Module[{state = Lookup[$GroupRegistry, id, None], class, others},
    If[!AssociationQ[state], Return[group]];
    class = groupDisplayClass[state];
    others = Select[Values[$GroupRegistry], groupDisplayClass[#] === class && #["InstanceID"] =!= id &];
    If[others =!= {},
        notice["Note: " <> Switch[First[class], "Label", "a group " <> class[[2]], "GAP", "a group with GAP ID [" <> StringRiffle[ToString /@ class[[2]], ","] <> "]",
            _, "a group of order " <> ToString[class[[2]]]] <> " already exists (Group[" <> groupDisplayText[First[SortBy[others, #["RegistrationIndex"] &]]["InstanceID"]] <>
            "]); this one is Group[" <> groupDisplayText[id] <> "]."]];
    group];
announceGroup[other_] := other;
True
