(*
    :Title: Mathematical group import
    :Context: VVMFTool`Private`
    :Summary: Allocate fresh group handles only after independent snapshot provenance is established.
    :Responsibilities: Stable reads, registered-export admission and actual native correspondence.
    :Dependencies: GroupSnapshots.wl; ExportLedger.wl; GAP/GroupImport.g; GAPWorkers.wl.
    :See Also: Schemas/GroupSnapshot.md; ImportGroupData in VVMFArch/step1Plan.md.
*)

Options[ImportGroupData] = Join[Options[RestoreGAPState], {ValidationGroup -> Automatic, Verification -> Automatic}];

(*
    Summary: Obtain an independently accepted native source for validating an unknown snapshot.
    Parameters: decoded — schema-checked snapshot; validation — Automatic or live Group;
        options/capabilities/call — validated shared execution settings and owned lifetime.
    Options/defaults: Automatic constructs only typed input and computes bound characters.
    Returns: Verified checkpoint reference, or correspondence/dependency/computation Failure.
    Effects: May lease/reconstruct the supplied group or construct a temporary typed source.
        No intermediate live Group is allocated and no imported raw code is executed.
    Failures: Unregistered raw input without an explicit validation group, unusable raw source
        state, failed construction/characters or resource exhaustion.
    Example: importing an unknown typed C5 file constructs its actual table before comparing rows.
    See also: validateImportedGroup; groupComputationSource; runCharacterRequest.
*)
importValidationSource[decoded_Association, validation_, options_Association,
    capabilities_Association, call_Association] := Module[
    {accepted, native, source, request, descriptor, context, base, complete},
    If[MatchQ[validation, _Group],
        accepted = groupData[validation]; If[FailureQ[accepted], Return[accepted]];
        native = groupEnvelope[accepted]; If[FailureQ[native], Return[native]];
        source = groupComputationSource[validation, accepted, capabilities, call];
        If[FailureQ[source], Return[source]];
        If[StringQ[source["Checkpoint"]], Return[source["Checkpoint"]]];
        Return[prepareGroupCheckpoint[accepted, native, options, capabilities, call]]];
    If[validation =!= Automatic || decoded["Data"]["Construction"]["type"] === "gapCode",
        Return[makeFailure["ImportNeedsValidationGroup", "An unregistered raw-code snapshot requires an accepted ValidationGroup; imported code is never executed."]]];
    request = <|"operation" -> "Construct", "requestID" -> CreateUUID["import-base-"],
        "stateID" -> CreateUUID["validation-state-"], "generatorIdentity" -> CreateUUID["validation-generators-"],
        "stateGeneration" -> "0", "construction" -> decoded["Data"]["Construction"]|>;
    descriptor = <|"Operation" -> "Construct", "Method" -> "GAP", "Model" -> "Original",
        "RecoveryStrategy" -> "Native", "WorkKey" -> "ImportValidationSource", "Tier" -> 0,
        "Parallel" -> False, "MinCores" -> 1, "MemoryEstimate" -> 128*2^20,
        "Availability" -> "Eligible", "Reason" -> None, "AllocatedCores" -> 1,
        "AllocatedMemory" -> options[MemoryBudget]|>;
    context = <|"Capabilities" -> capabilities, "Directory" -> call["Directory"], "Options" -> options|>;
    base = runAttempt[None, descriptor, request, context]; If[FailureQ[base], Return[base]];
    complete = runCharacterRequest[base["Checkpoint"], Join[options, <|CharacterMethod -> Automatic|>],
        capabilities, call["Directory"]];
    If[FailureQ[complete], complete, complete["Checkpoint"]]
];
importValidationSource[___] := makeFailure["InvalidSnapshot", "Expected decoded data and an owned validation call."];

(*
    Summary: Compare imported mathematical values with a fully verified native import candidate.
    Parameters: candidate/expected — decoded complete group data.
    Options/defaults: Producer, operation, request and diagnostics may reflect the new verification;
        every mathematical identity, ordering and optional payload must remain exactly equal.
    Returns: Boolean.
    Effects: Pure; this comparison is not itself a source of provenance.
    Failures: Missing/changed mathematical data return False.
    Example: class and irrep IDs in a valid permuted snapshot remain as saved after validation.
    See also: validateImportedGroup; VVMF_ValidateImported; publishConstructedGroup.
*)
importMathematicsQ[candidate_Association, expected_Association] := Module[{keys},
    keys = {"StateID", "GeneratorIdentity", "StateGeneration", "Construction", "Generators", "Order",
        "CatalogueID", "CharacterData", "AvailableData", "Elements", "SubgroupData", "ModularAssignment", "Representations"};
    ContainsAll[Keys[candidate], keys] && ContainsAll[Keys[expected], keys] &&
        KeyTake[candidate, keys] === KeyTake[expected, keys]
];
importMathematicsQ[___] := False;

(*
    Summary: Independently verify an unknown snapshot and publish its coherent native state.
    Parameters: decoded — structurally checked snapshot; validation — Automatic or accepted Group;
        options — effective ImportGroupData settings.
    Options/defaults: StoreGAPState controls newly validated imported state retention.
    Returns: Fresh Group preserving saved mathematical identities and name, or Failure.
    Effects: Uses actual native construction/generator/class/character/optional-data checks (inert
        representation variants are verified in Wolfram: verifyInertVariants),
        saves and freshly restores the candidate, then publishes it through the common boundary.
        The supplied ValidationGroup is never mutated.
    Failures: Incorrect mathematical claims, missing validation source, deadlines, save/restore
        errors or changed imported values prevent group publication.
    Example: a C5 column transposition without matching class words fails even if orthogonality passes.
    See also: importValidationSource; VVMF_ValidateImported; ImportGroupData.
*)
validateImportedGroup[decoded_Association, validation_, options_Association] :=
    Block[{$PublishedConstructionGroup = None}, validateImportedGroupScoped[decoded, validation, options]];
(*
    Summary: Validate an imported snapshot against actual group data (body of validateImportedGroup).
    Parameters: decoded — decodeGroupSnapshot result; validation — Automatic or accepted Group;
        options — validated import settings.
    Options/defaults: As validateImportedGroup.
    Returns: Fresh imported Group or Failure.
    Effects: As validateImportedGroup; runs inside its Block over $PublishedConstructionGroup, so a
        construction published for validation cannot leak its handle marker to later builds.
    Failures: As validateImportedGroup.
    Example: validateImportedGroup[decoded, Automatic, options] delegates here after scoping.
    See also: validateImportedGroup; publishConstructedGroup.
*)
validateImportedGroupScoped[decoded_Association, validation_, options_Association] := Module[{capabilities, classes},
    If[decoded["Data"]["Construction"]["type"] === "gapCode" && validation === Automatic,
        Return[makeFailure["ImportNeedsValidationGroup", "An unregistered raw-code snapshot requires an accepted ValidationGroup; imported code is never executed."]]];
    If[MatchQ[validation, _Group] && FailureQ[groupData[validation]], Return[groupData[validation]]];
    If[options[MemoryBudget] < 128*2^20,
        Return[makeFailure["MemoryLimit", "Import verification is below its initial admission estimate."]]];
    classes = knownSubgroupClassWitnesses[decoded["Data"]]; If[FailureQ[classes], Return[classes]];
    progressReport[<|"Event" -> "Stage", "Phase" -> "Checking GAP"|>];
    capabilities = CheckGAP[]; If[FailureQ[capabilities], Return[capabilities]];
    withCheckpointCall[Function[call, Module[{reference, record, request, descriptor, context, candidate, estimate, known, inert},
        reference = importValidationSource[decoded, validation, options, capabilities, call];
        If[FailureQ[reference], Return[reference]];
        record = checkpointRecord[reference, capabilities]; If[FailureQ[record], Return[record]];
        estimate = Max[128*2^20, 3 record["WorkspaceArtifact"]["Bytes"]];
        If[options[MemoryBudget] < estimate, Return[makeFailure["MemoryLimit", "The validation source exceeds the import admission budget."]]];
        request = Join[KeyTake[decoded["NativeEnvelope"], {"stateID", "generatorIdentity", "stateGeneration", "construction"}],
            <|"operation" -> "Import", "requestID" -> CreateUUID["import-"],
                "characterIdentity" -> decoded["Data"]["CharacterData"]["Identity"],
                "validationSource" -> KeyTake[record["Native"], {"stateID", "generatorIdentity", "stateGeneration"}],
                "importedGroup" -> decoded["NativeEnvelope"], "knownSubgroupClasses" -> classes|>];
        descriptor = <|"Operation" -> "Import", "Method" -> "GAP", "Model" -> "Original",
            "RecoveryStrategy" -> "Native", "WorkKey" -> "ImportCorrespondence", "Tier" -> 0,
            "Parallel" -> False, "MinCores" -> 1, "MemoryEstimate" -> estimate,
            "Availability" -> "Eligible", "Reason" -> None, "AllocatedCores" -> 1,
            "AllocatedMemory" -> options[MemoryBudget]|>;
        context = <|"Capabilities" -> capabilities, "Directory" -> call["Directory"], "Options" -> options|>;
        candidate = runAttempt[reference, descriptor, request, context]; If[FailureQ[candidate], Return[candidate]];
        If[!importMathematicsQ[candidate["Data"], decoded["Data"]],
            Return[makeFailure["InvalidImportCorrespondence", "Native verification changed the saved mathematical data."]]];
        (* Inert (Wolfram-exact, numerical) variants passed through GAP unverified; verify them here (R1)
           with the presentation certificate GAP just checked. *)
        inert = verifyInertVariants[candidate["Data"],
            Lookup[Lookup[decoded["NativeEnvelope"], "binding", <||>], "generatorPresentation", Missing["NotComputed"]]];
        If[FailureQ[inert], Return[makeFailure["InvalidImportCorrespondence", "An inert representation variant failed verification.",
            <|"Cause" -> inert|>]]];
        known = checkKnownGroupIdentities[candidate["Data"]]; If[FailureQ[known], Return[known]];
        publishConstructedGroup[candidate, capabilities, Join[options, <|Name -> decoded["Name"]|>]]
    ]]]
];
validateImportedGroup[___] := makeFailure["InvalidSnapshot", "Expected a decoded snapshot and import validation settings."];
validateImportedGroupScoped[___] := makeFailure["InvalidSnapshot", "Expected a decoded snapshot and import validation settings."];

(*
    Summary: Publish an exact independently registered snapshot without a GAP call.
    Parameters: decoded — complete checked snapshot; artifact — unchanged registered byte digest;
        options — effective import settings. Caller establishes the local ledger match.
    Options/defaults: StoreGAPState=False omits the old reference from the new handle without
        deleting any independently retained files.
    Returns: Fresh Group or explicit publication Failure.
    Effects: Issues a RegisteredExport receipt and allocates a fresh handle; no filesystem reads
        or executable source/workspace loading occur here.
    Failures: Invalid receipt/publication metadata does not become a usable imported group.
    Example: local registered snapshots retain exact characters after workspace eviction.
    See also: trustedExportRecord; ImportGroupData; newGroup.
*)
publishRegisteredImport[decoded_Association, artifact_Association, options_Association, source_ : "RegisteredExport"] := Module[
    {receipt, group, patch, committed},
    receipt = recordValidatedGroupResult[decoded["Data"],
        Join[<|"Source" -> source, "Reference" -> artifact["SHA256"]|>,
            If[source === "UnverifiedImport", <|"Verification" -> groupVerificationStatus[decoded["Data"]]|>, <||>]]];
    If[FailureQ[receipt], Return[receipt]];
    patch = Join[<|"NativeEnvelope" -> decoded["NativeEnvelope"], "IrrepOrder" -> decoded["IrrepOrder"],
        "RepresentationCache" -> emptyRepresentationCache[decoded["CacheEpoch"]]|>,
        If[TrueQ[options[StoreGAPState]], decoded["Cache"], <||>]];
    (* Allocation, envelope commit and partial-result recording form one uninterruptible step. *)
    AbortProtect[
        group = newGroup[decoded["Data"], receipt, decoded["Name"]];
        committed = If[FailureQ[group], group, commitGroup[group, 0, patch]];
        If[FailureQ[committed],
            If[MatchQ[group, _Group], KeyDropFrom[$GroupRegistry, group[[1]]]],
            $ProgressPartialResult = group]];
    If[FailureQ[committed], committed, group]
];
publishRegisteredImport[___] := makeFailure["InvalidSnapshot", "Expected independently registered snapshot data."];

(*
    Summary: The export identity a snapshot records, read from its raw fields before decoding.
    Parameters: snapshot — the parsed snapshot JSON.
    Options/defaults: None.
    Returns: <|"StateID", "GeneratorIdentity", "CharacterIdentity", "Order"|> (as exportedGroupIdentity of the decoded data),
        or Missing["NotAvailable"] for a snapshot without valid identities.
    Effects: Pure.
    Failures: None.
    Example: snapshotExportIdentity[readResult[SaveGroupData[g, path]]] === exportedGroupIdentity[groupData[g]].
    Remarks: Used to look a file up in the ledgers before decoding it (fastLoad.md); the decoded identities must agree.
    See also: exportedGroupIdentity; trustedExportRecord; ImportGroupData.
*)
snapshotExportIdentity[snapshot_Association] := Module[{group = Lookup[snapshot, "group", None], order, identity},
    If[!AssociationQ[group] || !AssociationQ[Lookup[group, "characterData", None]], Return[Missing["NotAvailable"]]];
    order = decodeInteger[Lookup[group, "order", None]];
    identity = <|"StateID" -> Lookup[group, "stateID", None], "GeneratorIdentity" -> Lookup[group, "generatorIdentity", None],
        "CharacterIdentity" -> Lookup[group["characterData"], "identity", None], "Order" -> If[IntegerQ[order], ToString[order], None]|>;
    If[validExportIdentityQ[identity], identity, Missing["NotAvailable"]]
];
snapshotExportIdentity[___] := Missing["NotAvailable"];

(*
    Summary: Import an exact mathematical snapshot into a fresh live Group after independent validation.
    Status: Alpha.
    Parameters: file — snapshot filename; relative paths resolve against the current directory.
    Options/defaults: ValidationGroup=Automatic; Verification=Automatic ("Exact" re-checks a registered file like an
        unknown one; "Numerical" and None import an unregistered file weakly); common configured GAP resources/state retention.
    Returns: Fresh Group with saved name and mathematical IDs, or structured Failure.
    Effects: Reads inert JSON and the independent local export ledger. Matching registered bytes
        import without GAP and without re-checking their mathematics (they were verified when saved; user decision
        2026-10-22): decoded once, saved CG bundles kept at their recorded statuses. Verification -> "Exact" re-checks
        everything as below. Otherwise
        validates through actual native state (and every saved CG bundle exactly) and saves a coherent
        checkpoint before publication; imported recipes and binary paths are never executed.
    Failures: Changed/corrupt files, unsupported schema, false correspondence or optional claims,
        missing raw ValidationGroup, invalid options, backend/resource/storage errors.
    Example: h=ImportGroupData[SaveGroupData[g,path]] gives a distinct live handle with the same
        character/irrep/class identities. Cache eviction does not prevent registered imports.
    Remarks: An explicitly supplied ValidationGroup is checked even for a registered file.
        Unknown raw snapshots require a group independently built from the same explicit recipe.
        ValidationGroup supplies evidence, not a waiver of mathematical checks.
    See also: SaveGroupData; RestoreGAPState; NormalSubgroupsByIndex; Schemas/GroupSnapshot.md.
*)
ImportGroupData[file_String, options : OptionsPattern[]] := Module[{effective, path},
    effective = resolveOperationOptions[ImportGroupData, "ImportGroupData", {options}];
    If[FailureQ[effective], Return[effective]];
    If[StringLength[file] === 0, Return[makeFailure["FileUnavailable", "The snapshot filename must not be empty."]]];
    path = ExpandFileName[file];
    withProgress[effective, "ImportGroupData", Function[Null, Module[
        {before, snapshot, after, decoded, known, trusted, result, data, patch, cgCache, level, mode, cap, recorded, preTrusted},
        before = fileDigest[path]; If[FailureQ[before], Return[before]];
        snapshot = readResult[path]; If[FailureQ[snapshot], Return[snapshot]];
        after = fileDigest[path];
        If[before =!= after, Return[makeFailure["ImportChanged", "The snapshot changed while being read."]]];
        level = effective[Verification];
        (* A registered file (its bytes and recorded identities match the user's or the library ledger) is not re-checked
           (user decision 2026-10-22, fastLoad.md): it was verified when it was saved and the ledger binds these bytes, so it
           is decoded once, at its recorded level, without the exact character Gram re-check, and its CG entries keep their
           recorded statuses (no check on first use). Verification -> "Exact" or a ValidationGroup re-checks everything. *)
        recorded = snapshotExportIdentity[snapshot];
        trusted = If[AssociationQ[recorded], trustedExportRecord[before, recorded], False];
        (* a damaged ledger is reported at once, before any decoding (review L4) *)
        If[FailureQ[trusted], Return[trusted]];
        preTrusted = effective[ValidationGroup] === Automatic && level =!= "Exact" && TrueQ[trusted];
        If[preTrusted,
            decoded = Block[{$GroupAcceptanceLevel = groupStatusLevel[trustedExportStatus[before]], $TrustedSnapshotDecode = True},
                decodeGroupSnapshot[snapshot]];
            If[FailureQ[decoded], Return[decoded]];
            If[decoded["Identity"] =!= recorded,
                Return[makeFailure["InvalidSnapshot", "The decoded identities differ from the snapshot's recorded ones."]]];
            trusted = True; mode = "Registered",
            (* the identities first (structure only), then the trust and the level (methodOptionsPlan.md 2C.4, 2C.5) *)
            decoded = Block[{$GroupAcceptanceLevel = None}, decodeGroupSnapshot[snapshot]]; If[FailureQ[decoded], Return[decoded]];
            trusted = trustedExportRecord[before, decoded["Identity"]]; If[FailureQ[trusted], Return[trusted]];
            mode = Which[effective[ValidationGroup] =!= Automatic || level === "Exact" || (level === Automatic && !TrueQ[trusted]), "Full",
                TrueQ[trusted], "Registered", True, "Unverified"]];
        (* a registered file imports at its recorded group level; an unregistered one at "Numerical"/None with its claims
           weakened first (unverifiedSnapshot: proved by no one here), so the stored envelope, the data and their status
           agree and a GAP rebuild of the envelope is weak too; a full import recomputes everything in GAP *)
        If[mode === "Unverified", snapshot = unverifiedSnapshot[snapshot]];
        If[mode =!= "Full" && !preTrusted,
            decoded = Block[{$GroupAcceptanceLevel = Switch[mode, "Registered", groupStatusLevel[trustedExportStatus[before]],
                    (* the numerical character check runs at "Numerical"; stored variants, a generator presentation certificate
                       and element words have no check at this level, so a file that holds any of them imports "Unverified"
                       (ValidateGroup proves the certificate and the words, a GAP rebuild re-proves native variants; final
                       review N3, N4) *)
                    _, If[level === "Numerical" && MissingQ[unverifiedSnapshotVariants[snapshot]] && !unverifiedSnapshotCertificateQ[snapshot] &&
                            !unverifiedSnapshotElementsQ[snapshot], "Numerical", None]]},
                decodeGroupSnapshot[snapshot]];
            If[FailureQ[decoded], Return[decoded]]];
        cap = groupVerificationStatus[decoded["Data"]];
        known = checkKnownGroupIdentities[decoded["Data"]]; If[FailureQ[known], Return[known]];
        (* Saved CG bundles: a registered file's entries keep their recorded statuses (trusted, no check on first use); an
           unregistered weak import defers the exact channel validation to first use; a full import validates every
           bundle exactly here. *)
        cgCache = importCGBundles[decoded["Data"], decoded["CGRecords"], decoded["CGEpoch"], Which[mode === "Full", "Full", preTrusted, "Trusted", True, "Deferred"]];
        If[FailureQ[cgCache], Return[cgCache]];
        (* an unregistered file's CG entries keep no status above the import level *)
        If[mode === "Unverified", cgCache["Entries"] = Map[Join[#, <|"VerificationStatus" -> cgWeakestStatus[{cgEntryStatus[#], cap}]|>] &, cgCache["Entries"]]];
        result = Switch[mode,
            "Registered", publishRegisteredImport[decoded, before, effective],
            (* the file's GAP workspace reference is not adopted: its state was proved for no one here *)
            "Unverified", publishRegisteredImport[decoded, before, Join[effective, <|StoreGAPState -> False|>], "UnverifiedImport"],
            _, validateImportedGroup[decoded, effective[ValidationGroup], effective]];
        If[FailureQ[result], Return[result]];
        data = groupData[result];
        (* The saved presentation order applies to both import paths; it is not mathematical data. *)
        patch = <|"IrrepOrder" -> decoded["IrrepOrder"], "RepresentationCache" -> emptyRepresentationCache[decoded["CacheEpoch"]],
            "CGCache" -> cgCache, Sequence @@ Normal[decoded["Presentation"]],
            "LastComputation" -> Join[data["LastComputation"], <|"Operation" -> "ImportGroupData",
            "Validation" -> Which[mode === "Unverified", "UnverifiedImport", mode === "Full", "GroupCorrespondence",
                (* trusted only through the package's library ledger (uxUpdatePlan.md 5) *)
                TrueQ[libraryLedgerTrust[before, decoded["Identity"]]] && !TrueQ[Block[{$LibraryLedgerDirectory = None}, trustedExportRecord[before, decoded["Identity"]]]],
                    "LibraryRegisteredExport",
                True, "RegisteredExport"], "SourceFile" -> path|>]|>;
        commitGroup[result, data["Revision"], patch]
    ]]]
];
ImportGroupData[___] := makeFailure["InvalidSnapshot", "Expected a mathematical snapshot filename."];

(*
    Summary: Weaken an unregistered snapshot's claims to what an unverified import establishes (methodOptionsPlan.md 2C.5,
        2C.6): the character claims "TransportOnly", the S,T claim "Unverified", every inert variant "Unverified".
    Parameters: snapshot — the raw snapshot read from the file.
    Options/defaults: None.
    Returns: unverifiedSnapshot: the snapshot with the weakened group envelope (and without its subgroup queries);
        unverifiedSnapshotVariants: the envelope's representation data, or Missing["None"]; unverifiedSnapshotCertificateQ /
        unverifiedSnapshotElementsQ: whether the envelope records a generator presentation certificate / element words.
    Effects: Pure.
    Failures: None (a malformed envelope is left for decodeGroupSnapshot to refuse).
    Example: unverifiedSnapshot[s]["group"]["binding"]["nativeCharactersVerified"] is "TransportOnly".
    Remarks: Native-tier variants carry no mark: GAP rebuilds them from their images and re-proves them (VVMF_VerifyRep) on
        any rebuild, and until then they are bounded by the group's status. The decoded data come from this envelope, so
        the receipt, groupEnvelope and sameGroupStateQ compare like with like.
    See also: ImportGroupData; validateGroupResult; GAP VVMF_TransferCharacters, VVMF_RebindGroup.
*)
unverifiedSnapshot[snapshot_Association] := Module[{native = Lookup[snapshot, "group", None]},
    If[!AssociationQ[native], Return[snapshot]];
    If[AssociationQ[Lookup[native, "binding", None]],
        native["binding"] = Join[native["binding"], AssociationMap["TransportOnly" &,
            Select[{"classTransportVerified", "nativeCharactersVerified"}, KeyExistsQ[native["binding"], #] &]]]];
    If[AssociationQ[Lookup[native, "modularAssignment", None]], native["modularAssignment"] = Join[native["modularAssignment"], <|"verified" -> "Unverified"|>]];
    (* the file's subgroup queries are dropped (final review H-2): a rebuild re-proves each subgroup's invariants but not a
       query's completeness, provenance or descriptions; GroupSubgroups recomputes them in GAP when asked *)
    If[Lookup[native, "subgroupData", Null] =!= Null,
        native["subgroupData"] = Null;
        (* an envelope last produced by GroupSubgroups must hold its query: the weakened envelope records the character
           computation instead (the file's history is not evidence here; the import records its own computation) *)
        If[Lookup[native, "operation", None] === "GroupSubgroups",
            native["operation"] = "Characters";
            If[AssociationQ[Lookup[native, "diagnostics", None]],
                native["diagnostics"] = Join[KeyDrop[native["diagnostics"], "subgroupQueryID"], <|"operation" -> "Characters"|>]]];
        If[AssociationQ[Lookup[native, "availableData", None]],
            native["availableData"] = Join[native["availableData"], <|"Subgroups" -> {}, "Descriptions" -> "NotComputed"|>]]];
    If[AssociationQ[Lookup[native, "representationData", None]],
        native["representationData"] = Map[If[AssociationQ[#] && AssociationQ[Lookup[#, "variants", None]],
            Join[#, <|"variants" -> Map[If[AssociationQ[#] && MemberQ[{"Wolfram", "Numerical"}, Lookup[#, "tier", None]],
                Join[#, <|"verificationStatus" -> "Unverified"|>], #] &, #["variants"]]|>], #] &, native["representationData"]]];
    Join[snapshot, <|"group" -> native|>]
];
unverifiedSnapshotCertificateQ[snapshot_Association] := KeyExistsQ[Replace[Lookup[Replace[Lookup[snapshot, "group", None], Except[_Association] -> <||>],
    "binding", <||>], Except[_Association] -> <||>], "generatorPresentation"];
unverifiedSnapshotElementsQ[snapshot_Association] := ListQ[Lookup[Replace[Lookup[snapshot, "group", None], Except[_Association] -> <||>], "elements", Null]];
unverifiedSnapshotVariants[snapshot_Association] := With[{data = Lookup[Replace[Lookup[snapshot, "group", None], Except[_Association] -> <||>], "representationData", Null]},
    If[AssociationQ[data] && data =!= <||>, data, Missing["None"]]];

True
