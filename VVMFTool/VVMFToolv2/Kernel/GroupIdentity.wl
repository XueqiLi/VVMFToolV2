(*
    :Title: Immutable mathematical identity bindings
    :Context: VVMFTool`Private`
    :Summary: Prevent an imported snapshot from reassigning previously accepted identities.
    :Responsibilities: Order-independent character correspondence and known-identity conflicts.
    :Dependencies: GroupObject.wl; ExportLedger.wl at call time; the decoded Representations shape of
        RepresentationStorage.wl (variant Identity) for representation bindings.
    :See Also: ImportGroupData; SaveGroupData; Schemas/GroupSnapshot.md.
*)

(*
    Summary: Digest one identity key or mathematical binding value.
    Parameters: value — any expression built from accepted decoded data.
    Options/defaults: None.
    Returns: Lowercase 64-digit SHA256 hexadecimal string.
    Effects: Pure.
    Failures: None.
    Example: StringLength[identityDigest[{"State", "s"}]] is 64.
    See also: groupIdentityBindings; modularAssignmentBinding.
*)
identityDigest[value_] := IntegerString[Hash[value, "SHA256"], 16, 64];

(*
    Summary: Build the identity binding of one explicit modular assignment of a group state.
    Parameters: stateID, generatorIdentity — accepted group identities; assignment — decoded
        Identity/S/T/Verified association.
    Options/defaults: None.
    Returns: identityDigest[{"ModularAssignment", identity}] -> identityDigest[{stateID, generatorIdentity, S, T}].
    Effects: Pure.
    Failures: Caller supplies a decoded assignment.
    Example: an assignment accepted earlier for a group remains in its IdentityBindings, so a context
        retaining that assignment can be checked against the group's history.
    See also: groupIdentityBindings; bindRepContext.
*)
modularAssignmentBinding[stateID_, generatorIdentity_, assignment_Association] :=
    identityDigest[{"ModularAssignment", assignment["Identity"]}] ->
        identityDigest[{stateID, generatorIdentity, assignment["S"], assignment["T"]}];

(*
    Summary: The identity-binding value of one representation variant.
    Parameters: generatorIdentity — the state's generator identity; irrepID — character ID;
        variant — decoded variant association.
    Options/defaults: None.
    Returns: {generatorIdentity, irrepID, realization identity, tier, arithmetic, unitary}.
    Effects: Pure.
    Failures: None; missing fields appear as Missing values and never match an accepted binding.
    Example: representationVariantBinding[gid, id, v][[3]] is v["Identity"].
    Remarks: Only matrix-intrinsic properties are bound; T-diagonality depends on the assignment and
        is rechecked by context binding.
    See also: groupIdentityBindings; bindRepContext.
*)
representationVariantBinding[generatorIdentity_, irrepID_, variant_Association] :=
    {generatorIdentity, irrepID, Lookup[variant, "Identity"], Lookup[variant, "Tier"], Lookup[variant, "Arithmetic"],
        Lookup[Lookup[variant, "BasisProperties", <||>], "Unitary"]};
representationVariantBinding[generatorIdentity_, irrepID_, _] := {generatorIdentity, irrepID, Missing["Invalid"]};

(*
    Summary: Fingerprint immutable group, generator, character, assignment, subgroup and representation identities.
    Parameters: data — independently accepted or schema-checked complete decoded group data.
    Options/defaults: Absent optional data add no binding; descriptions and computation metadata are excluded.
    Returns: Association of scoped identity digests to mathematical-binding digests, or Failure.
    Effects: Pure; fingerprints detect conflicts but never establish mathematical provenance.
    Failures: Incomplete records fail. The caller establishes the complete result schema.
    Example: permuting character rows and their IDs together leaves the bindings unchanged;
        permuting values without IDs changes the character binding. A representation variant binds
        {StateID, irrep ID, variant ID} to its realization identity, excluding basis properties that a
        later modular assignment recomputes.
    Remarks: Class/irrep ordering is normalized by ID. Recorded generator order and each class's
        representative word are immutable correspondence data, not rewritten by import.
        Exact character values are reduced algebraically before fingerprinting.
    See also: checkKnownGroupIdentities; compatibleIdentityBindingsQ; exportedGroupIdentity.
*)
groupIdentityBindings[data_Association] := Module[{characters, rows, columns, bindings, assignment, subgroups},
    If[Lookup[data, "Status", None] =!= "Complete" ||
        !ContainsAll[Keys[data], {"StateID", "GeneratorIdentity", "Construction", "Generators",
            "Order", "CatalogueID", "CharacterData"}] || !AssociationQ[data["CharacterData"]],
        Return[makeFailure["InvalidExportIdentity", "Complete group correspondence is required."]]];
    characters = data["CharacterData"];
    If[!ContainsAll[Keys[characters], {"Identity", "IrrepIDs", "ClassIDs", "Values", "Degrees",
        "ClassSizes", "ClassOrders", "ClassRepresentativeWords", "IdentityClassID", "TrivialIrrepID"}],
        Return[makeFailure["InvalidExportIdentity", "Complete character correspondence is required."]]];
    rows = Ordering[characters["IrrepIDs"]]; columns = Ordering[characters["ClassIDs"]];
    bindings = {
        {"State", data["StateID"]} -> {canonicalJSON[data["Construction"]], data["Order"],
            data["CatalogueID"], data["GeneratorIdentity"], characters["Identity"]},
        {"Generators", data["GeneratorIdentity"]} -> {data["StateID"], data["Generators"]},
        {"Characters", characters["Identity"]} -> {data["StateID"], data["GeneratorIdentity"],
            characters["IrrepIDs"][[rows]], characters["Degrees"][[rows]],
            characters["ClassIDs"][[columns]], characters["ClassSizes"][[columns]],
            characters["ClassOrders"][[columns]], characters["ClassRepresentativeWords"][[columns]],
            characters["IdentityClassID"], characters["TrivialIrrepID"],
            RootReduce[characters["Values"][[rows, columns]]]}
    };
    assignment = Lookup[data, "ModularAssignment", Missing["NotAssigned"]];
    subgroups = Lookup[data, "SubgroupData", Missing["NotComputed"]];
    If[AssociationQ[subgroups], Do[
        AppendTo[bindings, {"Subgroup", data["StateID"], item["SubgroupID"]} ->
            {data["GeneratorIdentity"], KeyTake[item, {"GeneratorWords", "Order", "Index", "Normal",
                "ConjugacyClassID", "ConjugacyClassSize"}]}],
        {item, Flatten[Lookup[Values[subgroups], "Items", {}], 1]}]];
    (* Representation variants: a variant ID of an irrep of this state names one exact realization,
       with its tier, arithmetic and (matrix-intrinsic) unitarity. *)
    Do[AppendTo[bindings, {"Representation", data["StateID"], entry["CharacterID"], variant} ->
            representationVariantBinding[data["GeneratorIdentity"], entry["CharacterID"], entry["Variants"][variant]]],
        {entry, Values[Lookup[data, "Representations", <||>]]}, {variant, Keys[entry["Variants"]]}];
    bindings = (identityDigest[First[#]] -> identityDigest[Last[#]]) & /@ bindings;
    (* Keep the established binding order: groups, generators, characters, assignment, subgroups. *)
    If[AssociationQ[assignment], bindings = Insert[bindings,
        modularAssignmentBinding[data["StateID"], data["GeneratorIdentity"], assignment], 4]];
    Association[bindings]
];
groupIdentityBindings[___] := makeFailure["InvalidExportIdentity", "Expected complete group correspondence."];

(*
    Summary: Check the portable digest-map grammar used by the independent local ledger.
    Parameters: bindings — arbitrary expression.
    Options/defaults: An empty map records no known bindings.
    Returns: Boolean.
    Effects: Pure; this grammar check establishes no provenance.
    Failures: Nonassociations or keys/values other than lowercase SHA256 strings return False.
    Example: validIdentityBindingsQ[<||>] returns True.
    See also: readExportLedger; groupIdentityBindings.
*)
validIdentityBindingsQ[bindings_] := AssociationQ[bindings] &&
    AllTrue[Join[Keys[bindings], Values[bindings]],
        StringQ[#] && StringMatchQ[#, RegularExpression["[0-9a-f]{64}"]] &];

(*
    Summary: Require every identity shared by two checked maps to retain its original binding.
    Parameters: candidate/known — validated binding digest associations.
    Options/defaults: Previously unknown identities have no conflicting local meaning.
    Returns: Boolean.
    Effects: Pure.
    Failures: A different binding for any shared identity returns False.
    Example: disjoint maps are compatible; changing one known character binding is not.
    See also: checkKnownGroupIdentities; writeExportRegistration.
*)
compatibleIdentityBindingsQ[candidate_Association, known_Association] :=
    AllTrue[Intersection[Keys[candidate], Keys[known]], candidate[#] === known[#] &];
compatibleIdentityBindingsQ[___] := False;

(*
    Summary: Reject imported identity reuse that conflicts with accepted live groups or saved exports.
    Parameters: data — schema-checked complete decoded import data.
    Options/defaults: Uses the fixed independent ledger; imported paths cannot select it.
    Returns: True or StateConflict/ledger/data Failure.
    Effects: Reads accepted registry values and, when present, the independent local ledger.
        It neither allocates a handle nor starts GAP nor trusts the imported mathematical claims.
    Failures: Known state/generator/character identities cannot acquire different meanings.
    Example: changing two C5 rows without moving their IDs fails even in a fresh kernel when
        the original export ledger survives and the GAP workspace has been evicted.
    See also: ImportGroupData; groupIdentityBindings; readExportLedger.
*)
checkKnownGroupIdentities[data_Association] := Module[{bindings, known, root, ledger},
    bindings = groupIdentityBindings[data]; If[FailureQ[bindings], Return[bindings]];
    known = If[KeyExistsQ[#, "IdentityBindings"], #["IdentityBindings"], groupIdentityBindings[#]] & /@ Values[$GroupRegistry];
    If[AnyTrue[known, FailureQ], Return[First[Select[known, FailureQ]]]];
    If[FileType[$ExportLedgerDirectory] =!= None,
        root = managedRoot[$ExportLedgerDirectory]; If[FailureQ[root], Return[root]];
        ledger = readExportLedger[root]; If[FailureQ[ledger], Return[ledger]];
        known = Join[known, Lookup[Values[ledger["Entries"]], "Bindings", {}]]];
    (* library groups take part in identity conflict checks (uxUpdatePlan.md 5) *)
    known = Join[known, libraryLedgerBindings[]];
    If[AllTrue[known, compatibleIdentityBindingsQ[bindings, #] &], True,
        makeFailure["StateConflict", "Imported identities conflict with previously accepted mathematical correspondence."]]
];
checkKnownGroupIdentities[___] := makeFailure["InvalidExportIdentity", "Expected complete imported data."];

(*
    Summary: Retain one accepted embedded witness for each known subgroup conjugacy-class ID.
    Parameters: data — complete decoded group data; subgroup words already passed native validation.
    Options/defaults: Missing subgroup data produce an empty witness list.
    Returns: JSON records with StateID, GeneratorIdentity, ClassID and named generator Words.
    Effects: Pure; does not enumerate subgroups or identify classes by descriptive metadata.
    Failures: Requires the caller's complete schema/word preconditions.
    Example: S3's three conjugate order-two subgroups provide one class witness.
    See also: knownSubgroupClassWitnesses; VVMF_CheckImportedSubgroupClasses; registerExport.
*)
subgroupClassWitnesses[data_Association] := Module[{queries, items, names},
    queries = Lookup[data, "SubgroupData", Missing["NotComputed"]];
    If[!AssociationQ[queries], Return[{}]];
    names = Lookup[data["Generators"], "Name", {}];
    items = DeleteDuplicatesBy[Flatten[Lookup[Values[queries], "Items", {}], 1], #["ConjugacyClassID"] &];
    (<|"StateID" -> data["StateID"], "GeneratorIdentity" -> data["GeneratorIdentity"],
        "ClassID" -> #["ConjugacyClassID"], "Words" -> (encodeWord[#, names] & /@ #["GeneratorWords"])|> &) /@ items
];

(*
    Summary: Validate inert local-ledger subgroup-class witness records.
    Parameters: witnesses — arbitrary expression.
    Options/defaults: Empty lists and trivial-subgroup empty generator words are valid.
    Returns: Boolean.
    Effects: Pure; does not execute words or establish their mathematical truth.
    Failures: Malformed identities, words or decimal exponents return False.
    Example: a nondecimal exponent in a ledger witness is rejected.
    See also: subgroupClassWitnesses; readExportLedger.
*)
validSubgroupClassWitnessesQ[witnesses_] := ListQ[witnesses] && AllTrue[witnesses, Function[entry,
    AssociationQ[entry] && resultFieldsQ[entry, {"StateID", "GeneratorIdentity", "ClassID", "Words"}] &&
    AllTrue[Lookup[entry, {"StateID", "GeneratorIdentity", "ClassID"}],
        StringQ[#] && StringLength[#] > 0 &] && ListQ[entry["Words"]] &&
    AllTrue[entry["Words"], Function[word, ListQ[word] && AllTrue[word, Function[pair,
        MatchQ[pair, {_String, _String}] && generatorNamesQ[{pair[[1]]}] &&
        IntegerQ[decodeInteger[pair[[2]]]] && decodeInteger[pair[[2]]] =!= 0]]]]]];

(*
    Summary: Collect independent class witnesses whose scoped IDs an import claims to reuse.
    Parameters: data — complete schema-checked decoded import.
    Options/defaults: Uses live accepted groups and the fixed independent export ledger.
    Returns: JSON witness list or a ledger/storage Failure.
    Effects: Reads the ledger; starts no computation. Native import must establish actual conjugacy.
    Failures: Corrupt independent storage is reported; a snapshot cannot supply its own evidence.
    Example: changed V4 class IDs require comparison to the saved distinct order-two subgroups.
    See also: validateImportedGroup; VVMF_CheckImportedSubgroupClasses.
*)
knownSubgroupClassWitnesses[data_Association] := Module[{ids, witnesses, root, ledger},
    ids = Lookup[subgroupClassWitnesses[data], "ClassID", {}];
    If[ids === {}, Return[{}]];
    witnesses = Flatten[(If[KeyExistsQ[#, "SubgroupClassWitnesses"], #["SubgroupClassWitnesses"],
        subgroupClassWitnesses[#]] &) /@ Values[$GroupRegistry], 1];
    If[FileType[$ExportLedgerDirectory] =!= None,
        root = managedRoot[$ExportLedgerDirectory]; If[FailureQ[root], Return[root]];
        ledger = readExportLedger[root]; If[FailureQ[ledger], Return[ledger]];
        witnesses = Join[witnesses, Flatten[Lookup[Values[ledger["Entries"]], "SubgroupClasses", {}], 1]]];
    DeleteDuplicates[Select[witnesses, #["StateID"] === data["StateID"] &&
        #["GeneratorIdentity"] === data["GeneratorIdentity"] && MemberQ[ids, #["ClassID"]] &]]
];

True
