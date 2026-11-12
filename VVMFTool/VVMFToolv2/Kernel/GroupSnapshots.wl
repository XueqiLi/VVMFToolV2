(*
    :Title: Mathematical group snapshots
    :Context: VVMFTool`Private`
    :Summary: Encode accepted mathematical state as versioned, executable-free JSON.
    :Responsibilities: Snapshot schema, inert cache references and registered atomic export.
    :Dependencies: GroupObject.wl (irrepOrderQ); ExportLedger.wl; ArtifactIO.wl.
    :See Also: GroupStorage.wl; Schemas/GroupSnapshot.md; SaveGroupData.
*)

(*
    Summary: Validate an optional retained-workspace reference without accessing its files.
    Parameters: reference — Null or path/metadata record; data — decoded group snapshot.
    Options/defaults: Null means no retained reference and decodes to NotStored properties.
    Returns: Public cache-property patch or InvalidSnapshot Failure.
    Effects: Pure path/schema checks; no workspace load or filesystem trust is conferred.
    Failures: Mismatched mathematical identities/generation, invalid paths or metadata types.
    Example: an evicted but syntactically valid reference remains inert saved metadata.
    See also: admitCheckpoint; decodeGroupSnapshot; RestoreGAPState.
*)
decodeCacheReference[reference_, data_Association] := Module[{metadata, fields, strings},
    If[reference === Null, Return[<|"GAPCachePath" -> Missing["NotStored"],
        "GAPCacheMetadata" -> Missing["NotStored"]|>]];
    fields = {"Root", "CacheID", "EntryID", "Runtime", "StateID", "GeneratorIdentity", "StateGeneration", "LastUsed"};
    If[!AssociationQ[reference] || !resultFieldsQ[reference, {"path", "metadata"}] ||
        !absolutePathQ[reference["path"]] || !AssociationQ[reference["metadata"]] ||
        !resultFieldsQ[reference["metadata"], fields],
        Return[makeFailure["InvalidSnapshot", "Malformed retained-state reference."]]];
    metadata = reference["metadata"];
    strings = Lookup[metadata, {"Root", "CacheID", "EntryID", "Runtime", "StateID", "GeneratorIdentity"}];
    If[!AllTrue[strings, StringQ[#] && StringLength[#] > 0 &] || !absolutePathQ[metadata["Root"]] ||
        !IntegerQ[metadata["StateGeneration"]] || metadata["StateGeneration"] < 0 ||
        !IntegerQ[metadata["LastUsed"]] || metadata["LastUsed"] < 0 ||
        !AllTrue[{"StateID", "GeneratorIdentity", "StateGeneration"},
            metadata[#] === Lookup[data, #, None] &],
        Return[makeFailure["InvalidSnapshot", "Retained-state identities or metadata disagree with the mathematics."]]];
    <|"GAPCachePath" -> reference["path"], "GAPCacheMetadata" -> metadata|>
];
decodeCacheReference[___] := makeFailure["InvalidSnapshot", "Expected an inert cache reference and decoded group."];

(*
    Summary: Decode the exact mathematical snapshot grammar without establishing producer trust.
    Parameters: snapshot — versioned native JSON record.
    Options/defaults: Format VVMFToolGroup, schemaVersion 1 or 2, complete mandatory character data.
        Schema 2 adds irrepOrder, the saved presentation order of the irrep IDs, and optionally
        representationCacheEpoch (decimal string; absent means 0), the derived-cache eviction epoch.
    Returns: Data/NativeEnvelope/Name/Cache/Identity/IrrepOrder/CacheEpoch association or schema/arithmetic
        Failure; a schema-1 snapshot has the canonical irrep order and epoch 0.
    Effects: Pure; retained code, paths, producer fields and verification claims remain inert.
    Failures: Extra/missing fields, unsupported schema, incomplete characters or invalid cache reference.
    Example: decoding a snapshot validates exact character orthogonality but does not publish a Group.
    Remarks: Import must additionally find independent registered provenance or verify actual
        group/generator/class/character correspondence; an embedded boolean or digest is insufficient.
    See also: decodeCacheReference; validateGroupResult; validateImportedGroup.
*)
decodeGroupSnapshot[snapshot_Association] := Module[{native, data, cache, identity, fields, order, epoch, presentation},
    fields = {"format", "schemaVersion", "name", "group", "gapCache"};
    If[MemberQ[{2, 3}, Lookup[snapshot, "schemaVersion", None]], AppendTo[fields, "irrepOrder"];
        (* schema 3: optional presentation keys (uxUpdatePlan.md 1.4) *)
        If[snapshot["schemaVersion"] === 3, fields = Join[fields, Select[$SnapshotPresentationKeys, KeyExistsQ[snapshot, #] &]]];
        If[KeyExistsQ[snapshot, "representationCacheEpoch"], AppendTo[fields, "representationCacheEpoch"]];
        (* Stage 4: optional CG store (validated on import, or trusted at their recorded statuses in a registered file). *)
        If[KeyExistsQ[snapshot, "cgData"], fields = Join[fields, {"cgData", "cgCacheEpoch"}]]];
    If[!resultFieldsQ[snapshot, fields] || snapshot["format"] =!= "VVMFToolGroup" ||
        !MemberQ[{1, 2, 3}, snapshot["schemaVersion"]] ||
        !StringQ[snapshot["name"]] || !AssociationQ[snapshot["group"]],
        Return[makeFailure["InvalidSnapshot", "Unsupported or malformed mathematical group snapshot."]]];
    native = snapshot["group"];
    data = validateGroupResult[native, KeyTake[native,
        {"requestID", "stateID", "generatorIdentity", "stateGeneration", "operation", "construction"}]];
    If[FailureQ[data], Return[data]];
    If[data["Status"] =!= "Complete",
        Return[makeFailure["IncompleteGroup", "A mathematical group snapshot requires complete characters."]]];
    If[AssociationQ[data["SubgroupData"]] && AnyTrue[Values[data["SubgroupData"]],
        #["QueryID"] =!= subgroupSelectionID[#["Kind"], #["Filters"]["Order"], #["Filters"]["Index"]] &],
        Return[makeFailure["InvalidSubgroups", "A saved subgroup query ID does not match its mathematical selection."]]];
    cache = decodeCacheReference[snapshot["gapCache"], data]; If[FailureQ[cache], Return[cache]];
    identity = exportedGroupIdentity[data]; If[FailureQ[identity], Return[identity]];
    order = If[MemberQ[{2, 3}, snapshot["schemaVersion"]], snapshot["irrepOrder"], data["CharacterData"]["IrrepIDs"]];
    presentation = decodeSnapshotPresentation[snapshot, data]; If[FailureQ[presentation], Return[presentation]];
    epoch = If[KeyExistsQ[snapshot, "representationCacheEpoch"], decodeInteger[snapshot["representationCacheEpoch"]], 0];
    If[!IntegerQ[epoch] || epoch < 0, Return[makeFailure["InvalidSnapshot", "The saved representation-cache epoch is invalid."]]];
    If[!irrepOrderQ[order, data["CharacterData"]],
        Return[makeFailure["InvalidSnapshot", "The saved irrep order is not a permutation of the irrep IDs."]]];
    If[KeyExistsQ[snapshot, "cgData"] && (!ListQ[snapshot["cgData"]] || !AllTrue[snapshot["cgData"], AssociationQ] ||
            !IntegerQ[decodeInteger[snapshot["cgCacheEpoch"]]] || decodeInteger[snapshot["cgCacheEpoch"]] < 0),
        Return[makeFailure["InvalidSnapshot", "The saved CG store is malformed."]]];
    <|"Data" -> data, "NativeEnvelope" -> native, "Name" -> snapshot["name"],
        "Cache" -> cache, "Identity" -> identity, "IrrepOrder" -> order, "CacheEpoch" -> epoch,
        "CGRecords" -> Lookup[snapshot, "cgData", {}], "Presentation" -> presentation,
        "CGEpoch" -> If[KeyExistsQ[snapshot, "cgCacheEpoch"], decodeInteger[snapshot["cgCacheEpoch"]], 0]|>
];
decodeGroupSnapshot[___] := makeFailure["InvalidSnapshot", "Expected a mathematical snapshot association."];

(*
    Summary: Encode the accepted live group and independently retained state reference.
    Parameters: group — live Group with matching native envelope and private validation receipt.
    Options/defaults: Schema 2 with the group's irrepOrder and representation-cache epoch (the derived
        entries themselves are recomputable and are not saved); missing retained state becomes Null, not an
        executable placeholder.
    Returns: Exact JSON snapshot or invalid/unbound group Failure.
    Effects: Pure; accepted optional mathematics is included, without starting GAP or saving its cache.
    Failures: Unknown handles, changed/unverified native envelope or inconsistent metadata.
    Example: a character-only group exports successfully after its GAP workspace was evicted.
    See also: groupEnvelope; decodeGroupSnapshot; SaveGroupData.
*)
groupSnapshot[group_Group] := Module[{accepted, native, cache, snapshot, checked},
    accepted = groupData[group]; If[FailureQ[accepted], Return[accepted]];
    native = groupEnvelope[accepted]; If[FailureQ[native], Return[native]];
    cache = If[MissingQ[accepted["GAPCachePath"]], Null,
        <|"path" -> accepted["GAPCachePath"], "metadata" -> accepted["GAPCacheMetadata"]|>];
    snapshot = <|"format" -> "VVMFToolGroup", "schemaVersion" -> 2,
        "name" -> accepted["Name"], "group" -> native, "gapCache" -> cache, "irrepOrder" -> accepted["IrrepOrder"],
        "representationCacheEpoch" -> ToString[accepted["RepresentationCache"]["Epoch"]]|>;
    (* Schema 3 only when presentation data are present (labels, class order, catalogue label, title). *)
    With[{p = encodeSnapshotPresentation[accepted]}, If[p =!= <||>, snapshot = Join[snapshot, p]; snapshot["schemaVersion"] = 3]];
    (* The mathematical CG store travels with the snapshot when it holds anything (Stage 4). *)
    If[accepted["CGCache"]["Entries"] =!= <||> || accepted["CGCache"]["Epoch"] > 0,
        snapshot["cgData"] = encodeCGBundle[#, Lookup[#, "Precision", Infinity]] & /@ (cgSnapshotEntry /@ Values[accepted["CGCache"]["Entries"]]);
        If[!FreeQ[snapshot["cgData"], _Failure], Return[FirstCase[snapshot["cgData"], _Failure, Null, Infinity]]];
        snapshot["cgCacheEpoch"] = ToString[accepted["CGCache"]["Epoch"]]];
    (* read at the group's own level (a weakly built group's claims, methodOptionsPlan.md 2C.6) *)
    checked = Block[{$GroupAcceptanceLevel = groupStatusLevel[groupVerificationStatus[accepted]]}, decodeGroupSnapshot[snapshot]];
    If[FailureQ[checked], checked, snapshot]
];
groupSnapshot[___] := makeFailure["InvalidGroup", "Expected a live accepted Group."];

(*
    Summary: Save a portable mathematical group snapshot and register its independently accepted bytes.
    Status: Alpha.
    Parameters: group — live accepted Group; file — destination filename with an existing parent directory.
    Options/defaults: No options. A relative filename resolves against the current directory.
    Returns: Absolute saved filename or a structured Failure. A ledger failure includes SavedFile.
    Effects: Atomically replaces the JSON target, then registers its exact digest in the independent
        local export ledger. No GAP computation, workspace save or group mutation occurs.
    Failures: Invalid/unbound group, file I/O or ledger registration. A ledger failure leaves the
        valid saved mathematical file available but does not claim that it was registered.
    Example: SaveGroupData[g, FileNameJoin[{$TemporaryDirectory,"group.json"}]] returns that path;
        ImportGroupData can recognize its registered bytes after computational cache eviction.
    See also: ImportGroupData; CleanGAPCache; registerExport; Schemas/GroupSnapshot.md.
*)
SaveGroupData[group_Group, file_String] := Module[{snapshot, path, written, decoded, bindings, registered},
    If[StringLength[file] === 0, Return[makeFailure["SaveFailed", "The snapshot filename must not be empty."]]];
    snapshot = groupSnapshot[group]; If[FailureQ[snapshot], Return[snapshot]];
    (* a weakly built group's own claims are read at its level (methodOptionsPlan.md 2C.6) *)
    decoded = Block[{$GroupAcceptanceLevel = groupAcceptanceLevel[group]}, decodeGroupSnapshot[snapshot]];
    If[FailureQ[decoded], Return[decoded]];
    bindings = groupIdentityBindings[decoded["Data"]]; If[FailureQ[bindings], Return[bindings]];
    path = ExpandFileName[file];
    written = writeResult[path, snapshot]; If[FailureQ[written], Return[written]];
    registered = registerExport[path, decoded["Identity"], written, bindings, subgroupClassWitnesses[decoded["Data"]],
        groupRecordsStatus[groupData[group]], groupVerificationStatus[groupData[group]]];
    If[FailureQ[registered], Failure[registered[[1]], Join[registered[[2]], <|"SavedFile" -> path|>]], path]
];
SaveGroupData[___] := makeFailure["InvalidSnapshot", "Expected a live Group and snapshot filename."];

True
