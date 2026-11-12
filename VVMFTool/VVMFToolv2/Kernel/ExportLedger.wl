(*
    :Title: Independent mathematical-export ledger
    :Context: VVMFTool`Private`
    :Summary: Recognize exact locally validated exports after computational cache eviction.
    :Responsibilities: Non-evictable local provenance, atomic registration and file-byte matching.
    :Dependencies: ManagedFiles.wl; ArtifactIO.wl; GroupObject.wl.
    :See Also: SaveGroupData; ImportGroupData; VVMFArch/step1Plan.md.
*)

(* This local provenance store is separate from CacheDirectory and is never a cache-cleanup
   candidate. Tests may dynamically localize the private path to their own temporary root. *)
If[!StringQ[$ExportLedgerDirectory], $ExportLedgerDirectory =
    FileNameJoin[{$UserBaseDirectory, "ApplicationData", "VVMFTool", "ExportLedger"}]];

(*
    Summary: Select portable mathematical identities for a locally validated exported group.
    Parameters: data — complete decoded group data whose provenance the caller establishes.
    Options/defaults: None.
    Returns: Exact JSON identity record or InvalidExportIdentity Failure.
    Effects: Pure; this function neither verifies provenance nor issues a receipt.
    Failures: Missing identities, incomplete characters or nonpositive order.
    Example: exportedGroupIdentity[data]["CharacterIdentity"] identifies its saved row/class IDs.
    See also: registerExport; groupEnvelope.
*)
exportedGroupIdentity[data_Association] := Module[{identity},
    If[Lookup[data, "Status", None] =!= "Complete" || !AssociationQ[Lookup[data, "CharacterData", None]],
        Return[makeFailure["InvalidExportIdentity", "A complete accepted group is required."]]];
    identity = <|"StateID" -> Lookup[data, "StateID", None],
        "GeneratorIdentity" -> Lookup[data, "GeneratorIdentity", None],
        "CharacterIdentity" -> Lookup[data["CharacterData"], "Identity", None],
        "Order" -> ToString[Lookup[data, "Order", None]]|>;
    If[validExportIdentityQ[identity], identity,
        makeFailure["InvalidExportIdentity", "The group has invalid export identities."]]
];
exportedGroupIdentity[___] := makeFailure["InvalidExportIdentity", "Expected complete group data."];

(*
    Summary: Check the exact independent-ledger mathematical identity schema.
    Parameters: identity — arbitrary expression.
    Options/defaults: None.
    Returns: Boolean; Order is a canonical positive decimal string.
    Effects: Pure; does not establish that identities describe a particular group.
    Failures: Malformed/extra fields or empty identities return False.
    Example: a zero order or missing CharacterIdentity is rejected.
    See also: exportedGroupIdentity; readExportLedger.
*)
validExportIdentityQ[identity_] := AssociationQ[identity] &&
    resultFieldsQ[identity, {"StateID", "GeneratorIdentity", "CharacterIdentity", "Order"}] &&
    AllTrue[Lookup[identity, {"StateID", "GeneratorIdentity", "CharacterIdentity"}],
        StringQ[#] && StringLength[#] > 0 &] &&
    With[{order = decodeInteger[identity["Order"]]}, IntegerQ[order] && order > 0];

(*
    Summary: Read the independent local ledger without trusting fields inside an imported file.
    Parameters: root — canonical package-owned ledger directory.
    Options/defaults: An absent index gives an empty schema-2 ledger with immutable bindings.
    Returns: Validated ledger or InvalidExportLedger/storage Failure.
    Effects: Reads only the fixed contained ledger.json; no executable workspace or source.
    Failures: Malformed schema, digests, byte counts, identities, timestamps or unsafe paths.
    Example: an empty ledger cannot recognize a file solely because that file has a hash field.
    See also: registerExport; trustedExportRecord; withStoreLock.
*)
readExportLedger[root_String] := Module[{path, ledger, entries},
    path = managedPath[root, {"ledger.json"}]; If[FailureQ[path], Return[path]];
    If[!FileExistsQ[path], Return[<|"SchemaVersion" -> 2, "Entries" -> <||>|>]];
    ledger = readResult[path]; If[FailureQ[ledger], Return[ledger]];
    If[!AssociationQ[ledger] || !resultFieldsQ[ledger, {"SchemaVersion", "Entries"}] ||
        ledger["SchemaVersion"] =!= 2 || !AssociationQ[ledger["Entries"]],
        Return[makeFailure["InvalidExportLedger", "The independent export ledger is malformed."]]];
    entries = ledger["Entries"];
    If[!AllTrue[Keys[entries], StringQ[#] && StringMatchQ[#, RegularExpression["[0-9a-f]{64}"]] &] ||
        !AllTrue[Values[entries], AssociationQ[#] && resultFieldsQ[KeyDrop[#, {"VerificationStatus", "GroupStatus"}], {"Bytes", "Identity", "Bindings", "SubgroupClasses", "RegisteredAt"}] &&
            (!KeyExistsQ[#, "VerificationStatus"] || verificationStatusQ[#["VerificationStatus"]]) &&
            (!KeyExistsQ[#, "GroupStatus"] || verificationStatusQ[#["GroupStatus"]]) &&
            IntegerQ[#["Bytes"]] && #["Bytes"] > 0 && validExportIdentityQ[#["Identity"]] &&
            validIdentityBindingsQ[#["Bindings"]] && validSubgroupClassWitnessesQ[#["SubgroupClasses"]] &&
            IntegerQ[#["RegisteredAt"]] &],
        Return[makeFailure["InvalidExportLedger", "An independent export entry is malformed."]]];
    ledger
];
readExportLedger[___] := makeFailure["InvalidExportLedger", "Expected the package-owned ledger root."];

(*
    Summary: Add one accepted digest to a ledger while its caller holds the storage lock.
    Parameters: root — owned canonical root; artifact/identity — validated saved records;
        bindings — immutable identity digests; classes — accepted subgroup-class witnesses; status — the weakest record
        of the file (default "Exact", not written); groupStatus — the group's own status (Automatic: status; "Exact" is
        not written), the level a registered file's group is read at (trustedExportStatus).
    Options/defaults: None; repeated registration preserves the same mathematical identity (the status is the latest).
    Returns: Artifact digest or explicit conflict/read/write Failure.
    Effects: Writes the local index atomically; caller owns locking and cleanup.
    Failures: Conflicting known identities or damaged/unwritable index remain failures.
    Example: registering identical bytes with a different CharacterIdentity is rejected.
    See also: registerExport; readExportLedger; writeResult.
*)
writeExportRegistration[root_String, artifact_Association, identity_Association, bindings_Association, classes_List, status_String : "Exact",
    groupStatus_ : Automatic] := Module[{ledger, prior, path, written, own = If[groupStatus === Automatic, status, groupStatus]},
    ledger = readExportLedger[root]; If[FailureQ[ledger], Return[ledger]];
    prior = Lookup[ledger["Entries"], artifact["SHA256"], Missing["Unregistered"]];
    If[!MissingQ[prior] && (prior["Bytes"] =!= artifact["Bytes"] ||
        canonicalJSON[prior["Identity"]] =!= canonicalJSON[identity]),
        Return[makeFailure["StateConflict", "These export bytes already have different registered identities."]]];
    (* the package library's bindings count too (uxUpdatePlan.md 5, review N10): a conflicting save fails here, not on import *)
    If[!AllTrue[Join[Lookup[Values[ledger["Entries"]], "Bindings", {}], libraryLedgerBindings[]], compatibleIdentityBindingsQ[bindings, #] &],
        Return[makeFailure["StateConflict", "An export cannot reassign known mathematical identities."]]];
    AssociateTo[ledger["Entries"], artifact["SHA256"] -> Join[<|"Bytes" -> artifact["Bytes"],
        "Identity" -> identity, "Bindings" -> Join[If[MissingQ[prior], <||>, prior["Bindings"]], bindings],
        "SubgroupClasses" -> DeleteDuplicates[Join[If[MissingQ[prior], {}, prior["SubgroupClasses"]], classes]],
        "RegisteredAt" -> Floor[AbsoluteTime[]]|>,
        (* the weakest record of the saved file, when weaker than Exact (methodOptionsPlan.md 2C.5) *)
        If[status === "Exact", <||>, <|"VerificationStatus" -> status|>],
        (* the group's own status, when weaker than Exact: a file's group is read at it, not at its weakest record *)
        If[own === "Exact", <||>, <|"GroupStatus" -> own|>]]];
    path = managedPath[root, {"ledger.json"}]; If[FailureQ[path], Return[path]];
    written = writeResult[path, ledger]; If[FailureQ[written], written, artifact]
];

(*
    Summary: Register exact saved bytes after the caller independently validates their mathematics.
    Parameters: file — saved absolute snapshot path; identity — exportedGroupIdentity record;
        expected — optional artifact digest from the atomic writer, or Automatic;
        bindings — immutable correspondence digests, default empty for identity-only private callers;
        classes — native-verified subgroup-class witnesses, default {}; status — the weakest record of the saved file
        ("Exact" by default; a weaker file is registered for its byte identity, methodOptionsPlan.md 2C.5); groupStatus —
        the group's own status (Automatic: status).
    Options/defaults: Production saves supply both the writer digest and complete bindings.
    Returns: Artifact digest association, or storage/identity/changed-file Failure.
    Effects: Creates the independent ledger when needed and atomically updates it under a lock.
    Failures: A changed saved file or failed ledger write is reported, never treated as trusted.
    Example: saving a group registers its SHA256 independently of the evictable GAP workspace.
    Remarks: This private boundary assumes already accepted mathematics. Never call it merely
        because imported fields claim validation or pass character orthogonality checks.
    See also: SaveGroupData; trustedExportRecord; writeResult.
*)
registerExport[file_String, identity_Association, expected_ : Automatic, bindings_ : <||>, classes_ : {}, status_ : "Exact",
    groupStatus_ : Automatic] := Module[{artifact, root},
    If[!validExportIdentityQ[identity] || !validIdentityBindingsQ[bindings] || !validSubgroupClassWitnessesQ[classes] || !verificationStatusQ[status] ||
        (groupStatus =!= Automatic && !verificationStatusQ[groupStatus]),
        Return[makeFailure["InvalidExportIdentity", "Invalid export identity or binding record."]]];
    artifact = fileDigest[file]; If[FailureQ[artifact], Return[artifact]];
    If[artifact["Bytes"] === 0 || (expected =!= Automatic && artifact =!= expected),
        Return[makeFailure["ExportChanged", "The snapshot bytes differ from the completed save."]]];
    root = managedRoot[$ExportLedgerDirectory, True]; If[FailureQ[root], Return[root]];
    withStoreLock[root, writeExportRegistration[root, artifact, identity, bindings, classes, status, groupStatus]]
];
registerExport[___] := makeFailure["InvalidExportIdentity", "Expected a saved file and accepted identities."];

(*
    Summary: Match previously read snapshot bytes to the independent local export ledger.
    Parameters: artifact — caller's stable File/SHA256/Bytes digest; identity — decoded snapshot identity.
    Options/defaults: None; no location or embedded digest in the snapshot chooses this ledger.
    Returns: True/False, or an explicit ledger/storage Failure.
    Effects: Reads the fixed independent local ledger; never creates storage or executes GAP.
    Failures: Missing ledger/digest returns False; unreadable or corrupt existing storage fails.
    Example: cache eviction leaves this lookup unchanged; a modified snapshot does not match.
    Remarks: Caller verifies its decoded data and this digest come from the same unchanged bytes.
    See also: trustedExportQ; ImportGroupData; fileDigest.
*)
trustedExportRecord[artifact_Association, identity_Association] := Module[{root, ledger, entry},
    If[!resultFieldsQ[artifact, {"File", "SHA256", "Bytes"}] || !validExportIdentityQ[identity] ||
        !StringQ[artifact["SHA256"]] || !IntegerQ[artifact["Bytes"]] || artifact["Bytes"] < 1,
        Return[makeFailure["InvalidExportIdentity", "Expected a saved-file digest and decoded identities."]]];
    (* the user's ledger first, then the package's read-only library ledger (uxUpdatePlan.md 5, D5) *)
    If[FileType[$ExportLedgerDirectory] === None, Return[libraryLedgerTrust[artifact, identity]]];
    root = managedRoot[$ExportLedgerDirectory]; If[FailureQ[root], Return[root]];
    ledger = readExportLedger[root]; If[FailureQ[ledger], Return[ledger]];
    entry = Lookup[ledger["Entries"], artifact["SHA256"], Missing["Unregistered"]];
    (!MissingQ[entry] && entry["Bytes"] === artifact["Bytes"] &&
        canonicalJSON[entry["Identity"]] === canonicalJSON[identity]) || libraryLedgerTrust[artifact, identity]
];
trustedExportRecord[___] := makeFailure["InvalidExportIdentity", "Expected exact artifact and identity records."];
(* The recorded group status of a registered file (methodOptionsPlan.md 2C.5): the user ledger's entry GroupStatus, for
   an older entry its VerificationStatus (the file's weakest record, never stronger), absent: "Exact"; the package
   library holds exact files only. The one place the ledger status is read for trust: a registered weak file's group
   imports at its recorded level (its variants and CG entries carry their own statuses). *)
trustedExportStatus[artifact_Association] := Module[{root, ledger},
    If[FileType[$ExportLedgerDirectory] === None, Return["Exact"]];
    root = managedRoot[$ExportLedgerDirectory]; If[FailureQ[root], Return["Exact"]];
    ledger = readExportLedger[root]; If[FailureQ[ledger], Return["Exact"]];
    With[{entry = Lookup[ledger["Entries"], Lookup[artifact, "SHA256", ""], <||>]},
        Lookup[entry, "GroupStatus", Lookup[entry, "VerificationStatus", "Exact"]]]];

(*
    Summary: Check a file against independently registered export bytes and identities.
    Parameters: file — absolute snapshot path; identity — the already decoded/checked identity record.
    Options/defaults: None; imports use trustedExportRecord with their stable read digest instead.
    Returns: True/False or explicit file/ledger Failure.
    Effects: Reads the file and local ledger only; never evaluates imported text.
    Failures: Changed bytes return False; invalid paths/identities or damaged ledger report Failure.
    Example: copying an export unchanged to another path still matches its registered bytes.
    See also: trustedExportRecord; registerExport; ImportGroupData.
*)
trustedExportQ[file_String, identity_Association] := Module[{artifact = fileDigest[file]},
    If[FailureQ[artifact], artifact, trustedExportRecord[artifact, identity]]
];
trustedExportQ[___] := makeFailure["InvalidExportIdentity", "Expected an export path and decoded identities."];

True
