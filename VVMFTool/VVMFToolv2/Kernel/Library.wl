(*
    :Title: The VVMF library of computed groups
    :Context: VVMFTool`Private`
    :Summary: Groups computed in the VVMFUse project, shipped with the package in Library/ (index, group snapshots with
        their labels, and a package-owned read-only ledger), loaded without GAP by LoadGroup (uxUpdatePlan.md 5, U10).
    :Responsibilities: libraryIndex, libraryLedgerTrust, libraryLedgerBindings; LoadGroup, LibraryGroups.
    :Dependencies: ExportLedger.wl (readExportLedger, validExportIdentityQ); GroupStorage.wl (ImportGroupData);
        GroupObject.wl (announceGroup, commitGroup).
    :See Also: Tools/UpdateLibrary.wls (builds the library from VVMFUse); Schemas/GroupSnapshot.md.
*)

(* The library and its ledger live in the package; tests localize these paths to temporary copies. *)
If[!StringQ[$LibraryDirectory], $LibraryDirectory = FileNameJoin[{$PackageRoot, "Library"}]];
If[!StringQ[$LibraryLedgerDirectory], $LibraryLedgerDirectory = FileNameJoin[{$LibraryDirectory, "ledger"}]];

(*
    Summary: Whether the package's library ledger registers a saved group's bytes and identities.
    Parameters: artifact — <|"File", "SHA256", "Bytes"|> of the file read; identity — its decoded identity record.
    Options/defaults: None.
    Returns: True or False (a missing or unreadable library ledger gives False).
    Effects: Reads Library/ledger/ledger.json (never writes it).
    Failures: None.
    Example: an unchanged library file is trusted; a changed byte makes it untrusted (full validation with GAP).
    Remarks: The repository is a trusted source like the package code itself (user decision D5): the update script is
        the only writer of this ledger, and the package treats a match exactly like a match in the user's own ledger.
    See also: trustedExportRecord; LoadGroup.
*)
libraryLedgerTrust[artifact_Association, identity_Association] := Module[{root, ledger, entry},
    If[!StringQ[$LibraryLedgerDirectory] || !DirectoryQ[$LibraryLedgerDirectory], Return[False]];
    root = managedRoot[$LibraryLedgerDirectory]; If[FailureQ[root], Return[False]];
    ledger = Quiet[readExportLedger[root]]; If[FailureQ[ledger], Return[False]];
    entry = Lookup[ledger["Entries"], artifact["SHA256"], Missing["Unregistered"]];
    !MissingQ[entry] && entry["Bytes"] === artifact["Bytes"] && canonicalJSON[entry["Identity"]] === canonicalJSON[identity]
];
libraryLedgerTrust[___] := False;

(*
    Summary: The identity bindings registered in the library ledger (for identity conflict checks).
    Parameters: None.
    Options/defaults: None.
    Returns: List of binding associations ({} without a library ledger).
    Effects: Reads the library ledger.
    Failures: None.
    Example: libraryLedgerBindings[] has one entry per library group.
    See also: checkKnownGroupIdentities.
*)
libraryLedgerBindings[] := Module[{root, ledger},
    If[!StringQ[$LibraryLedgerDirectory] || !DirectoryQ[$LibraryLedgerDirectory], Return[{}]];
    root = managedRoot[$LibraryLedgerDirectory]; If[FailureQ[root], Return[{}]];
    ledger = Quiet[readExportLedger[root]]; If[FailureQ[ledger], Return[{}]];
    Lookup[Values[ledger["Entries"]], "Bindings", {}]];

(*
    Summary: The library index.
    Parameters: None.
    Options/defaults: None.
    Returns: Association label -> entry (<|"file", "gapID", "title", "titlePlain", "order", "irreps", "representations",
        "cgPairs", "slowPairs", "status", "sourceDigest", "updated"|>), or Failure.
    Effects: Reads Library/index.json.
    Failures: LibraryUnavailable.
    Example: KeyExistsQ[libraryIndex[], "24-3I"] is True.
    See also: LoadGroup; LibraryGroups.
*)
libraryIndex[] := Module[{path = FileNameJoin[{$LibraryDirectory, "index.json"}], index},
    If[!FileExistsQ[path], Return[makeFailure["LibraryUnavailable", "The group library is not installed (Library/index.json is missing)."]]];
    index = Quiet[Check[Import[path, "RawJSON"], $Failed]];
    If[!AssociationQ[index] || Lookup[index, "schemaVersion", None] =!= 1 || !AssociationQ[Lookup[index, "groups", None]],
        Return[makeFailure["LibraryUnavailable", "The library index is malformed."]]];
    index["groups"]];

Options[LoadGroup] = {Fresh -> False, Verification -> Automatic};

(*
    Summary: Load a computed group from the package's library.
    Status: Alpha.
    Signatures: LoadGroup[label]; LoadGroup[label, "Information"].
    Parameters: label — a library label such as "24-3I" (LibraryGroups[] lists them).
    Options/defaults: Fresh -> False (True loads a new copy even when the same group is already loaded); Verification ->
        Automatic (nothing is re-checked: the library holds verified data and the ledger binds the file; user decision
        2026-10-22, fastLoad.md) or "Exact" (a new copy, every record re-checked with GAP).
    Returns: The Group with everything VVMFUse computed (irreps in the paper's basis, S and T, CG coefficients, element
        words, labels of irreps and classes, title); with "Information" the library's index entry; or Failure.
    Effects: Reads the library file; registers the group (an ordinary live group: it can be extended and saved anywhere,
        never back into Library/). No GAP is started for an unchanged library file. A notice when the file holds CG entries
        that are not exactly verified (Tools/UpdateLibrary.wls refuses such groups).
    Failures: LibraryUnavailable; UnknownLibraryGroup; LibraryFileModified (a changed library file on a machine without
        GAP); import failures.
    Example: g = LoadGroup["24-3I"] displays as Group[24-3I]; LoadGroup["24-3I", "Information"]["status"] is "complete".
    Remarks: The library is built from VVMFUse by Tools/UpdateLibrary.wls (uxUpdatePlan.md 5).
    See also: LibraryGroups; ImportGroupData.
*)
LoadGroup[label_String, options : OptionsPattern[]] := Module[{effective, index, entry, file, existing, group, data},
    effective = resolveOperationOptions[LoadGroup, "LoadGroup", {options}]; If[FailureQ[effective], Return[effective]];
    index = libraryIndex[]; If[FailureQ[index], Return[index]];
    entry = Lookup[index, label, Missing[]];
    If[MissingQ[entry], Return[makeFailure["UnknownLibraryGroup", "The library has no group with this label; LibraryGroups[] lists them.", <|"Label" -> label|>]]];
    file = FileNameJoin[Prepend[FileNameSplit[entry["file"]], $LibraryDirectory]];
    If[!TrueQ[effective[Fresh]] && effective[Verification] =!= "Exact",
        existing = SelectFirst[Values[$GroupRegistry], Lookup[#, "LibrarySource", None] === entry["sourceDigest"] &, None];
        If[AssociationQ[existing], Return[Group[existing["InstanceID"]]]]];
    (* the library is verified when it is built: by default nothing is re-checked (fastLoad.md); "Exact" re-checks all *)
    group = ImportGroupData[file, Verification -> effective[Verification]];
    (* without GAP an unchanged file imports registered; a GAP failure means the file is not registered, unless the call
       asked for the full re-check, which needs GAP itself (review L1) *)
    If[FailureQ[group], Return[If[effective[Verification] =!= "Exact" && MemberQ[{"GAPUnavailable", "GAPNotFound"}, First[group]],
        makeFailure["LibraryFileModified", "The library file does not match the library ledger and GAP is not available to validate it.", <|"File" -> file|>], group]]];
    data = groupData[group];
    commitGroup[group, data["Revision"], <|"LibrarySource" -> entry["sourceDigest"],
        (* a library group is named by its library label (D1), also when the saved file carries none *)
        If[data["CatalogueLabel"] === None && catalogueLabelForQ[label, data], "CatalogueLabel" -> label, Nothing],
        "LastComputation" -> Join[data["LastComputation"], <|"Operation" -> "LoadGroup", "Library" -> label|>]|>];
    (* the library holds exactly verified data only; a file built with the opt-in for unverified CG entries says so: its
       Unverified entries are checked on their first use at a verifying level, Numerical ones when a call asks for
       "Exact" (fastLoad.md) *)
    With[{weak = Count[Values[data["CGCache"]["Entries"]], e_ /; cgEntryStatus[e] =!= "Exact"] +
            If[groupVerificationStatus[data] =!= "Exact", 1, 0] +
            Total[Map[Count[Values[Lookup[#, "Variants", <||>]], v_ /; variantVerificationStatus[v] =!= "Exact"] &, Values[data["Representations"]]]]},
        If[weak > 0, notice["Note: the library file of " <> label <> " holds " <> ToString[weak] <>
            " records (CG entries, representation variants or the character table) that are not exactly verified; unverified CG entries are checked when first used at a verifying level."]]];
    announceGroup[group]
];
LoadGroup[label_String, "Information"] := With[{index = libraryIndex[]}, If[FailureQ[index], index,
    Lookup[index, label, makeFailure["UnknownLibraryGroup", "The library has no group with this label.", <|"Label" -> label|>]]]];
LoadGroup[___] := makeFailure["InvalidInput", "LoadGroup expects a library label (LibraryGroups[] lists them) and options."];

(*
    Summary: The groups of the library.
    Status: Alpha.
    Parameters: None.
    Options/defaults: None.
    Returns: Dataset of label, title, GAP ID, order, irreps, computed representations, stored CG pairs, slow pairs and
        status, one row per group; or Failure.
    Effects: Reads the library index only.
    Failures: LibraryUnavailable.
    Example: LibraryGroups[][Select[#status == "complete" &]] lists the complete groups.
    See also: LoadGroup.
*)
LibraryGroups[] := With[{index = libraryIndex[]}, If[FailureQ[index], index,
    Dataset[KeyValueMap[<|"label" -> #1, "title" -> Lookup[#2, "titlePlain", ""], "GAP ID" -> Lookup[#2, "gapID", Missing[]],
        "order" -> #2["order"], "irreps" -> #2["irreps"], "representations" -> #2["representations"], "CG pairs" -> #2["cgPairs"],
        "slow pairs" -> #2["slowPairs"], "status" -> #2["status"]|> &, index]]]];
LibraryGroups[___] := makeFailure["InvalidInput", "LibraryGroups takes no arguments."];
