(*
    :Title: Retained GAP cache ownership and eviction
    :Context: VVMFTool`Private`
    :Summary: Index immutable managed checkpoints and protect active readers with leases.
    :Responsibilities: Local cache authority, cross-kernel transactions and least-use cleanup.
    :Dependencies: ManagedFiles.wl; ArtifactIO.wl; OwnedProcesses.wl.
    :See Also: CheckpointStorage.wl; VVMFArch/step1Plan.md.
*)

(* Fixed names are the complete set owned inside each immutable cache entry. The
   index is package-local admission evidence; a portable manifest is not authority. *)
$CacheArtifactNames = <|"ResultArtifact" -> "result.json",
    "WorkspaceArtifact" -> "state.wsp", "ManifestArtifact" -> "manifest.json"|>;
$CacheIndexName = ".vvmf-cache.json";

(*
    Summary: Check an optional resumable-construction record of a cache entry.
    Parameters: resume — arbitrary expression.
    Options/defaults: None. Claim is Null or one kernel-identified claimant, like a lease.
    Returns: Boolean.
    Effects: Pure.
    Failures: Missing/extra fields, a non-SHA256 key, complete status or malformed claim fail.
    Example: a Conlon-partial SL(2,3) entry has Status -> "Partial" and Claim -> Null.
    Remarks: Only failed builds mark entries resumable; complete states are never resumed.
    See also: cacheEntryQ; claimResumableCheckpoint; publishCheckpoint.
*)
cacheResumeQ[resume_] := resultFieldsQ[resume,
    {"Key", "StateID", "GeneratorIdentity", "StateGeneration", "Status", "Claim"}] &&
    StringQ[resume["Key"]] && StringLength[resume["Key"]] === 64 &&
    StringMatchQ[resume["Key"], HexadecimalCharacter ..] &&
    AllTrue[{resume["StateID"], resume["GeneratorIdentity"]}, StringQ[#] && StringLength[#] > 0 &] &&
    IntegerQ[resume["StateGeneration"]] && resume["StateGeneration"] >= 0 &&
    MemberQ[{"BaseReady", "Partial"}, resume["Status"]] &&
    (resume["Claim"] === Null || (resultFieldsQ[resume["Claim"], {"Token", "PID", "Host", "Started"}] &&
        StringQ[resume["Claim"]["Token"]] && StringLength[resume["Claim"]["Token"]] > 0 &&
        IntegerQ[resume["Claim"]["PID"]] && resume["Claim"]["PID"] > 0 &&
        StringQ[resume["Claim"]["Host"]] && StringQ[resume["Claim"]["Started"]]));

(*
    Summary: Check one persistent cache entry's exact metadata schema.
    Parameters: entry — arbitrary expression.
    Options/defaults: None; timestamps are integer milliseconds since Wolfram's epoch.
    Returns: Boolean.
    Effects: Pure; hashes are only syntax-checked here.
    Failures: Extra/missing fields, invalid digests, sizes, timestamps or lease identities fail.
    Example: metadata with a path in place of a fixed artifact key is rejected.
    See also: readCacheIndex; cacheEntryFiles.
*)
cacheEntryQ[entry_] := (resultFieldsQ[entry,
    {"Runtime", "Artifacts", "Created", "LastUsed", "Leases", "PendingEviction"}] ||
    (resultFieldsQ[entry, {"Runtime", "Artifacts", "Created", "LastUsed", "Leases",
        "PendingEviction", "Resume"}] && cacheResumeQ[entry["Resume"]])) &&
    StringQ[entry["Runtime"]] && StringMatchQ[entry["Runtime"], HexadecimalCharacter ..] &&
    StringLength[entry["Runtime"]] === 64 &&
    resultFieldsQ[entry["Artifacts"], Keys[$CacheArtifactNames]] &&
    AllTrue[Values[entry["Artifacts"]], resultFieldsQ[#, {"SHA256", "Bytes"}] &&
        StringQ[#["SHA256"]] && StringLength[#["SHA256"]] === 64 &&
        StringMatchQ[#["SHA256"], HexadecimalCharacter ..] &&
        IntegerQ[#["Bytes"]] && #["Bytes"] > 0 &] &&
    IntegerQ[entry["Created"]] && IntegerQ[entry["LastUsed"]] &&
    0 <= entry["Created"] <= entry["LastUsed"] &&
    MemberQ[{True, False}, entry["PendingEviction"]] && AssociationQ[entry["Leases"]] &&
    resultIDsQ[Keys[entry["Leases"]]] &&
    AllTrue[Values[entry["Leases"]], resultFieldsQ[#, {"PID", "Host", "Started"}] &&
        IntegerQ[#["PID"]] && #["PID"] > 0 && StringQ[#["Host"]] &&
        StringQ[#["Started"]] && StringLength[#["Started"]] > 0 &];

(*
    Summary: Read and validate the local cache index without discovering arbitrary files.
    Parameters: root — canonical existing cache directory.
    Options/defaults: None; callers hold its storage lock for transactions.
    Returns: Exact index association or InvalidCacheIndex/other storage Failure.
    Effects: Reads the one fixed index file; never loads a binary workspace.
    Failures: Unknown schema, unsafe index path and invalid entries are preserved and reported.
    Example: an unindexed workspace beside the index never becomes a cleanup candidate.
    See also: ensureCacheStore; writeCacheIndex.
*)
readCacheIndex[root_String] := Module[{path, index},
    path = managedPath[root, {$CacheIndexName}];
    If[FailureQ[path], Return[path]];
    index = readResult[path];
    If[FailureQ[index], Return[index]];
    If[!resultFieldsQ[index, {"SchemaVersion", "Kind", "CacheID", "Entries"}] ||
        index["SchemaVersion"] =!= 1 || index["Kind"] =!= "VVMFToolGAPCache" ||
        !StringQ[index["CacheID"]] || StringLength[index["CacheID"]] === 0 ||
        !AssociationQ[index["Entries"]] ||
        !AllTrue[Keys[index["Entries"]], StringQ[#] &&
            StringMatchQ[#, "entry-" ~~ (HexadecimalCharacter | "-") ..] &] ||
        !AllTrue[Values[index["Entries"]], cacheEntryQ],
        makeFailure["InvalidCacheIndex", "The local cache index has an invalid schema."], index]
];
readCacheIndex[___] := makeFailure["InvalidCacheIndex", "Expected a canonical cache root."];

(*
    Summary: Atomically replace a cache index during an owned transaction.
    Parameters: root — canonical locked root; index — validated or internally formed index.
    Options/defaults: None; caller establishes the schema and holds withStoreLock.
    Returns: Artifact record or storage Failure.
    Effects: Writes only the fixed index file; does not alter workspace files.
    Failures: Unsafe path or atomic writer failure preserves the preceding index.
    Example: failed lease publication does not grant permission to use a checkpoint.
    See also: readCacheIndex; writeResult.
*)
writeCacheIndex[root_String, index_Association] := Module[{path = managedPath[root, {$CacheIndexName}]},
    If[FailureQ[path], path, writeResult[path, index]]
];
writeCacheIndex[___] := makeFailure["InvalidCacheIndex", "Expected root and index."];

(*
    Summary: Open or initialize the explicitly configured managed cache store.
    Parameters: directory — absolute directory, normally the configured CacheDirectory.
    Options/defaults: Missing directories and the index are created on this explicit operation.
    Returns: Canonical root or Failure; loading the package never calls this function.
    Effects: Creates metadata under a short cross-kernel lock, preserving unrelated files.
    Failures: Existing invalid indexes are not overwritten; ownership and I/O errors propagate.
    Example: ensureCacheStore[configuredDirectory] leaves unindexed notebooks untouched.
    See also: readCacheIndex; CleanGAPCache.
*)
ensureCacheStore[directory_String] := Module[{root, result},
    root = managedRoot[directory, True];
    If[FailureQ[root], Return[root]];
    result = withStoreLock[root, Module[{path, index, saved},
        path = managedPath[root, {$CacheIndexName}];
        If[FailureQ[path], Return[path]];
        If[FileExistsQ[path], readCacheIndex[root],
            index = <|"SchemaVersion" -> 1, "Kind" -> "VVMFToolGAPCache",
                "CacheID" -> CreateUUID["cache-"], "Entries" -> <||>|>;
            saved = writeCacheIndex[root, index];
            If[FailureQ[saved], saved, index]]
    ]];
    If[FailureQ[result], result, root]
];
ensureCacheStore[___] := makeFailure["InvalidStorageRoot", "Expected an absolute cache directory."];

(*
    Summary: Inspect exactly the fixed files of an indexed cache entry.
    Parameters: root — canonical root; id — an entry key in a validated local index.
    Options/defaults: Missing files are allowed for cleanup recovery; extra content is not.
    Returns: Directory, Files association and current Bytes, or CacheEntryConflict Failure.
    Effects: Inspects paths and file sizes without following internal symbolic links.
    Failures: Links, unexpected children, wrong file types or failed byte reads prevent deletion.
    Example: a user-added file inside an entry preserves the entire entry and reports a conflict.
    See also: cacheEntries; removeCacheEntryFiles.
*)
cacheEntryFiles[root_String, id_String] := Module[{directory, paths, present, sizes},
    directory = managedPath[root, {id}];
    If[FailureQ[directory], Return[directory]];
    If[FileExistsQ[directory] && !DirectoryQ[directory],
        Return[makeFailure["CacheEntryConflict", "An indexed entry is no longer a directory."]]];
    paths = (managedPath[root, {id, #}] &) /@ $CacheArtifactNames;
    If[AnyTrue[Values[paths], FailureQ], Return[First[Select[Values[paths], FailureQ]]]];
    If[DirectoryQ[directory] && Complement[FileNames[All, directory], Values[paths]] =!= {},
        Return[makeFailure["CacheEntryConflict", "An indexed cache entry contains unowned files.",
            <|"Directory" -> directory|>]]];
    present = Select[Values[paths], FileExistsQ];
    If[!AllTrue[present, FileType[#] === File &],
        Return[makeFailure["CacheEntryConflict", "An owned artifact is no longer a regular file."]]];
    sizes = Check[FileByteCount /@ present, $Failed];
    If[!ListQ[sizes] || !AllTrue[sizes, IntegerQ],
        Return[makeFailure["ReadFailed", "Cannot measure managed cache entries."]]];
    <|"Directory" -> directory, "Files" -> paths, "Bytes" -> Total[sizes]|>
];
cacheEntryFiles[___] := makeFailure["CacheEntryConflict", "Expected root and indexed entry ID."];

(*
    Summary: Remove only the enumerated owned artifacts and then their empty entry directory.
    Parameters: root — canonical locked root; id — indexed, unleased entry ID.
    Options/defaults: No recursive deletion. Caller has durably marked PendingEviction.
    Returns: True or storage Failure, with remaining files available for a later cleanup retry.
    Effects: Deletes fixed files after a fresh containment/content check.
    Failures: Any changed ownership or deletion error stops the operation.
    Example: an already missing workspace can be cleaned together with its surviving manifest.
    See also: cacheEntryFiles; cleanCacheStore.
*)
removeCacheEntryFiles[root_String, id_String] := Module[{files, result},
    files = cacheEntryFiles[root, id];
    If[FailureQ[files], Return[files]];
    result = Check[
        Scan[If[FileExistsQ[#], DeleteFile[#]] &, Values[files["Files"]]];
        If[DirectoryQ[files["Directory"]], DeleteDirectory[files["Directory"]]];
        True, $Failed];
    If[result === $Failed, makeFailure["CleanupFailed", "Cannot remove an owned cache entry."], True]
];
removeCacheEntryFiles[___] := makeFailure["CleanupFailed", "Expected root and indexed entry ID."];

(*
    Summary: Preserve live/uncertain leases and prune only demonstrably ended local kernels.
    Parameters: leases — validated lease association; snapshot — processSnapshot list or Failure.
    Options/defaults: A remote host or failed inspection is conservatively treated as active.
    Returns: Subset of the supplied leases.
    Effects: Pure; the caller persists changes while holding the index lock.
    Failures: Inspection failure does not authorize deletion; PID start identity avoids reuse.
    Example: a dead local kernel's lease is removed; a Dropbox peer's lease is preserved.
    See also: acquireCacheLease; processSnapshot.
*)
activeCacheLeases[leases_Association, snapshot_] := Select[leases,
    #["Host"] =!= $MachineName || FailureQ[snapshot] ||
        AnyTrue[snapshot, Function[process,
            process["PID"] === #["PID"] && process["Started"] === #["Started"]]] &
];

(*
    Summary: List only locally indexed entries with their actual size and active lease state.
    Parameters: root — canonical cache root; index — validated local index held under its lock.
    Options/defaults: None; one shared process snapshot serves all entries.
    Returns: Entry records, each with ID, metadata, Bytes and Inspection (possibly a Failure).
    Effects: Reads filesystem and processes. Does not mutate index or mathematical objects.
    Failures: A bad entry is reported in its record; its recorded size remains in cap accounting.
    Example: unrelated files outside indexed entries are absent from the returned list.
    See also: selectEvictions; cleanCacheStore.
*)
cacheEntries[root_String, index_Association] := Module[{snapshot = processSnapshot[]},
    KeyValueMap[Function[{id, metadata}, Module[{entry = metadata, inspection},
        entry["Leases"] = activeCacheLeases[entry["Leases"], snapshot];
        inspection = cacheEntryFiles[root, id];
        <|"ID" -> id, "Metadata" -> entry, "Inspection" -> inspection,
            "Bytes" -> If[FailureQ[inspection],
                Total[Lookup[Values[entry["Artifacts"]], "Bytes"]], inspection["Bytes"]]|>
    ]], index["Entries"]]
];
cacheEntries[root_String] := withStoreLock[root, Module[{index = readCacheIndex[root]},
    If[FailureQ[index], index, cacheEntries[root, index]]
]];
cacheEntries[___] := makeFailure["InvalidCacheIndex", "Expected a canonical cache root."];

(*
    Summary: Choose pending and oldest-used entries until removable bytes meet a cap.
    Parameters: entries — inspected cacheEntries list; cap — nonnegative integer byte limit or All.
    Options/defaults: All selects every entry. Stable ID breaks equal timestamp ties.
    Returns: Selected entry records ordered by LastUsed and ID.
    Effects: Pure; leased/conflicted selections cannot reduce immediately removable bytes.
    Failures: Caller establishes entry schema; invalid cap/list arguments return Failure.
    Example: a leased oldest entry is deferred while younger unleased entries can meet the cap.
    See also: cleanCacheStore; CleanGAPCache.
*)
selectEvictions[entries_List, cap : (All | _Integer)] := Module[{remaining, selected = {}, sorted},
    If[IntegerQ[cap] && cap < 0, Return[makeFailure["InvalidCacheCap", "The cache cap cannot be negative."]]];
    remaining = Total[Lookup[entries, "Bytes"]];
    sorted = SortBy[entries, {#["Metadata"]["LastUsed"], #["ID"]} &];
    Do[
        If[cap === All || remaining > cap || TrueQ[entry["Metadata"]["PendingEviction"]],
            AppendTo[selected, entry];
            If[entry["Metadata"]["Leases"] === <||> && !FailureQ[entry["Inspection"]],
                remaining -= entry["Bytes"]]], {entry, sorted}];
    selected
];
selectEvictions[___] := makeFailure["InvalidCacheCap", "Expected entries and a nonnegative byte cap or All."];

(*
    Summary: Publish eviction intent, remove unleased owned entries and report deferred work.
    Parameters: root — canonical cache root; cap — nonnegative bytes or All.
    Options/defaults: Only indexed workspace/result/manifest files count toward the cap.
    Returns: Deleted, Deferred, Failed, RemainingBytes and CapMet report, or index I/O Failure.
    Effects: Serializes index updates/deletion; never changes in-memory mathematical data.
    Failures: Conflicts stay indexed and reported; failed index publication precedes no deletion.
    Example: CleanGAPCache["All"] defers a leased snapshot until releaseCacheLease.
    See also: selectEvictions; removeCacheEntryFiles; releaseCacheLease.
*)
cleanCacheStore[root_String, cap : (All | _Integer)] := withStoreLock[root, Module[
    {index, entries, selected, metadata, saved, deleted = {}, deferred = {}, failed = <||>, removed,
        remaining, ids, inspection},
    If[IntegerQ[cap] && cap < 0, Return[makeFailure["InvalidCacheCap", "The cache cap cannot be negative."]]];
    index = readCacheIndex[root]; If[FailureQ[index], Return[index]];
    entries = cacheEntries[root, index]; selected = selectEvictions[entries, cap];
    ids = Lookup[selected, "ID"];
    Do[
        metadata = entry["Metadata"];
        If[MemberQ[ids, entry["ID"]], metadata["PendingEviction"] = True];
        AssociateTo[index["Entries"], entry["ID"] -> metadata], {entry, entries}];
    saved = writeCacheIndex[root, index]; If[FailureQ[saved], Return[saved]];
    (* Once intent is published, new leases cannot enter selected generations. *)
    Do[
        Which[
            entry["Metadata"]["Leases"] =!= <||>, AppendTo[deferred, entry["ID"]],
            FailureQ[entry["Inspection"]], AssociateTo[failed, entry["ID"] -> entry["Inspection"]],
            True,
            removed = removeCacheEntryFiles[root, entry["ID"]];
            If[FailureQ[removed], AssociateTo[failed, entry["ID"] -> removed],
                AppendTo[deleted, entry["ID"]]; KeyDropFrom[index["Entries"], entry["ID"]]]
        ], {entry, selected}];
    saved = writeCacheIndex[root, index];
    If[FailureQ[saved], Return[makeFailure["CleanupFailed", "Files were cleaned but index update failed.",
        <|"Deleted" -> deleted, "Cause" -> saved|>]]];
    remaining = Total[Map[Function[entry,
        inspection = cacheEntryFiles[root, entry["ID"]];
        If[FailureQ[inspection], entry["Bytes"], inspection["Bytes"]]
    ], Select[entries, !MemberQ[deleted, #["ID"]] &]]];
    <|"Deleted" -> deleted, "Deferred" -> deferred, "Failed" -> failed,
        "RemainingBytes" -> remaining, "CapMet" -> If[cap === All,
            index["Entries"] === <||>, remaining <= cap]|>
]];
cleanCacheStore[___] := makeFailure["InvalidCacheCap", "Expected cache root and byte cap or All."];

(*
    Summary: Acquire a durable lease before inspecting or loading a retained checkpoint.
    Parameters: root — configured canonical store; cacheID — matching local index identity;
        id — previously published entry identity.
    Options/defaults: None; leases are identified by fresh nonces and local kernel start time.
    Returns: Root/CacheID/EntryID/Token/Entry record, or MissingCheckpoint/CacheEvicting Failure.
    Effects: Records a reader in the index without yet touching or executing workspace bytes.
    Failures: Unknown/replaced stores, pending eviction and failed process/index inspection.
    Example: cleanup in another kernel sees the lease before GAP receives a -L argument.
    See also: releaseCacheLease; admitCheckpoint.
*)
acquireCacheLease[root_String, cacheID_String, id_String] := withStoreLock[root, Module[
    {index, entry, snapshot, owner, token, saved},
    index = readCacheIndex[root]; If[FailureQ[index], Return[index]];
    If[index["CacheID"] =!= cacheID || !KeyExistsQ[index["Entries"], id],
        Return[makeFailure["MissingCheckpoint", "No matching managed cache entry exists."]]];
    entry = index["Entries"][id];
    If[TrueQ[entry["PendingEviction"]], Return[makeFailure["CacheEvicting", "The checkpoint is queued for cleanup."]]];
    snapshot = processSnapshot[]; If[FailureQ[snapshot], Return[snapshot]];
    owner = Select[snapshot, #["PID"] === $ProcessID &];
    If[Length[owner] =!= 1, Return[makeFailure["ProcessInspectionFailed", "Cannot identify the leasing kernel."]]];
    token = CreateUUID["lease-"];
    AssociateTo[entry["Leases"], token -> <|"PID" -> $ProcessID, "Host" -> $MachineName,
        "Started" -> First[owner]["Started"]|>];
    AssociateTo[index["Entries"], id -> entry];
    saved = writeCacheIndex[root, index];
    If[FailureQ[saved], saved, <|"Root" -> root, "CacheID" -> cacheID,
        "EntryID" -> id, "Token" -> token, "Entry" -> entry|>]
]];
acquireCacheLease[___] := makeFailure["InvalidCacheLease", "Expected cache root and identities."];

(*
    Summary: Release a caller's exact lease and finish its deferred eviction when it is last.
    Parameters: lease — record returned by acquireCacheLease; used — successful save/restore flag.
    Options/defaults: used defaults False; True advances LastUsed only after verified success.
    Returns: Released/Deleted report or storage Failure.
    Effects: Removes only the recorded nonce, optionally deletes pending entry; no group mutation.
    Failures: Unknown lease/store is rejected. Failed cleanup remains pending for a later retry.
    Example: the final reader release completes an earlier CleanGAPCache["All"] request.
    See also: cleanCacheStore; acquireCacheLease.
*)
releaseCacheLease[lease_Association, used_ : False] := Module[{root},
    If[!ContainsAll[Keys[lease], {"Root", "CacheID", "EntryID", "Token"}] ||
        !AllTrue[Lookup[lease, {"Root", "CacheID", "EntryID", "Token"}], StringQ] ||
        !MemberQ[{True, False}, used],
        Return[makeFailure["InvalidCacheLease", "Malformed cache lease."]]];
    root = lease["Root"];
    withStoreLock[root, Module[{index, entry, saved, removed = False},
        index = readCacheIndex[root]; If[FailureQ[index], Return[index]];
        If[index["CacheID"] =!= lease["CacheID"] || !KeyExistsQ[index["Entries"], lease["EntryID"]],
            Return[makeFailure["InvalidCacheLease", "The leased entry no longer belongs to this store."]]];
        entry = index["Entries"][lease["EntryID"]];
        If[!KeyExistsQ[entry["Leases"], lease["Token"]],
            Return[makeFailure["InvalidCacheLease", "The lease has already ended or was never acquired."]]];
        KeyDropFrom[entry["Leases"], lease["Token"]];
        If[TrueQ[used], entry["LastUsed"] = Max[entry["LastUsed"], Round[1000 AbsoluteTime[]]]];
        AssociateTo[index["Entries"], lease["EntryID"] -> entry];
        saved = writeCacheIndex[root, index]; If[FailureQ[saved], Return[saved]];
        If[TrueQ[entry["PendingEviction"]] && entry["Leases"] === <||>,
            removed = removeCacheEntryFiles[root, lease["EntryID"]];
            If[FailureQ[removed], Return[Failure[removed[[1]],
                Join[removed[[2]], <|"LeaseReleased" -> True|>]]]];
            KeyDropFrom[index["Entries"], lease["EntryID"]];
            saved = writeCacheIndex[root, index];
            If[FailureQ[saved], Return[Failure[saved[[1]],
                Join[saved[[2]], <|"LeaseReleased" -> True|>]]]]
        ];
        <|"Released" -> True, "Deleted" -> TrueQ[removed]|>
    ]]
];
releaseCacheLease[___] := makeFailure["InvalidCacheLease", "Expected an acquired cache lease."];

Options[CleanGAPCache] = {MaxBytes -> 10^9};
(*
    Summary: Remove least-recently-used managed GAP checkpoints within the configured store.
    Signatures: CleanGAPCache[opts]; CleanGAPCache["All", opts].
    Status: Alpha.
    Parameters: "All" requests removal of every eligible retained entry.
    Options/defaults: MaxBytes -> 10^9, a nonnegative byte cap, ignored in All mode.
    Returns: Deleted/Deferred/Failed IDs, RemainingBytes and CapMet, or Failure.
    Effects: Removes only indexed checkpoint artifacts; active leases defer removal to release.
    Failures: Invalid options, unavailable storage and index failures are explicit; entry errors
        are reported without destroying other entries or accepted mathematical data.
    Example: CleanGAPCache[MaxBytes -> 0] evicts unleased managed checkpoints.
    See also: StoreGAPState; CacheDirectory; RestoreGAPState.
*)
CleanGAPCache[options : OptionsPattern[]] := cleanGAPCachePublic[False, {options}];
CleanGAPCache["All", options : OptionsPattern[]] := cleanGAPCachePublic[True, {options}];
CleanGAPCache[___] := makeFailure["InvalidInput", "Expected cleanup options, optionally preceded by All as a string."];

(*
    Summary: Resolve both public cache-cleanup forms through one validated transaction.
    Parameters: all — Boolean chosen by the public overload; options — option rule list.
    Options/defaults: Uses CleanGAPCache's MaxBytes and configured CacheDirectory.
    Returns: cleanCacheStore report or Failure.
    Effects: May initialize the configured cache store, then performs requested cleanup.
    Failures: Unsupported options fail before storage creation.
    Example: cleanGAPCachePublic[False, {MaxBytes -> 1000}] validates the cap before cleanup.
    See also: CleanGAPCache; validateOptions.
*)
cleanGAPCachePublic[all_, options_List] := Module[{supplied, checked, root},
    supplied = Association[Reverse[Flatten[options]]];
    checked = validateOptions["CleanGAPCache", supplied];
    If[FailureQ[checked], Return[checked]];
    root = ensureCacheStore[$Configuration[CacheDirectory]];
    If[FailureQ[root], root,
        cleanCacheStore[root, If[TrueQ[all], All,
            OptionValue[CleanGAPCache, options, MaxBytes]]]]
];

True
