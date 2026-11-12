(*
    :Title: Persistent verified checkpoint admission
    :Context: VVMFTool`Private`
    :Summary: Retain verified pairs and recover local authority under a durable reader lease.
    :Responsibilities: Checked copies, persistent publication and pre-execution admission.
    :Dependencies: GroupCache.wl; GAPWorkers.wl; ResultValidation.wl.
    :See Also: GroupStorage.wl; VVMFArch/step1Plan.md.
*)

(*
    Summary: Form the exact paired manifest shared by temporary and retained checkpoints.
    Parameters: record — verified/provisional native checkpoint with current artifact paths.
    Options/defaults: Schema version 1; caller supplies validated native and artifact records.
    Returns: Inert JSON manifest association.
    Effects: Pure; does not establish trust or write files.
    Failures: Caller establishes the record fields before invocation.
    Example: retaining a pair rewrites only artifact paths in its new manifest.
    See also: publishGAPCandidate; publishCheckpoint; admitCheckpoint.
*)
checkpointManifest[record_Association] := <|"schemaVersion" -> 1,
    "stateID" -> record["Native"]["stateID"],
    "generatorIdentity" -> record["Native"]["generatorIdentity"],
    "stateGeneration" -> record["Native"]["stateGeneration"],
    "requestID" -> record["Native"]["requestID"], "runtime" -> record["Runtime"],
    "result" -> record["ResultArtifact"], "workspace" -> record["WorkspaceArtifact"],
    "producer" -> record["Native"]["producer"]|>;

(*
    Summary: Copy one verified artifact to a new owned path and check the resulting bytes.
    Parameters: artifact — File/SHA256/Bytes from fileDigest; target — absent owned file path.
    Options/defaults: No overwrite; caller owns cleanup of a failed or interrupted copy.
    Returns: Copied artifact digest or SaveFailed/InvalidCheckpoint Failure.
    Effects: Copies and hashes the file without executing it.
    Failures: Copy/hash errors or changed source bytes cannot produce a successful artifact.
    Example: the original workspace remains available if retention fails midway.
    See also: publishCheckpoint; fileDigest.
*)
copyCheckpointArtifact[artifact_Association, target_String] := Module[{copied, observed},
    If[!resultFieldsQ[artifact, {"File", "SHA256", "Bytes"}] || !absolutePathQ[target] ||
        FileExistsQ[target], Return[makeFailure["SaveFailed", "Expected a verified artifact and new owned target."]]];
    copied = Check[CopyFile[artifact["File"], target], $Failed];
    If[copied === $Failed, Return[makeFailure["SaveFailed", "Cannot copy the checkpoint artifact."]]];
    observed = fileDigest[target];
    If[FailureQ[observed], Return[observed]];
    If[KeyDrop[observed, "File"] =!= KeyDrop[artifact, "File"],
        makeFailure["InvalidCheckpoint", "Checkpoint bytes changed during retention."], observed]
];
copyCheckpointArtifact[___] := makeFailure["SaveFailed", "Expected an artifact and owned target."];

(*
    Summary: Retain a kernel-verified checkpoint pair and publish local admission evidence.
    Parameters: reference — private verified checkpoint ID; capabilities — fresh GAP probe;
        resumeKey — None, or constructionResumeKey of a failed build's BaseReady/Partial state.
    Options/defaults: Uses the configured CacheDirectory; caller invokes only when StoreGAPState=True.
        With a resume key the entry is indexed as resumable by a later build of that construction.
    Returns: GAPCachePath/GAPCacheMetadata association or Failure; source remains intact.
    Effects: Copies immutable artifacts, writes a paired manifest, then indexes the generation.
    Failures: Any pre-publication error/abort removes this call's unfinished entry. An indexed
        generation survives cancellation and can be found by managed cleanup/recovery.
    Example: a retained partial generation can be resumed without publishing an incomplete Group.
    Remarks: Long file copies happen outside the short index lock. The index grants authority
        only after all copies match the already verified owned-worker bytes.
    See also: admitCheckpoint; cleanupCheckpoints; CleanGAPCache.
*)
publishCheckpoint[reference_String, capabilities_Association, resumeKey_ : None] := Module[
    {record, root, id, directory, files, retained, artifact, manifest, metadata, timestamp,
        published = False, created = False, result, cleanup = True, exitTag},
    record = checkpointRecord[reference, capabilities]; If[FailureQ[record], Return[record]];
    If[resumeKey =!= None && (!StringQ[resumeKey] ||
        !MemberQ[{"BaseReady", "Partial"}, record["Data"]["Status"]]),
        Return[makeFailure["InvalidCheckpoint", "Only a base or partial construction state can be resumable."]]];
    root = ensureCacheStore[$Configuration[CacheDirectory]]; If[FailureQ[root], Return[root]];
    id = CreateUUID["entry-"];
    directory = managedPath[root, {id}]; If[FailureQ[directory], Return[directory]];
    result = CheckAbort[Catch[Module[{index, saved},
        AbortProtect[
            created = StringQ[Check[CreateDirectory[directory], $Failed]]];
        If[!created, Throw[makeFailure["SaveFailed", "Cannot allocate the retained entry."], exitTag]];
        files = cacheEntryFiles[root, id]; If[FailureQ[files], Throw[files, exitTag]];
        retained = record;
        artifact = copyCheckpointArtifact[record["ResultArtifact"], files["Files"]["ResultArtifact"]];
        If[FailureQ[artifact], Throw[artifact, exitTag]]; retained["ResultArtifact"] = artifact;
        artifact = copyCheckpointArtifact[record["WorkspaceArtifact"], files["Files"]["WorkspaceArtifact"]];
        If[FailureQ[artifact], Throw[artifact, exitTag]]; retained["WorkspaceArtifact"] = artifact;
        manifest = checkpointManifest[retained];
        artifact = writeResult[files["Files"]["ManifestArtifact"], manifest];
        If[FailureQ[artifact], Throw[artifact, exitTag]]; retained["ManifestArtifact"] = artifact;
        timestamp = Round[1000 AbsoluteTime[]];
        metadata = <|"Runtime" -> record["Runtime"],
            "Artifacts" -> (KeyDrop[#, "File"] & /@ KeyTake[retained, Keys[$CacheArtifactNames]]),
            "Created" -> timestamp, "LastUsed" -> timestamp,
            "Leases" -> <||>, "PendingEviction" -> False|>;
        If[StringQ[resumeKey], metadata["Resume"] = <|"Key" -> resumeKey,
            "StateID" -> record["Data"]["StateID"], "GeneratorIdentity" -> record["Data"]["GeneratorIdentity"],
            "StateGeneration" -> record["Data"]["StateGeneration"], "Status" -> record["Data"]["Status"],
            "Claim" -> Null|>];
        withStoreLock[root, Module[{},
            index = readCacheIndex[root]; If[FailureQ[index], Throw[index, exitTag]];
            If[KeyExistsQ[index["Entries"], id], Throw[makeFailure["StateConflict", "The cache entry ID already exists."], exitTag]];
            AssociateTo[index["Entries"], id -> metadata];
            AbortProtect[
                saved = writeCacheIndex[root, index];
                If[!FailureQ[saved], published = True]
            ];
            If[FailureQ[saved], saved,
                <|"GAPCachePath" -> retained["WorkspaceArtifact"]["File"],
                    "GAPCacheMetadata" -> <|"Root" -> root, "CacheID" -> index["CacheID"],
                        "EntryID" -> id, "Runtime" -> record["Runtime"],
                        "StateID" -> record["Data"]["StateID"],
                        "GeneratorIdentity" -> record["Data"]["GeneratorIdentity"],
                        "StateGeneration" -> record["Data"]["StateGeneration"],
                        "LastUsed" -> timestamp|>|>]
        ]]
    ], exitTag], makeFailure["Cancelled", "Retaining the checkpoint was cancelled."]];
    If[created && !published, cleanup = removeCacheEntryFiles[root, id]];
    If[FailureQ[cleanup], makeFailure["CleanupFailed", "Retention failed and its temporary entry remains.",
        <|"Result" -> result, "Cleanup" -> cleanup, "Directory" -> directory|>], result]
];
publishCheckpoint[___] := makeFailure["MissingCheckpoint", "Expected a verified checkpoint reference and capabilities."];

(*
    Summary: Validate locally indexed bytes while a retained checkpoint is leased.
    Parameters: lease — acquireCacheLease result; metadata — stored group cache reference;
        capabilities — fresh probe record.
    Options/defaults: Exact native schema and current runtime/package compatibility are mandatory.
    Returns: A verified checkpoint record with CacheLease, or Failure before any -L execution.
    Effects: Reads/hashes fixed artifacts and parses inert JSON; does not start GAP.
    Failures: Missing/changed files, foreign metadata, invalid math, mismatched pair or runtime.
    Example: changing an imported path or embedded digest cannot authorize a workspace.
    Remarks: Provenance comes from the independent local index written by publishCheckpoint,
        not from rechecking orthogonality or believing manifest claims. A worker still reexports
        the restored native state before using it for further computation.
    See also: admitCheckpoint; checkpointRecord; advanceGAPAttempt.
*)
readLeasedCheckpoint[lease_Association, metadata_Association, capabilities_Association] := Module[
    {files, artifacts, expected, native, data, manifest, record, runtime, request},
    files = cacheEntryFiles[lease["Root"], lease["EntryID"]]; If[FailureQ[files], Return[files]];
    artifacts = fileDigest /@ files["Files"];
    If[AnyTrue[Values[artifacts], FailureQ], Return[First[Select[Values[artifacts], FailureQ]]]];
    expected = lease["Entry"]["Artifacts"];
    If[canonicalJSON[KeyDrop[#, "File"] & /@ artifacts] =!= canonicalJSON[expected],
        Return[makeFailure["InvalidCheckpoint", "The retained artifacts differ from the local admission index."]]];
    runtime = gapRuntimeFingerprint[capabilities]; If[FailureQ[runtime], Return[runtime]];
    If[runtime =!= lease["Entry"]["Runtime"] || runtime =!= metadata["Runtime"],
        Return[makeFailure["IncompatibleCheckpoint", "The checkpoint runtime has changed."]]];
    native = readResult[artifacts["ResultArtifact"]["File"]]; If[FailureQ[native], Return[native]];
    request = KeyTake[native, {"requestID", "stateID", "generatorIdentity", "stateGeneration", "operation"}];
    data = validateGroupResult[native, request]; If[FailureQ[data], Return[data]];
    If[KeyTake[data, {"StateID", "GeneratorIdentity", "StateGeneration"}] =!=
        KeyTake[metadata, {"StateID", "GeneratorIdentity", "StateGeneration"}] ||
        !compatibleGAPProducerQ[native["producer"], capabilities],
        Return[makeFailure["InvalidCheckpoint", "The retained state identities or producer do not match."]]];
    record = Join[artifacts, <|"Native" -> native, "Data" -> data, "Runtime" -> runtime,
        "Verified" -> True, "CacheLease" -> lease|>];
    manifest = readResult[artifacts["ManifestArtifact"]["File"]];
    If[canonicalJSON[manifest] =!= canonicalJSON[checkpointManifest[record]],
        makeFailure["InvalidCheckpoint", "The retained manifest does not name this exact artifact pair."], record]
];

(*
    Summary: Recover checkpoint authority from the configured local store under an active lease.
    Parameters: metadata — GAPCacheMetadata; capabilities — fresh GAP probe.
    Options/defaults: Only the currently configured canonical cache root may grant authority.
    Returns: New private checkpoint reference string or Failure; callers must release it.
    Effects: Acquires a lease, checks bytes, registers a kernel-local reference. Does not run GAP.
    Failures: Unknown/foreign stores, missing/incompatible/corrupt entries and cancellation release
        the lease before returning. Imported binary paths are never independently trusted.
    Example: after a fresh kernel load, admitCheckpoint[savedMetadata, CheckGAP[]] finds the index.
    See also: releaseCheckpoint; readLeasedCheckpoint; RestoreGAPState.
*)
admitCheckpoint[metadata_Association, capabilities_Association] := Module[
    {root, lease = None, record, reference = None, result, cleanup = True},
    If[!resultFieldsQ[metadata, {"Root", "CacheID", "EntryID", "Runtime", "StateID",
            "GeneratorIdentity", "StateGeneration", "LastUsed"}] ||
        !AllTrue[Lookup[metadata, {"Root", "CacheID", "EntryID", "Runtime", "StateID", "GeneratorIdentity"}], StringQ] ||
        !IntegerQ[metadata["StateGeneration"]] || metadata["StateGeneration"] < 0 ||
        !IntegerQ[metadata["LastUsed"]],
        Return[makeFailure["InvalidCheckpoint", "Malformed retained cache reference."]]];
    root = managedRoot[$Configuration[CacheDirectory]];
    If[FailureQ[root] || root =!= metadata["Root"],
        Return[makeFailure["MissingCheckpoint", "The referenced checkpoint is outside the configured local cache."]]];
    result = CheckAbort[
        AbortProtect[lease = acquireCacheLease[root, metadata["CacheID"], metadata["EntryID"]]];
        If[FailureQ[lease], lease,
            record = readLeasedCheckpoint[lease, metadata, capabilities];
            If[FailureQ[record], record,
                AbortProtect[
                    reference = CreateUUID["checkpoint-"];
                    AssociateTo[$GAPCheckpoints, reference -> record]
                ];
                reference
            ]
        ], makeFailure["Cancelled", "Checkpoint admission was cancelled."]];
    If[FailureQ[result],
        If[StringQ[reference], KeyDropFrom[$GAPCheckpoints, reference]];
        If[AssociationQ[lease], cleanup = releaseCacheLease[lease]]];
    If[FailureQ[cleanup], makeFailure["CleanupFailed", "Checkpoint admission failed and lease release failed.",
        <|"Result" -> result, "Cleanup" -> cleanup, "Lease" -> lease|>], result]
];
admitCheckpoint[___] := makeFailure["InvalidCheckpoint", "Expected cache metadata and capabilities."];

(*
    Summary: End a retained checkpoint's local authority and its durable reader lease.
    Parameters: reference — string returned by admitCheckpoint; used — successful restore flag.
    Options/defaults: used defaults False; pass True only after native restore verification.
    Returns: Lease release report or Failure; no mathematical data is removed.
    Effects: Releases persistent lease, finishes pending eviction, drops this local reference.
    Failures: Unknown/nonleased references are rejected; I/O failures leave the record for retry.
    Example: a failed attempt can release its source without changing that source's LastUsed.
    See also: releaseCacheLease; cleanupCheckpoints.
*)
releaseCheckpoint[reference_String, used_ : False] := Module[{record, released},
    record = Lookup[$GAPCheckpoints, reference, <||>];
    If[!KeyExistsQ[record, "CacheLease"], Return[makeFailure["InvalidCacheLease", "No retained lease matches this reference."]]];
    released = releaseCacheLease[record["CacheLease"], used];
    If[!FailureQ[released] || TrueQ[Lookup[released[[2]], "LeaseReleased", False]],
        KeyDropFrom[$GAPCheckpoints, reference]];
    released
];
releaseCheckpoint[___] := makeFailure["InvalidCacheLease", "Expected a leased checkpoint reference."];

(*
    Summary: Identify one failed construction for later resumption.
    Parameters: construction — validated construction record; modular — None or the requested
        S/T word record with name-based sWord/tWord syllables.
    Options/defaults: The fresh per-call assignment identity is excluded; its words are included.
    Returns: 64-digit lowercase SHA256 string.
    Effects: Pure.
    Failures: Callers supply validated records.
    Example: BuildGroup and BuildModularGroup of the same presentation have different keys.
    See also: claimResumableCheckpoint; publishCheckpoint.
*)
constructionResumeKey[construction_Association, modular_] := IntegerString[Hash[canonicalJSON[
    <|"construction" -> construction, "modular" -> If[AssociationQ[modular],
        KeyTake[modular, {"sWord", "tWord"}], Null]|>], "SHA256"], 16, 64];

(* Claims taken by builds still running in this kernel; a same-kernel claim absent here is stale. *)
If[!AssociationQ[$HeldResumeClaims], $HeldResumeClaims = <||>];

(*
    Summary: Test whether a live group in this kernel already carries a state identity.
    Parameters: stateID — string.
    Options/defaults: None.
    Returns: Boolean.
    Effects: Pure; reads $GroupRegistry.
    Failures: Nonstring input returns False.
    Example: after a resumed build publishes its group, its retained partial's StateID is live.
    See also: claimResumableCheckpoint; constructInCall.
*)
liveGroupStateQ[stateID_String] := AnyTrue[Values[$GroupRegistry], Lookup[#, "StateID", None] === stateID &];
liveGroupStateQ[___] := False;

(*
    Summary: Decide whether a recorded resume claim may be taken over.
    Parameters: claim — Null or recorded claimant; snapshot — processSnapshot list; self — this
        kernel's snapshot row.
    Options/defaults: None.
    Returns: True for no claim, a claim whose local owner process no longer exists, or a claim of
        this kernel that no running build here holds (left by an interrupted release).
    Effects: Pure; reads $HeldResumeClaims.
    Failures: Remote-host claims and live claims of other kernels return False.
    Example: an aborted build whose index write failed does not block its own kernel forever.
    See also: claimResumableCheckpoint; activeCacheLeases.
*)
resumeClaimFreeQ[claim_, snapshot_List, self_Association] := claim === Null ||
    activeCacheLeases[<|"claim" -> claim|>, snapshot] === <||> ||
    (claim["Host"] === $MachineName && claim["PID"] === self["PID"] &&
        claim["Started"] === self["Started"] && !KeyExistsQ[$HeldResumeClaims, claim["Token"]]);

(*
    Summary: Claim the most advanced resumable state of a construction in the configured store.
    Parameters: key — constructionResumeKey.
    Options/defaults: Unclaimed, dead-kernel or stale same-kernel claims only; highest generation,
        then newest entry. Entries whose StateID is a live group here are repaired, never claimed.
    Returns: None when nothing is resumable, else EntryID/Token/Root/Metadata where Metadata is
        the GAPCacheMetadata accepted by admitCheckpoint; or storage Failure.
    Effects: Records this kernel's claim in the index under the store lock; reads no workspace.
    Failures: Index/process inspection errors are returned; nothing is claimed on failure.
    Example: two kernels resuming the same failed SL(2,3) build cannot both claim one entry.
    Remarks: The claim excludes a second concurrent resume, which would publish two live
        groups with one StateID. Admission still verifies bytes, runtime and mathematics.
    See also: releaseResumeClaim; admitCheckpoint; buildFiniteGroup.
*)
claimResumableCheckpoint[key_String] := Module[{root},
    root = ensureCacheStore[$Configuration[CacheDirectory]]; If[FailureQ[root], Return[root]];
    withStoreLock[root, Module[{index, snapshot, owner, candidates, chosen, entry, token, saved, superseded},
        index = readCacheIndex[root]; If[FailureQ[index], Return[index]];
        snapshot = processSnapshot[]; If[FailureQ[snapshot], Return[snapshot]];
        owner = Select[snapshot, #["PID"] === $ProcessID &];
        If[Length[owner] =!= 1, Return[makeFailure["ProcessInspectionFailed", "Cannot identify the claiming kernel."]]];
        (* Repair entries a published group in this kernel already supersedes (a consume that
           could not be recorded): they are never resumable again. *)
        superseded = Select[Keys[index["Entries"]], With[{resume = Lookup[index["Entries"][#], "Resume", None]},
            AssociationQ[resume] && resume["Key"] === key && liveGroupStateQ[resume["StateID"]]] &];
        Do[entry = index["Entries"][id]; KeyDropFrom[entry, "Resume"]; entry["PendingEviction"] = True;
            AssociateTo[index["Entries"], id -> entry], {id, superseded}];
        If[superseded =!= {}, saved = writeCacheIndex[root, index]; If[FailureQ[saved], Return[saved]]];
        candidates = Select[Normal[index["Entries"]], Function[rule, With[{resume = Lookup[rule[[2]], "Resume", None]},
            AssociationQ[resume] && resume["Key"] === key && !TrueQ[rule[[2]]["PendingEviction"]] &&
                resumeClaimFreeQ[resume["Claim"], snapshot, First[owner]]]]];
        If[candidates === {}, Return[None]];
        chosen = Last[SortBy[candidates, {#[[2]]["Resume"]["StateGeneration"], #[[2]]["Created"], #[[1]]} &]];
        token = CreateUUID["claim-"];
        entry = chosen[[2]];
        entry["Resume"]["Claim"] = <|"Token" -> token, "PID" -> $ProcessID, "Host" -> $MachineName,
            "Started" -> First[owner]["Started"]|>;
        AssociateTo[index["Entries"], chosen[[1]] -> entry];
        saved = writeCacheIndex[root, index]; If[FailureQ[saved], Return[saved]];
        AssociateTo[$HeldResumeClaims, token -> True];
        <|"Root" -> root, "EntryID" -> chosen[[1]], "Token" -> token,
            "Metadata" -> <|"Root" -> root, "CacheID" -> index["CacheID"], "EntryID" -> chosen[[1]],
                "Runtime" -> entry["Runtime"], "StateID" -> entry["Resume"]["StateID"],
                "GeneratorIdentity" -> entry["Resume"]["GeneratorIdentity"],
                "StateGeneration" -> entry["Resume"]["StateGeneration"], "LastUsed" -> entry["LastUsed"]|>|>
    ]]
];
claimResumableCheckpoint[___] := makeFailure["InvalidCheckpoint", "Expected a construction resume key."];

(*
    Summary: End a resume claim, either returning the entry to resumable state or consuming it.
    Parameters: claim — claimResumableCheckpoint result; consume — True when a published group or a
        newer retained state supersedes it.
    Options/defaults: None.
    Returns: True, or storage Failure; a vanished entry or foreign token is already released.
    Effects: Under the store lock clears Claim, or removes the Resume record and marks the superseded
        entry PendingEviction; its files are deleted when its last lease ends or by CleanGAPCache.
        Forgets the claim in $HeldResumeClaims unless a consume failed, which keeps it held.
    Failures: Index I/O failure leaves the recorded claim, which stays reclaimable by a dead owner's
        successors and by this kernel once no running build holds it.
    Example: a timed-out resumed build releases its claim so the next call can try again.
    See also: claimResumableCheckpoint; buildFiniteGroup.
*)
releaseResumeClaim[claim_Association, consume_] := Module[{result},
    result = withStoreLock[claim["Root"], Module[{index, entry, saved},
        index = readCacheIndex[claim["Root"]]; If[FailureQ[index], Return[index]];
        entry = Lookup[index["Entries"], claim["EntryID"], None];
        If[!AssociationQ[entry] || !AssociationQ[Lookup[entry, "Resume", None]] ||
            !AssociationQ[entry["Resume"]["Claim"]] || entry["Resume"]["Claim"]["Token"] =!= claim["Token"],
            Return[True]];
        If[TrueQ[consume],
            KeyDropFrom[entry, "Resume"]; entry["PendingEviction"] = True,
            entry["Resume"]["Claim"] = Null];
        AssociateTo[index["Entries"], claim["EntryID"] -> entry];
        saved = writeCacheIndex[claim["Root"], index];
        If[FailureQ[saved], saved, True]
    ]];
    (* After a plain release the caller no longer holds the claim, so a failed update leaves a
       stale same-kernel claim that later builds may take over. A failed consume stays held: its
       group is published, and the entry must not become resumable in this kernel. *)
    If[result === True || !TrueQ[consume], KeyDropFrom[$HeldResumeClaims, claim["Token"]]];
    result
];
releaseResumeClaim[___] := makeFailure["InvalidCheckpoint", "Expected a resume claim and consume flag."];

True
