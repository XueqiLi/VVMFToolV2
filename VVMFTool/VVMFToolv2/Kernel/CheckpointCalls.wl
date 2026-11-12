(*
    :Title: GAP call resource lifetime
    :Context: VVMFTool`Private`
    :Summary: Own temporary generations, workers and retained-source leases for one public call.
    :Responsibilities: Call registration, exact ownership tracking and all-exit cleanup.
    :Dependencies: CheckpointStorage.wl; GAPProtocol.wl; POSIX rm for non-following tree removal.
    :See Also: GAPJobs.wl; StoreGAPState.
*)

(* Only this kernel can create a call owner. Portable metadata never reconstructs one. *)
If[!AssociationQ[$CheckpointCalls], $CheckpointCalls = <||>];

(*
    Summary: Allocate a unique owned temporary directory for one backend request.
    Parameters: None.
    Options/defaults: Uses the operating system temporary directory, independently of retention.
    Returns: ID/Directory call record or SaveFailed Failure.
    Effects: Creates a directory and private owner registry; does not start a worker.
    Failures: Failed creation is reported; assignment of ownership is protected from abort.
    Example: StoreGAPState=False calls still use this directory for intermediate checkpoints.
    See also: withCheckpointCall; cleanupCheckpoints.
*)
beginCheckpointCall[] := Module[{id = CreateUUID["call-"], directory, record},
    AbortProtect[
        directory = Check[CreateDirectory[FileNameJoin[{$TemporaryDirectory, "vvmf-" <> id}]], $Failed];
        If[!StringQ[directory], Return[makeFailure["SaveFailed", "Cannot create call storage."]]];
        directory = AbsoluteFileName[directory];
        record = <|"ID" -> id, "Directory" -> directory, "Workers" -> {}, "Sources" -> <||>|>;
        AssociateTo[$CheckpointCalls, id -> record]
    ];
    KeyTake[record, {"ID", "Directory"}]
];
beginCheckpointCall[___] := makeFailure["InvalidCall", "Call allocation takes no arguments."];

(*
    Summary: Associate a launched worker with the call owning its attempt's parent directory.
    Parameters: directory — registered call directory; token — owned worker token.
    Options/defaults: Unregistered integration-test directories return False without mutation.
    Returns: True if tracked, False when no call owns the directory.
    Effects: Adds the token to one private call record; does not change process ownership itself.
    Failures: Caller supplies a launch token immediately inside the launch's AbortProtect block.
    Example: a fresh verifier belongs to the same call as the original candidate worker.
    See also: startGAPAttempt; cleanupCheckpoints.
*)
trackCheckpointWorker[directory_String, token_String] := Module[{ids, id, record},
    ids = Select[Keys[$CheckpointCalls], $CheckpointCalls[#]["Directory"] === directory &];
    If[Length[ids] =!= 1, Return[False]];
    id = First[ids]; record = $CheckpointCalls[id];
    record["Workers"] = DeleteDuplicates[Append[record["Workers"], token]];
    AssociateTo[$CheckpointCalls, id -> record]; True
];
trackCheckpointWorker[___] := False;

(*
    Summary: Give a call responsibility for releasing one admitted persistent source.
    Parameters: id — registered call ID; reference — currently leased checkpoint reference.
    Options/defaults: The source begins unused; native verification marks successful restoration.
    Returns: True or InvalidCall/InvalidCacheLease Failure.
    Effects: Records release responsibility; callers acquire and track inside AbortProtect.
    Failures: Unknown calls and references without a durable lease are rejected.
    Example: the public enrichment coordinator tracks its source before launching any worker.
    See also: noteCheckpointRestored; releaseCheckpoint.
*)
trackCheckpointSource[id_String, reference_String] := Module[{record},
    record = Lookup[$CheckpointCalls, id, Missing["UnknownCall"]];
    If[MissingQ[record], Return[makeFailure["InvalidCall", "No call owns this source lease."]]];
    If[!KeyExistsQ[Lookup[$GAPCheckpoints, reference, <||>], "CacheLease"],
        Return[makeFailure["InvalidCacheLease", "Only admitted retained sources require lease release."]]];
    If[!KeyExistsQ[record["Sources"], reference], AssociateTo[record["Sources"], reference -> False]];
    AssociateTo[$CheckpointCalls, id -> record]; True
];
trackCheckpointSource[___] := makeFailure["InvalidCall", "Expected call and leased checkpoint IDs."];

(*
    Summary: Mark a source as successfully restored after its native JSON comparison passes.
    Parameters: reference — checkpoint reference just independently reexported by a GAP worker.
    Options/defaults: Temporary/untracked references need no persistent last-use update.
    Returns: Null.
    Effects: Records successful use for the owning call's eventual lease release.
    Failures: No trust is created; callers must already have completed actual native validation.
    Example: a later algorithm failure still retains evidence that source restoration succeeded.
    See also: advanceGAPAttempt; cleanupCheckpoints.
*)
noteCheckpointRestored[reference_String] := Module[{record},
    Do[
        record = $CheckpointCalls[id];
        If[KeyExistsQ[record["Sources"], reference],
            AssociateTo[record["Sources"], reference -> True];
            AssociateTo[$CheckpointCalls, id -> record]], {id, Keys[$CheckpointCalls]}];
    Null
];
noteCheckpointRestored[___] := Null;

(*
    Summary: Release only the workers, leases and temporary generations owned by one call.
    Parameters: id — opaque registered call ID.
    Options/defaults: Retained copies and previously existing checkpoints remain independent.
    Returns: Cleaned/Directory report or CleanupFailed with explicit remaining resources.
    Effects: Stops tracked workers, releases tracked leases and removes the owned temporary tree.
    Failures: Worker/lease cleanup failure preserves the directory and call record for retry.
        An unknown ID is rejected; a changed root path cannot authorize recursive deletion.
    Example: deleting a call with a symlink inside it preserves the link target outside the call.
    Remarks: POSIX rm removes links themselves and does not traverse them. The root is a
        kernel-created canonical directory, never a caller-supplied or imported deletion path.
    See also: withCheckpointCall; cleanCacheStore.
*)
cleanupCheckpoints[id_String] := Module[{record, failures = <||>, cleanup, references, removed, root},
    record = Lookup[$CheckpointCalls, id, Missing["UnknownCall"]];
    If[MissingQ[record], Return[makeFailure["InvalidCall", "No owned call matches this ID."]]];
    Do[
        cleanup = closeGAPProtocol[token, "CallFinished"];
        If[FailureQ[cleanup], AssociateTo[failures, token -> cleanup],
            record["Workers"] = DeleteCases[record["Workers"], token]], {token, record["Workers"]}];
    AssociateTo[$CheckpointCalls, id -> record];
    If[failures =!= <||>, Return[makeFailure["CleanupFailed", "Owned call workers could not all be stopped.",
        <|"CallID" -> id, "Failures" -> failures|>]]];
    Do[
        cleanup = releaseCheckpoint[reference, record["Sources"][reference]];
        If[FailureQ[cleanup], AssociateTo[failures, reference -> cleanup]];
        If[!FailureQ[cleanup] || TrueQ[Lookup[cleanup[[2]], "LeaseReleased", False]],
            KeyDropFrom[record["Sources"], reference]], {reference, Keys[record["Sources"]]}];
    AssociateTo[$CheckpointCalls, id -> record];
    If[failures =!= <||>, Return[makeFailure["CleanupFailed", "Owned call leases could not all be released.",
        <|"CallID" -> id, "Failures" -> failures|>]]];
    root = record["Directory"];
    If[FileExistsQ[root] && (!DirectoryQ[root] || AbsoluteFileName[root] =!= root),
        Return[makeFailure["CleanupFailed", "The owned call directory has changed."]]];
    references = Select[Keys[$GAPCheckpoints], With[
        {path = Lookup[Lookup[$GAPCheckpoints[#], "ResultArtifact", <||>], "File", ""]},
        StringQ[path] && StringStartsQ[path, root <> $PathnameSeparator]] &];
    removed = RunProcess[{"/bin/rm", "-rf", "--", root}];
    If[!AssociationQ[removed] || removed["ExitCode"] =!= 0 || FileExistsQ[root],
        Return[makeFailure["CleanupFailed", "Cannot remove the owned temporary call directory.", <|"CallID" -> id|>]]];
    KeyDropFrom[$GAPCheckpoints, references];
    KeyDropFrom[$CheckpointCalls, id];
    <|"Cleaned" -> True, "Directory" -> root|>
];
cleanupCheckpoints[___] := makeFailure["InvalidCall", "Expected an owned call ID."];

(*
    Summary: Run a backend callback with guaranteed cleanup of its call-owned resources.
    Parameters: body — function accepting the ID/Directory association from beginCheckpointCall.
    Options/defaults: None; the body chooses whether to publish a retained copy before returning.
    Returns: Callback result, Cancelled Failure on abort, or CleanupFailed with the result.
    Effects: Creates and cleans a call scope even on thrown exceptions; no persistent cache is
        removed except pending eviction completed when a tracked source lease is released.
    Failures: Allocation and cleanup errors are explicit; ordinary callback failures are preserved.
    Example: withCheckpointCall[Function[call, runWork[call["Directory"]]]] owns all work files.
    See also: publishCheckpoint; cleanupCheckpoints.
*)
withCheckpointCall[body_] := Module[{call = None, result, cleanup = True},
    result = CheckAbort[WithCleanup[
        call = beginCheckpointCall[],
        CheckAbort[If[FailureQ[call], call, body[call]],
            makeFailure["Cancelled", "The backend call was cancelled."]],
        If[AssociationQ[call], cleanup = cleanupCheckpoints[call["ID"]]]
    ],
        If[AssociationQ[call] && FailureQ[cleanup], cleanup = cleanupCheckpoints[call["ID"]]];
        makeFailure["Cancelled", "The backend call was cancelled."]
    ];
    If[FailureQ[cleanup], makeFailure["CleanupFailed", "Call cleanup did not complete.",
        <|"Result" -> result, "Cleanup" -> cleanup|>], result]
];

True
