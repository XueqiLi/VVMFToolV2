(*
    :Title: GAP attempt and checkpoint transport
    :Context: VVMFTool`Private`
    :Summary: Advance owned workers through computation, save, fresh restore and publication.
    :Responsibilities: Runtime compatibility, local checkpoint authority, asynchronous phases and
        the tracked construction-progress checkpoint.
    :Dependencies: GAPProtocol.wl; ArtifactIO.wl; ResultValidation.wl; GAPOperations.wl; GAP/Driver.g.
    :See Also: GAPJobs.wl; GroupStorage.wl; VVMFArch/step1Plan.md.
*)

$GAPWorkerModules = {"Diagnostics", "Dependencies", "JSON", "Scalars", "Groups", "Serialization",
    "Characters", "GroupData", "CharacterTransfer", "RepresentationAdapters", "Representations", "RepresentationBasis", "GroupBinding", "ResultExport", "Subgroups",
    "GroupMaps", "CG", "Driver", "NormalSearch", "GroupImport"};
If[!AssociationQ[$GAPCheckpoints], $GAPCheckpoints = <||>];

(* Latest verified construction checkpoint, tracked only inside constructInCall so that a
   cancelled build can retain its accepted progress. Shared by publishGAPCandidate,
   runCharacterRequest and the builders; owned here because publication is its lowest writer. *)
If[!ValueQ[$TrackConstructionCheckpoint], $TrackConstructionCheckpoint = False];
If[!ValueQ[$ConstructionCheckpoint], $ConstructionCheckpoint = None];

(*
    Summary: Recognize incomplete construction progress: a verified base or partial character table.
    Parameters: data — decoded verified result.
    Options/defaults: None.
    Returns: Boolean.
    Effects: Pure.
    Failures: Malformed data returns False.
    Example: constructionProgressQ[<|"Status" -> "Partial"|>] is True.
    Remarks: Only characters decide construction progress. A state with complete characters and
        missing optional data (elements, irreps) belongs to a published group and is retained
        through its enrichment publication, so resumable construction keys stay character-only.
    See also: noteConstructionCheckpoint; publishGAPCandidate; constructionResumeKey.
*)
constructionProgressQ[data_Association] := MemberQ[{"BaseReady", "Partial"}, Lookup[data, "Status", None]];
constructionProgressQ[___] := False;

(*
    Summary: Record a newly accepted verified construction checkpoint when a build is tracking it.
    Parameters: reference — private verified checkpoint ID.
    Options/defaults: No effect unless $TrackConstructionCheckpoint is True (set by constructInCall).
    Returns: The reference.
    Effects: Updates the Block-scoped $ConstructionCheckpoint.
    Failures: None.
    Example: after base construction and each merged partial, the latest generation is recorded.
    See also: runCharacterRequest; constructFromSource; constructInCall; publishGAPCandidate.
*)
noteConstructionCheckpoint[reference_String] := (
    If[TrueQ[$TrackConstructionCheckpoint], $ConstructionCheckpoint = reference]; reference);
noteConstructionCheckpoint[other_] := other;

(*
    Summary: Fingerprint the installed adapter sources and probed GAP runtime.
    Parameters: capabilities — a successful fresh CheckGAP capability record.
    Options/defaults: Uses all worker module bytes and the actual executable bytes.
    Returns: SHA256 string, or source/runtime Failure.
    Effects: Reads files; does not execute source or a workspace.
    Failures: Incomplete probe data, missing/changed/unreadable executable or source.
    Example: changing Driver.g changes the fingerprint and prevents an old restore.
    See also: checkpointRecord; compatibleGAPProducerQ.
*)
gapRuntimeFingerprint[capabilities_Association] := Module[{files, digests, fields},
    fields = {"Version", "KernelVersion", "Architecture", "BuildVersion", "BuildDateTime",
        "Packages", "Executable", "WorkspaceRestored"};
    If[!AllTrue[fields, KeyExistsQ[capabilities, #] &] ||
        !TrueQ[capabilities["WorkspaceRestored"]] || !AssociationQ[capabilities["Packages"]],
        Return[makeFailure["InvalidCapabilities", "A successful GAP workspace probe is required."]]];
    files = Prepend[FileNameJoin[{$PackageRoot, "GAP", # <> ".g"}] & /@ $GAPWorkerModules,
        capabilities["Executable"]];
    digests = fileDigest /@ files;
    If[AnyTrue[digests, FailureQ], Return[First[Select[digests, FailureQ]]]];
    IntegerString[Hash[{KeyTake[capabilities, fields], digests}, "SHA256"], 16, 64]
];
gapRuntimeFingerprint[___] := makeFailure["InvalidCapabilities", "Expected GAP capabilities."];

(*
    Summary: Match a candidate's actual loaded packages and build to the fresh probe.
    Parameters: producer — VVMF_Producer JSON; capabilities — CheckGAP result.
    Options/defaults: Every loaded dependency must match a probed installed version.
    Returns: Boolean. Extra packages loaded only by the probe do not cause rejection.
    Effects: Pure.
    Failures: Missing build/package metadata returns False.
    Example: an unreported transitive package makes a workspace incompatible.
    Remarks: The owned producer proves successful loading at creation. Installed metadata
        admits explicit recipe packages without loading all optional packages in the probe.
    See also: GAP/Probe.g; checkpointRecord.
*)
compatibleGAPProducerQ[producer_Association, capabilities_Association] := Module[
    {keys, packages, probed, installed},
    keys = <|"gapVersion" -> "Version", "kernelVersion" -> "KernelVersion",
        "architecture" -> "Architecture", "buildVersion" -> "BuildVersion",
        "buildDateTime" -> "BuildDateTime"|>;
    packages = Lookup[producer, "packages", None];
    probed = Lookup[capabilities, "Packages", None];
    installed = Lookup[capabilities, "InstalledPackages", <||>];
    AssociationQ[packages] && AssociationQ[probed] &&
        And @@ KeyValueMap[KeyExistsQ[producer, #1] && KeyExistsQ[capabilities, #2] &&
            producer[#1] === capabilities[#2] &, keys] &&
        AllTrue[Keys[packages], (KeyExistsQ[probed, #] &&
            TrueQ[Lookup[probed[#], "Available", False]] &&
            Lookup[probed[#], "Version", None] === packages[#]) ||
            (AssociationQ[installed] && MemberQ[Lookup[installed, #, {}], packages[#]]) &]
];
compatibleGAPProducerQ[___] := False;

(*
    Summary: Resolve a kernel-owned checkpoint reference and verify bytes before any -L load.
    Parameters: reference — private opaque checkpoint ID; capabilities — fresh GAP probe.
    Options/defaults: requireVerified defaults True; False is only for a candidate's own verifier.
    Returns: Registered record or MissingCheckpoint/IncompatibleCheckpoint/InvalidCheckpoint Failure.
    Effects: Reads and hashes both artifacts and, when published, their paired manifest.
    Failures: Imported paths/records cannot register authority; mismatches prevent execution.
    Example: modifying either saved artifact invalidates the reference before GAP starts.
    See also: launchGAPWorker; advanceGAPAttempt. Persistent cache admission is owned by storage.
*)
checkpointRecord[reference_String, capabilities_Association, requireVerified_ : True] := Module[
    {record, runtime, artifacts, observed},
    record = Lookup[$GAPCheckpoints, reference, Missing["NotRegistered"]];
    If[MissingQ[record] || (TrueQ[requireVerified] && !TrueQ[record["Verified"]]),
        Return[makeFailure["MissingCheckpoint", "No verified owned checkpoint matches this reference."]]];
    runtime = gapRuntimeFingerprint[capabilities];
    If[FailureQ[runtime], Return[runtime]];
    If[runtime =!= record["Runtime"] || !compatibleGAPProducerQ[record["Native"]["producer"], capabilities],
        Return[makeFailure["IncompatibleCheckpoint", "The GAP runtime or package adapters changed."]]];
    artifacts = {record["ResultArtifact"], record["WorkspaceArtifact"]};
    If[TrueQ[record["Verified"]], AppendTo[artifacts, record["ManifestArtifact"]]];
    observed = fileDigest /@ (#["File"] & /@ artifacts);
    If[observed =!= artifacts,
        Return[makeFailure["InvalidCheckpoint", "Checkpoint bytes do not match the registered generation."]]];
    record
];
checkpointRecord[___] := makeFailure["MissingCheckpoint", "Expected a registered checkpoint reference."];

(*
    Summary: Launch a fresh isolated GAP worker, optionally loading an admitted checkpoint.
    Parameters: capabilities — probe record; budget — owned-process budget; reference — None or
        private checkpoint ID; verifier — True only for verifying a just-saved candidate.
    Options/defaults: No user startup files or automatic packages; GAP workspace cap is budgeted.
    Returns: Worker/Nonce/Deadline association or Failure.
    Effects: Starts a process and sends trusted adapter loads plus a nonce-bound ready message.
    Failures: Unregistered/incompatible checkpoint, invalid runtime/budget, launch or write failure.
    Example: launchGAPWorker[capabilities, budget] starts with no mathematical state.
    See also: checkpointRecord; startGAPAttempt; initializeGAPProtocol.
*)
launchGAPWorker[capabilities_Association, budget_Association, reference_ : None,
    verifier_ : False] := Module[{runtime, checkpoint, arguments, token = None, nonce, command, result},
    runtime = gapRuntimeFingerprint[capabilities];
    If[FailureQ[runtime], Return[runtime]];
    If[!IntegerQ[Lookup[budget, "MemoryBytes", None]] || budget["MemoryBytes"] < 1,
        Return[makeFailure["InvalidProcessRequest", "An integral memory budget is required."]]];
    arguments = {capabilities["Executable"], "-q", "-b", "-r", "-A", "--quitonbreak",
        "-K", ToString[Max[1, Floor[budget["MemoryBytes"]/1024]]] <> "k"};
    If[reference =!= None,
        checkpoint = checkpointRecord[reference, capabilities, !TrueQ[verifier]];
        If[FailureQ[checkpoint], Return[checkpoint]];
        arguments = Join[arguments, {"-L", checkpoint["WorkspaceArtifact"]["File"]}]];
    result = CheckAbort[
        token = startOwnedProcess[arguments, budget];
        If[FailureQ[token], token,
            initializeGAPProtocol[token];
            nonce = CreateUUID["ready-"];
            command = If[reference === None,
                StringJoin[("Read(" <> gapStringLiteral[
                    FileNameJoin[{$PackageRoot, "GAP", # <> ".g"}]] <> ");;\n") & /@
                    $GAPWorkerModules], ""];
            command = command <> "VVMF_Emit(rec(type:=\"workerReady\",requestID:=" <>
                gapStringLiteral[nonce] <> ",producer:=VVMF_Producer()));;\n";
            result = writeOwnedProcess[token, command];
            If[FailureQ[result], result,
                <|"Worker" -> token, "Nonce" -> nonce,
                    "Deadline" -> Lookup[Lookup[$OwnedProcesses, token, <||>], "Deadline", SessionTime[]]|>]
        ],
        makeFailure["Cancelled", "GAP worker launch was cancelled."]
    ];
    If[FailureQ[result] && StringQ[token], closeGAPProtocol[token, "LaunchFailed"]];
    result
];
launchGAPWorker[___] := makeFailure["InvalidProcessRequest", "Expected capabilities and worker budget."];

(*
    Summary: Create one isolated asynchronous attempt with its own input and output directory.
    Parameters: checkpoint — None or verified reference; request — exact JSON operation record;
        capabilities — probe; budget — TimeLimit/MemoryBytes; parent — existing owned job directory.
    Options/defaults: The attempt deadline starts before file preparation and process startup.
    Returns: Attempt association in Starting phase, or Failure with owned cleanup diagnostics.
    Effects: Creates a unique child directory, writes inert request data and starts one GAP worker.
    Failures: Unregistered operation, invalid identities/generation, missing parent/checkpoint,
        I/O/launch failure or abort.
    Example: Construct with generation "0" produces a base checkpoint before character attempts.
    Remarks: The operation registry supplies the permitted source and the generation step.
    See also: advanceGAPAttempt; stopGAPAttempt; GAP/Driver.g.
*)
startGAPAttempt[checkpoint_, request_Association, capabilities_Association,
    budget_Association, parent_String] := Module[
    {attempt, directory, written, launch, result, generation, limit, deadline, previous, operation},
    generation = decodeInteger[Lookup[request, "stateGeneration", None]];
    limit = Lookup[budget, "TimeLimit", None];
    If[!resultJSONQ[request] || !AllTrue[{"requestID", "stateID", "generatorIdentity", "operation"},
        StringQ[Lookup[request, #, None]] && StringLength[request[#]] > 0 &] ||
        !IntegerQ[generation] || generation < 0 ||
        !(limit === Infinity || (NumberQ[limit] && TrueQ[Im[limit] == 0] && TrueQ[limit > 0])) ||
        !absolutePathQ[parent] || !DirectoryQ[parent],
        Return[makeFailure["InvalidRequest", "Invalid request identities, budget or owned job directory."]]];
    operation = gapOperation[request["operation"]];
    If[FailureQ[operation], Return[operation]];
    deadline = SessionTime[] + limit;
    If[checkpoint === None,
        If[operation["Source"] === "New",
            If[generation =!= 0,
                Return[makeFailure["StateConflict", "A new construction must start at generation zero."]]],
            previous = Lookup[request, "acceptedGroup", <||>];
            If[operation["Source"] =!= "Typed" ||
                !AssociationQ[previous] || Lookup[previous, "status", None] =!= "Complete" ||
                generation =!= decodeInteger[Lookup[previous, "stateGeneration", None]] + operation["GenerationStep"] ||
                request["stateID"] =!= Lookup[previous, "stateID", None] ||
                request["generatorIdentity"] =!= Lookup[previous, "generatorIdentity", None],
                Return[makeFailure["StateConflict", "Reconstruction must preserve the accepted generation; enrichment advances it once."]]]],
        If[operation["Source"] === "New",
            Return[makeFailure["StateConflict", "A new construction cannot start from an existing checkpoint."]]];
        previous = checkpointRecord[checkpoint, capabilities];
        If[FailureQ[previous], Return[previous]];
        If[operation["Source"] === "Import",
            If[Lookup[request, "validationSource", None] =!= KeyTake[previous["Native"],
                    {"stateID", "generatorIdentity", "stateGeneration"}] ||
                !AssociationQ[Lookup[request, "importedGroup", None]] ||
                KeyTake[request, {"stateID", "generatorIdentity", "stateGeneration"}] =!=
                    KeyTake[request["importedGroup"], {"stateID", "generatorIdentity", "stateGeneration"}],
                Return[makeFailure["StateConflict", "Import must identify its accepted source and the exact requested snapshot."]]],
            If[generation =!= previous["Data"]["StateGeneration"] + operation["GenerationStep"] ||
                request["stateID"] =!= previous["Native"]["stateID"] ||
                request["generatorIdentity"] =!= previous["Native"]["generatorIdentity"],
                Return[makeFailure["StateConflict", "The request must advance the same state once."]]]]
    ];
    directory = CreateDirectory[FileNameJoin[{parent, CreateUUID["attempt-"]}]];
    If[!StringQ[directory], Return[makeFailure["SaveFailed", "Cannot create attempt storage."]]];
    attempt = <|"Directory" -> directory, "CallDirectory" -> parent,
        "SourceCheckpoint" -> checkpoint, "Checkpoint" -> None,
        "Request" -> request, "Capabilities" -> capabilities, "Budget" -> budget,
        "Deadline" -> deadline, "Worker" -> None, "Phase" -> "Starting", "Status" -> "Running",
        "ResultPath" -> FileNameJoin[{directory, "result.json"}],
        "RequestPath" -> FileNameJoin[{directory, "request.json"}]|>;
    result = CheckAbort[
        written = writeResult[attempt["RequestPath"], request];
        If[FailureQ[written], written,
            AbortProtect[
                launch = If[deadline <= SessionTime[], makeFailure["Timeout", "The attempt expired during preparation."],
                    launchGAPWorker[capabilities,
                        Join[budget, <|"TimeLimit" -> deadline - SessionTime[]|>], checkpoint]];
                If[!FailureQ[launch],
                    attempt = Join[attempt, KeyTake[launch, {"Worker", "Nonce"}]];
                    trackCheckpointWorker[parent, launch["Worker"]]]
            ];
            If[FailureQ[launch], launch, attempt]
        ], makeFailure["Cancelled", "GAP attempt preparation was cancelled."]
    ];
    If[FailureQ[result], failGAPAttempt[attempt, result], result]
];
startGAPAttempt[___] := makeFailure["InvalidRequest", "Malformed GAP attempt arguments."];

(*
    Summary: Send a validated request to the worker's main input and begin computation.
    Parameters: attempt — internally created live attempt record.
    Options/defaults: Executable source is written only for the explicit ConstructGAP operation.
    Returns: Updated Computing attempt or Failure.
    Effects: Writes explicit source when authorized by the operation, then sends fixed driver calls.
    Failures: Source mismatch/storage failure, unavailable worker or failed write.
    Example: failures from VVMF_Run are emitted with this request's identity.
    See also: VVMF_Run; advanceGAPAttempt.
*)
sendGAPComputation[attempt_Association] := Module[{updated = attempt, request, path, written, command},
    request = attempt["Request"];
    If[request["operation"] === "ConstructGAP",
        If[FailureQ[validateConstructionRecord[Lookup[request, "construction", <||>]]] ||
            request["construction"]["type"] =!= "gapCode",
            Return[makeFailure["InvalidConstruction", "The explicit source recipe is invalid."]]];
        path = FileNameJoin[{attempt["Directory"], "explicit.g"}];
        written = Check[Export[path, request["construction"]["code"], "String"], $Failed];
        If[written === $Failed, Return[makeFailure["SaveFailed", "Cannot write the explicit GAP source."]]];
        request["codePath"] = path;
        written = writeResult[attempt["RequestPath"], request];
        If[FailureQ[written], Return[written]];
        updated["Request"] = request
    ];
    command = "VVMF_REQUEST := JsonStringToGap(StringFile(" <>
        gapStringLiteral[attempt["RequestPath"]] <> "));;\n" <>
        "VVMF_CANDIDATE := VVMF_Run(VVMF_REQUEST);;\n" <>
        "if VVMF_IsFailure(VVMF_CANDIDATE) then\n" <>
        "VVMF_ProtocolFailure(VVMF_CANDIDATE,VVMF_REQUEST);\nelse\n" <>
        "VVMF_PrepareCheckpoint(VVMF_CANDIDATE," <> gapStringLiteral[attempt["ResultPath"]] <>
        ");\nfi;\n";
    written = writeOwnedProcess[attempt["Worker"], command];
    If[FailureQ[written], written, updated["Phase"] = "Computing"; updated]
];

(*
    Summary: Stop a single attempt and optionally remove its unpublished owned artifacts.
    Parameters: attempt — internally created record; reason — diagnostic string; remove — Boolean.
    Options/defaults: remove defaults True; callers retain a successfully published checkpoint.
    Returns: Cleanup report or Failure.
    Effects: Stops only the recorded worker; removes only this unique attempt directory/receipt.
    Failures: Failed worker cleanup preserves artifacts for recovery. Published artifacts are
        preserved regardless of remove; their later lifecycle belongs to managed storage.
    Example: stopGAPAttempt[attempt, "LostRace"] cannot delete its source checkpoint.
    See also: failGAPAttempt; closeGAPProtocol.
*)
stopGAPAttempt[attempt_Association, reason_String, remove_ : True] := Module[{cleanup, reference},
    cleanup = If[StringQ[Lookup[attempt, "Worker", None]],
        closeGAPProtocol[attempt["Worker"], reason], <|"Stopped" -> {}, "Reason" -> reason|>];
    If[FailureQ[cleanup], Return[cleanup]];
    reference = Lookup[attempt, "Checkpoint", None];
    If[TrueQ[remove] && !(StringQ[reference] &&
        TrueQ[Lookup[Lookup[$GAPCheckpoints, reference, <||>], "Verified", False]]),
        If[StringQ[reference], KeyDropFrom[$GAPCheckpoints, reference]];
        If[DirectoryQ[attempt["Directory"]] &&
            Check[DeleteDirectory[attempt["Directory"], DeleteContents -> True], $Failed] === $Failed,
            Return[makeFailure["CleanupFailed", "Cannot remove the owned attempt directory.",
                <|"Directory" -> attempt["Directory"]|>]]]
    ];
    cleanup
];

(*
    Summary: Attach owned cleanup and prior recovery state to a failed attempt.
    Parameters: attempt — internal record; failure — primary Failure.
    Options/defaults: Unpublished output is removed; the source checkpoint is retained.
    Returns: The original failure tag with cleanup and source-reference diagnostics.
    Effects: Stops this attempt through stopGAPAttempt.
    Failures: Cleanup problems remain explicit and do not overwrite the primary cause.
    Example: a save failure retains a previously verified base for another method.
    See also: advanceGAPAttempt; stopGAPAttempt.
*)
failGAPAttempt[attempt_Association, failure_Failure] := Failure[failure[[1]],
    Join[failure[[2]], <|"Cleanup" -> stopGAPAttempt[attempt, "Failed"],
        "SourceCheckpoint" -> Lookup[attempt, "SourceCheckpoint", None],
        "Checkpoint" -> If[TrueQ[Lookup[Lookup[$GAPCheckpoints,
            Lookup[attempt, "Checkpoint", None], <||>], "Verified", False]],
            attempt["Checkpoint"], None]|>]
];

(*
    Summary: Validate and hash the artifacts reported saved by this owned worker.
    Parameters: attempt — Saving-phase record after its matching checkpointSaved reply.
    Options/defaults: Exact schema/arithmetic checks are mandatory even for BaseReady/Partial.
    Returns: An unpublished checkpoint record or Failure; issues no trust receipt itself.
    Effects: Reads result/workspace bytes and computes a current runtime fingerprint.
    Failures: Incomplete output, request/status mismatch, invalid math or incompatible producer.
    Example: a saved character table is still provisional until a fresh native restore matches it.
    See also: validateGroupResult; advanceGAPAttempt; publishGAPCandidate.
*)
readSavedGAPCandidate[attempt_Association] := Module[{native, data, result, workspace, runtime},
    native = readResult[attempt["ResultPath"]];
    If[FailureQ[native], Return[native]];
    data = validateGroupResult[native, attempt["Request"]];
    If[FailureQ[data], Return[data]];
    If[data["Status"] =!= attempt["ExpectedStatus"] ||
        !compatibleGAPProducerQ[native["producer"], attempt["Capabilities"]],
        Return[makeFailure["IncompatibleCheckpoint", "The saved status or producer does not match the worker."]]];
    result = fileDigest[attempt["ResultPath"]];
    workspace = fileDigest[attempt["ResultPath"] <> ".wsp"];
    runtime = gapRuntimeFingerprint[attempt["Capabilities"]];
    If[AnyTrue[{result, workspace, runtime}, FailureQ],
        Return[First[Select[{result, workspace, runtime}, FailureQ]]]];
    If[result["Bytes"] === 0 || workspace["Bytes"] === 0,
        Return[makeFailure["InvalidCheckpoint", "Saved checkpoint artifacts must be nonempty."]]];
    <|"Native" -> native, "Data" -> data, "ResultArtifact" -> result,
        "WorkspaceArtifact" -> workspace, "Runtime" -> runtime, "Verified" -> False|>
];

(*
    Summary: Publish one paired manifest after the candidate's fresh native comparison succeeds.
    Parameters: attempt — owns the provisional checkpoint reference; no imported record is accepted.
    Options/defaults: Manifest names immutable result/workspace hashes and one state generation.
    Returns: Verified attempt with decoded Data, or Failure.
    Effects: Rechecks artifact integrity, atomically writes the manifest, marks the local reference
        verified (noting construction progress, constructionProgressQ, as the tracked checkpoint)
        and stops the verifier. Rival attempts are left running for the batch coordinator.
    Failures: Changed files/runtime, save failure or deadline expiry prevents successful publication.
    Example: a verified partial character checkpoint can be resumed but cannot create a Group.
    See also: checkpointRecord; advanceGAPAttempt; acceptCandidate.
*)
publishGAPCandidate[attempt_Association] := Module[{updated = attempt, record, manifest, saved, cleanup, resources},
    record = checkpointRecord[attempt["Checkpoint"], attempt["Capabilities"], False];
    If[FailureQ[record], Return[record]];
    manifest = checkpointManifest[record];
    saved = writeResult[FileNameJoin[{attempt["Directory"], "manifest.json"}], manifest];
    If[FailureQ[saved], Return[saved]];
    If[SessionTime[] >= attempt["Deadline"],
        Return[makeFailure["Timeout", "The attempt expired before checkpoint publication."]]];
    resources = pollOwnedProcess[attempt["Worker"]];
    If[FailureQ[resources], Return[resources]];
    (* The pair is now durable within the filesystem's atomic-rename contract. The
       small registry update and returned handle must not be separated by user abort. *)
    AbortProtect[
        record = Join[record, <|"Verified" -> True, "ManifestArtifact" -> saved|>];
        AssociateTo[$GAPCheckpoints, attempt["Checkpoint"] -> record];
        (* Incomplete verified progress becomes a build's recovery reference before any progress
           observer can cancel the call; complete tables are published by the build itself. *)
        If[constructionProgressQ[record["Data"]], noteConstructionCheckpoint[attempt["Checkpoint"]]];
        updated["Status"] = "Verified"; updated["Phase"] = "Complete";
        updated["Data"] = record["Data"];
    ];
    cleanup = closeGAPProtocol[attempt["Worker"], "CheckpointVerified"];
    If[FailureQ[cleanup],
        makeFailure["CleanupFailed", "Checkpoint was verified but its worker could not be released.",
            <|"Checkpoint" -> attempt["Checkpoint"], "Cleanup" -> cleanup|>],
        updated["Worker"] = None; updated]
];

(*
    Summary: Advance one asynchronous attempt by at most one protocol phase.
    Parameters: attempt — record produced by startGAPAttempt or this function.
    Options/defaults: Uses the original attempt deadline across computation, exact validation,
        saves, fresh-process restoration and manifest publication.
    Returns: Updated Running/Verified attempt or Failure after owned cleanup.
    Effects: Performs nonblocking reads; sends fixed commands only after matching replies.
        Exact candidate checks and file hashes may take time while the resource monitor runs.
    Failures: Timeout/abort/protocol/math/save/restore failures preserve the source checkpoint.
    Example: a batch polls each attempt, accepting only Status="Verified" as a candidate.
    Remarks: SaveWorkspace is a literal main-input command sent only after checkpointReady.
        A native reexport must equal the saved JSON; identity fields alone are insufficient.
    See also: GAP/Driver.g; pollGAPPacket; publishGAPCandidate.
*)
advanceGAPAttempt[attempt_Association] := Module[
    {current = attempt, result, remaining, expected, packet, phase, reference, record,
        written, launch, native, nonce, command, cleanup},
    If[Lookup[attempt, "Status", None] === "Verified", Return[attempt]];
    remaining = attempt["Deadline"] - SessionTime[];
    If[remaining <= 0, Return[failGAPAttempt[current,
        makeFailure["Timeout", "The GAP attempt deadline expired."]]]];
    result = CheckAbort[TimeConstrained[
        phase = current["Phase"];
        expected = Switch[phase,
            "Starting" | "VerifierStarting",
            <|"type" -> "workerReady", "requestID" -> current["Nonce"]|>,
            "Computing" | "Saving",
            Join[KeyTake[current["Request"], {"requestID", "stateID", "generatorIdentity", "stateGeneration"}],
                <|"type" -> If[phase === "Computing", "checkpointReady", "checkpointSaved"],
                    "resultPath" -> current["ResultPath"], "workspacePath" -> current["ResultPath"] <> ".wsp"|>],
            "Restored" | "VerifiedFile",
            record = $GAPCheckpoints[current["VerificationReference"]];
            Join[KeyTake[record["Native"], {"stateID", "generatorIdentity", "stateGeneration", "status"}],
                <|"type" -> If[phase === "Restored", "checkpointRestored", "checkpointVerified"],
                    "requestID" -> current["RestoreNonce"],
                    "checkpointRequestID" -> record["Native"]["requestID"]|>,
                If[phase === "VerifiedFile", <|"verifiedResultPath" -> current["VerificationPath"]|>, <||>]],
            _, makeFailure["InvalidProtocol", "Unknown worker phase."]
        ];
        packet = If[FailureQ[expected], expected, pollGAPPacket[current["Worker"], expected]];
        Which[
            FailureQ[packet], packet,
            MissingQ[packet], current,
            MemberQ[{"Starting", "VerifierStarting"}, phase],
            If[!compatibleGAPProducerQ[Lookup[packet, "producer", <||>], current["Capabilities"]],
                makeFailure["IncompatibleCheckpoint", "The launched worker differs from the probed runtime."],
                reference = If[phase === "Starting", current["SourceCheckpoint"], current["Checkpoint"]];
                If[reference === None, sendGAPComputation[current],
                    nonce = CreateUUID["restore-"];
                    current["VerificationReference"] = reference;
                    current["RestoreNonce"] = nonce;
                    current["VerificationPath"] = FileNameJoin[{current["Directory"], nonce <> ".json"}];
                    written = writeOwnedProcess[current["Worker"], "VVMF_VerifyCheckpoint(" <>
                        gapStringLiteral[nonce] <> "," <> gapStringLiteral[current["VerificationPath"]] <> ");;\n"];
                    If[FailureQ[written], written, current["Phase"] = "Restored"; current]
                ]
            ],
            phase === "Restored", current["Phase"] = "VerifiedFile"; current,
            phase === "VerifiedFile",
            native = readResult[current["VerificationPath"]];
            If[FailureQ[native], native,
                If[native =!= $GAPCheckpoints[current["VerificationReference"]]["Native"],
                    makeFailure["InvalidCheckpoint", "The restored native envelope differs from the saved JSON."],
                    cleanup = removeWriteTemporary[current["VerificationPath"]];
                    If[FailureQ[cleanup], cleanup,
                        noteCheckpointRestored[current["VerificationReference"]];
                        If[current["VerificationReference"] === current["Checkpoint"],
                            publishGAPCandidate[current], sendGAPComputation[current]]]
                ]
            ],
            phase === "Computing",
            If[!MemberQ[{"BaseReady", "Partial", "Complete"}, Lookup[packet, "status", None]],
                makeFailure["InvalidProtocol", "Invalid checkpoint readiness status."],
                current["ExpectedStatus"] = packet["status"];
                command = "VVMF_SAVE_OK := SaveWorkspace(" <>
                    gapStringLiteral[current["ResultPath"] <> ".wsp"] <> ");;\n" <>
                    "VVMF_ReportCheckpoint(VVMF_SAVE_OK," <> gapStringLiteral[current["Request"]["requestID"]] <> ");;\n";
                written = writeOwnedProcess[current["Worker"], command];
                If[FailureQ[written], written, current["Phase"] = "Saving"; current]
            ],
            phase === "Saving",
            If[packet["status"] =!= current["ExpectedStatus"],
                makeFailure["InvalidProtocol", "The saved status differs from readiness."],
                record = readSavedGAPCandidate[current];
                If[FailureQ[record], record,
                    AbortProtect[
                        current["Checkpoint"] = CreateUUID["checkpoint-"];
                        AssociateTo[$GAPCheckpoints, current["Checkpoint"] -> record]];
                    cleanup = closeGAPProtocol[current["Worker"], "CandidateSaved"];
                    If[FailureQ[cleanup], cleanup,
                        current["Worker"] = None;
                        AbortProtect[
                            launch = If[current["Deadline"] <= SessionTime[],
                                makeFailure["Timeout", "The attempt expired before restoration."],
                                launchGAPWorker[current["Capabilities"],
                                    Join[current["Budget"], <|"TimeLimit" -> current["Deadline"] - SessionTime[]|>],
                                    current["Checkpoint"], True]];
                            If[!FailureQ[launch],
                                current = Join[current, KeyTake[launch, {"Worker", "Nonce"}]];
                                trackCheckpointWorker[Lookup[current, "CallDirectory", None], launch["Worker"]]]
                        ];
                        If[FailureQ[launch], launch, current["Phase"] = "VerifierStarting"; current]
                    ]
                ]
            ]
        ], remaining, makeFailure["Timeout", "The GAP attempt exceeded its total deadline."]],
        makeFailure["Cancelled", "The GAP attempt was cancelled."]
    ];
    result = If[FailureQ[result], failGAPAttempt[current, result], result];
    progressAttempt[attempt, result];
    result
];
advanceGAPAttempt[___] := makeFailure["InvalidRequest", "Expected an owned GAP attempt."];

True
