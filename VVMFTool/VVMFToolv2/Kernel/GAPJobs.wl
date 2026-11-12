(*
    :Title: Shared GAP method-batch coordinator
    :Context: VVMFTool`Private`
    :Summary: Race resource-allocated methods and preserve verified partial mathematical state.
    :Responsibilities: Descriptor execution, save-before-cancel selection and coherent partial merge.
    :Dependencies: GAPWorkers.wl (attempts, construction-progress tracker); GAPOperations.wl;
        JobScheduling.wl; validated effective configuration.
    :See Also: VVMFArch/step1Plan.md; GAP/CharacterTransfer.g.
*)

(*
    Summary: Start a method descriptor against the same verified base as its batch peers.
    Parameters: checkpoint — owned reference; descriptor — allocated method descriptor;
        request — exact operation record; context — Capabilities, Directory and Options.
    Options/defaults: Each attempt gets AttemptTimeLimit and its allocated memory share.
    Returns: A Running attempt or Failure.
    Effects: Adds method/model/recovery choices to inert request data and launches one worker.
    Failures: Missing allocation, invalid descriptor, stale checkpoint or launch/storage errors.
    Example: four sequential character descriptors launch independent single-process methods.
    Remarks: Adapters are sequential. A parallel descriptor runs only as the single-core children of its
        operation's registered expansion (expandParallelBatch), which share its allocation; a child carries
        ParentWorkKey and RequestFields (merged into its request), both outside the descriptor contract.
    See also: runJobBatch; startGAPAttempt; expandParallelBatch.
*)
beginMethodAttempt[checkpoint_, descriptor_Association, request0_Association,
    context_Association] := Module[{methodRequest, budget, baseFields, milliseconds, vertices, attempt, request},
    baseFields = KeyDrop[descriptor, {"AllocatedCores", "AllocatedMemory", "ParentWorkKey", "RequestFields"}];
    request = Join[request0, Lookup[descriptor, "RequestFields", <||>]];
    If[!jobDescriptorQ[baseFields] ||
        !IntegerQ[Lookup[descriptor, "AllocatedCores", None]] || descriptor["AllocatedCores"] < 1 ||
        !IntegerQ[Lookup[descriptor, "AllocatedMemory", None]] || descriptor["AllocatedMemory"] < 1 ||
        !AllTrue[{"Options", "Capabilities", "Directory"}, KeyExistsQ[context, #] &] ||
        descriptor["Operation"] =!= Lookup[request, "operation", None] ||
        descriptor["Availability"] =!= "Eligible" ||
        descriptor["AllocatedMemory"] < descriptor["MemoryEstimate"] ||
        descriptor["AllocatedCores"] < descriptor["MinCores"] ||
        (!descriptor["Parallel"] && descriptor["AllocatedCores"] =!= 1),
        Return[makeFailure["InvalidMethodPlan", "An allocated descriptor and execution context are required."]]];
    If[descriptor["Parallel"],
        Return[makeFailure["CapabilityUnavailable", "No internally parallel adapter is installed for this descriptor."]]];
    (* Cayley search has a finite vertex/CPU bound even with an infinite wall-clock
       request. The enclosing worker still enforces actual RSS and the whole-attempt
       deadline. 1024 bytes/vertex is an admission estimate, not a memory guarantee. *)
    vertices = Min[2^53 - 1, Max[1, Quotient[descriptor["AllocatedMemory"], 1024]]];
    milliseconds = If[context["Options"][AttemptTimeLimit] === Infinity, 2^53 - 1,
        Min[2^53 - 1, Max[1, Ceiling[1000 context["Options"][AttemptTimeLimit]]]]];
    methodRequest = Join[request, <|"method" -> descriptor["Method"], "model" -> descriptor["Model"],
        "wordRecoveryStrategy" -> descriptor["RecoveryStrategy"],
        "wordRecoveryBudget" -> <|"maxElements" -> vertices, "maxMilliseconds" -> milliseconds|>|>];
    budget = <|"TimeLimit" -> context["Options"][AttemptTimeLimit],
        "MemoryBytes" -> descriptor["AllocatedMemory"]|>;
    attempt = startGAPAttempt[checkpoint, methodRequest, context["Capabilities"], budget, context["Directory"]];
    If[AssociationQ[attempt], attempt = Join[attempt, <|"Descriptor" -> descriptor|>]];
    progressAttempt[<|"Request" -> methodRequest, "Descriptor" -> descriptor, "Budget" -> budget|>, attempt];
    attempt
];
beginMethodAttempt[___] := makeFailure["InvalidMethodPlan", "Malformed method attempt arguments."];

(*
    Summary: Run one allocated method through all checkpoint verification phases.
    Parameters: checkpoint, descriptor, request — beginMethodAttempt inputs;
        budget — execution context with Capabilities, Directory and Options.
    Options/defaults: Uses the same phase runner as concurrent batches.
    Returns: Verified candidate or Failure; no group is published here.
    Effects: Owns one method worker and its files; stops it on user cancellation.
    Failures: Propagates method/protocol/math/save/restore/resource failures with recovery data.
    Example: explicit methods and character-transfer jobs can be run sequentially.
    See also: beginMethodAttempt; stopAttempt; runJobBatch.
*)
runAttempt[checkpoint_, descriptor_Association, request_Association, budget_Association] := Module[
    {attempt = None, result},
    result = CheckAbort[
        AbortProtect[attempt = beginMethodAttempt[checkpoint, descriptor, request, budget]];
        While[AssociationQ[attempt] && attempt["Status"] === "Running",
            attempt = advanceGAPAttempt[attempt];
            If[AssociationQ[attempt] && attempt["Status"] === "Running", Pause[0.05]]
        ];
        attempt,
        If[AssociationQ[attempt], failGAPAttempt[attempt, makeFailure["Cancelled", "The method was cancelled."]],
            makeFailure["Cancelled", "Method preparation was cancelled."]]
    ];
    result
];
runAttempt[___] := makeFailure["InvalidRequest", "Expected one allocated method request."];

(*
    Summary: Stop one owned method attempt after a winner is saved, or on cancellation.
    Parameters: attempt — phase-runner record; reason — diagnostic string.
    Options/defaults: Unpublished files are removed; verified checkpoints are preserved.
    Returns: Cleanup report or Failure.
    Effects: Delegates exact worker/directory ownership to stopGAPAttempt.
    Failures: Cleanup problems remain explicit to the batch caller.
    Example: stopAttempt[rival, "WinnerPublished"] never stops an unrelated GAP process.
    See also: runJobBatch; stopGAPAttempt.
*)
stopAttempt[attempt_Association, reason_String] := stopGAPAttempt[attempt, reason];
stopAttempt[___] := makeFailure["InvalidRequest", "Expected owned attempt and cleanup reason."];

(*
    Summary: Run a preallocated batch and select the first verified checkpoint completing the request.
    Parameters: checkpoint — shared verified base; batch — packJobBatches member;
        request — common operation/generation data; context — execution capabilities/options/storage.
    Options/defaults: Each member receives a unique request ID. Completion is the registered
        operation predicate (operationCompleteQ); other verified candidates are retained as
        Partials and never stop rivals; no partial character table becomes a Group.
    Returns: Winner (candidate or None), Partials and per-method Outcomes, or Cancelled/CleanupFailed.
    Effects: Starts independent workers within allocation, polls them, then cancels rivals only
        after a request-completing candidate has a verified paired manifest. Save failures leave
        peers running. Outcome Results record the predicate's Complete/Partial judgement.
    Failures: Ordinary method failures are recorded and do not terminate the batch. User abort
        ends the whole batch; owned cleanup failures are reported rather than hidden.
    Example: a Conlon partial remains recoverable while Dixon or Unger continues computing.
    See also: runCharacterRequest; advanceGAPAttempt; packJobBatches.
*)
runJobBatch[checkpoint_String, batch0_Association, request_Association, context_Association] := Module[
    {active = <||>, outcomes = {}, partials = {}, winner = None, candidate, descriptor, batch,
        methodRequest, methodRequests = <||>, index, ids, result, cleanups = {}, cleanup, aborted = False,
        complete},
    batch = expandParallelBatch[batch0, request];
    If[!ListQ[Lookup[batch, "Attempts", None]] || batch["Attempts"] === {},
        Return[makeFailure["InvalidMethodPlan", "Expected a nonempty allocated batch."]]];
    If[!AssociationQ[Lookup[context, "Options", None]] ||
        !AllTrue[{CoreBudget, MemoryBudget}, IntegerQ[Lookup[context["Options"], #, None]] &&
            context["Options"][#] > 0 &] ||
        !AllTrue[batch["Attempts"], AssociationQ[#] &&
            IntegerQ[Lookup[#, "AllocatedCores", None]] && #["AllocatedCores"] > 0 &&
            IntegerQ[Lookup[#, "AllocatedMemory", None]] && #["AllocatedMemory"] > 0 &] ||
        Total[Lookup[batch["Attempts"], "AllocatedCores"]] > context["Options"][CoreBudget] ||
        Total[Lookup[batch["Attempts"], "AllocatedMemory"]] > context["Options"][MemoryBudget],
        Return[makeFailure["InvalidMethodPlan", "The batch exceeds or lacks the shared resource allocation."]]];
    progressReport[<|"Event" -> "BatchStarted", "Operation" -> Lookup[request, "operation", "GAP"],
        "Phase" -> "Starting batch", "PlannedAttempts" -> batch["Attempts"],
        "CoreBudget" -> context["Options"][CoreBudget], "MemoryBudget" -> context["Options"][MemoryBudget]|>];
    result = CheckAbort[
        Do[
            descriptor = batch["Attempts"][[index]];
            (* Completion is judged against the batch request; a child's RequestFields apply to its launch only. *)
            methodRequest = Join[request, <|"requestID" -> CreateUUID["request-"]|>];
            methodRequests[index] = methodRequest;
            AbortProtect[
                candidate = beginMethodAttempt[checkpoint, descriptor, methodRequest, context];
                If[AssociationQ[candidate],
                    AssociateTo[active, index -> <|"Attempt" -> candidate, "Descriptor" -> descriptor|>]]
            ];
            If[FailureQ[candidate],
                AppendTo[outcomes, <|"Descriptor" -> descriptor, "Result" -> candidate|>];
                If[candidate[[1]] === "Cancelled", aborted = True; Break[]]],
            {index, Length[batch["Attempts"]]}
        ];
        While[Length[active] > 0 && winner === None && !aborted,
            ids = Keys[active];
            Do[
                descriptor = active[index]["Descriptor"];
                candidate = advanceGAPAttempt[active[index]["Attempt"]];
                AbortProtect[
                    If[AssociationQ[candidate],
                        AssociateTo[active, index -> <|"Attempt" -> candidate, "Descriptor" -> descriptor|>]]
                ];
                Which[
                    FailureQ[candidate],
                    AppendTo[outcomes, <|"Descriptor" -> descriptor, "Result" -> candidate|>];
                    KeyDropFrom[active, index];
                    If[candidate[[1]] === "Cancelled", aborted = True; Break[]],
                    candidate["Status"] === "Verified",
                    (* The operation's completion predicate, not the envelope status alone, decides
                       whether this candidate satisfies the request and may stop its rivals. *)
                    complete = operationCompleteQ[candidate["Data"], methodRequests[index]];
                    AppendTo[outcomes, <|"Descriptor" -> descriptor,
                        "Result" -> If[complete, "Complete", Replace[candidate["Data"]["Status"], "Complete" -> "Partial"]],
                        "Checkpoint" -> candidate["Checkpoint"]|>];
                    KeyDropFrom[active, index];
                    If[complete, winner = candidate; Break[], AppendTo[partials, candidate]]
                ], {index, ids}
            ];
            If[aborted, Break[]];
            If[Length[active] > 0 && winner === None, Pause[0.05]]
        ];
        Null,
        aborted = True
    ];
    Do[
        candidate = active[index]["Attempt"];
        cleanup = stopAttempt[candidate, If[aborted, "Cancelled", "WinnerPublished"]];
        progressAttempt[candidate, Join[candidate, <|"Status" -> If[aborted, "Cancelled", "StoppedAfterVerifiedWinner"],
            "Phase" -> If[aborted, "Cancelled", "StoppedAfterVerifiedWinner"]|>]];
        AppendTo[cleanups, cleanup];
        AppendTo[outcomes, <|"Descriptor" -> active[index]["Descriptor"],
            "Result" -> If[aborted, "Cancelled", "StoppedAfterVerifiedWinner"], "Cleanup" -> cleanup|>],
        {index, Keys[active]}
    ];
    If[aborted, Return[makeFailure["Cancelled", "The GAP method batch was cancelled.",
        <|"Outcomes" -> outcomes, "Partials" -> partials, "Cleanup" -> cleanups|>]]];
    If[AnyTrue[cleanups, FailureQ], Return[makeFailure["CleanupFailed", "Some owned rivals could not be released.",
        <|"Winner" -> winner, "Partials" -> partials, "Outcomes" -> outcomes|>]]];
    progressReport[<|"Event" -> "BatchFinished", "Operation" -> Lookup[request, "operation", "GAP"],
        "Phase" -> If[AssociationQ[winner], "Verified and saved", "Trying remaining methods"],
        "Outcomes" -> outcomes|>];
    <|"Winner" -> winner, "Partials" -> partials, "Outcomes" -> outcomes|>
];
runJobBatch[___] := makeFailure["InvalidMethodPlan", "Expected a shared checkpoint and allocated batch."];

(*
    Summary: Replace each parallel attempt of a batch by its operation's single-core children.
    Parameters: batch — allocated batch; request — the batch's common request.
    Options/defaults: Operations without a registered ParallelExpansion keep their parallel attempt, which
        beginMethodAttempt refuses (CapabilityUnavailable).
    Returns: The batch with expanded attempts (Cores and MemoryBytes recomputed).
    Effects: Pure.
    Failures: None; an expansion returning no valid children keeps the parallel attempt.
    Example: a four-core Dixon parallel attempt over eight irreps becomes four one-core attempts of two irreps.
    Remarks: Children must stay within the parent's AllocatedCores and AllocatedMemory; each child carries
        ParentWorkKey (the parent's WorkKey, for retry history) and RequestFields (its request override).
    See also: runJobBatch; registerGAPOperation; representationParallelExpansion.
*)
expandParallelBatch[batch_Association, request_Association] := Module[{attempts},
    If[!ListQ[Lookup[batch, "Attempts", None]] || !AllTrue[batch["Attempts"], AssociationQ], Return[batch]];
    attempts = Flatten[Map[Function[attempt, Module[{entry, children},
        entry = If[TrueQ[attempt["Parallel"]], gapOperation[attempt["Operation"]], None];
        children = If[AssociationQ[entry] && KeyExistsQ[entry, "ParallelExpansion"], entry["ParallelExpansion"][attempt, request], None];
        If[ListQ[children] && children =!= {} && AllTrue[children, AssociationQ[#] && #["AllocatedCores"] === 1 &&
                IntegerQ[#["AllocatedMemory"]] && #["AllocatedMemory"] >= #["MemoryEstimate"] &&
                jobDescriptorQ[KeyDrop[#, {"AllocatedCores", "AllocatedMemory", "ParentWorkKey", "RequestFields"}]] &] &&
                Length[children] <= attempt["AllocatedCores"] && Total[Lookup[children, "AllocatedMemory"]] <= attempt["AllocatedMemory"],
            children, {attempt}]]], batch["Attempts"]], 1];
    Join[batch, <|"Attempts" -> attempts, "Cores" -> Total[Lookup[attempts, "AllocatedCores"]],
        "MemoryBytes" -> Total[Lookup[attempts, "AllocatedMemory"]]|>]
];
expandParallelBatch[batch_, _] := batch;

(*
    Summary: Keep a verified, saved winner when only the release of its stopped rivals failed.
    Parameters: result — runJobBatch result or Failure.
    Options/defaults: None.
    Returns: The batch result, or for CleanupFailed with a complete verified Winner a batch result
        whose outcomes record the RivalCleanupFailure; other values unchanged.
    Effects: Pure.
    Failures: Cancellation and every other failure are returned unchanged.
    Example: a rival whose process cannot be killed does not discard the saved complete table.
    Remarks: The winner's checkpoint was published and verified before rivals were stopped, so its
        mathematics is accepted; the cleanup failure remains visible in Outcomes.
    See also: runJobBatch; runCharacterRequest; runGroupRequest.
*)
acceptVerifiedWinner[result_] := If[MatchQ[result, Failure["CleanupFailed", _]] &&
    AssociationQ[Lookup[result[[2]], "Winner", None]],
    <|"Winner" -> result[[2]]["Winner"], "Partials" -> Lookup[result[[2]], "Partials", {}],
        "Outcomes" -> Append[Lookup[result[[2]], "Outcomes", {}],
            <|"Result" -> "RivalCleanupFailure", "Failure" -> result|>]|>,
    result];

(*
    Summary: Avoid repeating algorithms whose words already exported or whose route is inapplicable.
    Parameters: batch — allocated method batch; outcomes — earlier results for this request.
    Options/defaults: Only matching operation/method/model entries are considered; the operation's
        registered recovery rule (operationRecoverySkipQ) decides which earlier results suffice.
    Returns: Reduced Batch and explicit Skipped entries; retained allocations are unchanged.
    Effects: Pure; it neither removes accepted partial data nor changes algorithm selection.
    Failures: Invalid batch/outcome containers return InvalidMethodPlan.
    Example: verified partial Conlon output needs no second Conlon run merely to use FP words.
    Remarks: Timeout, native errors and word failures still permit isolated recovery retries.
    See also: runCharacterRequest; runGroupRequest; packJobBatches.
*)
reduceRecoveryBatch[batch_Association, outcomes_List] := Module[
    {attempts = {}, skipped = {}, prior, keys = {"Operation", "Method", "Model"}},
    If[!ListQ[Lookup[batch, "Attempts", None]] || !AllTrue[outcomes, AssociationQ],
        Return[makeFailure["InvalidMethodPlan", "Expected a batch and previous outcome records."]]];
    Do[
        prior = SelectFirst[outcomes, Function[outcome,
            KeyTake[Lookup[outcome, "Descriptor", <||>], keys] === KeyTake[descriptor, keys] &&
                operationRecoverySkipQ[descriptor["Operation"], Lookup[outcome, "Result", None]]], None];
        If[AssociationQ[prior],
            AppendTo[skipped, <|"Descriptor" -> descriptor, "Reason" -> "RecoveryNotNeeded",
                "PriorResult" -> prior["Result"]|>],
            AppendTo[attempts, descriptor]],
        {descriptor, batch["Attempts"]}];
    <|"Batch" -> Join[batch, <|"Attempts" -> attempts,
        "Cores" -> Total[Lookup[attempts, "AllocatedCores", 0]],
        "MemoryBytes" -> Total[Lookup[attempts, "AllocatedMemory", 0]]|>], "Skipped" -> skipped|>
];
reduceRecoveryBatch[___] := makeFailure["InvalidMethodPlan", "Expected a method batch and prior outcomes."];

(*
    Summary: Incorporate a verified sibling's characters into the chosen coherent checkpoint.
    Parameters: destination/source — verified private references; context — full execution allocation.
    Options/defaults: Transfer is internal and is not a publicly selectable character algorithm.
    Returns: A newly verified generation or Failure preserving both previous checkpoints.
    Effects: Sends the source's already verified mathematical envelope, evaluates its class words
        in the destination, merges rows, and saves/restores one native state before returning.
    Failures: Invalid source authority, incompatible state/identity, transfer or checkpoint failure.
    Example: two partial algorithm results are combined without merging their binary workspaces.
    See also: GAP VVMF_TransferCharacters; runCharacterRequest.
*)
mergeCharacterCheckpoints[destination_String, source_String, context_Association] := Module[
    {target, incoming, request, descriptor},
    target = checkpointRecord[destination, context["Capabilities"]];
    incoming = checkpointRecord[source, context["Capabilities"]];
    If[FailureQ[target], Return[target]]; If[FailureQ[incoming], Return[incoming]];
    If[target["Data"]["StateID"] =!= incoming["Data"]["StateID"] ||
        target["Data"]["GeneratorIdentity"] =!= incoming["Data"]["GeneratorIdentity"] ||
        !AssociationQ[incoming["Data"]["CharacterData"]],
        Return[makeFailure["StateConflict", "Only verified characters from the same state can be transferred."]]];
    request = <|"operation" -> "Characters", "requestID" -> CreateUUID["merge-"],
        "stateID" -> target["Native"]["stateID"], "generatorIdentity" -> target["Native"]["generatorIdentity"],
        "stateGeneration" -> ToString[target["Data"]["StateGeneration"] + 1],
        "characterIdentity" -> incoming["Native"]["characterData"]["identity"],
        "transferredCharacters" -> incoming["Native"]|>;
    descriptor = <|"Operation" -> "Characters", "Method" -> "Transfer", "Model" -> "Original",
        "RecoveryStrategy" -> "Native", "WorkKey" -> "Characters/Transfer", "Tier" -> 0,
        "Parallel" -> False, "MinCores" -> 1, "MemoryEstimate" -> 1,
        "Availability" -> "Eligible", "Reason" -> None, "AllocatedCores" -> 1,
        "AllocatedMemory" -> context["Options"][MemoryBudget]|>;
    runAttempt[destination, descriptor, request, context]
];
mergeCharacterCheckpoints[___] := makeFailure["InvalidRequest", "Expected two verified checkpoint references."];

(*
    Summary: Complete mandatory character data using the planned sequence of method batches.
    Parameters: checkpoint — verified base/partial reference; options — validated resolved
        character/resource options; capabilities — fresh probe; directory — owned call storage.
    Options/defaults: Automatic/explicit methods follow planBatches; complete cache wins first.
    Returns: Verified complete candidate, or MethodExhausted with resumable partial checkpoint.
    Effects: Runs resource-bounded batches; between unsuccessful batches incorporates all
        certified partials into one native state used by subsequent methods.
    Failures: Exhausted/unavailable methods, transfer error or cancellation never discard earlier
        verified state: a failed batch or merge returns the newest verified checkpoint containing all
        accepted rows as Checkpoint. No incomplete Group is published.
    Example: Conlon alone can return MethodExhausted with a reusable partial checkpoint.
    See also: planBatches; runJobBatch; mergeCharacterCheckpoints.
*)
runCharacterRequest[checkpoint_String, options_Association, capabilities_Association,
    directory_String] := Module[{accepted = checkpoint, record, request, identity, plan, context,
        batch, result, outcomes = {}, partial, merged, candidate = None, failed = None,
        reduced, skipped, source},
    record = checkpointRecord[accepted, capabilities];
    If[FailureQ[record], Return[record]];
    noteConstructionCheckpoint[accepted];
    If[record["Data"]["Status"] === "Complete", Return[<|"Status" -> "Verified",
        "Checkpoint" -> accepted, "Data" -> record["Data"], "Outcomes" -> {}|>]];
    identity = If[AssociationQ[record["Native"]["characterData"]],
        record["Native"]["characterData"]["identity"], CreateUUID["characters-"]];
    request = Join[<|"operation" -> "Characters", "characterIdentity" -> identity|>,
        (* a weak build's table (methodOptionsPlan.md 2C.6) *)
        If[MemberQ[{"Numerical", None}, $GroupAcceptanceLevel], <|"characterCheck" -> "TransportOnly"|>, <||>]];
    plan = planBatches[<|"Packages" -> capabilities["Packages"],
        "WorkspaceBytes" -> record["WorkspaceArtifact"]["Bytes"]|>, request, options];
    If[FailureQ[plan], Return[plan]];
    skipped = plan["Skipped"];
    context = <|"Options" -> options, "Capabilities" -> capabilities, "Directory" -> directory|>;
    Do[
        reduced = reduceRecoveryBatch[batch, outcomes];
        If[FailureQ[reduced], failed = reduced; Break[]];
        skipped = Join[skipped, reduced["Skipped"]];
        If[reduced["Batch"]["Attempts"] === {}, Continue[]];
        record = checkpointRecord[accepted, capabilities];
        If[FailureQ[record], failed = record; Break[]];
        request = Join[request, <|"stateID" -> record["Native"]["stateID"],
            "generatorIdentity" -> record["Native"]["generatorIdentity"],
            "stateGeneration" -> ToString[record["Data"]["StateGeneration"] + 1]|>];
        source = accepted;
        result = acceptVerifiedWinner[runJobBatch[accepted, reduced["Batch"], request, context]];
        (* A failed batch (cancelled, or rival cleanup failed without a winner) still carries
           verified, saved partials; keep the first as the recovery reference. Each was computed
           from the accepted source in a worker restored from it, and character methods merge the
           existing rows, so it contains the source's rows. *)
        If[FailureQ[result] && MatchQ[Lookup[result[[2]], "Partials", {}], {_Association, ___}],
            accepted = noteConstructionCheckpoint[First[result[[2]]["Partials"]]["Checkpoint"]]];
        If[FailureQ[result], failed = result; Break[]];
        outcomes = Join[outcomes, result["Outcomes"]];
        If[AssociationQ[result["Winner"]], candidate = result["Winner"]; Break[]];
        Do[
            If[!AssociationQ[record["Data"]["CharacterData"]],
                accepted = noteConstructionCheckpoint[partial["Checkpoint"]];
                record = checkpointRecord[accepted, capabilities],
                merged = mergeCharacterCheckpoints[accepted, partial["Checkpoint"], context];
                (* A failed merge keeps the verified partial when nothing was merged in this batch
                   yet: it then contains every row of the accepted source. *)
                If[FailureQ[merged],
                    If[accepted === source, accepted = noteConstructionCheckpoint[partial["Checkpoint"]]];
                    failed = merged; Break[]];
                (* Only incomplete progress is noted: a complete table is published directly, and an
                   abort before that keeps the last resumable partial as the recovery reference. *)
                accepted = merged["Checkpoint"];
                If[constructionProgressQ[merged["Data"]], noteConstructionCheckpoint[accepted]];
                record = checkpointRecord[accepted, capabilities];
                If[merged["Data"]["Status"] === "Complete", candidate = merged; Break[]]
            ], {partial, result["Partials"]}
        ];
        If[FailureQ[failed] || AssociationQ[candidate], Break[]],
        {batch, plan["Batches"]}
    ];
    If[FailureQ[failed], Return[Failure[failed[[1]], Join[failed[[2]],
        <|"Checkpoint" -> accepted, "Outcomes" -> outcomes|>]]]];
    If[AssociationQ[candidate], Return[Join[candidate, <|"Outcomes" -> outcomes, "Skipped" -> skipped|>]]];
    makeFailure["MethodExhausted", "Character methods did not produce a complete table. Choose a method or increase its time limit; with StoreGAPState->True the next build of this construction resumes the retained verified state.",
        <|"Checkpoint" -> accepted, "Outcomes" -> outcomes, "Skipped" -> skipped,
            "CharacterMethod" -> Lookup[options, CharacterMethod, Automatic],
            "AttemptTimeLimit" -> Lookup[options, AttemptTimeLimit, Missing["Unspecified"]]|>]
];
runCharacterRequest[___] := makeFailure["InvalidRequest", "Expected a verified base and character options."];

True
