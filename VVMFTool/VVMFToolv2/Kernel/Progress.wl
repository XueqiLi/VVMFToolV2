(*
    :Title: Scoped computation progress
    :Context: VVMFTool`Private`
    :Summary: Report actual stages and competing attempts to callbacks or a notebook monitor.
    :Responsibilities: Observer lifetime, event records, cancellation and automatic notebook UI.
    :Dependencies: Diagnostics.wl; validated ProgressFunction settings.
    :See Also: GAPJobs.wl; https://reference.wolfram.com/language/ref/Monitor.html.
*)

(* These dynamic defaults own no files or workers. Each outer public call localizes them.
   Nested builder enrichments share the call's monitor; observer reentry emits no recursion. *)
If[!ValueQ[$ProgressActive], $ProgressActive = False];
If[!ValueQ[$ProgressCallbackRunning], $ProgressCallbackRunning = False];

(*
    Summary: Invoke an observer or computation through a named Return boundary.
    Parameters: function — callable Function or symbol; arguments — its evaluated arguments.
    Options/defaults: No arguments calls a nullary computation body.
    Returns: The callback result, including an explicit Return from a pure function.
    Effects: Exactly the callback's effects; does not catch Throw or Abort.
    Failures: Exceptions pass to the owning progress scope.
    Example: invokeProgressFunction[Function[Null,Return[42]]] returns 42 to its caller.
    Remarks: A pure Function alone does not stop Return from exiting its named caller.
        This boundary keeps observer checks and completion reporting reachable.
    See also: withProgress; progressReport; Wolfram Return documentation.
*)
invokeProgressFunction[function_, arguments___] := function[arguments];

(*
    Summary: Format truthful notebook progress without a speculative completion percentage.
    Parameters: state — progress scope with Operation, LastEvent and Attempts.
    Options/defaults: None; only currently running attempts are shown.
    Returns: Panel containing the stage and active method/model/resource rows.
    Effects: Pure; dynamic updating belongs to withProgress.
    Failures: Caller supplies an internal progress state, never arbitrary imported data.
    Example: a four-method batch displays four independently allocated running attempts.
    See also: withProgress; ProgressIndicator; progressReport.
*)
progressPanel[state_Association] := Module[{event, active, phaseLabels},
    event = Lookup[state, "LastEvent", <||>];
    active = Select[Values[Lookup[state, "Attempts", <||>]], Lookup[#, "Status", None] === "Running" &];
    phaseLabels = <|"Starting" -> "Starting worker", "VerifierStarting" -> "Starting verification",
        "Restored" -> "Verifying restored state", "VerifiedFile" -> "Checking saved data",
        "Published" -> "Verified and saved"|>;
    Panel[Column[{
        Row[{state["Operation"], ": ", Lookup[event, "Phase", Lookup[event, "Event", "Starting"]]}],
        ProgressIndicator[Appearance -> "Necklace"],
        If[active === {}, Nothing, Grid[Prepend[
            ({Lookup[#, "Method", ""], Lookup[#, "Model", ""],
                Lookup[phaseLabels, Lookup[#, "Phase", ""], Lookup[#, "Phase", ""]],
                Lookup[#, "AllocatedCores", 1], Round[Lookup[#, "AllocatedMemory", 0]/2^20],
                Lookup[#, "AttemptTimeLimit", ""]} & /@ active),
            {"Method", "Model", "Stage", "Cores", "MiB budget", "Seconds per attempt"}],
            Alignment -> Left, Spacings -> {1.5, 0.6}]]
    }, Alignment -> Left]]
];

(*
    Summary: Publish one progress event and update the current call's observer state.
    Parameters: event — internal association with Event and optional attempt/stage metadata.
    Options/defaults: None; inactive, None and reentrant observers receive no callback.
    Returns: Null; callback output is ignored unless it is $Failed or Failure.
    Effects: Updates scoped state and invokes the configured observer synchronously.
    Failures: Observer messages, $Failed or Failure end the call with ProgressCallbackFailed;
        Abort ends it with Cancelled. Scoped backend cleanup still runs on those exits.
    Example: progressReport[<|"Event"->"BatchStarted", "PlannedAttempts"->descriptors|>].
    Remarks: Events report elapsed seconds, batch index and all currently known attempts.
        A callback must return promptly; it executes within running attempts' deadlines.
        No observer executes in the preemptive resource monitor.
    See also: withProgress; progressAttempt; runJobBatch.
*)
progressReport[event_Association] := Module[{packet, attempts, result},
    If[!TrueQ[$ProgressActive] || TrueQ[$ProgressCallbackRunning], Return[Null]];
    If[Lookup[event, "Event", None] === "BatchStarted", $ProgressState["Batch"]++];
    attempts = $ProgressState["Attempts"];
    If[StringQ[Lookup[event, "RequestID", None]],
        AssociateTo[attempts, event["RequestID"] -> event];
        $ProgressState["Attempts"] = attempts];
    packet = Join[<|"Operation" -> $ProgressState["Operation"]|>, event,
        <|"ElapsedSeconds" -> Max[0., SessionTime[] - $ProgressState["Started"]],
            "Batch" -> $ProgressState["Batch"], "Attempts" -> Values[attempts]|>];
    $ProgressState["LastEvent"] = packet;
    If[MemberQ[{Automatic, None}, $ProgressHandler], Return[Null]];
    result = Block[{$ProgressCallbackRunning = True},
        CheckAbort[Check[invokeProgressFunction[$ProgressHandler, packet], $Failed],
            makeFailure["Cancelled", "The progress callback cancelled the computation."]]];
    If[MatchQ[result, Failure["Cancelled", _]], Throw[result, $ProgressTag]];
    If[result === $Failed || FailureQ[result],
        Throw[makeFailure["ProgressCallbackFailed", "The progress callback failed.",
            <|"Event" -> packet, "Cause" -> result|>], $ProgressTag]];
    Null
];

(*
    Summary: Report a method's initial or changed transport phase, including terminal outcomes.
    Parameters: before — previous attempt or None; after — resulting attempt or Failure.
    Options/defaults: Unchanged phase/status produces no event; absent request data is ignored.
    Returns: Null, or the scoped observer failure/cancellation exit from progressReport.
    Effects: Reports existing request, descriptor and budget metadata; no process operations.
    Failures: This observer cannot declare a mathematical result accepted; Verified describes
        the shared runner's already completed native verification and paired save.
    Example: Computing -> Saving -> VerifierStarting -> Verified reports actual transitions.
    See also: beginMethodAttempt; advanceGAPAttempt; progressReport.
*)
progressAttempt[before_, after_] := Module[{attempt, status, phase, descriptor, packet},
    If[!TrueQ[$ProgressActive], Return[Null]];
    attempt = If[AssociationQ[after], after, before];
    If[!AssociationQ[attempt] || !AssociationQ[Lookup[attempt, "Request", None]], Return[Null]];
    status = If[FailureQ[after], If[after[[1]] === "Cancelled", "Cancelled", "Failed"],
        Lookup[attempt, "Status", "Running"]];
    phase = If[FailureQ[after], after[[1]], Lookup[attempt, "Phase", status]];
    If[AssociationQ[before] && !FailureQ[after] &&
        Lookup[before, "Phase", None] === phase && Lookup[before, "Status", None] === status, Return[Null]];
    descriptor = Lookup[attempt, "Descriptor", <||>];
    packet = Join[<|"Event" -> If[status === "Running", "AttemptProgress", "AttemptFinished"],
        "Operation" -> attempt["Request"]["operation"], "RequestID" -> attempt["Request"]["requestID"],
        "Phase" -> phase, "Status" -> status,
        "AttemptTimeLimit" -> Lookup[Lookup[attempt, "Budget", <||>], "TimeLimit", Missing["NotAvailable"]]|>,
        KeyTake[descriptor, {"Method", "Model", "RecoveryStrategy", "AllocatedCores", "AllocatedMemory"}]];
    progressReport[packet]
];

(*
    Summary: Own the progress observer for one public computation and its nested enrichments.
    Parameters: options — effective settings; operation — public operation label; body — nullary Function.
    Options/defaults: ProgressFunction Automatic displays Monitor only in notebook sessions;
        None is silent; a function receives progress associations in headless sessions too.
    Returns: The body's result or an explicit observer/cancellation failure. If a completion
        observer fails after publication, PartialResult contains the already accepted result.
    Effects: Localizes all observer state; Monitor removes its transient display on completion.
    Failures: The body owns worker cleanup. Tagged observer exits and Abort do not skip that cleanup.
        An ordinary user Throw remains available to its caller.
    Example: withProgress[<|ProgressFunction->None|>,"Test",Function[Null,42]] returns 42.
    See also: withCheckpointCall; progressReport; progressPanel.
*)
withProgress[options_Association, operation_String, body_Function] := Module[
    {execute, result, bodyResult = Missing["NoResult"], acceptedResult = Missing["NoResult"], partial},
    If[TrueQ[$ProgressActive], Return[invokeProgressFunction[body]]];
    Block[{$ProgressActive = True, $ProgressCallbackRunning = False,
        $ProgressHandler = Lookup[options, ProgressFunction, None], $ProgressTag = Unique["progressExit"],
        $ProgressPartialResult = Missing["NoResult"],
        $ProgressState = <|"Operation" -> operation, "Started" -> SessionTime[], "Batch" -> 0,
            "LastEvent" -> <||>, "Attempts" -> <||>|>},
        execute = Function[Null, Catch[CheckAbort[
            progressReport[<|"Event" -> "Started", "Phase" -> "Preparing"|>];
            bodyResult = invokeProgressFunction[body];
            progressReport[<|"Event" -> If[FailureQ[bodyResult], "Failed", "Completed"],
                "Phase" -> If[FailureQ[bodyResult], ToString[bodyResult[[1]]], "Completed"]|>];
            bodyResult,
            makeFailure["Cancelled", "The computation was cancelled."]], $ProgressTag]];
        result = If[$ProgressHandler === Automatic && TrueQ[$Notebooks],
            Monitor[execute[], Dynamic[progressPanel[$ProgressState]]],
            execute[]];
        acceptedResult = $ProgressPartialResult
    ];
    partial = If[!MissingQ[bodyResult] && !FailureQ[bodyResult], bodyResult, acceptedResult];
    If[FailureQ[result] && !KeyExistsQ[result[[2]], "PartialResult"] && !MissingQ[partial],
        Failure[result[[1]], Join[result[[2]], <|"PartialResult" -> partial|>]], result]
];
withProgress[___] := makeFailure["InvalidProgressRequest", "Expected options, an operation and a computation function."];

True
