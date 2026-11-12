(*
    :Title: Public bounded searches of supplied presentations
    :Context: VVMFTool`Private`
    :Summary: Run LINS with process ownership and bounds without constructing a finite parent.
    :Responsibilities: Public validation, timed single-method execution and all-exit cleanup.
    :Dependencies: NormalSearchValidation.wl; GAPWorkers.wl; CheckpointCalls.wl.
    :See Also: GAP/NormalSearch.g; VVMFArch/step1Plan.md.
*)

Options[NormalSubgroupsByIndex] = {
    IndexMode -> "Exact", MaxResults -> All, SmallGenerators -> True, Verification -> Automatic,
    AttemptTimeLimit :> $Configuration[AttemptTimeLimit], CoreBudget :> $Configuration[CoreBudget],
    MemoryBudget :> $Configuration[MemoryBudget], ProgressFunction :> $Configuration[ProgressFunction]
};

(*
    Summary: Run the single LINS algorithm inside a tracked, bounded native worker.
    Parameters: request — validated exact search data and identity; options — effective budgets;
        capabilities — fresh probe; call — owned temporary directory.
    Options/defaults: One sequential core; the supplied total memory budget bounds that worker.
    Returns: Decoded verified search data or structured process/protocol/validation Failure.
    Effects: Starts/tracks one worker, writes inert input/result files and reports actual phases.
        The enclosing withCheckpointCall cleans files and workers on every exit.
    Failures: Dependency, launch, timeout, cancellation, changed output, native error or schema failure.
    Example: an infinite presented parent can return finite quotient specifications without
        ever becoming a finite Group or creating a retained Group checkpoint.
    See also: NormalSubgroupsByIndex; awaitGAPPacket; decodeNormalSearch.
*)
runNormalSearch[request_Association, options_Association, capabilities_Association,
    call_Association] := Module[{deadline, written, launch, token, packet, result, before, after,
        report, event, input, output, command},
    deadline = SessionTime[] + options[AttemptTimeLimit];
    input = FileNameJoin[{call["Directory"], "normal-request.json"}];
    output = FileNameJoin[{call["Directory"], "normal-result.json"}];
    written = writeResult[input, request]; If[FailureQ[written], Return[written]];
    event = <|"Event" -> "AttemptPhase", "RequestID" -> request["requestID"], "Method" -> "LINS",
        "Model" -> "PresentedParent", "AllocatedCores" -> 1,
        "AllocatedMemory" -> options[MemoryBudget], "AttemptTimeLimit" -> options[AttemptTimeLimit],
        "Status" -> "Running", "Phase" -> "Starting"|>;
    progressReport[event];
    If[SessionTime[] >= deadline, Return[makeFailure["Timeout", "The search expired before worker startup."]]];
    AbortProtect[
        launch = launchGAPWorker[capabilities, <|"TimeLimit" -> deadline - SessionTime[],
            "MemoryBytes" -> options[MemoryBudget]|>];
        If[!FailureQ[launch], trackCheckpointWorker[call["Directory"], launch["Worker"]]]];
    If[FailureQ[launch], Return[launch]];
    token = launch["Worker"];
    packet = awaitGAPPacket[token, <|"type" -> "workerReady", "requestID" -> launch["Nonce"]|>];
    If[FailureQ[packet], Return[packet]];
    If[!compatibleGAPProducerQ[Lookup[packet, "producer", None], capabilities],
        Return[makeFailure["IncompatibleRuntime", "The search worker differs from the probed runtime."]]];
    progressReport[Join[event, <|"Phase" -> "Computing"|>]];
    command = "VVMF_RunNormalSearch(JsonStringToGap(StringFile(" <> gapStringLiteral[input] <>
        "))," <> gapStringLiteral[output] <> ");;\n";
    written = writeOwnedProcess[token, command]; If[FailureQ[written], Return[written]];
    packet = awaitGAPPacket[token, <|"type" -> "resultReady", "requestID" -> request["requestID"],
        "resultPath" -> output|>];
    If[FailureQ[packet], Return[packet]];
    progressReport[Join[event, <|"Phase" -> "Verifying"|>]];
    before = fileDigest[output]; If[FailureQ[before], Return[before]];
    result = readResult[output]; If[FailureQ[result], Return[result]];
    If[!AssociationQ[result] || !compatibleGAPProducerQ[Lookup[result, "producer", None], capabilities],
        Return[makeFailure["IncompatibleRuntime", "The search producer record is incompatible."]]];
    result = decodeNormalSearch[result, request]; If[FailureQ[result], Return[result]];
    after = fileDigest[output];
    If[before =!= after, Return[makeFailure["InvalidNormalSearch", "The search output changed during validation."]]];
    report = pollOwnedProcess[token]; If[FailureQ[report], Return[report]];
    If[SessionTime[] >= deadline, Return[makeFailure["Timeout", "The search expired during validation."]]];
    progressReport[Join[event, <|"Phase" -> "Verified", "Status" -> "Complete"|>]];
    result
];
runNormalSearch[___] := makeFailure["InvalidNormalSearch", "Expected an owned bounded-search context."];

(*
    Summary: Find normal subgroups of a supplied presentation at an exact or bounded index.
    Status: Alpha.
    Parameters: presentation — GroupPresentation; bound — positive integer within installed LINS range.
    Options/defaults: IndexMode="Exact", MaxResults=All, SmallGenerators=True; configuration
        supplies time/core/memory/progress settings. LINS uses one core within that budget.
    Returns: Search association with Items, Complete, CapReached and requested bound/options.
        Each item contains Index, GeneratorWords, GeneratorSemantics="Subgroup" and a finite
        QuotientPresentation on the parent's recorded generators; failures return Failure.
    Effects: Runs one owned GAP worker and cleans its temporary data. Returns immutable data;
        it does not create a finite Group object or retain a Group workspace.
    Failures: Invalid input/options before backend launch; unavailable LINS, unsupported bounds,
        timeouts and cancellation remain failures, never complete empty results.
    Example: NormalSubgroupsByIndex[GroupPresentation[{"a"}, {}], 3] finds the subgroup <a^3>;
        BuildGroup[result["Items"][[1]]["QuotientPresentation"], ComputeRepresentations->False]
        constructs its order-three quotient.
    Remarks: MaxResults uses one-result lookahead; Complete=True means the requested range is
        exhausted, even when its count equals the cap. SmallGenerators never changes the
        subgroup to one having only the same normal closure, and does not promise minimality.
    See also: GroupSubgroups; BuildGroup; https://gap-packages.github.io/LINS/doc/chap2.html.
*)
NormalSubgroupsByIndex[presentation_GroupPresentation, bound_Integer, options : OptionsPattern[]] := Module[
    {effective, encoded, request},
    effective = resolveOperationOptions[NormalSubgroupsByIndex, "NormalSubgroupsByIndex", {options}];
    If[FailureQ[effective], Return[effective]];
    With[{allowed = proofComputationLevelQ["NormalSubgroupsByIndex", effective[Verification]]}, If[FailureQ[allowed], Return[allowed]]];
    encoded = encodeConstruction[presentation]; If[FailureQ[encoded], Return[encoded]];
    If[bound < 1, Return[makeFailure["InvalidNormalSearch", "The index bound must be positive."]]];
    If[effective[MemoryBudget] < 128*2^20,
        Return[makeFailure["MemoryLimit", "The search budget is below the initial admission estimate."]]];
    request = <|"requestID" -> CreateUUID["normal-search-"], "operation" -> "NormalSubgroupsByIndex",
        "presentation" -> encoded, "bound" -> ToString[bound], "indexMode" -> effective[IndexMode],
        "maxResults" -> If[effective[MaxResults] === All, Null, ToString[effective[MaxResults]]],
        "smallGenerators" -> effective[SmallGenerators]|>;
    withProgress[effective, "NormalSubgroupsByIndex", Function[Null, Module[{capabilities},
        progressReport[<|"Event" -> "Stage", "Phase" -> "Checking GAP"|>];
        capabilities = CheckGAP[]; If[FailureQ[capabilities], Return[capabilities]];
        If[!TrueQ[Lookup[Lookup[capabilities["Packages"], "lins", <||>], "Available", False]],
            Return[makeFailure["DependencyUnavailable", "Bounded normal-subgroup search requires LINS."]]];
        withCheckpointCall[Function[call, runNormalSearch[request, effective, capabilities, call]]]
    ]]]
];
NormalSubgroupsByIndex[___] := makeFailure["InvalidNormalSearch", "Expected a GroupPresentation and positive integer index bound."];

True
