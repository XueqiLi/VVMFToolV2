(*
    :Title: Finite-group enrichment method planning
    :Context: VVMFTool`Private`
    :Summary: Retry permitted models and word-recovery routes from one verified source.
    :Responsibilities: Compatible preferences, finite descriptor lists and batch outcomes.
    :Dependencies: GAPOperations.wl; JobScheduling.wl; GAPJobs.wl; GroupObject.wl.
    :See Also: GroupEnrichment.wl; VVMFArch/step1Plan.md.
*)

(*
    Summary: Identify the output requirements relevant to a successful enrichment method.
    Parameters: request — validated operation and optional subgroupQuery.
    Options/defaults: Subgroup kind and description requirement distinguish preferences;
        filters select results from the same enumeration and do not change the algorithm.
    Returns: Private stable string key.
    Effects: Pure; this key supplies a preference, never mathematical cache authority.
    Failures: The caller must provide a validated request association.
    Example: normal and all-subgroup queries keep separate successful methods.
    See also: groupDescriptors; publishGroupEnrichment.
*)
groupAttemptKey[request_Association] := request["operation"] <> "/" <>
    IntegerString[Hash[KeyTake[Lookup[request, "subgroupQuery", <||>],
        {"kind", "descriptions"}], "SHA256"], 16, 64];

(*
    Summary: Build all permitted enrichment attempts in a finite reproducible order.
    Parameters: state — WorkspaceBytes, optional PreferredAttempt and AllSubgroupsUsesClasses;
        request — validated finite enrichment; options — effective Method/GroupModel choices.
    Options/defaults: Native, FP, Cayley recovery tiers for operations that export newly
        recovered words (elements, subgroups, maps); word orders and S,T assignments use Native
        only because accepted class words are pinned. Within each tier, original/permutation/PC
        models and GAP before the applicable alternative. Compatible previous success leads.
    Returns: List of shared job descriptors or InvalidMethodPlan Failure.
    Effects: Pure. Native adapters check model applicability; no speculative solvability test.
    Failures: Unknown operation, method, model, kind or malformed planning metadata.
        The registered operation supplies its permitted methods (operationMethods).
    Example: normal subgroups allow GAP and ClassFilter on each permitted model.
    Remarks: All-subgroup work is deduplicated only after the saved native state recognizes GAP's
        exact class-expansion implementation. Explicit ClassExpansion remains executable.
        Memory admission is max(128 MiB, three times saved workspace bytes), not a peak bound.
    See also: packJobBatches; runGroupRequest; GAP/Subgroups.g.
*)
groupDescriptors[state_Association, request_Association, options_Association] := Module[
    {operation, kind, methods, selected, models, modelChoice, recoveries, preferred,
        pairs, memory, bytes, preferredPair, algorithm, descriptors, recoveryChoice},
    operation = Lookup[request, "operation", None];
    kind = Lookup[Lookup[request, "subgroupQuery", <||>], "kind", None];
    methods = operationMethods[request];
    selected = Lookup[options, Method, Automatic];
    modelChoice = Lookup[options, GroupModel, Automatic];
    recoveryChoice = Lookup[options, WordRecovery, Automatic];
    preferred = Lookup[state, "PreferredAttempt", <||>];
    bytes = Lookup[state, "WorkspaceBytes", 0];
    If[methods === {} || (selected =!= Automatic && !MemberQ[methods, selected]) ||
        !groupModelChoiceQ[modelChoice] || !wordRecoveryChoiceQ[recoveryChoice] ||
        !AssociationQ[preferred] || !IntegerQ[bytes] || bytes < 0,
        Return[makeFailure["InvalidMethodPlan", "Invalid group operation, method or model selection."]]];
    methods = If[selected === Automatic, methods, {selected}];
    models = groupModelOrder[modelChoice, {"Original", "Permutation", "PC"}];
    recoveries = groupModelOrder[recoveryChoice, {"Native", "FP", "Cayley"}];
    (* The certificate and native decompositions work on the recorded generators of the original model. *)
    If[MemberQ[{"GeneratorPresentation", "Decompose"}, operation], models = {"Original"}; recoveries = {"Native"}];
    (* Accepted class words are pinned, and these operations export no newly recovered words,
       so FP/Cayley variants would only repeat the Native computation. An explicit WordRecovery without Native is
       refused rather than replaced (methodOptionsPlan.md 2B.6). *)
    If[MemberQ[{"GroupWordOrder", "AssignModularGenerators"}, operation],
        If[recoveryChoice =!= Automatic && recoveryChoice =!= {"Native"},
            Return[makeFailure["InapplicableOption", "This operation uses native word recovery only; use WordRecovery -> Automatic or {\"Native\"}.",
                <|"Options" -> {WordRecovery}, "Operation" -> operation|>]]];
        recoveries = {"Native"}];
    (* the learned preference reorders only what the caller left Automatic: an explicit model or recovery order is kept *)
    preferredPair = Lookup[preferred, {"Method", "Model"}, None];
    If[modelChoice === Automatic && MemberQ[methods, First[preferredPair]] && MemberQ[models, Last[preferredPair]],
        models = DeleteDuplicates[Prepend[models, Last[preferredPair]]]];
    If[recoveryChoice === Automatic && MemberQ[methods, First[preferredPair]] && MemberQ[models, Last[preferredPair]] &&
            MemberQ[recoveries, Lookup[preferred, "RecoveryStrategy", None]],
        recoveries = DeleteDuplicates[Prepend[recoveries, preferred["RecoveryStrategy"]]]];
    pairs = Flatten[Table[{method, model}, {model, models}, {method, methods}], 1];
    If[modelChoice === Automatic && MemberQ[pairs, preferredPair], pairs = DeleteDuplicates[Prepend[pairs, preferredPair]]];
    memory = Max[128*2^20, 3 bytes];
    descriptors = Flatten[Table[
        algorithm = If[operation === "GroupSubgroups" && kind === "All" &&
            TrueQ[Lookup[state, "AllSubgroupsUsesClasses", False]], "ClassExpansion", pair[[1]]];
        <|"Operation" -> operation, "Method" -> pair[[1]], "Model" -> pair[[2]],
            "RecoveryStrategy" -> recoveries[[tier]], "WorkKey" -> StringRiffle[
                {operation, algorithm, pair[[2]], recoveries[[tier]]}, "/"],
            "Tier" -> tier - 1, "Parallel" -> False, "MinCores" -> 1,
            "MemoryEstimate" -> memory, "Availability" -> "Eligible", "Reason" -> None|>,
        {tier, Length[recoveries]}, {pair, pairs}], 1];
    descriptors
];
groupDescriptors[___] := makeFailure["InvalidMethodPlan", "Expected group planning data, request and options."];

(*
    Summary: Run permitted enrichment batches from one independently verified common source.
    Parameters: checkpoint — verified private reference; accepted — live-group snapshot;
        request/options — validated operation/settings; capabilities/directory — owned context.
    Options/defaults: Shared core/memory/timeout policy; every attempt uses the same generation.
    Returns: Verified complete candidate with selection/outcomes, or a structured Failure.
    Effects: Runs isolated GAP workers and saves a winner before the shared runner stops rivals.
    Failures: Exhaustion reports every attempted/skipped choice. Cancellation ends the operation.
        Registered terminal failures (native proofs such as invalid modular generators) stop
        further equivalent attempts.
        The live group and accepted source are never changed by a failed batch.
    Example: failure in native word recovery permits FP and bounded Cayley attempts.
    See also: enrichGroupInCall; runJobBatch; groupDescriptors.
*)
runGroupRequest[checkpoint_String, accepted_Association, request_Association,
    options_Association, capabilities_Association, directory_String] := Module[
    {record, descriptors, plan, context, result, outcomes = {}, candidate = None, failed = None,
        key, preferred, selection, terminal, reduced, skipped},
    record = checkpointRecord[checkpoint, capabilities]; If[FailureQ[record], Return[record]];
    If[!sameGroupStateQ[record["Data"], accepted],
        Return[makeFailure["StateConflict", "The shared source differs from accepted group mathematics."]]];
    key = groupAttemptKey[request];
    preferred = Lookup[Lookup[accepted, "SuccessfulAttempts", <||>], key, <||>];
    descriptors = groupDescriptors[<|"WorkspaceBytes" -> record["WorkspaceArtifact"]["Bytes"],
        "PreferredAttempt" -> preferred,
        "AllSubgroupsUsesClasses" -> Lookup[record["Data"]["LastComputation"],
            "allSubgroupsUsesClasses", False]|>, request, options];
    If[FailureQ[descriptors], Return[descriptors]];
    plan = packJobBatches[descriptors, options]; If[FailureQ[plan], Return[plan]];
    skipped = plan["Skipped"];
    context = <|"Options" -> options, "Capabilities" -> capabilities, "Directory" -> directory|>;
    Do[
        reduced = reduceRecoveryBatch[batch, outcomes];
        If[FailureQ[reduced], failed = reduced; Break[]];
        skipped = Join[skipped, reduced["Skipped"]];
        If[reduced["Batch"]["Attempts"] === {}, Continue[]];
        result = acceptVerifiedWinner[runJobBatch[checkpoint, reduced["Batch"], request, context]];
        If[FailureQ[result],
            outcomes = Join[outcomes, Lookup[result[[2]], "Outcomes", {}]];
            failed = result; Break[]];
        outcomes = Join[outcomes, result["Outcomes"]];
        If[AssociationQ[result["Winner"]], candidate = result["Winner"]; Break[]];
        terminal = SelectFirst[Lookup[result["Outcomes"], "Result"],
            operationTerminalFailureQ[request["operation"], #] &, None];
        If[FailureQ[terminal], failed = terminal; Break[]],
        {batch, plan["Batches"]}];
    If[FailureQ[failed], Return[Failure[failed[[1]], Join[failed[[2]],
        <|"Outcomes" -> outcomes, "Skipped" -> skipped|>]]]];
    If[AssociationQ[candidate],
        selection = SelectFirst[outcomes, Lookup[#, "Checkpoint", None] === candidate["Checkpoint"] &];
        Return[Join[candidate, <|"Outcomes" -> outcomes, "Skipped" -> skipped,
            "PreferenceKey" -> key, "SelectedAttempt" -> KeyTake[selection["Descriptor"],
                {"Method", "Model", "RecoveryStrategy"}]|>]]];
    makeFailure["MethodExhausted", "Group computation exhausted its permitted attempts. Select a method/model or increase its time limit.",
        <|"Operation" -> request["operation"], "Outcomes" -> outcomes, "Skipped" -> skipped,
            "ExplicitMethods" -> DeleteDuplicates[Lookup[descriptors, "Method"]],
            "GroupModel" -> options[GroupModel], "AttemptTimeLimit" -> options[AttemptTimeLimit]|>]
];
runGroupRequest[___] := makeFailure["InvalidRequest", "Expected a verified common source and group computation request."];

True
