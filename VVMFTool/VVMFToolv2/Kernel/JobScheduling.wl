(*
    :Title: GAP method descriptors and resource-aware batches
    :Context: VVMFTool`Private`
    :Summary: Plan finite, explicit method attempts within one shared allocation.
    :Responsibilities: Character route/model ordering, applicability, deduplication and batching.
    :Dependencies: Validated Configuration.wl options; capability data from CheckGAP.
    :See Also: VVMFArch/step1Plan.md automatic method order; GAPJobs.wl.
*)

(*
    Summary: Validate one concrete computational attempt descriptor.
    Parameters: descriptor — association identifying an operation, method, model and recovery
        route, work-equivalence key, tier, parallelism, required cores/memory and applicability.
    Options/defaults: None; sequential methods require exactly one core.
    Returns: Boolean.
    Effects: Pure.
    Failures: Missing/unknown fields, invalid resources, types or availability return False.
    Example: a sequential character attempt has Parallel -> False and MinCores -> 1.
    See also: characterDescriptors; packJobBatches.
*)
jobDescriptorQ[descriptor_] := resultFieldsQ[descriptor, {"Operation", "Method", "Model",
    "RecoveryStrategy", "WorkKey", "Tier", "Parallel", "MinCores", "MemoryEstimate",
    "Availability", "Reason"}] &&
    AllTrue[{"Operation", "Method", "Model", "RecoveryStrategy", "WorkKey"},
        StringQ[descriptor[#]] && StringLength[descriptor[#]] > 0 &] &&
    IntegerQ[descriptor["Tier"]] && descriptor["Tier"] >= 0 &&
    MemberQ[{True, False}, descriptor["Parallel"]] &&
    IntegerQ[descriptor["MinCores"]] &&
    If[descriptor["Parallel"], descriptor["MinCores"] >= 2, descriptor["MinCores"] === 1] &&
    IntegerQ[descriptor["MemoryEstimate"]] && descriptor["MemoryEstimate"] > 0 &&
    MemberQ[{"Eligible", "Unavailable", "Inapplicable"}, descriptor["Availability"]] &&
    (descriptor["Reason"] === None || StringQ[descriptor["Reason"]]);

(*
    Summary: Build the finite character-method/model attempt list in its documented order.
    Parameters: state — capability context with Packages, optional Solvable, WorkspaceBytes
        (PreferredCharacterAttempt was never supplied and is removed, methodOptionsPlan.md 2B.10); request — operation="Characters", optionally
        wordRecoveryStrategy; options — validated CharacterMethod and GroupModel choices.
    Options/defaults: Native, FP and bounded Cayley recovery tiers are tried in order unless
        an internal request explicitly selects one recovery route. Unknown predicates are checked by
        the native adapter; missing package evidence disables methods that require it.
    Returns: Descriptor list, or Failure.
    Effects: Pure; no process or group computation.
    Failures: Unknown explicit method/model/recovery or malformed planning context.
    Example: Automatic tries KnownTable, the four applicable algorithms, model alternatives,
        then the GAP dispatcher. Explicit Conlon never introduces another character algorithm.
    Remarks: MemoryEstimate is a conservative admission floor, max(128 MiB, 3 workspace bytes),
        not a measured peak prediction. Running workers receive a larger bounded allocation.
        WorkKey deduplicates a dispatcher only when its actual underlying algorithm is known.
    See also: packJobBatches; GAP/Characters.g; step1Plan.md.
*)
characterDescriptors[state_Association, request_Association, options_Association] := Module[
    {methods, models, selected, modelChoice, recovery, solvable, packages,
        memory, workspaceBytes, pairs, descriptors, method, model, tier, status, reason,
        algorithm, primary, strategies},
    methods = {"DixonSchneider", "Unger", "Conlon", "BaumClausen", "KnownTable", "GAP"};
    selected = Lookup[options, CharacterMethod, Automatic];
    modelChoice = Lookup[options, GroupModel, Automatic];
    recovery = Lookup[request, "wordRecoveryStrategy", "Native"];
    packages = Lookup[state, "Packages", <||>];
    solvable = Lookup[state, "Solvable", Missing["Unknown"]];
    workspaceBytes = Lookup[state, "WorkspaceBytes", 0];
    If[Lookup[request, "operation", None] =!= "Characters" ||
        (selected =!= Automatic && !MemberQ[methods, selected]) ||
        !groupModelChoiceQ[modelChoice] || !wordRecoveryChoiceQ[Lookup[options, WordRecovery, Automatic]] ||
        !MemberQ[{"Native","FP","Cayley"}, recovery] || !AssociationQ[packages] ||
        !AllTrue[Values[packages], AssociationQ[#] &&
            MemberQ[{True,False},Lookup[#,"Available",None]] &] ||
        !IntegerQ[workspaceBytes] || workspaceBytes < 0,
        Return[makeFailure["InvalidMethodPlan", "Invalid character planning context or selection."]]];
    memory = Max[128 2^20, 3 workspaceBytes];
    models = groupModelOrder[modelChoice, {"Original","Permutation","PC"}];
    primary = First[models];
    pairs = If[selected === Automatic,
        Join[{{"KnownTable", primary, 0}},
            ({#, primary, 1} & /@ Take[methods,4]),
            Flatten[Table[{method,model,2}, {model,Rest[models]}, {method,Most[methods]}],1],
            ({"GAP",#,3} & /@ models)],
        ({selected,#,0} & /@ models)];
    descriptors = Table[
        {method,model,tier} = pair;
        status = "Eligible"; reason = None;
        If[method === "Unger" &&
            !TrueQ[Lookup[Lookup[packages,"inducereduce",<||>],"Available",False]],
            status = "Unavailable"; reason = "Missing InduceReduce package"];
        If[solvable === False && (model === "PC" || MemberQ[{"Conlon","BaumClausen"},method]),
            status = "Inapplicable"; reason = "Requires a solvable group"];
        algorithm = If[method === "GAP", Lookup[state,"DispatcherMethod","GAP"], method];
        If[!MemberQ[methods,algorithm], algorithm = "GAP"];
        <|"Operation" -> "Characters", "Method" -> method, "Model" -> model,
            "RecoveryStrategy" -> recovery, "WorkKey" -> StringRiffle[
                {"Characters",algorithm,model,recovery}, "/"],
            "Tier" -> tier, "Parallel" -> False, "MinCores" -> 1,
            "MemoryEstimate" -> memory, "Availability" -> status, "Reason" -> reason|>,
        {pair,pairs}];
    (* recovery tiers: an internal retry names one strategy; otherwise WordRecovery (Automatic: Native, FP, Cayley) in
       the given order (methodOptionsPlan.md 2B.6) *)
    strategies = Replace[Lookup[options, WordRecovery, Automatic], Automatic -> {"Native", "FP", "Cayley"}];
    If[KeyExistsQ[request, "wordRecoveryStrategy"], descriptors,
        Flatten[Table[Join[descriptor, <|"RecoveryStrategy" -> strategy,
            "WorkKey" -> StringReplace[descriptor["WorkKey"], "/Native" ~~ EndOfString -> "/" <> strategy],
            "Tier" -> descriptor["Tier"] + 4 (First[FirstPosition[strategies, strategy]] - 1)|>],
            {strategy, strategies}, {descriptor, descriptors}], 1]]
];

(* GroupModel: Automatic, one model, or a duplicate-free ordered list of models (2B.6). *)
groupModelChoiceQ[choice_] := choice === Automatic || MemberQ[{"Original", "Permutation", "PC"}, choice] ||
    (ListQ[choice] && choice =!= {} && DuplicateFreeQ[choice] && SubsetQ[{"Original", "Permutation", "PC"}, choice]);
groupModelOrder[choice_, default_List] := Which[choice === Automatic, default, StringQ[choice], {choice}, True, choice];
(* WordRecovery: Automatic or a duplicate-free ordered list of "Native", "FP", "Cayley" (2B.6). *)
wordRecoveryChoiceQ[choice_] := choice === Automatic ||
    (ListQ[choice] && choice =!= {} && DuplicateFreeQ[choice] && SubsetQ[{"Native", "FP", "Cayley"}, choice]);
characterDescriptors[___] := makeFailure["InvalidMethodPlan", "Expected state, request and options."];

(*
    Summary: Pack ordered attempts into shared-core and shared-memory batches.
    Parameters: descriptors — validated finite attempt list; budget — positive integer
        CoreBudget and MemoryBudget entries keyed by public option symbols.
    Options/defaults: None. Below four cores all attempts are sequential. At four or more,
        sequential attempts prefer four/multiples of four; limited final/tier/memory batches
        can be smaller. One internally parallel method receives the full allocation alone.
    Returns: Batches, Skipped and effective resource totals; or Failure for malformed input.
    Effects: Pure; stable within each tier and removes identical eligible WorkKeys.
    Failures: Unavailable/inapplicable/duplicate/oversized entries are explicit skipped records;
        no oversized job is silently launched.
    Example: ten eligible sequential attempts with eight cores form batches of eight and two.
    Remarks: Each member receives an equal share of the full memory budget after admission.
        Batch totals never exceed the allocation. A coordinator must still enforce actual RSS.
    See also: jobDescriptorQ; planBatches; OwnedProcesses.wl.
*)
packJobBatches[descriptors_List, budget_Association] := Module[
    {cores, memory, eligible = {}, skipped = {}, seen = {}, batches = {},
        limit, pending, batch, candidate, allocated, take, share, tier},
    cores = Lookup[budget,CoreBudget,None]; memory = Lookup[budget,MemoryBudget,None];
    If[!IntegerQ[cores] || cores < 1 || !IntegerQ[memory] || memory < 1 ||
        !AllTrue[descriptors,jobDescriptorQ],
        Return[makeFailure["InvalidMethodPlan", "Expected valid descriptors and resolved resource budgets."]]];
    Do[
        Which[
            descriptor["Availability"] =!= "Eligible",
                AppendTo[skipped,<|"Descriptor" -> descriptor,"Reason" -> descriptor["Availability"],
                    "Details" -> descriptor["Reason"]|>],
            descriptor["MinCores"] > cores || descriptor["MemoryEstimate"] > memory ||
                (cores < 4 && descriptor["Parallel"]),
                AppendTo[skipped,<|"Descriptor" -> descriptor,"Reason" -> "InsufficientResources"|>],
            MemberQ[seen,descriptor["WorkKey"]],
                AppendTo[skipped,<|"Descriptor" -> descriptor,"Reason" -> "DuplicateWork"|>],
            True, AppendTo[seen,descriptor["WorkKey"]]; AppendTo[eligible,descriptor]
        ],
        {descriptor,Last /@ SortBy[MapIndexed[{#1["Tier"],First[#2],#1} &,descriptors],
            Take[#,2] &]}];
    limit = If[cores < 4,1,4 Quotient[cores,4]];
    pending = eligible;
    While[pending =!= {},
        candidate = First[pending]; tier = candidate["Tier"];
        If[candidate["Parallel"],
            batch = {candidate}; pending = Rest[pending],
            take = TakeWhile[pending, !#["Parallel"] && #["Tier"] === tier &];
            take = Take[take,UpTo[limit]];
            (* Equal shares give each admitted method its own enforceable RSS cap. *)
            While[Length[take] > 1 &&
                Max[(#["MemoryEstimate"] & /@ take)] > Quotient[memory,Length[take]],
                take = Most[take]];
            batch = take; pending = Drop[pending,Length[batch]]
        ];
        share = Quotient[memory,Length[batch]];
        allocated = Map[Join[#,<|"AllocatedCores" -> If[#["Parallel"],cores,1],
            "AllocatedMemory" -> share|>] &,batch];
        AppendTo[batches,<|"Attempts" -> allocated,
            "Cores" -> Total[(#["AllocatedCores"] & /@ allocated)],
            "MemoryBytes" -> share Length[batch], "Tier" -> tier|>]
    ];
    <|"Batches" -> batches,"Skipped" -> skipped,"CoreBudget" -> cores,"MemoryBudget" -> memory|>
];
packJobBatches[___] := makeFailure["InvalidMethodPlan", "Expected descriptors and resource budget."];

(*
    Summary: Select operation descriptors and apply the common batch policy.
    Parameters: state — method capability context; request — registered operation;
        options — validated effective options with resolved resource budgets.
    Options/defaults: Character routes follow characterDescriptors. A request's internal
        descriptors field supplies already-registered adapters from other owning modules.
    Returns: packJobBatches result, or an unsupported/invalid operation Failure.
    Effects: Pure.
    Failures: No adapter list means an unsupported operation, never an empty claimed success.
    Example: planBatches[state,<|"operation" -> "Characters"|>,options] respects explicit methods.
    See also: characterDescriptors; packJobBatches; runRequest in step1Plan.md.
*)
planBatches[state_Association, request_Association, options_Association] := Module[{descriptors},
    descriptors = Which[
        KeyExistsQ[request,"descriptors"], request["descriptors"],
        Lookup[request,"operation",None] === "Characters", characterDescriptors[state,request,options],
        True, makeFailure["UnsupportedOperation","No method planner is installed for this operation."]
    ];
    If[FailureQ[descriptors], descriptors, packJobBatches[descriptors,options]]
];
planBatches[___] := makeFailure["InvalidMethodPlan", "Expected planning context, request and options."];

True
