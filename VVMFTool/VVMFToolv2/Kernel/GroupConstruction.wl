(*
    :Title: Public finite-group construction
    :Context: VVMFTool`Private`
    :Summary: Connect typed and explicit-code builders to verified group/character checkpoints.
    :Responsibilities: Public options, source reproducibility, publication and failure recovery.
    :Dependencies: GAPWorkers.wl (construction-progress tracker); GAPJobs.wl; CheckpointCalls.wl;
        GroupObject.wl.
    :See Also: VVMFArch/step1Plan.md; GroupInput.wl.
*)

(* Configuration-owned defaults are delayed, so later ConfigureVVMFTool calls affect
   both OptionValue and actual computation. Mathematical construction choices stay local. *)
Options[BuildGroup] = Join[
    Normal[KeyDrop[$BuilderDefaults, Keys[$Configuration]]],
    (* a session key too (the CG family's), but a builder's Verification is plain Automatic (2C-iii-b) *)
    {Verification -> Automatic},
    {StoreGAPState :> $Configuration[StoreGAPState],
        AttemptTimeLimit :> $Configuration[AttemptTimeLimit],
        CoreBudget :> $Configuration[CoreBudget], MemoryBudget :> $Configuration[MemoryBudget],
        ProgressFunction :> $Configuration[ProgressFunction]}
];
Options[BuildGroupFromGAP] = Join[Options[BuildGroup],
    {GeneratorNames -> Automatic, ConstructionDependencies -> {}}];
Options[BuildModularGroup] = Options[BuildGroup];

(*
    Summary: Resolve a public operation's OptionValue semantics exactly once per effective key.
    Parameters: head — public function symbol; operation — registered option schema; rules — options list.
    Options/defaults: Unknown names fail before evaluation of delayed option values.
    Returns: Effective validated association or Failure.
    Effects: Evaluates caller option values and hardware defaults; starts no backend or storage.
    Failures: Unknown operation/option, invalid values and inapplicable combinations are explicit.
    Example: duplicate options retain Wolfram's first-rule precedence.
    See also: validateOptions; OptionsPattern; ConfigureVVMFTool.
*)
resolveOperationOptions[head_Symbol, operation_String, rules_List] := Module[{supplied, defaults, effective},
    defaults = Lookup[$OperationDefaults, operation, None];
    If[!AssociationQ[defaults], Return[makeFailure["UnknownOperation", "No option schema is installed."]]];
    supplied = Association[Reverse[Flatten[rules]]];
    If[Complement[Keys[supplied], Keys[defaults]] =!= {},
        Return[makeFailure["UnknownOption", "An option is not supported by this operation.",
            <|"Operation" -> operation, "Options" -> Complement[Keys[supplied], Keys[defaults]]|>]]];
    (* explicit > operation key > family key > the option's own default (methodOptionsPlan.md 2D) *)
    effective = Association @@ Map[Function[key, key -> If[KeyExistsQ[supplied, key], OptionValue[head, rules, key],
        With[{session = sessionOptionDefault[operation, key]}, If[MissingQ[session], OptionValue[head, rules, key], session]]]], Keys[defaults]];
    validateOptions[operation, effective]
];
resolveOperationOptions[___] := makeFailure["InvalidOptions", "Expected operation and public option rules."];

(*
    Summary: Record explicit GAP source and exact declared dependency hashes for reproducibility.
    Parameters: code — nonempty source string; options — validated BuildGroupFromGAP settings.
    Options/defaults: GeneratorNames is required; ConstructionDependencies defaults to {}.
    Returns: Validated gapCode construction data or Failure; the source is not executed here.
    Effects: Reads declared dependency files only to hash them.
    Failures: Missing/changed dependency files, duplicate declarations or invalid source/names.
    Example: a GroupNames recipe is retained byte-for-byte beside its ordered generator names.
    See also: BuildGroupFromGAP; validateConstructionRecord; fileDigest.
*)
explicitGAPConstruction[code_String, options_Association] := Module[{dependencies, hashes},
    dependencies = options[ConstructionDependencies];
    If[!DuplicateFreeQ[dependencies], Return[makeFailure["InvalidConstruction", "Construction dependencies must be distinct."]]];
    hashes = fileDigest /@ dependencies;
    If[AnyTrue[hashes, FailureQ], Return[First[Select[hashes, FailureQ]]]];
    validateConstructionRecord[<|"type" -> "gapCode", "code" -> code, "names" -> options[GeneratorNames],
        "dependencies" -> (<|"path" -> #["File"], "sha256" -> #["SHA256"]|> & /@ hashes)|>]
];
explicitGAPConstruction[___] := makeFailure["InvalidConstruction", "Expected explicit source and validated options."];

(*
    Summary: Recheck declared raw-code inputs against the recipe's recorded file digests.
    Parameters: construction — validated typed or explicit GAP construction record.
    Options/defaults: Typed construction and self-contained raw code need no external file reads.
    Returns: True or ConstructionDependencyChanged Failure with the affected paths.
    Effects: Reads only declared input files; does not run source or publish state.
    Failures: Changed, removed or unreadable files prevent acceptance under stale provenance.
    Example: editing a declared C3 recipe to construct C5 after the Started callback fails.
    Remarks: Checks bracket raw execution and final publication. Declared paths are not locked;
        callers must keep inputs stable during the call. Undeclared reads cannot be certified.
    See also: explicitGAPConstruction; buildFiniteGroup; ConstructionDependencies.
*)
checkConstructionDependencies[construction_Association] := Module[{changed},
    If[construction["type"] =!= "gapCode", Return[True]];
    changed = Select[construction["dependencies"], Function[entry,
        With[{actual = fileDigest[entry["path"]]},
            FailureQ[actual] || actual["SHA256"] =!= entry["sha256"]]]];
    If[changed === {}, True,
        makeFailure["ConstructionDependencyChanged", "Declared construction inputs changed or became unavailable.",
            <|"Files" -> Lookup[changed, "path"]|>]]
];
checkConstructionDependencies[___] := makeFailure["InvalidConstruction", "Expected a validated construction record."];

(*
    Summary: Give a failed construction useful retained recovery metadata when requested.
    Parameters: failure — computation Failure; reference — last accepted private checkpoint or None;
        capabilities — current probe; options — validated builder settings; resume — None or
        <|"Key" -> constructionResumeKey, "Source" -> resumed reference, "Claim" -> claim|>.
    Options/defaults: StoreGAPState=False removes no preceding cache and returns no temporary path.
    Returns: Failure with Operation/Recovery and optional RetentionFailure; original tag is preserved.
    Effects: May publish the accepted base/partial checkpoint as a resumable entry; never publishes
        an incomplete Group. A resumed source that made no progress is not copied again.
    Failures: A failed recovery save is attached explicitly; it does not hide the primary failure.
    Example: explicit Conlon exhaustion retains partial state; a later build of the same
        construction resumes it.
    See also: publishCheckpoint; claimResumableCheckpoint; buildFiniteGroup.
*)
constructionFailure[failure_Failure, reference_, capabilities_Association, options_Association,
    resume_ : None] := Module[{details, retained = Missing["NotStored"], status, resumable},
    details = KeyDrop[failure[[2]], {"Checkpoint", "SourceCheckpoint"}];
    Which[
        !TrueQ[options[StoreGAPState]] || !StringQ[reference], Null,
        AssociationQ[resume] && reference === resume["Source"],
        status = checkpointRecord[reference, capabilities];
        retained = <|"GAPCachePath" -> If[FailureQ[status], Missing["NotAvailable"],
                status["WorkspaceArtifact"]["File"]],
            "GAPCacheMetadata" -> resume["Claim"]["Metadata"], "Resumable" -> True|>,
        True,
        status = checkpointRecord[reference, capabilities];
        resumable = !FailureQ[status] && AssociationQ[resume] &&
            MemberQ[{"BaseReady", "Partial"}, status["Data"]["Status"]];
        retained = If[resumable, publishCheckpoint[reference, capabilities, resume["Key"]],
            publishCheckpoint[reference, capabilities]];
        (* Only a base or partial state is resumable; a complete checkpoint is retained plainly. *)
        If[AssociationQ[retained], retained["Resumable"] = resumable]
    ];
    Failure[failure[[1]], Join[details, <|"Operation" -> "BuildGroup",
        "Recovery" -> If[FailureQ[retained], Missing["RetentionFailed"], retained]|>,
        If[FailureQ[retained], <|"RetentionFailure" -> retained|>, <||>]]]
];

(*
    Summary: Publish one complete verified native candidate as a fresh live group.
    Parameters: candidate — verified phase-runner result; capabilities — current probe;
        options — validated construction options including Name and StoreGAPState;
        source — diagnostic StateSource, "Constructed" (default) or "Resumed"; extra — optional
        diagnostics (for example ResumeFailure) added to LastComputation.
    Options/defaults: Retention is attempted after establishing a mathematically valid handle.
    Returns: Group or Failure carrying PartialResult when its requested persistence fails.
    Effects: Issues a private provenance receipt; allocates the registry entry and attaches its native
        envelope and diagnostics in one abort-protected step; then optionally retains a checkpoint
        and records its metadata in a second revision.
    Failures: Modified candidate data cannot match the independently registered checkpoint.
    Example: character-only A5 publication supplies NumberOfRep=5 without any matrices.
    See also: recordValidatedGroupResult; newGroup; publishCheckpoint; commitGroup.
*)
publishConstructedGroup[candidate_Association, capabilities_Association, options_Association,
    source_ : "Constructed", extra_ : <||>] := Module[
    {record, receipt, group, retained = <||>, patch, committed},
    record = checkpointRecord[Lookup[candidate, "Checkpoint", None], capabilities];
    If[FailureQ[record], Return[record]];
    If[Lookup[candidate, "Status", None] =!= "Verified" ||
        record["Data"]["Status"] =!= "Complete" || record["Data"] =!= Lookup[candidate, "Data", None],
        Return[makeFailure["UnboundGroupData", "The publication candidate does not match a complete verified checkpoint."]]];
    receipt = recordValidatedGroupResult[record["Data"],
        <|"Source" -> "OwnedWorker", "Reference" -> candidate["Checkpoint"]|>];
    If[FailureQ[receipt], Return[receipt]];
    patch = <|"NativeEnvelope" -> record["Native"],
        "LastComputation" -> <|"Operation" -> "BuildGroup", "Status" -> "Complete",
        "RequestID" -> record["Data"]["RequestID"], "StateSource" -> source,
        "Attempts" -> Lookup[candidate, "Outcomes", {}], "Skipped" -> Lookup[candidate, "Skipped", {}]|>|>;
    If[AssociationQ[extra], patch["LastComputation"] = Join[patch["LastComputation"], extra]];
    (* Allocation and its native envelope form one uninterruptible registry step, so an abort
       cannot leave a half-published handle. The slower retention copy follows separately. *)
    committed = AbortProtect[
        group = newGroup[record["Data"], receipt, options[Name]];
        If[FailureQ[group], group,
            (* Record the live handle before an abort deferred by this block can fire. *)
            $PublishedConstructionGroup = group;
            If[TrueQ[$ProgressActive], $ProgressPartialResult = group];
            commitGroup[group, 0, patch]]];
    If[FailureQ[committed], Return[committed]];
    If[TrueQ[options[StoreGAPState]], retained = publishCheckpoint[candidate["Checkpoint"], capabilities]];
    committed = commitGroup[group, 1, If[FailureQ[retained],
        <|"LastComputation" -> Join[patch["LastComputation"], <|"Status" -> "SaveFailed"|>]|>, retained]];
    If[FailureQ[committed], Return[Failure[committed[[1]], Join[committed[[2]], <|"PartialResult" -> group|>]]]];
    If[FailureQ[retained], Failure[retained[[1]], Join[retained[[2]],
        <|"PartialResult" -> group, "RemainingWork" -> {"RetainGAPState"}|>]], group]
];
publishConstructedGroup[___] := makeFailure["UnboundGroupData", "Expected a verified complete construction candidate."];

(* The handle published by the current constructInCall, visible to its abort handler. *)
If[!ValueQ[$PublishedConstructionGroup], $PublishedConstructionGroup = None];

(* Owning adapters of optional builder stages; RepresentationJobs.wl installs ComputeRepresentations.
   Stage-1 optional data adapters join after their group-level contracts are implemented and tested. *)
If[!AssociationQ[$BuilderEnrichments], $BuilderEnrichments = <||>];
(*
    Summary: Complete explicitly requested builder enrichment through installed owning adapters.
    Parameters: group — accepted character-complete handle; options — validated builder settings.
    Options/defaults: ComputeElements/ComputeSubgroups=False; ComputeRepresentations=True.
    Returns: Same Group or Failure with PartialResult and RemainingWork.
    Effects: Owning adapters may update the group; absent capabilities never appear complete.
    Failures: Missing/failing requested adapters preserve the accepted character-only group.
    Example: with the default ComputeRepresentations=True the representation stage (builderRepresentations,
        RepresentationJobs.wl) computes every irrep; an uninstalled capability reports CapabilityUnavailable.
    See also: BuildGroup; GroupElementWords; GroupSubgroups; VVMFArch/step2Plan.md.
*)
finishGroupBuild[group_Group, options_Association] := Module[{requested, remaining, result, adapter, failure = None},
    requested = Select[{ComputeElements, ComputeSubgroups, ComputeRepresentations}, TrueQ[options[#]] &];
    remaining = requested;
    Do[
        adapter = Lookup[$BuilderEnrichments, option, None];
        result = If[adapter === None,
            makeFailure["CapabilityUnavailable", "The requested builder capability is not installed.",
                <|"Capability" -> SymbolName[option]|>], adapter[group, options]];
        If[FailureQ[result],
            failure = Failure[result[[1]], Join[result[[2]],
                <|"PartialResult" -> group, "RemainingWork" -> (SymbolName /@ remaining)|>]];
            Break[]];
        remaining = Rest[remaining], {option, requested}];
    If[FailureQ[failure], failure, group]
];

(*
    Summary: Admit a claimed resumable construction state for this call after exact matching.
    Parameters: claim — claimResumableCheckpoint result; construction/modular — this request;
        capabilities — current probe; call — owning checkpoint call.
    Options/defaults: The entry must be BaseReady/Partial with the same construction and S/T words.
    Returns: <|"Key","Source","Claim"|> with a tracked, leased checkpoint reference; "Unusable" when
        the entry can never be resumed by this runtime/request; "Cancelled" when admission was
        aborted; "Busy" for other transient failures.
    Effects: Acquires a lease and registers it with the call, which releases it at call end.
        Admission checks bytes, runtime, exact mathematics and manifest; each later attempt still
        restores it in a fresh worker and compares the native reexport before computing.
    Failures: Caller releases or consumes the claim for non-association results.
    Example: a failed Conlon build of SL(2,3) is resumed by a later DixonSchneider build.
    See also: claimResumableCheckpoint; admitCheckpoint; buildFiniteGroup.
*)
resumeClaimedConstruction[claim_Association, construction_Association, modular_,
    capabilities_Association, call_Association] := Module[{reference, tracked, record, data, names, assigned},
    (* Admission and call tracking form one step, so an abort cannot leak the lease. *)
    AbortProtect[
        reference = admitCheckpoint[claim["Metadata"], capabilities];
        tracked = If[StringQ[reference], trackCheckpointSource[call["ID"], reference], None];
        If[FailureQ[tracked], releaseCheckpoint[reference]]];
    If[FailureQ[reference], Return[Which[
        MemberQ[{"IncompatibleCheckpoint", "InvalidCheckpoint", "MissingCheckpoint"}, reference[[1]]], "Unusable",
        reference[[1]] === "Cancelled", "Cancelled", True, "Busy"]]];
    If[FailureQ[tracked], Return["Busy"]];
    record = checkpointRecord[reference, capabilities];
    If[FailureQ[record], Return["Unusable"]];
    data = record["Data"];
    names = Lookup[data["Generators"], "Name", {}];
    assigned = data["ModularAssignment"];
    If[!MemberQ[{"BaseReady", "Partial"}, data["Status"]] ||
        canonicalJSON[data["Construction"]] =!= canonicalJSON[construction] ||
        If[AssociationQ[modular],
            !AssociationQ[assigned] || encodeWord[assigned["S"], names] =!= modular["sWord"] ||
                encodeWord[assigned["T"], names] =!= modular["tWord"],
            !MissingQ[assigned]],
        Return["Unusable"]];
    <|"Key" -> constructionResumeKey[construction, modular], "Source" -> reference, "Claim" -> claim|>
];
resumeClaimedConstruction[___] := "Unusable";

(*
    Summary: Construct the base once, compute bound characters, publish and finish requested work.
    Parameters: construction — validated encoded typed or explicitly authorized gapCode record;
        options — validated effective builder settings; modular — None or explicit identity/S/T
        word request used by BuildModularGroup, default None.
    Options/defaults: Automatic character batches use the shared scheduler; base construction is
        independent of character model selection and uses the whole sequential memory allocation.
    Returns: Complete Group, or typed Failure with accepted partial/recovery information.
    Effects: Probes GAP, runs owned workers/checkpoints, retains state when requested and cleans
        all temporary files at call completion, failure, cancellation or thrown exit.
        With StoreGAPState=True a retained base/partial state of the same construction and S/T
        words, left by an earlier failed build, is claimed and resumed instead of rebuilt; a
        failure retains its latest state as resumable. The claim is consumed once a group or a
        newer resumable state supersedes it and released otherwise, including on abort.
    Failures: Finiteness, input, method, resources, verification, storage and requested enrichment.
    Example: a typed finite matrix construction follows the same pipeline as a catalogue group.
    See also: runAttempt; runCharacterRequest; withCheckpointCall; publishConstructedGroup.
*)
(* The acceptance level of a build (methodOptionsPlan.md 2C.6): its Verification. *)
buildFiniteGroup[construction_Association, options_Association, modular_ : None] :=
    Block[{$GroupAcceptanceLevel = groupStatusLevel[Switch[Lookup[options, Verification, Automatic], None, "Unverified", "Numerical", "Numerical", _, "Exact"]]},
        buildFiniteGroupWork[construction, options, modular]];
buildFiniteGroupWork[construction_Association, options_Association, modular_ : None] := withProgress[
    options, Which[modular =!= None, "BuildModularGroup", construction["type"] === "gapCode",
        "BuildGroupFromGAP", True, "BuildGroup"], Function[Null,
        Module[{capabilities, operation},
            If[options[MemoryBudget] < 128*2^20,
                Return[makeFailure["MemoryLimit", "The construction budget is below its initial admission estimate."]]];
            progressReport[<|"Event" -> "Stage", "Phase" -> "Checking GAP"|>];
            capabilities = CheckGAP[]; If[FailureQ[capabilities], Return[capabilities]];
            operation = If[construction["type"] === "gapCode", "ConstructGAP", "Construct"];
            withCheckpointCall[Function[call,
                constructInCall[construction, options, modular, capabilities, call, operation]]]
        ]
    ]
];

(*
    Summary: Claim and admit a resumable state for this construction when retention is enabled.
    Parameters: key — constructionResumeKey; construction/modular — this request;
        capabilities — current probe; call — owning checkpoint call.
    Options/defaults: The caller invokes this only with StoreGAPState=True.
    Returns: Claim/Resume/ResumeFailure association; Resume is None when nothing is resumed.
    Effects: May claim, admit and lease an entry; an unusable entry's claim is consumed and a busy
        entry's claim released here. A storage failure is reported, not mistaken for no state.
    Failures: Returned in ResumeFailure; construction then proceeds from a fresh base, except that a
        cancellation (an abort in this phase, which also releases any claim) ends the build.
    Example: with no retained state, <|"Claim" -> None, "Resume" -> None, "ResumeFailure" -> None|>.
    See also: claimResumableCheckpoint; resumeClaimedConstruction; constructInCall.
*)
claimConstructionResume[key_String, construction_Association, modular_, capabilities_Association,
    call_Association] := Module[{claim = None, resume, released, cancelled},
    cancelled = makeFailure["Cancelled", "The group construction was cancelled."];
    CheckAbort[
        progressReport[<|"Event" -> "Stage", "Phase" -> "Checking resumable state"|>];
        claim = claimResumableCheckpoint[key];
        If[MatchQ[claim, Failure["Cancelled", _]], Return[<|"Claim" -> None, "Resume" -> None, "ResumeFailure" -> cancelled|>]];
        If[FailureQ[claim], Return[<|"Claim" -> None, "Resume" -> None, "ResumeFailure" -> claim|>]];
        If[!AssociationQ[claim], Return[<|"Claim" -> None, "Resume" -> None, "ResumeFailure" -> None|>]];
        resume = resumeClaimedConstruction[claim, construction, modular, capabilities, call];
        If[AssociationQ[resume], Return[<|"Claim" -> claim, "Resume" -> resume, "ResumeFailure" -> None|>]];
        released = AbortProtect[releaseResumeClaim[claim, resume === "Unusable"]];
        <|"Claim" -> None, "Resume" -> None, "ResumeFailure" -> Which[
            resume === "Cancelled", cancelled, FailureQ[released], released,
            True, makeFailure["ResumeUnavailable", "A retained state was found but could not be resumed.",
                <|"Reason" -> resume, "EntryID" -> claim["EntryID"]|>]]|>,
        (* An abort after claiming must not leave this kernel holding the claim. *)
        If[AssociationQ[claim], AbortProtect[releaseResumeClaim[claim, False]]];
        <|"Claim" -> None, "Resume" -> None, "ResumeFailure" -> cancelled|>]
];
claimConstructionResume[___] := <|"Claim" -> None, "Resume" -> None,
    "ResumeFailure" -> makeFailure["InvalidRequest", "Expected a resume key and construction request."]|>;

(*
    Summary: Compute and verify the base and complete characters from a fresh or resumed source.
    Parameters: construction/options/modular/capabilities/call/operation — constructInCall inputs;
        key — resume key or None; resume — None or resumeClaimedConstruction result.
    Options/defaults: A resumed source skips base construction.
    Returns: <|"Result" -> complete candidate or Failure, "Consume" -> Boolean|>; Consume is True when
        a newer resumable state or a complete candidate supersedes the resumed source.
    Effects: Runs owned workers; on failure retains the latest verified state per constructionFailure.
    Failures: Dependency, construction and character failures are returned in Result.
    Example: a resumed Conlon partial completed by Dixon-Schneider returns Consume -> True.
    See also: constructInCall; runCharacterRequest; constructionFailure.
*)
constructFromSource[construction_Association, options_Association, modular_, capabilities_Association,
    call_Association, operation_String, key_, resume_] := Module[
    {request, descriptor, context, base, complete, reference, failure, dependencies, done},
    done[result_, consume_] := <|"Result" -> result, "Consume" -> TrueQ[consume]|>;
    request = <|"operation" -> operation, "requestID" -> CreateUUID["request-"],
        "stateID" -> CreateUUID["state-"], "generatorIdentity" -> CreateUUID["generators-"],
        "stateGeneration" -> "0", "construction" -> construction|>;
    If[AssociationQ[modular], request["modularAssignment"] = modular;
        (* None skips the S,T proof (relations, centrality, generation; methodOptionsPlan.md 2C.4) *)
        If[$GroupAcceptanceLevel === None, request["stCheck"] = "Skip"]];
    (* "Numerical" or None: GAP keeps the transport and skips the character proof (2C.6) *)
    If[MemberQ[{"Numerical", None}, $GroupAcceptanceLevel], request["characterCheck"] = "TransportOnly"];
    descriptor = <|"Operation" -> operation, "Method" -> "GAP", "Model" -> "Original",
        "RecoveryStrategy" -> "Native", "WorkKey" -> operation, "Tier" -> 0,
        "Parallel" -> False, "MinCores" -> 1, "MemoryEstimate" -> 128*2^20,
        "Availability" -> "Eligible", "Reason" -> None, "AllocatedCores" -> 1,
        "AllocatedMemory" -> options[MemoryBudget]|>;
    context = <|"Capabilities" -> capabilities, "Directory" -> call["Directory"], "Options" -> options|>;
    If[AssociationQ[resume],
        base = <|"Checkpoint" -> resume["Source"]|>,
        base = runAttempt[None, descriptor, request, context];
        If[AssociationQ[base], noteConstructionCheckpoint[base["Checkpoint"]]];
        dependencies = checkConstructionDependencies[construction];
        If[FailureQ[dependencies], Return[done[dependencies, False]]];
        If[FailureQ[base], Return[done[constructionFailure[base, None, capabilities, options], False]]]];
    complete = runCharacterRequest[base["Checkpoint"], options, capabilities, call["Directory"]];
    If[FailureQ[complete],
        reference = Lookup[complete[[2]], "Checkpoint", base["Checkpoint"]];
        failure = constructionFailure[complete, reference, capabilities, options,
            Which[AssociationQ[resume], resume,
                StringQ[key], <|"Key" -> key, "Source" -> None, "Claim" -> None|>, True, None]];
        Return[done[failure, AssociationQ[resume] && reference =!= resume["Source"] &&
            TrueQ[Lookup[Replace[failure[[2]]["Recovery"], Except[_Association] -> <||>], "Resumable", False]]]]];
    dependencies = checkConstructionDependencies[construction];
    If[FailureQ[dependencies], Return[done[dependencies, False]]];
    done[complete, True]
];
constructFromSource[___] := <|"Result" -> makeFailure["InvalidRequest", "Malformed construction call."],
    "Consume" -> False|>;

(*
    Summary: Construct, publish and enrich one group inside an owned call, owning any resume claim.
    Parameters: construction/options/modular — validated build request; capabilities — probe;
        call — owning checkpoint call; operation — Construct or ConstructGAP.
    Options/defaults: StoreGAPState=True enables resumption and resumable failure retention.
    Returns: Group or Failure; a failed claim release or resume admission is attached as
        ClaimReleaseFailure/ResumeFailure to a returned Failure, or to the group's LastComputation.
    Effects: The claim is released or consumed exactly once after computation, including when the
        computation is aborted (the abort is consumed first and returned as Cancelled, carrying any
        group already published as PartialResult with its RemainingWork) or throws. A cancelled or
        thrown-out build with StoreGAPState=True retains its latest verified checkpoint as resumable
        (on the Throw exit too, before the thrown value propagates unchanged; a failed release there
        is not reported, and the stale claim stays reclaimable by later builds). Requested enrichment runs after the
        claim is released, also after a retention failure, whose RemainingWork then lists both.
    Failures: As constructFromSource and publishConstructedGroup; a claim that cannot be released
        stays reclaimable by later builds in this kernel.
    Example: aborting a resumed build returns Failure["Cancelled", ...] with the entry resumable again.
    See also: claimConstructionResume; constructFromSource; releaseResumeClaim.
*)
constructInCall[construction_Association, options_Association, modular_, capabilities_Association,
    call_Association, operation_String] := Block[{$PublishedConstructionGroup = None,
    $TrackConstructionCheckpoint = True, $ConstructionCheckpoint = None}, Module[
    {dependencies, key = None, resumeState = <|"Claim" -> None, "Resume" -> None, "ResumeFailure" -> None|>,
        outcome, released = True, pending = False, result, extra, group, data, requested, finished,
        bodyDone = False, retainProgress},
    requested = SymbolName /@ Select[{ComputeElements, ComputeSubgroups, ComputeRepresentations},
        TrueQ[options[#]] &];
    dependencies = checkConstructionDependencies[construction];
    If[FailureQ[dependencies], Return[dependencies]];
    If[TrueQ[options[StoreGAPState]],
        key = constructionResumeKey[construction, modular];
        resumeState = claimConstructionResume[key, construction, modular, capabilities, call]];
    If[MatchQ[resumeState["ResumeFailure"], Failure["Cancelled", _]], Return[resumeState["ResumeFailure"]]];
    extra = DeleteCases[<|"ResumeFailure" -> resumeState["ResumeFailure"]|>, None];
    pending = AssociationQ[resumeState["Claim"]];
    (* A cancelled or thrown-out build retains its latest verified checkpoint, like any other
       character failure; returns the Failure carrying Recovery and whether the claim is superseded. *)
    retainProgress[failure_] := Module[{retained},
        retained = AbortProtect[constructionFailure[failure, $ConstructionCheckpoint, capabilities, options,
            Which[AssociationQ[resumeState["Resume"]], resumeState["Resume"],
                StringQ[key], <|"Key" -> key, "Source" -> None, "Claim" -> None|>, True, None]]];
        <|"Result" -> retained, "Consume" -> AssociationQ[resumeState["Resume"]] &&
            StringQ[$ConstructionCheckpoint] && $ConstructionCheckpoint =!= resumeState["Resume"]["Source"] &&
            TrueQ[Lookup[Replace[Lookup[retained[[2]], "Recovery", None], Except[_Association] -> <||>],
                "Resumable", False]]|>];
    WithCleanup[
        (* Consume an abort before cleanup: storage transactions would otherwise observe it. *)
        outcome = CheckAbort[
            Module[{computed = constructFromSource[construction, options, modular, capabilities,
                    call, operation, key, resumeState["Resume"]], published},
                If[FailureQ[computed["Result"]], computed,
                    (* The claim is consumed only once a group has actually been published. *)
                    published = publishConstructedGroup[computed["Result"], capabilities, options,
                        If[AssociationQ[resumeState["Resume"]], "Resumed", "Constructed"], extra];
                    <|"Result" -> published, "Candidate" -> computed["Result"],
                        "Consume" -> !FailureQ[published] ||
                            MatchQ[Lookup[published[[2]], "PartialResult", None], _Group]|>]],
            (* An abort after publication still returns the live group it produced. *)
            If[MatchQ[$PublishedConstructionGroup, _Group],
                <|"Result" -> makeFailure["Cancelled", "The group construction was cancelled.",
                    <|"PartialResult" -> $PublishedConstructionGroup, "RemainingWork" -> Join[
                        If[TrueQ[options[StoreGAPState]] &&
                            MissingQ[$PublishedConstructionGroup["GAPCachePath"]], {"RetainGAPState"}, {}],
                        requested]|>], "Consume" -> True|>,
                retainProgress[makeFailure["Cancelled", "The group construction was cancelled."]]]];
        bodyDone = True;
        (* A group carrying the resumed state identity supersedes the entry, even if an abort
           interrupted the build after publication. *)
        If[pending, pending = False;
            released = AbortProtect[releaseResumeClaim[resumeState["Claim"], TrueQ[outcome["Consume"]] ||
                liveGroupStateQ[resumeState["Claim"]["Metadata"]["StateID"]]]]],
        (* Throw exit (for example a failing progress callback): retain progress, then release. *)
        If[!bodyDone,
            outcome = If[MatchQ[$PublishedConstructionGroup, _Group], <|"Consume" -> True|>,
                retainProgress[makeFailure["Cancelled", "The group construction was cancelled."]]]];
        If[pending, pending = False; releaseResumeClaim[resumeState["Claim"],
            TrueQ[outcome["Consume"]] || liveGroupStateQ[resumeState["Claim"]["Metadata"]["StateID"]]]]];
    If[FailureQ[released], AssociateTo[extra, "ClaimReleaseFailure" -> released]];
    result = outcome["Result"];
    group = Which[MatchQ[result, _Group], result,
        FailureQ[result] && MatchQ[Lookup[result[[2]], "PartialResult", None], _Group], result[[2]]["PartialResult"],
        True, None];
    If[group === None, Return[If[FailureQ[result], Failure[result[[1]], Join[result[[2]], extra]], result]]];
    If[KeyExistsQ[extra, "ClaimReleaseFailure"],
        data = groupData[group];
        If[AssociationQ[data], commitGroup[group, data["Revision"],
            <|"LastComputation" -> Join[data["LastComputation"], extra]|>]]];
    If[MatchQ[result, Failure["Cancelled", _]] || !KeyExistsQ[outcome, "Candidate"], Return[result]];
    (* Requested enrichment still runs after a retention failure; all missing work is reported. *)
    finished = Block[{$ActiveGroupCall = <|"Group" -> group, "Call" -> call,
        "Capabilities" -> capabilities, "Checkpoint" -> outcome["Candidate"]["Checkpoint"]|>},
        finishGroupBuild[group, options]];
    Which[
        !FailureQ[result], finished,
        FailureQ[finished], Failure[result[[1]], Join[result[[2]], <|"RemainingWork" ->
            DeleteDuplicates[Join[Lookup[result[[2]], "RemainingWork", {}],
                Lookup[finished[[2]], "RemainingWork", {}]]], "EnrichmentFailure" -> finished|>]],
        True, result]
]];
constructInCall[___] := makeFailure["InvalidRequest", "Malformed construction call."];

(*
    Summary: Build a finite group from a typed construction with mandatory complete characters.
    Status: Alpha.
    Parameters: spec — GroupPresentation, CatalogueGroup, PermutationGroupSpecification or
        MatrixGroupSpecification using the exact schemas in GroupInput.wl.
    Options/defaults: See $BuilderDefaults and step1Plan.md. StoreGAPState defaults True;
        ComputeRepresentations defaults True and requires the stage-2 adapter.
    Returns: Fresh shared Group handle or Failure, possibly with an accepted PartialResult.
    Effects: Computes through owned GAP workers; optional checkpoint retention and enrichment.
    Failures: Invalid input/options fail before GAP starts. Operational failures preserve
        accepted mathematical data and clean call-owned resources.
    Example: BuildGroup[CatalogueGroup["AlternatingGroup", 5], ComputeRepresentations -> False]
        returns a group of order 60 with five irreducible characters.
    See also: BuildGroupFromGAP; NumberOfRep; VVMFToolConfiguration.
*)
BuildGroup[specification_, options : OptionsPattern[]] := Module[{effective, construction},
    effective = resolveOperationOptions[BuildGroup, "BuildGroup", {options}];
    If[FailureQ[effective], Return[effective]];
    (* a relation string (v1 and GAP form) is accepted besides the typed specifications (uxUpdatePlan.md 4) *)
    (* a string must look like relations (brackets, ^, *, ., =, commas or parentheses); other strings stay invalid *)
    construction = If[StringQ[specification], If[StringContainsQ[specification, "[" | "^" | "*" | "." | "=" | "," | "("], RelationString[specification],
        makeFailure["InvalidSpecification", "A string specification must be a relation string such as \"[a^2, b^3, (a*b)^3]\"."]], specification];
    If[FailureQ[construction], Return[construction]];
    construction = encodeConstruction[construction];
    If[FailureQ[construction], construction, announceGroup[buildFiniteGroup[construction, effective]]]
];
BuildGroup[___] := makeFailure["InvalidInput", "Expected a typed group specification and option rules."];

(*
    Summary: Execute an explicitly supplied GAP recipe and build its validated finite group.
    Status: Alpha.
    Parameters: code — source defining VVMFInputGroup and ordered VVMFInputGenerators.
    Options/defaults: Builder options plus required GeneratorNames and ConstructionDependencies->{}.
    Returns: Fresh Group or Failure, possibly with accepted PartialResult or retained recovery.
    Effects: Deliberately executes the submitted GAP source; reads/hashes declared inputs and
        retains exact source/dependency identities in construction metadata.
    Failures: Unknown options, missing names, invalid dependencies, source/native errors and
        failed finiteness/generation/character verification are explicit.
    Example: BuildGroupFromGAP["VVMFInputGroup := CyclicGroup(3);; VVMFInputGenerators := GeneratorsOfGroup(VVMFInputGroup);;",
        GeneratorNames->{"a"}, ComputeRepresentations->False] builds C3.
    See also: BuildGroup; explicitGAPConstruction; VVMF_ConstructRaw.
*)
BuildGroupFromGAP[code_String, options : OptionsPattern[]] := Module[{effective, construction},
    effective = resolveOperationOptions[BuildGroupFromGAP, "BuildGroupFromGAP", {options}];
    If[FailureQ[effective], Return[effective]];
    construction = explicitGAPConstruction[code, effective];
    If[FailureQ[construction], construction, buildFiniteGroup[construction, effective]]
];
BuildGroupFromGAP[___] := makeFailure["InvalidInput", "Expected explicit GAP source and option rules."];

(*
    Summary: Build a finite modular realization with an explicitly validated recorded S,T pair.
    Signatures: BuildModularGroup[label_String, opts]; BuildModularGroup[pres_GroupPresentation, opts].
    Status: Alpha.
    Parameters: label — catalogue realization such as 24-3I or 24-3II; pres — typed presentation
        whose recorded generator names are exactly S and T, in either order.
    Options/defaults: BuildGroup options. S and T denote their named generators, not list positions.
    Returns: Group with a validated ModularAssignment, or Failure with recovery when available.
    Effects: Runs the common finite construction/character pipeline; preserves the chosen realization.
    Failures: Unknown label, unsuitable names and group-level modular relation/generation failures.
    Example: BuildModularGroup["24-3I", ComputeRepresentations->False] builds the recorded
        order-24 realization; the distinct 24-3II label is never replaced by abstract-group ID.
    See also: ModularGroupSpecification; BuildGroup; VVMF_CheckST.
*)
BuildModularGroup[input : (_String | _GroupPresentation), options : OptionsPattern[]] := Module[
    {effective, specification, construction, assignment, label, group},
    effective = resolveOperationOptions[BuildModularGroup, "BuildModularGroup", {options}];
    If[FailureQ[effective], Return[effective]];
    (* a string is a catalogue label, or else a relation string (uxUpdatePlan.md 4, D1) *)
    label = If[StringQ[input] && catalogueLabelQ[input], input, None];
    specification = Which[StringQ[label], ModularGroupSpecification[label], StringQ[input], RelationString[input], True, input];
    If[FailureQ[specification], Return[specification]];
    construction = encodeConstruction[specification]; If[FailureQ[construction], Return[construction]];
    If[Sort[construction["names"]] =!= {"S", "T"},
        Return[makeFailure["InvalidModularSpecification", "The presentation must record exactly the named S and T generators."]]];
    assignment = <|"identity" -> CreateUUID["modular-"],
        "sWord" -> {{"S", "1"}}, "tWord" -> {{"T", "1"}}|>;
    If[StringQ[label] && effective[Name] === Automatic, effective[Name] = label];
    group = buildFiniteGroup[construction, effective, assignment];
    If[StringQ[label] && MatchQ[group, _Group], With[{set = SetCatalogueLabel[group, label]}, If[FailureQ[set], Return[set]]]];
    announceGroup[group]
];
(*
    Summary: Whether a string names an entry of the modular catalogue.
    Parameters: s — string.
    Options/defaults: None.
    Returns: True for a key of Data/ModularGroups.json or text of the form 24-3I (order-number and Roman numerals).
    Effects: Reads the catalogue.
    Failures: None.
    Example: catalogueLabelQ["24-3I"] is True; catalogueLabelQ["[S^4,(S*T)^3]"] is False.
    See also: BuildModularGroup; RelationString.
*)
catalogueLabelQ[s_String] := KeyExistsQ[modularCatalogue[], s] || StringMatchQ[s, RegularExpression["[0-9]+-[0-9]+[IVX]*"]];
BuildModularGroup[___] := makeFailure["InvalidInput", "Expected a modular label or presentation and options."];

True
