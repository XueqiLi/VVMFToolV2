(*
    :Title: Finite-group enrichment
    :Context: VVMFTool`Private`
    :Summary: Extend accepted groups through coherent restored or reconstructed GAP candidates.
    :Responsibilities: Source correspondence, atomic publication, element words and explicit S,T.
    :Dependencies: GroupConstruction.wl; CheckpointCalls.wl; GAP/GroupBinding.g;
        RepresentationJobs.wl (representationDataExtendsQ, at call time).
    :See Also: VVMFArch/step1Plan.md; GroupObject.wl.
*)

Options[GroupElementWords] = Join[Options[RestoreGAPState], {WordRecovery -> Automatic, Verification -> Automatic}];
Options[GroupWordOrder] = Append[Options[RestoreGAPState], WordRecovery -> Automatic];
Options[AssignModularGenerators] = Join[Options[RestoreGAPState], {WordRecovery -> Automatic, Verification -> Automatic}];

(*
    Summary: Select a matching call-owned or retained checkpoint before typed reconstruction.
    Parameters: group — live handle; accepted — its snapshot; capabilities — probe;
        call — registered call; local — known call-owned reference or None.
    Options/defaults: Missing/incompatible storage permits only typed reconstruction.
    Returns: Checkpoint/StateSource association, or Failure requiring explicit raw-code rebuild.
    Effects: Acquires/tracks a retained-source lease before inspecting executable workspace bytes.
    Failures: Ownership/lease failures are explicit. Unusable storage is recorded as CacheFailure.
    Example: StoreGAPState=False builders still pass their active-call reference to enrichment.
    See also: admitCheckpoint; groupEnvelope; enrichGroupInCall.
*)
groupComputationSource[group_Group, accepted_Association, capabilities_Association,
    call_Association, local_ : None] := Module[{reference = local, record, tracked, failure = None},
    If[reference === None && AssociationQ[accepted["GAPCacheMetadata"]],
        AbortProtect[
            reference = admitCheckpoint[accepted["GAPCacheMetadata"], capabilities];
            If[StringQ[reference], tracked = trackCheckpointSource[call["ID"], reference]]];
        If[StringQ[reference] && FailureQ[tracked], Return[tracked]]];
    If[StringQ[reference],
        record = checkpointRecord[reference, capabilities];
        If[!FailureQ[record] && sameGroupStateQ[record["Data"], accepted],
            Return[<|"Checkpoint" -> reference, "StateSource" -> If[local === None, "Restored", "CallCheckpoint"]|>]];
        failure = If[FailureQ[record], record,
            makeFailure["StateConflict", "The retained state does not match the accepted group."]],
        If[FailureQ[reference], failure = reference]];
    If[accepted["Construction"]["type"] === "gapCode",
        Return[makeFailure["ExplicitRebuildRequired", "No usable checkpoint remains. Explicitly rebuild this group from its retained GAP source.",
            <|"Construction" -> accepted["Construction"], "CacheFailure" -> failure|>]]];
    <|"Checkpoint" -> None, "StateSource" -> "Reconstructed", "CacheFailure" -> failure|>
];
groupComputationSource[___] := makeFailure["InvalidRequest", "Expected an accepted group and owned computation call."];

(*
    Summary: Save and independently verify one reconstructed source before algorithm attempts.
    Parameters: accepted/native — matching trusted group data; options/capabilities/call — ownership.
    Options/defaults: Keeps the accepted generation; each later candidate advances it once.
    Returns: Private verified checkpoint reference, or Failure without changing the live group.
    Effects: Constructs typed input once, transports certified data, saves and restores its workspace.
    Failures: Raw input, insufficient resources, changed correspondence or unsuccessful verification.
    Example: automatic subgroup methods resume this common source after an earlier method times out.
    See also: enrichGroupInCall; VVMF_RebindGroup; sameGroupStateQ.
*)
prepareGroupCheckpoint[accepted_Association, native_Association, options_Association,
    capabilities_Association, call_Association] := Module[{request, descriptor, context, candidate, record},
    If[Lookup[accepted["Construction"], "type", None] === "gapCode",
        Return[makeFailure["ExplicitRebuildRequired", "Executable source cannot be reconstructed implicitly."]]];
    request = <|"operation" -> "Reconstruct", "requestID" -> CreateUUID["reconstruct-"],
        "stateID" -> accepted["StateID"], "generatorIdentity" -> accepted["GeneratorIdentity"],
        "stateGeneration" -> ToString[accepted["StateGeneration"]], "acceptedGroup" -> native,
        "construction" -> accepted["Construction"], "characterIdentity" -> accepted["CharacterData"]["Identity"]|>;
    descriptor = <|"Operation" -> "Reconstruct", "Method" -> "GAP", "Model" -> "Original",
        "RecoveryStrategy" -> "Native", "WorkKey" -> "Reconstruct", "Tier" -> 0,
        "Parallel" -> False, "MinCores" -> 1, "MemoryEstimate" -> 128*2^20,
        "Availability" -> "Eligible", "Reason" -> None, "AllocatedCores" -> 1,
        "AllocatedMemory" -> options[MemoryBudget]|>;
    context = <|"Capabilities" -> capabilities, "Directory" -> call["Directory"], "Options" -> options|>;
    candidate = runAttempt[None, descriptor, request, context];
    If[FailureQ[candidate], Return[candidate]];
    record = checkpointRecord[Lookup[candidate, "Checkpoint", None], capabilities];
    If[FailureQ[record], Return[record]];
    If[Lookup[candidate, "Status", None] =!= "Verified" || record["Data"] =!= candidate["Data"] ||
        !sameGroupStateQ[record["Data"], accepted],
        Return[makeFailure["StateConflict", "The reconstructed source differs from accepted group mathematics."]]];
    candidate["Checkpoint"]
];
prepareGroupCheckpoint[___] := makeFailure["InvalidRequest", "Expected accepted typed group data and an owned call."];

(*
    Summary: Publish a verified next generation while preserving accepted mathematical identities.
    Parameters: group/accepted — live handle and expected snapshot; candidate — verified attempt;
        capabilities/options — execution settings; source — restore/reconstruction diagnostics.
    Options/defaults: StoreGAPState controls new retention; old cache files are not deleted here.
    Returns: Same Group or Failure; retention failure includes its accepted PartialResult.
    Effects: Verifies unchanged group/character correspondence, issues receipt, publishes optional
        retention and commits one registry revision with the matching inert native envelope.
    Failures: Changed immutable fields/characters, stale revision or unverified candidate cannot commit.
    Example: adding elements keeps every existing irrep and class ID unchanged.
    See also: commitGroup; publishCheckpoint; recordValidatedGroupResult.
*)
publishGroupEnrichment[group_Group, accepted_Association, candidate_Association,
    capabilities_Association, options_Association, source_Association] := Module[
    {record, data, receipt, retained, patch, committed, diagnostics, preferences},
    record = checkpointRecord[Lookup[candidate, "Checkpoint", None], capabilities];
    If[FailureQ[record], Return[record]];
    data = record["Data"];
    If[Lookup[candidate, "Status", None] =!= "Verified" || data =!= Lookup[candidate, "Data", None] ||
        data["Status"] =!= "Complete" || data["StateGeneration"] =!= accepted["StateGeneration"] + 1 ||
        KeyTake[data, $GroupImmutableKeys] =!= KeyTake[accepted, $GroupImmutableKeys] ||
        data["CharacterData"] =!= accepted["CharacterData"] ||
        (!MissingQ[accepted["Elements"]] && data["Elements"] =!= accepted["Elements"]) ||
        !subgroupDataExtendsQ[data["SubgroupData"], accepted["SubgroupData"]] ||
        !representationDataExtendsQ[data["Representations"], accepted["Representations"], Lookup[candidate, "ReplaceActive", {}]],
        Return[makeFailure["StateConflict", "Enrichment changed accepted mathematical identities or data."]]];
    (* a weak group is raised only by a proof (methodOptionsPlan.md 2C.6): weak character claims turn full only under
       ValidateGroup, and the group status rises only under ValidateGroup or a proved AssignModularGenerators; anything
       else is a state that claims more than was proved here, refused, never written *)
    If[data["Operation"] =!= "ValidateGroup" && (weakCharacterClaimsQ[accepted] && !weakCharacterClaimsQ[data] ||
            data["Operation"] =!= "AssignModularGenerators" && cgStatusRank[groupVerificationStatus[data]] > cgStatusRank[groupVerificationStatus[accepted]]),
        Return[makeFailure["StateConflict", "An enrichment cannot raise a group's verification status; use ValidateGroup."]]];
    receipt = recordValidatedGroupResult[data,
        <|"Source" -> "OwnedWorker", "Reference" -> candidate["Checkpoint"]|>];
    If[FailureQ[receipt], Return[receipt]];
    retained = If[TrueQ[options[StoreGAPState]], publishCheckpoint[candidate["Checkpoint"], capabilities],
        <|"GAPCachePath" -> Missing["NotStored"], "GAPCacheMetadata" -> Missing["NotStored"]|>];
    diagnostics = Join[data["LastComputation"], KeyDrop[source, "Checkpoint"],
        KeyTake[candidate, {"Outcomes", "Skipped", "SelectedAttempt"}],
        <|"Operation" -> data["Operation"], "Status" -> If[FailureQ[retained], "SaveFailed", "Complete"],
            "RequestID" -> data["RequestID"]|>];
    preferences = Lookup[accepted, "SuccessfulAttempts", <||>];
    (* only a winner verified at the full level teaches the planner (methodOptionsPlan.md 2C.5): a weak group's or a weak
       request's winner never reorders later full-level work *)
    If[StringQ[Lookup[candidate, "PreferenceKey", None]] &&
        AssociationQ[Lookup[candidate, "SelectedAttempt", None]] && MemberQ[{Automatic, "Exact"}, $GroupAcceptanceLevel] &&
        groupVerificationStatus[data] === "Exact",
        AssociateTo[preferences, candidate["PreferenceKey"] -> candidate["SelectedAttempt"]]];
    patch = Join[KeyDrop[data, $GroupImmutableKeys],
        (* the new generation's own status replaces the old one (absent means "Exact") *)
        <|"VerificationStatus" -> groupVerificationStatus[data]|>,
        <|"ValidationReceipt" -> receipt, "NativeEnvelope" -> record["Native"],
            "SuccessfulAttempts" -> preferences,
            "LastComputation" -> diagnostics|>,
        If[FailureQ[retained], <|"GAPCachePath" -> Missing["NotStored"],
            "GAPCacheMetadata" -> Missing["NotStored"]|>, retained]];
    (* R6: a changed modular assignment identity invalidates assignment-dependent derived data (the
       Unitarity cache records T-diagonality); element matrices and decompositions do not depend on it. *)
    If[Lookup[Replace[data["ModularAssignment"], Except[_Association] -> <||>], "Identity", None] =!=
            Lookup[Replace[accepted["ModularAssignment"], Except[_Association] -> <||>], "Identity", None],
        patch["RepresentationCache"] = ReplacePart[accepted["RepresentationCache"], {"Entries", "Unitarity"} -> <||>]];
    committed = commitGroup[group, accepted["Revision"], patch];
    If[FailureQ[committed], Return[committed]];
    If[AssociationQ[$ActiveGroupCall] && Lookup[$ActiveGroupCall, "Group", None] === group,
        $ActiveGroupCall["Checkpoint"] = candidate["Checkpoint"]];
    If[FailureQ[retained], Failure[retained[[1]], Join[retained[[2]], <|"PartialResult" -> group|>]], group]
];
publishGroupEnrichment[___] := makeFailure["UnboundGroupData", "Expected a verified enrichment candidate."];
(* the group's character claims are GAP's "TransportOnly" (a weak build or an unverified import) *)
weakCharacterClaimsQ[data_Association] := Lookup[Replace[Lookup[data, "Binding", <||>], Except[_Association] -> <||>], "nativeCharactersVerified", None] === "TransportOnly";
weakCharacterClaimsQ[_] := False;

(*
    Summary: Execute one enrichment against a verified source inside an existing owned call.
    Parameters: group/accepted — expected live state; operation/payload — validated request;
        options/capabilities/call — effective settings and ownership; local — temporary source.
    Options/defaults: Finite method/model/recovery batches share the configured resource allocation.
    Returns: Same Group or Failure. No result is published before paired-checkpoint verification.
    Effects: Reconstructs only typed data when needed, computes, saves/restores and publishes.
    Failures: Input provenance, resources, native computation, correspondence and commit errors.
    Example: a cache-evicted catalogue rebuild checks its certified generator presentation.
    See also: runGroupEnrichment; groupComputationSource; runGroupRequest.
*)
enrichGroupInCall[group_Group, accepted_Association, operation_String, payload_Association,
    options_Association, capabilities_Association, call_Association, local_ : None] := Module[
    {native, source, request, candidate, record, estimate = 128*2^20},
    native = groupEnvelope[accepted]; If[FailureQ[native], Return[native]];
    source = groupComputationSource[group, accepted, capabilities, call, local];
    If[FailureQ[source], Return[source]];
    request = Join[<|"operation" -> operation, "requestID" -> CreateUUID["request-"],
        "stateID" -> accepted["StateID"], "generatorIdentity" -> accepted["GeneratorIdentity"],
        "stateGeneration" -> ToString[accepted["StateGeneration"] + 1],
        "construction" -> accepted["Construction"], "characterIdentity" -> accepted["CharacterData"]["Identity"],
        "evictionEpoch" -> ToString[accepted["RepresentationCache"]["Epoch"]]|>, payload];
    If[source["Checkpoint"] === None,
        source["Checkpoint"] = prepareGroupCheckpoint[accepted, native, options, capabilities, call];
        If[FailureQ[source["Checkpoint"]], Return[source["Checkpoint"]]]];
    record = checkpointRecord[source["Checkpoint"], capabilities]; If[FailureQ[record], Return[record]];
    estimate = Max[estimate, 3 record["WorkspaceArtifact"]["Bytes"]];
    If[options[MemoryBudget] < estimate,
        Return[makeFailure["MemoryLimit", "The budget is below this checkpoint's admission estimate."]]];
    candidate = runGroupRequest[source["Checkpoint"], accepted, request, options, capabilities, call["Directory"]];
    If[FailureQ[candidate], Return[Failure[candidate[[1]], Join[KeyDrop[candidate[[2]],
        {"Checkpoint", "SourceCheckpoint"}], <|"Operation" -> operation|>, KeyDrop[source, "Checkpoint"]]]]];
    publishGroupEnrichment[group, accepted, candidate, capabilities, options, source]
];
enrichGroupInCall[___] := makeFailure["InvalidRequest", "Expected an accepted group enrichment request."];

(*
    Summary: Own the resource lifetime of a public group enrichment, or reuse its builder call.
    Parameters: group — live Group; operation/payload — validated native request; options — settings.
    Options/defaults: Active builder reuse is private and restricted to that exact group handle.
    Returns: Same Group or Failure.
    Effects: Probes GAP once for a standalone call; always releases call-owned workers/files/leases.
    Failures: Unknown groups, invalid resource limits, unavailable GAP and computation errors.
    Example: two builder enrichments share the latest successful call checkpoint with retention off.
    See also: withCheckpointCall; enrichGroupInCall; finishGroupBuild.
*)
(* An enrichment of a weakly built group accepts its weak claims at the group's own level (methodOptionsPlan.md 2C.6);
   ValidateGroup raises the level explicitly. *)
groupAcceptanceLevel[group_Group] := With[{data = groupData[group]}, If[AssociationQ[data], groupStatusLevel[groupVerificationStatus[data]], Automatic]];
runGroupEnrichment[group_Group, operation_String, payload_Association, options_Association] :=
    Block[{$GroupAcceptanceLevel = If[$GroupAcceptanceLevel === Automatic, groupAcceptanceLevel[group], $GroupAcceptanceLevel]},
        runGroupEnrichmentWork[group, operation, payload, options]];
runGroupEnrichmentWork[group_Group, operation_String, payload_Association, options_Association] :=
    withProgress[options, operation, Function[Null,
        Module[
            {accepted, capabilities},
            accepted = groupData[group]; If[FailureQ[accepted], Return[accepted]];
            If[TrueQ[$ProgressActive], $ProgressPartialResult = group];
            If[options[MemoryBudget] < 128*2^20,
                Return[makeFailure["MemoryLimit", "The budget is below the initial admission estimate."]]];
            If[AssociationQ[$ActiveGroupCall] && Lookup[$ActiveGroupCall, "Group", None] === group,
                Return[enrichGroupInCall[group, accepted, operation, payload, options,
                    $ActiveGroupCall["Capabilities"], $ActiveGroupCall["Call"], $ActiveGroupCall["Checkpoint"]]]];
            progressReport[<|"Event" -> "Stage", "Phase" -> "Checking GAP"|>];
            capabilities = CheckGAP[]; If[FailureQ[capabilities], Return[capabilities]];
            withCheckpointCall[Function[call,
                enrichGroupInCall[group, accepted, operation, payload, options, capabilities, call]]]
        ]
    ]];
runGroupEnrichment[___] := makeFailure["InvalidRequest", "Expected a live group enrichment request."];

(*
    Summary: Obtain every group element as a word on the recorded generators.
    Status: Alpha.
    Parameters: group — live finite Group.
    Options/defaults: Common GAP options; complete cached words return without a backend call.
    Returns: List of GroupWord values or Failure; the group is enriched in place on success.
    Effects: Optional GAP computation, verified checkpoint storage and atomic group update.
    Failures: Invalid input/options, unavailable source, resources and failed word recovery.
    Example: Length[GroupElementWords[g]] equals g["Order"], including one empty word for the trivial group.
    See also: BuildGroup; GroupWordOrder; StoreGAPState.
*)
GroupElementWords[group_Group, options : OptionsPattern[]] := Module[{effective, accepted, result},
    effective = resolveOperationOptions[GroupElementWords, "GroupElementWords", {options}];
    If[FailureQ[effective], Return[effective]];
    With[{allowed = proofComputationLevelQ["GroupElementWords", effective[Verification]]}, If[FailureQ[allowed], Return[allowed]]];
    accepted = groupData[group]; If[FailureQ[accepted], Return[accepted]];
    If[!MissingQ[accepted["Elements"]], Return[accepted["Elements"]]];
    result = runGroupEnrichment[group, "GroupElementWords", <||>, effective];
    If[FailureQ[result], result, group["Elements"]]
];
GroupElementWords[___] := makeFailure["InvalidInput", "Expected a live group and element options."];

Options[ValidateGroup] = Join[Options[RestoreGAPState], {Verification -> Automatic}];

(*
    Summary: Raise a weakly built group's own verification status (methodOptionsPlan.md 2C.6).
    Status: Alpha.
    Parameters: g — live Group.
    Options/defaults: Verification -> Automatic or "Exact" (GAP proves the character table: the full check on the retained
        workspace's native characters, or, in a state rebuilt from the saved envelope, a fresh native computation that must
        give the same rows; a skipped S,T check is proved too) or "Numerical" (one export-only generation read with
        Wolfram's numerical orthogonality, degree and integrality checks: at most "Numerical"; a skipped S,T check stays
        "Unverified"); None is InvalidOption; common GAP job options.
    Returns: <|"Previous", "VerificationStatus", "Raised"|>, or Failure.
    Effects: One GAP generation committed with a new receipt (the status changes in place; contexts, vectors and models
        built before keep their identities, since statuses are outside the context digest).
    Failures: InvalidOption; the GAP proof's failures (InvalidCharacters, InvalidModularGenerators, ...); resources.
    Example: ValidateGroup[BuildModularGroup["24-3I", Verification -> None]]["VerificationStatus"] is "Exact".
    See also: BuildGroup; ImportGroupData; ValidateRepresentation.
*)
ValidateGroup[group_Group, options : OptionsPattern[]] := Module[{effective, data, previous, level, result, after},
    effective = resolveOperationOptions[ValidateGroup, "ValidateGroup", {options}]; If[FailureQ[effective], Return[effective]];
    level = effective[Verification];
    If[level === None, Return[makeFailure["InvalidOption", "ValidateGroup checks: Verification is Automatic, \"Exact\" or \"Numerical\".", <|"Options" -> {Verification}|>]]];
    data = groupData[group]; If[FailureQ[data], Return[data]];
    previous = groupVerificationStatus[data];
    If[previous === "Exact" || (level === "Numerical" && previous === "Numerical"),
        Return[<|"Previous" -> previous, "VerificationStatus" -> previous, "Raised" -> False|>]];
    (* the source state is admitted at the group's own level; a proved table comes back with full claims ("Exact"),
       an export-only generation is read at "Numerical" *)
    result = Block[{$GroupAcceptanceLevel = If[level === "Numerical", "Numerical", groupAcceptanceLevel[group]]},
        runGroupEnrichment[group, "ValidateGroup", If[level === "Numerical", <|"level" -> "Export"|>, <|"stCheck" -> "Full"|>], effective]];
    If[FailureQ[result], Return[result]];
    after = groupVerificationStatus[groupData[group]];
    <|"Previous" -> previous, "VerificationStatus" -> after, "Raised" -> cgStatusRank[after] > cgStatusRank[previous]|>
];
ValidateGroup[___] := makeFailure["InvalidInput", "ValidateGroup expects a live group and options."];

(*
    Summary: Compute the exact order of an explicit word in a finite group.
    Status: Alpha.
    Parameters: group — live Group; word — GroupWord with names, powers and ordered products.
    Options/defaults: Common GAP options; no S,T assignment is needed.
    Returns: Positive integer or Failure.
    Effects: Reuses or reconstructs verified state; retains the successful generation when requested.
    Failures: Invalid word/options, missing unreplayable source, timeout or backend failure.
    Example: GroupWordOrder[g, GroupWord["a^-1"]] equals the order of generator a.
    See also: GroupWord; GroupElementWords; AssignModularGenerators.
*)
GroupWordOrder[group_Group, word_GroupWord, options : OptionsPattern[]] := Module[
    {effective, accepted, encoded, result},
    effective = resolveOperationOptions[GroupWordOrder, "GroupWordOrder", {options}];
    If[FailureQ[effective], Return[effective]];
    accepted = groupData[group]; If[FailureQ[accepted], Return[accepted]];
    encoded = encodeWord[word, Lookup[accepted["Generators"], "Name", {}]];
    If[FailureQ[encoded], Return[encoded]];
    result = runGroupEnrichment[group, "GroupWordOrder", <|"word" -> encoded|>, effective];
    If[FailureQ[result], result, decodeInteger[group["LastComputation"]["wordOrder"]["order"]]]
];
GroupWordOrder[group_Group, word_String, rest___] := GroupWordOrder[group, GroupWord[word], rest];
GroupWordOrder[___] := makeFailure["InvalidInput", "Expected a live group, GroupWord and options."];

(*
    Summary: Assign explicit S,T words after group-level modular relation and generation checks.
    Status: Alpha.
    Parameters: group — live finite Group; s/t — GroupWord values on its recorded generators.
    Options/defaults: Common GAP settings; each successful assignment receives a fresh identity.
    Returns: The same Group or Failure; failed assignment preserves the preceding assignment.
    Effects: Updates the mutable object after native verification and checkpoint publication.
    Failures: Invalid words, the relation (ST)^3 = S^4, noncentral S^2, or nongeneration.
    Example: AssignModularGenerators[g, GroupWord["a"], GroupWord["b"]] assigns the supplied pair.
    See also: BuildModularGroup; GroupWordOrder; the separate discovery/classification TODOs.
*)
AssignModularGenerators[group_Group, s_GroupWord, t_GroupWord, options : OptionsPattern[]] := Module[
    {effective, accepted, names, words},
    effective = resolveOperationOptions[AssignModularGenerators, "AssignModularGenerators", {options}];
    If[FailureQ[effective], Return[effective]];
    accepted = groupData[group]; If[FailureQ[accepted], Return[accepted]];
    names = Lookup[accepted["Generators"], "Name", {}];
    words = encodeWord[#, names] & /@ {s, t};
    If[AnyTrue[words, FailureQ], Return[First[Select[words, FailureQ]]]];
    (* Verification (methodOptionsPlan.md 2C.4): the S,T proof has no numerical analogue; None evaluates the words only
       (GAP's stCheck "Skip"), which makes the group's status "Unverified"; any other level proves the new pair, also on a
       state whose S,T mode was "Skip" (stCheck "Full" resets the persistent mode) *)
    If[effective[Verification] === "Numerical", Return[makeFailure["InapplicableOption",
        "The S,T relations and generation are group identities with no numerical check; use Automatic or None.", <|"Options" -> {Verification}|>]]];
    Block[{$GroupAcceptanceLevel = If[effective[Verification] === None, None, $GroupAcceptanceLevel]},
        runGroupEnrichment[group, "AssignModularGenerators", Join[<|"modularAssignment" ->
            <|"identity" -> CreateUUID["modular-"], "sWord" -> First[words], "tWord" -> Last[words]|>|>,
            <|"stCheck" -> If[effective[Verification] === None, "Skip", "Full"]|>], effective]]
];
AssignModularGenerators[group_Group, s : (_String | _GroupWord), t : (_String | _GroupWord), rest___] /; StringQ[s] || StringQ[t] :=
    AssignModularGenerators[group, If[StringQ[s], GroupWord[s], s], If[StringQ[t], GroupWord[t], t], rest];
AssignModularGenerators[___] := makeFailure["InvalidInput", "Expected a live group, explicit S,T words and options."];

(* Builder adapters receive only the public options applicable to their own operation. *)
AssociateTo[$BuilderEnrichments, ComputeElements -> Function[{group, options},
    GroupElementWords[group, Sequence @@ Normal[KeyTake[options, Append[Keys[$CommonJobDefaults], WordRecovery]]]]]];

True
