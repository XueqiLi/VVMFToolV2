(*
    :Title: Public prescribed generator maps
    :Context: VVMFTool`Private`
    :Summary: Compare supplied generator images using accepted source and target identities.
    :Responsibilities: Target certificate provenance, shared temporary lifetime and public reports.
    :Dependencies: GroupEnrichment.wl; GroupMapValidation.wl; GAP/GroupMaps.g.
    :See Also: CheckGeneratorMap in VVMFArch/step1Plan.md.
*)

Options[CheckGeneratorMap] = Join[Options[RestoreGAPState], {WordRecovery -> Automatic, Verification -> Automatic}];

(*
    Summary: Extract an independently accepted recorded-generator certificate for a map target.
    Parameters: accepted — private live-group snapshot with its native envelope and receipt.
    Options/defaults: None; an absent certificate is Missing[NotComputed], not a guessed presentation.
    Returns: Native target specification, Missing or Failure.
    Effects: Pure; groupEnvelope checks local provenance and exact envelope matching.
    Failures: Unbound or modified data cannot supply trusted target construction instructions.
    Example: a catalogue group's certified presentation can target a map without its workspace.
    See also: prepareMapTarget; VVMF_MapTarget; groupEnvelope.
*)
mapTargetSpecification[accepted_Association] := Module[{native, certificate},
    native = groupEnvelope[accepted]; If[FailureQ[native], Return[native]];
    certificate = Lookup[native["binding"], "generatorPresentation", Missing["NotComputed"]];
    If[MissingQ[certificate], Return[certificate]];
    <|"stateID" -> accepted["StateID"], "generatorIdentity" -> accepted["GeneratorIdentity"],
        "order" -> ToString[accepted["Order"]], "presentation" -> certificate|>
];
mapTargetSpecification[___] := makeFailure["InvalidGeneratorMap", "Expected an independently accepted map target."];

(*
    Summary: Obtain a target certificate within the map call, preserving its temporary checkpoint.
    Parameters: target — live Group; options/capabilities/call — validated shared execution context.
    Options/defaults: Certificate preparation uses Original and one native algorithm; the public
        GroupModel choice applies to the subsequent prescribed map, independently.
    Returns: Target specification and optional temporary Checkpoint, or Failure.
    Effects: Reuses a trusted certificate; otherwise enriches the target through its accepted
        workspace or typed reconstruction and retains the call-local source even with retention off.
    Failures: Missing raw workspace requires explicit rebuild; source text is never replayed.
    Example: mapping a raw group to itself can certify it and resume that same temporary state.
    See also: CheckGeneratorMap; mapTargetSpecification; enrichGroupInCall.
*)
prepareMapTarget[target_Group, options_Association, capabilities_Association, call_Association] := Module[
    {accepted, specification, result, local = None},
    accepted = groupData[target]; If[FailureQ[accepted], Return[accepted]];
    specification = mapTargetSpecification[accepted]; If[FailureQ[specification], Return[specification]];
    If[MissingQ[specification],
        Block[{$ActiveGroupCall = <|"Group" -> target, "Call" -> call,
            "Capabilities" -> capabilities, "Checkpoint" -> None|>},
            result = enrichGroupInCall[target, accepted, "GeneratorPresentation", <||>,
                Join[options, <|GroupModel -> "Original"|>], capabilities, call];
            local = $ActiveGroupCall["Checkpoint"]];
        If[FailureQ[result], Return[result]];
        specification = mapTargetSpecification[groupData[target]];
        If[FailureQ[specification], Return[specification]];
        If[MissingQ[specification],
            Return[makeFailure["InvalidGeneratorMap", "The native certificate computation returned no certificate."]]]];
    <|"Target" -> specification, "Checkpoint" -> local|>
];
prepareMapTarget[___] := makeFailure["InvalidGeneratorMap", "Expected a live target and owned computation context."];

(*
    Summary: Check whether the prescribed images define a homomorphism and an isomorphism.
    Status: Alpha.
    Parameters: source/target — live finite Groups; images — one target GroupWord per
        recorded source generator, in the source's recorded order.
    Options/defaults: Common GAP options from configuration; GroupModel defaults Automatic.
    Returns: Homomorphism, Injective, Surjective, Isomorphism booleans, Images and
        InverseImages (Missing[NotIsomorphism] unless isomorphic), with both group/generator IDs.
    Effects: May certify the target's recorded generators and enrich the source's GAP state.
        One owned call preserves temporary preparation; StoreGAPState controls later retention.
    Failures: Invalid words/arity/options fail before GAP. Undecided, unavailable, timed-out
        or failed computation returns Failure; only a checked invalid map returns false flags.
        No abstract isomorphism or modular-realization equivalence is inferred.
    Example: CheckGeneratorMap[c6,c3,{GroupWord["b"]}] is surjective but not injective
        when b is c3's recorded generator. An isomorphism additionally returns inverse words.
    See also: AssignModularGenerators; GroupWordOrder; GroupWord; VVMF_Map.
*)
CheckGeneratorMap[source_Group, target_Group, images_List, options : OptionsPattern[]] := Module[
    {effective, sourceData, targetData, encoded},
    effective = resolveOperationOptions[CheckGeneratorMap, "CheckGeneratorMap", {options}];
    If[FailureQ[effective], Return[effective]];
    With[{allowed = proofComputationLevelQ["CheckGeneratorMap", effective[Verification], True]}, If[FailureQ[allowed], Return[allowed]]];
    sourceData = groupData[source]; If[FailureQ[sourceData], Return[sourceData]];
    targetData = groupData[target]; If[FailureQ[targetData], Return[targetData]];
    If[Length[images] =!= Length[sourceData["Generators"]] || !AllTrue[images, MatchQ[#, _GroupWord] &],
        Return[makeFailure["InvalidGeneratorMap", "Supply one target GroupWord per recorded source generator."]]];
    encoded = encodeWord[#, Lookup[targetData["Generators"], "Name"]] & /@ images;
    If[AnyTrue[encoded, FailureQ], Return[First[Select[encoded, FailureQ]]]];
    If[effective[MemoryBudget] < 128*2^20,
        Return[makeFailure["MemoryLimit", "The map budget is below the initial admission estimate."]]];
    withProgress[effective, "CheckGeneratorMap", Function[Null,
        Module[{capabilities},
            $ProgressPartialResult = source;
            progressReport[<|"Event" -> "Stage", "Phase" -> "Checking GAP"|>];
            capabilities = CheckGAP[]; If[FailureQ[capabilities], Return[capabilities]];
            withCheckpointCall[Function[call, Module[{prepared, accepted, request, result, nativeGenerators},
                prepared = prepareMapTarget[target, effective, capabilities, call];
                If[FailureQ[prepared], Return[prepared]];
                accepted = groupData[source]; If[FailureQ[accepted], Return[accepted]];
                request = <|"targetGroup" -> prepared["Target"], "imageWords" -> encoded|>;
                result = enrichGroupInCall[source, accepted, "CheckGeneratorMap", request, effective,
                    capabilities, call, If[source === target, prepared["Checkpoint"], None]];
                If[FailureQ[result], Return[result]];
                nativeGenerators = (<|"id" -> #["ID"], "name" -> #["Name"]|> & /@ accepted["Generators"]);
                decodeGeneratorMapReport[Lookup[source["LastComputation"], "generatorMap", None],
                    nativeGenerators, accepted["Order"], Join[request,
                        <|"stateID" -> accepted["StateID"], "generatorIdentity" -> accepted["GeneratorIdentity"]|>]]
            ]]]
        ]
    ]]
];
CheckGeneratorMap[___] := makeFailure["InvalidGeneratorMap", "Expected source/target groups and an ordered list of target words."];

True
