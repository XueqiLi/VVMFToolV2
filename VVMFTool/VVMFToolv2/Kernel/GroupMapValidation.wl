(*
    :Title: Prescribed generator-map reports
    :Context: VVMFTool`Private`
    :Summary: Decode exact map flags and words separately from native correspondence proof.
    :Responsibilities: Report grammar, request identities and finite-order consistency.
    :Dependencies: ResultValidation.wl; GroupWords.wl.
    :See Also: GAP/GroupMaps.g; CheckGeneratorMap in step1Plan.md.
*)

(*
    Summary: Validate and decode a native report about the prescribed generator images.
    Parameters: report — native result; generators/order — accepted source generator records
        and positive finite order; request — source identities and optional target/images.
    Options/defaults: No inverse images exist in the report unless the map is an isomorphism.
    Returns: String-keyed map flags and GroupWord lists, or InvalidGeneratorMap Failure.
    Effects: Pure; schema/invariants alone never prove a map exists or a negative claim.
    Failures: Missing/extra fields, incompatible booleans/orders, malformed words or identities.
    Example: a surjective C6->C3 report decodes with Injective=False and no inverse-word list.
    See also: validateGroupResult; VVMF_MapRequest; the owned fresh-native verification protocol.
*)
decodeGeneratorMapReport[report_Association, generators_List, order_Integer,
    request_Association] := Module[{flags, names, targetOrder, images, inverse, sourceWords, targetWords, target},
    If[!resultFieldsQ[report, {"homomorphism", "injective", "surjective", "isomorphism",
        "imageWords", "inverseImageWords", "sourceStateID", "sourceGeneratorIdentity",
        "targetStateID", "targetGeneratorIdentity", "targetNames", "targetOrder"}] ||
        !AllTrue[{"homomorphism", "injective", "surjective", "isomorphism"},
            MemberQ[{True, False}, report[#]] &] ||
        !AllTrue[{"sourceStateID", "sourceGeneratorIdentity", "targetStateID", "targetGeneratorIdentity"},
            StringQ[report[#]] && StringLength[report[#]] > 0 &],
        Return[makeFailure["InvalidGeneratorMap", "The map report has malformed fields or flags."]]];
    names = report["targetNames"]; targetOrder = decodeInteger[report["targetOrder"]];
    flags = Lookup[report, {"homomorphism", "injective", "surjective", "isomorphism"}];
    If[order < 1 || !generatorNamesQ[names] || !IntegerQ[targetOrder] || targetOrder < 1 ||
        report["sourceStateID"] =!= Lookup[request, "stateID", None] ||
        report["sourceGeneratorIdentity"] =!= Lookup[request, "generatorIdentity", None] ||
        (!flags[[1]] && Or @@ Rest[flags]) || flags[[4]] =!= (flags[[2]] && flags[[3]]) ||
        (flags[[2]] && !Divisible[targetOrder, order]) || (flags[[3]] && !Divisible[order, targetOrder]),
        Return[makeFailure["InvalidGeneratorMap", "Map identities, booleans or finite orders are inconsistent."]]];
    sourceWords = (<|"id" -> #["name"], "name" -> #["name"]|> & /@ generators);
    targetWords = (<|"id" -> #, "name" -> #|> & /@ names);
    If[!ListQ[report["imageWords"]] || Length[report["imageWords"]] =!= Length[generators],
        Return[makeFailure["InvalidGeneratorMap", "Supply exactly one image per source generator."]]];
    images = decodeResultWord[#, targetWords] & /@ report["imageWords"];
    If[AnyTrue[images, FailureQ], Return[makeFailure["InvalidGeneratorMap", "A target image word is invalid."]]];
    inverse = Missing["NotIsomorphism"];
    If[flags[[4]],
        If[!ListQ[report["inverseImageWords"]] || Length[report["inverseImageWords"]] =!= Length[names],
            Return[makeFailure["InvalidGeneratorMap", "An isomorphism requires one inverse word per target generator."]]];
        inverse = decodeResultWord[#, sourceWords] & /@ report["inverseImageWords"];
        If[AnyTrue[inverse, FailureQ], Return[makeFailure["InvalidGeneratorMap", "An inverse source word is invalid."]]],
        If[report["inverseImageWords"] =!= Null,
            Return[makeFailure["InvalidGeneratorMap", "A nonisomorphism cannot report inverse words for all target generators."]]]];
    If[KeyExistsQ[request, "imageWords"] && report["imageWords"] =!= request["imageWords"],
        Return[makeFailure["InvalidGeneratorMap", "The report changed a prescribed generator image."]]];
    If[KeyExistsQ[request, "targetGroup"],
        target = request["targetGroup"];
        If[report["targetStateID"] =!= target["stateID"] ||
            report["targetGeneratorIdentity"] =!= target["generatorIdentity"] ||
            report["targetOrder"] =!= target["order"] || names =!= target["presentation"]["names"],
            Return[makeFailure["InvalidGeneratorMap", "The map report changed its certified target."]]]];
    <|"Homomorphism" -> flags[[1]], "Injective" -> flags[[2]], "Surjective" -> flags[[3]],
        "Isomorphism" -> flags[[4]], "Images" -> images, "InverseImages" -> inverse,
        "SourceStateID" -> report["sourceStateID"], "SourceGeneratorIdentity" -> report["sourceGeneratorIdentity"],
        "TargetStateID" -> report["targetStateID"], "TargetGeneratorIdentity" -> report["targetGeneratorIdentity"]|>
];
decodeGeneratorMapReport[___] := makeFailure["InvalidGeneratorMap", "Expected a native map report and accepted source context."];

True
