(*
    :Title: Bounded normal-subgroup result validation
    :Context: VVMFTool`Private`
    :Summary: Decode search bounds, completeness and subgroup/quotient words as inert data.
    :Responsibilities: Request matching and structural invariants, separate from native provenance.
    :Dependencies: ResultValidation.wl; GroupInput.wl; GroupWords.wl.
    :See Also: GAP/NormalSearch.g; NormalSubgroupsByIndex.
*)

(*
    Summary: Decode a bound-specific search result from an owned native LINS computation.
    Parameters: envelope — inert native JSON; request — validated supplied presentation/options.
    Options/defaults: Exact/UpTo; MaxResults is Null for an uncapped native request.
    Returns: Association with Items, Complete, CapReached, Bound, IndexMode, MaxResults,
        SmallGenerators, Presentation, Method and LINSVersion, or InvalidNormalSearch.
    Effects: Pure; constructing GroupPresentation values does not execute them.
    Failures: Changed request, flags, count, indices, word grammar or quotient relators.
    Example: an index-three result for <a|> decodes a quotient GroupPresentation with a^3.
    Remarks: Every returned word set generates the subgroup itself. Schema checks cannot
        establish normality, quotient order or enumeration completeness; the owned native
        producer verifies those facts. An imported flag alone is not accepted evidence.
    See also: runNormalSearch; VVMF_NormalItem; validateConstructionRecord.
*)
decodeNormalSearch[envelope_Association, request_Association] := Module[
    {result, presentation, names, generators, bound, cap, fields, items, item, index,
        words, quotient, relators, decoded = {}, failure = None, parentWords},
    If[!resultFieldsQ[envelope, {"schemaVersion", "requestID", "operation", "result", "producer"}] ||
        envelope["schemaVersion"] =!= 1 || envelope["operation"] =!= "NormalSubgroupsByIndex" ||
        envelope["requestID"] =!= Lookup[request, "requestID", None],
        Return[makeFailure["InvalidNormalSearch", "The search envelope does not match its request."]]];
    result = envelope["result"];
    fields = {"presentation", "bound", "indexMode", "maxResults", "smallGenerators"};
    If[!AssociationQ[result] || !resultFieldsQ[result, Join[fields,
        {"complete", "capReached", "items", "method", "linsVersion"}]] ||
        !AllTrue[fields, canonicalJSON[result[#]] === canonicalJSON[Lookup[request, #, None]] &],
        Return[makeFailure["InvalidNormalSearch", "The search changed its presentation, bound or options."]]];
    presentation = validateConstructionRecord[result["presentation"]];
    bound = decodeInteger[result["bound"]];
    cap = If[result["maxResults"] === Null, Infinity, decodeInteger[result["maxResults"]]];
    If[FailureQ[presentation] || Lookup[presentation, "type", None] =!= "presentation" ||
        !IntegerQ[bound] || bound < 1 || !(cap === Infinity || (IntegerQ[cap] && cap > 0)) ||
        !MemberQ[{"Exact", "UpTo"}, result["indexMode"]] ||
        !AllTrue[Lookup[result, {"complete", "capReached", "smallGenerators"}], BooleanQ] ||
        result["capReached"] === result["complete"] || result["method"] =!= "LINS" ||
        !StringQ[result["linsVersion"]] || StringLength[result["linsVersion"]] === 0 ||
        !ListQ[result["items"]] || Length[result["items"]] > cap ||
        (!result["complete"] && (cap === Infinity || Length[result["items"]] =!= cap)),
        Return[makeFailure["InvalidNormalSearch", "Malformed bounds, completeness or capped result count."]]];
    names = presentation["names"];
    generators = (<|"id" -> #, "name" -> #|> & /@ names);
    parentWords = decodeResultWord[#, generators] & /@ presentation["relators"];
    Do[
        If[!resultFieldsQ[item, {"index", "generatorWords", "generatorSemantics", "quotientPresentation"}] ||
            item["generatorSemantics"] =!= "Subgroup" || !ListQ[item["generatorWords"]],
            failure = makeFailure["InvalidNormalSearch", "Malformed normal subgroup entry."]; Break[]];
        index = decodeInteger[item["index"]];
        words = decodeResultWord[#, generators] & /@ item["generatorWords"];
        quotient = validateConstructionRecord[item["quotientPresentation"]];
        If[!IntegerQ[index] || index < 1 || index > bound ||
            (result["indexMode"] === "Exact" && index =!= bound) || AnyTrue[words, FailureQ] ||
            FailureQ[quotient] || Lookup[quotient, "type", None] =!= "presentation" ||
            quotient["names"] =!= names ||
            quotient["relators"] =!= Join[presentation["relators"], item["generatorWords"]],
            failure = makeFailure["InvalidNormalSearch", "Invalid index, subgroup words or quotient presentation."]; Break[]];
        AppendTo[decoded, <|"Index" -> index, "GeneratorWords" -> words,
            "GeneratorSemantics" -> "Subgroup",
            "QuotientPresentation" -> GroupPresentation[names, Join[parentWords, words]]|>],
        {item, result["items"]}];
    If[FailureQ[failure], Return[failure]];
    If[(bound === 1 && (!TrueQ[result["complete"]] || Length[decoded] =!= 1)) ||
        (result["indexMode"] === "UpTo" && Count[Lookup[decoded, "Index"], 1] =!= 1),
        Return[makeFailure["InvalidNormalSearch", "The unique index-one subgroup is missing or duplicated."]]];
    <|"Items" -> decoded, "Complete" -> result["complete"], "CapReached" -> result["capReached"],
        "Bound" -> bound, "IndexMode" -> result["indexMode"],
        "MaxResults" -> If[cap === Infinity, All, cap], "SmallGenerators" -> result["smallGenerators"],
        "Presentation" -> GroupPresentation[names, parentWords], "Method" -> "LINS",
        "LINSVersion" -> result["linsVersion"]|>
];
decodeNormalSearch[___] := makeFailure["InvalidNormalSearch", "Expected a search envelope and matching request."];

True
