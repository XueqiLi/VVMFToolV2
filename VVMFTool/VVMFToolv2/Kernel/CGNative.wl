(*
    :Title: Native, chain and subgroup Clebsch-Gordan routes
    :Context: VVMFTool`Private`
    :Summary: SubgroupChain and AveragedBSGS (RepnDecomp's GroupSumBSGS of the intertwiner action over a stabilizer
        chain, in a GAP worker), Serre and SerreBSGS (the Stage 2 native decomposition of P (x) Q, full-pair
        requests only) and SubgroupEmbedding (Hom over a proper subgroup, then the remaining generator equations).
    :Responsibilities: cgLiveGroup, cgCyclotomicMatrices, chainCG, serreCG, cgSubgroupWords, subgroupHomBasis,
        subgroupCG; registers $CGNativeMethods and the CGNative GAP operation.
    :Dependencies: CGData.wl (cgMethodDescriptors reads $CGNativeMethods); RepresentationDecomposition.wl
        (nativeDecompositionSolutions); RepresentationJobs.wl (cyclotomicEncoding); RepresentationStorage.wl
        (decodeNativeRepScalar); Representation.wl (wordMatrix); GroupEnrichment.wl (runGroupEnrichment); GAP/CG.g.
    :See Also: VVMFArch/step4Plan.md (method table); VVMFArch/implementation/step4Status.md.
*)

registerGAPOperation["CGNative", <|"Source" -> "Typed", "GenerationStep" -> 1, "CompleteQ" -> statusCompleteQ,
    "RecoverySkipQ" -> repeatSkipQ, "TerminalFailures" -> {}, "Methods" -> Function[request, {"GAP"}]|>];

(*
    Summary: The live accepted group behind a CG request.
    Parameters: request — from makeCGRequest.
    Options/defaults: None.
    Returns: Group, or None.
    Effects: Pure.
    Failures: None.
    Example: a context request finds the registered group with the same state ID.
    See also: chainCG; serreCG.
*)
cgLiveGroup[request_Association] := If[Head[request["Context"]] === Group, request["Context"],
    With[{state = Lookup[request["Snapshot"], "GroupIdentity", None]},
        SelectFirst[Keys[$GroupRegistry], Lookup[$GroupRegistry[#], "StateID", None] === state &, None] /. id_String :> Group[id]]];

(*
    Summary: Encode generator matrices in a cyclotomic field for a native route.
    Parameters: matrices — list of exact matrices; characters — the group's CharacterData.
    Options/defaults: None.
    Returns: Encoded matrices, or $Failed when an entry is not in a supported cyclotomic field.
    Effects: Pure.
    Failures: $Failed.
    Example: permutation matrices encode as integer records.
    See also: cyclotomicEncoding.
*)
cgCyclotomicMatrices[matrices_List, characters_Association] := Module[{orders = LCM[LCM @@ characters["ClassOrders"], 4] {1, 2, 3, 5, 6, 10, 15, 30}, encoded},
    encoded = Map[cyclotomicEncoding[#, orders] &, matrices, {3}];
    If[FreeQ[encoded, $Failed], encoded, $Failed]];

(*
    Summary: SubgroupChain / AveragedBSGS: kets and bras from a stabilizer-chain average in GAP.
    Parameters: problem — from cgProblem; variant — "Operator" (SubgroupChain) or "Trial" (AveragedBSGS).
    Options/defaults: The request's job options (StoreGAPState, AttemptTimeLimit, budgets).
    Returns: <|"Kets", "Bras"|> in the problem's exact domain, or Failure.
    Effects: Runs one GAP query (CGNative) on the live group, also for a context request: the group's mathematical
        state and CG store are unchanged, but the query is a worker enrichment that advances its state generation
        and, with StoreGAPState -> True, retains a workspace.
    Failures: NativeUnavailable (no live group); InapplicableMethod (non-cyclotomic matrices, numerical arithmetic,
        no recorded generators); GAP failures; InvalidCGRecord for a malformed result.
    Example: chainCG[problem, "Operator"]["Kets"] spans the generator-equation kets.
    Remarks: The action X -> R(g) X D(g^-1) is a homomorphism, so the chain product of transversal sums equals the
        group sum (GAP/CG.g VVMF_CGChain); scalar-weighted sums are never factored this way.
    See also: VVMF_CGChain; averagedCG.
*)
chainCG[problem_Association, variant_String] := Module[{request = problem["Request"], group, characters, encoded, run, result, decode},
    If[problem["Arithmetic"]["Field"] === None, Return[makeFailure["InapplicableMethod", "The chain route is exact (cyclotomic) only."]]];
    If[problem["Original"]["P"] === {}, Return[makeFailure["InapplicableMethod", "The chain route needs recorded generators."]]];
    group = cgLiveGroup[request];
    If[group === None, Return[makeFailure["NativeUnavailable", "The chain route needs an accepted live group of this state."]]];
    characters = request["Characters"];
    encoded = cgCyclotomicMatrices[#, characters] & /@ {problem["Original"]["P"], problem["Original"]["Q"], problem["Original"]["D"]};
    If[MemberQ[encoded, $Failed], Return[makeFailure["InapplicableMethod", "The chain route needs cyclotomic matrices."]]];
    run = runGroupEnrichment[group, "CGNative", <|"cgChain" -> <|"p" -> encoded[[1]], "q" -> encoded[[2]], "target" -> encoded[[3]],
            "multiplicity" -> ToString[problem["Multiplicity"]], "variant" -> variant|>|>,
        Join[KeyTake[request["Options"], {StoreGAPState, AttemptTimeLimit, CoreBudget, MemoryBudget, ProgressFunction}],
            <|Method -> Automatic, GroupModel -> Automatic|>]];
    If[FailureQ[run], Return[run]];
    result = Lookup[groupData[group]["LastComputation"], "cgNative", None];
    If[!AssociationQ[result] || !ListQ[Lookup[result, "kets", None]] || !ListQ[Lookup[result, "bras", None]],
        Return[makeFailure["InvalidCGRecord", "The chain result is absent or malformed."]]];
    decode[m_] := Map[decodeNativeRepScalar, m, {2}];
    result = <|"Kets" -> (decode /@ result["kets"]), "Bras" -> (decode /@ result["bras"])|>;
    If[!FreeQ[result, _Failure], Return[makeFailure["InvalidCGRecord", "The chain result has invalid entries."]]];
    <|"Kets" -> (problem["Arithmetic"]["Embed"] /@ result["Kets"]), "Bras" -> (problem["Arithmetic"]["Embed"] /@ result["Bras"])|>
];

(* One full native decomposition serves every target of a pair: memo of the last pair (kernel-local). *)
If[!AssociationQ[$CGSerreMemo], $CGSerreMemo = <||>];

(*
    Summary: Serre / SerreBSGS: kets of every target from the native decomposition of P (x) Q, bras from the exact
        inverse of the full embedding.
    Parameters: problem; method — "Serre" or "SerreKronecker".
    Options/defaults: The request's job options.
    Returns: <|"Kets", "Bras"|> of the problem's target, or Failure.
    Effects: One GAP Decompose query per pair (memoized for the pair's other targets).
    Failures: MethodInapplicable for a selected-target request (the native wrapper decomposes the whole product;
        step4Plan.md reserves it for complete pair requests); InapplicableMethod for non-cyclotomic data or
        numerical arithmetic; NativeUnavailable; decomposition failures.
    Example: serreCG on A4 3 (x) 3 with all targets gives the triplet's two kets.
    Remarks: Targets are supplied as the stored matrices (GAP verifies them as irreps), so no basis transport is
        needed. SerreKronecker enables RepnDecomp's use_kronecker projections (stabilizer-chain sums).
    See also: nativeDecompositionSolutions; VVMF_Decompose.
*)
serreCG[problem_Association, method_String] := Module[{request = problem["Request"], key, solutions, targets, positive, columns, u, uinverse,
        field, index, position, arithmetic = problem["Arithmetic"], rows},
    If[arithmetic["Field"] === None, Return[makeFailure["InapplicableMethod", "The native decomposition is exact (cyclotomic) only."]]];
    positive = request["AllTargets"];
    If[!SubsetQ[request["Targets"], positive],
        Return[makeFailure["MethodInapplicable", "The native full decomposition serves complete pair requests only (all targets)."]]];
    If[cgLiveGroup[request] === None, Return[makeFailure["NativeUnavailable", "The native decomposition needs an accepted live group of this state."]]];
    key = Hash[{method, request["Variants"][#]["Identity"] & /@ Join[request["Pair"], positive]}, "SHA256"];
    solutions = Lookup[$CGSerreMemo, key, None];
    If[solutions === None,
        targets = AssociationMap[<|"Rep" -> request["Variants"][#]["Rep"], "Native" -> request["Variants"][#]["Matrices"],
            "Scales" -> ConstantArray[1, request["Variants"][#]["Dimension"]], "Source" -> "Supplied"|> &, positive];
        solutions = nativeDecompositionSolutions[If[Head[request["Context"]] === Group, request["Context"], cgLiveGroup[request]],
            <|"Snapshot" -> If[KeyExistsQ[request["Snapshot"], "GroupIdentity"], request["Snapshot"], contextSnapshot[request["Snapshot"]]],
                "Matrices" -> MapThread[KroneckerProduct, {problem["Original"]["P"], problem["Original"]["Q"]}]|>,
            targets, KeyTake[request["Multiplicities"], positive], method,
            Join[request["Options"], <|IsomorphismMethod -> Automatic, Method -> Automatic, GroupModel -> Automatic|>]];
        If[FailureQ[solutions], Return[solutions]];
        $CGSerreMemo = <|key -> solutions|>];
    (* Full embedding U (targets in character order, copies in order) and its exact inverse. *)
    columns = Flatten[Map[solutions[#] &, positive], 1];
    u = Join @@ (Transpose /@ columns) // Transpose;
    field = arithmetic["Field"];
    uinverse = fieldBack[fieldInverse[field, fieldEmbed[field, u]]];
    index = 0;
    rows = Association[Map[Function[t, t -> Table[With[{d = request["Variants"][t]["Dimension"]},
        index += d; uinverse[[index - d + 1 ;; index]]], {Length[solutions[t]]}]], positive]];
    position = problem["Request"]["Targets"];
    <|"Kets" -> (arithmetic["Embed"] /@ solutions[problem["TargetID"]]), "Bras" -> (arithmetic["Embed"] /@ rows[problem["TargetID"]])|>
];

(*
    Summary: The order of the subgroup generated by words, and whether it is proper.
    Parameters: request; words — list of GroupWord on the recorded generators.
    Options/defaults: None.
    Returns: <|"Order" -> integer or Missing["Unverified"], "Proper" -> True | False | "Unverified"|>.
    Effects: Pure.
    Failures: None (unknown generators give an unverified order; cgSubgroupWords and subgroupCG report them).
    Example: the cyclic subgroup of a generator of order 3 in A4 has Order 3 and Proper True.
    Remarks: The direct sum of every irrep is faithful, so the image of H there has |H| elements; without every
        irrep's matrices the order is unverified.
    See also: cgSubgroupWords; subgroupCG.
*)
subgroupOrderInfo[request_Association, words_List] := Module[{snapshot = request["Snapshot"], names, variants, blockDiagonal, generators, images},
    names = If[KeyExistsQ[snapshot, "GeneratorNames"], snapshot["GeneratorNames"], Lookup[snapshot["Generators"], "Name", {}]];
    If[words === {}, Return[<|"Order" -> 1, "Proper" -> snapshot["Order"] > 1|>]];
    variants = cgVariant[snapshot, #] & /@ request["Characters"]["IrrepIDs"];
    If[AnyTrue[variants, MissingQ], Return[<|"Order" -> Missing["Unverified"], "Proper" -> "Unverified"|>]];
    blockDiagonal[blocks_List] := Fold[ArrayFlatten[{{#1, 0}, {0, #2}}] &, First[blocks], Rest[blocks]];
    generators = Quiet[Map[Function[w, blockDiagonal[Map[wordMatrix[#["Rep"], w, names] &, variants]]], words]];
    If[!FreeQ[generators, _Failure], Return[<|"Order" -> Missing["Unverified"], "Proper" -> "Unverified"|>]];
    images = imageClosure[generators, snapshot["Order"], arithmeticSettings["Exact", 50, Automatic, Infinity], Map[RootReduce, #, {2}] &];
    If[FailureQ[images], <|"Order" -> Missing["Unverified"], "Proper" -> "Unverified"|>,
        <|"Order" -> Length[images], "Proper" -> Length[images] < snapshot["Order"]|>]
];

(*
    Summary: The subgroup generator words of a SubgroupEmbedding request.
    Parameters: request.
    Options/defaults: MethodData <|"SubgroupGenerators" -> words|> or <|"SubgroupRecord" -> record|> (a Stage 1 subgroup
        record with GeneratorWords); otherwise a recorded proper subgroup of the group; only with "SubgroupSource" -> "Any"
        the first cyclic subgroup of a recorded generator that is certified proper, otherwise the identity subgroup
        (methodOptionsPlan.md 2A.6: no silent fallback).
    Returns: <|"Words" -> list of GroupWord, "Source" -> description|>, or Failure.
    Effects: Pure.
    Failures: InvalidMethodData (a record without generator words); MethodInapplicable (no subgroup data and no
        SubgroupSource "Any").
    Example: a group with recorded subgroup classes uses the first proper class representative.
    Remarks: Automatic never starts GAP (context calls stay worker-free): it uses recorded subgroups and cyclic
        generator subgroups instead of a GAP subgroup search.
    See also: subgroupCG; subgroupOrderInfo.
*)
cgSubgroupWords[request_Association] := Module[{data = request["Options"][MethodData], snapshot = request["Snapshot"], recorded, names, cyclic},
    names = If[KeyExistsQ[snapshot, "GeneratorNames"], snapshot["GeneratorNames"], Lookup[snapshot["Generators"], "Name", {}]];
    Which[
        AssociationQ[data] && KeyExistsQ[data, "SubgroupGenerators"], <|"Words" -> data["SubgroupGenerators"], "Source" -> "MethodData"|>,
        AssociationQ[data] && KeyExistsQ[data, "SubgroupRecord"],
            If[ListQ[Lookup[data["SubgroupRecord"], "GeneratorWords", None]],
                <|"Words" -> data["SubgroupRecord"]["GeneratorWords"], "Source" -> "SubgroupRecord"|>,
                makeFailure["InvalidMethodData", "The subgroup record has no generator words."]],
        True,
        recorded = If[AssociationQ[Lookup[snapshot, "SubgroupData", Missing[]]],
            SelectFirst[Flatten[Lookup[Values[snapshot["SubgroupData"]], "Subgroups", {}]],
                AssociationQ[#] && IntegerQ[Lookup[#, "Order", None]] && 1 < #["Order"] < snapshot["Order"] && ListQ[Lookup[#, "GeneratorWords", None]] &, None],
            None];
        (* the cyclic and identity fallbacks only when requested (2A.6): MethodData -> <|"SubgroupSource" -> "Any"|> *)
        If[recorded === None && !(AssociationQ[data] && Lookup[data, "SubgroupSource", "Recorded"] === "Any"),
            Return[makeFailure["MethodInapplicable", "SubgroupEmbedding needs subgroup generators in MethodData or a recorded proper subgroup; MethodData -> <|\"SubgroupSource\" -> \"Any\"|> allows a cyclic or the identity subgroup.",
                <|"Method" -> "SubgroupEmbedding"|>], Module]];
        cyclic = If[recorded =!= None, None,
            SelectFirst[names, subgroupOrderInfo[request, {GroupWord[{{#, 1}}]}]["Proper"] === True &, None]];
        Which[recorded =!= None, <|"Words" -> recorded["GeneratorWords"], "Source" -> "RecordedSubgroup"|>,
            cyclic =!= None, <|"Words" -> {GroupWord[{{cyclic, 1}}]}, "Source" -> "CyclicGenerator"|>,
            True, <|"Words" -> {}, "Source" -> "IdentitySubgroup"|>]]
];

(*
    Summary: Hom_H spaces of P (x) Q against a target over a subgroup H, from H's generator equations.
    Parameters: hTensor — R(h_j) for the subgroup generators; hTarget — D(h_j); dims; arithmetic.
    Options/defaults: None.
    Returns: <|"Kets", "Bras"|> spanning Hom_H (dimension at least the G multiplicity), or Failure.
    Effects: Pure.
    Failures: PrecisionFailure (numerical).
    Example: for the identity subgroup Hom_H is every N by dt matrix.
    Remarks: The base route of the subgroup recursion is the generator equations on H (step4Plan.md); H-irrep CG
        tensoring would give the same span.
    See also: subgroupCG.
*)
subgroupHomBasis[hTensor_List, hTarget_List, {dp_Integer, dq_Integer, dt_Integer}, arithmetic_Association] := Module[{kets, bras, keepK, keepW},
    keepK = If[hTensor === {}, ConstantArray[True, {dp dq, dt}], None];
    keepW = If[hTensor === {}, ConstantArray[True, {dt, dp dq}], None];
    kets = cgNullSpace[intertwinerSystem[hTensor, hTarget, "Ket"], keepK, arithmetic];
    If[FailureQ[kets], Return[kets]];
    bras = cgNullSpace[intertwinerSystem[hTensor, hTarget, "Bra"], keepW, arithmetic];
    If[FailureQ[bras], Return[bras]];
    <|"Kets" -> (Partition[#, dt] & /@ kets), "Bras" -> (Partition[#, dp dq] & /@ bras)|>
];

(*
    Summary: SubgroupEmbedding: Hom over a subgroup, cut down by the group's generator equations.
    Parameters: problem.
    Options/defaults: MethodData as cgSubgroupWords.
    Returns: <|"Kets", "Bras", "Subgroup" -> <|"Source", "Words", "Order" (or Missing), "Proper" (or "Unverified")|>|>, or
        Failure.
    Effects: Pure.
    Failures: InvalidMethodData; MethodInapplicable (the words generate the whole group); InvalidWord (words on unknown
        generators); UnprovedIdentity when the reduced space does not have the multiplicity.
    Example: subgroupCG with the A4 Klein subgroup V4 gives the same span as GeneratorEquations.
    Remarks: The subgroup's words are evaluated on the stored matrices, so its embedding is the given one. Hom_G is the
        subspace of Hom_H satisfying the G generator equations: with B_k a basis of Hom_H, the coefficients c solve
        Sum_k c_k (R_i B_k - B_k D_i) = 0 for every recorded generator i. Properness is certified by subgroupOrderInfo
        when every irrep is stored; a certified whole group is rejected, an unverified one is reported as such (the
        route stays correct either way).
    See also: subgroupHomBasis; generatorCGSpaces.
*)
subgroupCG[problem_Association] := Module[{request = problem["Request"], words, names, evaluate, hP, hQ, hD, hTensor, hTarget, ar = problem["Arithmetic"],
        homH, kets, bras, reduce, tensor, sizeInfo},
    words = cgSubgroupWords[request];
    If[FailureQ[words], Return[words]];
    (* The route needs a proper subgroup: the whole group would only repeat GeneratorEquations. *)
    sizeInfo = subgroupOrderInfo[request, words["Words"]];
    If[sizeInfo["Proper"] === False, Return[makeFailure["MethodInapplicable", "The subgroup words generate the whole group; SubgroupEmbedding needs a proper subgroup.",
        <|"Method" -> "SubgroupEmbedding", "Order" -> sizeInfo["Order"], "Source" -> words["Source"]|>]]];
    names = If[KeyExistsQ[request["Snapshot"], "GeneratorNames"], request["Snapshot"]["GeneratorNames"], Lookup[request["Snapshot"]["Generators"], "Name", {}]];
    evaluate[id_] := Map[wordMatrix[request["Variants"][id]["Rep"], #, names] &, words["Words"]];
    {hP, hQ, hD} = evaluate /@ Append[request["Pair"], problem["TargetID"]];
    If[!FreeQ[{hP, hQ, hD}, _Failure], Return[FirstCase[{hP, hQ, hD}, _Failure, Null, Infinity]]];
    hTensor = MapThread[ar["Reduce"][KroneckerProduct[#1, #2]] &, {ar["Embed"][hP], ar["Embed"][hQ]}];
    hTarget = ar["Embed"][hD];
    homH = subgroupHomBasis[hTensor, hTarget, problem["Dims"], ar];
    If[FailureQ[homH], Return[homH]];
    tensor = MapThread[ar["Reduce"][KroneckerProduct[#1, #2]] &, {problem["P"], problem["Q"]}];
    (* Coefficients c of Hom_G = {Sum c_k B_k} inside Hom_H. *)
    reduce[basis_List, side_String] := Module[{columns, null},
        If[basis === {} || tensor === {}, Return[basis]];
        columns = Map[Function[b, Flatten[Map[If[side === "Ket", tensor[[#]] . b - b . problem["D"][[#]], b . tensor[[#]] - problem["D"][[#]] . b] &,
            Range[Length[tensor]]]]], basis];
        null = cgNullSpace[ar["Reduce"][Transpose[columns]], None, ar];
        If[FailureQ[null], null, Map[ar["Reduce"][#. basis] &, null]]];
    kets = reduce[homH["Kets"], "Ket"]; If[FailureQ[kets], Return[kets]];
    bras = reduce[homH["Bras"], "Bra"]; If[FailureQ[bras], Return[bras]];
    If[Length[kets] =!= problem["Multiplicity"] || Length[bras] =!= problem["Multiplicity"],
        Return[makeFailure["UnprovedIdentity", "The subgroup-reduced spaces do not have the character multiplicity.",
            <|"Kets" -> Length[kets], "Bras" -> Length[bras]|>]]];
    <|"Kets" -> kets, "Bras" -> bras, "Subgroup" -> Join[KeyTake[words, {"Source", "Words"}], sizeInfo]|>
];

$CGNativeMethods = <|
    "SubgroupChain" -> <|"Route" -> (chainCG[#, "Operator"] &), "Kind" -> "Native", "Exact" -> "Direct", "Numerical" -> False,
        "UnitaryInputs" -> False, "Elements" -> False|>,
    "AveragedBSGS" -> <|"Route" -> (chainCG[#, "Trial"] &), "Kind" -> "Native", "Exact" -> "Direct", "Numerical" -> False,
        "UnitaryInputs" -> False, "Elements" -> False|>,
    "Serre" -> <|"Route" -> (serreCG[#, "Serre"] &), "Kind" -> "Native", "Exact" -> "Direct", "Numerical" -> False,
        "UnitaryInputs" -> False, "Elements" -> False|>,
    "SerreBSGS" -> <|"Route" -> (serreCG[#, "SerreKronecker"] &), "Kind" -> "Native", "Exact" -> "Direct", "Numerical" -> False,
        "UnitaryInputs" -> False, "Elements" -> False|>,
    "SubgroupEmbedding" -> <|"Route" -> subgroupCG, "Kind" -> "Wolfram", "Exact" -> "Direct", "Numerical" -> True,
        "UnitaryInputs" -> False, "Elements" -> False|>|>;

True
