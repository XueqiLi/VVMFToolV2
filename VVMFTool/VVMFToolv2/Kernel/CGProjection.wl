(*
    :Title: Projection Clebsch-Gordan spaces
    :Context: VVMFTool`Private`
    :Summary: Ket and bra intertwiner spaces from the matrix units P_ab = (dt/|G|) Sum_g D(g^-1)[b,a] R(g) of the
        target, eagerly (all units) or lazily (columns and rows only for the seeds consumed).
    :Responsibilities: cgElementImages, matrixUnitEntry, projectionSeeds, projectionCG; averageAction,
        averagedCG (whole-group streaming of trial maps) and orbitAverage (exact orbit enumeration).
    :Dependencies: RepresentationBasis.wl (imageClosure); CGLinear.wl (cgArithmetic); CGValidation.wl
        (independentMatrices).
    :See Also: VVMFArch/step4Plan.md (ProjectionEager, ProjectionLazy); v1 VVMFTool-Group-CG.wl:12-233.
*)

(*
    Summary: The image group of P (+) Q (+) D^-T, as element triples.
    Parameters: p, q, target — generator matrices in domain arithmetic; order — group order; arithmetic.
    Options/defaults: None.
    Returns: List of {P(g), Q(g), Dinv(g)} with Dinv(g) = Transpose[D(g^-1)], one per image element, or Failure.
    Effects: Pure.
    Failures: imageClosure failures (ResourceLimit, InvalidRepresentation); a singular target generator.
    Example: for a trivial target and permutation inputs, every element's Dinv is {{1}}.
    Remarks: g -> D(g^-1)^T is the contragredient representation, so only generators are inverted. The image
        is a quotient of G; the matrix-unit average over it equals the average over G, so 1/|image| replaces
        1/|G|. With no generators the image is the identity alone.
    See also: projectionCG; imageClosure.
*)
cgElementImages[p_List, q_List, target_List, dims : {dp_Integer, dq_Integer, dt_Integer}, order_Integer, arithmetic_Association] := Module[
    {inverses, blocks, elements},
    If[p === {}, Return[{{IdentityMatrix[dp], IdentityMatrix[dq], IdentityMatrix[dt]}}]];
    inverses = If[arithmetic["Field"] =!= None, fieldInverse[arithmetic["Field"], #], Inverse[#]] & /@ target;
    blocks = MapThread[ArrayFlatten[{{#1, 0, 0}, {0, #2, 0}, {0, 0, Transpose[#3]}}] &, {p, q, inverses}];
    elements = imageClosure[blocks, order, arithmetic["Settings"], arithmetic["Reduce"]];
    If[FailureQ[elements], Return[elements]];
    {#[[1 ;; dp, 1 ;; dp]], #[[dp + 1 ;; dp + dq, dp + 1 ;; dp + dq]], #[[dp + dq + 1 ;;, dp + dq + 1 ;;]]} & /@ elements
];

(*
    Summary: One column (ket side) or row (bra side) of a matrix unit, streamed over the elements.
    Parameters: elements — from cgElementImages; a, b — unit indices; side — "Column" (P_ab e_j) or "Row"
        (e_j^T P_ab); j — basis index of C^N; dims — {dp, dq, dt}; arithmetic.
    Options/defaults: None.
    Returns: The vector (length N), reduced in the domain.
    Effects: Pure.
    Failures: None.
    Example: matrixUnitEntry[elements, 1, 1, "Column", 1, dims, ar] is the first column of P_11.
    Remarks: R(g) e_j = P(g) e_{jp} (x) Q(g) e_{jq} with j = (jp - 1) dq + jq, so R(g) is never formed.
    See also: projectionCG.
*)
matrixUnitEntry[elements_List, a_Integer, b_Integer, side_String, j_Integer, {dp_Integer, dq_Integer, dt_Integer}, arithmetic_Association] := Module[
    {jp = Quotient[j - 1, dq] + 1, jq = Mod[j - 1, dq] + 1},
    arithmetic["Reduce"][(dt/Length[elements]) Total[Map[
        (* D(g^-1)[b, a] = Dinv(g)[a, b]. *)
        #[[3, a, b]] If[side === "Column", Flatten[KroneckerProduct[#[[1, All, jp]], #[[2, All, jq]]]],
            Flatten[KroneckerProduct[#[[1, jp]], #[[2, jq]]]]] &, elements]]]
];

(*
    Summary: Independent ket or bra candidates from systematic seeds.
    Parameters: candidate — function j -> candidate matrix (or None to skip); n — number of seeds; multiplicity;
        arithmetic.
    Options/defaults: None.
    Returns: List of multiplicity independent matrices, or Failure.
    Effects: Pure.
    Failures: UnprovedIdentity when the seeds e_1..e_N give fewer independent candidates than the multiplicity
        (rank deficiency; this cannot happen for a correct target and multiplicity).
    Example: projectionSeeds[f, 9, 2, ar] stops after the second independent candidate.
    Remarks: The seed progression is the standard basis, so the search is finite and deterministic.
    See also: projectionCG.
*)
projectionSeeds[candidate_, n_Integer, multiplicity_Integer, arithmetic_Association] := Module[{selected = {}, j = 0, c},
    While[Length[selected] < multiplicity && j < n,
        j++;
        c = candidate[j];
        If[c =!= None && !cgZeroTest[c, arithmetic] &&
                Length[independentMatrices[Append[selected, c], arithmetic]] > Length[selected],
            AppendTo[selected, c]]];
    If[Length[selected] < multiplicity,
        makeFailure["UnprovedIdentity", "The projection seeds give fewer independent copies than the character multiplicity.",
            <|"Found" -> Length[selected], "Multiplicity" -> multiplicity|>], selected]
];

(*
    Summary: Ket and bra spaces of P (x) Q for one target from matrix units.
    Parameters: p, q, target — domain generator matrices; dims; order — group order; multiplicity; arithmetic;
        evaluation — "Eager" (all units P_a1 and P_1a formed once) or "Lazy" (columns/rows per consumed seed).
    Options/defaults: None.
    Returns: <|"Kets", "Bras", "Elements" -> number of image elements, "SeedsConsumed"|>, or Failure.
    Effects: Pure.
    Failures: cgElementImages and projectionSeeds failures.
    Example: projectionCG[...]["Kets"] spans the same space as generatorCGSpaces[...]["Kets"].
    Remarks: For a seed j, K has columns P_a1 e_j (a = 1..dt) and W has rows e_j^T P_1a; then R K = K D and
        W R = D W in any basis, because the units use D(g^-1) rather than the conjugate of D(g). Lazy
        evaluation still sums every element; only operator entries are lazy. A zero diagonal probe
        (P_11)_jj skips seed j only when every matrix is unitary (P_11 is then a positive projector).
    See also: matrixUnitEntry; projectionSeeds; generatorCGSpaces.
*)
projectionCG[p_List, q_List, target_List, dims : {dp_Integer, dq_Integer, dt_Integer}, order_Integer, multiplicity_Integer,
    arithmetic_Association, evaluation_String, unitary_ : False] := Module[{elements, n = dp dq, units, kets, bras, consumed = 0, probe},
    If[multiplicity === 0, Return[<|"Kets" -> {}, "Bras" -> {}, "Elements" -> 0, "SeedsConsumed" -> 0|>]];
    elements = cgElementImages[p, q, target, dims, order, arithmetic];
    If[FailureQ[elements], Return[elements]];
    If[evaluation === "Eager",
        units = <|"Column" -> Table[Transpose[Table[matrixUnitEntry[elements, a, 1, "Column", j, dims, arithmetic], {j, n}]], {a, dt}],
            "Row" -> Table[Table[matrixUnitEntry[elements, 1, a, "Row", j, dims, arithmetic], {j, n}], {a, dt}]|>;
        kets = projectionSeeds[Function[j, Transpose[units["Column"][[All, All, j]]]], n, multiplicity, arithmetic];
        bras = projectionSeeds[Function[j, units["Row"][[All, j]]], n, multiplicity, arithmetic];
        consumed = n,
        probe[j_] := !TrueQ[unitary] || !cgZeroTest[matrixUnitEntry[elements, 1, 1, "Column", j, dims, arithmetic][[j]], arithmetic];
        kets = projectionSeeds[Function[j, If[probe[j], consumed++;
            Transpose[Table[matrixUnitEntry[elements, a, 1, "Column", j, dims, arithmetic], {a, dt}]], None]], n, multiplicity, arithmetic];
        bras = projectionSeeds[Function[j, If[probe[j],
            Table[matrixUnitEntry[elements, 1, a, "Row", j, dims, arithmetic], {a, dt}], None]], n, multiplicity, arithmetic]];
    If[FailureQ[kets], Return[kets]];
    If[FailureQ[bras], Return[bras]];
    <|"Kets" -> kets, "Bras" -> bras, "Elements" -> Length[elements], "SeedsConsumed" -> consumed|>
];

(*
    Summary: Group average of the intertwiner action on one trial map.
    Parameters: elements — from cgElementImages (or a chain's transversal products); x — trial map (ket side:
        N by dt; bra side: dt by N); side — "Ket" or "Bra"; arithmetic.
    Options/defaults: None.
    Returns: Ket: (1/|image|) Sum_g R(g) X D(g^-1); bra: (1/|image|) Sum_g D(g^-1) X R(g); reduced.
    Effects: Pure.
    Failures: None.
    Example: averaging any X for a target absent from P (x) Q gives the zero map.
    Remarks: L_g(X) = R(g) X D(g^-1) is a genuine linear group action (a homomorphism g -> L_g), so its
        average is the projection onto Hom_G(D, R). The bra average uses g -> g^-1 under the sum.
    See also: averagedCG; orbitAverage.
*)
averageAction[elements_List, x_, side_String, arithmetic_Association] := arithmetic["Reduce"][Total[Map[
    With[{r = KroneckerProduct[#[[1]], #[[2]]], dinverse = Transpose[#[[3]]]},
        If[side === "Ket", r . x . dinverse, dinverse . x . r]] &, elements]] / Length[elements]];

(*
    Summary: Ket and bra spaces from group-averaged trial maps.
    Parameters: p, q, target, dims, order, multiplicity, arithmetic as projectionCG; variant — "Whole" (stream
        the image group) or "Orbit" (exact orbit sums, orbitAverage); retries — number of deterministic
        pseudorandom trial maps tried before systematic seeds (default 4 multiplicity).
    Options/defaults: Trial maps are integer matrices from fixed seeds (reproducible; a seed list is hashed, because
        RandomSeeding uses only the first element of a list); afterwards the matrix units E_jc are used, so the
        search always ends.
    Returns: <|"Kets", "Bras", "Elements", "Trials"|>, or Failure.
    Effects: Pure (the random generator is seeded locally).
    Failures: cgElementImages failures; InapplicableMethod for "Orbit" in numerical arithmetic; orbit
        ResourceLimit; UnprovedIdentity when even the systematic seeds do not reach the rank.
    Example: averagedCG[...]["Kets"] spans Hom_G(D, P (x) Q).
    See also: averageAction; projectionSeeds.
*)
averagedCG[p_List, q_List, target_List, dims : {dp_Integer, dq_Integer, dt_Integer}, order_Integer, multiplicity_Integer,
    arithmetic_Association, variant_String : "Whole", retries_ : Automatic] := Module[
    {elements, tensor, n = dp dq, tries, trial, average, kets, bras, count = 0, failure = None},
    If[multiplicity === 0, Return[<|"Kets" -> {}, "Bras" -> {}, "Elements" -> 0, "Trials" -> 0|>]];
    If[variant === "Orbit",
        If[arithmetic["Field"] === None, Return[makeFailure["InapplicableMethod", "Orbit averaging needs exact matrices or an exact witness."]]];
        tensor = MapThread[arithmetic["Reduce"][KroneckerProduct[#1, #2]] &, {p, q}];
        elements = None;
        average[x_, side_] := With[{o = orbitAverage[tensor, target, x, side, arithmetic, order]},
            If[FailureQ[o], failure = o; None, First[o]]],
        elements = cgElementImages[p, q, target, dims, order, arithmetic];
        If[FailureQ[elements], Return[elements]];
        average[x_, side_] := averageAction[elements, x, side, arithmetic]];
    tries = If[retries === Automatic, 4 multiplicity, retries];
    trial[side_, j_] := (count++; If[j <= tries,
        BlockRandom[RandomInteger[{-3, 3}, If[side === "Ket", {n, dt}, {dt, n}]], RandomSeeding -> Hash[{side, j}]],
        With[{k = j - tries}, If[k > n dt, None, If[side === "Ket",
            Normal[SparseArray[{{Quotient[k - 1, dt] + 1, Mod[k - 1, dt] + 1} -> 1}, {n, dt}]],
            Normal[SparseArray[{{Mod[k - 1, dt] + 1, Quotient[k - 1, dt] + 1} -> 1}, {dt, n}]]]]]]);
    kets = projectionSeeds[Function[j, With[{x = trial["Ket", j]}, If[x === None || failure =!= None, None, average[x, "Ket"]]]],
        tries + n dt, multiplicity, arithmetic];
    If[failure =!= None, Return[failure]];
    If[FailureQ[kets], Return[kets]];
    bras = projectionSeeds[Function[j, With[{x = trial["Bra", j]}, If[x === None || failure =!= None, None, average[x, "Bra"]]]],
        tries + n dt, multiplicity, arithmetic];
    If[failure =!= None, Return[failure]];
    If[FailureQ[bras], Return[bras]];
    <|"Kets" -> kets, "Bras" -> bras, "Elements" -> If[elements === None, Missing["Orbit"], Length[elements]], "Trials" -> count|>
];

(*
    Summary: Sum of the exact orbit of a trial map under the generators' action.
    Parameters: tensor — R_i (domain); target — D_i (domain); x — trial map; side; arithmetic; cap — maximum
        orbit size (the group order).
    Options/defaults: None.
    Returns: {sum over the orbit, orbit size}, or Failure.
    Effects: Pure.
    Failures: InapplicableMethod in numerical arithmetic (orbit equality needs canonical exact values);
        ResourceLimit when the orbit exceeds cap.
    Example: a fixed point has orbit size 1 and sum x.
    Remarks: The orbit average equals the group average up to the positive stabilizer factor, so it spans the
        same Hom-space; copies are normalized afterwards. Exact canonical field values decide equality; no
        tolerance merging.
    See also: averagedCG.
*)
orbitAverage[tensor_List, target_List, x_, side_String, arithmetic_Association, cap_Integer] := Module[{inverses, act, seen, queue, y, z},
    If[arithmetic["Field"] === None, Return[makeFailure["InapplicableMethod", "Orbit averaging needs exact matrices or an exact witness."]]];
    If[tensor === {}, Return[{x, 1}]];
    (* Ket action X -> R_i X D_i^-1; bra action W -> D_i W R_i^-1. *)
    inverses = fieldInverse[arithmetic["Field"], #] & /@ If[side === "Ket", target, tensor];
    act[i_, m_] := arithmetic["Reduce"][If[side === "Ket", tensor[[i]] . m . inverses[[i]], target[[i]] . m . inverses[[i]]]];
    seen = <|x -> True|>; queue = {x};
    While[queue =!= {},
        y = First[queue]; queue = Rest[queue];
        Do[z = act[i, y];
            If[!KeyExistsQ[seen, z], seen[z] = True; AppendTo[queue, z];
                If[Length[seen] > cap, Return[makeFailure["ResourceLimit", "The orbit exceeds the group order."], Module]]],
            {i, Length[tensor]}]];
    {arithmetic["Reduce"][Total[Keys[seen]]], Length[seen]}
];

True
