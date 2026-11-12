(*
    :Title: Isotypic, spectral and adapted-state Clebsch-Gordan routes
    :Context: VVMFTool`Private`
    :Summary: CanonicalHybrid (character projector, then generator equations on the isotypic image),
        CommutantSpectral (eigenspaces of a generic Hermitian commutant element, aligned to the target) and
        AdaptedStates (SMILY-type adapted bases from two generic Hermitian group-algebra elements), with exact
        reconstruction of numerical proposals in the inputs' number field.
    :Responsibilities: isotypicImage, canonicalCG, commutantCG, adaptedStateCG, alignCGBlocks, recognizeFieldEntry,
        reconstructCG.
    :Dependencies: CGLinear.wl; CGProjection.wl (cgElementImages); CGValidation.wl; RepresentationValidation.wl.
    :See Also: VVMFArch/step4Plan.md (CanonicalHybrid, CommutantSpectral, AdaptedStates);
        https://arxiv.org/html/1610.01054v2 (adapted states).
*)

(*
    Summary: Evaluate a numerical route at the fixed working precision of its settings.
    Parameters: settings — numerical arithmeticSettings; body — held expression.
    Options/defaults: None.
    Returns: The value of body.
    Effects: Pure.
    Failures: None.
    Example: fixedPrecision[<|"Precision" -> 50|>, Eigensystem[h]] keeps 50-digit numbers.
    Remarks: Wolfram's significance arithmetic reports clustered (degenerate) eigensystems with very low
        precision, although the invariant subspaces are well determined; the spectral routes need the working
        precision kept. Their results are always validated afterwards (residuals, or exact reconstruction).
        Machine precision is left unchanged.
    See also: commutantCG; adaptedStateCG.
*)
SetAttributes[fixedPrecision, HoldRest];
fixedPrecision[settings_Association, body_] := If[NumericQ[settings["Precision"]] && settings["Precision"] =!= MachinePrecision,
    Block[{$MinPrecision = settings["Precision"], $MaxPrecision = settings["Precision"]}, body], body];

(*
    Summary: Basis of the target's isotypic component of P (x) Q and the equivariant coordinate map onto it.
    Parameters: elements — from cgElementImages; dims; multiplicity; arithmetic.
    Options/defaults: None.
    Returns: <|"Basis" -> B (N by k), "Coordinates" -> C (k by N), "Restricted" -> R_V(g_i) for the generator
        images supplied as tensor, "Rank" -> k|> with k = multiplicity dt, or Failure.
    Effects: Pure.
    Failures: UnprovedIdentity when the projector rank differs from multiplicity dt.
    Example: for A4 3 (x) 3 and the triplet target the image has dimension 6.
    Remarks: Pi = (dt/|image|) Sum_g chi(g^-1) R(g) with chi(g^-1) = Tr D(g^-1) = Tr Dinv(g). Pi commutes with R,
        so with B the independent columns of Pi and C solving B C = Pi, C R = R_V C and R B = B R_V.
    See also: canonicalCG.
*)
isotypicImage[elements_List, tensor_List, dims : {dp_Integer, dq_Integer, dt_Integer}, multiplicity_Integer, arithmetic_Association] := Module[
    {n = dp dq, projector, columns = {}, b, c, rank = 0, r, field = arithmetic["Field"], solve},
    projector = arithmetic["Reduce"][(dt/Length[elements]) Total[Map[Tr[#[[3]]] KroneckerProduct[#[[1]], #[[2]]] &, elements]]];
    Do[With[{candidate = Append[columns, projector[[All, j]]]},
            r = If[field =!= None, fieldRank[field, candidate], MatrixRank[candidate, Tolerance -> arithmetic["Settings"]["Tolerance"]]];
            If[r > rank, columns = candidate; rank = r]],
        {j, n}];
    If[rank =!= multiplicity dt,
        Return[makeFailure["UnprovedIdentity", "The character projector's rank is not multiplicity times the target dimension.",
            <|"Rank" -> rank, "Expected" -> multiplicity dt|>]]];
    b = Transpose[columns];
    solve = If[field =!= None, fieldInverse[field, arithmetic["Reduce"][arithmetic["Adjoint"][b] . b]] . arithmetic["Adjoint"][b],
        PseudoInverse[b]];
    (* C = B^+ Pi: a left inverse of B composed with Pi (B C = Pi because Pi's columns lie in span B). *)
    c = arithmetic["Reduce"][solve . projector];
    <|"Basis" -> b, "Coordinates" -> c, "Restricted" -> (arithmetic["Reduce"][solve . # . b] & /@ tensor), "Rank" -> rank|>
];

(*
    Summary: CanonicalHybrid: generator equations restricted to the target's isotypic image, lifted back.
    Parameters: p, q, target — domain generator matrices; dims; order; multiplicity; arithmetic.
    Options/defaults: None.
    Returns: <|"Kets", "Bras", "IsotypicDimension"|> on the full space, or Failure.
    Effects: Pure.
    Failures: cgElementImages, isotypicImage and generatorCGSpaces failures.
    Example: canonicalCG[...]["Kets"] spans the same space as generatorCGSpaces[...]["Kets"].
    Remarks: The restricted system has k dt unknowns (k = multiplicity dt) instead of N dt. Kets lift by B,
        bras by C (W = W_V C): R B = B R_V and C R = R_V C keep covariance.
    See also: isotypicImage; generatorCGSpaces.
*)
canonicalCG[p_List, q_List, target_List, dims : {dp_Integer, dq_Integer, dt_Integer}, order_Integer, multiplicity_Integer,
    arithmetic_Association] := Module[{elements, tensor, image, inner},
    If[multiplicity === 0, Return[<|"Kets" -> {}, "Bras" -> {}, "IsotypicDimension" -> 0|>]];
    elements = cgElementImages[p, q, target, dims, order, arithmetic];
    If[FailureQ[elements], Return[elements]];
    tensor = MapThread[arithmetic["Reduce"][KroneckerProduct[#1, #2]] &, {p, q}];
    image = isotypicImage[elements, tensor, dims, multiplicity, arithmetic];
    If[FailureQ[image], Return[image]];
    (* The restricted representation is not a tensor product: solve its equations with Q = the trivial factor. *)
    inner = generatorCGSpaces[image["Restricted"], ConstantArray[{{1}}, Length[target]], target, {image["Rank"], 1, dt}, multiplicity,
        arithmetic, True];
    If[FailureQ[inner], Return[inner]];
    <|"Kets" -> (arithmetic["Reduce"][image["Basis"] . #] & /@ inner["Kets"]),
        "Bras" -> (arithmetic["Reduce"][# . image["Coordinates"]] & /@ inner["Bras"]), "IsotypicDimension" -> image["Rank"]|>
];

(*
    Summary: Align an invariant block of P (x) Q to the stored target by the isomorphism equations.
    Parameters: block — N by dt basis matrix of an invariant subspace; tensor — R_i; target — D_i; settings — numerical
        arithmetic settings.
    Options/defaults: None.
    Returns: K = block . X with R K = K D (X the one-dimensional solution of R_b X = X D, R_b the restriction), or
        Failure.
    Effects: Pure.
    Failures: UnprovedIdentity when the block is not isomorphic to the target (no or several solutions).
    Example: an eigenspace block of a commutant element that carries the triplet aligns to the stored triplet.
    Remarks: Schur's lemma makes the solution unique up to a scalar for an irreducible block.
    See also: commutantCG; adaptedStateCG.
*)
alignCGBlocks[block_, tensor_List, target_List, settings_Association] := Module[{dt = Length[First[target]], left, restricted, ar, null},
    left = PseudoInverse[block];
    restricted = (left . # . block) & /@ tensor;
    ar = cgArithmetic[{}, settings]; (* numerical settings: no exact domain, so FieldMethod does not apply *)
    null = cgNullSpace[intertwinerSystem[restricted, target, "Ket"], None, ar];
    If[FailureQ[null], Return[null]];
    If[Length[null] =!= 1, Return[makeFailure["UnprovedIdentity", "The block is not one copy of the target.", <|"Solutions" -> Length[null]|>]]];
    block . Partition[First[null], dt]
];

(*
    Summary: Numerical intertwiner kets from eigenspaces of a generic Hermitian element of the commutant.
    Parameters: p, q, target — numerical generator matrices of unitary inputs and target; dims; multiplicity;
        settings — numerical settings; seed — integer for the generic combination.
    Options/defaults: None.
    Returns: <|"Kets", "Bras", "Candidates"|>, or Failure.
    Effects: Pure (local random seed).
    Failures: UnprovedIdentity when no generic split separates the copies (degenerate eigenvalues for every
        tried combination) or the aligned copies do not reach the multiplicity; PrecisionFailure.
    Example: for A4 3 (x) 3 the commutant has dimension 1 + 1 + 1 + 4 = 7 and the triplet gives two blocks.
    Remarks: The commutant of R is a direct sum of matrix algebras M_m (x) I_d; a generic Hermitian element has
        one eigenspace per irreducible copy. Eigenspaces of dimension dt are aligned to the target; unitary
        inputs make the bras the adjoints. Requires unitary inputs (callers transport general bases through a
        verified temporary unitary form first).
    See also: alignCGBlocks; adaptedStateCG; reconstructCG.
*)
commutantCG[p_List, q_List, target_List, dims : {dp_Integer, dq_Integer, dt_Integer}, multiplicity_Integer, settings_Association,
    seed_Integer : 1] := fixedPrecision[settings, Module[{n = dp dq, tensor, ar, commutant, attempt, result = None},
    If[multiplicity === 0, Return[<|"Kets" -> {}, "Bras" -> {}, "Candidates" -> 0|>]];
    tensor = MapThread[KroneckerProduct, {p, q}];
    ar = cgArithmetic[{}, settings]; (* numerical settings: no exact domain, so FieldMethod does not apply *)
    (* Commutant: H R_i - R_i H = 0, row-major. *)
    commutant = cgNullSpace[If[tensor === {}, {}, Join @@ (KroneckerProduct[#, IdentityMatrix[n]] - KroneckerProduct[IdentityMatrix[n], Transpose[#]] & /@ tensor)],
        If[tensor === {}, ConstantArray[True, {n, n}], None], ar];
    If[FailureQ[commutant], Return[commutant]];
    Do[Module[{coefficients, h, system, values, vectors, groups, kets},
            coefficients = BlockRandom[RandomComplex[{-1 - I, 1 + I}, Length[commutant], WorkingPrecision -> settings["Precision"]], RandomSeeding -> Hash[{seed, attempt}]];
            h = Partition[coefficients . commutant, n];
            h = (h + ConjugateTranspose[h])/2;
            {values, vectors} = Eigensystem[h];
            (* Group eigenvalues that agree at the tolerance; a generic element gives one group per copy. *)
            groups = Gather[Range[n], Abs[values[[#1]] - values[[#2]]] <= 100 settings["Tolerance"] Max[1, Max[Abs[values]]] &];
            kets = DeleteCases[Map[If[Length[#] === dt, alignCGBlocks[Transpose[Orthogonalize[vectors[[#]]]], tensor, target, settings], Nothing] &, groups],
                _Failure];
            If[Length[kets] === multiplicity, result = kets; Break[]]],
        {attempt, 3}];
    If[result === None, Return[makeFailure["UnprovedIdentity", "No generic commutant element separated the target's copies."]]];
    <|"Kets" -> result, "Bras" -> (ConjugateTranspose /@ result), "Candidates" -> Length[result]|>
]];

(*
    Summary: Numerical kets from adapted states of two generic Hermitian group-algebra elements (SMILY steps 1-8).
    Parameters: p, q, target — numerical generator matrices of unitary inputs and target; dims; order; multiplicity;
        settings; seed.
    Options/defaults: None.
    Returns: <|"Kets", "Bras"|>, or Failure.
    Effects: Pure (local random seed).
    Failures: UnprovedIdentity when the elements are not generic (an eigenvalue of A1 on the target is not simple,
        a transfer amplitude vanishes, or the eigenspace dimensions differ from the multiplicity) for every tried
        seed; image enumeration failures.
    Example: adaptedStateCG on A4 3 (x) 3 -> 3 gives two kets.
    Remarks: A_k = Sum_g a_g R(g) with a_(g^-1) = conj(a_g) is Hermitian for unitary R and acts as I_m (x) Ahat_k on
        the target's isotypic part. With w_1 a unit eigenvector of Ahat_1 and w_j = Pihat_j Ahat_2 w_1 (Pihat_j the
        eigenprojector of Ahat_1 for its j-th eigenvalue), and on the tensor side y_(c,1) an orthonormal basis of the
        lambda_1-eigenspace of A_1 restricted to the isotypic part and y_(c,j) = Pi_j A_2 y_(c,1), the maps K_c with
        K_c w_j = y_(c,j) intertwine D and R (both sides are built by the same algebra elements). Genericity is
        checked, not assumed.
    See also: commutantCG; cgElementImages.
*)
adaptedStateCG[p_List, q_List, target_List, dims : {dp_Integer, dq_Integer, dt_Integer}, order_Integer, multiplicity_Integer,
    settings_Association, seed_Integer : 1] := fixedPrecision[settings, Module[{ar, elements, inverseIndex, result = None, n = dp dq, tolerance},
    If[multiplicity === 0, Return[<|"Kets" -> {}, "Bras" -> {}|>]];
    ar = cgArithmetic[{}, settings]; (* numerical settings: no exact domain, so FieldMethod does not apply *)
    tolerance = 100 settings["Tolerance"];
    elements = cgElementImages[p, q, target, dims, order, ar];
    If[FailureQ[elements], Return[elements]];
    (* Index of each element's inverse (Dinv(g) = D(g^-1)^T, so g^-1 has Dinv = D(g)^T; match on the full triple). *)
    (* The nearest element to the numerical inverse; the match must be unambiguous at the tolerance. *)
    (* Values are already at the working precision (no N: inside fixedPrecision a lower N request is refused). *)
    inverseIndex = Module[{vectors = Flatten[{Re[#], Im[#]}] & /@ elements, nearest},
        nearest = Nearest[vectors -> Automatic];
        Table[With[{v = Flatten[{Re[#], Im[#]}] &[{Inverse[elements[[k, 1]]], Inverse[elements[[k, 2]]], Inverse[elements[[k, 3]]]}]},
            First[nearest[v, 1]]], {k, Length[elements]}]];
    If[Sort[inverseIndex] =!= Range[Length[elements]],
        Return[makeFailure["PrecisionFailure", "Group elements could not be paired with their inverses at this precision."]]];
    Do[Module[{a1, a2, coefficients, bigA, hatA, isotypic, values, vectors, hatValues, hatVectors, order1, eigen, w, y, kets, project, hatProject, simple},
            (* Two independent pseudorandom coefficient vectors from one seeded draw; a_(g^-1) = conj(a_g) makes each
               element Hermitian. *)
            coefficients = Map[Function[c, Table[(c[[i]] + Conjugate[c[[inverseIndex[[i]]]]])/2, {i, Length[elements]}]],
                Partition[BlockRandom[RandomComplex[{-1 - I, 1 + I}, 2 Length[elements], WorkingPrecision -> settings["Precision"]],
                    RandomSeeding -> Hash[{"AdaptedStates", seed, attempt}]], Length[elements]]];
            bigA = Table[Total[MapThread[#1 KroneckerProduct[#2[[1]], #2[[2]]] &, {coefficients[[k]], elements}]], {k, 2}];
            hatA = Table[Total[MapThread[#1 Transpose[Inverse[#2[[3]]]] &, {coefficients[[k]], elements}]], {k, 2}];
            {hatValues, hatVectors} = Eigensystem[(hatA[[1]] + ConjugateTranspose[hatA[[1]]])/2];
            simple = AllTrue[Subsets[Range[dt], {2}], Abs[hatValues[[#[[1]]]] - hatValues[[#[[2]]]]] > tolerance &];
            If[!simple, Continue[]];
            hatProject[j_] := Outer[Times, hatVectors[[j]], Conjugate[hatVectors[[j]]]];
            (* Tensor-side eigenspace of A1 for each target eigenvalue (restricted to the isotypic part via the
               character projector). *)
            isotypic = (dt/Length[elements]) Total[Map[Tr[#[[3]]] KroneckerProduct[#[[1]], #[[2]]] &, elements]];
            project[j_] := Module[{shifted = isotypic . (bigA[[1]] - hatValues[[j]] IdentityMatrix[n]) . isotypic, null},
                null = NullSpace[Chop[shifted, tolerance] + (IdentityMatrix[n] - isotypic) , Tolerance -> tolerance];
                null];
            eigen = Orthogonalize[project[1]];
            If[Length[eigen] =!= multiplicity, Continue[]];
            w = Table[If[j === 1, hatVectors[[1]], hatProject[j] . hatA[[2]] . hatVectors[[1]]], {j, dt}];
            If[AnyTrue[w[[2 ;;]], Norm[#] <= tolerance &], Continue[]];
            y = Table[Table[If[j === 1, eigen[[c]], With[{space = project[j]},
                    Transpose[space] . PseudoInverse[Transpose[space]] . bigA[[2]] . eigen[[c]]]], {j, dt}], {c, multiplicity}];
            kets = Table[Transpose[y[[c]]] . Inverse[Transpose[w]], {c, multiplicity}];
            result = kets; Break[]],
        {attempt, 3}];
    If[result === None, Return[makeFailure["UnprovedIdentity", "The adapted-state elements were not generic for this target."]]];
    <|"Kets" -> result, "Bras" -> (PseudoInverse /@ result)|>
]];

(*
    Summary: Recognize a numerical value as an element of a number field.
    Parameters: x — numerical value (or an exact rational, returned unchanged); field — NumberField domain from
        exactField (or None for the rationals); bound — maximal denominator considered; digits — trusted digits of
        x (Automatic: its precision).
    Options/defaults: None.
    Returns: AlgebraicNumber (or rational) whose value agrees with x, or $Failed.
    Effects: Pure.
    Failures: $Failed.
    Example: recognizeFieldEntry[N[Sqrt[2]/3, 60], exactField[{Sqrt[2]}], 10^6] is the field element Sqrt[2]/3.
    Remarks: An integer relation among the power basis of the field generator and x (LatticeReduce); the caller
        verifies every recognized matrix exactly, so a wrong recognition is rejected, never accepted.
    See also: reconstructCG.
*)
recognizeFieldEntry[x_, field_, bound_Integer, digits_ : Automatic] := Module[{generator, degree, basis, value, scale, lattice, row, accuracy},
    If[MatchQ[x, _Integer | _Rational | Complex[_Integer | _Rational, _Integer | _Rational]], Return[x]];
    accuracy = Replace[digits, Automatic :> Precision[x]];
    If[!NumericQ[accuracy] || accuracy === Infinity || accuracy === MachinePrecision, accuracy = 15];
    If[Abs[x] < 10^(-accuracy/2), Return[0]];
    If[field === None || field["Kind"] =!= "NumberField",
        Return[With[{r = Rationalize[Re[x], 10^(-accuracy/2)] + I Rationalize[Im[x], 10^(-accuracy/2)]},
            If[Max[Denominator[Re[r]], Denominator[Im[r]]] <= bound, r, $Failed]]]];
    generator = field["Generator"]; degree = field["Degree"];
    basis = N[generator^Range[0, degree - 1], accuracy + 20];
    value = SetPrecision[x, accuracy];
    scale = 10^Floor[accuracy/2];
    lattice = Join[MapThread[Join[UnitVector[degree + 1, #1], Round[scale {Re[#2], Im[#2]}]] &, {Range[degree], basis}],
        {Join[UnitVector[degree + 1, degree + 1], Round[-scale {Re[value], Im[value]}]]}];
    row = SelectFirst[LatticeReduce[lattice], #[[degree + 1]] =!= 0 && Abs[#[[degree + 1]]] <= bound &, None];
    If[row === None, $Failed, AlgebraicNumber[generator, row[[1 ;; degree]]/row[[degree + 1]]]]
];

(*
    Summary: Exact kets and bras from a numerical proposal.
    Parameters: proposal — <|"Kets", "Bras"|> numerical; p, q, target — exact generator matrices; dims; multiplicity;
        precision — digits of the proposal; carrier — the request's settings (NumberField, FieldMethod; cgCheckSettings).
    Options/defaults: carrier <||> (Automatic domain).
    Returns: <|"Kets", "Bras", "Arithmetic" -> domain|> in exact domain values, or Failure.
    Effects: Pure.
    Failures: ReconstructionFailed when an entry is not recognized, the recognized matrices are not exact
        intertwiners on every generator, or the rank drops below the multiplicity.
    Example: reconstructCG of commutantCG's kets for A4 3 (x) 3 -> 3 gives two exact kets.
    Remarks: The proposal's span is brought to reduced row-echelon form (pivot entries 1) so its entries are field
        elements independent of the arbitrary numerical basis; each entry is recognized in the inputs' number field
        and the result is accepted only after exact covariance and rank checks.
    See also: recognizeFieldEntry; commutantCG; adaptedStateCG.
*)
reconstructCG[proposal_Association, p_List, q_List, target_List, dims : {dp_Integer, dq_Integer, dt_Integer}, multiplicity_Integer,
    precision_, carrier_Association : <||>] := Module[{settings, ar, field, side, result = <||>, tensor, ps, qs, ds, failure},
    (* the call's domain choice (cgCheckSettings); this runs in race subkernels too *)
    settings = cgCheckSettings[arithmeticSettings["Exact", 50, Automatic, Infinity], carrier];
    ar = cgArithmetic[{p, q, target}, settings];
    field = ar["Field"];
    {ps, qs, ds} = ar["Embed"] /@ {p, q, target};
    tensor = MapThread[ar["Reduce"][KroneckerProduct[#1, #2]] &, {ps, qs}];
    failure = Catch[Do[Module[{vectors, echelon, recognized, matrices, covariant},
            vectors = Flatten /@ proposal[side];
            If[Length[vectors] =!= multiplicity, Throw[makeFailure["ReconstructionFailed", "The proposal does not have the multiplicity."], "Reconstruction"]];
            echelon = Select[RowReduce[vectors, Tolerance -> 10^(-precision/3)], Norm[#] > 10^(-precision/3) &];
            recognized = Map[recognizeFieldEntry[#, field, 10^6, precision/2] &, echelon, {2}];
            If[!FreeQ[recognized, $Failed], Throw[makeFailure["ReconstructionFailed", "An entry of the numerical proposal was not recognized in the field."], "Reconstruction"]];
            matrices = If[side === "Kets", Partition[#, dt], Partition[#, dp dq]] & /@ recognized;
            covariant = AllTrue[matrices, Function[m, AllTrue[Range[Length[tensor]], If[side === "Kets",
                fieldZeroQ[ar["Reduce"][tensor[[#]] . m - m . ds[[#]]]], fieldZeroQ[ar["Reduce"][m . tensor[[#]] - ds[[#]] . m]]] &]]];
            If[!covariant || Length[independentMatrices[matrices, ar]] =!= multiplicity,
                Throw[makeFailure["ReconstructionFailed", "The recognized matrices are not exact intertwiners of full rank."], "Reconstruction"]];
            result[side] = matrices],
        {side, {"Kets", "Bras"}}]; None, "Reconstruction"];
    If[FailureQ[failure], Return[failure]];
    Join[result, <|"Arithmetic" -> ar|>]
];

True
