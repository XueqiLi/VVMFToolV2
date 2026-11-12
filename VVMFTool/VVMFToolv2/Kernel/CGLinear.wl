(*
    :Title: Generator-equation Clebsch-Gordan spaces
    :Context: VVMFTool`Private`
    :Summary: Exact (or declared numerical) ket and bra intertwiner spaces of P (x) Q against a target irrep,
        from the equations on every recorded generator, with certified diagonal prefiltering.
    :Responsibilities:
        - cgArithmetic, cgArithmeticFromField: one exact domain (number field or RootReduce) or numerical settings per
          request; the domain is plain data, so the arithmetic can be rebuilt in another kernel.
        - intertwinerSystem: row-major ket/bra equations of all generators.
        - exactDiagonalFilter: unknowns eliminated by exactly certified distinct diagonal eigenvalues.
        - cgNullSpace, cgZeroTest: sound null spaces and zero tests.
        - generatorCGSpaces: complete ket and bra spaces with the character multiplicity.
    :Dependencies: RepresentationValidation.wl (exactField and field helpers, toArithmetic).
    :See Also: VVMFArch/step4Plan.md (GeneratorEquations); RepresentationDecomposition.wl (generatorDecomposition).
*)

(*
    Summary: The working arithmetic of one CG computation.
    Parameters: matrices — every input and target generator matrix (nested lists); settings — from
        arithmeticSettings.
    Options/defaults: settings may carry "NumberField" -> Automatic | True | False (the NumberField option) and
        "FieldMethod" (the FieldMethod option; cgCheckSettings).
    Returns: <|"Settings" -> settings, "Field" -> exact domain or None, "Embed", "Reduce", "Adjoint",
        "ZeroQ", "Back"|> (functions on arrays of the domain).
    Effects: Pure (exactField memoizes domains).
    Failures: An explicit FieldMethod whose domains are all unavailable throws the FieldMethodUnavailable Failure with
        tag cgFieldMethodTag (caught by cgFieldCatch at the CG entry points; never a validation result).
    Example: cgArithmetic[{{{{0, 1}, {1, 0}}}}, exact]["Field"]["Kind"] is "NumberField".
    Remarks: Exact data use one number field containing every entry (Stage 2 exactField; RootReduce domain
        when no field is found in its budget). Numerical data use the settings' precision.
    See also: exactField; arithmeticSettings.
*)
cgArithmetic[matrices_, settings_Association] := Module[{mode = Lookup[settings, "NumberField", Automatic],
        method = Lookup[settings, "FieldMethod", Automatic], field},
    If[settings["Arithmetic"] =!= "Exact", Return[cgArithmeticFromField[None, settings]]];
    (* NumberField: False keeps canonical RootReduce arithmetic; True requires a common number field (callers turn
       a RootReduce domain into FieldConversionFailed); Automatic takes the field when one is found in budget.
       An explicit FieldMethod is used as given (methodOptionsPlan.md 1.1): no silent fallback. *)
    field = Which[mode === False, <|"Kind" -> "RootReduce", "I" -> I, "Method" -> "RootReduce"|>,
        method === Automatic, exactField[matrices],
        True, exactField[matrices, 5, method]];
    If[field["Kind"] === "Unavailable",
        Throw[makeFailure["FieldMethodUnavailable", "No domain of the requested FieldMethod applies to these values.",
            <|"FieldMethod" -> method, "Reason" -> field["Reason"]|>], cgFieldMethodTag]];
    cgArithmeticFromField[field, settings]
];

(*
    Summary: Evaluate CG work, turning a thrown FieldMethodUnavailable into the returned Failure.
    Parameters: expr — held expression.
    Options/defaults: None.
    Returns: The value of expr, or the FieldMethodUnavailable Failure.
    Effects: As expr.
    Failures: FieldMethodUnavailable.
    Example: cgFieldCatch[cgArithmetic[{{{2^(1/3)}}}, s]] with FieldMethod "Cyclotomic" is that Failure.
    See also: cgArithmetic.
*)
SetAttributes[cgFieldCatch, HoldAll];
cgFieldCatch[expr_] := Catch[expr, cgFieldMethodTag];
cgFieldMethodUnavailableQ[x_] := FailureQ[x] && First[x] === "FieldMethodUnavailable";

(*
    Summary: The settings of a CG check or computation carrying the call's domain and verification choices.
    Parameters: base — arithmeticSettings association; carrier — settings, or validated options, of the call.
    Options/defaults: Missing choices are Automatic.
    Returns: base with "NumberField", "FieldMethod", "Verification" and "CheckPrecision" (WorkingPrecision of numerical
        checks of exact data) from the carrier.
    Effects: Pure.
    Failures: None.
    Example: cgCheckSettings[arithmeticSettings["Exact", 50, Automatic, Infinity], <|FieldMethod -> "Cyclotomic"|>]["FieldMethod"]
        is "Cyclotomic".
    Remarks: The one carrier of methodOptionsPlan.md 1.3: every CG site that builds or rebuilds settings uses it, so a
        race subkernel, a revalidation or a stored-entry check works in the domain and at the level the call chose.
    See also: cgArithmetic; prepareCGRequest.
*)
cgCheckSettings[base_Association, carrier_Association] := Join[base, <|
    "NumberField" -> Lookup[carrier, "NumberField", Lookup[carrier, NumberField, Automatic]],
    "FieldMethod" -> Lookup[carrier, "FieldMethod", Lookup[carrier, FieldMethod, Automatic]],
    "Verification" -> Lookup[carrier, "Verification", Lookup[carrier, Verification, Automatic]],
    "CheckPrecision" -> Replace[Lookup[carrier, "CheckPrecision", Lookup[carrier, WorkingPrecision, 50]], Except[_?NumericQ] -> 50]|>];

(*
    Summary: The working arithmetic of a known exact domain (or of numerical settings).
    Parameters: field — exact domain from exactField, a RootReduce domain, or None for numerical settings;
        settings — from arithmeticSettings.
    Options/defaults: None.
    Returns: As cgArithmetic.
    Effects: Pure.
    Failures: None.
    Example: cgArithmeticFromField[cgArithmetic[m, s]["Field"], s] embeds exactly as cgArithmetic[m, s].
    Remarks: The domain itself is plain data and can cross kernels; the functions are rebuilt here, so a result
        computed in a race subkernel is finished in the same domain in the main kernel (CGRace.wl).
    See also: cgArithmetic; cgRaceBatch.
*)
cgArithmeticFromField[field_, settings_Association] := If[field === None || settings["Arithmetic"] =!= "Exact",
    <|"Settings" -> settings, "Field" -> None, "Embed" -> (toArithmetic[#, settings] &), "Reduce" -> Identity,
        "Adjoint" -> ConjugateTranspose, "ZeroQ" -> (Max[Append[Abs[Flatten[{#}]], 0]] <= settings["Tolerance"] &),
        "Back" -> Identity|>,
    <|"Settings" -> settings, "Field" -> field, "Embed" -> (If[# === {}, {}, fieldEmbed[field, #]] &),
        "Reduce" -> (fieldReduce[field, #] &), "Adjoint" -> (fieldAdjoint[field, #] &), "ZeroQ" -> fieldZeroQ,
        "Back" -> (If[# === {}, {}, fieldBack[#]] &)|>];

(*
    Summary: Decide that a domain value (or array) is zero.
    Parameters: expr — value or array; arithmetic — from cgArithmetic.
    Options/defaults: None.
    Returns: True or False.
    Effects: Pure.
    Failures: None.
    Example: cgZeroTest[10^-40, exact] is False: a tiny exact nonzero value is not zero.
    Remarks: Exact mode never uses a tolerance (v1's simpleCGZeroQ could accept small exact values).
    See also: cgArithmetic.
*)
cgZeroTest[expr_, arithmetic_Association] := TrueQ[arithmetic["ZeroQ"][expr]];

(*
    Summary: Row-major linear equations of every generator for kets K (N by dt) or bras W (dt by N).
    Parameters: tensor — matrices R_i (N by N); target — matrices D_i (dt by dt); side — "Ket" or "Bra".
    Options/defaults: None.
    Returns: Matrix acting on Flatten[K] (ket: (R kron I - I kron D^T)) or Flatten[W] (bra:
        (D kron I - I kron R^T)), one block of rows per generator; {} for no generators.
    Effects: Pure.
    Failures: None.
    Example: for one generator R = D = {{1}}, the ket system is {{0}}.
    Remarks: Row-major vec(A X B) = (A kron B^T) vec(X).
    See also: generatorCGSpaces.
*)
intertwinerSystem[tensor_List, target_List, side_String] := Module[{n, dt},
    If[tensor === {}, Return[{}]];
    n = Length[First[tensor]]; dt = Length[First[target]];
    Join @@ MapThread[If[side === "Ket",
        KroneckerProduct[#1, IdentityMatrix[dt]] - KroneckerProduct[IdentityMatrix[n], Transpose[#2]],
        KroneckerProduct[#2, IdentityMatrix[n]] - KroneckerProduct[IdentityMatrix[dt], Transpose[#1]]] &, {tensor, target}]
];

(*
    Summary: Unknowns that the equations of diagonal generators force to vanish.
    Parameters: tensor — R_i; target — D_i; side — "Ket" or "Bra"; arithmetic.
    Options/defaults: None.
    Returns: Boolean matrix (ket N by dt, bra dt by N): True where the entry may be nonzero.
    Effects: Pure.
    Failures: None.
    Example: R = diag(1, -1), D = {{1}} keeps only K[[1, 1]].
    Remarks: For R_i and D_i both diagonal, (R K - K D)_ac = (r_a - d_c) K_ac, so K_ac = 0 when r_a != d_c
        is certified exactly (a nonzero exact difference). A difference that is not decided keeps the
        entry. The full retained system is still solved and every generator validated afterwards.
    See also: generatorCGSpaces.
*)
exactDiagonalFilter[tensor_List, target_List, side_String, arithmetic_Association] := Module[{n, dt, keep},
    If[tensor === {}, Return[None]];
    n = Length[First[tensor]]; dt = Length[First[target]];
    keep = If[side === "Ket", ConstantArray[True, {n, dt}], ConstantArray[True, {dt, n}]];
    Do[If[DiagonalMatrixQ[tensor[[i]]] && DiagonalMatrixQ[target[[i]]],
        With[{r = Diagonal[tensor[[i]]], d = Diagonal[target[[i]]]},
            Do[If[keep[[If[side === "Ket", a, c], If[side === "Ket", c, a]]] &&
                    certifiedNonzeroQ[r[[a]] - d[[c]], arithmetic],
                keep[[If[side === "Ket", a, c], If[side === "Ket", c, a]]] = False], {a, n}, {c, dt}]]],
        {i, Length[tensor]}];
    keep
];

(*
    Summary: Certify that a domain value is nonzero.
    Parameters: x — domain value; arithmetic.
    Options/defaults: None.
    Returns: True only when x is certainly nonzero (exact domains: a nonzero canonical value; numerical:
        magnitude above 10 times the tolerance), otherwise False.
    Effects: Pure.
    Failures: None.
    Example: certifiedNonzeroQ[0, exact] is False.
    See also: exactDiagonalFilter.
*)
certifiedNonzeroQ[x_, arithmetic_Association] := If[arithmetic["Field"] === None,
    TrueQ[Abs[x] > 10 arithmetic["Settings"]["Tolerance"]],
    Which[x === 0, False, Head[x] === AlgebraicNumber, True,
        True, TrueQ[Quiet[TimeConstrained[RootReduce[x] =!= 0, 5, False]]]]];

(*
    Summary: Null space of a CG system, with optional eliminated unknowns.
    Parameters: system — equation matrix; keep — None or a Boolean array of retained unknowns (row-major);
        arithmetic.
    Options/defaults: None.
    Returns: List of null vectors on all unknowns (eliminated entries restored as zeros), or Failure.
    Effects: Pure.
    Failures: PrecisionFailure when a numerical rank is not separated by the tolerance.
    Example: cgNullSpace[{{1, -1}}, None, exact] spans {1, 1}.
    Remarks: Numerical mode uses the SVD and requires a clear rank gap (no singular value in
        (tolerance, 10 tolerance]).
    See also: generatorCGSpaces.
*)
cgNullSpace[system_, keep_, arithmetic_Association] := Module[{columns, reduced, null, u, w, v, sigma, threshold, kept, unknowns},
    unknowns = If[system === {}, If[keep === None, 0, Length[Flatten[keep]]], Length[First[system]]];
    columns = If[keep === None, Range[unknowns], Flatten[Position[Flatten[keep], True]]];
    If[columns === {}, Return[{}]];
    If[system === {}, Return[UnitVector[unknowns, #] & /@ columns]];
    reduced = system[[All, columns]];
    null = If[arithmetic["Field"] =!= None,
        fieldNullSpace[arithmetic["Field"], arithmetic["Reduce"][reduced]],
        {u, w, v} = SingularValueDecomposition[reduced];
        sigma = Join[Diagonal[w], ConstantArray[0, Max[0, Length[columns] - Length[Diagonal[w]]]]];
        threshold = arithmetic["Settings"]["Tolerance"] Max[Append[Abs[sigma], 1]];
        kept = Flatten[Position[Abs[sigma], x_ /; x <= threshold, {1}, Heads -> False]];
        If[Complement[Range[Length[columns]], kept] =!= {} &&
                Min[Abs[sigma[[Complement[Range[Length[columns]], kept]]]]] <= 10 threshold,
            Return[makeFailure["PrecisionFailure", "The numerical rank of the CG equations is not separated at this precision."]]];
        Transpose[v][[kept]]];
    Normal[SparseArray[Thread[columns -> #], unknowns]] & /@ null
];

(*
    Summary: Complete ket and bra intertwiner spaces of P (x) Q for one target irrep.
    Parameters: p, q, target — generator matrix lists of the inputs and the target (domain values);
        multiplicity — the character multiplicity; arithmetic; prefilter — Boolean.
    Options/defaults: None.
    Returns: <|"Kets" -> list of N by dt matrices, "Bras" -> list of dt by N matrices, "Tensor" -> R_i|>, or
        Failure.
    Effects: Pure.
    Failures: UnprovedIdentity when either space does not have the character multiplicity;
        PrecisionFailure (numerical rank).
    Example: A4 triplet (x) triplet against the triplet gives two kets and two bras.
    Remarks: No group elements are enumerated. With no generators every vector is invariant: the trivial
        target gets N copies.
    See also: intertwinerSystem; exactDiagonalFilter; normalizeCGCopies.
*)
generatorCGSpaces[p_List, q_List, target_List, dims : {dp_Integer, dq_Integer, dt_Integer}, multiplicity_Integer,
    arithmetic_Association, prefilter_ : True] := Module[{tensor, kets, bras, keepK, keepW},
    tensor = MapThread[arithmetic["Reduce"][KroneckerProduct[#1, #2]] &, {p, q}];
    keepK = If[TrueQ[prefilter], exactDiagonalFilter[tensor, target, "Ket", arithmetic], None];
    keepW = If[TrueQ[prefilter], exactDiagonalFilter[tensor, target, "Bra", arithmetic], None];
    If[tensor === {}, keepK = ConstantArray[True, {dp dq, dt}]; keepW = ConstantArray[True, {dt, dp dq}]];
    kets = cgNullSpace[intertwinerSystem[tensor, target, "Ket"], keepK, arithmetic];
    If[FailureQ[kets], Return[kets]];
    bras = cgNullSpace[intertwinerSystem[tensor, target, "Bra"], keepW, arithmetic];
    If[FailureQ[bras], Return[bras]];
    If[Length[kets] =!= multiplicity || Length[bras] =!= multiplicity,
        Return[makeFailure["UnprovedIdentity", "The intertwiner spaces do not have the character multiplicity.",
            <|"Kets" -> Length[kets], "Bras" -> Length[bras], "Multiplicity" -> multiplicity|>]]];
    <|"Kets" -> (Partition[#, dt] & /@ kets), "Bras" -> (Partition[#, dp dq] & /@ bras), "Tensor" -> tensor|>
];

True
