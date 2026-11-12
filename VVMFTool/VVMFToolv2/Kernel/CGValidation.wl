(*
    :Title: CG exchange sectors, normalization, duals and validation
    :Context: VVMFTool`Private`
    :Summary: Shared post-processing of every CG route: split equal-factor exchange sectors, normalize the
        multiplicity space (Unitary: orthonormal copies with W = K^dagger; Dual: W H^-1 pairing), and validate
        covariance, rank, pairing and symmetry on every recorded generator.
    :Responsibilities: swapOperator, independentMatrices, splitExchangeCopies, normalizeCGCopies, dualCGMaps,
        validateCGBundle, assembleCG, flipCG.
    :Dependencies: CGLinear.wl (cgArithmetic, cgZeroTest); RepresentationBasis.wl (ldlDecomposition);
        RepresentationValidation.wl (field helpers).
    :See Also: VVMFArch/step4Plan.md (shared mathematical contracts).
*)

(*
    Summary: The exchange operator on C^(d d): a_i b_j -> a_j b_i.
    Parameters: d — factor dimension.
    Options/defaults: None.
    Returns: d^2 by d^2 permutation matrix S (row (i-1) d + j).
    Effects: Pure.
    Failures: None.
    Example: swapOperator[2] swaps rows 2 and 3.
    See also: splitExchangeCopies; flipCG.
*)
swapOperator[d_Integer] := Normal[SparseArray[Flatten[Table[{(i - 1) d + j, (j - 1) d + i} -> 1, {i, d}, {j, d}]], {d^2, d^2}]];

(*
    Summary: A maximal linearly independent subfamily of matrices, in order.
    Parameters: matrices — equally shaped matrices; arithmetic — from cgArithmetic.
    Options/defaults: None.
    Returns: The selected matrices.
    Effects: Pure.
    Failures: None.
    Example: independentMatrices[{a, 2 a, b}, exact] is {a, b} for independent a, b.
    Remarks: Exact rank in the field; numerical rank at the settings' tolerance.
    See also: splitExchangeCopies.
*)
independentMatrices[matrices_List, arithmetic_Association] := Module[{selected = {}, rank = 0, r},
    Do[
        r = If[arithmetic["Field"] =!= None,
            fieldRank[arithmetic["Field"], Flatten /@ Append[selected, m]],
            MatrixRank[Flatten /@ Append[selected, m], Tolerance -> arithmetic["Settings"]["Tolerance"]]];
        If[r > rank, AppendTo[selected, m]; rank = r],
        {m, matrices}];
    selected
];

(*
    Summary: Split ket and bra spaces of an equal-factor product into symmetric and antisymmetric sectors.
    Parameters: spaces — <|"Kets", "Bras"|> from generatorCGSpaces; d — factor dimension; arithmetic.
    Options/defaults: None.
    Returns: {<|"Symmetry" -> "Symmetric", "Kets", "Bras"|>, <|"Symmetry" -> "Antisymmetric", ...|>} with empty
        sectors dropped, or Failure.
    Effects: Pure.
    Failures: UnprovedIdentity when the sector dimensions of kets and bras disagree or do not add up.
    Example: A4 3 (x) 3 -> 3 splits into one symmetric and one antisymmetric copy.
    Remarks: S commutes with P (x) P, so the spaces are S-invariant and K +- S K span the sectors.
    See also: swapOperator; normalizeCGCopies.
*)
splitExchangeCopies[spaces_Association, d_Integer, arithmetic_Association] := Module[{s = swapOperator[d], sectors, m},
    m = Length[spaces["Kets"]];
    sectors = {
        <|"Symmetry" -> "Symmetric", "Kets" -> independentMatrices[arithmetic["Reduce"][# + s . #] & /@ spaces["Kets"], arithmetic],
            "Bras" -> independentMatrices[arithmetic["Reduce"][# + # . s] & /@ spaces["Bras"], arithmetic]|>,
        <|"Symmetry" -> "Antisymmetric", "Kets" -> independentMatrices[arithmetic["Reduce"][# - s . #] & /@ spaces["Kets"], arithmetic],
            "Bras" -> independentMatrices[arithmetic["Reduce"][# - # . s] & /@ spaces["Bras"], arithmetic]|>};
    If[AnyTrue[sectors, Length[#["Kets"]] =!= Length[#["Bras"]] &] || Total[Length[#["Kets"]] & /@ sectors] =!= m,
        Return[makeFailure["UnprovedIdentity", "The exchange sectors of kets and bras do not match the multiplicity."]]];
    Select[sectors, #["Kets"] =!= {} &]
];

(*
    Summary: Normalize one sector's multiplicity space.
    Parameters: sector — <|"Symmetry", "Kets", "Bras"|> in domain arithmetic; mode — "Unitary" or "Dual";
        arithmetic; dt — target dimension.
    Options/defaults: None.
    Returns: List of <|"Symmetry", "Embedding" -> K, "Dual" -> W|> with canonical exact (or numerical) entries,
        or Failure.
    Effects: Pure.
    Failures: UnprovedIdentity — Schur block identities K_a^dagger K_b = H_ab I or W_a K_b = H_ab I fail, a
        nonpositive Gram pivot, or a singular pairing.
    Example: one unitary copy K with K^dagger K = 2 I becomes K/Sqrt[2] with W = K^dagger.
    Remarks: Unitary: with unitary inputs and target, H = (K_a^dagger K_b)_11 is positive; LDL H = L D L^dagger
        and Y = X (L^dagger)^-1 give Y_k^dagger Y_k = D_k I, and K_k = Y_k / Sqrt[D_k] (square roots enter only
        here). Dual: H_ab from W_a K_b = H_ab I, W' = H^-1 W; no square roots.
    See also: dualCGMaps; ldlDecomposition.
*)
normalizeCGCopies[sector_Association, mode_String, arithmetic_Association, dt_Integer] := Module[
    {kets = sector["Kets"], m, adjoint = arithmetic["Adjoint"], reduce = arithmetic["Reduce"], g, ldl, mixing, ys, back},
    m = Length[kets];
    If[mode === "Dual", Return[dualCGMaps[sector, arithmetic, dt]]];
    g = Table[reduce[adjoint[kets[[a]]] . kets[[b]]][[1, 1]], {a, m}, {b, m}];
    If[!AllTrue[Flatten[Table[reduce[adjoint[kets[[a]]] . kets[[b]] - g[[a, b]] IdentityMatrix[dt]], {a, m}, {b, m}], 1],
            cgZeroTest[#, arithmetic] &],
        Return[makeFailure["UnprovedIdentity", "The copies' Gram blocks are not scalar (the inputs or target are not unitary)."]]];
    ldl = ldlDecomposition[g, If[arithmetic["Field"] =!= None, <|"Field" -> arithmetic["Field"]|>, arithmetic["Settings"]]];
    If[FailureQ[ldl], Return[ldl]];
    mixing = If[arithmetic["Field"] =!= None, fieldInverse[arithmetic["Field"], adjoint[First[ldl]]], Inverse[ConjugateTranspose[First[ldl]]]];
    ys = Table[reduce[Sum[mixing[[l, k]] kets[[l]], {l, m}]], {k, m}];
    back = If[arithmetic["Field"] =!= None, fieldBack[Last[ldl]], Last[ldl]];
    Table[With[{k = If[arithmetic["Field"] =!= None,
                Map[RootReduce, fieldBack[ys[[c]]] / Sqrt[back[[c]]], {2}], ys[[c]] / Sqrt[back[[c]]]]},
            Join[<|"Symmetry" -> sector["Symmetry"], "Embedding" -> k,
                "Dual" -> If[arithmetic["Field"] =!= None, Map[RootReduce, ConjugateTranspose[k], {2}], ConjugateTranspose[k]]|>,
                (* exact: the field form the stored values are made from, K = Y / Sqrt[n] and W = K^dagger
                   (cgFactoredValidationPlan.md 7); a private key, dropped by finishCGBundle *)
                If[arithmetic["Field"] =!= None, <|"FieldForm" -> <|"Y" -> ys[[c]], "Norm" -> Last[ldl][[c]]|>|>, <||>]]],
        {c, m}]
];

(*
    Summary: Dual normalization of one sector: bras paired to kets, W_a K_b = delta_ab I.
    Parameters: sector — <|"Symmetry", "Kets", "Bras"|>; arithmetic; dt.
    Options/defaults: None.
    Returns: List of <|"Symmetry", "Embedding", "Dual"|> (canonical values), or Failure.
    Effects: Pure.
    Failures: UnprovedIdentity — a pairing block that is not scalar, or a singular pairing matrix.
    Example: kets {K} and bras {W} with W K = 3 I give the dual W/3.
    Remarks: The pairing W_a K_b is a scalar multiple of the identity by Schur's lemma; a non-scalar block
        proves a wrong space. General (nonunitary) bases need no positivity.
    See also: normalizeCGCopies.
*)
dualCGMaps[sector_Association, arithmetic_Association, dt_Integer] := Module[
    {kets = sector["Kets"], bras = sector["Bras"], m, reduce = arithmetic["Reduce"], h, hinverse, duals},
    m = Length[kets];
    h = Table[reduce[bras[[a]] . kets[[b]]][[1, 1]], {a, m}, {b, m}];
    If[!AllTrue[Flatten[Table[reduce[bras[[a]] . kets[[b]] - h[[a, b]] IdentityMatrix[dt]], {a, m}, {b, m}], 1], cgZeroTest[#, arithmetic] &],
        Return[makeFailure["UnprovedIdentity", "The bra-ket pairing blocks are not scalar."]]];
    If[If[arithmetic["Field"] =!= None, fieldRank[arithmetic["Field"], h], MatrixRank[h, Tolerance -> arithmetic["Settings"]["Tolerance"]]] < m,
        Return[makeFailure["UnprovedIdentity", "The bra-ket pairing is singular."]]];
    hinverse = If[arithmetic["Field"] =!= None, fieldInverse[arithmetic["Field"], h], Inverse[h]];
    duals = Table[reduce[Sum[hinverse[[a, b]] bras[[b]], {b, m}]], {a, m}];
    Table[<|"Symmetry" -> sector["Symmetry"], "Embedding" -> arithmetic["Back"][kets[[c]]], "Dual" -> arithmetic["Back"][duals[[c]]]|>, {c, m}]
];

(*
    Summary: Validate one target bundle on every recorded generator.
    Parameters: channels — list of <|"Symmetry", "Embedding", "Dual"|>; p, q, target — exact or numerical
        generator matrices (canonical values, not field elements); mode — "Unitary" or "Dual"; settings —
        arithmeticSettings; exchange — True when the factors are equal and sectors are claimed.
    Options/defaults: None.
    Returns: <|"Covariance", "DualCovariance", "Pairing", "FullRank", "Symmetry", "Unitary" (or Missing)|>
        Booleans, with "Residual" for numerical data.
    Effects: Pure.
    Failures: None (False entries).
    Example: validateCGBundle[normalized, p, p, t, "Unitary", exact, True]["Pairing"] is True.
    Remarks: Exact unitary data are checked factored (factoredValidateCGBundle, cgFactoredValidationPlan.md): each
        channel matrix is s Y with Y in the inputs' field, so the domain need not adjoin the square roots of the unitary
        normalization; the checks are exactly equivalent. A factoring over $CGFactorTimeLimit seconds, or scalars that
        are not exact algebraic numbers, use the direct check. Numerical data use one domain containing all entries
        (validateCGBundleDirect) and report the largest scaled residual. validateCGBundleChecked returns the same with
        the private key "CheckDomain" (the field of the check), which cgVerifyBundle records.
    See also: normalizeCGCopies; ValidateCG; cgFactorChannelMatrix.
*)
validateCGBundle[channels_List, p_List, q_List, target_List, mode_String, settings_Association, exchange_] :=
    KeyDrop[validateCGBundleChecked[channels, p, q, target, mode, settings, exchange], "CheckDomain"];
(* the same checks with the exact domain of the check under "CheckDomain" (cgVerifyBundle records it) *)
(* Factored only for exact unitary bundles (Dual bundles carry no normalization square roots); a factoring that is
   not cheap (over $CGFactorTimeLimit seconds) or whose scalars are not exact algebraic numbers uses the direct check
   (plan review 1, findings 1, 3, 4). *)
$CGFactorTimeLimit = 60;
(* After a passed factored check, a field over the stored values is still built within this time (the cyclotomic hints
   of the CG entries, which readable display uses; the direct check registered them as a side effect, review 2 F6; 10 s, review 3). *)
$CGHintTimeLimit = 10;
validateCGBundleChecked[channels_List, p_List, q_List, target_List, mode_String, settings_Association, exchange_] /;
        mode === "Unitary" && Lookup[settings, "Arithmetic", "Exact"] === "Exact" && channels =!= {} &&
            Precision[{p, q, target, Lookup[channels, "Embedding"], Lookup[channels, "Dual"]}] === Infinity :=
    With[{factors = TimeConstrained[{cgFactorChannelMatrix /@ Lookup[channels, "Embedding"], cgFactorChannelMatrix /@ Lookup[channels, "Dual"]},
            $CGFactorTimeLimit, $Failed]},
        (* a syntactic nonzero that is zero (unsimplified user input) would give infinities: the direct check (review 2 F2) *)
        If[factors === $Failed || !FreeQ[factors, ComplexInfinity | Indeterminate | DirectedInfinity] ||
                !AllTrue[Flatten[Map[#["Scalar"] &, factors, {2}]], TrueQ[Element[#, Algebraics]] &],
            validateCGBundleDirect[channels, p, q, target, mode, settings, exchange],
            With[{result = factoredValidateCGBundle[channels, p, q, target, mode, settings, exchange, factors]},
                If[AllTrue[KeyDrop[result, {"Residual", "CheckDomain"}], TrueQ[#] || MissingQ[#] &],
                    (* display help only: a domain failure (FieldMethodUnavailable is thrown) never becomes a check outcome (review 3) *)
                    Quiet[cgFieldCatch[TimeConstrained[cgArithmetic[{p, q, target, Lookup[channels, "Embedding"], Lookup[channels, "Dual"]}, settings], $CGHintTimeLimit]]]];
                result]]];
validateCGBundleChecked[channels_List, p_List, q_List, target_List, mode_String, settings_Association, exchange_] :=
    validateCGBundleDirect[channels, p, q, target, mode, settings, exchange];
validateCGBundleDirect[channels_List, p_List, q_List, target_List, mode_String, settings_Association, exchange_] := Module[
    {arithmetic, ks, ws, ps, qs, ds, tensor, m = Length[channels], dt, residuals = {}, check, s, results},
    If[channels === {}, Return[<|"Covariance" -> True, "DualCovariance" -> True, "Pairing" -> True, "FullRank" -> True,
        "Symmetry" -> True, "Unitary" -> Missing["Empty"]|>]];
    arithmetic = cgArithmetic[{p, q, target, Lookup[channels, "Embedding"], Lookup[channels, "Dual"]}, settings];
    ks = arithmetic["Embed"][#] & /@ Lookup[channels, "Embedding"];
    ws = arithmetic["Embed"][#] & /@ Lookup[channels, "Dual"];
    {ps, qs, ds} = arithmetic["Embed"] /@ {p, q, target};
    tensor = MapThread[arithmetic["Reduce"][KroneckerProduct[#1, #2]] &, {ps, qs}];
    dt = Length[First[First[ks]]];
    check[x_] := If[arithmetic["Field"] =!= None, fieldZeroQ[arithmetic["Reduce"][x]],
        (AppendTo[residuals, Max[Append[Abs[Flatten[{x}]], 0]]]; Max[Append[Abs[Flatten[{x}]], 0]] <= settings["Tolerance"])];
    s = If[TrueQ[exchange], swapOperator[Length[First[p, {{1}}]]], None];
    results = <|
        "Covariance" -> AllTrue[ks, Function[k, AllTrue[Range[Length[tensor]], check[tensor[[#]] . k - k . ds[[#]]] &]]],
        "DualCovariance" -> AllTrue[ws, Function[w, AllTrue[Range[Length[tensor]], check[w . tensor[[#]] - ds[[#]] . w] &]]],
        "Pairing" -> AllTrue[Flatten[Table[check[ws[[a]] . ks[[b]] - If[a === b, IdentityMatrix[dt], 0]], {a, m}, {b, m}]], TrueQ],
        "FullRank" -> If[arithmetic["Field"] =!= None, fieldRank[arithmetic["Field"], Join @@ (Transpose /@ ks)],
                MatrixRank[Join @@ (Transpose /@ ks), Tolerance -> settings["Tolerance"]]] === m dt,
        "Symmetry" -> If[s === None, AllTrue[Lookup[channels, "Symmetry"], # === "Unspecified" &],
            AllTrue[Range[m], With[{sign = Switch[channels[[#, "Symmetry"]], "Symmetric", 1, "Antisymmetric", -1, _, 0]},
                sign =!= 0 && check[s . ks[[#]] - sign ks[[#]]] && check[ws[[#]] . s - sign ws[[#]]]] &]],
        "Unitary" -> If[mode === "Unitary", AllTrue[Range[m], check[ws[[#]] - arithmetic["Adjoint"][ks[[#]]]] &], Missing["Dual"]]|>;
    If[arithmetic["Field"] === None, results["Residual"] = Max[Append[residuals, 0]]];
    results
];

(*
    Summary: A channel matrix as s Y: s its first nonzero entry (reading order), Y = m / s entrywise RootReduced
        (cgFactoredValidationPlan.md 2.1).
    Parameters: m — exact matrix (canonical values).
    Options/defaults: None.
    Returns: <|"Scalar" -> s, "Y" -> Y|>; an all-zero matrix is <|"Scalar" -> 1, "Y" -> m|>.
    Effects: Pure.
    Failures: None.
    Example: cgFactorChannelMatrix[{{Sqrt[2]}, {Sqrt[2] I}}] is <|"Scalar" -> Sqrt[2], "Y" -> {{1}, {I}}|>.
    Remarks: s Y equals m exactly (RootReduce is an exact canonical form), and s is nonzero.
    See also: factoredValidateCGBundle.
*)
cgFactorChannelMatrix[m_] := With[{s = SelectFirst[Flatten[m], # =!= 0 &, 0]},
    If[s === 0, <|"Scalar" -> 1, "Y" -> m|>, <|"Scalar" -> s, "Y" -> Map[RootReduce, m / s, {2}]|>]];

(*
    Summary: Exact validation of one target bundle on factored channels (cgFactoredValidationPlan.md 2.2).
    Parameters: As validateCGBundle (exact unitary data, at least one channel); factors — {kets, duals} from
        cgFactorChannelMatrix (Automatic: computed here).
    Options/defaults: None.
    Returns: As validateCGBundle, with "CheckDomain" -> the check's exact domain (or None).
    Effects: Pure.
    Failures: None (False entries).
    Example: for a unitary T' 3 x 3 bundle it agrees with validateCGBundleDirect.
    Remarks: With K_a = s_a Y_a and W_a = t_a Z_a (s_a, t_a nonzero): Covariance, DualCovariance, Symmetry and the
        off-diagonal Pairing are homogeneous, so they hold for K_a, W_a exactly when they hold for Y_a, Z_a; the diagonal
        Pairing is c_a Z_a Y_a = I with c_a = t_a s_a; Unitary W_a = K_a^dagger is r_a Z_a = Y_a^dagger with
        r_a = t_a / conj(s_a); FullRank is unchanged by nonzero block scaling. Only c_a and r_a join the inputs' field.
    See also: validateCGBundleDirect; cgFactorChannelMatrix.
*)
factoredValidateCGBundle[channels_List, p_List, q_List, target_List, mode_String, settings_Association, exchange_,
    factors_ : Automatic] := Module[
    {fk, fw, c, r, arithmetic, ys, zs, cs, rs, ps, qs, ds, tensor, m = Length[channels], dt, residuals = {}, check, s, results},
    {fk, fw} = If[factors === Automatic, {cgFactorChannelMatrix /@ Lookup[channels, "Embedding"], cgFactorChannelMatrix /@ Lookup[channels, "Dual"]}, factors];
    c = MapThread[RootReduce[#1["Scalar"] #2["Scalar"]] &, {fw, fk}];
    r = MapThread[RootReduce[#1["Scalar"] / Conjugate[#2["Scalar"]]] &, {fw, fk}];
    arithmetic = cgArithmetic[{p, q, target, Lookup[fk, "Y"], Lookup[fw, "Y"], c, r}, settings];
    ys = arithmetic["Embed"] /@ Lookup[fk, "Y"];
    zs = arithmetic["Embed"] /@ Lookup[fw, "Y"];
    cs = arithmetic["Embed"][c]; rs = arithmetic["Embed"][r];
    {ps, qs, ds} = arithmetic["Embed"] /@ {p, q, target};
    tensor = MapThread[arithmetic["Reduce"][KroneckerProduct[#1, #2]] &, {ps, qs}];
    dt = Length[First[First[ys]]];
    check[x_] := If[arithmetic["Field"] =!= None, fieldZeroQ[arithmetic["Reduce"][x]],
        (AppendTo[residuals, Max[Append[Abs[Flatten[{x}]], 0]]]; Max[Append[Abs[Flatten[{x}]], 0]] <= settings["Tolerance"])];
    s = If[TrueQ[exchange], swapOperator[Length[First[p, {{1}}]]], None];
    results = <|
        "Covariance" -> AllTrue[ys, Function[y, AllTrue[Range[Length[tensor]], check[tensor[[#]] . y - y . ds[[#]]] &]]],
        "DualCovariance" -> AllTrue[zs, Function[z, AllTrue[Range[Length[tensor]], check[z . tensor[[#]] - ds[[#]] . z] &]]],
        "Pairing" -> AllTrue[Flatten[Table[check[If[a === b, cs[[a]] zs[[a]] . ys[[a]] - IdentityMatrix[dt], zs[[a]] . ys[[b]]]], {a, m}, {b, m}]], TrueQ],
        "FullRank" -> If[arithmetic["Field"] =!= None, fieldRank[arithmetic["Field"], Join @@ (Transpose /@ ys)],
                MatrixRank[Join @@ (Transpose /@ ys), Tolerance -> settings["Tolerance"]]] === m dt,
        "Symmetry" -> If[s === None, AllTrue[Lookup[channels, "Symmetry"], # === "Unspecified" &],
            AllTrue[Range[m], With[{sign = Switch[channels[[#, "Symmetry"]], "Symmetric", 1, "Antisymmetric", -1, _, 0]},
                sign =!= 0 && check[s . ys[[#]] - sign ys[[#]]] && check[zs[[#]] . s - sign zs[[#]]]] &]],
        "Unitary" -> If[mode === "Unitary", AllTrue[Range[m], check[rs[[#]] zs[[#]] - arithmetic["Adjoint"][ys[[#]]]] &], Missing["Dual"]]|>;
    If[arithmetic["Field"] === None, results["Residual"] = Max[Append[residuals, 0]]];
    Join[results, <|"CheckDomain" -> arithmetic["Field"]|>]
];

(*
    Summary: Exact validation of a freshly normalized unitary bundle on the field form it was made from
        (cgFactoredValidationPlan.md 7).
    Parameters: channels — normalized channels (without FieldForm); forms — their FieldForm records <|"Y" -> matrix in
        the field of arithmetic, "Norm" -> n (the LDL pivot, a field element)|> (K = Y / Sqrt[n], W = K^dagger, by normalizeCGCopies); p, q, target —
        canonical generator matrices; arithmetic — the domain the route and the normalization used; exchange.
    Options/defaults: None.
    Returns: As validateCGBundle, with "CheckDomain" -> the domain's field.
    Effects: Pure.
    Failures: None (False entries).
    Example: for a unitary T' 3 x 3 bundle it agrees with validateCGBundleDirect.
    Remarks: Each check on K_a = Y_a / Sqrt[n_a] (n_a > 0) and W_a = K_a^dagger is the same check on Y_a and
        Z_a = Y_a^dagger in the field: Covariance, DualCovariance, Symmetry and the off-diagonal Pairing are homogeneous;
        the diagonal Pairing is Z_a Y_a / n_a = I; FullRank is unchanged by nonzero scaling. W = K^dagger holds by
        construction (normalizeCGCopies). Used only where the field form was computed in this kernel (finishCGBundle);
        stored values are checked by validateCGBundle.
    See also: factoredValidateCGBundle; normalizeCGCopies; finishCGBundle.
*)
fieldFormValidateCGBundle[channels_List, forms_List, p_List, q_List, target_List, arithmetic_Association, exchange_] := Module[
    {ys, zs, ns, ps, qs, ds, tensor, m = Length[channels], dt, check, s, reduce = arithmetic["Reduce"]},
    ys = Lookup[forms, "Y"]; zs = arithmetic["Adjoint"] /@ ys; ns = Lookup[forms, "Norm"];
    {ps, qs, ds} = arithmetic["Embed"] /@ {p, q, target};
    tensor = MapThread[reduce[KroneckerProduct[#1, #2]] &, {ps, qs}];
    dt = Length[First[First[ys]]];
    check[x_] := fieldZeroQ[reduce[x]];
    s = If[TrueQ[exchange], swapOperator[Length[First[p, {{1}}]]], None];
    <|"Covariance" -> AllTrue[ys, Function[y, AllTrue[Range[Length[tensor]], check[tensor[[#]] . y - y . ds[[#]]] &]]],
        "DualCovariance" -> AllTrue[zs, Function[z, AllTrue[Range[Length[tensor]], check[z . tensor[[#]] - ds[[#]] . z] &]]],
        "Pairing" -> AllTrue[Flatten[Table[check[If[a === b, (1 / ns[[a]]) zs[[a]] . ys[[a]] - IdentityMatrix[dt], zs[[a]] . ys[[b]]]], {a, m}, {b, m}]], TrueQ],
        "FullRank" -> fieldRank[arithmetic["Field"], Join @@ (Transpose /@ ys)] === m dt,
        "Symmetry" -> If[s === None, AllTrue[Lookup[channels, "Symmetry"], # === "Unspecified" &],
            AllTrue[Range[m], With[{sign = Switch[channels[[#, "Symmetry"]], "Symmetric", 1, "Antisymmetric", -1, _, 0]},
                sign =!= 0 && check[s . ys[[#]] - sign ys[[#]]] && check[zs[[#]] . s - sign zs[[#]]]] &]],
        "Unitary" -> True, "CheckDomain" -> arithmetic["Field"]|>
];

(*
    Summary: Check one target bundle at the verification level the settings carry (methodOptionsPlan.md 1.4).
    Parameters: channels, p, q, target, mode, exchange — as validateCGBundle; settings — cgCheckSettings association
        ("Verification" Automatic | "Exact" | "Numerical" | None); unitary — whether a Unitary bundle must pass
        W = K^dagger (False for exact-witness output, as before).
    Options/defaults: unitary True.
    Returns: <|"Passed" -> Boolean, "Validation" -> validateCGBundle result (<|"Skipped" -> True|> for None),
        "VerificationStatus" -> "Exact" | "Numerical" | "Unverified", "ValidationDomain" -> domainSummary of the check
        (Missing["NotChecked"] for None)|>.
    Effects: Pure (exactField memoizes; the domain summary reuses the check's memoized domain).
    Failures: An explicit FieldMethod without an available domain throws FieldMethodUnavailable (cgArithmetic).
    Example: cgVerifyBundle[c, p, q, t, "Dual", <|..., "Verification" -> None|>, False]["VerificationStatus"] is "Unverified".
    Remarks (fieldForm, optional 9th argument, cgFactoredValidationPlan.md 7): <|"Forms" -> the channels' field forms,
        "Arithmetic" -> the route's domain|> from finishCGBundle for a fresh exact unitary bundle; the check then runs on
        the field forms in that domain (fieldFormValidateCGBundle; "Unitary" holds by construction there). None: the
        stored values are checked (validateCGBundleChecked).
    Remarks: Automatic and "Exact" run today's checks in the settings' arithmetic. "Numerical" on exact data runs the
        same checks on N[] of every matrix at the settings' "CheckPrecision" (the WorkingPrecision option) (residuals recorded). None checks nothing.
    See also: validateCGBundle; cgEntryStatus.
*)
cgVerifyBundle[channels_List, p_List, q_List, target_List, mode_String, settings_Association, exchange_, unitary_ : True, fieldForm_ : None] := Module[
    {level = Lookup[settings, "Verification", Automatic], exact = settings["Arithmetic"] === "Exact", check, validation, domain, status},
    If[level === None, Return[<|"Passed" -> True, "Validation" -> <|"Skipped" -> True|>, "VerificationStatus" -> "Unverified",
        "ValidationDomain" -> Missing["NotChecked"]|>]];
    If[level === "Exact" && !exact, Return[<|"Passed" -> False, "Validation" -> <|"Inapplicable" -> "Exact checks of numerical data"|>,
        "VerificationStatus" -> "Unverified", "ValidationDomain" -> Missing["NotChecked"]|>]];
    If[level === "Numerical" && exact,
        With[{digits = Max[16, Lookup[settings, "CheckPrecision", 50]]},
            check = arithmeticSettings["Numerical", digits, Automatic, Infinity];
            validation = validateCGBundle[Map[Join[#, <|"Embedding" -> N[#["Embedding"], digits], "Dual" -> N[#["Dual"], digits]|>] &, channels],
                N[p, digits], N[q, digits], N[target, digits], mode, check, exchange]];
        domain = <|"Kind" -> "Numerical"|>; status = "Numerical",
        validation = If[AssociationQ[fieldForm] && exact && mode === "Unitary" && channels =!= {},
            (* a fresh unitary bundle: its field form, checked in the route's own domain (cgFactoredValidationPlan.md 7) *)
            With[{result = fieldFormValidateCGBundle[channels, fieldForm["Forms"], p, q, target, fieldForm["Arithmetic"], exchange]},
                (* display help, as after a factored check (review 3: never a check outcome) *)
                If[AllTrue[KeyDrop[result, "CheckDomain"], TrueQ],
                    Quiet[cgFieldCatch[TimeConstrained[cgArithmetic[{p, q, target, Lookup[channels, "Embedding"], Lookup[channels, "Dual"]}, settings], $CGHintTimeLimit]]]];
                result],
            validateCGBundleChecked[channels, p, q, target, mode, settings, exchange]];
        (* the domain of the check itself (the factored check's, cgFactoredValidationPlan.md 2.3) *)
        domain = If[exact && channels =!= {},
            domainSummary[If[KeyExistsQ[validation, "CheckDomain"], validation["CheckDomain"],
                cgArithmetic[{p, q, target, Lookup[channels, "Embedding"], Lookup[channels, "Dual"]}, settings]["Field"]]],
            If[exact, Missing["Empty"], <|"Kind" -> "Numerical"|>]];
        validation = KeyDrop[validation, "CheckDomain"];
        status = If[exact, "Exact", "Numerical"]];
    <|"Passed" -> AllTrue[KeyDrop[validation, {"Residual", "Unitary"}], TrueQ] && (!TrueQ[unitary] || mode =!= "Unitary" || TrueQ[validation["Unitary"]]),
        "Validation" -> validation, "VerificationStatus" -> status, "ValidationDomain" -> domain|>
];

(*
    Summary: The verification status of a CG bundle or store entry, its order, and the level a call requires.
    Parameters: entry — bundle or stored entry; statuses — list of statuses; level — Verification value; arithmetic.
    Options/defaults: None.
    Returns: verificationStatusQ: True for "Exact", "Numerical" or "Unverified"; cgEntryStatus: "Exact" | "Numerical" | "Unverified" (an entry made before statuses existed: "Exact" for exact
        arithmetic, "Numerical" for numerical; migration of methodOptionsPlan.md 1.4); cgStatusRank: 0, 1, 2;
        cgWeakestStatus: the weakest of the list ("Exact" for an empty list); cgRequiredStatus: the status a call at that
        level requires.
    Effects: Pure.
    Failures: None.
    Example: cgWeakestStatus[{"Exact", "Unverified"}] is "Unverified".
    See also: cgVerifyBundle; lookupCG.
*)
cgEntryStatus[entry_Association] := Lookup[entry, "VerificationStatus",
    If[Lookup[entry, "Arithmetic", "Exact"] === "Numerical", "Numerical", "Exact"]];
cgEntryStatus[_] := "Unverified";
cgStatusRank[status_] := Lookup[<|"Unverified" -> 0, "Numerical" -> 1, "Exact" -> 2|>, status, 0];
cgWeakestStatus[statuses_List] := If[statuses === {}, "Exact", First[SortBy[statuses, cgStatusRank]]];
(* a recorded status must be one of the three statuses (readers refuse anything else, methodOptionsPlan.md C3) *)
verificationStatusQ[status_] := MemberQ[{"Exact", "Numerical", "Unverified"}, status];
cgRequiredStatus[level_, arithmetic_] := Switch[level, None, "Unverified", "Numerical", "Numerical", "Exact", "Exact",
    _, If[arithmetic === "Numerical", "Numerical", "Exact"]];

(*
    Summary: Assemble target bundles into the embedding or dual matrix.
    Parameters: bundles — list of channel lists (in channel order); side — "Embedding" or "Dual".
    Options/defaults: None.
    Returns: Embedding: N by (sum of channel dimensions) (blocks side by side); Dual: stacked rows.
    Effects: Pure.
    Failures: None; an empty selection gives {} .
    Example: a full-pair assembly is square and the dual is its inverse.
    See also: CGMatrix.
*)
assembleCG[bundles_List, side_String] := Module[{channels = Flatten[bundles, 1]},
    If[channels === {}, Return[{}]];
    If[side === "Embedding", Join[Sequence @@ (Transpose /@ Lookup[channels, "Embedding"])] // Transpose,
        Join @@ Lookup[channels, "Dual"]]
];

(*
    Summary: The reverse-pair bundle from a verified tensor flip.
    Parameters: channels — validated channels of (p, q); dims — {dp, dq}.
    Options/defaults: None.
    Returns: Channels of (q, p): K' = F K and W' = W F with F the flip a_i b_j -> b_j a_i; symmetry tags and
        copy order preserved.
    Effects: Pure.
    Failures: None.
    Example: flipping twice returns the original channels.
    Remarks: F maps P (x) Q to Q (x) P (F (P kron Q) F^-1 = Q kron P), so covariance and pairing transfer; the
        caller validates the flipped bundle like any other.
    See also: swapOperator.
*)
flipCG[channels_List, {dp_Integer, dq_Integer}] := Module[{f},
    f = Normal[SparseArray[Flatten[Table[{(j - 1) dp + i, (i - 1) dq + j} -> 1, {i, dp}, {j, dq}]], {dp dq, dp dq}]];
    Map[Join[#, <|"Embedding" -> f . #["Embedding"], "Dual" -> #["Dual"] . Transpose[f]|>] &, channels]
];

True
