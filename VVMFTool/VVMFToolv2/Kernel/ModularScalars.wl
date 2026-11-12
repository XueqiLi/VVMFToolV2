(*
    :Title: Scalar modular ingredients, their exact q-series and the modular derivative
    :Context: VVMFTool`Private`
    :Summary: Inert nodes for Eta, E2, E4, E6, Delta, j, K and the generalized hypergeometric function of K; exact series
        with valuation-aware required orders (no blanket expansion to a global order); series of whole expression trees;
        the symbolic derivative q d/dq on trees and the modular derivative D_k.
    :Responsibilities: scalarRecipe, hypergeometricRecipe, scalarNodeViolations, hypergeometricSingularity, scalarSeries,
        eisensteinSeries, etaSeries, hypergeometricSeries, seriesOrderRequirements, provableValuationBound, treeSeries, differentiateScalarRecipe,
        cleanScalarSeriesCache; ScalarModularExpression, HypergeometricK, ScalarQSeries, ModularDerivativeExpression.
    :Dependencies: ModularSeries.wl (jets, QExpansionData); ModularFormObjects.wl (FormVariable, FormParameter).
    :See Also: VVMFArch/step7Plan.md (scalar functions and series); local MLDE.tex (D_k, K = 1728/j).
*)

$ScalarModularNames = {"Eta", "E2", "E4", "E6", "Delta", "j", "K"};
If[!AssociationQ[$ScalarSeriesCache], $ScalarSeriesCache = <||>];

(*
    Summary: Inert scalar-ingredient nodes.
    Parameters: name — ingredient name; a, b — exact parameter lists; var — FormVariable or a user symbol; coordinate —
        "q" or "tau".
    Options/defaults: None.
    Returns: ModularScalarNode[name, var, coordinate] or HypergeometricKNode[a, b, var, coordinate], or Failure.
    Effects: Pure.
    Failures: UnsupportedScalar (unknown name); InvalidOption (coordinate); SingularHypergeometric (a denominator
        parameter is a nonpositive integer not cancelled by an earlier terminating numerator); InvalidInput.
    Example: scalarRecipe["E4", FormVariable["q"], "q"] is ModularScalarNode["E4", FormVariable["q"], "q"].
    Remarks: A FormVariable argument fixes the coordinate. The nodes never evaluate.
    See also: ScalarModularExpression; HypergeometricK.
*)
scalarRecipe[name_String, var_, coordinate_String] := Which[
    !MemberQ[$ScalarModularNames, name], makeFailure["UnsupportedScalar", "Supported scalar ingredients are Eta, E2, E4, E6, Delta, j and K.", <|"Name" -> name|>],
    !MemberQ[{"q", "tau"}, coordinate], makeFailure["InvalidOption", "Coordinate must be \"q\" or \"tau\".", <|"Options" -> {Coordinate}|>],
    MatchQ[var, FormVariable[_String]] && First[var] =!= coordinate, makeFailure["InvalidOption", "The coordinate differs from the definition's variable.", <|"Options" -> {Coordinate}|>],
    True, ModularScalarNode[name, var, coordinate]];
hypergeometricRecipe[a_List, b_List, var_, coordinate_String] := Which[
    !AllTrue[Join[a, b], MatchQ[#, _Integer | _Rational] &], makeFailure["InvalidInput", "Hypergeometric parameters must be exact rationals."],
    !MemberQ[{"q", "tau"}, coordinate], makeFailure["InvalidOption", "Coordinate must be \"q\" or \"tau\".", <|"Options" -> {Coordinate}|>],
    MatchQ[var, FormVariable[_String]] && First[var] =!= coordinate, makeFailure["InvalidOption", "The coordinate differs from the definition's variable.", <|"Options" -> {Coordinate}|>],
    hypergeometricSingularity[a, b] =!= None, makeFailure["SingularHypergeometric", "A denominator parameter is a nonpositive integer that the series reaches.",
        <|"Parameters" -> {a, b}, "Denominator" -> hypergeometricSingularity[a, b]|>],
    True, HypergeometricKNode[a, b, var, coordinate]];

(*
    Summary: The first denominator parameter that makes the hypergeometric series singular.
    Parameters: a, b — exact numerator and denominator parameters.
    Options/defaults: None.
    Returns: The offending denominator parameter, or None.
    Effects: Pure.
    Failures: None.
    Example: hypergeometricSingularity[{1}, {-2}] is -2; hypergeometricSingularity[{-1}, {-2}] is None (the series stops
        at m = 1, before (-2)_m vanishes at m = 3).
    Remarks: (b)_m first vanishes at m = 1 - b for a nonpositive integer b; the series stops after m = -a* for the
        nonpositive integer numerator a* closest to zero, so it is regular exactly when a* >= b.
    See also: hypergeometricRecipe.
*)
hypergeometricSingularity[a_List, b_List] := Module[{stop = Max[Append[Select[a, IntegerQ[#] && # <= 0 &], -Infinity]]},
    SelectFirst[Select[b, IntegerQ[#] && # <= 0 &], !(stop >= #) &, None]];

(*
    Summary: Malformed scalar-ingredient nodes in a definition tree.
    Parameters: node — ModularScalarNode or HypergeometricKNode.
    Options/defaults: None.
    Returns: {} for a valid node (argument a FormVariable of its coordinate), else {node}.
    Effects: Pure.
    Failures: None.
    Example: scalarNodeViolations[ModularScalarNode["E4", FormVariable["q"], "q"]] is {}.
    See also: definitionTreeViolations.
*)
scalarNodeViolations[node_] := If[Which[
    MatchQ[node, ModularScalarNode[_String, FormVariable[_String], _String]], MemberQ[$ScalarModularNames, node[[1]]] && node[[2, 1]] === node[[3]],
    MatchQ[node, HypergeometricKNode[_List, _List, FormVariable[_String], _String]],
        AllTrue[Join[node[[1]], node[[2]]], MatchQ[#, _Integer | _Rational] &] && node[[3, 1]] === node[[4]] && hypergeometricSingularity[node[[1]], node[[2]]] === None,
    True, False], {}, {node}];

Options[ScalarModularExpression] = {Coordinate -> "q"};
Options[HypergeometricK] = {Coordinate -> "q"};

(*
    Summary: Public constructors of the inert scalar ingredients.
    Status: Alpha.
    Signatures: ScalarModularExpression[name, z, opts]; HypergeometricK[a, b, z, opts].
    Parameters: name — "Eta", "E2", "E4", "E6", "Delta", "j" or "K"; a, b — exact parameter lists; z — the variable
        (a symbol, or the definition's FormVariable).
    Options/defaults: Coordinate -> "q" ("tau" makes z the upper-half-plane coordinate).
    Returns: Inert node, or Failure.
    Effects: Pure.
    Failures: UnsupportedScalar; SingularHypergeometric; InvalidOption; InvalidInput.
    Example: ScalarQSeries[ScalarModularExpression["E4", q], q, 3] is 1 + 240 q + 2160 q^2 + O(q^3).
    Remarks: HypergeometricK[a, b, z] is Sum_m Product (a)_m / Product (b)_m K(z)^m / m! with K = 1728/j (v1's FK). The
        nodes may occur in modular-form definitions; they never multiply form objects.
    See also: ScalarQSeries; ModularDerivativeExpression.
*)
ScalarModularExpression[name_String, z_, options : OptionsPattern[]] := Module[{effective},
    effective = resolveOperationOptions[ScalarModularExpression, "ScalarModularExpression", {options}]; If[FailureQ[effective], Return[effective]];
    If[!MatchQ[z, _Symbol | FormVariable[_String]], Return[makeFailure["InvalidInput", "The variable must be a symbol."]]];
    scalarRecipe[name, z, If[MatchQ[z, FormVariable[_String]], First[z], effective[Coordinate]]]];
ScalarModularExpression[___] := makeFailure["InvalidInput", "ScalarModularExpression expects a name, a variable and options."];
HypergeometricK[a_List, b_List, z_, options : OptionsPattern[]] := Module[{effective},
    effective = resolveOperationOptions[HypergeometricK, "HypergeometricK", {options}]; If[FailureQ[effective], Return[effective]];
    If[!MatchQ[z, _Symbol | FormVariable[_String]], Return[makeFailure["InvalidInput", "The variable must be a symbol."]]];
    hypergeometricRecipe[a, b, z, If[MatchQ[z, FormVariable[_String]], First[z], effective[Coordinate]]]];
HypergeometricK[___] := makeFailure["InvalidInput", "HypergeometricK expects parameter lists, a variable and options."];

(*
    Summary: Exact series of the scalar ingredients.
    Parameters: name — ingredient; requested — exact rational cutoff (exponents below it are returned; the series is
        computed to at least 2 and truncated).
    Options/defaults: None.
    Returns: Jet known below the cutoff, or Failure.
    Effects: Reads and extends $ScalarSeriesCache (immutable jets keyed by name; a longer prefix serves shorter requests).
    Failures: InvalidSeries.
    Example: scalarSeries["E4", 3] has Terms <|0 -> 1, 1 -> 240, 2 -> 2160|>.
    Remarks: E2/E4/E6 from divisor sums; Eta = q^(1/24) times Euler's pentagonal series; Delta = (E4^3 - E6^2)/1728;
        j = E4^3/Delta (q^-1 leading) and K = 1728 Delta/E4^3, each factor requested only to the order it can affect.
    See also: treeSeries; eisensteinSeries; etaSeries.
*)
scalarSeries[name_String, requested_] := Module[{cached = Lookup[$ScalarSeriesCache, name, None], jet, cutoff = Max[requested, 2]},
    (* Every ingredient is computed to at least cutoff 2 (so products and reciprocals see a leading term) and truncated. *)
    If[AssociationQ[cached] && cached["Cutoff"] >= requested, Return[jetTruncate[cached, requested]]];
    jet = Switch[name,
        "E2", eisensteinSeries[1, -24, cutoff], "E4", eisensteinSeries[3, 240, cutoff], "E6", eisensteinSeries[5, -504, cutoff],
        "Eta", etaSeries[cutoff],
        "Delta", jetScale[jetAdd[jetMultiply[jetMultiply[scalarSeries["E4", cutoff], scalarSeries["E4", cutoff], cutoff], scalarSeries["E4", cutoff], cutoff],
            jetScale[jetMultiply[scalarSeries["E6", cutoff], scalarSeries["E6", cutoff], cutoff], -1]], 1/1728],
        "j", jetMultiply[jetRationalPower[scalarSeries["E4", cutoff + 1], 3]["Series"], jetReciprocal[scalarSeries["Delta", cutoff + 2]], cutoff],
        "K", jetScale[jetMultiply[scalarSeries["Delta", cutoff], jetReciprocal[jetRationalPower[scalarSeries["E4", cutoff - 1], 3]["Series"]], cutoff], 1728],
        _, Return[makeFailure["UnsupportedScalar", "Unknown scalar ingredient.", <|"Name" -> name|>]]];
    If[FailureQ[jet], Return[jet]];
    jet = jetTruncate[jet, cutoff];
    If[jet["Cutoff"] =!= cutoff && !(cutoff === Infinity), Return[makeFailure["InvalidSeries", "An ingredient series did not reach the requested order.", <|"Name" -> name|>]]];
    If[!AssociationQ[cached] || cached["Cutoff"] < jet["Cutoff"], AssociateTo[$ScalarSeriesCache, name -> jet]];
    jetTruncate[jet, requested]
];
eisensteinSeries[power_Integer, factor_Integer, cutoff_] := makeJet[Join[<|0 -> 1|>,
    Association[Table[n -> factor DivisorSigma[power, n], {n, 1, Ceiling[cutoff] - 1}]]], cutoff];
etaSeries[cutoff_] := makeJet[Association[Select[Flatten[Table[{1/24 + k (3 k - 1)/2 -> (-1)^k, 1/24 + k (3 k + 1)/2 -> (-1)^k},
    {k, 0, Ceiling[Sqrt[2 Max[cutoff, 1]]] + 1}]], First[#] < cutoff &]], cutoff];

(*
    Summary: The series of a generalized hypergeometric function of K.
    Parameters: a, b — parameters; cutoff — requested cutoff.
    Options/defaults: None.
    Returns: Jet known below the cutoff (K has valuation one, so the terms K^m with m below the cutoff suffice; a
        terminating series stops at its last nonzero term), or Failure.
    Effects: Pure (uses the K series cache).
    Failures: SingularHypergeometric.
    Example: hypergeometricSeries[{1/12, 5/12}, {1/2}, 2] is 1 + 1/12 5/12 2 1728 q... per the definition.
    See also: hypergeometricRecipe; treeSeries.
*)
hypergeometricSeries[a_List, b_List, cutoff_] := Module[{k, sum, power, coefficient = 1, m = 0, stop},
    If[hypergeometricSingularity[a, b] =!= None, Return[makeFailure["SingularHypergeometric", "The hypergeometric series is singular.", <|"Parameters" -> {a, b}|>]]];
    k = scalarSeries["K", cutoff]; If[FailureQ[k], Return[k]];
    stop = Max[Append[Select[a, IntegerQ[#] && # <= 0 &], -Infinity]];
    sum = makeJet[<|0 -> 1|>, cutoff]; power = makeJet[<|0 -> 1|>, Infinity];
    While[m + 1 < cutoff && !(stop > -Infinity && m + 1 > -stop),
        coefficient = coefficient (Times @@ (a + m))/((Times @@ (b + m)) (m + 1)); m++;
        power = jetMultiply[power, k, cutoff]; sum = jetAdd[sum, jetScale[power, coefficient]]];
    jetTruncate[sum, cutoff]
];

(*
    Summary: A lower bound for the valuation of an expression tree (the input orders a series needs).
    Parameters: e — tree in FormVariable["q"], FormParameter atoms, constants and scalar nodes.
    Options/defaults: None.
    Returns: Exact rational lower bound (Infinity for an exact zero), or Failure.
    Effects: Pure.
    Failures: NotAQSeries (a variable that is not a power of q, a non-rational power of a non-constant base).
    Example: seriesOrderRequirements[ModularScalarNode["j", FormVariable["q"], "q"]] is -1.
    Remarks: Constants 0; q^r -> r; Eta 1/24; Delta and K 1; j -1; E2, E4, E6 and hypergeometric nodes 0; sums take the
        minimum, products the sum, powers r v. Used to request each factor only to the order it can affect.
    See also: treeSeries.
*)
seriesOrderRequirements[e_] := Which[
    numericConstantQ[e] || MatchQ[e, _FormParameter], If[TrueQ[e == 0], Infinity, 0],
    MatchQ[e, FormVariable["q"]], 1,
    MatchQ[e, ModularScalarNode[_, _, _]], Switch[e[[1]], "Eta", 1/24, "Delta" | "K", 1, "j", -1, _, 0],
    MatchQ[e, _HypergeometricKNode], 0,
    MatchQ[e, Power[E, _]] && !FreeQ[e, FormVariable["tau"]], With[{r = Simplify[e[[2]]/(2 Pi I FormVariable["tau"])]}, If[MatchQ[r, _Integer | _Rational], r, 0]],
    MatchQ[e, _Plus], Min[seriesOrderRequirements /@ (List @@ e)],
    MatchQ[e, _Times], Total[seriesOrderRequirements /@ (List @@ e)],
    MatchQ[e, Power[_, _Integer | _Rational]], e[[2]] seriesOrderRequirements[e[[1]]],
    MatchQ[e, Power[_, _]] && FreeQ[e[[1]], FormVariable | ModularScalarNode | HypergeometricKNode], 0,
    True, 0];

(*
    Summary: A provable lower bound of the valuation of an expression tree.
    Parameters: e — tree as for seriesOrderRequirements.
    Options/defaults: None.
    Returns: Exact rational lower bound, Infinity for an exact zero, or -Infinity when nothing is provable.
    Effects: Pure.
    Failures: None.
    Example: provableValuationBound[(E4 - E6)^-1] is -Infinity (the sum may cancel: its valuation is 1, not 0), while
        seriesOrderRequirements gives 0; provableValuationBound[K^(1/12)] is 1/12.
    Remarks: seriesOrderRequirements sizes requests (a too-small request is caught by the cutoff check); only this bound may
        raise a product's cutoff (jetMultiply hints). A negative power is bounded only when its base contains no sum, so
        the base's bound is its exact valuation (ingredients, q, constants and hypergeometric nodes have exact leading
        terms).
    See also: seriesOrderRequirements; treeSeries; jetMultiply.
*)
provableValuationBound[e_] := Which[
    MatchQ[e, Power[_, _Integer | _Rational]] && !MatchQ[e, Power[E, _]],
        Which[e[[2]] < 0, If[FreeQ[e[[1]], Plus], e[[2]] seriesOrderRequirements[e[[1]]], -Infinity],
            e[[2]] == 0, 0,
            True, With[{b = provableValuationBound[e[[1]]]}, If[b === -Infinity, -Infinity, e[[2]] b]]],
    MatchQ[e, _Plus], Min[provableValuationBound /@ (List @@ e)],
    MatchQ[e, _Times], With[{b = provableValuationBound /@ (List @@ e)}, Which[MemberQ[b, Infinity], Infinity, MemberQ[b, -Infinity], -Infinity, True, Total[b]]],
    True, seriesOrderRequirements[e]];

(*
    Summary: The series of an expression tree to a requested cutoff.
    Parameters: e — tree (q coordinate: FormVariable["q"]; tau coordinate: Exp[2 Pi I r FormVariable["tau"]] factors);
        cutoff — exact rational.
    Options/defaults: None.
    Returns: Jet known below the cutoff (or exactly, for a finite expression), or Failure.
    Effects: Extends the scalar cache.
    Failures: NotAQSeries (tau not under Exp[2 Pi I r tau]; non-rational powers of a series; unsupported heads);
        DivisionByZero; SingularHypergeometric.
    Example: treeSeries[2 ModularScalarNode["E4", FormVariable["q"], "q"], 2] is 2 + 480 q + O(q^2).
    Remarks: A product requests each factor to the cutoff minus the other factors' valuation bounds (again with slack
        when a cancellation leaves it short); a power r of a
        series with valuation v requests c - r v + v (and at least v + 1, re-requested from the actual valuation after a
        cancellation); a negative power uses the reciprocal (proved nonzero leading term).
    See also: ScalarQSeries; expandForm.
*)
treeSeries[e_, cutoff_] := Module[{parts, bounds, proved, total, base, product},
    Which[
        numericConstantQ[e] || MatchQ[e, _FormParameter], jetConstant[e],
        MatchQ[e, FormVariable["q"]], jetMonomial[1, 1],
        MatchQ[e, Power[E, _]] && !FreeQ[e, FormVariable["tau"]],
            With[{r = Simplify[e[[2]]/(2 Pi I FormVariable["tau"])]}, If[MatchQ[r, _Integer | _Rational], jetMonomial[1, r],
                makeFailure["NotAQSeries", "In the tau coordinate the variable may occur only as Exp[2 Pi I r tau] with rational r.", <|"Expression" -> e|>]]],
        MatchQ[e, ModularScalarNode[_, _, _]], scalarSeries[e[[1]], cutoff],
        MatchQ[e, _HypergeometricKNode], hypergeometricSeries[e[[1]], e[[2]], cutoff],
        MatchQ[e, _Plus], Module[{terms = treeSeries[#, cutoff] & /@ (List @@ e)}, If[AnyTrue[terms, FailureQ], FirstCase[terms, _Failure], jetTruncate[jetAdd[terms], cutoff]]],
        MatchQ[e, _Times], parts = List @@ e; bounds = seriesOrderRequirements /@ parts; total = Total[bounds];
            If[total === Infinity, Return[makeJet[<||>, Infinity]]];
            proved = provableValuationBound /@ parts;
            (* The partial product of the first k factors is needed below target - (bounds of the remaining factors). When a
               factor's valuation exceeds its bound (cancellation), the product falls short; the factors are then
               requested again with that much slack (at most three times) and the result truncated to the cutoff. *)
            product[target_] := Fold[Function[{acc, k}, If[FailureQ[acc], acc,
                With[{f = treeSeries[parts[[k]], target - (total - bounds[[k]])]}, If[FailureQ[f], f,
                    (* Provable tree bounds keep a truncated (possibly empty) partial product's valuation known; request
                       sizes may use the plain bounds, cutoffs only provable ones. *)
                    jetMultiply[acc, f, target - Total[bounds[[k + 1 ;;]]], {If[MemberQ[proved[[;; k - 1]], -Infinity], -Infinity, Total[proved[[;; k - 1]]]], proved[[k]]}]]]]],
                jetConstant[1], Range[Length[parts]]];
            Module[{target = cutoff, result = product[cutoff], tries = 0},
                While[tries < 3 && !FailureQ[result] && result["Cutoff"] < cutoff && cutoff =!= Infinity,
                    tries++; target = target + (cutoff - result["Cutoff"]); result = product[target]];
                If[FailureQ[result], result, jetTruncate[result, cutoff]]],
        MatchQ[e, Power[_, _Integer | _Rational]],
            Module[{v = seriesOrderRequirements[e[[1]]], r = e[[2]], tries = 0, required},
                (* Nonnegative integer powers are repeated products (no leading-term proof needed, symbolic coefficients
                   allowed): the k-th partial product is needed below cutoff - (r - k) v. Other powers need a proved
                   nonzero leading term: the base is requested past its valuation bound and, when cancellation raises the
                   actual valuation, requested again from it (at most six times). *)
                If[IntegerQ[r] && r >= 0,
                    With[{w = If[v === Infinity, 0, v], p = provableValuationBound[e[[1]]]}, base = treeSeries[e[[1]], cutoff - r w + w];
                        Return[If[FailureQ[base], base, Fold[jetMultiply[#1, base, cutoff - (r - #2) w,
                            If[MatchQ[p, _Integer | _Rational], {(#2 - 1) p, p}, {-Infinity, -Infinity}]] &, jetConstant[1], Range[r]]], Module]]];
                If[v === Infinity, Return[makeFailure["DivisionByZero", "A negative or fractional power of an exact zero.", <|"Expression" -> e|>], Module]];
                required = Function[x, Max[cutoff - r x + x, x + 1]];
                base = treeSeries[e[[1]], required[v]];
                (* The request grows at least geometrically (2 c + 1 from a cutoff c), so a deep cancellation is reached in
                   a few steps even when the requested cutoff is not positive (a factor inside a product). *)
                While[tries < 6 && !FailureQ[base] && (MissingQ[jetLeadingTerm[base]] || base["Cutoff"] < required[jetValuationBound[base]]) && base["Cutoff"] =!= Infinity,
                    tries++; base = treeSeries[e[[1]], Max[required[jetValuationBound[base]], 2 Max[base["Cutoff"], 0] + 1]]];
                Which[FailureQ[base], base,
                    MissingQ[jetLeadingTerm[base]], makeFailure["InsufficientOrder", "The base of a power cancels beyond the orders expanded; its leading term was not reached.",
                        <|"Expression" -> e, "ReachedCutoff" -> base["Cutoff"], "ValuationBound" -> v|>],
                    True, With[{p = jetRationalPower[base, r, cutoff]}, If[FailureQ[p], p, p["Series"]]]]],
        MatchQ[e, Power[_, _]] && FreeQ[e, FormVariable | ModularScalarNode | HypergeometricKNode], jetConstant[e],
        True, makeFailure["NotAQSeries", "The expression is not a supported q-series.", <|"Expression" -> e|>]]
];

Options[ScalarQSeries] = {Coordinate -> "q"};

(*
    Summary: The q-series of a scalar expression to a public order.
    Status: Alpha.
    Parameters: expr — expression in the variable, numeric constants and scalar ingredients; var — the variable symbol;
        n — nonnegative integer order (exponents below n are kept; remainder O(q^n)).
    Options/defaults: Coordinate -> "q" ("tau": var is tau and occurs as Exp[2 Pi I r tau]).
    Returns: Scalar QExpansionData (dimension one), or Failure.
    Effects: Extends the scalar series cache; no global variable or order changes.
    Failures: InvalidInput; NotAQSeries; DivisionByZero; SingularHypergeometric; UndeclaredSymbol (free symbols).
    Example: ScalarQSeries[ScalarModularExpression["j", q], q, 0] keeps q^-1 (a Laurent series at cutoff 0).
    Remarks: n = 0 is valid: a holomorphic series then has an empty truncation (not evidence of zero).
    See also: ScalarModularExpression; QExpansionExpression.
*)
ScalarQSeries[expr_, var_Symbol, n_Integer?NonNegative, options : OptionsPattern[]] := Module[{effective, tree, bad, jet},
    effective = resolveOperationOptions[ScalarQSeries, "ScalarQSeries", {options}]; If[FailureQ[effective], Return[effective]];
    tree = expr /. {var -> FormVariable[effective[Coordinate]], ModularScalarNode[nm_, var, c_] :> ModularScalarNode[nm, FormVariable[c], c],
        HypergeometricKNode[a_, b_, var, c_] :> HypergeometricKNode[a, b, FormVariable[c], c]};
    bad = DeleteDuplicates[Flatten[definitionTreeViolations /@ Flatten[{tree}]]];
    If[bad =!= {}, Return[makeFailure["UndeclaredSymbol", "The expression may only contain its variable, numeric constants and scalar ingredients.", <|"Expressions" -> bad|>]]];
    jet = treeSeries[tree, n]; If[FailureQ[jet], Return[jet]];
    If[jet["Cutoff"] < n, Return[makeFailure["InsufficientOrder", "The series could not be determined to the requested order.", <|"Reached" -> jet["Cutoff"], "Requested" -> n|>]]];
    makeQExpansion[{jetTruncate[jet, n]}, <|"Binding" -> "Scalar"|>]
];
ScalarQSeries[___] := makeFailure["InvalidInput", "ScalarQSeries expects an expression, a variable symbol, a nonnegative integer order and options."];

(*
    Summary: The derivative q d/dq of an expression tree (symbolic, through the ingredients' differential equations).
    Parameters: e — tree; coordinate — "q" or "tau".
    Options/defaults: None.
    Returns: Tree of the derivative, or Failure.
    Effects: Pure.
    Failures: NotAQSeries (unsupported heads, symbolic powers of non-constants).
    Example: differentiateScalarRecipe[E4node, "q"] is (E2node E4node - E6node)/3.
    Remarks: Ramanujan: q E2' = (E2^2 - E4)/12, q E4' = (E2 E4 - E6)/3, q E6' = (E2 E6 - E4^2)/2; q eta' = eta E2/24;
        q Delta' = Delta E2; q j' = -j E6/E4; q K' = K E6/E4; d/dK pFq(a; b; K) = (Prod a/Prod b) pFq(a + 1; b + 1; K).
        In the tau coordinate the derivative is (2 Pi I)^-1 d/dtau, which acts on Exp[2 Pi I r tau] as r.
    See also: ModularDerivativeExpression; differentiateFormData.
*)
differentiateScalarRecipe[e_, coordinate_String] := Module[{node, d = differentiateScalarRecipe[#, coordinate] &},
    node[name_] := ModularScalarNode[name, FormVariable[coordinate], coordinate];
    Which[
        numericConstantQ[e] || MatchQ[e, _FormParameter], 0,
        MatchQ[e, FormVariable["q"]], e,
        MatchQ[e, FormVariable["tau"]], 1/(2 Pi I),
        MatchQ[e, ModularScalarNode[_, _, _]], Switch[e[[1]],
            "E2", (node["E2"]^2 - node["E4"])/12, "E4", (node["E2"] node["E4"] - node["E6"])/3, "E6", (node["E2"] node["E6"] - node["E4"]^2)/2,
            "Eta", e node["E2"]/24, "Delta", e node["E2"], "j", -e node["E6"]/node["E4"], "K", e node["E6"]/node["E4"]],
        MatchQ[e, _HypergeometricKNode], (Times @@ e[[1]])/(Times @@ e[[2]]) HypergeometricKNode[e[[1]] + 1, e[[2]] + 1, e[[3]], e[[4]]] node["K"] node["E6"]/node["E4"],
        MatchQ[e, _Plus], Total[d /@ (List @@ e)],
        MatchQ[e, _Times], Total[Table[d[e[[i]]] Times @@ Delete[List @@ e, i], {i, Length[e]}]],
        MatchQ[e, Power[E, _]], e d[e[[2]]],
        MatchQ[e, Power[_, _?NumericQ]], e[[2]] e[[1]]^(e[[2]] - 1) d[e[[1]]],
        True, makeFailure["NotAQSeries", "The expression cannot be differentiated as a q-series.", <|"Expression" -> e|>]]
];

Options[ModularDerivativeExpression] = {Coordinate -> "q"};

(*
    Summary: The modular derivative D_k of a scalar expression.
    Status: Alpha.
    Parameters: k — exact rational weight; expr — expression in the variable and scalar ingredients; var — variable symbol.
    Options/defaults: Coordinate -> "q".
    Returns: The expression q d/dq expr - k E2 expr/12 (tau: (2 Pi I)^-1 d/dtau expr - k E2 expr/12) in var, or Failure.
    Effects: Pure.
    Failures: InvalidInput; NotAQSeries; UndeclaredSymbol.
    Example: ModularDerivativeExpression[4, ScalarModularExpression["E4", q], q] equals -E6/3.
    See also: differentiateScalarRecipe; ModularFormDerivative.
*)
ModularDerivativeExpression[k_?modularWeightQ, expr_, var_Symbol, options : OptionsPattern[]] := Module[{effective, c, tree, bad, derivative},
    effective = resolveOperationOptions[ModularDerivativeExpression, "ModularDerivativeExpression", {options}]; If[FailureQ[effective], Return[effective]];
    c = effective[Coordinate];
    tree = expr /. {var -> FormVariable[c], ModularScalarNode[nm_, var, cc_] :> ModularScalarNode[nm, FormVariable[cc], cc],
        HypergeometricKNode[a_, b_, var, cc_] :> HypergeometricKNode[a, b, FormVariable[cc], cc]};
    bad = DeleteDuplicates[Flatten[definitionTreeViolations /@ Flatten[{tree}]]];
    If[bad =!= {}, Return[makeFailure["UndeclaredSymbol", "The expression may only contain its variable, numeric constants and scalar ingredients.", <|"Expressions" -> bad|>]]];
    derivative = differentiateScalarRecipe[tree, c]; If[FailureQ[derivative], Return[derivative]];
    (derivative - k ModularScalarNode["E2", FormVariable[c], c] tree/12) /. FormVariable[c] -> var
];
ModularDerivativeExpression[___] := makeFailure["InvalidInput", "ModularDerivativeExpression expects an exact rational weight, an expression, a variable symbol and options."];

(*
    Summary: Empty the scalar series cache.
    Parameters: None.
    Options/defaults: None.
    Returns: Number of removed entries.
    Effects: Clears $ScalarSeriesCache (derived data only).
    Failures: None.
    Example: cleanScalarSeriesCache[] after a series request returns a positive count.
    See also: scalarSeries.
*)
cleanScalarSeriesCache[] := With[{n = Length[$ScalarSeriesCache]}, $ScalarSeriesCache = <||>; n];

Format[node : ModularScalarNode[name_String, var_, _String], StandardForm] := Interpretation[Row[{name, "(", var, ")"}], node];
Format[node : HypergeometricKNode[a_List, b_List, var_, _String], StandardForm] := Interpretation[Row[{"F(", a, "; ", b, "; K(", var, "))"}], node];

True
