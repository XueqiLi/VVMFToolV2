(*
    :Title: Rational-exponent q-series with truncation bookkeeping
    :Context: VVMFTool`Private`
    :Summary: Scalar series ("jets") as exact-rational exponent -> coefficient maps with a known cutoff (every exponent
        below the cutoff is known; the remainder is O(q^cutoff)), their arithmetic with rigorous cutoff propagation, basis
        transport of vector series, and the immutable public QExpansionData value.
    :Responsibilities: makeJet, jetZeroQ, jetValuationBound, jetLeadingTerm, jetAdd, jetScale, jetMultiply, jetReciprocal,
        jetRationalPower, jetThetaDerivative, jetTruncate, transportSeries, makeQExpansion, validateQExpansion;
        QExpansionData, QExpansionExpression, QExpansionCoefficients.
    :Dependencies: Diagnostics.wl (makeFailure); Models.wl (dataPrecision, inexactDataQ).
    :See Also: VVMFArch/step7Plan.md (series contract); VVMFArch/implementation/step7Status.md D-S7-3.
*)

(*
    Summary: Whether a series coefficient is zero.
    Parameters: c — coefficient (number, exact constant, or expression in FormParameter atoms).
    Options/defaults: None.
    Returns: True only for a proved zero (exact zero after RootReduce or Expand, or an approximate number equal to zero at
        its precision); False otherwise (a coefficient that may vanish for special parameter values is kept).
    Effects: Pure.
    Failures: None.
    Example: jetZeroQ[Sqrt[2]^2 - 2] is True; jetZeroQ[FormParameter["f:c"] - 1] is False.
    See also: makeJet.
*)
jetZeroQ[c_] := Which[
    c === 0, True,
    InexactNumberQ[c], c == 0,
    NumericQ[c], TrueQ[Quiet[TimeConstrained[RootReduce[c], 10, $Failed]] === 0],
    True, Expand[c] === 0];

(*
    Summary: A scalar series from exponent -> coefficient rules and a cutoff.
    Parameters: terms — association of exact rational exponents to coefficients; cutoff — exact rational or Infinity (an
        exact finite sum).
    Options/defaults: None.
    Returns: <|"Terms" -> association sorted by exponent (proved zeros and exponents >= cutoff removed), "Cutoff"|>, or
        Failure.
    Effects: Pure.
    Failures: InvalidSeries (an exponent that is not an exact rational, or a cutoff that is neither rational nor Infinity).
    Example: makeJet[<|0 -> 1, 1 -> 24, 2 -> 0|>, 2] has Terms <|0 -> 1, 1 -> 24|> and Cutoff 2.
    Remarks: The jet asserts every exponent below the cutoff: absent exponents have coefficient zero there.
    See also: jetAdd; jetMultiply.
*)
makeJet[terms_Association, cutoff_] := Module[{kept},
    If[!AllTrue[Keys[terms], MatchQ[#, _Integer | _Rational] &] || !(cutoff === Infinity || MatchQ[cutoff, _Integer | _Rational]),
        Return[makeFailure["InvalidSeries", "Series exponents and cutoffs must be exact rationals (cutoff Infinity for an exact finite sum)."]]];
    kept = KeySort[Select[KeySelect[terms, cutoff === Infinity || # < cutoff &], !jetZeroQ[#] &]];
    <|"Terms" -> kept, "Cutoff" -> cutoff|>
];
makeJet[___] := makeFailure["InvalidSeries", "Expected exponent rules and a cutoff."];
jetConstant[c_] := makeJet[<|0 -> c|>, Infinity];
jetMonomial[c_, r_] := makeJet[<|r -> c|>, Infinity];

(*
    Summary: A lower bound for the valuation of a series and its leading term.
    Parameters: a — jet.
    Options/defaults: None.
    Returns: jetValuationBound: the lowest kept exponent, else the cutoff (the series is O(q^cutoff)); Infinity for the
        exact zero series. jetLeadingTerm: <|"Exponent", "Coefficient", "Status" -> "Nonzero" | "PotentiallyNonzero"|>,
        or Missing["UnknownLeadingTerm"] when no exponent below the cutoff is nonzero.
    Effects: Pure.
    Failures: None.
    Example: jetLeadingTerm[makeJet[<|1/24 -> 1|>, 2]]["Exponent"] is 1/24.
    Remarks: "Nonzero" is proved (a number); a coefficient in parameters is "PotentiallyNonzero". An empty truncation is
        never evidence of the zero function.
    See also: jetReciprocal; jetRationalPower.
*)
jetValuationBound[a_Association] := If[a["Terms"] === <||>, a["Cutoff"], First[Keys[a["Terms"]]]];
jetLeadingTerm[a_Association] := If[a["Terms"] === <||>, Missing["UnknownLeadingTerm"],
    With[{e = First[Keys[a["Terms"]]], c = First[Values[a["Terms"]]]},
        <|"Exponent" -> e, "Coefficient" -> c, "Status" -> If[NumericQ[c], "Nonzero", "PotentiallyNonzero"]|>]];

(*
    Summary: Sum, scalar multiple and truncation of series.
    Parameters: a, b — jets; c — coefficient; n — new cutoff.
    Options/defaults: None.
    Returns: Jet. A sum is known below the smaller cutoff; a scalar multiple keeps the cutoff (zero gives the exact zero
        series); truncation lowers the cutoff.
    Effects: Pure.
    Failures: None.
    Example: jetAdd[makeJet[<|0 -> 1|>, 3], makeJet[<|1 -> 2|>, 2]] has cutoff 2.
    See also: makeJet.
*)
jetAdd[a_Association, b_Association] := With[{cutoff = Min[a["Cutoff"], b["Cutoff"]]},
    makeJet[Merge[{a["Terms"], b["Terms"]}, Total], cutoff]];
jetAdd[list_List] := Fold[jetAdd, makeJet[<||>, Infinity], list];
jetScale[a_Association, c_] := If[jetZeroQ[c], makeJet[<||>, Infinity], makeJet[Map[c # &, a["Terms"]], a["Cutoff"]]];
jetTruncate[a_Association, n_] := makeJet[a["Terms"], Min[a["Cutoff"], n]];

(*
    Summary: Product of two series with the cutoff it actually determines.
    Parameters: a, b — jets; limit — optional cutoff requested by the caller (default Infinity); {va, vb} — optional
        known lower bounds of the true valuations (from the expression tree), used when a truncation hides them.
    Options/defaults: None.
    Returns: Jet known below min(c_a + v_b, c_b + v_a, limit), with v the larger of the jet's valuation bound and the
        known bound.
    Effects: Pure.
    Failures: None.
    Example: (1 + 2 q + O(q^3)) (q^(1/2) + O(q^(5/2))) is known below 5/2.
    Remarks: Only products below the cutoff are formed, so no work is spent on terms that are discarded.
    See also: jetValuationBound.
*)
jetMultiply[a_Association, b_Association, limit_ : Infinity, hints : {_, _} : {-Infinity, -Infinity}] := Module[{cutoff, terms = <||>},
    cutoff = Min[a["Cutoff"] + Max[jetValuationBound[b], Last[hints]], b["Cutoff"] + Max[jetValuationBound[a], First[hints]], limit];
    KeyValueMap[Function[{e1, c1}, KeyValueMap[Function[{e2, c2},
        If[cutoff === Infinity || e1 + e2 < cutoff, terms[e1 + e2] = Lookup[terms, e1 + e2, 0] + c1 c2]], b["Terms"]]], a["Terms"]];
    makeJet[Map[Expand, terms], cutoff]
];

(*
    Summary: The reciprocal of a series with a proved nonzero leading coefficient.
    Parameters: a — jet; limit — optional requested cutoff.
    Options/defaults: None.
    Returns: Jet of 1/a known below min(c - 2 v, limit) (v the leading exponent, c the cutoff), or Failure.
    Effects: Pure.
    Failures: DivisionByZero (no known leading term, or a leading coefficient that is not a proved nonzero number).
    Example: the reciprocal of q (1 - q + O(q^4)) is q^-1 (1 + q + q^2 + O(q^3)), known below 2.
    Remarks: 1/a = q^-v/c0 Sum_k (-w)^k with w = a/(c0 q^v) - 1 of valuation delta > 0; terms are kept while k delta is
        below the relative precision c - v.
    See also: jetRationalPower.
*)
jetReciprocal[a_Association, limit_ : Infinity] := Module[{lead, v, c0, w, relative, exponents, result = <|0 -> 1|>},
    lead = jetLeadingTerm[a];
    If[MissingQ[lead] || lead["Status"] =!= "Nonzero",
        Return[makeFailure["DivisionByZero", "A reciprocal needs a known leading term with a proved nonzero coefficient.", <|"Leading" -> lead|>]]];
    {v, c0} = {lead["Exponent"], lead["Coefficient"]};
    w = KeyDrop[KeyMap[# - v &, Map[#/c0 &, a["Terms"]]], 0];
    relative = Min[a["Cutoff"] - v, limit + v];
    If[relative === Infinity && w =!= <||>,
        Return[makeFailure["InfiniteSeries", "The reciprocal of an exact finite sum is an infinite series; give a cutoff.", <|"Series" -> a|>]]];
    (* (1 + w) R = 1 gives R_e = -Sum_f w_f R_(e - f) over the exponents generated by w below the relative precision. *)
    exponents = exponentClosure[Keys[w], relative];
    Scan[Function[e, result[e] = Expand[-Total[KeyValueMap[Function[{f, wf}, If[f <= e, wf Lookup[result, e - f, 0], 0]], w]]]], Rest[exponents]];
    makeJet[KeyMap[# - v &, Map[#/c0 &, result]], relative - v]
];

(*
    Summary: The exponents generated by sums of positive exponents below a bound.
    Parameters: steps — positive exact exponents; bound — exact rational or Infinity (then only 0 when steps is empty).
    Options/defaults: None.
    Returns: Sorted list starting with 0.
    Effects: Pure.
    Failures: None.
    Example: exponentClosure[{1/2, 1}, 2] is {0, 1/2, 1, 3/2}.
    See also: jetReciprocal; jetRationalPower.
*)
exponentClosure[steps_List, bound_] := Module[{set = {0}, next},
    If[steps === {} || bound === Infinity, Return[{0}]];
    While[(next = Union[set, Select[Flatten[Outer[Plus, set, steps]], # < bound &]]) =!= set, set = next];
    set];

(*
    Summary: A rational power of a series with a proved nonzero leading coefficient.
    Parameters: a — jet; r — exact rational power; limit — optional requested cutoff.
    Options/defaults: None.
    Returns: <|"Series" -> jet known below min(r v + c - v, limit), "Branch" -> <|"LeadingCoefficient" -> "Principal",
        "Cusp" -> "Exp[2 Pi I tau r v]"|>|>, or Failure.
    Effects: Pure.
    Failures: DivisionByZero (no proved nonzero leading term); InvalidSeries (r not rational).
    Example: (q (1 + q + O(q^3)))^(1/2) is q^(1/2) (1 + q/2 - q^2/8 + O(q^2)), known below 5/2.
    Remarks: a^r = c0^r q^(r v) (1 + w)^r; c0^r is the principal power of the leading coefficient and q^(r v) the cusp
        branch Exp[2 Pi I tau r v] (recorded); (1 + w)^r is the binomial series, convergent as a formal series.
    See also: jetReciprocal.
*)
jetRationalPower[a_Association, r_, limit_ : Infinity] := Module[{lead, v, c0, w, relative, exponents, result = <|0 -> 1|>},
    If[!MatchQ[r, _Integer | _Rational], Return[makeFailure["InvalidSeries", "Series powers must be exact rationals."]]];
    lead = jetLeadingTerm[a];
    If[MissingQ[lead] || lead["Status"] =!= "Nonzero",
        Return[makeFailure["DivisionByZero", "A rational power needs a known leading term with a proved nonzero coefficient.", <|"Leading" -> lead|>]]];
    {v, c0} = {lead["Exponent"], lead["Coefficient"]};
    w = KeyDrop[KeyMap[# - v &, Map[#/c0 &, a["Terms"]]], 0];
    relative = Min[a["Cutoff"] - v, limit - r v];
    If[relative === Infinity && w =!= <||>,
        If[IntegerQ[r] && r >= 0, relative = r Max[Keys[w]] + 1,
            Return[makeFailure["InfiniteSeries", "This power of an exact finite sum is an infinite series; give a cutoff.", <|"Series" -> a|>]]]];
    (* Miller's recurrence for P = (1 + w)^r: e P_e = Sum_f ((r + 1) f - e) w_f P_(e - f). *)
    exponents = exponentClosure[Keys[w], relative];
    Scan[Function[e, result[e] = Expand[Total[KeyValueMap[Function[{f, wf}, If[f <= e, ((r + 1) f - e) wf Lookup[result, e - f, 0], 0]], w]]/e]], Rest[exponents]];
    <|"Series" -> makeJet[KeyMap[# + r v &, Map[c0^r # &, result]],
            If[a["Cutoff"] === Infinity && IntegerQ[r] && r >= 0 && limit === Infinity, Infinity, relative + r v]],
        "Branch" -> <|"LeadingCoefficient" -> "Principal", "Cusp" -> "Exp[2 Pi I tau r v]"|>|>
];

(*
    Summary: The derivative q d/dq of a series.
    Parameters: a — jet.
    Options/defaults: None.
    Returns: Jet with coefficient c e at exponent e and the same cutoff.
    Effects: Pure.
    Failures: None.
    Example: q d/dq (q^(1/3) + 2 q + O(q^2)) is q^(1/3)/3 + 2 q + O(q^2).
    Remarks: The derivative of the remainder O(q^c) is O(q^c), so the cutoff is unchanged.
    See also: differentiateScalarRecipe.
*)
jetThetaDerivative[a_Association] := makeJet[Association[KeyValueMap[#1 -> #1 #2 &, a["Terms"]]], a["Cutoff"]];

(*
    Summary: Transport a vector of series by a constant matrix.
    Parameters: b — d' x d matrix; components — list of d jets.
    Options/defaults: None.
    Returns: List of d' jets (b . components); component i is known below the smallest cutoff among the components it
        mixes with a nonzero entry, or Failure.
    Effects: Pure.
    Failures: InvalidSeries (dimension mismatch).
    Example: transporting {q^(1/3), q^(2/3)} by {{1, 1}, {0, 1}} mixes the exponent sets of the first component.
    Remarks: A general basis mixes exponent sets; no component is assumed to have one exponent class.
    See also: changeFormBasisData.
*)
transportSeries[b_?MatrixQ, components_List] := If[Last[Dimensions[b]] =!= Length[components],
    makeFailure["InvalidSeries", "The transport matrix must have one column per series component."],
    Map[Function[row, jetAdd[MapThread[If[jetZeroQ[#1], makeJet[<||>, Infinity], jetScale[#2, #1]] &, {row, components}]]], b]];

(*
    Summary: Build and validate the public immutable QExpansionData value.
    Parameters: components — list of jets; meta — <|"Arithmetic", "Precision", "Binding", "Source"|> (missing keys default
        to exact arithmetic, raw binding and Missing source).
    Options/defaults: None.
    Returns: QExpansionData[<|"SchemaVersion" -> 1, "Dimension", "Components" -> {<|exponent -> coefficient|>, ...},
        "Cutoff" -> common cutoff, "ComponentCutoffs", "Arithmetic", "Precision", "Binding", "Source"|>], or Failure.
    Effects: Pure.
    Failures: InvalidSeries.
    Example: makeQExpansion[{makeJet[<|0 -> 1|>, 4]}, <||>] is the scalar 1 + O(q^4).
    Remarks: The common cutoff is the smallest component cutoff; each component keeps its own. Exponents are exact
        rationals; a requested public order n keeps every exponent strictly below n.
    See also: QExpansionExpression; QExpansionCoefficients.
*)
makeQExpansion[components_List, meta_Association] := Module[{data},
    If[!AllTrue[components, AssociationQ[#] && KeyExistsQ[#, "Terms"] && KeyExistsQ[#, "Cutoff"] &],
        Return[makeFailure["InvalidSeries", "Every component must be a series."]]];
    data = <|"SchemaVersion" -> 1, "Dimension" -> Length[components], "Components" -> Lookup[components, "Terms"],
        "Cutoff" -> Min[Append[Lookup[components, "Cutoff"], Infinity]], "ComponentCutoffs" -> Lookup[components, "Cutoff"],
        "Arithmetic" -> Lookup[meta, "Arithmetic", If[inexactDataQ[Lookup[components, "Terms"]], "Numerical", "Exact"]],
        "Precision" -> Lookup[meta, "Precision", dataPrecision[Values /@ Lookup[components, "Terms"]]],
        "Binding" -> Lookup[meta, "Binding", "Raw"], "Source" -> Lookup[meta, "Source", Missing["NoSource"]]|>;
    With[{checked = validateQExpansion[QExpansionData[data]]}, If[FailureQ[checked], checked, QExpansionData[data]]]
];

(*
    Summary: Validate QExpansionData before use.
    Parameters: q — any expression.
    Options/defaults: None.
    Returns: The data association, or InvalidSeries Failure.
    Effects: Pure.
    Failures: InvalidSeries (missing keys, exponents not exact rationals or at or above a component cutoff, inconsistent
        dimension or cutoffs).
    Example: a QExpansionData whose component holds an exponent 1.5 fails.
    See also: makeQExpansion.
*)
validateQExpansion[QExpansionData[data_Association]] := Module[{},
    If[!SubsetQ[Keys[data], {"SchemaVersion", "Dimension", "Components", "Cutoff", "ComponentCutoffs", "Arithmetic", "Precision", "Binding", "Source"}] ||
            data["SchemaVersion"] =!= 1 || !ListQ[data["Components"]] || Length[data["Components"]] =!= data["Dimension"] ||
            !ListQ[data["ComponentCutoffs"]] || Length[data["ComponentCutoffs"]] =!= data["Dimension"] ||
            !AllTrue[data["ComponentCutoffs"], # === Infinity || MatchQ[#, _Integer | _Rational] &] ||
            data["Cutoff"] =!= Min[Append[data["ComponentCutoffs"], Infinity]] || !MemberQ[{"Exact", "Numerical"}, data["Arithmetic"]] ||
            !AllTrue[Transpose[{data["Components"], data["ComponentCutoffs"]}], Function[pair, AssociationQ[pair[[1]]] &&
                AllTrue[Keys[pair[[1]]], MatchQ[#, _Integer | _Rational] && (pair[[2]] === Infinity || # < pair[[2]]) &]]],
        Return[makeFailure["InvalidSeries", "Malformed QExpansionData."]]];
    data
];
validateQExpansion[___] := makeFailure["InvalidSeries", "Expected QExpansionData."];

(* The jets of validated QExpansionData. *)
qExpansionJets[data_Association] := MapThread[makeJet, {data["Components"], data["ComponentCutoffs"]}];

SetAttributes[QExpansionExpression, HoldRest];

(*
    Summary: The finite expansion of QExpansionData in a variable, with its remainder.
    Status: Alpha.
    Parameters: qexp — QExpansionData; z — symbol without a value.
    Options/defaults: None.
    Returns: List of component expressions Sum c z^e + O[z]^cutoff (SeriesData with rational and negative exponents);
        an exact finite component has no remainder.
    Effects: Pure.
    Failures: InvalidSeries; InvalidVariable (z is not a symbol, or has a value).
    Example: QExpansionExpression[QExpansionData[...], q] gives {1 + 240 q + 2160 q^2 + O[q]^3} for E4 to order 3.
    Remarks: The remainder is never erased; an empty truncation is O[z]^n, not zero.
    See also: QExpansionCoefficients; ModularFormQExp.
*)
QExpansionExpression[qexp_QExpansionData, z_] := Module[{data = validateQExpansion[qexp]},
    If[FailureQ[data], Return[data]];
    If[!MatchQ[Unevaluated[z], _Symbol] || ValueQ[z], Return[makeFailure["InvalidVariable", "The expansion variable must be a symbol without a value."]]];
    MapThread[Function[{terms, cutoff}, Total[KeyValueMap[#2 z^#1 &, terms]] + If[cutoff === Infinity, 0, SeriesData[z, 0, {}, Numerator[cutoff], Numerator[cutoff], Denominator[cutoff]]]],
        {data["Components"], data["ComponentCutoffs"]}]
];
QExpansionExpression[___] := makeFailure["InvalidInput", "QExpansionExpression expects QExpansionData and a symbol."];

(*
    Summary: The coefficient maps of QExpansionData.
    Status: Alpha.
    Parameters: qexp — QExpansionData.
    Options/defaults: None.
    Returns: <|"Components" -> list of exponent -> coefficient associations in ascending exponent order,
        "ComponentCutoffs", "Cutoff"|>, or Failure.
    Effects: Pure.
    Failures: InvalidSeries.
    Example: QExpansionCoefficients[e4]["Components"] is {<|0 -> 1, 1 -> 240, 2 -> 2160|>}.
    See also: QExpansionExpression.
*)
QExpansionCoefficients[qexp_QExpansionData] := Module[{data = validateQExpansion[qexp]},
    If[FailureQ[data], data, <|"Components" -> KeySort /@ data["Components"], "ComponentCutoffs" -> data["ComponentCutoffs"], "Cutoff" -> data["Cutoff"]|>]];
QExpansionCoefficients[___] := makeFailure["InvalidInput", "QExpansionCoefficients expects QExpansionData."];

QExpansionData[data_Association][key_String] := Lookup[data, key, Missing["UnknownProperty", key]];

Format[QExpansionData[data_Association], StandardForm] := Interpretation[Row[{"QExpansionData[", Lookup[data, "Dimension", "?"], " components, O(q^",
    Lookup[data, "Cutoff", "?"], ")]"}], QExpansionData[data]];

True
