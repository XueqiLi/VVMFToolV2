(*
    :Title: Relative normalization of modular forms
    :Context: VVMFTool`Private`
    :Summary: Series of a form's components with its unknowns symbolic, the linear S-transformation system at independent
        sample points with an exact anchor row, least-squares solution with rank and residual checks, algebraic
        reconstruction proposals verified at higher precision on holdout points, proof-status reporting, anchors of
        manual definitions, and the atomic coefficient commit.
    :Responsibilities: formComponentJets, linearParameterParts, evaluateComponentJets, normalizationPoints,
        resolveNormalizationAnchor, homogeneousDefinitionQ, definitionValuationBound, transportNormalizationAnchor, normalizationSystem,
        chopNormalizationSystem, automaticSeriesOrder, solveNormalization,
        reconstructNormalization, verifyNormalization, normalizationTarget; CoefficientResult, SolveModularCoefficients,
        ModularFormGetCoeff.
    :Dependencies: ModularScalars.wl (treeSeries); ModularConstructors.wl (MLDE recipes); ModularFormObjects.wl (records).
    :See Also: VVMFArch/step7Plan.md (normalization frame, solver and statuses); D-S7-4.
*)

(*
    Summary: The component series of a definition in the stored basis, unknowns symbolic.
    Parameters: definition — definition data; cutoff — exact rational cutoff (each component's exponents below it).
    Options/defaults: None.
    Returns: List of jets (FormParameter atoms in the coefficients), or Failure.
    Effects: Extends the scalar series cache.
    Failures: NotAQSeries; InsufficientOrder (a finite jet shorter than the cutoff); MLDE failures.
    Example: formComponentJets[e4definition, 3] is {1 + 240 q + 2160 q^2 + O(q^3)}.
    Remarks: Analytic definitions expand their trees; MLDE definitions extend their recipe to the cutoff and transport
        c_i times the frame solutions by B^-1; a finite jet supplies only its known coefficients and never more.
    See also: ModularFormQExp; normalizationSystem.
*)
formComponentJets[definition_Association, cutoff_] := With[{base = baseComponentJets[definition, cutoff]},
    (* A basis change composes as a final transform of the stored components (ChangeModularFormBasis). *)
    If[KeyExistsQ[definition, "Transform"] && !FailureQ[base], jetTruncate[#, cutoff] & /@ transportSeries[definition["Transform"], base], base]];
baseComponentJets[definition_Association, cutoff_] := Switch[definition["Kind"],
    "Analytic", Module[{jets = treeSeries[#, cutoff] & /@ definition["Components"]},
        Which[AnyTrue[jets, FailureQ], FirstCase[jets, _Failure], AnyTrue[jets, #["Cutoff"] < cutoff &],
            makeFailure["InsufficientOrder", "A component series could not be determined to the requested order.", <|"Requested" -> cutoff|>],
            True, jetTruncate[#, cutoff] & /@ jets]],
    "Jet", With[{jets = qExpansionJets[validateQExpansion[definition["Jet"]]]}, If[AnyTrue[jets, #["Cutoff"] < cutoff &],
        makeFailure["InsufficientOrder", "A finite jet does not define coefficients beyond its cutoff.", <|"Cutoff" -> Min[Lookup[jets, "Cutoff"]], "Requested" -> cutoff|>],
        jetTruncate[#, cutoff] & /@ jets]],
    "MLDE", mldeComponentJets[definition, cutoff],
    "Derived", derivedComponentJets[definition, cutoff],
    _, makeFailure["InvalidDefinition", "Unknown definition kind."]];

(*
    Summary: The stored-basis component series of an MLDE definition.
    Parameters: definition — MLDE definition data; cutoff — exact rational cutoff.
    Options/defaults: None.
    Returns: List of jets, or Failure.
    Effects: Extends the recipe's solution as needed (not stored in the record).
    Failures: As extendMLDESeries.
    Example: the [48,29] F definition expands to four components mixing nothing (T-diagonal stored basis).
    See also: formComponentJets.
*)
mldeComponentJets[definition_Association, cutoff_] := Module[{recipe = definition["Recipe"], system, solution, needed, frame, seedJets, key},
    system = mldeSystem[recipe["System"]]; If[FailureQ[system], Return[system]];
    needed = Ceiling[cutoff - Min[recipe["Exponents"]]] + 1;
    (* Extended solutions are derived data shared by the seeds of one recipe (kernel-local cache). *)
    key = Hash[KeyTake[recipe, {"System", "Coefficients", "GLeading", "Exponents", "Weight"}], "SHA256"];
    solution = Which[recipe["Solution"]["Order"] >= needed, recipe["Solution"],
        KeyExistsQ[$MLDESolutionCache, key] && $MLDESolutionCache[key]["Order"] >= needed, $MLDESolutionCache[key],
        True, extendMLDESeries[system, <|"Coefficients" -> recipe["Coefficients"], "GLeading" -> recipe["GLeading"]|>, recipe["Exponents"], recipe["Weight"], needed]];
    If[FailureQ[solution], Return[solution]];
    If[!KeyExistsQ[$MLDESolutionCache, key] || $MLDESolutionCache[key]["Order"] < solution["Order"], AssociateTo[$MLDESolutionCache, key -> solution]];
    seedJets = If[recipe["SeedID"] === "G", solution["G"], solution["F"]];
    frame = MapIndexed[If[First[#2] === 1, #1, jetScale[#1, FormParameter[definition["Parameters"][[First[#2] - 1]]["ID"]]]] &, seedJets];
    jetTruncate[#, cutoff] & /@ transportSeries[recipe["FrameBInverse"], frame]
];

If[!AssociationQ[$MLDESolutionCache], $MLDESolutionCache = <||>];

(*
    Summary: Split component series linear in the unknowns into a fixed part and one part per unknown.
    Parameters: jets — component series; ids — FormParameter IDs.
    Options/defaults: None.
    Returns: <|"Fixed" -> jets, "Parts" -> <|id -> jets|>|>, or NonlinearParameters Failure.
    Effects: Pure.
    Failures: NonlinearParameters (a coefficient of degree above one in the unknowns, or a product of two).
    Example: {2 + c q} splits into Fixed {2}, Parts <|c -> {q}|>.
    See also: normalizationSystem.
*)
linearParameterParts[jets_List, ids_List] := Module[{atoms = FormParameter /@ ids, nonlinear},
    nonlinear = Select[Flatten[Values /@ Lookup[jets, "Terms"]], !PolynomialQ[#, atoms] || (atoms =!= {} && Max[Append[Total /@ Keys[CoefficientRules[#, atoms]], 0]] > 1) &];
    If[nonlinear =!= {}, Return[makeFailure["NonlinearParameters", "The normalization unknowns must occur linearly in the component data.", <|"Coefficients" -> Take[nonlinear, UpTo[3]]|>]]];
    <|"Fixed" -> Map[makeJet[Map[# /. Thread[atoms -> 0] &, #["Terms"]], #["Cutoff"]] &, jets],
        "Parts" -> AssociationMap[Function[id, Map[makeJet[Map[Coefficient[#, FormParameter[id]] &, #["Terms"]], #["Cutoff"]] &, jets]], ids]|>
];

(*
    Summary: Numerical values of component series at an upper-half-plane point.
    Parameters: jets — component series (numeric coefficients); tau — point; digits — working precision.
    Options/defaults: None.
    Returns: Vector of values Sum c Exp[2 Pi I tau e] (the cusp branch: never a principal power of q).
    Effects: Pure.
    Failures: None.
    Example: evaluateComponentJets[{eta jet}, I, 30] gives Dedekind eta(I) to the series' accuracy.
    See also: normalizationSystem; ModularFormEvaluate.
*)
evaluateComponentJets[jets_List, tau_, digits_] := Map[Total[KeyValueMap[N[#2, digits] Exp[2 Pi I N[tau, digits] #1] &, #["Terms"]]] &, jets];

(*
    Summary: Fit and holdout sample points with Im tau and Im(-1/tau) bounded below.
    Parameters: count — number of fit points; holdout — number of holdout points.
    Options/defaults: None.
    Returns: <|"Fit" -> exact points, "Holdout" -> exact points (disjoint), "MinimumImaginaryPart"|>.
    Effects: Pure.
    Failures: None.
    Example: normalizationPoints[4, 2]["MinimumImaginaryPart"] is above 0.7.
    Remarks: Exact rational real and imaginary parts near the unit circle, so both tau and -1/tau are well inside the
        cusp chart.
    See also: normalizationSystem.
*)
$NormalizationPoints = {1/10 + I, -1/5 + 11 I/10, 1/7 + 6 I/5, -1/9 + 9 I/10, 2/9 + I, -2/7 + I, 1/4 + 23 I/20, -1/8 + 6 I/5};
$HoldoutPoints = {1/3 + I, -1/4 + 21 I/20, 1/6 + 9 I/10};
(* ValidateModularForm samples the transformation laws at points disjoint from the fit and holdout points. *)
$ValidationPoints = {3/11 + 13 I/10, -2/13 + 23 I/20};
normalizationPoints[count_Integer, holdout_Integer] := With[{fit = Take[$NormalizationPoints, UpTo[count]], hold = Take[$HoldoutPoints, UpTo[holdout]]},
    <|"Fit" -> fit, "Holdout" -> hold, "MinimumImaginaryPart" -> N[Min[Im /@ Join[fit, hold, -1/fit, -1/hold]]]|>];

(*
    Summary: The automatic anchor of a manual or raw parameterized definition (manual-input policy).
    Parameters: definition — definition data; ctx — formContextData; options — validated options (Normalization).
    Options/defaults: Normalization Automatic, or an explicit anchor <|"Component", "Exponent", "Value"|> in the supplied
        Rep frame.
    Returns: Anchor record (Kind "Anchor", FrameFromStored identity, Rules Missing["Unresolved"]), or Failure.
    Effects: Extends the scalar series cache.
    Failures: AnchorUnavailable (no known leading datum and no free overall scale, or a zero/ambiguous anchor);
        IncompatibleAnchor (an explicit anchor contradicts a fixed coefficient); NonlinearParameters.
    Example: {2 f, c g} with f leading 1 anchors component 1 at its leading exponent with value 2.
    Remarks: Homogeneity is decided from the definition, not from a truncation: an analytic definition is homogeneous
        when every component tree vanishes identically with the unknowns set to 0; other kinds are not (an MLDE seed fixes
        component 1). A homogeneous definition (a free overall scale) gets value 1 at the first component with a leading
        term; otherwise the first component whose leading coefficient is a proved nonzero number (parameter-free) supplies
        the anchor with its written scale; else AnchorUnavailable. The series are read to Max[3, v + 1] with v the tree
        valuation bound (and past an explicit anchor's exponent), so a fixed part of high valuation is seen.
    See also: initialNormalization; transportNormalizationAnchor; homogeneousDefinitionQ.
*)
resolveNormalizationAnchor[definition_Association, ctx_Association, options_Association] := Module[{ids = Lookup[definition["Parameters"], "ID", {}], jets, parts, fixedLead, anchor,
        explicit = Lookup[options, Normalization, Automatic], cutoff, homogeneous},
    If[AssociationQ[explicit] && !(IntegerQ[explicit["Component"]] && 1 <= explicit["Component"] <= definition["Dimension"] && MatchQ[explicit["Exponent"], _Integer | _Rational] &&
            NumericQ[explicit["Value"]] && explicit["Value"] != 0),
        Return[makeFailure["AnchorUnavailable", "An explicit anchor names a component, a rational exponent and a nonzero value.", <|"Normalization" -> explicit|>]]];
    cutoff = Max[3, definitionValuationBound[definition] + 1, If[AssociationQ[explicit], explicit["Exponent"] + 1, 3]];
    jets = formComponentJets[definition, cutoff]; If[FailureQ[jets], Return[jets]];
    parts = linearParameterParts[jets, ids]; If[FailureQ[parts], Return[parts]];
    homogeneous = homogeneousDefinitionQ[definition];
    anchor = If[AssociationQ[explicit],
        With[{fixed = Lookup[parts["Fixed"][[explicit["Component"]]]["Terms"], explicit["Exponent"], 0],
                variable = AnyTrue[ids, Lookup[parts["Parts"][#][[explicit["Component"]]]["Terms"], explicit["Exponent"], 0] =!= 0 &]},
            If[!variable && !TrueQ[fixed == explicit["Value"]], Return[makeFailure["IncompatibleAnchor", "The explicit anchor contradicts a fixed coefficient of the definition.",
                <|"Fixed" -> fixed, "Requested" -> explicit["Value"]|>]]];
            KeyTake[explicit, {"Component", "Exponent", "Value"}]],
        fixedLead = SelectFirst[Range[Length[jets]], Function[i, With[{lead = jetLeadingTerm[jets[[i]]]},
            !MissingQ[lead] && lead["Status"] === "Nonzero"]], None];
        Which[
            homogeneous && AnyTrue[jets, !MissingQ[jetLeadingTerm[#]] &],
                With[{i = SelectFirst[Range[Length[jets]], !MissingQ[jetLeadingTerm[jets[[#]]]] &]}, <|"Component" -> i, "Exponent" -> jetLeadingTerm[jets[[i]]]["Exponent"], "Value" -> 1|>],
            fixedLead =!= None, With[{lead = jetLeadingTerm[jets[[fixedLead]]]}, <|"Component" -> fixedLead, "Exponent" -> lead["Exponent"], "Value" -> lead["Coefficient"]|>],
            homogeneous, Return[makeFailure["AnchorUnavailable", "No component has a known leading term below the series cutoff; give an explicit Normalization anchor.", <|"Cutoff" -> cutoff|>]],
            True, Return[makeFailure["AnchorUnavailable", "No known nonzero leading datum fixes the scale and the overall scale is not free (the definition is not homogeneous in its unknowns); give an explicit Normalization anchor."]]]];
    <|"Kind" -> "Anchor", "Rules" -> Missing["Unresolved"], "ProofStatus" -> "None", "AnchorFrameID" -> "frame-stored-" <> ctx["BasisID"], "FrameRep" -> ctx["Rep"],
        "FrameFromStored" -> IdentityMatrix[ctx["Dimension"]], "FamilyID" -> definition["FamilyID"], "SeedID" -> "Manual", "AnchorSeed" -> "Manual",
        "Component" -> anchor["Component"], "Exponent" -> anchor["Exponent"], "Value" -> anchor["Value"]|>
];

(*
    Summary: Whether a definition's overall scale is free (homogeneous in its unknowns) and its valuation bound.
    Parameters: definition — definition data.
    Options/defaults: None.
    Returns: homogeneousDefinitionQ: True when the definition is analytic, has unknowns, and every component tree expands
        to exactly 0 with the unknowns set to 0; False otherwise (MLDE seeds fix component 1, jets have no unknowns,
        derived definitions keep their source's anchor). definitionValuationBound: the largest finite tree valuation bound
        of an analytic definition's components (seriesOrderRequirements), 0 for other kinds or when nothing is bounded,
        so every component's leading datum is read (a later component may supply the anchor).
    Effects: Pure.
    Failures: None.
    Example: {c E4^9 + Delta^3} is not homogeneous (its fixed part Delta^3 is not identically zero); {c Delta^3} is, with
        valuation bound 3; {c E4^9, 2 Delta^3} has bound 3, so it anchors (2, 3, 2).
    Remarks: Structural: a fixed part that cancels only as a series (not as a tree) counts as not homogeneous, so the
        scale is never declared free by a truncation.
    See also: resolveNormalizationAnchor.
*)
homogeneousDefinitionQ[definition_Association] := definition["Kind"] === "Analytic" && definition["Parameters"] =!= {} && !KeyExistsQ[definition, "Transform"] &&
    AllTrue[definition["Components"], Expand[# /. FormParameter[_] -> 0] === 0 &];
definitionValuationBound[definition_Association] := If[definition["Kind"] === "Analytic",
    With[{bounds = Select[seriesOrderRequirements /@ definition["Components"], MatchQ[#, _Integer | _Rational] &]}, If[bounds === {}, 0, Ceiling[Max[bounds]]]], 0];

(*
    Summary: The anchor record of a form transported to a new basis.
    Parameters: anchor — normalization record; b — the basis change (F_new = b . F_old).
    Options/defaults: None.
    Returns: The record with FrameFromStored A . Inverse[b] (the same linear functional on the new components).
    Effects: Pure.
    Failures: None.
    Example: a constructed anchor with A = B becomes B . Inverse[b].
    See also: ChangeModularFormBasis.
*)
transportNormalizationAnchor[anchor_Association, b_?MatrixQ] := If[KeyExistsQ[anchor, "FrameFromStored"],
    Join[anchor, <|"FrameFromStored" -> anchor["FrameFromStored"] . Inverse[b]|>], anchor];

(*
    Summary: The linear S-transformation system of a form's unknowns.
    Parameters: target — normalizationTarget; points — sample points; digits — working precision; order — series order.
    Options/defaults: None.
    Returns: <|"Matrix", "RightSide", "AnchorRow", "AnchorRightSide", "ColumnScale" (raw magnitude of each unknown's
        terms), "RightSideScale" (raw magnitude of the fixed part)|>, or Failure.
    Effects: Extends series caches.
    Failures: As formComponentJets and linearParameterParts.
    Example: the T' triplet seed gives 3 rows per point in its two unknowns plus the anchor row.
    Remarks: Rows: [F(-1/tau) - (-tau)^k rho(S) F(tau)]_i = 0 for every component and point, F = F_fixed + Sum p F_p; the
        anchor (A . F)_component's coefficient at its exponent equals its value, an exact row.
    See also: solveNormalization.
*)
normalizationSystem[target_Association, points_List, digits_, order_] := Module[{ids = target["Parameters"], jets, parts, s = target["S"], k = target["Weight"], rows = {}, rhs = {},
        anchorRow, anchorRhs, a = target["Anchor"]["FrameFromStored"], frameJets, scale, fixedScale},
    jets = formComponentJets[target["Definition"], target["Cutoff"]]; If[FailureQ[jets], Return[jets]];
    parts = linearParameterParts[jets, ids]; If[FailureQ[parts], Return[parts]];
    scale = ConstantArray[0, Length[ids]]; fixedScale = 0;
    Do[Module[{tauPrime = -1/tau, factor = (-tau)^k, fixedVals, partVals},
            fixedVals = evaluateComponentJets[parts["Fixed"], tauPrime, digits] - N[factor, digits] (s . evaluateComponentJets[parts["Fixed"], tau, digits]);
            partVals = Map[evaluateComponentJets[parts["Parts"][#], tauPrime, digits] - N[factor, digits] (s . evaluateComponentJets[parts["Parts"][#], tau, digits]) &, ids];
            (* The raw magnitude of each unknown's terms, so a column that cancels is recognized as zero. *)
            scale = scale + Map[Total[Abs[evaluateComponentJets[parts["Parts"][#], tauPrime, digits]]] + Total[Abs[N[factor, digits] (s . evaluateComponentJets[parts["Parts"][#], tau, digits])]] &, ids];
            fixedScale = fixedScale + Total[Abs[evaluateComponentJets[parts["Fixed"], tauPrime, digits]]] + Total[Abs[N[factor, digits] (s . evaluateComponentJets[parts["Fixed"], tau, digits])]];
            rows = Join[rows, Transpose[partVals]]; rhs = Join[rhs, -fixedVals]],
        {tau, points}];
    frameJets = transportSeries[a, jets];
    With[{entry = Lookup[frameJets[[target["Anchor"]["Component"]]]["Terms"], target["Anchor"]["Exponent"], 0]},
        anchorRow = Map[Coefficient[entry, FormParameter[#]] &, ids]; anchorRhs = target["Anchor"]["Value"] - (entry /. Thread[FormParameter /@ ids -> 0])];
    <|"Matrix" -> Append[rows, N[anchorRow, digits]], "RightSide" -> Append[rhs, N[anchorRhs, digits]], "AnchorRow" -> anchorRow, "AnchorRightSide" -> anchorRhs,
        "ColumnScale" -> MapThread[Max[#1, Abs[#2], 10^-digits] &, {scale, N[anchorRow, digits]}], "RightSideScale" -> Max[fixedScale, Abs[N[anchorRhs, digits]], 10^-digits]|>
];

(*
    Summary: Everything the coefficient solver needs about a form or a raw definition.
    Parameters: definition; ctx — formContextData; weight; anchor — normalization record; cutoff — series cutoff.
    Options/defaults: None.
    Returns: <|"Definition", "Parameters" (IDs), "S" (stored S matrix), "Weight", "Anchor", "Cutoff"|>.
    Effects: Pure.
    Failures: None.
    Example: normalizationTarget[def, ctx, 2, anchor, 20]["Parameters"] lists the two relative constants of a triplet.
    See also: solveNormalization.
*)
normalizationTarget[definition_Association, ctx_Association, weight_, anchor_Association, cutoff_] :=
    <|"Definition" -> definition, "Parameters" -> Lookup[definition["Parameters"], "ID", {}], "S" -> ctx["S"], "Weight" -> weight, "Anchor" -> anchor, "Cutoff" -> cutoff|>;

(*
    Summary: Solve the normalization unknowns numerically, reconstruct exact candidates and verify them.
    Parameters: target — normalizationTarget; effective — validated options.
    Options/defaults: WorkingPrecision 80; AccuracyGoal Automatic (Floor[WorkingPrecision/2]); SeriesOrder Automatic
        (from the accuracy goal, the weight and the actual series tail at the sample points: automaticSeriesOrder); Method Automatic, "NumericalFit" or "Reconstruct" ("Exact" fails:
        no exact identity is implemented for these recipes); NormalizationRules (explicit rules checked through the same
        evidence path); RequireProof.
    Returns: CoefficientResult data, or Failure.
    Effects: Extends series caches.
    Failures: RankDeficient (the samples do not determine the unknowns); InconsistentNormalization (large residuals);
        UnstableFit (the fit at two orders disagrees beyond the goal); MethodUnavailable; ProofRequired;
        ReconstructionRejected (explicit "Reconstruct" whose candidates fail; the fit is attached).
    Example: the T' triplet's two relative constants are reconstructed as algebraic numbers and checked on holdouts.
    Remarks: ProofStatus is "Unchecked" (Verification -> None), "NumericalFit", "NumericallyCheckedReconstruction" or, for explicit NormalizationRules,
        "NumericallyCheckedExplicitRules" (exact) / "NumericalExplicitRules" (inexact); "Proven" needs an exact identity
        and is never inferred from samples. A fitted value's precision never exceeds the goal or the achieved accuracy.
    See also: reconstructNormalization; verifyNormalization; SolveModularCoefficients.
*)
solveNormalization[target_Association, effective_Association] := Module[{ids = target["Parameters"], digits = effective[WorkingPrecision], goal, order, points, system, solve,
        first, second, fit, rank, residual, result, minIm, accuracy},
    If[effective[Method] === "Exact", Return[makeFailure["MethodUnavailable", "No exact normalization identity is implemented for this recipe; use Automatic, \"NumericalFit\" or \"Reconstruct\"."]]];
    (* Verification (methodOptionsPlan.md 2C.4): "Exact" has no identity to prove; None cannot accept a reconstruction
       (its holdout check is what accepts it) nor a proof *)
    Switch[Lookup[effective, Verification, Automatic],
        "Exact", Return[makeFailure["InapplicableOption", "No exact normalization identity exists; Verification is Automatic, \"Numerical\" or None.", <|"Options" -> {Verification}|>]],
        None, If[effective[Method] === "Reconstruct" || TrueQ[effective[RequireProof]], Return[makeFailure["InapplicableOption",
            "Method -> \"Reconstruct\" and RequireProof -> True need the checks that Verification -> None skips.", <|"Options" -> {Verification, Method, RequireProof}|>]]]];
    goal = Replace[effective[AccuracyGoal], Automatic -> Floor[digits/2]];
    If[ids === {}, Return[<|"Rules" -> {}, "NumericFit" -> {}, "ExactCandidates" -> {}, "Normalization" -> target["Anchor"], "ProofStatus" -> "NotApplicable",
        "Evidence" -> "No unknowns."|>]];
    (* No exact identity is implemented, so nothing below is Proven: RequireProof refuses every numerical route. *)
    If[TrueQ[effective[RequireProof]], Return[makeFailure["ProofRequired", "RequireProof -> True needs an exact normalization identity; only numerical evidence is available for this recipe."]]];
    points = normalizationPoints[Max[2, Ceiling[(Length[ids] + 1)/Max[1, Length[target["S"]]]] + 1], 2];
    minIm = points["MinimumImaginaryPart"];
    order = Replace[effective[SeriesOrder], Automatic -> automaticSeriesOrder[target, goal, minIm]];
    If[FailureQ[order], Return[order]];
    solve[n_] := Module[{t = Join[target, <|"Cutoff" -> n|>], sys},
        sys = normalizationSystem[t, points["Fit"], digits + 10, n]; If[FailureQ[sys], Return[sys, Module]];
        sys = chopNormalizationSystem[sys, goal];
        <|"System" -> sys, "Solution" -> LeastSquares[sys["Matrix"], sys["RightSide"]],
            "Singular" -> SingularValueList[sys["Matrix"] . DiagonalMatrix[1/sys["ColumnScale"]], Tolerance -> 0]|>];
    If[AssociationQ[effective[NormalizationRules]] || ListQ[effective[NormalizationRules]],
        fit = Lookup[Association[effective[NormalizationRules]], ids, Missing[]];
        If[AnyTrue[fit, MissingQ], Return[makeFailure["InvalidOption", "NormalizationRules must give every unknown.", <|"Options" -> {NormalizationRules}|>]]];
        If[Lookup[effective, Verification, Automatic] === None, Return[<|"Rules" -> Thread[ids -> fit], "NumericFit" -> {}, "ExactCandidates" -> {},
            "Normalization" -> target["Anchor"], "ProofStatus" -> "Unchecked", "Evidence" -> <|"Verification" -> None|>, "Source" -> "NormalizationRules"|>]];
        result = verifyNormalization[target, AssociationThread[ids, fit], points["Holdout"], digits, order, goal];
        (* Explicit rules are checked, not reconstructed: the status names their source. *)
        Return[If[FailureQ[result], result, <|"Rules" -> Thread[ids -> fit], "NumericFit" -> {}, "ExactCandidates" -> If[FreeQ[fit, _Real], Thread[ids -> fit], {}], "Normalization" -> target["Anchor"],
            "ProofStatus" -> If[FreeQ[fit, _Real], "NumericallyCheckedExplicitRules", "NumericalExplicitRules"], "Evidence" -> Join[result, <|"Order" -> order|>], "Source" -> "NormalizationRules"|>]]];
    first = solve[order]; If[FailureQ[first], Return[first]];
    (* Rank of the scale-normalized system: a column that cancels relative to its own terms is not determined. *)
    rank = Count[first["Singular"], x_ /; x > 10^-goal];
    If[rank < Length[ids], Return[makeFailure["RankDeficient", "The sampled transformation equations do not determine the normalization unknowns.", <|"Rank" -> rank, "Unknowns" -> Length[ids]|>]]];
    (* Verification -> None: the fit at one order, unchecked (no stability, residual, reconstruction or holdout check) *)
    If[Lookup[effective, Verification, Automatic] === None,
        fit = AssociationThread[ids, Map[SetPrecision[#, Min[Precision[#], goal]] &, first["Solution"]]];
        Return[<|"Rules" -> Normal[fit], "NumericFit" -> Normal[fit], "ExactCandidates" -> {}, "Normalization" -> target["Anchor"], "ProofStatus" -> "Unchecked",
            "Evidence" -> <|"Rank" -> rank, "Order" -> order, "Samples" -> points["Fit"], "WorkingPrecision" -> digits, "Verification" -> None|>|>]];
    second = solve[order + 5]; If[FailureQ[second], Return[second]];
    If[Max[Abs[first["Solution"] - second["Solution"]]] > 10^-goal, Return[makeFailure["UnstableFit",
        "The fitted unknowns change with the series order beyond the accuracy goal; raise SeriesOrder (or WorkingPrecision).",
        <|"Difference" -> N[Max[Abs[first["Solution"] - second["Solution"]]], 5], "Order" -> order, "WorkingPrecision" -> digits|>]]];
    residual = Max[Abs[second["System"]["Matrix"] . second["Solution"] - second["System"]["RightSide"]]];
    If[residual > 10^-goal, Return[makeFailure["InconsistentNormalization",
        "The transformation equations are not satisfied by any choice of the unknowns (if the definition is right, raise SeriesOrder or WorkingPrecision).",
        <|"Residual" -> N[residual, 5], "Order" -> order, "WorkingPrecision" -> digits|>]]];
    (* achieved accuracy: the agreement of the fits at two series orders; a numerical value never gains digits by padding *)
    accuracy = Min[digits, Floor[-Log10[Max[Abs[first["Solution"] - second["Solution"]], 10^-digits]]]];
    fit = AssociationThread[ids, Map[SetPrecision[#, Min[Precision[#], goal, accuracy]] &, second["Solution"]]];
    result = If[effective[Method] === "NumericalFit", Missing["NotRequested"],
        reconstructNormalization[target, AssociationThread[ids, second["Solution"]], points, digits, order, goal, accuracy]];
    (* an explicit Method -> "Reconstruct" is honoured: a rejected reconstruction is a Failure carrying the fit, never
       a silent NumericalFit (methodOptionsPlan.md 2A.2); Automatic keeps the fallback *)
    If[effective[Method] === "Reconstruct" && !AssociationQ[result],
        Return[makeFailure["ReconstructionRejected", "Method -> \"Reconstruct\" was requested, but no exact candidate passed the checks; Method -> Automatic or \"NumericalFit\" returns the numerical fit.",
            <|"Reconstruction" -> result, "NumericalFit" -> <|"Rules" -> Normal[fit], "NumericFit" -> Normal[fit], "ExactCandidates" -> {}, "Normalization" -> target["Anchor"],
                "ProofStatus" -> "NumericalFit", "Evidence" -> <|"Rank" -> rank, "FitResidual" -> N[residual, 5], "Order" -> order, "Samples" -> points["Fit"],
                    "Holdout" -> points["Holdout"], "WorkingPrecision" -> digits, "AchievedAccuracy" -> accuracy, "Reconstruction" -> result|>|>|>]]];
    Which[
        AssociationQ[result], <|"Rules" -> Normal[result["Candidates"]], "NumericFit" -> Normal[fit], "ExactCandidates" -> Normal[result["Candidates"]], "Normalization" -> target["Anchor"],
            "ProofStatus" -> "NumericallyCheckedReconstruction", "Evidence" -> Join[result["Evidence"], <|"Rank" -> rank, "FitResidual" -> N[residual, 5], "Order" -> order,
                "Samples" -> points["Fit"], "Holdout" -> points["Holdout"], "WorkingPrecision" -> digits, "AchievedAccuracy" -> accuracy|>]|>,
        True, <|"Rules" -> Normal[fit], "NumericFit" -> Normal[fit], "ExactCandidates" -> {}, "Normalization" -> target["Anchor"],
            "ProofStatus" -> "NumericalFit", "Evidence" -> <|"Rank" -> rank, "FitResidual" -> N[residual, 5], "Order" -> order, "Samples" -> points["Fit"], "Holdout" -> points["Holdout"],
                "WorkingPrecision" -> digits, "AchievedAccuracy" -> accuracy, "Reconstruction" -> If[MissingQ[result], "NotRequested", result]|>|>]
];

(*
    Summary: Set entries of the S rows that vanish relative to their column's (or the fixed part's) raw magnitude to an
        exact zero.
    Parameters: sys — normalizationSystem; goal — accuracy goal (digits).
    Options/defaults: None.
    Returns: sys with chopped Matrix and RightSide (the exact anchor row is kept).
    Effects: Pure.
    Failures: None.
    Example: for {c E4} every S entry of c's column is a cancellation of size 10^-(goal+10) and becomes 0, so c is fixed by
        the anchor row alone (exactly 1, then reconstructed and verified).
    Remarks: The threshold 10^-(goal+5) times the raw magnitude lies above the series truncation noise and below the rank
        tolerance; without it LeastSquares inherits the few digits left in near-cancelling differences.
    See also: solveNormalization.
*)
chopNormalizationSystem[sys_Association, goal_] := Module[{rows = Most[sys["Matrix"]], rhs = Most[sys["RightSide"]]},
    rows = Map[MapThread[If[Abs[#1] < 10^-(goal + 5) #2, 0, #1] &, {#, sys["ColumnScale"]}] &, rows];
    rhs = Map[If[Abs[#] < 10^-(goal + 5) sys["RightSideScale"], 0, #] &, rhs];
    Join[sys, <|"Matrix" -> Append[rows, Last[sys["Matrix"]]], "RightSide" -> Append[rhs, Last[sys["RightSide"]]]|>]];

(*
    Summary: The automatic series order of the normalization samples.
    Parameters: target — normalizationTarget; goal — accuracy goal; minIm — smallest Im of the sample points and images.
    Options/defaults: None.
    Returns: Integer order: the smallest n at which the weight-k growth n^(k-1) times |q|^n is below 10^-(goal+10), raised
        until the actual tail of the component series (largest coefficient magnitude in the last unit window times
        |q|^e) is below that bound; capped at 600.
    Effects: Extends series caches.
    Failures: As formComponentJets.
    Example: a weight-2 triplet at goal 40 needs about 30; a weight-36 definition at goal 15 needs about 50.
    See also: solveNormalization.
*)
automaticSeriesOrder[target_Association, goal_, minIm_] := Module[{rate = N[2 Pi minIm/Log[10]], k = Max[target["Weight"] - 1, 0], n, tail, jets, parts, bound = goal + 10, step = 0},
    n = Ceiling[bound/rate] + 2;
    Do[n = Ceiling[(bound + k Log10[N[n]])/rate] + 2, {4}];
    While[step < 6 && n < 600, step++;
        jets = formComponentJets[target["Definition"], n]; If[FailureQ[jets], Return[jets, Module]];
        parts = linearParameterParts[jets, target["Parameters"]]; If[FailureQ[parts], Return[parts, Module]];
        tail = Max[Append[Flatten[Map[Function[jet, KeyValueMap[If[#1 >= n - 1 && NumericQ[#2] && #2 != 0, Log10[Abs[N[#2]]] - rate #1, -Infinity] &, jet["Terms"]]],
            Join[parts["Fixed"], Flatten[Values[parts["Parts"]], 1]]]], -Infinity]];
        If[tail <= -bound, Break[]];
        n = Min[600, n + Ceiling[(tail + bound)/rate] + 2]];
    n
];

(*
    Summary: Propose exact algebraic values for fitted unknowns and verify them.
    Parameters: target; fit — <|id -> value|>; points — normalizationPoints; digits; order; goal; accuracy — achieved
        decimal accuracy of the fit (agreement of two series orders).
    Options/defaults: None.
    Returns: <|"Candidates" -> <|id -> exact|>, "Evidence"|> when every candidate passes verification at higher
        precision on the holdout points, else Failure["ReconstructionRejected", ...].
    Effects: Extends series caches.
    Failures: ReconstructionRejected.
    Example: a relative constant 1.7320508... is proposed as Sqrt[3] and verified.
    Remarks: RootApproximant proposes the lowest degree (1 to 8) that reproduces the fit to 90% of its achieved accuracy
        (compared at 20 extra digits with the fit's value, so large candidates are not lost to significance arithmetic)
        with a minimal polynomial of at most half that many digits (candidateHeightDigits), then the law is verified at
        doubled precision on holdout points to 1.5 times the working digits; a proposal is never a proof.
    See also: verifyNormalization.
*)
reconstructNormalization[target_Association, fit_Association, points_Association, digits_, order_, goal_, accuracy_] := Module[{candidates, check},
    (* The lowest degree whose proposal reproduces the fit to most of its digits, then a holdout verification. *)
    candidates = Map[Function[x, If[Abs[x] < 10^-(0.9 accuracy), 0, SelectFirst[Table[Quiet[RootApproximant[x, d]], {d, 1, 8}],
        NumericQ[#] && Precision[#] === Infinity && Abs[N[#, digits + 20] - SetPrecision[x, digits + 20]] < 10^-(0.9 accuracy) && candidateHeightDigits[#] <= accuracy/2 &,
        Missing["NoCandidate"]]]], fit];
    candidates = Map[If[MissingQ[#], #, RootReduce[ToRadicals[#]] // If[LeafCount[ToRadicals[#]] <= LeafCount[#], ToRadicals[#], #] &] &, candidates];
    If[!AllTrue[candidates, NumericQ[#] && Precision[#] === Infinity &], Return[makeFailure["ReconstructionRejected", "No exact candidate was proposed.", <|"Fit" -> fit|>]]];
    (* A true algebraic value satisfies the law far beyond the fit's precision; an approximant does not. *)
    check = automaticSeriesOrder[target, Ceiling[3 digits/2], points["MinimumImaginaryPart"]]; If[FailureQ[check], Return[check]];
    check = verifyNormalization[target, candidates, points["Holdout"], 2 digits, check, Ceiling[3 digits/2]];
    If[FailureQ[check], makeFailure["ReconstructionRejected", "The exact candidates fail the higher-precision holdout check.", <|"Candidates" -> candidates, "Check" -> check|>],
        <|"Candidates" -> candidates, "Evidence" -> check|>]
];

(*
    Summary: The number of decimal digits in the minimal polynomial of an algebraic number.
    Parameters: c — exact algebraic number.
    Options/defaults: None.
    Returns: Total IntegerLength of the minimal polynomial's integer coefficients (Infinity if it cannot be computed in
        10 seconds).
    Effects: Pure.
    Failures: None.
    Example: candidateHeightDigits[3 Sqrt[2]] is 3 (x^2 - 18); a 25-digit fraction has about 50.
    Remarks: A reconstruction is accepted only when this information is well below the fit's precision, so a rational
        approximant of a fitted irrational value is not mistaken for an exact value.
    See also: reconstructNormalization.
*)
candidateHeightDigits[c_] := Module[{poly = Quiet[TimeConstrained[MinimalPolynomial[c, \[FormalX]], 10, $Failed]]},
    If[poly === $Failed || !PolynomialQ[poly, \[FormalX]], Infinity, Total[IntegerLength /@ DeleteCases[CoefficientList[poly, \[FormalX]], 0]]]];

(*
    Summary: Verify candidate values of the unknowns on independent points.
    Parameters: target; values — <|id -> value|>; points — holdout points; digits; order; goal.
    Options/defaults: None.
    Returns: <|"HoldoutResidual", "AnchorResidual", "HoldoutPoints", "VerificationPrecision"|>, or InconsistentNormalization Failure.
    Effects: Extends series caches.
    Failures: InconsistentNormalization.
    Example: exact candidates of the triplet pass with residuals far below 10^-goal.
    See also: reconstructNormalization.
*)
verifyNormalization[target_Association, values_Association, points_List, digits_, order_, goal_] := Module[{sys, x, residual, anchor},
    sys = normalizationSystem[Join[target, <|"Cutoff" -> order|>], points, digits + 10, order]; If[FailureQ[sys], Return[sys]];
    x = N[Lookup[values, target["Parameters"]], digits + 10];
    residual = Max[Abs[Most[sys["Matrix"]] . x - Most[sys["RightSide"]]]];
    anchor = Abs[sys["AnchorRow"] . Lookup[values, target["Parameters"]] - sys["AnchorRightSide"]];
    If[residual > 10^-goal || N[anchor] > 10^-goal, makeFailure["InconsistentNormalization", "The candidate values do not satisfy the transformation law on holdout points.",
        <|"HoldoutResidual" -> N[residual, 5], "AnchorResidual" -> N[anchor, 5]|>],
        <|"HoldoutResidual" -> N[residual, 5], "AnchorResidual" -> N[anchor, 5], "HoldoutPoints" -> points, "VerificationPrecision" -> digits|>]
];

(*
    Summary: The definition and weight on which a form's anchor is stated.
    Parameters: record — form record; anchor — its normalization record.
    Options/defaults: None.
    Returns: {definition, weight}: the frozen source of a derivative, the companion F recipe of a coupled G, or the form's
        own definition and weight.
    Effects: Pure.
    Failures: None.
    Example: for the G seed of a NonCyclic4D family it is the F recipe at weight k0.
    Remarks: Shared by ModularFormGetCoeff and ValidateModularForm, so solving and checking use the same anchor.
    See also: ModularFormGetCoeff; ValidateModularForm.
*)
normalizationSource[record_Association, anchor_Association] := Which[
    KeyExistsQ[anchor, "DerivedSource"], {anchor["DerivedSource"]["Definition"], anchor["DerivedSource"]["Weight"]},
    Lookup[anchor, "AnchorSeed", "F"] === "F" && record["Definition"]["Kind"] === "MLDE" && record["Definition"]["Recipe"]["SeedID"] === "G",
        {Join[record["Definition"], <|"Recipe" -> Join[record["Definition"]["Recipe"], <|"SeedID" -> "F"|>]|>], record["Definition"]["Recipe"]["Weight"]},
    True, {record["Definition"], record["Weight"]}];

Options[SolveModularCoefficients] = Options[ModularFormGetCoeff] = {Method -> Automatic, WorkingPrecision -> 80, AccuracyGoal -> Automatic, SeriesOrder -> Automatic,
    NormalizationRules -> Automatic, RequireProof -> False, Normalization -> Automatic, TimeLimit -> 600, Verification -> Automatic};

(*
    Summary: Relative-normalization coefficients of raw definitions and of forms.
    Status: Alpha.
    Signatures: SolveModularCoefficients[c, r, k, definition, opts]; ModularFormGetCoeff[y, opts]; CoefficientResult[data].
    Parameters: c — Group or RepresentationContext with an S,T assignment; r — Rep bound to c (or an irrep ID); k — weight;
        definition — ModularFormDefinition; y — ModularForm.
    Options/defaults: Method -> Automatic ("NumericalFit", "Reconstruct"; "Exact" is unavailable for these recipes);
        WorkingPrecision -> 80; AccuracyGoal -> Automatic (half the working precision); SeriesOrder -> Automatic;
        NormalizationRules -> Automatic (or explicit rules ID -> value, checked); RequireProof -> False; Normalization ->
        Automatic (an explicit anchor for raw definitions); TimeLimit -> 600; Verification -> Automatic or "Numerical"
        (today's checks; "Exact" is InapplicableOption: no exact identity exists) or None (the fit at one order without
        its stability, residual and holdout checks and without reconstruction: ProofStatus "Unchecked"; explicit
        NormalizationRules are taken unchecked; Method -> "Reconstruct" and RequireProof -> True are InapplicableOption).
    Returns: SolveModularCoefficients: CoefficientResult (nothing is changed). ModularFormGetCoeff: the same y after an
        atomic commit of the coefficient record (aliases see it); Failure leaves y unchanged.
    Effects: ModularFormGetCoeff commits one registry update (revision check) unless the rules, status and evidence are
        all unchanged (then nothing is committed); a changed binding drops a stored normalized QExpansion.
    Failures: As solveNormalization; AnchorUnavailable; IncompatibleAnchor; NonlinearParameters; RevisionConflict;
        TimeLimit; option failures.
    Example: ModularFormGetCoeff[First[ConstructModularForms[c, triplet]]] resolves its two relative constants.
    Remarks: A coefficient-free definition is a no-op (Rules {}, NoNormalizationNeeded); its written scale is kept.
        ProofStatus is explicit: "NumericalFit" or "NumericallyCheckedReconstruction" (or "Proven" only from an exact
        identity, none implemented).
    See also: solveNormalization; ConstructModularForms.
*)
SolveModularCoefficients[c : (_Group | _RepresentationContext), r : (_Rep | _String), k_?modularWeightQ, definition_ModularFormDefinition, options : OptionsPattern[]] := Module[
    {effective, def, ctx, anchor, result},
    effective = resolveOperationOptions[SolveModularCoefficients, "SolveModularCoefficients", {options}]; If[FailureQ[effective], Return[effective]];
    def = validateFormDefinition[definition]; If[FailureQ[def], Return[def]];
    ctx = formContextData[c, r]; If[FailureQ[ctx], Return[ctx]];
    If[def["Parameters"] === {}, Return[CoefficientResult[<|"Rules" -> {}, "ProofStatus" -> "NotApplicable", "Normalization" -> <|"Kind" -> "NoNormalizationNeeded"|>,
        "NumericFit" -> {}, "ExactCandidates" -> {}, "Evidence" -> "No unknowns."|>]]];
    anchor = resolveNormalizationAnchor[def, ctx, effective]; If[FailureQ[anchor], Return[anchor]];
    result = TimeConstrained[solveNormalization[normalizationTarget[def, ctx, k, anchor, 10], effective], effective[TimeLimit],
        makeFailure["TimeLimit", "The normalization did not finish within TimeLimit."]];
    If[FailureQ[result], result, CoefficientResult[result]]
];
SolveModularCoefficients[c : (_Group | _RepresentationContext), i_Integer, rest___] := withIrreps[c, {i}, SolveModularCoefficients[c, #, rest] &];
SolveModularCoefficients[___] := makeFailure["InvalidInput", "SolveModularCoefficients expects a context, a Rep or irrep ID, an exact rational weight, a ModularFormDefinition and options."];

ModularFormGetCoeff[y_ModularForm, options : OptionsPattern[]] := Module[{effective, record, ctx, anchor, result, coefficients, patch, definition, weight},
    effective = resolveOperationOptions[ModularFormGetCoeff, "SolveModularCoefficients", {options}]; If[FailureQ[effective], Return[effective]];
    record = snapshotForm[y]; If[FailureQ[record], Return[record]];
    If[record["Definition"]["Parameters"] === {}, Return[y]];
    anchor = record["Coefficients"];
    If[!AssociationQ[anchor] || anchor["Kind"] =!= "Anchor", Return[makeFailure["AnchorUnavailable", "The form has no normalization anchor."]]];
    ctx = <|"S" -> modularGeneratorMatrix[record["Context"], record["Rep"], "S"], "Dimension" -> record["Dimension"]|>;
    If[FailureQ[ctx["S"]], Return[ctx["S"]]];
    (* A coupled G shares F's anchor and unknowns: it is normalized through the frozen companion F recipe (same family).
       A derived form is normalized through its frozen source recipe and anchor (the rules then apply unchanged). *)
    {definition, weight} = normalizationSource[record, anchor];
    (* The solve sees the anchor convention only (never an earlier result), so evidence does not nest and an identical
       re-solve is recognized. *)
    result = TimeConstrained[solveNormalization[normalizationTarget[definition, ctx, weight,
            Join[KeyDrop[anchor, "Result"], <|"Rules" -> Missing["Unresolved"], "ProofStatus" -> "None"|>], 10], effective], effective[TimeLimit],
        makeFailure["TimeLimit", "The normalization did not finish within TimeLimit."]];
    If[FailureQ[result], Return[result]];
    (* Identical rules, status and evidence: nothing to commit (the stored expansion and the revision stay). New evidence
       for the same rules (another precision or order) is committed; the expansion survives since its binding holds. *)
    If[anchor["Rules"] === result["Rules"] && anchor["ProofStatus"] === result["ProofStatus"] && Lookup[anchor, "Result"] === result, Return[y]];
    coefficients = Join[anchor, <|"Rules" -> result["Rules"], "ProofStatus" -> result["ProofStatus"], "Result" -> result|>];
    (* A stored expansion survives when its binding is raw or already the binding of the new rules. *)
    patch = <|"Coefficients" -> coefficients, "QExpansion" -> If[MatchQ[record["QExpansion"], _QExpansionData] &&
        !MemberQ[{"Raw", "Rules-" <> Hash[result["Rules"], "SHA256", "HexString"]}, record["QExpansion"]["Binding"]], Missing["NotComputed"], record["QExpansion"]]|>;
    With[{committed = commitFormUpdate[record["ID"], record["Revision"], patch]}, If[FailureQ[committed], committed, y]]
];
ModularFormGetCoeff[___] := makeFailure["InvalidInput", "ModularFormGetCoeff expects a ModularForm and options."];

CoefficientResult[data_Association][key_String] := Lookup[data, key, Missing["UnknownProperty", key]];
Format[CoefficientResult[data_Association], StandardForm] := Interpretation[Row[{"CoefficientResult[", Lookup[data, "ProofStatus", "?"], ", ",
    Length[Lookup[data, "Rules", {}]], " rules]"}], CoefficientResult[data]];

True
