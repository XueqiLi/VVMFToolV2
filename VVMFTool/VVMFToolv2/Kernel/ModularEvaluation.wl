(*
    :Title: Evaluation and validation of modular forms
    :Context: VVMFTool`Private`
    :Summary: Points in the upper half plane (TauPoint, QPoint with an explicit logarithm sheet), adaptive q-series
        evaluation with an error estimate from successive orders (never a tail bound), scalar evaluation, numerical S and
        exact T checks, and the read-only validation report.
    :Responsibilities: resolveModularPoint, adaptiveSeriesValue, evaluateModularRecipe, checkModularTransformations,
        exactTCheck; TauPoint, QPoint, ModularFormEvaluate, EvaluateScalarModular, ValidateModularForm.
    :Dependencies: ModularOperations.wl (expandForm, recordContextData); ModularNormalization.wl (formComponentJets,
        evaluateComponentJets); ModularScalars.wl (treeSeries).
    :See Also: VVMFArch/step7Plan.md (evaluation contract, validation).
*)

(*
    Summary: Resolve an evaluation point.
    Parameters: point — TauPoint[tau] or QPoint[q, sheet].
    Options/defaults: QPoint sheet 0.
    Returns: <|"Tau", "Branch" -> "Tau" | "Sheet" -> n, "Cusp" -> False|>, <|"Cusp" -> True|> for QPoint[0], or Failure.
    Effects: Pure.
    Failures: OutsideDomain (Im tau <= 0; |q| >= 1); InvalidPoint.
    Example: QPoint[q, 1] has tau = (Log[q] + 2 Pi I)/(2 Pi I), not the principal tau.
    Remarks: Equal q on different sheets are different points: fractional powers use Exp[2 Pi I tau r], never a principal
        power of q (needed for T covariance).
    See also: ModularFormEvaluate.
*)
resolveModularPoint[TauPoint[tau_]] := If[NumericQ[tau] && TrueQ[Im[tau] > 0], <|"Tau" -> tau, "Branch" -> "Tau", "Cusp" -> False|>,
    makeFailure["OutsideDomain", "A TauPoint needs Im(tau) > 0.", <|"Point" -> tau|>]];
resolveModularPoint[QPoint[q_, sheet_Integer : 0]] := Which[
    q === 0, <|"Cusp" -> True, "Branch" -> "Cusp"|>,
    NumericQ[q] && TrueQ[0 < Abs[q] < 1], <|"Tau" -> (Log[q] + 2 Pi I sheet)/(2 Pi I), "Branch" -> <|"Sheet" -> sheet|>, "Cusp" -> False|>,
    True, makeFailure["OutsideDomain", "A QPoint needs 0 < |q| < 1 (or the exact cusp q = 0).", <|"Point" -> q|>]];
resolveModularPoint[other_] := makeFailure["InvalidPoint", "Points are TauPoint[tau] or QPoint[q, sheet].", <|"Point" -> other|>];

(*
    Summary: Adaptive evaluation of series at a point.
    Parameters: getJets — function of a cutoff returning component jets (or Failure); tau — point; settings —
        <|"Digits", "Goal" (accuracy goal), "PrecisionGoal", "Max", "Explicit" (an explicit SeriesOrder)|>.
    Options/defaults: None.
    Returns: <|"Value", "Previous", "Order", "EstimatedError", "Converged" -> True|> (two successive orders differ by at most
        Max[10^-Goal, 10^-PrecisionGoal |value|]; Previous is the earlier approximation);
        for an explicit order <|"Value", "Previous" (the value at the next longer order, or Missing for a finite jet),
        "Order", "EstimatedError" (Missing["NoTailBound"] for a finite jet), "Converged" -> False|>; or Failure.
    Effects: Uses temporary series only (no record changes).
    Failures: ConvergenceFailure (MaxSeriesOrder reached, with the best estimate); FiniteJet (a finite jet without an
        explicit SeriesOrder); series failures.
    Example: E4 at tau = I converges in a few dozen terms to 50 digits.
    Remarks: Agreement of successive approximations is a numerical error estimate, not a rigorous tail bound.
    See also: ModularFormEvaluate; EvaluateScalarModular.
*)
adaptiveSeriesValue[getJets_, tau_, settings_Association] := Module[{qabs = N[Abs[Exp[2 Pi I tau]], 20], step, n, previous, current, jets, digits = settings["Digits"]},
    step = Max[2, Ceiling[5/Max[-Log10[qabs], 10^-3]]];
    n = Replace[settings["Explicit"], Automatic -> Min[settings["Max"], Max[2, Ceiling[(settings["Goal"] + 5)/Max[-Log10[qabs], 10^-3]]]]];
    jets = getJets[n];
    If[FailureQ[jets] && First[jets] === "InsufficientOrder",
        Return[If[settings["Explicit"] === Automatic, makeFailure["FiniteJet", "A finite jet cannot support adaptive accuracy; give an explicit SeriesOrder for a truncated value.",
            Last[jets]], jets]]];
    If[FailureQ[jets], Return[jets]];
    current = evaluateComponentJets[jets, tau, digits];
    If[!AllTrue[current, NumericQ], Return[makeFailure["SymbolicCoefficients", "The series has non-numeric coefficients; it cannot be evaluated numerically."]]];
    If[settings["Explicit"] =!= Automatic,
        With[{longer = getJets[n + step]}, If[FailureQ[longer],
            Return[<|"Value" -> current, "Previous" -> Missing["NoTailBound"], "Order" -> n, "EstimatedError" -> Missing["NoTailBound"], "Converged" -> False|>],
            With[{other = evaluateComponentJets[longer, tau, digits]},
                Return[<|"Value" -> current, "Previous" -> other, "Order" -> n, "EstimatedError" -> N[Max[Abs[other - current]], 5], "Converged" -> False|>]]]]];
    While[True,
        previous = current; n = n + step;
        If[n > settings["Max"], Return[makeFailure["ConvergenceFailure", "The series did not converge to the accuracy goal within MaxSeriesOrder.",
            <|"BestEstimate" -> previous, "Order" -> n - step|>]]];
        jets = getJets[n]; If[FailureQ[jets], Return[jets]];
        current = evaluateComponentJets[jets, tau, digits];
        (* The standard criterion: absolute error below 10^-AccuracyGoal or relative error below 10^-PrecisionGoal. *)
        If[Max[Abs[current - previous]] <= Max[10^-settings["Goal"], 10^-settings["PrecisionGoal"] Max[Abs[current]]],
            Return[<|"Value" -> current, "Previous" -> previous, "Order" -> n, "EstimatedError" -> N[Max[Abs[current - previous]], 5], "Converged" -> True|>]]]
];

(*
    Summary: Evaluate a recipe at a point by the selected method.
    Parameters: getJets — cutoff -> jets; point — resolved point; effective — validated evaluation options.
    Options/defaults: Method Automatic or "QSeries"; "Analytic" is unavailable (no branch-continuation route is
        implemented; principal hypergeometric branches outside the cusp chart are not an analytic evaluator).
    Returns: Evaluation record (with the internal "Previous" approximation, dropped by the public evaluators), or Failure.
    Effects: Temporary series only.
    Failures: MethodUnavailable; Pole (a negative leading exponent at the cusp); as adaptiveSeriesValue.
    Example: the cusp QPoint[0] of E4 is {1}.
    See also: adaptiveSeriesValue.
*)
evaluateModularRecipe[getJets_, point_Association, effective_Association] := Module[{digits = effective[WorkingPrecision], goal, precisionGoal, result, jets},
    If[effective[Method] === "Analytic", Return[makeFailure["MethodUnavailable", "No analytic branch-continuation evaluator is implemented; use Automatic or \"QSeries\"."]]];
    goal = Replace[effective[AccuracyGoal], Automatic -> Floor[digits/2]];
    precisionGoal = Replace[effective[PrecisionGoal], Automatic -> Floor[digits/2]];
    If[point["Cusp"],
        jets = getJets[1]; If[FailureQ[jets], Return[jets]];
        If[AnyTrue[jets, AnyTrue[Keys[#["Terms"]], Negative] &], Return[makeFailure["Pole", "A component has a negative leading exponent: the cusp value is infinite."]]];
        Return[<|"Value" -> Map[Lookup[#["Terms"], 0, 0] &, jets], "Previous" -> Map[Lookup[#["Terms"], 0, 0] &, jets], "WorkingPrecision" -> Infinity, "EstimatedError" -> 0, "Method" -> "CuspLimit", "Order" -> 1,
            "Branch" -> "Cusp", "Converged" -> True|>]];
    result = adaptiveSeriesValue[getJets, point["Tau"], <|"Digits" -> digits + 10, "Goal" -> goal, "PrecisionGoal" -> precisionGoal, "Explicit" -> effective[SeriesOrder],
        "Max" -> effective[MaxSeriesOrder]|>];
    If[FailureQ[result], result, Join[KeyDrop[result, "Converged"], <|"Value" -> SetPrecision[result["Value"], digits],
        "Previous" -> If[ListQ[result["Previous"]], SetPrecision[result["Previous"], digits], result["Previous"]], "WorkingPrecision" -> digits, "AccuracyGoal" -> goal,
        "PrecisionGoal" -> precisionGoal,
        "Method" -> "QSeries", "Branch" -> point["Branch"], "Tau" -> point["Tau"], "Converged" -> result["Converged"]|>]]
];

Options[ModularFormEvaluate] = {Method -> Automatic, WorkingPrecision -> 80, AccuracyGoal -> Automatic, PrecisionGoal -> Automatic, SeriesOrder -> Automatic,
    MaxSeriesOrder -> 2000, TimeLimit -> 600, ApplyCoefficients -> True};
Options[EvaluateScalarModular] = Join[Options[ModularFormEvaluate], {Coordinate -> "q"}];

(*
    Summary: Numerical values of modular forms and scalar modular expressions.
    Status: Alpha.
    Signatures: ModularFormEvaluate[y, point, opts]; EvaluateScalarModular[expr, var, point, opts].
    Parameters: y — ModularForm; expr — scalar expression in var and scalar ingredients; point — TauPoint[tau] or
        QPoint[q, sheet].
    Options/defaults: Method -> Automatic ("QSeries"; "Analytic" unavailable); WorkingPrecision -> 80; AccuracyGoal and
        PrecisionGoal -> Automatic (Floor[WorkingPrecision/2]; converged when successive orders differ by at most
        10^-AccuracyGoal or 10^-PrecisionGoal relative to the value); SeriesOrder -> Automatic (adaptive) or an explicit order
        (needed for finite jets); MaxSeriesOrder -> 2000; TimeLimit -> 600; ApplyCoefficients -> True.
    Returns: <|"Value" (component vector, or scalar), "WorkingPrecision", "AccuracyGoal", "PrecisionGoal", "EstimatedError", "Method",
        "Order", "Branch", "Tau", "Converged", "ValidationStatus"|>, or Failure.
    Effects: Read-only: the stored QExpansion and the registry are never changed.
    Failures: OutsideDomain; InvalidPoint; MethodUnavailable; ConvergenceFailure; FiniteJet; Pole;
        UnresolvedCoefficients; TimeLimit; option failures.
    Example: ModularFormEvaluate[y, TauPoint[1/7 + 6 I/5], WorkingPrecision -> 70]["Value"].
    Remarks: EstimatedError is the agreement of successive orders (or Missing["NoTailBound"] for an explicit truncation),
        never a certified bound.
    See also: evaluateModularRecipe; adaptiveSeriesValue.
*)
ModularFormEvaluate[y_ModularForm, point_, options : OptionsPattern[]] := Module[{effective, record, resolved, rules, result},
    effective = resolveOperationOptions[ModularFormEvaluate, "ModularFormEvaluate", {options}]; If[FailureQ[effective], Return[effective]];
    record = snapshotForm[y]; If[FailureQ[record], Return[record]];
    resolved = resolveModularPoint[point]; If[FailureQ[resolved], Return[resolved]];
    If[MissingQ[expansionBinding[record, effective[ApplyCoefficients]]], Return[makeFailure["UnresolvedCoefficients",
        "The form's relative coefficients are not resolved; use ModularFormGetCoeff first."]]];
    If[expansionBinding[record, effective[ApplyCoefficients]] === "Raw", Return[makeFailure["SymbolicCoefficients",
        "A numerical value needs numeric coefficients; the raw definition keeps its unknowns (use ModularFormExpression or ModularFormQExp with ApplyCoefficients -> False)."]]];
    rules = If[TrueQ[effective[ApplyCoefficients]] && ListQ[Lookup[Replace[record["Coefficients"], _Missing -> <||>], "Rules", None]],
        Map[FormParameter[First[#]] -> Last[#] &, record["Coefficients"]["Rules"]], {}];
    result = TimeConstrained[evaluateModularRecipe[Function[n, With[{jets = formComponentJets[record["Definition"], n]},
            If[FailureQ[jets], jets, Map[makeJet[Map[Expand[# /. rules] &, #["Terms"]], #["Cutoff"]] &, jets]]]], resolved, effective],
        effective[TimeLimit], makeFailure["TimeLimit", "The evaluation did not finish within TimeLimit."]];
    If[FailureQ[result], result, Join[KeyDrop[result, "Previous"], <|"ValidationStatus" -> record["Validation"]["Status"],
        "VerificationStatus" -> formVerificationStatus[record]|>]]
];
ModularFormEvaluate[___] := makeFailure["InvalidInput", "ModularFormEvaluate expects a ModularForm, a TauPoint or QPoint and options."];

EvaluateScalarModular[expr_, var_Symbol, point_, options : OptionsPattern[]] := Module[{effective, resolved, tree, bad, result},
    effective = resolveOperationOptions[EvaluateScalarModular, "EvaluateScalarModular", {options}]; If[FailureQ[effective], Return[effective]];
    resolved = resolveModularPoint[point]; If[FailureQ[resolved], Return[resolved]];
    tree = expr /. {var -> FormVariable[effective[Coordinate]], ModularScalarNode[nm_, var, c_] :> ModularScalarNode[nm, FormVariable[c], c],
        HypergeometricKNode[a_, b_, var, c_] :> HypergeometricKNode[a, b, FormVariable[c], c]};
    bad = DeleteDuplicates[Flatten[definitionTreeViolations /@ Flatten[{tree}]]];
    If[bad =!= {}, Return[makeFailure["UndeclaredSymbol", "The expression may only contain its variable, numeric constants and scalar ingredients.", <|"Expressions" -> bad|>]]];
    result = TimeConstrained[evaluateModularRecipe[Function[n, With[{jet = treeSeries[tree, n]}, If[FailureQ[jet], jet, {jetTruncate[jet, n]}]]], resolved, effective],
        effective[TimeLimit], makeFailure["TimeLimit", "The evaluation did not finish within TimeLimit."]];
    If[FailureQ[result], result, Join[KeyDrop[result, "Previous"], <|"Value" -> First[result["Value"]]|>]]
];
EvaluateScalarModular[___] := makeFailure["InvalidInput", "EvaluateScalarModular expects an expression, a variable symbol, a point and options."];

(*
    Summary: Exact T check of an expansion: each exponent's coefficient vector is an eigenvector of rho(T).
    Parameters: jets — stored-basis component series (numeric coefficients); t — rho(T).
    Options/defaults: None.
    Returns: <|"Status" -> "ExactThroughOrder" | "Failed" | "NotAvailable", "Order", "FailedExponents"|>.
    Effects: Pure.
    Failures: None.
    Example: a T'-triplet form passes through its expansion order.
    Remarks: F(tau + 1) = rho(T) F(tau) termwise means rho(T) v_e = Exp[2 Pi I e] v_e for every exponent e; checked exactly
        (RootReduce) for exact data, to the data's precision otherwise. It covers the known coefficients only.
    See also: ValidateModularForm.
*)
exactTCheck[jets_List, t_?MatrixQ] := Module[{exponents = Union[Flatten[Keys /@ Lookup[jets, "Terms"]]], failed},
    If[!FreeQ[Lookup[jets, "Terms"], _FormParameter], Return[<|"Status" -> "NotAvailable", "Reason" -> "UnresolvedCoefficients"|>]];
    failed = Select[exponents, Function[e, With[{v = Map[Lookup[#["Terms"], e, 0] &, jets]},
        With[{r = t . v - Exp[2 Pi I e] v}, If[inexactDataQ[{t, v}], Max[Abs[N[r]]] > 10^-(Max[10, dataPrecision[{t, v}] /. MachinePrecision -> 16] - 5),
            !AllTrue[r, TrueQ[Quiet[TimeConstrained[RootReduce[#], 30, $Failed]] === 0] &]]]]]];
    <|"Status" -> If[failed === {}, If[inexactDataQ[{t, Lookup[jets, "Terms"]}], "NumericalThroughOrder", "ExactThroughOrder"], "Failed"],
        "Order" -> Min[Lookup[jets, "Cutoff"]], "FailedExponents" -> failed|>
];

(*
    Summary: Numerical S (and T) transformation residuals of a form at independent points.
    Parameters: record; rules — coefficient rules; points; digits; order.
    Options/defaults: None.
    Returns: <|"Status" -> "Numerical", "SResidual", "TResidual" (5 digits), "Points", "Order", "ResidualValues" (unrounded)|>, or Failure.
    Effects: Temporary series only.
    Failures: Series failures.
    Example: a normalized T' triplet has S residuals near the working precision.
    Remarks: Samples test the law in the recorded basis; they never prove a global identity.
    See also: ValidateModularForm.
*)
checkModularTransformations[record_Association, rules_List, points_List, digits_, order_] := Module[{jets, s, t, k = record["Weight"], sres, tres},
    jets = formComponentJets[record["Definition"], order]; If[FailureQ[jets], Return[jets]];
    jets = Map[makeJet[Map[Expand[# /. rules] &, #["Terms"]], #["Cutoff"]] &, jets];
    s = modularGeneratorMatrix[record["Context"], record["Rep"], "S"]; t = modularGeneratorMatrix[record["Context"], record["Rep"], "T"];
    sres = Max[Map[Max[Abs[evaluateComponentJets[jets, -1/#, digits] - N[(-#)^k, digits] (s . evaluateComponentJets[jets, #, digits])]] &, points]];
    tres = Max[Map[Max[Abs[evaluateComponentJets[jets, # + 1, digits] - t . evaluateComponentJets[jets, #, digits]]] &, points]];
    <|"Status" -> "Numerical", "SResidual" -> N[sres, 5], "TResidual" -> N[tres, 5], "Points" -> points, "Order" -> order,
        "ResidualValues" -> {sres, tres}|>
];

Options[ValidateModularForm] = {RequireProof -> False, WorkingPrecision -> 40, SeriesOrder -> Automatic, Verification -> Automatic};

(*
    Summary: A report of the evidence for a modular form.
    Status: Alpha.
    Parameters: y — ModularForm.
    Options/defaults: RequireProof -> False (True: Failure unless every check is a proof); WorkingPrecision -> 40;
        SeriesOrder -> Automatic (expansion order of the checks: 6 for the exact T and normalization checks; for the
        S/T sampling the order covering the weight growth and the series tail at the validation points, goal
        WorkingPrecision/2; an explicit order is used for every check); Verification -> Automatic or "Numerical" (the same
        checks; "Exact" is InapplicableOption, None InvalidOption).
    Returns: <|"Checks" -> <|"RecordBinding", "Dimension", "Parity", "TExpansion", "Recipe", "Normalization",
        "STransformation"|> each with its status ("Proven", "ExactThroughOrder", "Numerical", "NotAvailable", "Failed")
        and data, "ProofStatus" -> "Proven" | "NumericalEvidence" | "Incomplete" | "Failed", "Remedies",
        "VerificationStatus" ("Exact" | "Numerical" | "Unverified")|>, or Failure.
    Effects: Temporary expansions, no group changes; a "Proven" or "NumericalEvidence" result is recorded in the form's
        Validation "Status" at the same revision (commitFormValidation; it survives saving; new coefficients reset it).
    Failures: UnknownModularForm; ProofRequired (RequireProof with a non-proof report).
    Example: ValidateModularForm[y]["ProofStatus"] is "NumericalEvidence" for a normalized constructed form.
    Remarks: Exact T coefficients, MLDE residuals and finitely many samples are evidence through an order or at points,
        never a proof of a global identity; a missing coefficient, a finite jet or an unsupported route names its remedy.
    See also: exactTCheck; checkModularTransformations.
*)
ValidateModularForm[y_ModularForm, options : OptionsPattern[]] := Module[{effective, record, checks = <||>, order, ctx, jets, rules, remedies = {}, status, binding},
    effective = resolveOperationOptions[ValidateModularForm, "ValidateModularForm", {options}]; If[FailureQ[effective], Return[effective]];
    (* the checks are evidence at points and through orders: there is no exact route ("Exact" is InapplicableOption,
       methodOptionsPlan.md 2C.4); "Numerical" is the Automatic checks *)
    If[effective[Verification] === "Exact", Return[makeFailure["InapplicableOption",
        "ValidateModularForm has no exact proof route (sampled S checks, exact T coefficients through an order); use Automatic or \"Numerical\".", <|"Options" -> {Verification}|>]]];
    With[{allowed = checkLevelQ["ValidateModularForm", effective[Verification], False]}, If[FailureQ[allowed], Return[allowed]]];
    record = snapshotForm[y]; If[FailureQ[record], Return[record]];
    order = Replace[effective[SeriesOrder], Automatic -> 6];
    binding = validateFormRecord[record];
    ctx = recordContextData[record];
    checks["RecordBinding"] = <|"Status" -> If[FailureQ[binding] || FailureQ[ctx], "Failed", "Proven"]|>;
    If[FailureQ[ctx], Return[<|"Checks" -> checks, "ProofStatus" -> "Failed", "Remedies" -> {"The form's frozen context is not bound in this kernel."}|>]];
    checks["Dimension"] = <|"Status" -> If[ctx["Dimension"] === record["Dimension"], "Proven", "Failed"]|>;
    checks["Parity"] = <|"Status" -> Switch[formParityQ[ctx["S"], record["Weight"]], True, If[inexactDataQ[ctx["S"]], "Numerical", "Proven"], False, "Failed", _, "NotAvailable"]|>;
    rules = If[ListQ[Lookup[Replace[record["Coefficients"], _Missing -> <||>], "Rules", None]], Map[FormParameter[First[#]] -> Last[#] &, record["Coefficients"]["Rules"]], {}];
    jets = formComponentJets[record["Definition"], order];
    If[FailureQ[jets],
        checks["TExpansion"] = <|"Status" -> "NotAvailable", "Reason" -> First[jets]|>; AppendTo[remedies, "The expansion is unavailable: " <> Last[jets]["MessageTemplate"]],
        jets = Map[makeJet[Map[Expand[# /. rules] &, #["Terms"]], #["Cutoff"]] &, jets];
        checks["TExpansion"] = exactTCheck[jets, ctx["T"]]];
    checks["Recipe"] = Which[
        record["Definition"]["Kind"] === "MLDE", With[{recipe = record["Definition"]["Recipe"]}, With[{v = validateMLDEResidual[mldeSystem[recipe["System"]], recipe["Coefficients"],
            recipe["Solution"], recipe["Weight"]]}, If[FailureQ[v], <|"Status" -> "Failed"|>, <|"Status" -> "ExactThroughOrder", "ZeroThrough" -> v["ZeroThrough"]|>]]],
        KeyExistsQ[record["Validation"], "RecipeEvidence"], <|"Status" -> "ExactThroughOrder", "Evidence" -> record["Validation"]["RecipeEvidence"]|>,
        True, <|"Status" -> "NotAvailable", "Reason" -> "No recipe evidence (manual or derived form)."|>];
    checks["Normalization"] = Which[
        !AssociationQ[record["Coefficients"]], AppendTo[remedies, "Resolve the coefficients with ModularFormGetCoeff."]; <|"Status" -> "NotAvailable"|>,
        record["Coefficients"]["Kind"] === "NoNormalizationNeeded", <|"Status" -> "Proven", "Kind" -> "NoNormalizationNeeded"|>,
        !ListQ[record["Coefficients"]["Rules"]], AppendTo[remedies, "Resolve the coefficients with ModularFormGetCoeff."]; <|"Status" -> "NotAvailable"|>,
        FailureQ[jets], <|"Status" -> "NotAvailable"|>,
        (* The anchor is stated on the normalization source (companion F of a coupled G, the source of a derivative). *)
        True, With[{a = record["Coefficients"], frame = transportSeries[record["Coefficients"]["FrameFromStored"],
                Map[makeJet[Map[Expand[# /. rules] &, #["Terms"]], #["Cutoff"]] &, formComponentJets[First[normalizationSource[record, record["Coefficients"]]], order]]]},
            (* an exact zero is a proof; a numerical agreement is numerical evidence, never "Proven" (methodOptionsPlan.md 2C.3) *)
            With[{value = Lookup[frame[[a["Component"]]]["Terms"], a["Exponent"], 0]}, <|"Status" -> Which[TrueQ[RootReduce[value - a["Value"]] == 0], "Proven",
                TrueQ[Abs[N[value - a["Value"]]] < 10^-20], "Numerical", True, "Failed"], "AnchorValue" -> value, "CoefficientStatus" -> a["ProofStatus"]|>]]];
    checks["STransformation"] = If[!MissingQ[expansionBinding[record, True]],
        (* An explicit SeriesOrder reaches the S/T check; otherwise the order covers the weight growth and the series tail. *)
        With[{c = With[{sOrder = Replace[effective[SeriesOrder], Automatic :> automaticSeriesOrder[<|"Definition" -> record["Definition"],
                    "Parameters" -> Lookup[record["Definition"]["Parameters"], "ID", {}], "Weight" -> record["Weight"]|>, Ceiling[effective[WorkingPrecision]/2],
                    Min[Im /@ Join[$ValidationPoints, -1/$ValidationPoints]]]]},
                If[FailureQ[sOrder], sOrder, checkModularTransformations[record, rules, $ValidationPoints, effective[WorkingPrecision], sOrder]]]},
            If[FailureQ[c], <|"Status" -> "NotAvailable", "Reason" -> First[c]|>,
            (* A residual above the threshold that still changes with five more terms is truncation, not a violated law;
               residuals are compared unrounded. A finite jet that cannot be sampled five terms further gives no verdict. *)
            With[{passed = Max[c["ResidualValues"]] < 10^-(effective[WorkingPrecision]/2),
                    resolved = AllTrue[c["ResidualValues"], Accuracy[#] >= effective[WorkingPrecision]/2 &]},
            With[{longer = If[passed || !resolved, None, checkModularTransformations[record, rules, $ValidationPoints, effective[WorkingPrecision], c["Order"] + 5]]},
                Which[
                    passed, Join[KeyDrop[c, "ResidualValues"], <|"Points" -> $ValidationPoints, "Status" -> "Numerical"|>],
                    (* A residual whose accuracy cannot resolve the threshold (data of fewer digits) gives no verdict. *)
                    !resolved, AppendTo[remedies, "The S/T residual cannot resolve 10^-(WorkingPrecision/2) with the data's precision: lower WorkingPrecision to the data's digits."];
                        Join[KeyDrop[c, "ResidualValues"], <|"Points" -> $ValidationPoints, "Status" -> "NotAvailable", "Reason" -> "InsufficientPrecision"|>],
                    FailureQ[longer], AppendTo[remedies, "The S/T samples at order " <> ToString[c["Order"]] <> " are above the threshold and the series is not known five terms further; sample at a lower order with fewer digits (WorkingPrecision) or supply more terms."];
                        Join[KeyDrop[c, "ResidualValues"], <|"Points" -> $ValidationPoints, "Status" -> "NotAvailable", "Reason" -> "InsufficientOrder"|>],
                    (* Truncation when the residual is within ten times its change under five more terms; a residual that
                       stays far above the threshold relative to its change is a violated law. *)
                    First[c["ResidualValues"]] - 10 Abs[First[longer["ResidualValues"]] - First[c["ResidualValues"]]] <= 10^-(effective[WorkingPrecision]/2),
                        AppendTo[remedies, "The S/T samples are truncation-limited at order " <> ToString[c["Order"]] <> ": raise SeriesOrder (or use SeriesOrder -> Automatic) or lower WorkingPrecision."];
                        Join[KeyDrop[c, "ResidualValues"], <|"Points" -> $ValidationPoints, "Status" -> "NotAvailable", "Reason" -> "SeriesOrderTooLow", "LongerOrderSResidual" -> longer["SResidual"]|>],
                    True, Join[KeyDrop[c, "ResidualValues"], <|"Points" -> $ValidationPoints, "Status" -> "Failed"|>]]]]]],
        <|"Status" -> "NotAvailable", "Reason" -> "UnresolvedCoefficients"|>];
    status = Which[MemberQ[Lookup[Values[checks], "Status"], "Failed"], "Failed", AllTrue[Values[checks], #["Status"] === "Proven" &], "Proven",
        MemberQ[Lookup[Values[checks], "Status"], "NotAvailable"], "Incomplete", True, "NumericalEvidence"];
    If[TrueQ[effective[RequireProof]] && status =!= "Proven", Return[makeFailure["ProofRequired", "The validation report is not a proof (exact checks through an order and numerical samples only).",
        <|"ProofStatus" -> status|>]]];
    (* write-back (methodOptionsPlan.md 2C.3; user decision 2026-10-13): the result is recorded in the form itself, for
       this revision, without a new revision (bindings pin forms by revision) *)
    If[MemberQ[{"Proven", "NumericalEvidence"}, status],
        With[{committed = commitFormValidation[record["ID"], record["Revision"], status]}, If[AssociationQ[committed], record = committed]]];
    <|"Checks" -> checks, "ProofStatus" -> status, "Remedies" -> DeleteDuplicates[remedies], "VerificationStatus" -> formVerificationStatus[record]|>
];

(*
    Summary: The verification status of a modular form record (methodOptionsPlan.md 2C.1, 2C.2).
    Parameters: record — form record (snapshotForm); status — a stored validation status.
    Options/defaults: Stored values map: Validation "Proven" -> "Exact", "NumericalEvidence" -> "Numerical", anything else
        (new forms "Unverified", "Incomplete", "Failed", archived) -> "Unverified"; Coefficients ProofStatus NumericalFit,
        NumericallyChecked*, NumericalExplicitRules -> "Numerical", ArchivedUnverified -> "Unverified", others no bound;
        the frozen context's group and basis-variant statuses bound it (formContextStatus).
    Returns: "Exact" | "Numerical" | "Unverified".
    Effects: Pure.
    Failures: None.
    Example: formVerificationStatus of a new constructed form is "Unverified".
    See also: ValidateModularForm.
*)
formValidationStatusRank[status_] := Switch[status, "Proven", "Exact", "NumericalEvidence", "Numerical", _, "Unverified"];
formVerificationStatus[record_Association] := cgWeakestStatus[{
    (* the stored validation status (ValidateModularForm records its result in the form) *)
    formValidationStatusRank[Lookup[Lookup[record, "Validation", <||>], "Status", "Unverified"]],
    With[{coefficients = Lookup[record, "Coefficients", None]},
        If[!AssociationQ[coefficients], "Exact", Switch[Lookup[coefficients, "ProofStatus", None],
            "NumericalFit" | "NumericallyCheckedReconstruction" | "NumericallyCheckedExplicitRules" | "NumericalExplicitRules", "Numerical",
            (* nothing to resolve, unresolved (the form's own status bounds it) or an exact proof *)
            "NotApplicable" | "None" | "Proven", "Exact",
            (* "ArchivedUnverified", "Unchecked" (Verification -> None) and any word not listed here *)
            _, "Unverified"]]],
    (* bounded by the frozen context (methodOptionsPlan.md 2C.2, 2C.6): the group's status and the form's basis variant *)
    formContextStatus[record]}];
(* The status of a form's frozen context: the group's and that of the irrep variant whose identity is the form's basis
   (the active one when none matches); "Exact" for a record without a context (an archive record before rebinding). *)
formContextStatus[record_Association] := With[{snapshot = Replace[Lookup[record, "Context", None], {c_RepresentationContext :> First[c], g_Group :> groupData[g], _ -> None}]},
    If[!AssociationQ[snapshot], "Exact",
        With[{id = Lookup[record, "IrrepID", None]},
            cgWeakestStatus[{groupVerificationStatus[snapshot],
                If[!StringQ[id], "Exact", With[{variants = Lookup[Lookup[Lookup[snapshot, "Representations", <||>], id, <||>], "Variants", <||>]},
                    variantVerificationStatus[SelectFirst[Values[variants], Lookup[#, "Identity", None] === Lookup[record, "BasisID", None] &,
                        cgVariant[snapshot, id]]]]]}]]]];
formVerificationStatus[_] := "Unverified";
ValidateModularForm[___] := makeFailure["InvalidInput", "ValidateModularForm expects a ModularForm and options."];

Format[p : TauPoint[tau_], StandardForm] := Interpretation[Row[{"TauPoint[", tau, "]"}], p];

True
