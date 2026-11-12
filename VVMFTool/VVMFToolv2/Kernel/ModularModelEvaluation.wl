(*
    :Title: Validation and evaluation of modular models
    :Context: VVMFTool`Private`
    :Summary: The three-layer report of a modular model (schema and identities; formal covariance and total weight;
        actual binding completeness, membership and independence evidence, kept separate), entrywise modular weights of
        extracted matrices, and numerical evaluation of model expressions and matrices at a point with each bound slot
        evaluated once from its frozen record.
    :Responsibilities: validateModularModelChecks, entryWeights, validateModularMassData, resolveModularModelInputs,
        evaluateFrozenForm, evaluateBoundSlots, evaluateModularOutput; ValidateModularModel, EvaluateModularModel,
        EvaluateModularMassMatrix.
    :Dependencies: ModularModels.wl; ModularBindings.wl; ModularEvaluation.wl (evaluateModularRecipe, resolveModularPoint);
        ModularNormalization.wl (formComponentJets); MassMatrices.wl (ValidateMassMatrix).
    :See Also: VVMFArch/step8Plan.md (validation, matrices and evaluation); D-S8-7, D-S8-8.
*)

(*
    Summary: The layered validation report of a modular model.
    Parameters: model — validated modular model data; m — the Model value; level — the formal checks' Verification (default
        Automatic).
    Options/defaults: None.
    Returns: <|"ModelID", "Schema" -> "Valid", "Formal" -> <|"Covariant", "Status", "Arithmetic", "ModularWeight",
        "SuperpotentialWeight", "VerificationStatus"|>, "Binding" -> <|"Status", "Slots" (slot -> bound, form, revision,
        Stage 7 proof status, verification status), "Unbound", "Spaces" (space -> coverage and independence evidence)|>,
        "Proven" -> Boolean, "VerificationStatus" (weakest of the formal status and the bound forms)|>, or Failure.
    Effects: Pure.
    Failures: ValidateModel failures.
    Example: an unbound L.R.Y model reports Formal "Covariant", Binding "Unbound" and Proven False.
    Remarks: Formal covariance (exact or numerical) and analytic binding evidence are separate axes: an unbound symbolic Y
        never upgrades a numerical residual, and the (exact rational) weight bookkeeping is exact independently. Proven needs exact
        formal covariance, homogeneous weights, every used slot bound with full independent coverage and every bound
        form's Stage 7 report "Proven".
    See also: ValidateModularModel; bindingStatus.
*)
validateModularModelChecks[model_Association, m_Model, level_ : Automatic] := Module[{formal = ValidateModel[m, Verification -> level], md = model["ModularData"], used, slots, spaces},
    If[FailureQ[formal], Return[formal]];
    used = Keys[md["Slots"]];
    slots = AssociationMap[Function[sid, With[{b = Lookup[md["Bindings"], sid, Missing[]]}, If[MissingQ[b], <|"Bound" -> False|>,
        <|"Bound" -> True, "FormID" -> b["FormID"], "Revision" -> b["Revision"], "Kind" -> b["Kind"], "ProofStatus" -> b["Validation"]["ProofStatus"],
            "VerificationStatus" -> bindingVerificationStatus[b]|>]]], used];
    spaces = AssociationMap[Function[sid, Join[KeyTake[First[Select[Values[md["Slots"]], #["SpaceID"] === sid &]], {"IrrepID", "Weight", "SpaceDimension"}],
        <|"Established" -> If[KeyExistsQ[Lookup[md, "SuppliedSpaces", <||>], sid], "Supplied", "StageSeven"]|>,
        Lookup[Lookup[md, "BindingEvidence", <||>], sid, <|"Bound" -> 0, "Coverage" -> "None"|>]]], DeleteDuplicates[Lookup[Values[md["Slots"]], "SpaceID", {}]]];
    <|"ModelID" -> model["ID"], "Schema" -> "Valid",
        "Formal" -> <|"Covariant" -> formal["Covariant"], "Status" -> formal["Status"], "Arithmetic" -> If[model["Arithmetic"] === "Numerical" || MemberQ[Lookup[model["Terms"], "Arithmetic", {}], "Numerical"], "Numerical", "Exact"],
            "ModularWeight" -> formal["ModularWeight"], "SuperpotentialWeight" -> md["SuperpotentialWeight"], "VerificationStatus" -> formal["VerificationStatus"]|>,
        "Binding" -> <|"Status" -> bindingStatus[model], "Slots" -> slots, "Unbound" -> Select[used, !slots[#]["Bound"] &], "Spaces" -> spaces|>,
        "Proven" -> formal["Status"] === "Covariant" && formal["ModularWeight"] === "Homogeneous" && bindingStatus[model] === "Full" &&
            AllTrue[Values[spaces], Lookup[#, "Coverage", "None"] === "Full" && #["Established"] === "StageSeven" &] &&
            AllTrue[Values[slots], #["ProofStatus"] === "Proven" &],
        (* the weakest of the formal checks and the bound forms (methodOptionsPlan.md 2C.2) *)
        "VerificationStatus" -> cgWeakestStatus[{formal["VerificationStatus"], boundSlotsStatus[model]}]|>
];

(*
    Summary: The required modular weight of every entry of an extracted matrix, and its check.
    Parameters: model — modular model data; data — MassMatrix data.
    Options/defaults: None.
    Returns: entryWeights: matrix of required actual weights kW - w(row) - w(column). validateModularMassData:
        <|"EntryWeights", "ModularWeight" -> "Homogeneous" | <|"Status" -> "Inhomogeneous", "Entries", "Remainder"|>|>.
    Effects: Pure.
    Failures: None.
    Example: for L of label 1, R of label 1 and kW = 0 every entry of the L-R matrix needs weight 2 (one Y of weight 2).
    Remarks: Rows and columns of direct-sum blocks may have different weights, so the weights are entrywise; spectator
        fields and slots inside an entry count; the remainder is checked monomial by monomial against kW.
    See also: ValidateMassMatrix.
*)
entryWeights[model_Association, data_Association] := Module[{w = model["ModularData"]["ActualFieldWeights"], kW = model["ModularData"]["SuperpotentialWeight"], weightOf},
    weightOf[x_] := If[MatchQ[x, FieldComponent[_String, _Integer]], Lookup[w, First[x], 0], 0];
    Outer[kW - weightOf[#1] - weightOf[#2] &, data["Rows"], data["Columns"]]
];
validateModularMassData[model_Association, data_Association] := Module[{required = entryWeights[model, data], bad, remainder},
    bad = Select[Flatten[MapIndexed[{#2, monomialWeightViolations[#1, model, Extract[required, #2]]} &, data["Matrix"], {2}], 1], Last[#] =!= {} &];
    remainder = monomialWeightViolations[data["Remainder"], model, model["ModularData"]["SuperpotentialWeight"]];
    <|"EntryWeights" -> required, "ModularWeight" -> If[bad === {} && remainder === {}, "Homogeneous",
        <|"Status" -> "Inhomogeneous", "Entries" -> Take[bad[[All, 1]], UpTo[5]], "Remainder" -> Take[remainder, UpTo[3]]|>]|>
];

(*
    Summary: Check the numerical inputs of an evaluation.
    Parameters: model — modular model data; expr — expression to evaluate; effective — validated options (ParameterValues,
        FieldValues).
    Options/defaults: ParameterValues <||> (parameter ID -> finite scalar); FieldValues <||> (field ID -> full ordered
        vector of finite scalars).
    Returns: <|"Parameters" -> rules, "Fields" -> rules, "Slots" -> required slot IDs, "ParameterIDs", "FieldIDs"|>, or
        Failure.
    Effects: Pure.
    Failures: UnknownParameter / UnknownField (IDs not in the model); MissingParameterValues / MissingFieldValues (a required
        input absent); InvalidFieldValues (wrong length); NonfiniteInput.
    Example: an L.R.Y matrix with one coupling needs that coupling's value; its spectator-free entries need no fields.
    Remarks: Extra known entries are allowed and ignored; missing values are never zero.
    See also: EvaluateModularModel; EvaluateModularMassMatrix.
*)
resolveModularModelInputs[model_Association, expr_, effective_Association] := Module[{params = effective[ParameterValues], fields = effective[FieldValues],
        knownParams = Lookup[model["Parameters"], "ID", {}], byField = AssociationThread[Lookup[model["Fields"], "ID", {}], model["Fields"]], needParams, needFields, finiteQ},
    finiteQ = NumericQ[#] && FreeQ[N[#], ComplexInfinity | Indeterminate | _DirectedInfinity] &;
    If[!SubsetQ[knownParams, Keys[params]], Return[makeFailure["UnknownParameter", "ParameterValues names parameters that are not in the model.", <|"Unknown" -> Complement[Keys[params], knownParams]|>]]];
    If[!SubsetQ[Keys[byField], Keys[fields]], Return[makeFailure["UnknownField", "FieldValues names fields that are not in the model.", <|"Unknown" -> Complement[Keys[fields], Keys[byField]]|>]]];
    needParams = DeleteDuplicates[Cases[expr, Coupling[id_String] :> id, {0, Infinity}]];
    needFields = DeleteDuplicates[Cases[expr, FieldComponent[id_String, _] :> id, {0, Infinity}]];
    If[!SubsetQ[Keys[params], needParams], Return[makeFailure["MissingParameterValues", "Every parameter of the expression needs a value.", <|"Missing" -> Complement[needParams, Keys[params]]|>]]];
    If[!SubsetQ[Keys[fields], needFields], Return[makeFailure["MissingFieldValues", "Every field of the expression needs a full vector of values.", <|"Missing" -> Complement[needFields, Keys[fields]]|>]]];
    If[!AllTrue[KeyTake[fields, needFields], ListQ] || !AllTrue[needFields, Length[fields[#]] === byField[#]["Dimension"] &],
        Return[makeFailure["InvalidFieldValues", "A field value must be a list of its dimension.", <|"Fields" -> needFields|>]]];
    If[!AllTrue[Join[Values[KeyTake[params, needParams]], Flatten[Values[KeyTake[fields, needFields]]]], finiteQ],
        Return[makeFailure["NonfiniteInput", "Parameter and field values must be finite numbers."]]];
    <|"Parameters" -> Map[Coupling[#] -> params[#] &, needParams], "Fields" -> Flatten[Map[Thread[byField[#]["Components"] -> fields[#]] &, needFields]],
        "Slots" -> DeleteDuplicates[Cases[expr, FormComponent[s_String, _] :> s, {0, Infinity}]], "ParameterIDs" -> needParams, "FieldIDs" -> needFields|>
];

(*
    Summary: Evaluate a frozen form record at a point (never the live registry).
    Parameters: record — frozen Stage 7 record; point — resolved point; effective — Stage 7 evaluation options.
    Options/defaults: WorkingPrecision, AccuracyGoal, PrecisionGoal, SeriesOrder, MaxSeriesOrder as ModularFormEvaluate.
    Returns: Stage 7 evaluation record, or Failure.
    Effects: Temporary series.
    Failures: evaluateModularRecipe failures (FiniteJet without SeriesOrder, ConvergenceFailure, Pole, ...).
    Example: the bound T' triplet evaluates to the same value as ModularFormEvaluate of its source at that revision.
    See also: evaluateBoundSlots.
*)
evaluateFrozenForm[record_Association, point_Association, effective_Association] := Module[{rules},
    rules = If[ListQ[Lookup[Replace[record["Coefficients"], _Missing -> <||>], "Rules", None]], Map[FormParameter[First[#]] -> Last[#] &, record["Coefficients"]["Rules"]], {}];
    evaluateModularRecipe[Function[n, With[{jets = formComponentJets[record["Definition"], n]},
        If[FailureQ[jets], jets, Map[makeJet[Map[Expand[# /. rules] &, #["Terms"]], #["Cutoff"]] &, jets]]]], point, effective]
];

(*
    Summary: Evaluate each required bound slot once.
    Parameters: bindings — the model's bindings; ids — required slot IDs; point — resolved point; effective — options.
    Options/defaults: As evaluateFrozenForm.
    Returns: <|slotID -> <|"Value" (component vector), "Previous" (the earlier successive approximation, internal), "EstimatedError",
        "Order", "Converged", "Method", "FormID", "Revision", "ValidationStatus"|>|>, or Failure.
    Effects: Temporary series.
    Failures: MissingBindings (a required slot is unbound); evaluation failures.
    Example: an L.R.Y matrix needs one slot evaluation, used for all three entries.
    See also: evaluateModularOutput.
*)
evaluateBoundSlots[bindings_Association, ids_List, point_Association, effective_Association] := Module[{missing = Complement[ids, Keys[bindings]], values},
    If[missing =!= {}, Return[makeFailure["MissingBindings", "Required form slots are not bound; bind actual forms with BindModularForms.", <|"SlotIDs" -> missing|>]]];
    values = AssociationMap[Function[sid, With[{v = evaluateFrozenForm[bindings[sid]["Record"], point, effective]}, If[FailureQ[v], v,
        Join[KeyTake[v, {"Value", "Previous", "EstimatedError", "Order", "Converged", "Method"}], <|"FormID" -> bindings[sid]["FormID"], "Revision" -> bindings[sid]["Revision"],
            "ValidationStatus" -> bindings[sid]["Validation"]["ProofStatus"]|>]]]], ids];
    If[AnyTrue[values, FailureQ], FirstCase[Values[values], _Failure], values]
];

(*
    Summary: Substitute inputs and slot values into a model expression at the working precision.
    Parameters: expr — expression or matrix; inputs — resolveModularModelInputs result; slots — evaluateBoundSlots
        result; key — "Value" or "Previous" (the slot approximation used); digits — WorkingPrecision.
    Options/defaults: None.
    Returns: The numerical value (shape of expr), or Failure NonfiniteValue.
    Effects: Pure.
    Failures: NonfiniteValue (a singular or non-numeric result).
    Example: the L.R.Y matrix with the current slot values is a 3 x 1 numeric matrix.
    See also: evaluateModularOutput; modularOutputError.
*)
modularOutputValue[expr_, inputs_Association, slots_Association, key_String, digits_] := Module[{rules, value},
    rules = Join[inputs["Parameters"], inputs["Fields"],
        Flatten[KeyValueMap[Function[{sid, v}, Thread[Table[FormComponent[sid, i], {i, Length[v[key]]}] -> v[key]]], slots]]];
    value = N[expr /. rules, digits];
    If[!FreeQ[value, ComplexInfinity | Indeterminate | _DirectedInfinity] || !AllTrue[Flatten[{value}], NumericQ],
        makeFailure["NonfiniteValue", "The evaluated expression is not a finite number (check the inputs and bindings)."], value]
];

(*
    Summary: The estimated error of an evaluated model output (D-S9-12 semantics, as the generated Python modules).
    Parameters: expr, inputs, slots, digits — as modularOutputValue; value — the output with the current slot values.
    Options/defaults: None.
    Returns: The largest entrywise change of the output when every slot takes its previous successive approximation,
        at least the output's own roundoff (10^-Accuracy of each entry, which significance arithmetic propagates from the
        slot values and amplifying couplings or fields); Missing["NoTailBound"] when a slot has no second approximation
        (a finite jet that cannot be extended past the explicit order).
    Effects: Pure.
    Failures: None (a singular earlier output is an infinite change).
    Example: an output proportional to a coupling 10^12 reports an error about 10^12 times the slot error.
    See also: evaluateModularOutput.
*)
modularOutputError[expr_, inputs_Association, slots_Association, value_, digits_] := Module[{previous, change, roundoff},
    If[!AllTrue[slots, ListQ[#["Previous"]] &], Return[Missing["NoTailBound"]]];
    previous = modularOutputValue[expr, inputs, slots, "Previous", digits];
    change = If[FailureQ[previous], Infinity, Max[Append[Abs[Flatten[{value - previous}]], 0]]];
    roundoff = Max[Append[Map[If[Accuracy[#] === Infinity, 0, 10^-Accuracy[#]] &, Flatten[{value}]], 0]];
    If[change === Infinity, Infinity, N[Max[change, roundoff], 5]]
];

(*
    Summary: Evaluate an expression (scalar or matrix) of a modular model at a point.
    Parameters: model — modular model data; expr — expression or matrix; point — TauPoint or QPoint; effective — options.
    Options/defaults: ParameterValues, FieldValues; WorkingPrecision, AccuracyGoal, PrecisionGoal (Automatic:
        Floor[WorkingPrecision/2]), SeriesOrder, MaxSeriesOrder, TimeLimit.
    Returns: <|"Value" (same shape as expr), "WorkingPrecision", "AccuracyGoal", "PrecisionGoal", "Point" -> tau, "Branch",
        "Inputs" -> <|"ParameterIDs", "FieldIDs", "SlotIDs"|>, "SlotEvaluations", "EstimatedError" (the output's own
        estimate, modularOutputError; Missing["NoTailBound"] when a slot has no earlier approximation), "Refinements",
        "Converged"|>, or Failure.
    Effects: Temporary series; nothing stored is mutated.
    Failures: point, input, binding and evaluation failures; NonfiniteValue (a singular result); OutputAccuracy (the output
        misses the requested goals after three refinements of the slot goals).
    Example: the evaluated L.R.Y matrix keeps its 3 x 1 shape.
    Remarks: The slot values are substituted once each; numbers are evaluated at the working precision. The output is
        accepted when its estimate is at most Max[10^-AccuracyGoal, 10^-PrecisionGoal Max|value|]; otherwise the slot goals
        rise by five digits per round (at most WorkingPrecision - 2, never below the requested goals), up to three rounds,
        as in the generated Python modules (D-S9-12). An explicit SeriesOrder is a truncated value: it is reported
        (Converged False) and not refined.
    See also: EvaluateModularModel; EvaluateModularMassMatrix.
*)
evaluateModularOutput[model_Association, expr_, point_, effective_Association] := Module[
    {resolved, inputs, digits = effective[WorkingPrecision], goal, precisionGoal, cap, round = 0, slots, value, error, accepted, explicit},
    resolved = resolveModularPoint[point]; If[FailureQ[resolved], Return[resolved]];
    If[resolved["Cusp"], Return[makeFailure["OutsideDomain", "Evaluate model expressions at a point of the upper half plane (the cusp limit is a form property)."]]];
    inputs = resolveModularModelInputs[model, expr, effective]; If[FailureQ[inputs], Return[inputs]];
    goal = Replace[effective[AccuracyGoal], Automatic -> Floor[digits/2]];
    precisionGoal = Replace[effective[PrecisionGoal], Automatic -> Floor[digits/2]];
    cap = digits - 2; explicit = effective[SeriesOrder] =!= Automatic;
    While[True,
        slots = evaluateBoundSlots[model["ModularData"]["Bindings"], inputs["Slots"], resolved,
            Join[effective, <|AccuracyGoal -> Max[goal, Min[goal + 5 round, cap]], PrecisionGoal -> Max[precisionGoal, Min[precisionGoal + 5 round, cap]]|>]];
        If[FailureQ[slots], Return[slots]];
        value = modularOutputValue[expr, inputs, slots, "Value", digits]; If[FailureQ[value], Return[value]];
        error = modularOutputError[expr, inputs, slots, value, digits];
        accepted = !NumericQ[error] && error =!= Infinity || NumericQ[error] && error <= Max[10^-goal, 10^-precisionGoal Max[Abs[Flatten[{value}]]]];
        If[accepted || explicit, Break[]];
        If[round >= 3 || Min[goal + 5 (round + 1), cap] <= Min[goal + 5 round, cap] && Min[precisionGoal + 5 (round + 1), cap] <= Min[precisionGoal + 5 round, cap],
            Return[makeFailure["OutputAccuracy", "The output did not reach the accuracy goal after refining the form series (cancellation or amplification); raise WorkingPrecision.",
                <|"EstimatedError" -> error, "AccuracyGoal" -> goal, "PrecisionGoal" -> precisionGoal, "Refinements" -> round|>]]];
        round++];
    <|"Value" -> value, "WorkingPrecision" -> digits, "AccuracyGoal" -> goal, "PrecisionGoal" -> precisionGoal, "Point" -> resolved["Tau"], "Branch" -> resolved["Branch"],
        "Inputs" -> <|"ParameterIDs" -> inputs["ParameterIDs"], "FieldIDs" -> inputs["FieldIDs"], "SlotIDs" -> inputs["Slots"]|>,
        "SlotEvaluations" -> Map[KeyDrop[#, "Previous"] &, slots], "EstimatedError" -> error, "Refinements" -> round,
        "Converged" -> accepted && !explicit && NumericQ[error] && AllTrue[slots, TrueQ[#["Converged"]] &]|>
];

Options[ValidateModularModel] = {RequireBindings -> False, RequireProof -> False, Verification -> Automatic};

(*
    Summary: The layered validation report of a modular model, with optional requirements.
    Status: Alpha.
    Parameters: m — modular Model.
    Options/defaults: RequireBindings -> False (True: every used slot bound with full independent coverage of its space);
        RequireProof -> False (True: the report's Proven must be True); Verification -> Automatic, "Exact" or "Numerical",
        the level of the formal checks (ValidateModel's Verification; None is InvalidOption).
    Returns: Report (validateModularModelChecks), or Failure.
    Effects: Pure.
    Failures: InvalidModel; NotModularModel; MissingBindings (RequireBindings); ProofRequired (RequireProof).
    Example: ValidateModularModel[m]["Binding"]["Status"] is "Unbound" before BindModularForms.
    Remarks: An integer count without actual basis data is never binding evidence; numerical formal covariance never
        becomes exact because Y is symbolic or unbound.
    See also: ValidateModel; BindModularForms.
*)
ValidateModularModel[m_Model, options : OptionsPattern[]] := Module[{model = validateModelSchema[m], effective, report},
    If[FailureQ[model], Return[model]];
    If[!KeyExistsQ[model, "ModularData"], Return[makeFailure["NotModularModel", "The model has no modular weights; create it with CreateModularModel."]]];
    effective = resolveOperationOptions[ValidateModularModel, "ValidateModularModel", {options}]; If[FailureQ[effective], Return[effective]];
    report = validateModularModelChecks[model, m, effective[Verification]]; If[FailureQ[report], Return[report]];
    Which[
        TrueQ[effective[RequireBindings]] && (report["Binding"]["Status"] =!= "Full" || !AllTrue[Values[report["Binding"]["Spaces"]], #["Coverage"] === "Full" &]),
            makeFailure["MissingBindings", "Every used slot must be bound with full independent coverage of its space.",
                <|"Unbound" -> report["Binding"]["Unbound"], "Spaces" -> Map[#["Coverage"] &, report["Binding"]["Spaces"]]|>],
        TrueQ[effective[RequireProof]] && !report["Proven"], makeFailure["ProofRequired", "The model's formal and binding evidence is not a proof.",
            <|"Formal" -> report["Formal"]["Status"], "Binding" -> report["Binding"]["Status"]|>],
        True, report]
];
ValidateModularModel[___] := makeFailure["InvalidInput", "ValidateModularModel expects a modular Model and options."];

Options[EvaluateModularModel] = {ParameterValues -> <||>, FieldValues -> <||>, WorkingPrecision -> 50, AccuracyGoal -> Automatic, PrecisionGoal -> Automatic,
    SeriesOrder -> Automatic, MaxSeriesOrder -> 2000, TimeLimit -> 600};
Options[EvaluateModularMassMatrix] = Options[EvaluateModularModel];

(*
    Summary: Numerical values of a modular model's expression and of its extracted matrices at a point.
    Status: Alpha.
    Signatures: EvaluateModularModel[m, point, opts]; EvaluateModularMassMatrix[m, mass, point, opts].
    Parameters: m — modular Model with the needed bindings; mass — MassMatrix extracted from ModelExpression[m]; point —
        TauPoint[tau] or QPoint[q, sheet].
    Options/defaults: ParameterValues -> <||> (every required parameter ID -> finite scalar); FieldValues -> <||> (every
        required field ID -> full vector); WorkingPrecision -> 50; AccuracyGoal, PrecisionGoal, SeriesOrder, MaxSeriesOrder,
        TimeLimit as ModularFormEvaluate.
    Returns: Evaluation report (value, inputs, slot evaluations, the output's estimated error, goals, refinements and
        convergence; for a matrix also the source/sector/convention and the formal validation; "VerificationStatus", at
        best "Numerical", bounded by the formal checks and the bound forms), or Failure.
    Effects: Temporary series; no form, model or group data are mutated.
    Failures: InvalidModel; NotModularModel; ValidateMassMatrix failures (the matrix is validated against its source
        first); input, binding, point and evaluation failures; OutputAccuracy (the output misses AccuracyGoal/PrecisionGoal
        after refining the slot series); TimeLimit.
    Example: Dimensions[EvaluateModularMassMatrix[mb, mass, TauPoint[1/7 + 6 I/5], ParameterValues -> values]["Value"]] is {3, 1}.
    Remarks: Each distinct bound slot is evaluated once from its frozen record; matrices keep their 2D shape (also 1 x 1);
        missing bindings or inputs are never replaced by zero. EstimatedError is the output's own estimate (the slot
        successive approximations propagated through the expression, at least the output's roundoff), never a certified
        bound; amplification by couplings or fields refines the slot series or fails OutputAccuracy (evaluateModularOutput).
    See also: BindModularForms; ExtractBilinearMatrix.
*)
EvaluateModularModel[m_Model, point_, options : OptionsPattern[]] := Module[{model = validateModelSchema[m], effective, result},
    If[FailureQ[model], Return[model]];
    If[!KeyExistsQ[model, "ModularData"], Return[makeFailure["NotModularModel", "The model has no modular weights; create it with CreateModularModel."]]];
    effective = resolveOperationOptions[EvaluateModularModel, "EvaluateModularModel", {options}]; If[FailureQ[effective], Return[effective]];
    result = TimeConstrained[evaluateModularOutput[model, Total[Lookup[model["Terms"], "Value", {}]], point, effective], effective[TimeLimit],
        makeFailure["TimeLimit", "The evaluation did not finish within TimeLimit."]];
    If[FailureQ[result], result, With[{formal = ValidateModel[m]}, Join[result, <|"ModelID" -> model["ID"], "Formal" -> formal["Status"], "BindingStatus" -> bindingStatus[model],
        (* a numerical value: at best "Numerical", bounded by the formal checks and the bound forms *)
        "VerificationStatus" -> cgWeakestStatus[{"Numerical", formal["VerificationStatus"], boundSlotsStatus[model]}]|>]]]
];
EvaluateModularModel[___] := makeFailure["InvalidInput", "EvaluateModularModel expects a modular Model, a point and options."];

EvaluateModularMassMatrix[m_Model, mass_MassMatrix, point_, options : OptionsPattern[]] := Module[{model = validateModelSchema[m], effective, check, data, result},
    If[FailureQ[model], Return[model]];
    If[!KeyExistsQ[model, "ModularData"], Return[makeFailure["NotModularModel", "The model has no modular weights; create it with CreateModularModel."]]];
    effective = resolveOperationOptions[EvaluateModularMassMatrix, "EvaluateModularMassMatrix", {options}]; If[FailureQ[effective], Return[effective]];
    check = ValidateMassMatrix[m, mass]; If[FailureQ[check], Return[check]];
    data = First[mass];
    result = TimeConstrained[evaluateModularOutput[model, data["Matrix"], point, effective], effective[TimeLimit],
        makeFailure["TimeLimit", "The evaluation did not finish within TimeLimit."]];
    If[FailureQ[result], result, Join[result, <|"ModelID" -> model["ID"], "Sector" -> check["Sector"], "Convention" -> data["Convention"],
        "Formal" -> check["Status"], "ModularWeight" -> Lookup[check, "ModularWeight", Missing["NotModular"]], "BindingStatus" -> bindingStatus[model],
        "VerificationStatus" -> cgWeakestStatus[{"Numerical", check["VerificationStatus"], boundSlotsStatus[model]}]|>]]
];
EvaluateModularMassMatrix[___] := makeFailure["InvalidInput", "EvaluateModularMassMatrix expects a modular Model, a MassMatrix, a point and options."];

True
