(*
    :Title: Models with modular weights
    :Context: VVMFTool`Private`
    :Summary: The modular mode of a Stage 5 model: per-model field weights and target weight (the weight convention lives
        here, D-S8-1), the S,T assignment and a fresh slot namespace, the model's formal components and per-generator
        substitution rules including registered form slots (D-S8-7), and the checks of weighted polynomial factors.
    :Responsibilities: modularWeightQ, actualFieldWeight, resolveFieldWeights, makeModularModel, validateModularModelData,
        modelComponents, modelGeneratorRules, monomialWeightViolations, validateWeightedPolynomial, bindingStatus; CreateModularModel,
        FieldModularWeight.
    :Dependencies: Models.wl (makeModelData, modelSettings, zeroCoefficientQ); Fields.wl; ModularCandidates.wl
        (recomputed slot records, at call time).
    :See Also: VVMFArch/step8Plan.md (model data, weight convention); D-S8-1, D-S8-7.
*)

(*
    Summary: Whether a value is an admissible modular weight: an exact rational (integers included).
    Parameters: x — any expression.
    Options/defaults: None.
    Returns: True or False.
    Effects: Pure.
    Failures: None.
    Example: {modularWeightQ[1/2], modularWeightQ[2], modularWeightQ[0.5]} is {True, True, False}.
    Remarks: Weights are exact (fractionalWeightPlan.md, C2); approximate weights are refused.
    See also: actualFieldWeight; resolveFieldWeights.
*)
modularWeightQ[x_] := MatchQ[x, _Integer | _Rational];

(*
    Summary: One-line text of a weight (or of any other table entry).
    Parameters: x — exact rational weight, string, or other expression.
    Options/defaults: None.
    Returns: String: a weight in InputForm ("1/2", "-3/2"), a string unchanged, anything else by ToString.
    Effects: Pure.
    Failures: None.
    Example: weightText[-3/2] is "-3/2" (ToString would give a three-line OutputForm fraction).
    See also: modularWeightQ.
*)
weightText[x_?modularWeightQ] := ToString[x, InputForm];
weightText[x_String] := x;
weightText[x_] := ToString[x];

(*
    Summary: The actual modular weight of a field with user label kf.
    Parameters: kf — exact rational label (FieldWeights).
    Options/defaults: None.
    Returns: -kf.
    Effects: Pure.
    Failures: None.
    Example: actualFieldWeight[1] is -1, so a weight-2 form and two fields of label 1 make actual weight 0.
    Remarks: The one place of the convention (v1 ModelBuildingKit.wl:78-99): fields are labelled kf, transform with weight
        -kf, a form has actual weight kY, and kY - Sum kf = kW is the admission rule.
    See also: resolveFieldWeights; CreateModularModel.
*)
actualFieldWeight[kf_?modularWeightQ] := -kf;

(*
    Summary: Check a FieldWeights association against the model's fields.
    Parameters: fields — validated field data; weights — FieldWeights option value.
    Options/defaults: None.
    Returns: <|fieldID -> kf|> in field order, or Failure.
    Effects: Pure.
    Failures: MissingFieldWeights (Automatic, or a field without a weight); InvalidFieldWeights (unknown field IDs or
        weights that are not exact rationals).
    Example: resolveFieldWeights[{l, r}, <|l["ID"] -> 1, r["ID"] -> 1|>] is that association.
    Remarks: No default is guessed: every field needs an explicit label, an exact rational such as 1/2 (v1 RepVecW).
    See also: makeModularModel.
*)
resolveFieldWeights[fields_List, weights_] := Module[{ids = Lookup[fields, "ID", {}]},
    If[weights === Automatic, Return[makeFailure["MissingFieldWeights", "CreateModularModel needs FieldWeights: an exact rational weight label kf for every field ID."]]];
    If[!AssociationQ[weights], Return[makeFailure["InvalidFieldWeights", "FieldWeights must be an association from field IDs to exact rationals."]]];
    If[!SubsetQ[ids, Keys[weights]], Return[makeFailure["InvalidFieldWeights", "FieldWeights names fields that are not in the model.",
        <|"Unknown" -> Complement[Keys[weights], ids]|>]]];
    If[!SubsetQ[Keys[weights], ids], Return[makeFailure["MissingFieldWeights", "Every field needs a weight label.",
        <|"Missing" -> Complement[ids, Keys[weights]]|>]]];
    If[!AllTrue[Values[weights], modularWeightQ], Return[makeFailure["InvalidFieldWeights", "Field weight labels must be exact rationals (for example 1/2).",
        <|"Invalid" -> Keys[Select[weights, !modularWeightQ[#] &]]|>]]];
    AssociationThread[ids, Lookup[weights, ids]]
];

(*
    Summary: Build the data of a new modular model.
    Parameters: context — RepresentationContext; fields — validated field data; effective — validated CreateModularModel
        options.
    Options/defaults: As CreateModularModel.
    Returns: Model data with a "ModularData" record, or Failure.
    Effects: Allocates a model ID and a slot namespace.
    Failures: makeModelData failures; MissingModularAssignment; field weight failures; InvalidOption (a
        SuperpotentialWeight that is not an exact rational).
    Example: makeModularModel[ctx, {l, r}, opts]["ModularData"]["ActualFieldWeights"] is <|l -> -1, r -> -1|>.
    Remarks: ModularData: SchemaVersion, AssignmentID and words, FieldWeights (kf), ActualFieldWeights (-kf),
        SuperpotentialWeight (kW, actual), SlotNamespaceID, Spaces and Slots registered by terms, Bindings, SlotCouplings;
        SupplyModularFormSpace adds SuppliedSpaces (space ID -> suppliedSpaceRecord) when it is first used.
    See also: CreateModularModel; validateModularModelData.
*)
makeModularModel[context_RepresentationContext, fields_List, effective_Association] := Module[{snapshot = First[context], assignment, weights, base},
    assignment = snapshot["ModularAssignment"];
    If[!AssociationQ[assignment], Return[makeFailure["MissingModularAssignment", "A modular model needs a group with an S,T assignment; use AssignModularGenerators or BuildModularGroup."]]];
    weights = resolveFieldWeights[fields, effective[FieldWeights]]; If[FailureQ[weights], Return[weights]];
    base = makeModelData[context, fields, KeyTake[effective, {Name, TargetIrrep, Arithmetic, WorkingPrecision, Tolerance}]];
    If[FailureQ[base], Return[base]];
    Join[base, <|"ModularData" -> <|"SchemaVersion" -> 1, "AssignmentID" -> assignment["Identity"], "AssignmentWords" -> KeyTake[assignment, {"S", "T"}],
        "FieldWeights" -> weights, "ActualFieldWeights" -> Map[actualFieldWeight, weights], "SuperpotentialWeight" -> effective[SuperpotentialWeight],
        "SlotNamespaceID" -> "slots-" <> CreateUUID[], "Spaces" -> <||>, "Slots" -> <||>, "Bindings" -> <||>, "SlotCouplings" -> <||>|>|>]
];

(*
    Summary: Validate the modular record of a model.
    Parameters: data — model data with "ModularData".
    Options/defaults: None.
    Returns: data, or InvalidModel Failure.
    Effects: Pure.
    Failures: InvalidModel (schema, weights inconsistent with the fields, a changed assignment, or a registered slot or
        space that differs from its recomputation in the model's namespace).
    Example: a model whose ActualFieldWeights were edited by hand fails here.
    Remarks: Registered slots are recomputed from their space keys (recomputeSlotRecord), so a forged record cannot
        enter through a model value either.
    See also: validateModelSchema; makeModularModel.
*)
validateModularModelData[data_Association] := Module[{md = data["ModularData"], snapshot, ids = Lookup[data["Fields"], "ID", {}]},
    If[!AssociationQ[md] || !SubsetQ[Keys[md], {"SchemaVersion", "AssignmentID", "FieldWeights", "ActualFieldWeights", "SuperpotentialWeight",
            "SlotNamespaceID", "Spaces", "Slots", "Bindings", "SlotCouplings"}] || md["SchemaVersion"] =!= 1,
        Return[makeFailure["InvalidModel", "Malformed modular model data."]]];
    snapshot = resolveRepContext[data["Context"]]; If[FailureQ[snapshot], Return[snapshot]];
    If[!AssociationQ[snapshot["ModularAssignment"]] || snapshot["ModularAssignment"]["Identity"] =!= md["AssignmentID"] ||
            Keys[md["FieldWeights"]] =!= ids || !AllTrue[Values[md["FieldWeights"]], modularWeightQ] ||
            md["ActualFieldWeights"] =!= Map[actualFieldWeight, md["FieldWeights"]] || !modularWeightQ[md["SuperpotentialWeight"]] ||
            !StringQ[md["SlotNamespaceID"]] || !AllTrue[{md["Spaces"], md["Slots"], md["Bindings"], md["SlotCouplings"]}, AssociationQ],
        Return[makeFailure["InvalidModel", "The modular model data disagree with its fields, weights or assignment."]]];
    (* Supplied spaces (SupplyModularFormSpace): complete records keyed by their recomputed space ID. *)
    If[KeyExistsQ[md, "SuppliedSpaces"] && !(AssociationQ[md["SuppliedSpaces"]] &&
            AllTrue[Keys[md["SuppliedSpaces"]], suppliedSpaceRecordQ[data, #, md["SuppliedSpaces"][#]] &]),
        Return[makeFailure["InvalidModel", "A supplied form space is malformed or does not match its irrep and weight."]]];
    If[!AllTrue[Keys[md["Slots"]], With[{r = recomputeSlotRecord[data, md["Slots"][#]]}, AssociationQ[r] && r === md["Slots"][#]] &],
        Return[makeFailure["InvalidModel", "A registered form slot differs from its recomputation in the model's namespace."]]];
    (* Bindings name registered slots and their frozen records still fit them (a forged record cannot enter). *)
    If[!SubsetQ[Keys[md["Slots"]], Keys[md["Bindings"]]] || !AllTrue[Keys[md["Bindings"]], Function[sid, With[{b = md["Bindings"][sid]},
            AssociationQ[b] && b["SlotID"] === sid && AssociationQ[b["Record"]] && AssociationQ[validateFormRecord[b["Record"]]] &&
                TrueQ[validateFormBinding[md["Slots"][sid], b["Record"], <|SeriesOrder -> If[b["Kind"] === "Jet", 1, Automatic]|>]]]]],
        Return[makeFailure["InvalidModel", "A form binding names an unregistered slot or its frozen record does not fit the slot."]]];
    data
];

(*
    Summary: The formal components of a model and their substitution rules for one generator.
    Parameters: model — model data; i — generator index.
    Options/defaults: None.
    Returns: modelComponents: field components followed by the components of registered slots (in registration order).
        modelGeneratorRules: {x -> D_f(g_i) . x for every field} joined with {Y -> rho_r(g_i) . Y for every registered slot}.
    Effects: Pure.
    Failures: None.
    Example: a non-modular model has only its field rules; a modular model with one triplet slot adds three rules.
    Remarks: The single source of the substitution law (D-S8-7), used by term, model and matrix covariance.
    See also: validatePolynomialCovariance; validateMatrixCovariance.
*)
modelComponents[model_Association] := Join[Flatten[Lookup[model["Fields"], "Components", {}]],
    Flatten[Lookup[Values[Lookup[Lookup[model, "ModularData", <||>], "Slots", <||>]], "Components", {}]]];
modelGeneratorRules[model_Association, i_Integer] := Join[
    Flatten[Map[Function[f, Thread[f["Components"] -> repMatrices[f["Rep"]][[i]] . f["Components"]]], model["Fields"]]],
    Flatten[Map[Function[s, Thread[s["Components"] -> repMatrices[s["Rep"]][[i]] . s["Components"]]], Values[Lookup[Lookup[model, "ModularData", <||>], "Slots", <||>]]]]];

(*
    Summary: The monomials of an expression whose total actual modular weight differs from a required weight.
    Parameters: expr — polynomial in field and slot components; model — model data (field weights, registered slots);
        target — required actual weight.
    Options/defaults: None.
    Returns: List of <|"Monomial", "Weight"|> for every offending monomial ({} when homogeneous of weight target).
    Effects: Pure.
    Failures: None.
    Example: for L of label 1, Y of weight 2 and kW = 0, Y L L is homogeneous and Y L alone has weight 1.
    Remarks: Each field component contributes -kf per power, each slot component kY per power; a constant term has weight
        0. Scalar coefficients (couplings, numbers) carry weight 0.
    See also: addModularTermData; validateMatrixWeights.
*)
monomialWeightViolations[expr_, model_Association, target_?modularWeightQ] := Module[{components = modelComponents[model], weights, rules},
    weights = Join[Flatten[Map[Function[f, Thread[f["Components"] -> model["ModularData"]["ActualFieldWeights"][f["ID"]]]], model["Fields"]]],
        Flatten[Map[Function[s, Thread[s["Components"] -> s["Weight"]]], Values[model["ModularData"]["Slots"]]]]];
    If[Expand[expr] === 0, Return[{}]];
    rules = If[components === {}, {{} -> Expand[expr]}, CoefficientRules[Expand[expr], components]];
    Select[Map[<|"Monomial" -> If[components === {}, 1, Times @@ (components^First[#])], "Weight" -> If[components === {}, 0, First[#] . Lookup[weights, components]]|> &, rules],
        #["Weight"] =!= target &]
];

(*
    Summary: Check one channel of a user-supplied weighted vector: polynomial in the model's fields, covariant under its
        irrep on every generator, homogeneous of its declared actual weight.
    Parameters: model — modular model data; record — vector record (TargetID, Components); weight — declared actual weight.
    Options/defaults: The model's arithmetic.
    Returns: True, or Failure.
    Effects: Pure.
    Failures: modelPolynomialCheck failures; NotCovariant (the components do not transform with the record's irrep);
        UndecidableCovariance; InconsistentWeight (a monomial of another actual weight); MissingRepresentations.
    Example: the CG product of two triplet fields of label 1 into a triplet is covariant with actual weight -2.
    Remarks: A declared grading is not trusted: the field content fixes the weight.
    See also: resolveModularFactors; MakeWeightedRepVector.
*)
validateWeightedPolynomial[model_Association, record_Association, weight_?modularWeightQ] := Module[{fieldModel = Join[model, <|"ModularData" -> Join[model["ModularData"], <|"Slots" -> <||>|>]|>],
        snapshot, variant, settings, check, outcomes},
    snapshot = resolveRepContext[model["Context"]]; If[FailureQ[snapshot], Return[snapshot]];
    variant = cgVariant[snapshot, record["TargetID"]];
    If[MissingQ[variant], Return[makeFailure["MissingRepresentations", "The channel's irrep has no accepted matrices in the model's context.", <|"IrrepIDs" -> {record["TargetID"]}|>]]];
    check = modelPolynomialCheck[#, Flatten[Lookup[model["Fields"], "Components", {}]]] & /@ record["Components"];
    If[AnyTrue[check, FailureQ], Return[FirstCase[check, _Failure]]];
    settings = modelSettings[model];
    outcomes = Table[Module[{rules = Flatten[Map[Function[f, Thread[f["Components"] -> repMatrices[f["Rep"]][[i]] . f["Components"]]], model["Fields"]]], difference, coefficients},
            difference = Expand[(record["Components"] /. rules) - repMatrices[variant["Rep"]][[i]] . record["Components"]];
            If[settings["Arithmetic"] === "Exact" && inexactDataQ[difference], Return["Undecidable", Module]];
            coefficients = Flatten[Map[If[# === 0, {0}, Values[CoefficientRules[#, Flatten[Lookup[model["Fields"], "Components", {}]]]]] &, difference]];
            With[{decided = zeroCoefficientQ[#, settings] & /@ coefficients}, Which[MemberQ[decided, False], False, MemberQ[decided, "Undecidable"], "Undecidable", True, True]]],
        {i, Length[repMatrices[variant["Rep"]]]}];
    Which[
        MemberQ[outcomes, False], makeFailure["NotCovariant", "A supplied weighted channel does not transform with its irrep.", <|"Generator" -> First[FirstPosition[outcomes, False]]|>],
        MemberQ[outcomes, "Undecidable"], makeFailure["UndecidableCovariance", "The covariance of a supplied weighted channel could not be decided."],
        AnyTrue[record["Components"], monomialWeightViolations[#, fieldModel, weight] =!= {} &],
            makeFailure["InconsistentWeight", "A supplied channel has monomials whose field content gives another actual weight than its declared weight.",
                <|"Weight" -> weight|>],
        True, True]
];

(*
    Summary: The binding status of the slots a modular model's terms use.
    Parameters: model — modular model data.
    Options/defaults: None.
    Returns: "NoForms" (no slot used), "Unbound", "Partial" or "Full".
    Effects: Pure.
    Failures: None.
    Example: a model with one L.R.Y term and no binding is "Unbound".
    See also: ValidateModel; ValidateModularModel.
*)
bindingStatus[model_Association] := Module[{used = Keys[model["ModularData"]["Slots"]], bound = Keys[model["ModularData"]["Bindings"]]},
    Which[used === {}, "NoForms", Intersection[used, bound] === {}, "Unbound", SubsetQ[bound, used], "Full", True, "Partial"]];

(*
    Summary: Verification statuses of a modular model's slots and bindings (methodOptionsPlan.md 2C.2).
    Parameters: model — modular model data; binding — a frozen binding record.
    Options/defaults: None.
    Returns: suppliedSlotsStatus: "Unverified" when a used slot belongs to a space the user supplied (its completeness is
        the user's assertion), else "Exact"; bindingVerificationStatus: the bound form's status, with the Stage 7 proof
        status the binding recorded as its validation (formVerificationStatus); boundSlotsStatus: the weakest over the
        bindings of used slots ("Exact" when none is bound).
    Effects: Pure.
    Failures: None.
    Example: a model whose L.R.Y term uses a slot of SupplyModularFormSpace has suppliedSlotsStatus "Unverified".
    Remarks: Recomputed from the model's data, so an imported model reports the same statuses as the live one.
    See also: ValidateModel; validateModularModelChecks; formVerificationStatus.
*)
suppliedSlotsStatus[model_Association] := With[{supplied = Lookup[model["ModularData"], "SuppliedSpaces", <||>]},
    If[AnyTrue[Values[model["ModularData"]["Slots"]], KeyExistsQ[supplied, #["SpaceID"]] &], "Unverified", "Exact"]];
bindingVerificationStatus[binding_Association] := formVerificationStatus[Join[binding["Record"],
    <|"Validation" -> <|"Status" -> binding["Validation"]["ProofStatus"]|>|>]];
boundSlotsStatus[model_Association] := cgWeakestStatus[bindingVerificationStatus /@
    Values[KeyTake[model["ModularData"]["Bindings"], Keys[model["ModularData"]["Slots"]]]]];

Options[CreateModularModel] = {FieldWeights -> Automatic, SuperpotentialWeight -> 0, Name -> "Model", TargetIrrep -> Automatic, Arithmetic -> "Exact",
    WorkingPrecision -> 50, Tolerance -> Automatic};

(*
    Summary: An empty model of weighted fields over a group with an S,T assignment.
    Status: Alpha.
    Parameters: c — Group or RepresentationContext (with a modular assignment); fields — list of Field values.
    Options/defaults: FieldWeights (required: field ID -> exact rational label kf); SuperpotentialWeight -> 0 (the target's actual
        weight kW); Name, TargetIrrep (degree one, trivial by default), Arithmetic, WorkingPrecision, Tolerance as
        CreateModel.
    Returns: Model with ModularData, or Failure.
    Effects: Freezing a group registers its context; allocates a slot namespace.
    Failures: Option failures; MissingFieldWeights; InvalidFieldWeights; MissingModularAssignment; CreateModel failures.
    Example: CreateModularModel[c, {l, r}, FieldWeights -> <|l["ID"] -> 1, r["ID"] -> 1|>].
    Remarks: A field with label kf transforms with actual weight -kf; a term with one form of weight kY is admitted when
        kY - Sum kf = kW. No positivity or extra parity rule is imposed on matter fields. Each call starts a new slot
        namespace; models derived by AddModelTerm and the modular operations keep it.
    See also: FieldModularWeight; ModularContractions; ModularFormCandidates.
*)
CreateModularModel[c : (_Group | _RepresentationContext), fields_List, options : OptionsPattern[]] := Module[{effective, data, context, model},
    effective = resolveOperationOptions[CreateModularModel, "CreateModularModel", {options}]; If[FailureQ[effective], Return[effective]];
    effective = resolveIrrepOptions[c, effective]; If[FailureQ[effective], Return[effective]];
    data = validateField /@ fields;
    If[AnyTrue[data, FailureQ], Return[FirstCase[data, _Failure]]];
    context = If[Head[c] === Group, modelContextForGroup[c, data, effective[TargetIrrep]], vectorContext[c]];
    If[FailureQ[context], Return[context]];
    model = makeModularModel[context, data, effective];
    If[FailureQ[model], model, Model[model]]
];
CreateModularModel[___] := makeFailure["InvalidInput", "CreateModularModel expects a Group or RepresentationContext, a list of fields and options."];

(*
    Summary: The weight label kf of a field of a modular model.
    Status: Alpha.
    Parameters: m — modular Model; f — Field or field ID.
    Options/defaults: None.
    Returns: Exact rational kf (the field's actual weight is -kf), or Failure.
    Effects: Pure.
    Failures: InvalidModel; NotModularModel; UnknownField.
    Example: FieldModularWeight[m, l] is 1 for FieldWeights -> <|l["ID"] -> 1, ...|>.
    See also: CreateModularModel.
*)
FieldModularWeight[m_Model, f : (_Field | _String)] := Module[{model = validateModelSchema[m], fields},
    If[FailureQ[model], Return[model]];
    If[!KeyExistsQ[model, "ModularData"], Return[makeFailure["NotModularModel", "The model has no modular weights; create it with CreateModularModel."]]];
    fields = resolveModelFields[model, {f}]; If[FailureQ[fields], Return[fields]];
    model["ModularData"]["FieldWeights"][First[fields]["ID"]]
];
FieldModularWeight[___] := makeFailure["InvalidInput", "FieldModularWeight expects a Model and a Field or field ID."];

True
