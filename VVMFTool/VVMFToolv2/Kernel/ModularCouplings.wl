(*
    :Title: Per-slot couplings of modular models
    :Context: VVMFTool`Private`
    :Summary: v1's optional coefficient per distinct Y (AddCoeffToY) as an explicit model edit: one physical coupling per
        selected used slot, applied to every occurrence of that slot's components in every term, recorded so a repeat
        reuses it (D-S8-9).
    :Responsibilities: usedSlots, replaceSlotComponents, rebuildSlotTerm, addFormCouplingData; AddModularFormCouplings.
    :Dependencies: Couplings.wl (resolveCouplingParameters, mergeParameterRecords, coupledData); ModularContractions.wl
        (addModularTermData).
    :See Also: VVMFArch/step8Plan.md (AddModularFormCouplings); D-S8-9.
*)

(*
    Summary: The registered slots that the model's terms actually use.
    Parameters: model — modular model data.
    Options/defaults: None.
    Returns: Slot IDs in registration order.
    Effects: Pure.
    Failures: None.
    Example: a model with one L.R.Y term uses its one triplet slot.
    See also: addFormCouplingData.
*)
usedSlots[model_Association] := With[{present = DeleteDuplicates[Cases[Lookup[model["Terms"], "Value", {}], FormComponent[s_String, _] :> s, Infinity]]},
    Select[Keys[model["ModularData"]["Slots"]], MemberQ[present, #] &]];

(*
    Summary: Multiply every component of the mapped slots by the slot's coefficient.
    Parameters: expr — expression; map — <|slotID -> coefficient|>.
    Options/defaults: None.
    Returns: The expression with FormComponent[s, i] -> map[s] FormComponent[s, i] for every mapped s (every occurrence).
    Effects: Pure.
    Failures: None.
    Example: replaceSlotComponents[Y1 L1 + Y2 L2, <|s -> a|>] is a Y1 L1 + a Y2 L2.
    Remarks: Consistent with v1 AddCoeffToY: each occurrence of a Y component gets the factor, so a power Y^2 gets a^2.
    See also: rebuildSlotTerm.
*)
replaceSlotComponents[expr_, map_Association] := expr /. FormComponent[s_String, i_Integer] /; KeyExistsQ[map, s] :> map[s] FormComponent[s, i];

(*
    Summary: A term with per-slot coefficients applied, as a new term.
    Parameters: term — coupled-expression data; map — <|slotID -> coefficient|>; records — <|slotID -> parameter records|>.
    Options/defaults: None.
    Returns: Term data with a fresh TermID, replaced expressions and value, merged parameters; or the term unchanged when
        it uses none of the mapped slots; or Failure.
    Effects: Allocates a term ID.
    Failures: ParameterConflict.
    Example: an L.R.Y term with map <|s -> a|> becomes a c L.R.Y with parameters {c, a}.
    Remarks: The value stays the sum of coefficient times expression (validateCoupledExpression), since the factor goes
        into each expression.
    See also: addFormCouplingData.
*)
rebuildSlotTerm[term_Association, map_Association, records_Association] := Module[{slots, parameters},
    slots = Select[Keys[map], !FreeQ[term["Value"], FormComponent[#, _]] &];
    If[slots === {}, Return[term]];
    parameters = mergeParameterRecords[Join[{term["Parameters"]}, Lookup[records, slots]]]; If[FailureQ[parameters], Return[parameters]];
    Join[term, <|"TermID" -> "term-" <> CreateUUID[], "Terms" -> Map[Join[#, <|"Expression" -> Expand[replaceSlotComponents[#["Expression"], map]]|>] &, term["Terms"]],
        "Value" -> Expand[replaceSlotComponents[term["Value"], map]], "Parameters" -> parameters|>]
];

(*
    Summary: A modular model with one coupling per selected used slot (AddModularFormCouplings' work).
    Parameters: model — modular model data; selection — All or a list of slot IDs; effective — validated options.
    Options/defaults: FormCouplings Automatic (fresh couplings) or <|slotID -> coefficient|> for the selected slots;
        CouplingPrefix "a"; ParameterSymbols {}.
    Returns: New model data, or Failure (the input model is unchanged).
    Effects: Registers new parameter records.
    Failures: InvalidSelection (unknown, unused or repeated slot IDs); InvalidOption (FormCouplings not covering exactly the
        selected slots); CouplingConflict (an explicit coefficient for a slot that already has another recorded one);
        FieldDependentCoupling; UndeclaredSymbol; term insertion failures.
    Example: addFormCouplingData[m, All, opts]["ModularData"]["SlotCouplings"] has one entry per used slot.
    Remarks: Slots with a recorded coupling keep it (no second factor), so a repeated call returns an equal model. The new
        model's affected terms have new TermIDs and are re-inserted with full covariance and weight checks.
    See also: AddModularFormCouplings; rebuildSlotTerm.
*)
addFormCouplingData[model_Association, selection_, effective_Association] := Module[{used = usedSlots[model], md = model["ModularData"], selected, fresh, explicit,
        resolved, map, records, terms, rebuilt},
    selected = If[selection === All, used, selection];
    If[!ListQ[selected] || !DuplicateFreeQ[selected] || !SubsetQ[used, selected],
        Return[makeFailure["InvalidSelection", "Select used slots of the model once each (All selects every used slot).", <|"Unused" -> If[ListQ[selected], Complement[selected, used], selected]|>]]];
    explicit = effective[FormCouplings];
    If[explicit =!= Automatic && (!AssociationQ[explicit] || Sort[Keys[explicit]] =!= Sort[selected]),
        Return[makeFailure["InvalidOption", "FormCouplings must give a coefficient for exactly the selected slots.", <|"Options" -> {FormCouplings}|>]]];
    If[explicit =!= Automatic, With[{conflicts = Select[selected, KeyExistsQ[md["SlotCouplings"], #] && !resolvedSameCoefficientQ[md["SlotCouplings"][#], explicit[#]] &]},
        If[conflicts =!= {}, Return[makeFailure["CouplingConflict", "A slot already has another recorded coupling; it cannot be replaced.", <|"SlotIDs" -> conflicts|>]]]]];
    fresh = Select[selected, !KeyExistsQ[md["SlotCouplings"], #] &];
    If[fresh === {}, Return[model]];
    resolved = resolveCouplingParameters[If[explicit === Automatic, Automatic, Lookup[explicit, fresh]], Length[fresh], effective[ParameterSymbols],
        effective[CouplingPrefix], {}];
    If[FailureQ[resolved], Return[resolved]];
    If[!FreeQ[resolved["Coefficients"], _FormComponent], Return[makeFailure["FieldDependentCoupling", "Form couplings must not contain form or field components."]]];
    map = AssociationThread[fresh, resolved["Coefficients"]];
    records = AssociationThread[fresh, Map[Function[c, Lookup[$CouplingRecords, First /@ DeleteDuplicates[Cases[{c}, Coupling[_String], {0, Infinity}]]]], resolved["Coefficients"]]];
    terms = Map[rebuildSlotTerm[#, map, records] &, model["Terms"]];
    If[AnyTrue[terms, FailureQ], Return[FirstCase[terms, _Failure]]];
    rebuilt = Fold[Function[{m, t}, If[FailureQ[m], m, addModularTermData[m, t, effective[Verification]]]],
        Join[model, <|"Terms" -> {}, "Parameters" -> {}, "Validation" -> <|"Status" -> "Covariant", "Arithmetic" -> model["Arithmetic"],
                (* the inputs' status survives the rebuild; the rebuilt terms add theirs (methodOptionsPlan.md 2C.2) *)
                "VerificationStatus" -> cgWeakestStatus[{modelInputsStatus[First[model["Context"]], Lookup[model["Fields"], "IrrepID", {}], model["TargetIrrepID"],
                    model["Arithmetic"]], suppliedSlotsStatus[model]}]|>,
            "ModularData" -> Join[md, <|"SlotCouplings" -> Join[md["SlotCouplings"], AssociationThread[fresh, Map[<|"Coefficient" -> map[#], "Parameters" -> records[#]|> &, fresh]]]|>]|>],
        terms];
    rebuilt
];
resolvedSameCoefficientQ[record_Association, coefficient_] := record["Coefficient"] === coefficient;

Options[AddModularFormCouplings] = {FormCouplings -> Automatic, CouplingPrefix -> "a", ParameterSymbols -> {}, Verification -> Automatic};

(*
    Summary: Multiply each selected used form slot by its own physical coupling throughout the model.
    Status: Alpha.
    Signatures: AddModularFormCouplings[m, opts]; AddModularFormCouplings[m, slotIDs, opts].
    Parameters: m — modular Model; slotIDs — All (default: every used slot) or a list of used slot IDs.
    Options/defaults: FormCouplings -> Automatic (a fresh coupling per selected slot) or <|slotID -> coefficient|> (stage 5
        declaration rules through ParameterSymbols); CouplingPrefix -> "a"; ParameterSymbols -> {}; Verification -> the
        level of the re-insertion covariance checks (as AddModelTerm).
    Returns: New Model with new affected terms, updated parameters and the recorded slot -> coupling map
        (ModularData "SlotCouplings"), or Failure (the input model is unchanged).
    Effects: Registers new parameter records.
    Failures: InvalidModel; NotModularModel; as addFormCouplingData.
    Example: AddModularFormCouplings[AddModularFormCouplings[m]] === AddModularFormCouplings[m] (no duplicate factor).
    Remarks: Repeated components and copies of one slot share its coupling; different slots get independent couplings.
        This may add redundant parameterizations relative to the independent channel couplings; it records a per-slot
        factor map, not new independent physics. Re-extract matrices from the new ModelExpression.
    See also: ModularContractions; ExtractBilinearMatrix.
*)
AddModularFormCouplings[m_Model, selection : (All | _List) : All, options : OptionsPattern[]] := Module[{model = validateModelSchema[m], effective, data},
    If[FailureQ[model], Return[model]];
    If[!KeyExistsQ[model, "ModularData"], Return[makeFailure["NotModularModel", "The model has no modular weights; create it with CreateModularModel."]]];
    effective = resolveOperationOptions[AddModularFormCouplings, "AddModularFormCouplings", {options}]; If[FailureQ[effective], Return[effective]];
    data = addFormCouplingData[model, selection, effective];
    Which[FailureQ[data], data, data === model, m, True, Model[data]]
];
AddModularFormCouplings[___] := makeFailure["InvalidInput", "AddModularFormCouplings expects a modular Model, an optional slot selection and options."];

True
