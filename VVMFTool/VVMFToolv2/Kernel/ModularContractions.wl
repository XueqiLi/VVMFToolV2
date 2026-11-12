(*
    :Title: Contractions of model fields with formal modular forms
    :Context: VVMFTool`Private`
    :Summary: Y-augmented products: the fields' product (once, character-pruned), grouped by actual weight, times the
        joined vector of the matching formal slots as the last left-associated factor; all copies, paths and zeros kept.
        The representation-valued result (ModularTensorProductVectors), its scalar-target contraction set
        (ModularContractions) with slot components as formal variables, and term insertion with slot registration,
        formal covariance and weight homogeneity (D-S8-4, D-S8-6, D-S8-7).
    :Responsibilities: slotVector, modularCGSettings, buildModularVectorProducts, contractWithFormSlots,
        modularPolynomialVariables, validateModularContraction, registerTermSlots, addModularTermData;
        ModularTensorProductVectors, ModularContractions.
    :Dependencies: ModularCandidates.wl (candidateData, selectModularCandidates, recomputeSlotRecord); WeightedVectors.wl;
        Contractions.wl (ContractionSet); Models.wl (addTermData).
    :See Also: VVMFArch/step8Plan.md (candidates and contractions); D-S8-4, D-S8-6, D-S8-7.
*)

(*
    Summary: The weighted vector of formal slots (one leaf channel per slot, actual weight kY).
    Parameters: context — the model's RepresentationContext; slots — slot records; supplied — IDs of the spaces the user
        supplied (SupplyModularFormSpace; default {}).
    Options/defaults: None.
    Returns: Weighted data whose channels are the slots' FormComponent vectors, or Failure. A slot of a supplied space has
        the status "Unverified" (the space's completeness is the user's assertion, methodOptionsPlan.md 2C.4).
    Effects: Pure.
    Failures: makeWeightedVector failures.
    Example: one weight-2 triplet slot gives one channel of weight 2 with three components.
    Remarks: A slot leaf's path names the slot ID, so every product channel records which copy it used.
    See also: buildModularVectorProducts.
*)
slotVector[context_RepresentationContext, slots_List, supplied_List : {}] := Module[{records, vector},
    records = Map[Join[<|"TargetID" -> #["IrrepID"], "Components" -> #["Components"], "Path" -> <|"Kind" -> "Leaf", "VectorID" -> #["ID"]|>, "BasisID" -> #["BasisID"],
        "ChannelIDs" -> {}|>, If[MemberQ[supplied, #["SpaceID"]], <|"VerificationStatus" -> "Unverified"|>, <||>]] &, slots];
    vector = makeVectorData[context, records, AssociationThread[Lookup[slots, "ID", {}], ConstantArray["Y", Length[slots]]]];
    With[{w = makeWeightedVector[vector, AssociationThread[weightedChannelID /@ First[vector]["Records"], Lookup[slots, "Weight", {}]],
            AssociationThread[Lookup[slots, "ID", {}], slots], {}, Missing["NotUsed"]]}, If[FailureQ[w], w, First[w]]]
];

(*
    Summary: Arithmetic settings and forwarded CG options of a modular product.
    Parameters: model — modular model data; irreps — every irrep the product touches (fields, slots, targets); options —
        supplied option rules.
    Options/defaults: The model's arithmetic, precision and tolerance unless supplied.
    Returns: <|"Settings" -> arithmetic settings, "Forwarded" -> CG option rules|>, or Failure.
    Effects: Pure.
    Failures: arithmeticSettings and checkedTolerance failures.
    Example: an exact model gives exact settings and forwards Arithmetic -> "Exact".
    Remarks: The same rules as Stage 5 contractions (reviews M7, M25, M29): the representation data of every touched irrep
        and of the left-associated intermediates bound the precision.
    See also: buildContractionSet.
*)
modularCGSettings[model_Association, irreps_List, options_List] := Module[{supplied = Association[options], snapshot = First[model["Context"]], arithmetic, precision, settings},
    arithmetic = Lookup[supplied, Arithmetic, model["Arithmetic"]];
    precision = dataPrecision[Map[repMatrices, Lookup[DeleteMissing[cgVariant[snapshot, #] & /@ DeleteDuplicates[Join[irreps, intermediateIrreps[snapshot, irreps]]]], "Rep", {}]]];
    settings = If[arithmetic === "Exact", arithmeticSettings["Exact", 50, Automatic, precision],
        arithmeticSettings["Numerical", Lookup[supplied, WorkingPrecision, If[NumericQ[model["Precision"]], model["Precision"], 50]], Lookup[supplied, Tolerance, model["Tolerance"]], precision]];
    If[FailureQ[settings], Return[settings]];
    settings = checkedTolerance[settings, precision =!= Infinity]; If[FailureQ[settings], Return[settings]];
    (* the call's domain choice (methodOptionsPlan.md 1.3); the session default when not supplied *)
    settings = cgCheckSettings[settings, <|NumberField -> Lookup[supplied, NumberField, Automatic],
        FieldMethod -> Lookup[supplied, FieldMethod, OptionValue[Contractions, FieldMethod]]|>];
    <|"Settings" -> settings, "Forwarded" -> Join[FilterRules[options, Options[CGCoefficients]], If[KeyExistsQ[supplied, Arithmetic], {}, {Arithmetic -> arithmetic}],
        If[arithmetic === "Numerical" && !KeyExistsQ[supplied, WorkingPrecision], {WorkingPrecision -> settings["Precision"]}, {}],
        If[arithmetic === "Numerical" && !KeyExistsQ[supplied, Tolerance] && model["Tolerance"] =!= Automatic, {Tolerance -> model["Tolerance"]}, {}]]|>
];

(*
    Summary: All Y-augmented channels of the requested targets.
    Parameters: model — modular model data; resolved — validated weighted factors; candidates — candidate data;
        chosen — selectModularCandidates result; targets — irrep IDs; options — CG option rules.
    Options/defaults: CG options as Contractions.
    Returns: WeightedRepVector data (channels of total actual weight kW with their slot records), or Failure.
    Effects: CG computation in the model's frozen context.
    Failures: CG and vector failures.
    Example: T' triplet fields of label 1 with the weight-2 triplet slot give the scalar channels of L R Y.
    Remarks: The fields' product is formed once with the irreps that can still reach a target with a chosen slot; its
        channels are grouped by actual weight w and each group is multiplied by the joined slots of weight kW - w as the
        last factor (v1 order: fields, then Y). Every copy, zero and path is kept.
    See also: ModularTensorProductVectors; contractWithFormSlots.
*)
buildModularVectorProducts[model_Association, resolved_List, candidates_Association, chosen_Association, targets_List, options_List] := Module[
    {characters = First[model["Context"]]["CharacterData"], slotIrreps, fieldTargets, fieldProduct, groups, products, kW = model["ModularData"]["SuperpotentialWeight"], empty},
    empty = First[makeWeightedVector[makeVectorData[model["Context"], {}, <||>], <||>, AssociationThread[Lookup[chosen["Slots"], "ID", {}], chosen["Slots"]], {}, Missing["NotUsed"]]];
    If[chosen["Slots"] === {}, Return[empty]];
    slotIrreps = DeleteDuplicates[Lookup[chosen["Slots"], "IrrepID"]];
    fieldTargets = Select[characters["IrrepIDs"], Function[s, AnyTrue[slotIrreps, IntersectingQ[Keys[characterPairProduct[characters, s, #]], targets] &]]];
    fieldProduct = weightedTensorChannels[model["Context"], resolved, Append[options, TargetIrreps -> fieldTargets]]; If[FailureQ[fieldProduct], Return[fieldProduct]];
    fieldProduct = First[fieldProduct];
    groups = GroupBy[Transpose[{First[fieldProduct["Vector"]]["Records"], Lookup[fieldProduct["Weights"], fieldProduct["ChannelIDs"]]}], Last -> First];
    products = KeyValueMap[Function[{w, records}, With[{slots = Select[chosen["Slots"], #["Weight"] === kW - w &]},
            If[slots === {}, Nothing, Module[{group = makeWeightedVector[makeVectorData[model["Context"], records, First[fieldProduct["Vector"]]["Labels"]],
                        AssociationThread[weightedChannelID /@ records, ConstantArray[w, Length[records]]], <||>, {}, Missing["NotUsed"]], ys = slotVector[model["Context"], slots, Keys[Lookup[model["ModularData"], "SuppliedSpaces", <||>]]]},
                If[FailureQ[group], Return[group, Module]]; If[FailureQ[ys], Return[ys, Module]];
                weightedTensorChannels[model["Context"], {First[group], ys}, Append[options, TargetIrreps -> targets]]]]]], groups];
    If[AnyTrue[products, FailureQ], Return[FirstCase[products, _Failure]]];
    If[products === {}, Return[empty]];
    With[{joined = joinWeightedVectors[First /@ products]}, If[FailureQ[joined], joined,
        (* Every admitted channel has total actual weight kW by construction; the filter states the rule. *)
        Module[{data = First[joined], keep},
            keep = Select[Transpose[{First[data["Vector"]]["Records"], data["ChannelIDs"]}], data["Weights"][Last[#]] === kW &];
            First[makeWeightedVector[makeVectorData[model["Context"], keep[[All, 1]], First[data["Vector"]]["Labels"]], KeyTake[data["Weights"], keep[[All, 2]]],
                AssociationThread[Lookup[chosen["Slots"], "ID", {}], chosen["Slots"]], {}, Missing["NotUsed"]]]]]]
];

(*
    Summary: The formal variables of a modular contraction: field components and slot components.
    Parameters: data — association with "ResolvedFactors" (weighted data) and "Slots" (slot records).
    Options/defaults: None.
    Returns: Duplicate-free list of FieldComponent and FormComponent atoms.
    Effects: Pure.
    Failures: None.
    Example: L R Y with a triplet slot has 3 + 1 + 3 variables.
    Remarks: Independence treats both kinds as commuting formal variables; no analytic relation between forms is used
        (D-S8-6).
    See also: contractWithFormSlots; IndependentContractions.
*)
modularPolynomialVariables[data_Association] := DeleteDuplicates[Join[
    Cases[Map[First[#["Vector"]]["Records"] &, data["ResolvedFactors"]], _FieldComponent, Infinity],
    Flatten[Lookup[data["Slots"], "Components", {}]]]];

(*
    Summary: The scalar contraction set of a modular product (ModularContractions' work).
    Parameters: model — modular model data; factors — model factors; effective — validated options; supplied — the caller's
        option rules (only these CG options are forwarded).
    Options/defaults: FormSelection, DimensionCache, CG options.
    Returns: ContractionSet data with the Stage 5 keys plus "FormSlots", "Weights", "CandidateReport", "Coverage",
        or Failure.
    Effects: CG computation; character and dimension caches.
    Failures: candidate, selection and CG failures.
    Example: the T' example gives one channel L.R.Y in the trivial target.
    Remarks: Channel IDs hash the factor channel IDs and the path; polynomials and zero flags as Stage 5; the set's
        variables include the slot components (D-S8-6).
    See also: ModularContractions; buildModularVectorProducts.
*)
contractWithFormSlots[model_Association, factors_List, effective_Association, supplied_List] := Module[{candidates, chosen, irreps, settings, product, records, channels, cgOptions},
    candidates = candidateData[model, factors, <|TargetIrreps -> Automatic, DimensionCache -> effective[DimensionCache]|>]; If[FailureQ[candidates], Return[candidates]];
    chosen = selectModularCandidates[candidates, effective[FormSelection]]; If[FailureQ[chosen], Return[chosen]];
    (* Only the caller's CG options are forwarded, so the model's own arithmetic applies otherwise (as Stage 5). *)
    cgOptions = FilterRules[supplied, Except[FormSelection | DimensionCache | TargetIrreps]];
    irreps = DeleteDuplicates[Join[Flatten[Lookup[candidates["Factors"], "Irreps", {}]], Lookup[chosen["Slots"], "IrrepID", {}], {model["TargetIrrepID"]}]];
    settings = modularCGSettings[model, irreps, cgOptions]; If[FailureQ[settings], Return[settings]];
    product = buildModularVectorProducts[model, candidates["ResolvedFactors"], candidates, chosen, {model["TargetIrrepID"]}, settings["Forwarded"]];
    If[FailureQ[product], Return[product]];
    records = First[product["Vector"]]["Records"];
    channels = Map[Function[record, With[{p = Expand[First[record["Components"]]]},
            <|"ChannelID" -> "path:" <> StringTake[Hash[{Lookup[candidates["Factors"], "ChannelIDs"], record["Path"]}, "SHA256", "HexString"], 16],
                "Path" -> record["Path"], "ChannelIDs" -> record["ChannelIDs"], "Polynomial" -> p, "Weight" -> product["Weights"][weightedChannelID[record]],
                "Slots" -> DeleteDuplicates[Cases[record["Path"], <|"Kind" -> "Leaf", "VectorID" -> s_String|> /; StringStartsQ[s, "slot:"] :> s, Infinity]],
                "Zero" -> If[settings["Settings"]["Arithmetic"] === "Exact", p === 0 || TrueQ[cgZeroTest[p, cgArithmetic[{}, settings["Settings"]]]],
                    AllTrue[Flatten[{CoefficientList[p, modularPolynomialVariables[<|"ResolvedFactors" -> candidates["ResolvedFactors"], "Slots" -> chosen["Slots"]|>]]}],
                        Abs[#] <= settings["Settings"]["Tolerance"] &]],
                "VerificationStatus" -> Lookup[record, "VerificationStatus", "Exact"]|>]], records];
    <|"SchemaVersion" -> 1, "ID" -> "contractions-" <> CreateUUID[], "ModelID" -> model["ID"], "ContextDigest" -> model["ContextDigest"],
        "TargetIrrepID" -> model["TargetIrrepID"], "Factors" -> Map[#["ChannelIDs"] &, candidates["ResolvedFactors"]],
        "FieldIDs" -> DeleteDuplicates[Cases[Map[First[#["Vector"]]["Records"] &, candidates["ResolvedFactors"]], FieldComponent[f_String, _] :> f, Infinity]],
        "Variables" -> modularPolynomialVariables[<|"ResolvedFactors" -> candidates["ResolvedFactors"], "Slots" -> chosen["Slots"]|>],
        "Channels" -> channels, "RawChannels" -> channels, "Independence" -> Missing["NotComputed"], "Arithmetic" -> settings["Settings"]["Arithmetic"],
        "Precision" -> settings["Settings"]["Precision"], "Tolerance" -> settings["Settings"]["Tolerance"], "FieldMethod" -> settings["Settings"]["FieldMethod"],
        "VerificationStatus" -> contractionChannelsStatus[channels],
        "FieldNames" -> AssociationThread[Lookup[model["Fields"], "ID", {}], Lookup[model["Fields"], "Name", {}]], "Context" -> model["Context"],
        "FormSlots" -> AssociationThread[Lookup[chosen["Slots"], "ID", {}], chosen["Slots"]], "SuperpotentialWeight" -> model["ModularData"]["SuperpotentialWeight"],
        "Namespace" -> model["ModularData"]["SlotNamespaceID"], "Coverage" -> chosen["Coverage"], "Selection" -> chosen["Selection"],
        "CandidateReport" -> KeyDrop[candidates, "ResolvedFactors"]|>
];

(*
    Summary: Check the modular records of a contraction set.
    Parameters: data — ContractionSet data.
    Options/defaults: None.
    Returns: data, or InvalidContractionSet Failure.
    Effects: Pure.
    Failures: InvalidContractionSet (a channel of another weight than the set's kW, slot atoms without records, or slot
        components missing from the variables).
    Example: a set whose channel weight was edited fails here.
    See also: ModularContractions.
*)
validateModularContraction[data_Association] := Module[{slots = Lookup[data, "FormSlots", <||>], atoms},
    atoms = DeleteDuplicates[Cases[Lookup[data["RawChannels"], "Polynomial", {}], FormComponent[s_String, _] :> s, Infinity]];
    If[!AssociationQ[slots] || !SubsetQ[Keys[slots], atoms] || !SubsetQ[data["Variables"], Flatten[Lookup[Values[slots], "Components", {}]]] ||
            !AllTrue[data["RawChannels"], Lookup[#, "Weight", data["SuperpotentialWeight"]] === data["SuperpotentialWeight"] &],
        makeFailure["InvalidContractionSet", "The set's form slots, variables or channel weights are inconsistent."], data]
];

(*
    Summary: Register the slots a term uses in a model (recomputed, never trusted).
    Parameters: model — modular model data; term — coupled-expression data.
    Options/defaults: None.
    Returns: Model data whose ModularData lists every slot and space the term uses, or Failure.
    Effects: Reads the dimension cache.
    Failures: UnknownComponent (a slot atom with neither a registered record nor a carried record); ForeignSlot and
        InvalidSlot (recomputeSlotRecord); SlotConflict (a carried record that differs from the recomputed or registered
        one).
    Example: the first L.R.Y term registers the weight-2 triplet slot and its space.
    See also: addModularTermData; recomputeSlotRecord.
*)
registerTermSlots[model_Association, term_Association] := Module[{md = model["ModularData"], used, carried = Lookup[term, "FormSlots", <||>], records},
    used = DeleteDuplicates[Cases[term["Value"], FormComponent[s_String, _] :> s, {0, Infinity}]];
    records = Map[Function[id, Which[
        KeyExistsQ[md["Slots"], id], If[KeyExistsQ[carried, id] && carried[id] =!= md["Slots"][id],
            makeFailure["SlotConflict", "The term's slot record differs from the model's registered slot.", <|"SlotID" -> id|>], md["Slots"][id]],
        KeyExistsQ[carried, id], With[{r = recomputeSlotRecord[model, carried[id]]}, Which[FailureQ[r], r,
            r =!= carried[id] || r["ID"] =!= id, makeFailure["SlotConflict", "A carried slot record differs from its recomputation in the model's namespace.", <|"SlotID" -> id|>],
            True, r]],
        True, makeFailure["UnknownComponent", "The term uses a form slot that is neither registered in the model nor carried with its record; build it with ModularContractions or ModularTensorProductVectors of this model.",
            <|"SlotID" -> id|>]]], used];
    If[AnyTrue[records, FailureQ], Return[FirstCase[records, _Failure]]];
    Join[model, <|"ModularData" -> Join[md, <|"Slots" -> Join[md["Slots"], AssociationThread[Lookup[records, "ID", {}], records]],
        "Spaces" -> Join[md["Spaces"], AssociationThread[Lookup[records, "SpaceID", {}], Map[KeyTake[#, {"SpaceID", "IrrepID", "Weight", "SpaceDimension", "FormalBasisID"}] &, records]]]|>]|>]
];

(*
    Summary: A modular model with one more term: slots registered, formal covariance, weight homogeneity.
    Parameters: model — modular model data; term — coupled-expression data.
    Options/defaults: None.
    Returns: New model data, or Failure (the input model is unchanged).
    Effects: Pure.
    Failures: registerTermSlots failures; addTermData failures (covariance under fields and slots, contexts, targets,
        parameters); InconsistentWeight (a monomial whose total actual weight is not kW); TargetMismatch for a set built on
        another namespace.
    Example: an L.R.Y term with kf = 1, 1 and kY = 2 at kW = 0 is accepted; L.L alone (weight -2) is not.
    Remarks: Covariance is formal: Y transforms with its slot's representation; nothing analytic is claimed. Pure field
        terms enter only when their weight is already kW.
    See also: AddModelTerm; registerTermSlots.
*)
addModularTermData[model_Association, term_Association, level_ : Automatic] := Module[{registered, added, violations},
    If[StringQ[Lookup[term, "Namespace", None]] && term["Namespace"] =!= model["ModularData"]["SlotNamespaceID"],
        Return[makeFailure["ForeignSlot", "The term was built for another model namespace; rebuild it in this model."]]];
    registered = registerTermSlots[model, term]; If[FailureQ[registered], Return[registered]];
    violations = monomialWeightViolations[term["Value"], registered, model["ModularData"]["SuperpotentialWeight"]];
    If[violations =!= {}, Return[makeFailure["InconsistentWeight", "A monomial of the term does not have the model's total actual weight kW.",
        <|"Violations" -> Take[violations, UpTo[3]], "SuperpotentialWeight" -> model["ModularData"]["SuperpotentialWeight"]|>]]];
    added = addTermData[registered, term, level];
    added
];

Options[ModularTensorProductVectors] = Join[Options[Contractions], {TargetIrreps -> Automatic, FormSelection -> All, DimensionCache -> True, DimensionMethod -> Automatic}];

(*
    Summary: The representation-valued channels of model fields times formal modular forms, for any targets.
    Status: Alpha.
    Parameters: m — modular Model; factors — list of Fields, field IDs or weighted vectors of the model's fields.
    Options/defaults: TargetIrreps -> Automatic (the model target; an ID, a list or All, higher dimensions allowed);
        FormSelection -> All (exhaustive, needs every relevant count) or a duplicate-free list of slot IDs of the candidate
        report; DimensionCache -> True; CG options as Contractions.
    Returns: WeightedRepVector whose channels have total actual weight kW, with "FormSlots", "CandidateReport" and
        "Selection" (<|"Coverage" -> "Exhaustive" | "Selected", ...|>), or Failure.
    Effects: CG computation in the model's frozen context; character and dimension caches.
    Failures: InvalidModel; NotModularModel; IncompleteModularSpace; InvalidSelection; candidate, option and CG failures.
    Example: ModularTensorProductVectors[m, {l, r}, TargetIrreps -> t] keeps every triplet copy of L R Y.
    Remarks: No claim that a component sum is a scalar: select components and couple them with CoupleExpressions (an
        Unverified raw term); AddModelTerm later requires scalar covariance.
    See also: ModularContractions; ModularFormCandidates.
*)
ModularTensorProductVectors[m_Model, factors_List, options : OptionsPattern[]] :=
    Block[{$formalDimensionMethod = Replace[Lookup[Association[FilterRules[Flatten[{options}], DimensionMethod]], DimensionMethod, Automatic], Except[Automatic | "Profile" | "TraceFormula"] -> Automatic]},
        modularTensorProductVectorsWork[m, factors, options]];
modularTensorProductVectorsWork[m_Model, factors_List, options : OptionsPattern[ModularTensorProductVectors]] := Module[{model = validateModelSchema[m], effective, candidates, chosen, targets, irreps, cgOptions, settings, product},
    If[FailureQ[model], Return[model]];
    If[!KeyExistsQ[model, "ModularData"], Return[makeFailure["NotModularModel", "The model has no modular weights; create it with CreateModularModel."]]];
    effective = resolveOperationOptions[ModularTensorProductVectors, "ModularTensorProductVectors", {options}]; If[FailureQ[effective], Return[effective]];
    effective = resolveIrrepOptions[model["Context"], effective]; If[FailureQ[effective], Return[effective]];
    candidates = candidateData[model, factors, <|TargetIrreps -> effective[TargetIrreps], DimensionCache -> effective[DimensionCache]|>]; If[FailureQ[candidates], Return[candidates]];
    chosen = selectModularCandidates[candidates, effective[FormSelection]]; If[FailureQ[chosen], Return[chosen]];
    targets = candidates["TargetIrreps"];
    cgOptions = FilterRules[{options}, Except[FormSelection | DimensionCache | TargetIrreps]];
    irreps = DeleteDuplicates[Join[Flatten[Lookup[candidates["Factors"], "Irreps", {}]], Lookup[chosen["Slots"], "IrrepID", {}], targets]];
    settings = modularCGSettings[model, irreps, cgOptions]; If[FailureQ[settings], Return[settings]];
    product = buildModularVectorProducts[model, candidates["ResolvedFactors"], candidates, chosen, targets, settings["Forwarded"]];
    If[FailureQ[product], product,
        WeightedRepVector[Join[product, <|"CandidateReports" -> {KeyDrop[candidates, "ResolvedFactors"]}, "Selection" -> KeyTake[chosen, {"Coverage", "Selection"}]|>]]]
];
ModularTensorProductVectors[___] := makeFailure["InvalidInput", "ModularTensorProductVectors expects a modular Model, a list of factors and options."];

Options[ModularContractions] = Join[Options[Contractions], {FormSelection -> All, DimensionCache -> True, DimensionMethod -> Automatic}];

(*
    Summary: Every CG contraction of model fields with formal modular forms into the model's degree-one target.
    Status: Alpha.
    Parameters: m — modular Model; factors — list of Fields, field IDs or weighted vectors of the model's fields.
    Options/defaults: FormSelection -> All or a list of slot IDs; DimensionCache -> True; CG options as Contractions.
    Returns: ContractionSet whose channels are linear in one formal Y factor (all copies, paths and zeros), with
        FormSlots, Weights, Coverage and the candidate report; or Failure.
    Effects: As ModularTensorProductVectors.
    Failures: As ModularTensorProductVectors.
    Example: ModularContractions[m0, {left, right}] has one channel for the T' triplet example.
    Remarks: IndependentContractions treats Y components as formal commuting variables; CoupleContractions and
        AddModelTerm work as in Stage 5, with slots registered on insertion. Contractions[m, ...] remains the field-only
        operation.
    See also: ModularTensorProductVectors; CoupleContractions; AddModelTerm.
*)
ModularContractions[m_Model, factors_List, options : OptionsPattern[]] :=
    Block[{$formalDimensionMethod = Replace[Lookup[Association[FilterRules[Flatten[{options}], DimensionMethod]], DimensionMethod, Automatic], Except[Automatic | "Profile" | "TraceFormula"] -> Automatic]},
        modularContractionsWork[m, factors, options]];
modularContractionsWork[m_Model, factors_List, options : OptionsPattern[ModularContractions]] := Module[{model = validateModelSchema[m], effective, data},
    If[FailureQ[model], Return[model]];
    If[!KeyExistsQ[model, "ModularData"], Return[makeFailure["NotModularModel", "The model has no modular weights; create it with CreateModularModel."]]];
    effective = resolveOperationOptions[ModularContractions, "ModularContractions", {options}]; If[FailureQ[effective], Return[effective]];
    effective = resolveIrrepOptions[model["Context"], effective]; If[FailureQ[effective], Return[effective]];
    data = cgFieldCatch[contractWithFormSlots[model, factors, effective, {options}]]; If[FailureQ[data], Return[data]];
    data = validateModularContraction[data];
    If[FailureQ[data], data, ContractionSet[data]]
];
ModularContractions[___] := makeFailure["InvalidInput", "ModularContractions expects a modular Model, a list of factors and options."];

True
