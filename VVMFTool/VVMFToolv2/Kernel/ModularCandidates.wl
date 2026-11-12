(*
    :Title: Modular-form candidates of model factors
    :Context: VVMFTool`Private`
    :Summary: The formal form spaces a product of model fields needs to reach requested targets at the model's weight:
        character-pruned form irreps per factor-channel combination, Stage 7 dimension counts (unknown is never zero),
        deterministic space and slot identities in the model's namespace, and explicit slot selection (D-S8-4, D-S8-5).
    :Responsibilities: resolveModularTargets, factorChannelCombinations, filterCandidateIrreps, requiredModularSpaces,
        spaceKey, spaceRecordID, formalSlotID, makeFormalSpace, establishedSpaceQ, makeSlotRecord, recomputeSlotRecord, selectModularCandidates;
        ModularFormCandidateData, ModularFormCandidates.
    :Dependencies: ModularModels.wl; WeightedVectors.wl (resolveModularFactors); TensorCharacters.wl
        (characterPairProduct, tensorMultiplicities); ModularDimensions.wl (ModularDimension).
    :See Also: VVMFArch/step8Plan.md (candidates and contractions); D-S8-4, D-S8-5.
*)

(*
    Summary: The requested target irreps of a candidate or vector operation.
    Parameters: model — modular model data; targets — TargetIrreps option value (Automatic, an ID, a list or All).
    Options/defaults: Automatic is the model's (degree-one) target.
    Returns: Duplicate-free list of irrep IDs, or InvalidIrrep Failure.
    Effects: Pure.
    Failures: InvalidIrrep (unknown IDs).
    Example: resolveModularTargets[m, Automatic] is {m's TargetIrrepID}.
    See also: ModularFormCandidates; ModularTensorProductVectors.
*)
resolveModularTargets[model_Association, targets_] := Module[{ids = First[model["Context"]]["CharacterData"]["IrrepIDs"], list},
    list = Which[targets === Automatic, {model["TargetIrrepID"]}, targets === All, ids, StringQ[targets], {targets}, True, targets];
    If[!SubsetQ[ids, list], makeFailure["InvalidIrrep", "Unknown target irrep ID.", <|"IrrepIDs" -> Complement[list, ids]|>], DeleteDuplicates[list]]
];

(*
    Summary: Every choice of one channel per factor with its irreps and total actual weight.
    Parameters: factors — validated weighted data (model factors) in product order.
    Options/defaults: None.
    Returns: List of <|"ChannelIDs", "Irreps", "Weight"|> (one entry, the empty choice of weight 0, for no factors).
    Effects: Pure.
    Failures: None.
    Example: a doublet-plus-singlet family times a triplet gives two combinations, of weights -3 and -2.
    See also: requiredModularSpaces.
*)
factorChannelCombinations[factors_List] := Map[Function[choice, <|"ChannelIDs" -> choice[[All, 1]], "Irreps" -> choice[[All, 2]], "Weight" -> Total[choice[[All, 3]]]|>],
    Tuples[Map[Function[f, MapThread[{#1, #2["TargetID"], f["Weights"][#1]} &, {f["ChannelIDs"], First[f["Vector"]]["Records"]}]], factors]]];

(*
    Summary: The form irreps r that let a field-product irrep reach a requested target.
    Parameters: characters — character data; product — association irrep -> multiplicity of the field product; targets — IDs.
    Options/defaults: None.
    Returns: Duplicate-free list of irrep IDs r (character-table order) such that s (x) r contains a target for some s of
        positive multiplicity, or Failure.
    Effects: Fills the character pair memo.
    Failures: characterPairProduct failures.
    Example: for T' triplet fields and the trivial target the trivial irrep and the triplet are candidates.
    Remarks: Character multiplicities only; a zero CG channel (for example an antisymmetric product of equal fields) is
        still a candidate, so nothing is lost before the exact contraction.
    See also: requiredModularSpaces.
*)
filterCandidateIrreps[characters_Association, product_Association, targets_List] := Module[{sources = Keys[Select[product, # > 0 &]], pairs},
    pairs = Table[With[{p = characterPairProduct[characters, s, r]}, If[FailureQ[p], p, {r, IntersectingQ[Keys[p], targets]}]], {s, sources}, {r, characters["IrrepIDs"]}];
    If[!FreeQ[pairs, _Failure], Return[FirstCase[pairs, _Failure, Null, Infinity]]];
    Select[characters["IrrepIDs"], Function[r, MemberQ[Flatten[pairs, 1], {r, True}]]]
];

(*
    Summary: The identity of a formal space and of its slots.
    Parameters: model — modular model data; irrep — form irrep ID; weight — exact rational kY; namespace — slot namespace;
        key — space key; copy — 1-based copy index.
    Options/defaults: None.
    Returns: spaceKey: {ContextDigest, AssignmentID, irrep, BasisID, kY}. spaceRecordID: "space:" plus 24 hex digits of the
        hash of the key. formalSlotID: "slot:" plus 24 hex digits of the hash
        of {namespace, key, copy}.
    Effects: Pure.
    Failures: None (the basis identity is Missing when the irrep has no accepted matrices).
    Example: repeated calls on one model lineage give the same slot IDs; another CreateModularModel gives other IDs.
    See also: makeFormalSpace.
*)
spaceKey[model_Association, irrep_String, weight_?modularWeightQ] := {model["ContextDigest"], model["ModularData"]["AssignmentID"], irrep,
    Lookup[Replace[cgVariant[First[model["Context"]], irrep], _Missing -> <||>], "Identity", Missing["NoRepresentation"]], weight};
spaceRecordID[key_List] := "space:" <> StringTake[Hash[key, "SHA256", "HexString"], 24];
formalSlotID[namespace_String, key_List, copy_Integer] := "slot:" <> StringTake[Hash[{namespace, key, copy}, "SHA256", "HexString"], 24];

(*
    Summary: A formal form space with its Stage 7 count and slot IDs.
    Parameters: model — modular model data; irrep — form irrep ID; weight — kY; dimensionCache — DimensionCache;
        useSupplied — whether a space the user supplied (SupplyModularFormSpace) replaces an unknown count (default True).
    Options/defaults: None.
    Returns: <|"ID", "Key", "IrrepID", "Weight", "Status" ("Known" | "Supplied" | "Unknown" | "Failed"), "Dimension" (integer or Missing),
        "Evidence", "FormalBasisID", "SlotIDs"|>.
    Effects: Reads and fills the Stage 7 dimension cache.
    Failures: None (a Stage 7 failure becomes Status "Failed" with its failure as evidence).
    Example: the T' triplet at weight 2 is Known with one slot.
    Remarks: Missing["UnknownDimension"] and Stage 7 failures (MissingExactSpectrum, MissingRepresentations) give no slots
        and make a report incomplete; they never mean zero (D-S8-4). An unknown space the user supplied (the model's
        SuppliedSpaces) has Status "Supplied", the number of supplied forms as its dimension and slots; a Stage 7 count
        always wins (a supplied record never changes a Known or Failed space).
    See also: requiredModularSpaces; makeSlotRecord.
*)
makeFormalSpace[model_Association, irrep_String, weight_?modularWeightQ, dimensionCache_, useSupplied_ : True] := Module[
    {key = spaceKey[model, irrep, weight], namespace = model["ModularData"]["SlotNamespaceID"], count, space, supplied},
    (* the dimension method of the calling operation (DimensionMethod, methodOptionsPlan.md 2B.7) *)
    count = ModularDimensionData[model["Context"], irrep, weight, DimensionCache -> dimensionCache, Method -> $formalDimensionMethod];
    space = spaceFromCount[key, namespace, irrep, weight, count];
    supplied = Lookup[Lookup[model["ModularData"], "SuppliedSpaces", <||>], space["ID"], None];
    If[TrueQ[useSupplied] && space["Status"] === "Unknown" && AssociationQ[supplied],
        Join[space, <|"Status" -> "Supplied", "Dimension" -> supplied["Dimension"],
            "Evidence" -> <|"Method" -> "Supplied", "Evidence" -> "The user supplied " <> ToString[supplied["Dimension"]] <>
                " independent forms as spanning this space (SupplyModularFormSpace); Stage 7 has no count.", "StageSevenCount" -> count["Dimension"]|>,
            "SlotIDs" -> Table[formalSlotID[namespace, key, i], {i, supplied["Dimension"]}]|>],
        space]
];

(*
    Summary: Whether a formal space has an established dimension (a Stage 7 count or a supplied space), so it has slots.
    Parameters: space — formal space record.
    Options/defaults: None.
    Returns: True or False.
    Effects: Pure.
    Failures: None.
    Example: a space of Status "Unknown" is not established.
    See also: makeFormalSpace.
*)
establishedSpaceQ[space_Association] := MemberQ[{"Known", "Supplied"}, space["Status"]];
spaceFromCount[key_List, namespace_String, irrep_String, weight_?modularWeightQ, count_] := Module[{status, dimension},
    {status, dimension} = Which[
        FailureQ[count], {"Failed", Missing["DimensionFailure", First[count]]},
        IntegerQ[count["Dimension"]], {"Known", count["Dimension"]},
        True, {"Unknown", count["Dimension"]}];
    <|"ID" -> spaceRecordID[key], "Key" -> key, "IrrepID" -> irrep, "Weight" -> weight, "Status" -> status,
        "Dimension" -> dimension, "Evidence" -> If[FailureQ[count], count, KeyTake[count, {"Method", "Evidence"}]],
        "FormalBasisID" -> "formal-" <> StringTake[Hash[{namespace, key}, "SHA256", "HexString"], 24],
        "SlotIDs" -> If[status === "Known", Table[formalSlotID[namespace, key, i], {i, dimension}], {}]|>
];

(*
    Summary: The record of one formal slot (copy) of a known space.
    Parameters: model — modular model data; space — known space record; copy — 1-based copy index.
    Options/defaults: None.
    Returns: <|"ID", "SpaceID", "Namespace", "ContextDigest", "GroupIdentity", "GeneratorIdentity", "AssignmentID", "IrrepID", "Rep", "BasisID",
        "Dimension" (of the irrep),
        "Weight" (kY), "Copy", "SpaceDimension", "FormalBasisID", "Components" -> {FormComponent[ID, i]...}|>, or Failure.
    Effects: Pure.
    Failures: MissingRepresentations (the form irrep has no accepted matrices in the model's context).
    Example: the weight-2 T' triplet slot has three components.
    Remarks: A slot is a chosen formal basis element of its space; its copy index is not an identification with a
        constructor seed (bindings decide which actual form occupies it).
    See also: recomputeSlotRecord.
*)
makeSlotRecord[model_Association, space_Association, copy_Integer] := Module[{variant = cgVariant[First[model["Context"]], space["IrrepID"]], id},
    If[MissingQ[variant], Return[makeFailure["MissingRepresentations", "The form irrep has no accepted matrices in the model's context.", <|"IrrepIDs" -> {space["IrrepID"]}|>]]];
    id = formalSlotID[model["ModularData"]["SlotNamespaceID"], space["Key"], copy];
    <|"ID" -> id, "SpaceID" -> space["ID"], "Namespace" -> model["ModularData"]["SlotNamespaceID"], "ContextDigest" -> model["ContextDigest"],
        "GroupIdentity" -> First[model["Context"]]["GroupIdentity"], "GeneratorIdentity" -> First[model["Context"]]["GeneratorIdentity"],
        "AssignmentID" -> model["ModularData"]["AssignmentID"], "IrrepID" -> space["IrrepID"], "Rep" -> variant["Rep"], "BasisID" -> variant["Identity"],
        "Dimension" -> variant["Dimension"], "Weight" -> space["Weight"], "Copy" -> copy, "SpaceDimension" -> space["Dimension"],
        "FormalBasisID" -> space["FormalBasisID"], "Components" -> Table[FormComponent[id, i], {i, variant["Dimension"]}]|>
];

(*
    Summary: Recompute a carried slot record in a model's namespace.
    Parameters: model — modular model data; slot — any association claiming to be a slot record.
    Options/defaults: None.
    Returns: The recomputed record, or Failure.
    Effects: Reads the dimension cache.
    Failures: ForeignSlot (another namespace or context, or an unknown irrep); InvalidSlot (a copy beyond the established
        dimension, a weight that is not an exact rational, an unknown space).
    Example: recomputeSlotRecord[m, s] === s for every slot produced by ModularFormCandidates on m's lineage.
    Remarks: Slot records are never trusted: the irrep, weight and copy index are rechecked against Stage 7 counts.
    See also: validateModularModelData; registerTermSlots.
*)
recomputeSlotRecord[model_Association, slot_] := Module[{space},
    If[!AssociationQ[slot] || !SubsetQ[Keys[slot], {"ID", "Namespace", "ContextDigest", "IrrepID", "Weight", "Copy"}],
        Return[makeFailure["InvalidSlot", "Malformed slot record."]]];
    If[slot["Namespace"] =!= model["ModularData"]["SlotNamespaceID"] || slot["ContextDigest"] =!= model["ContextDigest"] ||
            !StringQ[slot["IrrepID"]] || !MemberQ[First[model["Context"]]["CharacterData"]["IrrepIDs"], slot["IrrepID"]],
        Return[makeFailure["ForeignSlot", "The slot belongs to another model namespace or context; rebuild it in this model.", <|"SlotID" -> slot["ID"]|>]]];
    If[!modularWeightQ[slot["Weight"]] || !IntegerQ[slot["Copy"]] || slot["Copy"] < 1, Return[makeFailure["InvalidSlot", "Malformed slot weight or copy.", <|"SlotID" -> slot["ID"]|>]]];
    space = makeFormalSpace[model, slot["IrrepID"], slot["Weight"], True];
    If[!establishedSpaceQ[space] || slot["Copy"] > space["Dimension"],
        Return[makeFailure["InvalidSlot", "The slot's copy is not in an established form space.", <|"SlotID" -> slot["ID"], "Space" -> KeyTake[space, {"Status", "Dimension"}]|>]]];
    makeSlotRecord[model, space, slot["Copy"]]
];

(*
    Summary: The formal spaces required by a product of model factors for requested targets.
    Parameters: model — modular model data; factors — validated weighted data; targets — irrep IDs; dimensionCache.
    Options/defaults: None.
    Returns: <|"Combinations" -> {<|"ChannelIDs", "Irreps", "Weight", "FormWeight", "FormIrreps"|>...}, "Spaces" -> space
        records (each once, in first-need order)|>, or Failure.
    Effects: Character and dimension caches.
    Failures: Character failures.
    Example: T' triplet fields of label 1 with kW = 0 need the weight-2 spaces of the trivial irrep and the triplet.
    Remarks: For a combination of actual field weight w the forms have kY = kW - w; only form irreps that can reach a target
        with the combination's product are asked for (character pruning).
    See also: makeFormalSpace; ModularFormCandidates.
*)
requiredModularSpaces[model_Association, factors_List, targets_List, dimensionCache_] := Module[{characters = First[model["Context"]]["CharacterData"], combos, spaces = <||>},
    combos = Map[Function[combo, Module[{product = tensorMultiplicities[characters, combo["Irreps"]], irreps},
            If[FailureQ[product], Return[product, Module]];
            irreps = filterCandidateIrreps[characters, product, targets]; If[FailureQ[irreps], Return[irreps, Module]];
            Join[combo, <|"FormWeight" -> model["ModularData"]["SuperpotentialWeight"] - combo["Weight"], "FormIrreps" -> irreps|>]]],
        factorChannelCombinations[factors]];
    If[AnyTrue[combos, FailureQ], Return[FirstCase[combos, _Failure]]];
    Do[With[{key = {r, combo["FormWeight"]}}, If[!KeyExistsQ[spaces, key], spaces[key] = makeFormalSpace[model, r, combo["FormWeight"], dimensionCache]]],
        {combo, combos}, {r, combo["FormIrreps"]}];
    <|"Combinations" -> combos, "Spaces" -> Values[spaces]|>
];

(*
    Summary: Choose the slots of a candidate report.
    Parameters: data — candidate data; selection — All or a duplicate-free list of slot IDs of the report.
    Options/defaults: None.
    Returns: <|"Slots" -> chosen slot records, "Coverage" -> "Exhaustive" | "Selected", "Selection"|>, or Failure.
    Effects: Pure.
    Failures: IncompleteModularSpace (All with an unknown or failed relevant space); InvalidSelection (duplicates or slot IDs
        that the report does not contain).
    Example: selectModularCandidates[d, All] is exhaustive when every relevant count is known.
    See also: ModularTensorProductVectors; ModularContractions.
*)
selectModularCandidates[data_Association, selection_] := Module[{byID = AssociationThread[Lookup[data["Slots"], "ID", {}], data["Slots"]]},
    Which[
        selection === All && !data["Complete"], makeFailure["IncompleteModularSpace",
            "Some relevant form-space counts are unknown, so the exhaustive set cannot be built; select known slots with FormSelection.",
            <|"Unknown" -> Map[KeyTake[#, {"IrrepID", "Weight", "Status", "Dimension"}] &, data["Unknown"]], "KnownSlots" -> Keys[byID]|>],
        selection === All, <|"Slots" -> data["Slots"], "Coverage" -> "Exhaustive", "Selection" -> All|>,
        ListQ[selection] && DuplicateFreeQ[selection] && SubsetQ[Keys[byID], selection], <|"Slots" -> Lookup[byID, selection], "Coverage" -> "Selected", "Selection" -> selection|>,
        True, makeFailure["InvalidSelection", "FormSelection must be All or a duplicate-free list of slot IDs from this candidate report.",
            <|"Unknown" -> If[ListQ[selection], Complement[selection, Keys[byID]], selection]|>]]
];

(* Data access by property name: "Complete", "Slots", "Spaces", "Unknown", "Combinations", "TargetIrreps", ... *)
ModularFormCandidateData[data_Association][property_String] := Lookup[data, property, Missing["NotAvailable", property]];
Format[ModularFormCandidateData[data_Association], StandardForm] := Interpretation[Row[{"ModularFormCandidateData[", Length[Lookup[data, "Slots", {}]], " slots, ",
    If[TrueQ[Lookup[data, "Complete", False]], "complete", "incomplete"], "]"}], ModularFormCandidateData[data]];

(*
    Summary: The candidate data of factors (ModularFormCandidates' work, shared by the vector and contraction operations).
    Parameters: model — modular model data; factors — list of model factors; effective — validated options (TargetIrreps,
        DimensionCache).
    Options/defaults: As ModularFormCandidates.
    Returns: Candidate data association, or Failure.
    Effects: Character and dimension caches.
    Failures: As resolveModularFactors, resolveModularTargets, requiredModularSpaces; MissingRepresentations for a known
        space whose irrep has no matrices (reported by ID).
    Example: candidateData[m, {l, r}, opts]["Complete"] is True for the T' example.
    See also: ModularFormCandidates.
*)
candidateData[model_Association, factors_List, effective_Association] := Module[{resolved, targets, required, slots},
    resolved = resolveModularFactors[model, factors]; If[FailureQ[resolved], Return[resolved]];
    targets = resolveModularTargets[model, effective[TargetIrreps]]; If[FailureQ[targets], Return[targets]];
    required = requiredModularSpaces[model, resolved, targets, effective[DimensionCache]]; If[FailureQ[required], Return[required]];
    slots = Flatten[Map[Function[space, Table[makeSlotRecord[model, space, i], {i, Length[space["SlotIDs"]]}]], Select[required["Spaces"], establishedSpaceQ]]];
    If[AnyTrue[slots, FailureQ], Return[FirstCase[slots, _Failure]]];
    <|"SchemaVersion" -> 1, "ModelID" -> model["ID"], "Namespace" -> model["ModularData"]["SlotNamespaceID"], "ContextDigest" -> model["ContextDigest"],
        "SuperpotentialWeight" -> model["ModularData"]["SuperpotentialWeight"], "TargetIrreps" -> targets,
        "Factors" -> Map[<|"ChannelIDs" -> #["ChannelIDs"], "Weights" -> #["Weights"], "Irreps" -> Lookup[First[#["Vector"]]["Records"], "TargetID", {}]|> &, resolved],
        "Combinations" -> required["Combinations"], "Spaces" -> required["Spaces"], "Slots" -> slots,
        "Unknown" -> Select[required["Spaces"], !establishedSpaceQ[#] &], "Complete" -> AllTrue[required["Spaces"], establishedSpaceQ],
        "ResolvedFactors" -> resolved|>
];

Options[ModularFormCandidates] = {TargetIrreps -> Automatic, DimensionCache -> True, DimensionMethod -> Automatic};
$formalDimensionMethod = Automatic;

(*
    Summary: The formal modular-form copies a product of model fields needs, with their counts and slot records.
    Status: Alpha.
    Parameters: m — modular Model; factors — list of Fields, field IDs or WeightedRepVector values of the model's fields.
    Options/defaults: TargetIrreps -> Automatic (the model target; an ID, a duplicate-free list or All); DimensionCache -> True.
    Returns: ModularFormCandidateData with "Complete", "Slots", "Spaces", "Unknown", "Combinations", "TargetIrreps",
        "Factors", or Failure.
    Effects: Read-only apart from the character and dimension caches.
    Failures: InvalidModel; NotModularModel; factor and target failures; option failures.
    Example: ModularFormCandidates[m0, {left, right}]["Complete"] is True for the T' triplet example.
    Remarks: For each choice of factor channels of actual weight w, the forms need weight kY = kW - w and irreps reachable
        by characters. A known count d gives d formal copies; an unknown count or a missing spectrum makes the report
        incomplete instead of giving zero copies. No actual form is constructed.
    See also: ModularTensorProductVectors; ModularContractions.
*)
ModularFormCandidates[m_Model, factors_List, options : OptionsPattern[]] :=
    Block[{$formalDimensionMethod = Replace[Lookup[Association[FilterRules[Flatten[{options}], DimensionMethod]], DimensionMethod, Automatic], Except[Automatic | "Profile" | "TraceFormula"] -> Automatic]},
        modularFormCandidatesWork[m, factors, options]];
modularFormCandidatesWork[m_Model, factors_List, options : OptionsPattern[ModularFormCandidates]] := Module[{model = validateModelSchema[m], effective, data},
    If[FailureQ[model], Return[model]];
    If[!KeyExistsQ[model, "ModularData"], Return[makeFailure["NotModularModel", "The model has no modular weights; create it with CreateModularModel."]]];
    effective = resolveOperationOptions[ModularFormCandidates, "ModularFormCandidates", {options}]; If[FailureQ[effective], Return[effective]];
    effective = resolveIrrepOptions[model["Context"], effective]; If[FailureQ[effective], Return[effective]];
    data = candidateData[model, factors, effective];
    If[FailureQ[data], data, ModularFormCandidateData[KeyDrop[data, "ResolvedFactors"]]]
];
ModularFormCandidates[___] := makeFailure["InvalidInput", "ModularFormCandidates expects a modular Model, a list of factors and options."];

True
