(*
    :Title: Prepared model outputs
    :Context: VVMFTool`Private`
    :Summary: Immutable ModelOutput snapshots: named scalar and matrix outputs of a model (its expression, validated
        mass matrices, raw matrices or user-selected scalars) as typed expression trees, with explicit parameter
        substitutions, the ordered runtime parameter vector and the required field inputs.
    :Responsibilities: prepareOutputData, validateModelOutput, resolveOutputParameters, collectOutputDependencies,
        outputRegistry; ModelOutput, PrepareModelOutput.
    :Dependencies: Models.wl (validateModelSchema, ValidateModel, ModelExpression); MassMatrices.wl (ValidateMassMatrix,
        validateMassMatrixData); PythonIR.wl (encodeScalarTree, decodeScalarTree, validateScalarTree,
        scalarTreeDependencies, scalarTreePrecision).
    :See Also: VVMFArch/step6Plan.md (Prepared outputs and parameters).
*)

(*
    Summary: The tree registry of a model: its parameter IDs and field dimensions (and form-slot dimensions).
    Parameters: model — validated model data.
    Options/defaults: None.
    Returns: <|"Parameters" -> IDs (model order), "Fields" -> <|field ID -> dimension|>|>, plus "Slots" -> <|slot ID ->
        dimension|> for a modular model (Stage 9, D-S9-5).
    Effects: Pure.
    Failures: None.
    Example: outputRegistry[m]["Fields"] has one entry per model field.
    See also: encodeScalarTree.
*)
outputRegistry[model_Association] := Join[<|"Parameters" -> Lookup[model["Parameters"], "ID", {}],
    "Fields" -> AssociationThread[Lookup[model["Fields"], "ID", {}], Lookup[model["Fields"], "Dimension", {}]]|>,
    If[KeyExistsQ[model, "ModularData"], <|"Slots" -> Map[#["Dimension"] &, model["ModularData"]["Slots"]]|>, <||>]];

(*
    Summary: Validate explicit parameter substitutions.
    Parameters: model — validated model data; values — the ParameterValues option.
    Options/defaults: None.
    Returns: <|ID -> value|> (model order), or Failure.
    Effects: Pure.
    Failures: InvalidOption (not an association, unknown IDs, a value that is not a finite field-free numeric
        constant: it may not contain parameters, field components, symbols or infinities).
    Example: resolveOutputParameters[m, <|id -> 1|>] is <|id -> 1|>.
    Remarks: Exact constants (Pi, Sqrt[2], Exp[2 Pi I/3]) and approximate numbers are allowed; identity is by
        parameter ID only, so two parameters with the same label stay distinct.
    See also: prepareOutputData.
*)
resolveOutputParameters[model_Association, values_] := Module[{known = Lookup[model["Parameters"], "ID", {}], bad},
    If[!AssociationQ[values] || !AllTrue[Keys[values], StringQ],
        Return[makeFailure["InvalidOption", "ParameterValues must be an association from parameter IDs to numbers.", <|"Options" -> {ParameterValues}|>]]];
    If[!SubsetQ[known, Keys[values]],
        Return[makeFailure["InvalidOption", "ParameterValues names unknown parameter IDs.", <|"Options" -> {ParameterValues},
            "Unknown" -> Complement[Keys[values], known]|>]]];
    bad = Select[Keys[values], With[{v = values[#]}, !NumericQ[v] || !FreeQ[v, _Coupling | _FieldComponent | DirectedInfinity | Indeterminate | ComplexInfinity] ||
        !NumberQ[N[v]] || !FreeQ[N[v], DirectedInfinity | Indeterminate | Overflow[] | Underflow[]]] &];
    If[bad =!= {}, Return[makeFailure["InvalidOption", "ParameterValues must be finite numeric constants without parameters or fields.",
        <|"Options" -> {ParameterValues}, "ParameterIDs" -> bad|>]]];
    KeyTake[values, Select[known, KeyExistsQ[values, #] &]]
];

(*
    Summary: Normalize one requested output to its kind, shape, source value and metadata.
    Parameters: model — validated model data; m — the Model; name — output name; value — scalar, matrix or MassMatrix.
    Options/defaults: None.
    Returns: <|"Name", "Kind" -> "Scalar" | "Matrix", "Origin" -> "ModelExpression" | "MassMatrix" | "UserSelected",
        "Shape" -> {} | {r, c}, "Convention" -> None | <|"Kind", "Convention", "Rows", "Columns"|>, "SourceValue"|>, or Failure.
    Effects: Pure (ValidateMassMatrix recomputes a mass's checks).
    Failures: InvalidOutput (empty or ragged matrices, lists that are not matrices); mass failures
        (SourceModelMismatch, NonClosedFieldSelection, InvalidMassMatrix) and NotCovariant for a mass that fails covariance.
    Example: a MassMatrix extracted from ModelExpression[m] is a "MassMatrix" output with its convention.
    Remarks: A MassMatrix is marked model-derived only after ValidateMassMatrix certifies it against this model; its
        certificate status ("Covariant" or "Covariant (numerical)") is kept with the convention. An uncertified
        extraction can be exported through MatrixValues as a user-selected raw matrix.
    See also: prepareOutputData.
*)
normalizeOutputValue[model_Association, m_Model, name_String, value_] := Which[
    MatchQ[value, _MassMatrix], Module[{data = validateMassMatrixData[value], certificate},
        If[FailureQ[data], Return[data, Module]];
        (* the output records no status: the full check, not a session level (methodOptionsPlan.md 2D) *)
        certificate = ValidateMassMatrix[m, value, Verification -> Automatic];
        If[FailureQ[certificate], Return[Failure[First[certificate], Join[Last[certificate], <|"Output" -> name|>]], Module]];
        If[!TrueQ[certificate["Covariant"]], Return[makeFailure["NotCovariant", "The mass matrix does not transform covariantly in this model.",
            <|"Output" -> name, "Generator" -> certificate["Generator"]|>], Module]];
        (* Stage 9: a modular model's matrix must also have homogeneous entrywise weights. *)
        If[certificate["Status"] === "InconsistentWeight", Return[makeFailure["InconsistentWeight", "The mass matrix entries do not have the modular weights the model requires.",
            <|"Output" -> name, "ModularWeight" -> certificate["ModularWeight"]|>], Module]];
        <|"Name" -> name, "Kind" -> "Matrix", "Origin" -> "MassMatrix", "Shape" -> Dimensions[data["Matrix"]],
            "Convention" -> <|"Kind" -> data["Kind"], "Convention" -> data["Convention"], "Rows" -> data["Rows"], "Columns" -> data["Columns"],
                "Certificate" -> certificate["Status"]|>,
            Sequence @@ If[KeyExistsQ[certificate, "EntryWeights"], {"EntryWeights" -> certificate["EntryWeights"]}, {}],
            "SourceValue" -> data["Matrix"]|>],
    ListQ[value], If[MatrixQ[value] && Length[value] > 0 && Length[First[value]] > 0,
        <|"Name" -> name, "Kind" -> "Matrix", "Origin" -> "UserSelected", "Shape" -> Dimensions[value], "Convention" -> None, "SourceValue" -> value|>,
        makeFailure["InvalidOutput", "A matrix output must be a nonempty rectangular list of lists.", <|"Output" -> name|>]],
    True, <|"Name" -> name, "Kind" -> "Scalar", "Origin" -> "UserSelected", "Shape" -> {}, "Convention" -> None, "SourceValue" -> value|>
];

(*
    Summary: Build the ModelOutput data of a model.
    Parameters: m — Model; outputs — Automatic or an ordered association name -> scalar | matrix | MassMatrix;
        values — ParameterValues.
    Options/defaults: Automatic is <|"ModelExpression" -> ModelExpression[m]|>.
    Returns: ModelOutput data, or Failure.
    Effects: Pure apart from ValidateModel / ValidateMassMatrix recomputation.
    Failures: InvalidModel and the model's own validation failures; InvalidOutput (no outputs, empty or repeated
        names); InvalidOption (ParameterValues); tree failures with the output name and entry position
        (UndeclaredAtom, UnsupportedExpression, NonfiniteConstant — also after substitution, for example 1/0).
    Example: prepareOutputData[m, <|"ELMatrix" -> mass|>, <||>]["RuntimeParameters"] lists the couplings mass uses.
    Remarks: Substitution is by parameter ID (Coupling[id] -> value) on the source values; parameters that are fixed
        or unused by every selected output are absent from the runtime vector, in ModelParameters order. Required
        fields are the fields whose components remain, in model field order, each taken as a full vector.
    See also: PrepareModelOutput; validateModelOutput.
*)
prepareOutputData[m_Model, outputs_, values_] := Module[{model = validateModelSchema[m], validation, requested, normalized, substitutions, registry, rules,
        built, dependencies, runtime, fields, snapshot, substitutionTrees},
    If[FailureQ[model], Return[model]];
    (* the output records no status: the full check, not a session level (methodOptionsPlan.md 2D) *)
    validation = ValidateModel[m, Verification -> Automatic]; If[FailureQ[validation], Return[validation]];
    requested = If[outputs === Automatic, <|"ModelExpression" -> Total[Lookup[model["Terms"], "Value", {}]]|>, outputs];
    If[!AssociationQ[requested] || requested === <||> || !AllTrue[Keys[requested], StringQ[#] && StringLength[#] > 0 &],
        Return[makeFailure["InvalidOutput", "Outputs must be a nonempty association of nonempty names to scalars, matrices or mass matrices."]]];
    substitutions = resolveOutputParameters[model, values]; If[FailureQ[substitutions], Return[substitutions]];
    normalized = KeyValueMap[normalizeOutputValue[model, m, #1, #2] &, requested];
    If[AnyTrue[normalized, FailureQ], Return[FirstCase[normalized, _Failure]]];
    If[outputs === Automatic, normalized[[1, "Origin"]] = "ModelExpression"];
    registry = outputRegistry[model];
    rules = KeyValueMap[Coupling[#1] -> #2 &, substitutions];
    (* A substitution can make a coefficient infinite (1/c at c = 0): the tree encoder reports it, so the evaluation
       messages of that expected failure are silenced. *)
    built = Map[Function[output, Module[{value = Quiet[output["SourceValue"] /. rules], trees},
            trees = If[output["Kind"] === "Scalar", encodeScalarTree[value, registry], Map[encodeScalarTree[#, registry] &, value, {2}]];
            If[!FreeQ[trees, _Failure], Return[With[{f = FirstCase[{trees}, _Failure, Null, Infinity]},
                Failure[First[f], Join[Last[f], <|"Output" -> output["Name"], "Entry" -> If[output["Kind"] === "Scalar", {},
                    First[FirstPosition[trees, _Failure, {}, {2}]]]|>]]], Module]];
            Join[KeyDrop[output, "SourceValue"], <|"SourceValue" -> output["SourceValue"], "Value" -> value, "Trees" -> trees|>,
                outputArithmetic[If[output["Kind"] === "Scalar", {trees}, Flatten[trees]]]]]], normalized];
    If[AnyTrue[built, FailureQ], Return[FirstCase[built, _Failure]]];
    dependencies = collectOutputDependencies[built];
    runtime = Select[Lookup[model["Parameters"], "ID", {}], MemberQ[dependencies["Parameters"], #] &];
    fields = Select[Lookup[model["Fields"], "ID", {}], KeyExistsQ[dependencies["Fields"], #] &];
    snapshot = First[model["Context"]];
    substitutionTrees = Map[encodeScalarTree[#, <|"Parameters" -> {}, "Fields" -> <||>|>] &, substitutions];
    If[AnyTrue[substitutionTrees, FailureQ], Return[With[{f = FirstCase[Values[substitutionTrees], _Failure]},
        Failure[First[f], Join[Last[f], <|"Options" -> {ParameterValues}|>]]]]];
    <|"SchemaVersion" -> 1, "ID" -> "output-" <> CreateUUID[], "ModelID" -> model["ID"], "ModelName" -> model["Name"],
        "Context" -> model["Context"], "ContextDigest" -> model["ContextDigest"], "TargetIrrepID" -> model["TargetIrrepID"],
        "Group" -> <|"StateID" -> snapshot["GroupIdentity"], "GeneratorIdentity" -> snapshot["GeneratorIdentity"],
            "CharacterIdentity" -> snapshot["CharacterData"]["Identity"],
            "AssignmentIdentity" -> If[AssociationQ[snapshot["ModularAssignment"]], snapshot["ModularAssignment"]["Identity"], Missing["NotAssigned"]]|>,
        "Fields" -> Map[KeyTake[#, {"ID", "Name", "IrrepID", "Dimension", "BasisID"}] &, model["Fields"]],
        "Parameters" -> Map[KeyTake[#, {"ID", "Label", "Domain", "SourceAtom"}] &, model["Parameters"]],
        "SourceArithmetic" -> model["Arithmetic"], "SourcePrecision" -> model["Precision"], "SourceValidation" -> validation["Status"],
        "Substitutions" -> substitutions, "SubstitutionTrees" -> substitutionTrees,
        "Outputs" -> built, "RuntimeParameters" -> runtime, "RuntimeFields" -> fields,
        "FieldDimensions" -> KeyTake[registry["Fields"], fields],
        (* Stage 9: frozen slot and binding records of the used form slots (extendModularModelOutput). *)
        Sequence @@ If[KeyExistsQ[model, "ModularData"], {"Modular" -> extendModularModelOutput[model, dependencies, validation, normalized]}, {}]|>
];

(*
    Summary: The arithmetic status of an output from its actual trees.
    Parameters: trees — list of the output's trees.
    Options/defaults: None.
    Returns: <|"Arithmetic" -> "Exact" | "Numerical", "Precision" -> Infinity | MachinePrecision | digits|>.
    Effects: Pure.
    Failures: None.
    Example: an output with a 0.5 coefficient is Numerical at MachinePrecision even in an exact model.
    See also: scalarTreePrecision.
*)
outputArithmetic[trees_List] := With[{precisions = scalarTreePrecision /@ trees}, Which[
    AllTrue[precisions, # === Infinity &], <|"Arithmetic" -> "Exact", "Precision" -> Infinity|>,
    MemberQ[precisions, MachinePrecision], <|"Arithmetic" -> "Numerical", "Precision" -> MachinePrecision|>,
    True, <|"Arithmetic" -> "Numerical", "Precision" -> Min[DeleteCases[precisions, Infinity]]|>]];

(*
    Summary: The parameters and fields every selected output uses.
    Parameters: outputs — built output records (with Trees).
    Options/defaults: None.
    Returns: <|"Parameters" -> IDs, "Fields" -> <|field ID -> component indices|>, "Slots" -> <|form slot ID -> component
        indices|>|>.
    Effects: Pure.
    Failures: None.
    Example: a constant output contributes nothing.
    See also: scalarTreeDependencies; prepareOutputData.
*)
collectOutputDependencies[outputs_List] := Module[{all = Map[scalarTreeDependencies, Flatten[{Lookup[outputs, "Trees", {}]}]]},
    <|"Parameters" -> DeleteDuplicates[Flatten[Lookup[all, "Parameters", {}]]],
        "Fields" -> Merge[Lookup[all, "Fields", {}], Union @@ # &], "Slots" -> Merge[Lookup[all, "Slots", {}], Union @@ # &]|>
];

(*
    Summary: Validate a ModelOutput before use.
    Parameters: out — any expression.
    Options/defaults: None.
    Returns: The data, or InvalidModelOutput Failure.
    Effects: Pure.
    Failures: Missing fields, malformed outputs, trees outside the grammar or the registry, trees that do not decode to
        the stored values, shapes that disagree with the trees, runtime parameters or fields that are not exactly the
        dependencies (in model order), substitutions of unknown parameters; for a modular output (Stage 9) also a
        "Modular" record whose runtime slots, slot records and bindings disagree with the trees
        (validateModularOutputRecord).
    Example: a ModelOutput whose Value was edited by hand fails here.
    Remarks: Structural only; the source model's mathematics was validated when the output was prepared.
    See also: PrepareModelOutput; ToPython.
*)
validateModelOutput[ModelOutput[data_Association]] := Module[{invalid, registry, outputs, dependencies},
    invalid[reason_] := makeFailure["InvalidModelOutput", "The model output is malformed.", <|"Reason" -> reason|>];
    If[!SubsetQ[Keys[data], {"SchemaVersion", "ID", "ModelID", "ModelName", "Context", "ContextDigest", "TargetIrrepID", "Group", "Fields", "Parameters",
            "SourceArithmetic", "SourcePrecision", "SourceValidation", "Substitutions", "SubstitutionTrees", "Outputs", "RuntimeParameters",
            "RuntimeFields", "FieldDimensions"}] || data["SchemaVersion"] =!= 1 || !ListQ[data["Outputs"]] || data["Outputs"] === {},
        Return[invalid["Fields"]]];
    registry = Join[<|"Parameters" -> Lookup[data["Parameters"], "ID", {}], "Fields" -> AssociationThread[Lookup[data["Fields"], "ID", {}], Lookup[data["Fields"], "Dimension", {}]]|>,
        If[KeyExistsQ[data, "Modular"], <|"Slots" -> If[AssociationQ[data["Modular"]], Lookup[data["Modular"], "SlotDimensions", <||>], <||>]|>, <||>]];
    outputs = data["Outputs"];
    If[!DuplicateFreeQ[Lookup[outputs, "Name", {}]] || !AllTrue[outputs, Function[o, AssociationQ[o] &&
            SubsetQ[Keys[o], {"Name", "Kind", "Origin", "Shape", "Convention", "SourceValue", "Value", "Trees", "Arithmetic", "Precision"}] &&
            MemberQ[{"Scalar", "Matrix"}, o["Kind"]] && MemberQ[{"ModelExpression", "MassMatrix", "UserSelected"}, o["Origin"]] &&
            If[o["Kind"] === "Scalar", o["Shape"] === {} && TrueQ[validateScalarTree[o["Trees"], registry]] && decodeScalarTree[o["Trees"]] === o["Value"],
                MatrixQ[o["Trees"], AssociationQ] && Dimensions[o["Trees"], 2] === o["Shape"] &&
                    AllTrue[Flatten[o["Trees"]], TrueQ[validateScalarTree[#, registry]] &] && Map[decodeScalarTree, o["Trees"], {2}] === o["Value"]]]],
        Return[invalid["Outputs"]]];
    If[!SubsetQ[registry["Parameters"], Keys[data["Substitutions"]]] || Sort[Keys[data["SubstitutionTrees"]]] =!= Sort[Keys[data["Substitutions"]]],
        Return[invalid["Substitutions"]]];
    dependencies = collectOutputDependencies[outputs];
    If[data["RuntimeParameters"] =!= Select[registry["Parameters"], MemberQ[dependencies["Parameters"], #] &] ||
            data["RuntimeFields"] =!= Select[Keys[registry["Fields"]], KeyExistsQ[dependencies["Fields"], #] &] ||
            data["FieldDimensions"] =!= KeyTake[registry["Fields"], data["RuntimeFields"]],
        Return[invalid["Runtime inputs"]]];
    If[KeyExistsQ[data, "Modular"] && !TrueQ[validateModularOutputRecord[data["Modular"], dependencies]], Return[invalid["Modular"]]];
    data
];
validateModelOutput[___] := makeFailure["InvalidModelOutput", "Expected a ModelOutput."];

(* Data access by property name, e.g. out["RuntimeParameters"]. *)
ModelOutput[data_Association][property_String] := Lookup[data, property, Missing["NotAvailable", property]];

Format[ModelOutput[data_Association], StandardForm] := Interpretation[Row[{"ModelOutput[", Lookup[data, "ModelName", "?"], ": ",
    Short[Lookup[Lookup[data, "Outputs", {}], "Name", {}], 1], ", ", Length[Lookup[data, "RuntimeParameters", {}]], " parameters]"}], ModelOutput[data]];

Options[PrepareModelOutput] = {ParameterValues -> <||>};

(*
    Summary: Prepare named numerical-export outputs of a model.
    Parameters: m — Model; outputs — Automatic (the model expression) or an ordered association of output names to
        scalar expressions, rectangular matrices or MassMatrix values.
    Options/defaults: ParameterValues <||> — explicit substitutions parameter ID -> finite numeric constant.
    Returns: ModelOutput, or Failure.
    Effects: Recomputes the model's validation and each mass's certificate; the model is unchanged.
    Failures: As prepareOutputData; UnknownOption.
    Example: PrepareModelOutput[m, <|"ELMatrix" -> mass|>]["RuntimeParameters"] lists the couplings of the matrix.
    Remarks: A substitution such as fixing one coupling to 1 is an explicit parameter choice recorded in the output;
        nothing is removed automatically. Arbitrary scalar outputs are labelled user-selected: membership in the model
        is not a covariance certificate.
    See also: ToPython; ModelOutputView; MassMatrix.
*)
PrepareModelOutput[m_Model, outputs : Except[_Rule | _RuleDelayed] : Automatic, options : OptionsPattern[]] := Module[{effective, data},
    effective = resolveOperationOptions[PrepareModelOutput, "PrepareModelOutput", {options}];
    If[FailureQ[effective], Return[effective]];
    data = prepareOutputData[m, outputs, effective[ParameterValues]];
    If[FailureQ[data], data, ModelOutput[data]]
];
PrepareModelOutput[___] := makeFailure["InvalidInput", "PrepareModelOutput expects a Model, outputs and options."];

True
