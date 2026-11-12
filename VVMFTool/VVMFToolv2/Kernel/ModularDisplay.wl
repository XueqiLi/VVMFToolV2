(*
    :Title: Modular display documents
    :Context: VVMFTool`Private`
    :Summary: Immutable display snapshots of Stage 7 forms and Stage 8 slots: ModularFormView, ModularFormTable,
        QExpansionView, ModularDimensionView and FormSlotTable, with their document kinds; the slot labels and rows the
        Stage 6 model views use for modular models.
    :Responsibilities: slotLabelNode, slotAtoms, formSlotRows, formSlotTableParts, formSlotRowsQ, storedExpansionData,
        snapshotFormDisplay, formRowData, formTableData, dimensionDisplayData, slotDisplayData, snapshotModularDisplay and
        the kind handlers; ModularFormView, ModularFormTable, QExpansionView, ModularDimensionView, FormSlotTable.
    :Dependencies: ModularDisplayNodes.wl (nodes); ModelDisplay.wl (modelTable, modelHeader, irrepDisplayLabel, idText,
        idNode); DisplayData.wl (registerDisplayKind, makeDisplayDocument); ModularFormObjects.wl (snapshotForm);
        ModularOperations.wl (expansionBinding); ModularSeries.wl (validateQExpansion); ModularModels.wl (bindingStatus).
    :See Also: VVMFArch/step9Plan.md (Presentation contracts); VVMFArch/implementation/step9Status.md (D-S9-6 to D-S9-8).
*)

(* -------------------------------------------------------------------------
   Slots (shared with the Stage 6 model views)
   ------------------------------------------------------------------------- *)

$SlotLegend = "Y^(k)_r is a formal form slot of actual weight k in the irrep r (a Roman numeral is its copy in a space of dimension above one); bindings decide which actual form occupies a slot.";

(*
    Summary: The label node of a form slot.
    Parameters: slot — slot record (ID, Weight, IrrepID, Dimension, Copy, optional SpaceDimension); data — display group
        data of the context or None; effective — options (FormSlotLabels, IrrepLabels, DisplayTimeLimit).
    Options/defaults: None.
    Returns: The custom FormSlotLabels label, or a FormLabel node Y^(k) with the actual irrep label and the Roman copy
        index unless the stored space dimension is one.
    Effects: Read-only label data of the context.
    Failures: None.
    Example: the weight-2 triplet slot of T' is labelled Y^{(2)}_{3} (one copy).
    Remarks: The copy index only distinguishes slots of one space; it never identifies a constructor seed.
    See also: slotAtoms; formLabelNode.
*)
slotLabelNode[slot_Association, data_, effective_Association] := With[{custom = Lookup[effective, FormSlotLabels, <||>]},
    If[KeyExistsQ[custom, slot["ID"]], labelNode[custom[slot["ID"]]],
        formLabelNode[slot["Weight"], irrepDisplayLabel[data, slot["IrrepID"], slotDimension[slot], effective],
            If[IntegerQ[Lookup[slot, "SpaceDimension", None]] && slot["SpaceDimension"] <= 1, None, slot["Copy"]]]]];
slotDimension[slot_Association] := Lookup[slot, "Dimension", Length[Lookup[slot, "Components", {}]]];

(*
    Summary: The slot atoms of a document (labels and dimensions by slot ID).
    Parameters: slots — slot records; data — display group data or None; effective — options.
    Options/defaults: None.
    Returns: <|slot ID -> <|"Label" -> node, "Dimension" -> d|>|>.
    Effects: Read-only.
    Failures: None.
    Example: slotAtoms[Values[model["ModularData"]["Slots"]], data, opts] has one entry per slot.
    See also: modelAtoms; slotLabelNode.
*)
slotAtoms[slots_List, data_, effective_Association] := Association[Map[#["ID"] -> <|"Label" -> slotLabelNode[#, data, effective], "Dimension" -> slotDimension[#]|> &, slots]];

(*
    Summary: The display rows of a model's form slots.
    Parameters: model — modular model data (or its slots, bindings and term values: a prepared output's frozen records);
        atoms — modelAtoms with slots; data — display group data; effective — options.
    Options/defaults: None.
    Returns: List of <|"SlotID", "Label", "IrrepID", "IrrepLabel", "Weight", "Dimension", "Copy", "SpaceDimension", "BasisID",
        "Used", "Binding" -> None | <|"FormID", "Revision", "Kind", "ProofStatus"|>|>, in orderedSlots order.
    Effects: Pure: bound rows are read from the model's frozen binding records, never from a live form.
    Failures: None.
    Example: an unbound T' slot has Binding None and Used True when a term uses it.
    See also: FormSlotTable; formSlotTableParts.
*)
formSlotRows[model_Association, atoms_Association, data_, effective_Association] :=
    formSlotRows[model["ModularData"]["Slots"], model["ModularData"]["Bindings"], Lookup[model["Terms"], "Value", {}], atoms, data, effective,
        Keys[Lookup[model["ModularData"], "SuppliedSpaces", <||>]]];
formSlotRows[slots_Association, bindings_Association, terms_, atoms_Association, data_, effective_Association, supplied_List : {}] :=
    Map[Function[slot, <|"SlotID" -> slot["ID"], "Label" -> atoms["Slots"][slot["ID"]]["Label"], "IrrepID" -> slot["IrrepID"],
        "IrrepLabel" -> irrepDisplayLabel[data, slot["IrrepID"], slotDimension[slot], effective], "Weight" -> slot["Weight"], "Dimension" -> slotDimension[slot],
        "Copy" -> slot["Copy"], "SpaceDimension" -> Lookup[slot, "SpaceDimension", Missing["Unknown"]],
        "SpaceSupplied" -> MemberQ[supplied, slot["SpaceID"]], "BasisID" -> slot["BasisID"],
        "Used" -> !FreeQ[terms, FormComponent[slot["ID"], _]],
        "Binding" -> With[{b = Lookup[bindings, slot["ID"], None]}, If[AssociationQ[b],
            <|"FormID" -> b["FormID"], "Revision" -> b["Revision"], "Kind" -> b["Kind"], "ProofStatus" -> ToString[b["Validation"]["ProofStatus"]]|>, None]]|>],
        orderedSlots[Values[slots]]];

(*
    Summary: Slot records in display order: spaces in registration order, copies ascending within a space.
    Parameters: slots — slot records.
    Options/defaults: None.
    Returns: The same records, reordered.
    Effects: Pure.
    Failures: None.
    Example: the two copies of the weight-12 trivial space are listed as copy 1, then copy 2.
    Remarks: Slot IDs are hashes of a fresh namespace, so the stored order alone would vary between equal models.
    See also: formSlotRows.
*)
orderedSlots[slots_List] := Flatten[Map[SortBy[#, Lookup[#, "Copy", 0] &] &, Values[GroupBy[slots, Lookup[#, "SpaceID", None] &]]], 1];

(*
    Summary: Check form-slot rows, and their table parts.
    Parameters: rows — formSlotRows result.
    Options/defaults: None.
    Returns: formSlotRowsQ: Boolean. formSlotTableParts: modelTable result (a "none" row for a model without slots).
    Effects: Pure.
    Failures: None.
    Example: formSlotTableParts[{}] has one row reading "none".
    See also: FormSlotTable; modelViewParts.
*)
formSlotRowsQ[rows_] := ListQ[rows] && DuplicateFreeQ[Lookup[rows, "SlotID", {}]] && AllTrue[rows, Function[r, AssociationQ[r] && StringQ[Lookup[r, "SlotID", None]] &&
    labelNodeQ[Lookup[r, "Label", None]] && displayNodeQ[Lookup[r, "IrrepLabel", None]] && modularWeightQ[Lookup[r, "Weight", None]] && IntegerQ[Lookup[r, "Copy", None]] &&
    r["Copy"] >= 1 && BooleanQ[Lookup[r, "Used", None]] && (r["Binding"] === None || (AssociationQ[r["Binding"]] && StringQ[Lookup[r["Binding"], "FormID", None]] &&
        IntegerQ[Lookup[r["Binding"], "Revision", None]]))]];
formSlotTableParts[rows_List] := modelTable["form slots", {"Slot"}, {"Label", "Irrep", "Weight", "Copy", "Space dim.", "Basis", "Used", "Binding"},
    If[rows === {}, {{{textNode["none"]}, ConstantArray[textNode["\[LongDash]"], 8]}},
        Map[{{idNode[#["SlotID"]]}, {#["Label"], #["IrrepLabel"], textNode[weightText[#["Weight"]]], textNode[ToString[#["Copy"]]],
            textNode[If[IntegerQ[#["SpaceDimension"]], ToString[#["SpaceDimension"]] <> If[TrueQ[Lookup[#, "SpaceSupplied", False]], " (supplied)", ""], "unknown"]], idNode[#["BasisID"]], textNode[If[#["Used"], "yes", "no"]],
            textNode[If[#["Binding"] === None, "unbound", idText[#["Binding"]["FormID"]] <> " rev. " <> ToString[#["Binding"]["Revision"]] <> ", " <>
                #["Binding"]["Kind"] <> ", " <> #["Binding"]["ProofStatus"]]]}} &, rows]], "p"];

(* -------------------------------------------------------------------------
   Form snapshots
   ------------------------------------------------------------------------- *)

(*
    Summary: The stored q-expansion of a form record, checked against the record.
    Parameters: record — form record.
    Options/defaults: None.
    Returns: Validated QExpansionData association, Missing["NotComputed"], or StaleExpansion Failure.
    Effects: Pure: never computes an expansion.
    Failures: StaleExpansion: the binding is not one the record can carry (D-S9-8: "Fixed" for a definition without
        unknowns; otherwise "Raw" or the binding of the record's resolved rules), or its source names another basis,
        assignment or a later revision (a transported expansion records Missing["Transported"]).
    Example: storedExpansionData[ModularFormData[y]] is Missing["NotComputed"] before ModularFormQExp.
    See also: QExpansionView; expansionBinding.
*)
storedExpansionData[record_Association] := Module[{stored = record["QExpansion"], data, expected, source},
    If[!MatchQ[stored, _QExpansionData], Return[Missing["NotComputed"]]];
    data = validateQExpansion[stored]; If[FailureQ[data], Return[data]];
    expected = If[record["Definition"]["Parameters"] === {}, {"Fixed"},
        DeleteCases[{"Raw", expansionBinding[record, True]}, _Missing]];
    source = data["Source"];
    If[!MemberQ[expected, data["Binding"]] || data["Dimension"] =!= record["Dimension"] ||
            !(source === Missing["Transported"] || (AssociationQ[source] && Lookup[source, "BasisID", None] === record["BasisID"] &&
                Lookup[source, "AssignmentID", None] === record["AssignmentID"] && IntegerQ[Lookup[source, "Revision", None]] && source["Revision"] <= record["Revision"])),
        Return[makeFailure["StaleExpansion", "The stored q-expansion does not belong to this form record (binding, basis, assignment or revision).",
            <|"FormID" -> record["ID"], "Binding" -> data["Binding"], "Expected" -> expected|>]]];
    data
];

(*
    Summary: The definition text rows of a form record.
    Parameters: definition — definition data; weight — the form's weight.
    Options/defaults: None.
    Returns: List of {property, text}.
    Effects: Pure.
    Failures: None.
    Example: an MLDE definition gives its system, weight and exponents.
    Remarks: A recipe without a closed analytic expression is shown as its differential or derivative definition, never
        as an invented formula.
    See also: snapshotFormDisplay.
*)
definitionRows[definition_Association, weight_?modularWeightQ] := Join[
    {{"Definition", Switch[definition["Kind"],
        "Analytic", "closed expression in " <> definition["Coordinate"],
        "Jet", "finite q-expansion (no extension beyond its cutoff)",
        "MLDE", "modular linear differential equation (" <> ToString[definition["Recipe"]["System"]] <> ")",
        "Derived", "modular derivative D_" <> weightText[definition["Recipe"]["SourceWeight"]] <> " of a frozen " <> definition["Recipe"]["Source"]["Kind"] <> " source",
        _, definition["Kind"]] <> If[KeyExistsQ[definition, "Transform"], ", then a stored basis transform", ""]}},
    If[definition["Kind"] === "MLDE", {{"MLDE recipe", "system " <> ToString[definition["Recipe"]["System"]] <> ", weight " <> weightText[definition["Recipe"]["Weight"]] <>
        ", exponents " <> ToString[definition["Recipe"]["Exponents"], InputForm] <> ", seed " <> ToString[Lookup[definition["Recipe"], "Seed", "F"]]}}, {}],
    If[definition["Kind"] === "Derived", {{"Source weight", weightText[definition["Recipe"]["SourceWeight"]] <> " (this form: " <> weightText[weight] <> ")"}}, {}]];

(*
    Summary: The evidence node of a form record.
    Parameters: record — form record.
    Options/defaults: None.
    Returns: Evidence node with the validation status and the stored recipe, derivation and coefficient evidence.
    Effects: Pure.
    Failures: None.
    Example: a constructed form shows "recipe checks through order 6".
    See also: evidenceNode.
*)
formEvidenceNode[record_Association] := With[{v = record["Validation"], evidence = Lookup[record["Validation"], "RecipeEvidence", None]},
    evidenceNode[ToString[Lookup[v, "Status", "Unverified"]], Join[
        {{"method", ToString[record["Method"]]}, {"arithmetic", record["Arithmetic"]}},
        If[AssociationQ[evidence], {{"recipe", "checks through order " <> ToString[Lookup[evidence, "Order", "?"]] <>
            If[KeyExistsQ[evidence, "Derivation"], ", then " <> ToString[evidence["Derivation"]], ""]}}, {}],
        If[KeyExistsQ[v, "DerivedFrom"], {{"derived from", idText[v["DerivedFrom"]]}}, {}],
        If[AssociationQ[record["Coefficients"]], {{"coefficients", ToString[record["Coefficients"]["ProofStatus"]]}}, {}]]]];

(*
    Summary: The display cells of one form record (shared by ModularFormView and ModularFormTable).
    Parameters: record — form record (one snapshot); effective — options (FormLabels, IrrepLabels, ExpressionMode,
        MaxQTerms, FactorQSeries, DisplayTimeLimit).
    Options/defaults: None.
    Returns: <|"FormID", "Revision", "GroupKey", "GroupName", "AssignmentID", "Label", "IrrepID", "IrrepLabel", "Weight",
        "Dimension", "BasisID", "Method", "Arithmetic", "DefinitionRows", "Expression" -> ModularExpression or Text node,
        "ExpressionStatus", "QExpansion" -> QSeries or Text node, "QExpansionStatus", "Normalization", "Evidence",
        "Parameters" -> {<|"ID", "Label"|>...}|>, or Failure.
    Effects: Read-only: no q-expansion, coefficient solve, validation or GAP.
    Failures: StaleExpansion; UnverifiedContext.
    Example: formRowData[ModularFormData[y], opts]["Weight"] is y's actual weight.
    Remarks: ExpressionMode "Normalized" substitutes only stored resolved rules; unresolved normalization shows the raw
        expression with status "Unresolved"; "Raw" shows the parameter atoms with their labels and IDs.
    See also: snapshotFormDisplay; formTableData.
*)
formRowData[record_Association, effective_Association] := Module[{data, irrep, params, definition = record["Definition"], components, rules, status, qdata, label},
    data = displayGroupData[record["Context"]]; If[FailureQ[data], Return[data]];
    irrep = If[StringQ[record["IrrepID"]], irrepDisplayLabel[data, record["IrrepID"], record["Dimension"], effective],
        <|"Kind" -> "IrrepLabel", "Dimension" -> record["Dimension"], "Phases" -> None|>];
    label = If[KeyExistsQ[effective[FormLabels], record["ID"]], labelNode[effective[FormLabels][record["ID"]]], formLabelNode[record["Weight"], irrep, None]];
    params = parameterLabelNodes[definition["Parameters"], {}];
    rules = Lookup[Replace[record["Coefficients"], _Missing -> <||>], "Rules", Missing[]];
    components = Lookup[definition, "Components", Missing[]];
    status = Which[
        !ListQ[components], "FiniteJet",
        definition["Parameters"] === {}, "Fixed",
        effective[ExpressionMode] === "Raw", "Raw",
        ListQ[rules] && SubsetQ[Keys[rules], Lookup[definition["Parameters"], "ID", {}]], "Normalized",
        True, "Unresolved"];
    If[status === "Normalized", components = components /. Map[FormParameter[First[#]] -> Last[#] &, rules]];
    qdata = storedExpansionData[record]; If[FailureQ[qdata], Return[qdata]];
    <|"FormID" -> record["ID"], "Revision" -> record["Revision"], "GroupKey" -> {record["GroupIdentity"], record["AssignmentID"]},
        "GroupName" -> ToString[Lookup[data, "Name", "Group of order " <> ToString[data["Order"]]]], "AssignmentID" -> record["AssignmentID"], "Label" -> label,
        "IrrepID" -> If[StringQ[record["IrrepID"]], record["IrrepID"], "raw representation"], "IrrepLabel" -> irrep, "Weight" -> record["Weight"],
        "Dimension" -> record["Dimension"], "BasisID" -> record["BasisID"], "Method" -> ToString[record["Method"]], "Arithmetic" -> record["Arithmetic"],
        "DefinitionRows" -> definitionRows[definition, record["Weight"]],
        "Expression" -> If[ListQ[components], modularExpressionNode[components, params, definition["Coordinate"]],
            textNode["finite q-expansion to O(q^" <> ToString[validateQExpansion[definition["Jet"]]["Cutoff"], InputForm] <> ")"]],
        "ExpressionStatus" -> status,
        "QExpansion" -> If[MissingQ[qdata], textNode["not computed (ModularFormQExp stores it)"],
            qSeriesNode[qdata, params, effective[MaxQTerms], effective[FactorQSeries]]],
        "QExpansionStatus" -> If[MissingQ[qdata], "NotComputed", "Stored (" <> qdata["Binding"] <> ", cutoff " <> ToString[qdata["Cutoff"], InputForm] <> ")"],
        "Normalization" -> normalizationNode[record["Coefficients"], params], "Evidence" -> formEvidenceNode[record],
        "Parameters" -> KeyValueMap[<|"ID" -> #1, "Label" -> #2|> &, params]|>
];

(*
    Summary: The cells of a ModularForm document.
    Parameters: y — ModularForm; effective — options.
    Options/defaults: As ModularFormView.
    Returns: Association of header and cells, or Failure.
    Effects: One registry read (a consistent revision); read-only.
    Failures: UnknownModularForm; InvalidOption (FormLabels naming another form); formRowData failures.
    Example: snapshotFormDisplay[y, opts]["Revision"] is y's current revision.
    See also: ModularFormView.
*)
snapshotFormDisplay[y_ModularForm, effective_Association] := Module[{record = snapshotForm[y], header, row},
    If[FailureQ[record], Return[record]];
    If[!SubsetQ[{record["ID"]}, Keys[effective[FormLabels]]], Return[makeFailure["InvalidOption", "FormLabels names unknown form IDs.", <|"Options" -> {FormLabels}|>]]];
    If[!SubsetQ[First[record["Context"]]["CharacterData"]["IrrepIDs"], Keys[effective[IrrepLabels]]],
        Return[makeFailure["InvalidOption", "IrrepLabels names unknown irrep IDs.", <|"Options" -> {IrrepLabels}|>]]];
    header = modelHeader[record["Context"], "modular form"]; If[FailureQ[header], Return[header]];
    row = formRowData[record, effective]; If[FailureQ[row], Return[row]];
    Join[header, row]
];

(*
    Summary: The cells of a ModularForms document.
    Parameters: forms — list of ModularForm values (caller order); effective — options.
    Options/defaults: As ModularFormTable.
    Returns: Association of header and cells ("Rows" in caller order, "IncludeWeight", "Mixed"), or Failure.
    Effects: One registry read per form; read-only.
    Failures: InvalidInput (an element that is not a ModularForm, with its position); UnknownModularForm; InvalidOption;
        formRowData failures.
    Example: formTableData[{}, opts]["Rows"] is {}.
    Remarks: Rows over different groups or assignments keep their own metadata; the header names one group only when every
        row shares it.
    See also: ModularFormTable.
*)
formTableData[forms_List, effective_Association] := Module[{records, rows, keys, header},
    Do[If[Head[forms[[i]]] =!= ModularForm, Return[makeFailure["InvalidInput", "Every element must be a ModularForm.", <|"Position" -> i|>], Module]], {i, Length[forms]}];
    records = snapshotForm /@ forms;
    If[AnyTrue[records, FailureQ], Return[FirstCase[records, _Failure]]];
    If[!SubsetQ[Lookup[records, "ID", {}], Keys[effective[FormLabels]]], Return[makeFailure["InvalidOption", "FormLabels names unknown form IDs.", <|"Options" -> {FormLabels}|>]]];
    If[!SubsetQ[Union @@ Prepend[Map[First[#["Context"]]["CharacterData"]["IrrepIDs"] &, records], {}], Keys[effective[IrrepLabels]]],
        Return[makeFailure["InvalidOption", "IrrepLabels names unknown irrep IDs.", <|"Options" -> {IrrepLabels}|>]]];
    rows = Map[formRowData[#, effective] &, records];
    If[AnyTrue[rows, FailureQ], Return[FirstCase[rows, _Failure]]];
    keys = DeleteDuplicates[Lookup[rows, "GroupKey", {}]];
    header = If[Length[keys] === 1, modelHeader[First[records]["Context"], "modular forms"],
        modelHeader[Missing[], If[rows === {}, "no forms", "several groups or assignments"]]];
    If[FailureQ[header], Return[header]];
    Join[header, <|"Rows" -> rows, "IncludeWeight" -> effective[IncludeWeight], "Mixed" -> Length[keys] > 1|>]
];

(* -------------------------------------------------------------------------
   Document kinds
   ------------------------------------------------------------------------- *)

$FormLegend = "Ingredients eta, E2, E4, E6, Delta, j and K = 1728/j are functions of tau (q = exp(2 pi i tau)); {}_pF_q(a; b; K) is the hypergeometric function at K; F_i and G_i are components of an MLDE solution family; D_k = q d/dq - k E2/12.";
$SeriesLegend = "q-series show known nonzero terms in exponent order; a dots marker means known terms omitted by MaxQTerms; O(q^n) is the stored cutoff (a factored series writes it inside as O(q^(n - r))); no O term means an exact finite expansion.";

(*
    Summary: Plain-text summaries of Normalization and Evidence nodes (wrapping table cells).
    Parameters: node — Normalization or Evidence node.
    Options/defaults: None.
    Returns: String.
    Effects: Pure.
    Failures: None.
    Example: evidenceText[evidenceNode["Unverified", {{"method", "Manual"}}]] is "Unverified; method: Manual";
        shortHexText["Rules-0123456789abcdef"] is "Rules-01234567" followed by an ellipsis.
    See also: formViewParts; formTableParts.
*)
normalizationText[node_Association] := shortHexText[Switch[node["Status"], "NotNeeded", "none needed", "Resolved", "resolved", _, "unresolved"] <>
    " (" <> node["ProofStatus"] <> ")" <> If[StringQ[node["Anchor"]], "; anchor: " <> node["Anchor"], ""]];
evidenceText[node_Association] := shortHexText[node["Status"] <> StringJoin[Map["; " <> #[[1]] <> ": " <> #[[2]] &, node["Items"]]]];
(* Long hexadecimal identities (hashes, frame IDs) keep their first eight digits in table text; DisplayData keeps them whole. *)
shortHexText[s_String] := StringReplace[s, RegularExpression["([0-9a-f]{8})[0-9a-f]{8,}"] :> "$1" <> "\[Ellipsis]"];

(*
    Summary: The table parts of a ModularForm document.
    Parameters: data — document data.
    Options/defaults: None.
    Returns: List of modelTable results: the summary (wrapping text), the mathematics (expression, q-expansion and the
        resolved normalization values; width-aware, scaled only as a last resort) and, when the definition has unknowns,
        the parameter table.
    Effects: Pure.
    Failures: None.
    Example: the summary lists weight, representation, definition, normalization and evidence.
    See also: ModularFormView.
*)
formViewParts[data_Association] := Join[{
    modelTable["form", {"Property"}, {"Value"}, Join[{
        {{textNode["ID"]}, {textNode[idText[data["FormID"]] <> " (revision " <> ToString[data["Revision"]] <> ")"]}},
        {{textNode["Basis"]}, {idNode[data["BasisID"]]}},
        {{textNode["Assignment"]}, {idNode[data["AssignmentID"]]}},
        {{textNode["Weight"]}, {textNode["k = " <> weightText[data["Weight"]]]}},
        {{textNode["Dimension"]}, {textNode[ToString[data["Dimension"]]]}}},
        Map[{{textNode[#[[1]]]}, {textNode[#[[2]]]}} &, data["DefinitionRows"]], {
        {{textNode["Expression status"]}, {textNode[data["ExpressionStatus"]]}},
        {{textNode["q-expansion status"]}, {textNode[shortHexText[data["QExpansionStatus"]]]}},
        {{textNode["Normalization"]}, {textNode[normalizationText[data["Normalization"]]]}},
        {{textNode["Evidence"]}, {textNode[evidenceText[data["Evidence"]]]}}}], "p"],
    modelTable["mathematics", {"Property"}, {"Value"}, Join[{
        {{textNode["Form"]}, {data["Label"]}},
        {{textNode["Representation"]}, {data["IrrepLabel"]}},
        {{textNode["Expression"]}, {data["Expression"]}},
        {{textNode["q-expansion"]}, {data["QExpansion"]}}},
        Map[{{#["Label"]}, {<|"Kind" -> "ModularExpression", "Components" -> {#["Value"]}, "Parameters" -> <||>, "Coordinate" -> "q"|>}} &,
            data["Normalization"]["Rules"]]], "c"]},
    If[data["Parameters"] === {}, {}, {modelTable["normalization parameters", {"ID"}, {"Label"},
        Map[{{textNode[#["ID"]]}, {#["Label"]}} &, data["Parameters"]], "p"]}]];

(*
    Summary: Check one form row of a document.
    Parameters: row — formRowData result.
    Options/defaults: None.
    Returns: Boolean.
    Effects: Pure.
    Failures: None.
    Example: formRowQ[formRowData[record, opts]] is True.
    See also: registerDisplayKind.
*)
formRowQ[row_] := AssociationQ[row] && StringQ[Lookup[row, "FormID", None]] && IntegerQ[Lookup[row, "Revision", None]] && modularWeightQ[Lookup[row, "Weight", None]] &&
    AllTrue[Lookup[row, {"Label", "IrrepLabel", "Expression", "QExpansion", "Normalization", "Evidence"}, None], displayNodeQ] &&
    MemberQ[{"Fixed", "Raw", "Normalized", "Unresolved", "FiniteJet"}, Lookup[row, "ExpressionStatus", None]] && ListQ[Lookup[row, "Parameters", None]] &&
    AllTrue[row["Parameters"], displayNodeQ[Lookup[#, "Label", None]] &];

registerDisplayKind["ModularForm", <|"Fields" -> {"FormID", "Revision", "Label", "IrrepID", "IrrepLabel", "Weight", "Dimension", "BasisID", "AssignmentID",
        "DefinitionRows", "Expression", "ExpressionStatus", "QExpansion", "QExpansionStatus", "Normalization", "Evidence", "Parameters"},
    "Check" -> formRowQ,
    "Caption" -> Function[data, "Modular form of weight " <> weightText[data["Weight"]] <> " over " <> ToString[data["Group"]["Name"]]],
    "TeX" -> Function[{data, settings}, <|"Tables" -> Map[#["TeX"] &, formViewParts[data]], "Legend" -> {$FormLegend, $SeriesLegend,
        "A display certifies nothing: the evidence is as stored (ValidateModularForm checks).", $ShortIDLegend}|>],
    "Notebook" -> Function[{data, settings}, <|"Sections" -> Map[#["Notebook"] &, formViewParts[data]], "Legend" -> {$FormLegend, $SeriesLegend,
        "A display certifies nothing: the evidence is as stored."}|>]|>];

(*
    Summary: The table parts of a ModularForms document: one table per run of consecutive rows over the same group and
        assignment (caller order is kept).
    Parameters: data — document data.
    Options/defaults: None.
    Returns: List of modelTable results (one "none" row for an empty table).
    Effects: Pure.
    Failures: None.
    Example: two T' forms give one table with two rows.
    See also: ModularFormTable.
*)
formTableParts[data_Association] := Module[{columns, cells, runs, title},
    columns = Join[{"Form", "Irrep"}, If[TrueQ[data["IncludeWeight"]], {"k"}, {}], {"Expression", "q-expansion"}];
    cells[row_] := {{idNode[row["FormID"]]}, Join[{row["Label"], row["IrrepLabel"]}, If[TrueQ[data["IncludeWeight"]], {textNode[weightText[row["Weight"]]]}, {}],
        {row["Expression"], row["QExpansion"]}]};
    If[data["Rows"] === {}, Return[{modelTable["forms", {"ID"}, columns, {{{textNode["none"]}, ConstantArray[textNode["\[LongDash]"], Length[columns]]}}, "p"]}]];
    runs = Split[data["Rows"], #1["GroupKey"] === #2["GroupKey"] &];
    title[run_] := If[TrueQ[data["Mixed"]], " over " <> First[run]["GroupName"] <> " (assignment " <> idText[First[run]["AssignmentID"]] <> ")", ""];
    (* Per run: the mathematics (width-aware panels) and the status text (wrapping). *)
    Flatten[Map[{modelTable["forms" <> title[#], {"ID"}, columns, Map[cells, #], "c"],
        modelTable["status" <> title[#], {"ID"}, {"Normalization", "Evidence"},
            Map[Function[row, {{idNode[row["FormID"]]}, {textNode[normalizationText[row["Normalization"]]], textNode[evidenceText[row["Evidence"]]]}}], #], "p"]} &, runs]]
];
registerDisplayKind["ModularForms", <|"Fields" -> {"Rows", "IncludeWeight", "Mixed"},
    "Check" -> Function[data, ListQ[data["Rows"]] && AllTrue[data["Rows"], formRowQ] && BooleanQ[data["IncludeWeight"]] && BooleanQ[data["Mixed"]] &&
        (* The header names one group only when every row shares it. *)
        (TrueQ[data["Mixed"]] === (Length[DeleteDuplicates[Lookup[data["Rows"], "GroupKey", {}]]] > 1))],
    "Caption" -> Function[data, Which[data["Rows"] === {}, "Modular forms (none)", TrueQ[data["Mixed"]], "Modular forms over several groups or assignments (see the section titles)",
        True, "Modular forms over " <> ToString[data["Group"]["Name"]]]],
    "TeX" -> Function[{data, settings}, <|"Tables" -> Map[#["TeX"] &, formTableParts[data]], "Legend" -> {$FormLegend, $SeriesLegend, $ShortIDLegend}|>],
    "Notebook" -> Function[{data, settings}, <|"Sections" -> Map[#["Notebook"] &, formTableParts[data]], "Legend" -> {$FormLegend, $SeriesLegend}|>]|>];

(*
    Summary: The table parts of a QExpansion document.
    Parameters: data — document data.
    Options/defaults: None.
    Returns: List with one modelTable result.
    Effects: Pure.
    Failures: None.
    Example: a missing expansion shows "not computed".
    See also: QExpansionView.
*)
qExpansionParts[data_Association] := {modelTable["q-expansion", {"Property"}, {"Value"}, {
    {{textNode["Form"]}, {textNode[If[StringQ[data["FormID"]], idText[data["FormID"]] <> " (revision " <> ToString[data["Revision"]] <> ")", "supplied data"]]}},
    {{textNode["Status"]}, {textNode[data["Status"]]}},
    {{textNode["Binding"]}, {textNode[ToString[data["Binding"]]]}},
    {{textNode["Cutoff"]}, {textNode[ToString[data["Cutoff"], InputForm]]}},
    {{textNode["Arithmetic"]}, {textNode[ToString[data["Arithmetic"]] <> If[data["Arithmetic"] === "Numerical", " (precision " <> ToString[data["Precision"]] <> ")", ""]]}},
    {{textNode["Series"]}, {data["Series"]}}}, "p"]};
registerDisplayKind["QExpansion", <|"Fields" -> {"FormID", "Revision", "Status", "Binding", "Cutoff", "Arithmetic", "Precision", "Series"},
    "Check" -> Function[data, MemberQ[{"Stored", "NotComputed", "Supplied"}, data["Status"]] && displayNodeQ[data["Series"]] &&
        (data["Status"] === "NotComputed" || Lookup[data["Series"], "Kind", None] === "QSeries")],
    "Caption" -> Function[data, If[StringQ[data["FormID"]], "q-expansion of the modular form " <> idText[data["FormID"]], "q-expansion data"]],
    "TeX" -> Function[{data, settings}, <|"Tables" -> Map[#["TeX"] &, qExpansionParts[data]], "Legend" -> {$SeriesLegend, $ShortIDLegend}|>],
    "Notebook" -> Function[{data, settings}, <|"Sections" -> Map[#["Notebook"] &, qExpansionParts[data]], "Legend" -> {$SeriesLegend}|>]|>];

(*
    Summary: The cells of a ModularDimensions document.
    Parameters: table — ModularDimensionTable result <|irrep ID -> <|k -> dimension | Missing | Failure|>|>; effective —
        options (IrrepLabels).
    Options/defaults: As ModularDimensionView.
    Returns: Association of header and cells ("IrrepIDs", "Weights" in first-appearance order, "Rows"), or Failure.
    Effects: Pure: no dimension is computed.
    Failures: InvalidInput (a malformed table: non-string irrep IDs, weights that are not exact rationals, negative or non-integer
        dimensions); InvalidOption (IrrepLabels naming irreps outside the table).
    Example: dimensionDisplayData[<|"irrep-1" -> <|0 -> 1, 2 -> 0|>|>, opts]["Weights"] is {0, 2}.
    Remarks: Zero, unknown (Missing, with its reason), failed (Failure, with its tag) and not requested cells stay distinct.
    See also: ModularDimensionView.
*)
dimensionDisplayData[table_Association, effective_Association] := Module[{weights, cell},
    If[!AllTrue[Keys[table], StringQ] || !AllTrue[Values[table], AssociationQ[#] && AllTrue[Keys[#], modularWeightQ] &&
            AllTrue[Values[#], (IntegerQ[#] && # >= 0) || MissingQ[#] || FailureQ[#] &] &],
        Return[makeFailure["InvalidInput", "ModularDimensionView expects a ModularDimensionTable result: irrep ID -> <|weight -> dimension, Missing or Failure|>."]]];
    If[!SubsetQ[Keys[table], Keys[effective[IrrepLabels]]], Return[makeFailure["InvalidOption", "IrrepLabels names irreps that are not in the table.", <|"Options" -> {IrrepLabels}|>]]];
    weights = DeleteDuplicates[Flatten[Keys /@ Values[table]]];
    cell[row_, k_] := With[{v = Lookup[row, k, Missing["NotRequested"]]}, Which[
        IntegerQ[v], <|"Weight" -> k, "Status" -> "Known", "Value" -> v, "Text" -> ToString[v]|>,
        v === Missing["NotRequested"], <|"Weight" -> k, "Status" -> "NotRequested", "Value" -> v, "Text" -> "\[LongDash]"|>,
        MissingQ[v], <|"Weight" -> k, "Status" -> "Unknown", "Value" -> v, "Text" -> "unknown" <> If[Length[v] > 0, " (" <> ToString[First[v]] <> ")", ""]|>,
        True, <|"Weight" -> k, "Status" -> "Failed", "Value" -> v, "Text" -> "failed (" <> ToString[First[v]] <> ")"|>]];
    Join[modelHeader[Missing[], "modular dimension table"], <|"IrrepIDs" -> Keys[table], "Weights" -> weights,
        "Rows" -> KeyValueMap[<|"IrrepID" -> #1, "Label" -> Lookup[Map[labelNode, effective[IrrepLabels]], #1, textNode[#1]], "Cells" -> Map[Function[k, cell[#2, k]], weights]|> &, table]|>]
];
(*
    Summary: The ModularDimensions document of ModularDimensionTable (uxUpdatePlan.md 2.5, U9).
    Parameters: c — Group or RepresentationContext; records — irrep ID -> <|k -> dimension record or Failure|>;
        effective — options (IrrepForm, IrrepLabels).
    Options/defaults: None.
    Returns: DisplayDocument["ModularDimensions", data] whose rows carry the irrep index, user label, automatic label and
        dimension, and whose cells show the count, "-" for 0 and "/" when the formula could not be evaluated; at weight 1
        the formula's value with a note (user decision); "Table" is <|irrep (IrrepForm) -> <|k -> dimension or Missing|>|>.
    Effects: Reads the group's presentation; no dimension is computed here.
    Failures: Context failures.
    Example: DisplayData[ModularDimensionTable[g]]["Table"][7][2] is 1 for the T' triplet.
    See also: ModularDimensionTable; dimensionViewParts.
*)
dimensionTableDocument[c_, records_Association, effective_Association] := Module[{data, ids = Keys[records], weights, labelData, names, rows, table, notes = {}, reasons = {}},
    data = displayGroupData[c]; If[FailureQ[data], Return[data]];
    weights = Keys[First[Values[records], <||>]];
    labelData = AssociationMap[irrepLabelData[data, #, Automatic, 5] &, ids];
    names = irrepPresentation[data, ids, labelData, Lookup[effective, IrrepLabels, <||>]];
    rows = Map[Function[id, <|"IrrepID" -> id, "Label" -> names[id]["Display"], "Index" -> names[id]["Index"], "User" -> names[id]["User"],
        "Auto" -> names[id]["Auto"], "Dimension" -> data["CharacterData"]["Degrees"][[First[FirstPosition[data["CharacterData"]["IrrepIDs"], id]]]],
        "Cells" -> Map[Function[k, With[{r = records[id][k]}, Which[
            FailureQ[r], AppendTo[reasons, Lookup[Last[r], "MessageTemplate", First[r]]];
                <|"Weight" -> k, "Status" -> "Failed", "Value" -> r, "Text" -> "/"|>,
            KeyExistsQ[r, "FormulaValue"], If[KeyExistsQ[r, "Diagnostics"], AppendTo[notes, r["Diagnostics"]]];
                <|"Weight" -> k, "Status" -> "Formula", "Value" -> r["FormulaValue"], "Text" -> If[r["FormulaValue"] === 0, "-", ToString[r["FormulaValue"], InputForm]]|>,
            IntegerQ[r["Dimension"]], If[KeyExistsQ[r, "Diagnostics"], AppendTo[notes, "irrep " <> ToString[names[id]["Index"]] <> ", weight " <> weightText[k] <> ": " <> r["Diagnostics"]]];
                <|"Weight" -> k, "Status" -> "Known", "Value" -> r["Dimension"], "Text" -> If[r["Dimension"] === 0, "-", ToString[r["Dimension"]]]|>,
            True, AppendTo[reasons, Replace[r["Dimension"], {Missing[_, reason_String] :> reason, _ -> "not established"}]];
                <|"Weight" -> k, "Status" -> "Unknown", "Value" -> r["Dimension"], "Text" -> "/"|>]]], weights]|>], ids];
    table = presentIrrepKeys[c, Map[Function[row, Map[If[FailureQ[#], #, #["Dimension"]] &, row]], records], Lookup[effective, IrrepForm, "Index"]];
    If[FailureQ[table], Return[table]];
    makeDisplayDocument["ModularDimensions", Join[modelHeader[Missing[], "modular dimension table"], displayHeader[data],
        <|"IrrepIDs" -> ids, "Weights" -> weights, "Rows" -> rows, "Table" -> table,
        "Columns" -> <|"Auto" -> AnyTrue[rows, #["Auto"] =!= None &], "User" -> AnyTrue[rows, #["User"] =!= None &]|>,
        "Notes" -> Join[
            (* only when a weight-1 cell actually shows a formula value (not, e.g., the parity rule's zero) *)
            If[AnyTrue[rows, AnyTrue[#["Cells"], Function[cell, cell["Status"] === "Formula"]] &], {"Weight-1 values come from the dimension formula and may be incorrect."}, {}],
            ("/: " <> # &) /@ DeleteDuplicates[reasons], DeleteDuplicates[notes]]|>],
        KeyDrop[effective, {Method, DimensionCache, Weights, IrrepForm, IrrepLabels}]]];

dimensionViewParts[data_Association] := If[KeyExistsQ[data, "Columns"],
    (* rows: index, [user label], [automatic label], dimension, then the weights (user decision, U9) *)
    {modelTable["dimensions", Join[{"Index"}, If[data["Columns"]["User"], {"Name"}, {}], If[data["Columns"]["Auto"], {"Label"}, {}], {"Dim."}],
        Map[weightText, data["Weights"]],
        If[data["Rows"] === {}, {{{textNode["none"]}, {}}}, Map[{Join[{textNode[ToString[#["Index"]]]}, If[data["Columns"]["User"], {Replace[#["User"], None -> textNode[""]]}, {}],
            If[data["Columns"]["Auto"], {Replace[#["Auto"], None -> textNode[""]]}, {}], {textNode[ToString[#["Dimension"]]]}],
            Map[Function[c, textNode[c["Text"]]], #["Cells"]]} &, data["Rows"]]], "c"]},
    {modelTable["dimensions", {"Irrep"}, Map["k = " <> weightText[#] &, data["Weights"]],
        If[data["Rows"] === {}, {{{textNode["none"]}, {}}}, Map[{{#["Label"]}, Map[Function[c, textNode[c["Text"]]], #["Cells"]]} &, data["Rows"]]], "c"]}];
dimensionLegend[data_Association] := If[KeyExistsQ[data, "Columns"],
    Join[{"-: no forms of this weight" <> If[AnyTrue[data["Rows"], AnyTrue[#["Cells"], Function[c, c["Text"] === "/"]] &],
        "; /: the dimension could not be determined (reasons below; ModularDimensionData gives the details).", "."]}, data["Notes"]],
    {"0: known zero; unknown: not established; failed: the computation failed; a dash: not requested."}];
registerDisplayKind["ModularDimensions", <|"Fields" -> {"IrrepIDs", "Weights", "Rows"},
    "Check" -> Function[data, ListQ[data["Rows"]] && Lookup[data["Rows"], "IrrepID", {}] === data["IrrepIDs"] && DuplicateFreeQ[data["IrrepIDs"]] &&
        AllTrue[data["Rows"], displayNodeQ[#["Label"]] && Lookup[#["Cells"], "Weight", {}] === data["Weights"] &&
            AllTrue[#["Cells"], Function[c, MemberQ[{"Known", "Unknown", "Failed", "NotRequested", "Formula"}, c["Status"]] && StringQ[c["Text"]]]] &]],
    "Caption" -> Function[data, "Dimensions of vector-valued modular form spaces by irrep and weight"],
    "TeX" -> Function[{data, settings}, <|"Tables" -> Map[#["TeX"] &, dimensionViewParts[data]], "Legend" -> dimensionLegend[data]|>],
    "Notebook" -> Function[{data, settings}, <|"Sections" -> Map[#["Notebook"] &, dimensionViewParts[data]], "Legend" -> dimensionLegend[data]|>]|>];

(*
    Summary: The cells of a FormSlots document.
    Parameters: m — modular Model; effective — options (FormSlotLabels, IrrepLabels, DisplayTimeLimit).
    Options/defaults: As FormSlotTable.
    Returns: Association of header and cells ("ModelID", "ModelName", "Namespace", "BindingStatus", "Slots"), or Failure.
    Effects: Read-only: bindings are read from the model's frozen records; no dimension is recomputed.
    Failures: InvalidModel; NotModularModel; InvalidOption; UnverifiedContext.
    Example: slotDisplayData[m, opts]["Slots"] has one row per registered slot.
    See also: FormSlotTable; formSlotRows.
*)
slotDisplayData[m_Model, effective_Association] := Module[{model = validateModelSchema[m], slots, data, header, check, atoms},
    If[FailureQ[model], Return[model]];
    If[!KeyExistsQ[model, "ModularData"], Return[makeFailure["NotModularModel", "FormSlotTable needs a modular model (CreateModularModel)."]]];
    slots = Values[model["ModularData"]["Slots"]];
    check = checkModelLabels[<|FieldLabels -> <||>, CouplingLabels -> <||>, IrrepLabels -> effective[IrrepLabels], FormSlotLabels -> effective[FormSlotLabels]|>,
        {}, {}, First[model["Context"]]["CharacterData"]["IrrepIDs"], Lookup[slots, "ID", {}]];
    If[FailureQ[check], Return[check]];
    header = modelHeader[model["Context"], "model"]; If[FailureQ[header], Return[header]];
    data = displayGroupData[model["Context"]];
    atoms = <|"Slots" -> slotAtoms[slots, data, effective]|>;
    Join[header, <|"ModelID" -> model["ID"], "ModelName" -> model["Name"], "Namespace" -> model["ModularData"]["SlotNamespaceID"],
        "BindingStatus" -> bindingStatus[model], "Slots" -> formSlotRows[model, atoms, data, effective]|>]
];
registerDisplayKind["FormSlots", <|"Fields" -> {"ModelID", "ModelName", "Namespace", "BindingStatus", "Slots"},
    "Check" -> Function[data, formSlotRowsQ[data["Slots"]] && StringQ[data["BindingStatus"]]],
    "Caption" -> Function[data, "Form slots of the model " <> data["ModelName"] <> " over " <> ToString[data["Group"]["Name"]] <> " (" <> data["BindingStatus"] <> ")"],
    "TeX" -> Function[{data, settings}, <|"Tables" -> {formSlotTableParts[data["Slots"]]["TeX"]}, "Legend" -> {$SlotLegend,
        "Used: a model term contains the slot; Binding: the frozen form, its revision, definition kind and proof status at binding time.", $ShortIDLegend}|>],
    "Notebook" -> Function[{data, settings}, <|"Sections" -> {formSlotTableParts[data["Slots"]]["Notebook"]}, "Legend" -> {$SlotLegend}|>]|>];

(* -------------------------------------------------------------------------
   View producers
   ------------------------------------------------------------------------- *)

(*
    Summary: The display document of a Stage 9 modular view.
    Parameters: x — value; kind — document kind; operation — option operation name; symbol — the producer (Options);
        options — option rules.
    Options/defaults: As the producer.
    Returns: DisplayDocument, or Failure.
    Effects: Read-only: no q-expansion, coefficient solve, validation, binding, dimension computation or GAP.
    Failures: Option failures; the producer's cell failures; InvalidDisplayDocument.
    Example: snapshotModularDisplay[y, "ModularForm", "ModularFormView", ModularFormView, {}] is ModularFormView[y].
    See also: ModularFormView; ModularFormTable; QExpansionView; ModularDimensionView; FormSlotTable.
*)
snapshotModularDisplay[x_, kind_String, operation_String, symbol_Symbol, options_List] := Module[{effective, cells},
    effective = resolveOperationOptions[symbol, operation, options]; If[FailureQ[effective], Return[effective]];
    effective = displayIrrepOptions[x, effective]; If[FailureQ[effective], Return[effective]];
    cells = Switch[kind,
        "ModularForm", snapshotFormDisplay[x, effective],
        "ModularForms", formTableData[x, effective],
        "QExpansion", qExpansionCells[x, effective],
        "ModularDimensions", dimensionDisplayData[x, effective],
        "FormSlots", slotDisplayData[x, effective]];
    If[FailureQ[cells], cells, makeDisplayDocument[kind, cells, effective]]
];

(*
    Summary: The cells of a QExpansion document.
    Parameters: x — ModularForm or QExpansionData; effective — options (MaxQTerms, FactorQSeries).
    Options/defaults: As QExpansionView.
    Returns: Association of header and cells, or Failure.
    Effects: Read-only: a missing expansion is reported, never computed.
    Failures: UnknownModularForm; StaleExpansion; InvalidSeries (malformed supplied data).
    Example: qExpansionCells[y, opts]["Status"] is "NotComputed" before ModularFormQExp[y, n].
    See also: QExpansionView; storedExpansionData.
*)
qExpansionCells[y_ModularForm, effective_Association] := Module[{record = snapshotForm[y], data, header},
    If[FailureQ[record], Return[record]];
    data = storedExpansionData[record]; If[FailureQ[data], Return[data]];
    header = modelHeader[record["Context"], "modular form"]; If[FailureQ[header], Return[header]];
    Join[header, <|"FormID" -> record["ID"], "Revision" -> record["Revision"]|>,
        If[MissingQ[data],
            <|"Status" -> "NotComputed", "Binding" -> Missing["NotComputed"], "Cutoff" -> Missing["NotComputed"], "Arithmetic" -> Missing["NotComputed"],
                "Precision" -> Missing["NotComputed"], "Series" -> textNode["not computed: ModularFormQExp[y, n] computes and stores it"]|>,
            <|"Status" -> "Stored", "Binding" -> data["Binding"], "Cutoff" -> data["Cutoff"], "Arithmetic" -> data["Arithmetic"], "Precision" -> data["Precision"],
                "Series" -> qSeriesNode[data, parameterLabelNodes[record["Definition"]["Parameters"], {}], effective[MaxQTerms], effective[FactorQSeries]]|>]]
];
qExpansionCells[qexp_QExpansionData, effective_Association] := With[{data = validateQExpansion[qexp]},
    If[FailureQ[data], data, Join[modelHeader[Missing[], "q-expansion data"], <|"FormID" -> Missing["Supplied"], "Revision" -> Missing["Supplied"], "Status" -> "Supplied",
        "Binding" -> data["Binding"], "Cutoff" -> data["Cutoff"], "Arithmetic" -> data["Arithmetic"], "Precision" -> data["Precision"],
        "Series" -> qSeriesNode[data, <||>, effective[MaxQTerms], effective[FactorQSeries]]|>]]];

$FormViewOptions = {FormLabels -> <||>, IrrepLabels -> <||>, ExpressionMode -> "Normalized", MaxQTerms -> 6, FactorQSeries -> True, DisplayTimeLimit -> 5,
    ScalarNotation -> "Standard", NotationStyle -> "Standard", OneByOneMatrix -> "Scalar", DefineOmega -> True, Digits -> Automatic, Caption -> Automatic,
    Label -> None, PageSize -> 20};
$DisplayPresentationRules = {ScalarNotation -> "Standard", NotationStyle -> "Standard", OneByOneMatrix -> "Scalar", DefineOmega -> True, Digits -> Automatic,
    Caption -> Automatic, Label -> None, PageSize -> 20};

Options[ModularFormView] = $FormViewOptions;

(*
    Summary: Display snapshot of a modular form.
    Status: Alpha.
    Parameters: y — ModularForm.
    Options/defaults: FormLabels (<||>: custom label by form ID, string or TeXFragment); IrrepLabels; ExpressionMode
        ("Normalized": substitute the stored resolved coefficients, or "Raw"); MaxQTerms (6, or All); FactorQSeries
        (True); DisplayTimeLimit; the Stage 3 presentation options.
    Returns: DisplayDocument["ModularForm", data]: actual group and assignment, representation and basis, weight k and
        dimension, the definition (closed expression, MLDE or derivative recipe, or finite jet), the expression and its
        status, the stored q-expansion or "not computed", the normalization (rules, proof status, anchor frame), the
        evidence and revision; or Failure.
    Effects: Read-only: one consistent snapshot of the form; no q-expansion, coefficient solve, validation or GAP.
    Failures: UnknownModularForm; StaleExpansion; UnverifiedContext; InvalidOption.
    Example: ToLaTeX[ModularFormView[y]] shows Y^{(2)}_{3} with its expression and stored expansion.
    Remarks: Unresolved normalization shows the raw expression with status "Unresolved" and assigns no value.
    See also: ModularFormTable; QExpansionView; ModularFormQExp; ValidateModularForm.
*)
ModularFormView[y_ModularForm, options : OptionsPattern[]] := snapshotModularDisplay[y, "ModularForm", "ModularFormView", ModularFormView, {options}];
ModularFormView[___] := makeFailure["InvalidInput", "ModularFormView expects a ModularForm and options."];

Options[ModularFormTable] = Append[$FormViewOptions, IncludeWeight -> True];

(*
    Summary: Display snapshot of a list of modular forms.
    Status: Alpha.
    Parameters: forms — list of ModularForm values (caller order; may be empty).
    Options/defaults: As ModularFormView, plus IncludeWeight (True: a column of the actual weight k).
    Returns: DisplayDocument["ModularForms", data]: one row per form (ID, label, irrep, weight, expression, q-expansion,
        normalization and evidence status) in caller order, tables split into runs over one group and assignment with
        their own titles; or Failure.
    Effects: Read-only, as ModularFormView.
    Failures: InvalidInput (with the position of an element that is not a ModularForm); UnknownModularForm; StaleExpansion;
        InvalidOption.
    Example: ToLaTeX[ModularFormTable[{y1, y2}, MaxQTerms -> 4]].
    Remarks: Every element is validated; the caption never assigns the first form's group to all rows.
    See also: ModularFormView.
*)
ModularFormTable[forms_List, options : OptionsPattern[]] := snapshotModularDisplay[forms, "ModularForms", "ModularFormTable", ModularFormTable, {options}];
ModularFormTable[___] := makeFailure["InvalidInput", "ModularFormTable expects a list of ModularForm values and options."];

Options[QExpansionView] = Join[{MaxQTerms -> 6, FactorQSeries -> True}, $DisplayPresentationRules];

(*
    Summary: Display snapshot of a stored or supplied q-expansion.
    Status: Alpha.
    Parameters: y — ModularForm, or qexp — QExpansionData.
    Options/defaults: MaxQTerms (6 known nonzero terms per component, or All); FactorQSeries (True); the Stage 3
        presentation options.
    Returns: DisplayDocument["QExpansion", data]: status (Stored, NotComputed or Supplied), binding, cutoff, arithmetic and
        the series with exact rational powers, omitted-term markers and the stored O(q^n); or Failure.
    Effects: Read-only: a missing expansion shows "not computed" and is never computed (ModularFormQExp stores one).
    Failures: UnknownModularForm; StaleExpansion (an expansion that does not belong to the form's record); InvalidSeries.
    Example: ModularFormQExp[y, 10]; ToNotebook[QExpansionView[y, MaxQTerms -> All]].
    Remarks: A zero jet shows O(q^n), not a proved zero function; factoring never changes the cutoff's meaning.
    See also: ModularFormQExp; QExpansionExpression.
*)
QExpansionView[x : (_ModularForm | _QExpansionData), options : OptionsPattern[]] := snapshotModularDisplay[x, "QExpansion", "QExpansionView", QExpansionView, {options}];
QExpansionView[___] := makeFailure["InvalidInput", "QExpansionView expects a ModularForm or QExpansionData and options."];

Options[ModularDimensionView] = Join[{IrrepLabels -> <||>}, $DisplayPresentationRules];

(*
    Summary: Display snapshot of a modular dimension table.
    Status: Alpha.
    Parameters: data — the result of ModularDimensionTable (irrep ID -> <|weight -> dimension, Missing or Failure|>).
    Options/defaults: IrrepLabels (<||>: labels for irrep IDs of the table); the Stage 3 presentation options.
    Returns: DisplayDocument["ModularDimensions", data]: irreps in table order, weights in first-appearance order, and
        zero, known, unknown, failed and not-requested cells kept distinct; or Failure.
    Effects: Pure: no dimension is computed.
    Failures: InvalidInput (a malformed table); InvalidOption.
    Example: ToLaTeX[ModularDimensionView[ModularDimensionTable[c, All, {0, 2, 4}]]].
    See also: ModularDimensionTable; ModularDimension.
*)
(* a ModularDimensionTable document is already the view *)
ModularDimensionView[doc : DisplayDocument["ModularDimensions", _Association], OptionsPattern[]] := doc;
ModularDimensionView[data_Association, options : OptionsPattern[]] := snapshotModularDisplay[data, "ModularDimensions", "ModularDimensionView", ModularDimensionView, {options}];
ModularDimensionView[___] := makeFailure["InvalidInput", "ModularDimensionView expects a ModularDimensionTable result and options."];

Options[FormSlotTable] = Join[{FormSlotLabels -> <||>, IrrepLabels -> <||>, DisplayTimeLimit -> 5}, $DisplayPresentationRules];

(*
    Summary: Display snapshot of the form slots of a modular model.
    Status: Alpha.
    Parameters: m — modular Model.
    Options/defaults: FormSlotLabels (<||>: custom label by slot ID); IrrepLabels; DisplayTimeLimit; the Stage 3
        presentation options.
    Returns: DisplayDocument["FormSlots", data]: every registered slot with its full ID, label Y^(k)_r (Roman copy index
        in a space of dimension above one), irrep, weight, copy, stored space dimension, basis, whether a term uses it,
        and its frozen binding (form ID, revision, kind, proof status) or "unbound"; or Failure.
    Effects: Read-only: bindings come from the model's frozen records, never from live forms.
    Failures: InvalidModel; NotModularModel; InvalidOption; UnverifiedContext.
    Example: ToNotebook[FormSlotTable[BindModularForms[m, <|slot -> y|>]]].
    See also: ModularFormCandidates; BindModularForms; ModelView.
*)
FormSlotTable[m_Model, options : OptionsPattern[]] := snapshotModularDisplay[m, "FormSlots", "FormSlotTable", FormSlotTable, {options}];
FormSlotTable[___] := makeFailure["InvalidInput", "FormSlotTable expects a modular Model and options."];

True
