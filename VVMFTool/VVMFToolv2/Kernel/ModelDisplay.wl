(*
    :Title: Model display documents
    :Context: VVMFTool`Private`
    :Summary: Immutable display snapshots of Stage 5 values and Stage 6 outputs (ModelView, FieldTable, ContractionTable,
        CouplingTable, MassMatrixView, ModelOutputView) and the display nodes FieldComponent, Coupling and
        ScalarExpression, rendered through the shared Stage 3 notebook and LaTeX layers.
    :Responsibilities: modelAtomLabel, modelExpressionNode, texScalarTree, notebookScalarTree, snapshotModelDisplay and
        the kind handlers; ModelView, FieldTable, ContractionTable, CouplingTable, MassMatrixView, ModelOutputView.
    :Dependencies: DisplayData.wl (registerDisplayNode, registerDisplayKind, makeDisplayDocument, displayHeader,
        irrepLabelData); DisplayNotation.wl (scalarDisplayNode); LaTeXDisplay.wl; NotebookDisplay.wl; PythonIR.wl
        (encodeScalarTree, scalarTreeValue); Models.wl; Contractions.wl; Couplings.wl; MassMatrices.wl; ModelOutput.wl.
    :See Also: VVMFArch/step6Plan.md (Display records); VVMFArch/step3Plan.md (display contracts).
*)

(* -------------------------------------------------------------------------
   Atom labels and expression nodes
   ------------------------------------------------------------------------- *)

(*
    Summary: The label node of a model atom (a parameter or a field).
    Parameters: id — parameter or field ID; default — the record's label or name; custom — CouplingLabels or FieldLabels;
        duplicates — the default labels that more than one atom of the document uses.
    Options/defaults: None.
    Returns: Text or RawTeX label node.
    Effects: Pure.
    Failures: None.
    Example: modelAtomLabel["coupling-1a2b...", "c", <||>, {"c"}] is a Text node "c (1a2b...)".
    Remarks: A custom label is used as given (string or TeXFragment). A default label shared by several atoms gets the
        first eight characters of its ID appended, so two parameters labelled "c" stay distinguishable; labels never
        become symbols and never replace IDs in tables.
    See also: modelExpressionNode; CouplingTable.
*)
modelAtomLabel[id_String, default_String, custom_Association, duplicates_List] := Which[
    KeyExistsQ[custom, id], labelNode[custom[id]],
    MemberQ[duplicates, default], textNode[default <> " (" <> StringTake[StringReplace[id, RegularExpression["^[a-z]+-"] -> ""], UpTo[8]] <> ")"],
    True, textNode[default]];

(*
    Summary: The atom labels of a document: every parameter and field it can show.
    Parameters: parameters — parameter records (ID, Label); fields — field records (ID, Name, Dimension);
        effective — options with CouplingLabels and FieldLabels; slots — optional slot atoms (Stage 9, slotAtoms):
        <|slot ID -> <|"Label" -> node, "Dimension" -> d|>|> (default <||>).
    Options/defaults: None.
    Returns: <|"Slots" -> slot atoms, "Parameters" -> <|ID -> label node|>, "Fields" -> <|ID -> <|"Label" -> node, "Dimension" -> d|>|>|>.
    Effects: Pure.
    Failures: None.
    Example: modelAtoms[model["Parameters"], model["Fields"], opts]["Fields"] has one entry per field.
    See also: modelAtomLabel; modelExpressionNode.
*)
modelAtoms[parameters_List, fields_List, effective_Association] := modelAtoms[parameters, fields, effective, <||>];
modelAtoms[parameters_List, fields_List, effective_Association, slots_Association] := Module[{pLabels = Lookup[parameters, "Label", {}], fNames = Lookup[fields, "Name", {}]},
    <|"Slots" -> slots, "Parameters" -> AssociationThread[Lookup[parameters, "ID", {}], MapThread[modelAtomLabel[#1, #2, effective[CouplingLabels],
            Keys[Select[Counts[pLabels], # > 1 &]]] &, {Lookup[parameters, "ID", {}], pLabels}]],
        "Fields" -> AssociationThread[Lookup[fields, "ID", {}], MapThread[<|"Label" -> modelAtomLabel[#1, #2, effective[FieldLabels],
            Keys[Select[Counts[fNames], # > 1 &]]], "Dimension" -> #3|> &, {Lookup[fields, "ID", {}], fNames, Lookup[fields, "Dimension", {}]}]]|>
];

(*
    Summary: The ScalarExpression node of a model expression.
    Parameters: expr — scalar expression; atoms — modelAtoms result.
    Options/defaults: None.
    Returns: <|"Kind" -> "ScalarExpression", "Tree" -> tree, "Atoms" -> atoms|>, or, for syntax outside the tree grammar,
        <|"Kind" -> "ScalarExpression", "Literal" -> InputForm text, "Atoms" -> atoms|> (shown literally and marked).
    Effects: Pure.
    Failures: None.
    Example: modelExpressionNode[c x1 y1, atoms]["Tree"]["node"] is "times".
    Remarks: The tree is the same typed tree used by Python export and archives; the literal fallback is never
        presented as a different mathematical operation.
    See also: encodeScalarTree; texScalarTree; notebookScalarTree.
*)
modelExpressionNode[expr_, atoms_Association] := With[{tree = encodeScalarTree[expr, <|"Parameters" -> Keys[atoms["Parameters"]],
        "Fields" -> Map[#["Dimension"] &, atoms["Fields"]], "Slots" -> Map[#["Dimension"] &, Lookup[atoms, "Slots", <||>]]|>]},
    If[FailureQ[tree], <|"Kind" -> "ScalarExpression", "Literal" -> ToString[expr, InputForm], "Atoms" -> atoms|>,
        <|"Kind" -> "ScalarExpression", "Tree" -> tree, "Atoms" -> atoms|>]];

(*
    Summary: Whether a tree node is an exact constant (no parameter, field, temporary or approximate real inside).
    Parameters: node — tree node.
    Options/defaults: None.
    Returns: Boolean.
    Effects: Pure.
    Failures: None.
    Example: exactConstantTreeQ[encodeScalarTree[Sqrt[3], reg]] is True.
    See also: texScalarTree.
*)
exactConstantTreeQ[node_Association] := FreeQ[{node}, a_Association /; MemberQ[{"parameter", "field", "form", "temporary", "real"}, Lookup[a, "node", None]]];

(*
    Summary: The display scalar node of an exact algebraic constant subtree, or None.
    Parameters: node — tree node.
    Options/defaults: None.
    Returns: A Scalar or Phase node (Stage 3 notation), or None for non-algebraic constants (Pi), for atoms and when the
        exact reduction does not finish within two seconds (the structural form is shown then).
    Effects: Pure.
    Failures: None.
    Example: constantScalarNode[tree of Exp[2 Pi I/3]] is a Phase node, so ScalarNotation -> "Omega" applies.
    See also: scalarDisplayNode.
*)
constantScalarNode[node_Association] := If[!MemberQ[{"plus", "times", "power", "function", "surd", "complex", "algebraic"}, node["node"]] ||
        !exactConstantTreeQ[node], None,
    (* The scalar notation needs exact reduction of the constant (RootReduce, radical forms), which can be very slow for a
       sum of unrelated algebraic numbers (a field of high degree): it is bounded, and the structural form is used otherwise. *)
    Replace[TimeConstrained[With[{value = scalarTreeValue[node]}, If[exactAlgebraicQ[value], scalarDisplayNode[value], None]], 2, None],
        _Failure | $Aborted -> None]];

(*
    Summary: LaTeX of a scalar tree, keeping its structure.
    Parameters: node — tree node; atoms — label nodes; settings — render settings.
    Options/defaults: None.
    Returns: <|"TeX" -> string, "Precedence" -> 1 (sum or leading minus), 2 (product) or 3 (atomic)|>.
    Effects: Pure.
    Failures: None for valid trees.
    Example: texScalarTree[tree of c x_1^2, atoms, settings]["TeX"] contains "^{2}".
    Remarks: Maximal exact algebraic constant subtrees use the Stage 3 scalar notation (radicals, certified phases in
        the chosen ScalarNotation, Root notation); principal fractional powers are written x^{p/q} (x^{1/2} as a square
        root), real roots (Surd) as \sqrt[n]{x} with a legend; negative powers become fractions; nothing is simplified.
    See also: notebookScalarTree; ScalarExpression node.
*)
texScalarTree[node_Association, atoms_Association, settings_Association] := Module[{sub, wrap, constant},
    sub[n_] := texScalarTree[n, atoms, settings];
    wrap[r_, minimum_] := If[r["Precedence"] < minimum, "\\left(" <> r["TeX"] <> "\\right)", r["TeX"]];
    constant = constantScalarNode[node];
    If[AssociationQ[constant], Return[With[{t = renderTeXNode[constant, settings]},
        <|"TeX" -> t, "Precedence" -> If[StringStartsQ[t, "-"] || StringContainsQ[StringDrop[t, 1], "+" | "-"], 1, 2]|>]]];
    Switch[node["node"],
        "integer" | "rational", With[{v = scalarTreeValue[node]}, <|"TeX" -> texRational[v], "Precedence" -> If[v < 0, 1, 3]|>],
        "real", With[{v = realTreeValue[node]}, <|"TeX" -> texNumerical[v, settings], "Precedence" -> If[v < 0, 1, 3]|>],
        "complex", <|"TeX" -> texComplexParts[scalarTreeValue[node["re"]], scalarTreeValue[node["im"]],
            If[Precision[scalarTreeValue[node]] === Infinity, texRealExact, texNumerical[#, settings] &], settings], "Precedence" -> 1|>,
        "algebraic", <|"TeX" -> renderTeXNode[algebraicRootLabel[scalarTreeValue[node]], settings], "Precedence" -> 3|>,
        "constant", <|"TeX" -> Switch[node["name"], "Pi", "\\pi", "E", exponentialBaseTeX[settings], "EulerGamma", "\\gamma", "Catalan", "\\mathrm{G}"],
            "Precedence" -> 3|>,
        "parameter", <|"TeX" -> renderTeXNode[atoms["Parameters"][node["id"]], settings], "Precedence" -> 3|>,
        "field", <|"TeX" -> renderTeXNode[atoms["Fields"][node["id"]]["Label"], settings] <> "_{" <> node["index"] <> "}", "Precedence" -> 3|>,
        "form", <|"TeX" -> texFormLabel[atoms["Slots"][node["slot"]]["Label"], decodeInteger[node["index"]], settings], "Precedence" -> 3|>,
        "plus", With[{terms = sub /@ node["args"]},
            <|"TeX" -> StringJoin[MapIndexed[If[First[#2] === 1 || StringStartsQ[#1["TeX"], "-"], #1["TeX"], "+" <> #1["TeX"]] &, terms]], "Precedence" -> 1|>],
        "times", texTreeProduct[node, atoms, settings],
        "power", Module[{base = sub[node["base"]], exponent = node["exponent"], value},
            value = If[MemberQ[{"integer", "rational"}, exponent["node"]], scalarTreeValue[exponent], None];
            Which[
                node["base"] === <|"node" -> "constant", "name" -> "E"|>, <|"TeX" -> exponentialBaseTeX[settings] <> "^{" <> sub[exponent]["TeX"] <> "}", "Precedence" -> 3|>,
                value === 1/2, <|"TeX" -> "\\sqrt{" <> base["TeX"] <> "}", "Precedence" -> 3|>,
                NumericQ[value] && value < 0, <|"TeX" -> "\\frac{1}{" <> If[value === -1, base["TeX"],
                    If[value === -1/2, "\\sqrt{" <> base["TeX"] <> "}", wrap[base, 3] <> "^{" <> texRational[-value] <> "}"]] <> "}", "Precedence" -> 3|>,
                True, <|"TeX" -> wrap[base, 3] <> "^{" <> If[NumericQ[value], texRational[value], sub[exponent]["TeX"]] <> "}", "Precedence" -> 3|>]],
        "surd", <|"TeX" -> "\\sqrt[" <> node["n"] <> "]{" <> sub[node["base"]]["TeX"] <> "}", "Precedence" -> 3|>,
        "function", With[{arg = sub[First[node["args"]]]}, <|"TeX" -> Switch[node["name"],
            "Abs", "\\left|" <> arg["TeX"] <> "\\right|", "Conjugate", "\\overline{" <> arg["TeX"] <> "}",
            "Re", "\\operatorname{Re}\\left(" <> arg["TeX"] <> "\\right)", "Im", "\\operatorname{Im}\\left(" <> arg["TeX"] <> "\\right)",
            _, "\\" <> ToLowerCase[node["name"]] <> "\\left(" <> arg["TeX"] <> "\\right)"], "Precedence" -> 3|>]]
];

(*
    Summary: LaTeX of a product node: one constant coefficient, then the symbolic factors, negative powers as a fraction.
    Parameters: node — times node; atoms; settings.
    Options/defaults: None.
    Returns: As texScalarTree.
    Effects: Pure.
    Failures: None.
    Example: the product of -1/2, c and x^-1 renders as "-\frac{1}{2}\frac{c}{x}".
    See also: texScalarTree.
*)
texTreeProduct[node_Association, atoms_Association, settings_Association] := Module[{args = node["args"], constants, symbols, numerator, denominator,
        coefficient, coefficientTeX, negativeQ, factorTeX, body},
    constants = Select[args, exactConstantTreeQ]; symbols = Complement[args, constants];
    symbols = Select[args, MemberQ[symbols, #] &];
    negativeQ[n_] := n["node"] === "power" && MemberQ[{"integer", "rational"}, n["exponent"]["node"]] && scalarTreeValue[n["exponent"]] < 0;
    numerator = Select[symbols, !negativeQ[#] &];
    (* x^-k goes to the denominator as x^k, and x^-1 as x itself. *)
    denominator = Map[If[scalarTreeValue[#["exponent"]] === -1, #["base"],
        ReplacePart[#, "exponent" -> encodeScalarTree[-scalarTreeValue[#["exponent"]], <|"Parameters" -> {}, "Fields" -> <||>|>]]] &,
        Select[symbols, negativeQ]];
    factorTeX[n_] := With[{r = texScalarTree[n, atoms, settings]}, If[r["Precedence"] < 2, "\\left(" <> r["TeX"] <> "\\right)", r["TeX"]]];
    coefficient = Times @@ (scalarTreeValue /@ constants);
    coefficientTeX = Which[
        constants === {} || coefficient === 1, "",
        coefficient === -1, "-",
        exactAlgebraicQ[coefficient], With[{t = renderTeXNode[scalarDisplayNode[coefficient], settings]},
            If[StringContainsQ[StringDrop[t, 1], "+" | "-"], "\\left(" <> t <> "\\right)", t]],
        True, StringRiffle[factorTeX /@ constants, " "]];
    body = If[denominator === {}, StringRiffle[factorTeX /@ numerator, " "],
        "\\frac{" <> If[numerator === {}, "1", StringRiffle[factorTeX /@ numerator, " "]] <> "}{" <> StringRiffle[factorTeX /@ denominator, " "] <> "}"];
    <|"TeX" -> StringTrim[coefficientTeX <> If[coefficientTeX === "" || coefficientTeX === "-" || body === "", "", " "] <> body],
        "Precedence" -> If[StringStartsQ[coefficientTeX, "-"], 1, 2]|>
];

(*
    Summary: A notebook display expression of a scalar tree, keeping its structure.
    Parameters: node — tree node; atoms; settings.
    Options/defaults: None.
    Returns: Display expression (Row, Superscript, Subscript, DisplayForm boxes for fractions and roots).
    Effects: Pure.
    Failures: None for valid trees.
    Example: notebookScalarTree[tree of c x_1^2, atoms, settings] shows c and a subscripted, squared component.
    Remarks: Mirrors texScalarTree: exact constants use the Stage 3 notebook scalar notation; Surd is shown as a radical
        with a root index; nothing is evaluated.
    See also: texScalarTree.
*)
notebookScalarTree[node_Association, atoms_Association, settings_Association] := Module[{sub, paren, constant},
    sub[n_] := notebookScalarTree[n, atoms, settings];
    paren[n_] := If[MemberQ[{"plus", "times", "complex"}, n["node"]] || (MemberQ[{"integer", "rational", "real"}, n["node"]] && scalarTreeValue[n] < 0),
        Row[{"(", sub[n], ")"}], sub[n]];
    constant = constantScalarNode[node];
    If[AssociationQ[constant], Return[renderNotebookCell[constant, settings]]];
    Switch[node["node"],
        "integer" | "rational", scalarTreeValue[node],
        "real", renderNotebookCell[scalarDisplayNode[realTreeValue[node]], settings],
        "complex", With[{v = scalarTreeValue[node]}, If[Precision[v] === Infinity, HoldForm @@ {v}, renderNotebookCell[scalarDisplayNode[v], settings]]],
        "algebraic", renderNotebookCell[algebraicRootLabel[scalarTreeValue[node]], settings],
        "constant", Switch[node["name"], "Pi", "\[Pi]", "E", "\[ExponentialE]", "EulerGamma", Subscript["\[Gamma]", "E"], "Catalan", "G"],
        "parameter", renderNotebookCell[atoms["Parameters"][node["id"]], settings],
        "field", Subscript[renderNotebookCell[atoms["Fields"][node["id"]]["Label"], settings], decodeInteger[node["index"]]],
        "form", notebookFormLabel[atoms["Slots"][node["slot"]]["Label"], decodeInteger[node["index"]], settings],
        "plus", Row[Riffle[sub /@ node["args"], " + "]],
        "times", Row[Riffle[paren /@ node["args"], " "]],
        "power", Which[
            node["base"] === <|"node" -> "constant", "name" -> "E"|>, Superscript["\[ExponentialE]", sub[node["exponent"]]],
            node["exponent"] === <|"node" -> "rational", "value" -> {"1", "2"}|>, DisplayForm[SqrtBox[ToBoxes[sub[node["base"]]]]],
            True, Superscript[paren[node["base"]], sub[node["exponent"]]]],
        "surd", DisplayForm[RadicalBox[ToBoxes[sub[node["base"]]], ToBoxes[decodeInteger[node["n"]]]]],
        "function", With[{arg = sub[First[node["args"]]]}, Switch[node["name"],
            "Abs", Row[{"|", arg, "|"}], "Conjugate", Superscript[Row[{"(", arg, ")"}], "*"],
            _, Row[{ToLowerCase[node["name"]], "(", arg, ")"}]]]]
];

(*
    Summary: Legend tags a scalar tree needs.
    Parameters: node — tree node.
    Options/defaults: None.
    Returns: Tags ("SurdLegend", "NumericalLegend", "OmegaLegend", "RootLegend").
    Effects: Pure.
    Failures: None.
    Example: a tree with Surd needs "SurdLegend".
    See also: texDependencies.
*)
scalarTreeDependencyTags[node_Association] := Module[{nodes = Cases[{node}, a_Association /; KeyExistsQ[a, "node"], Infinity]},
    DeleteDuplicates[Join[
        If[MemberQ[Lookup[nodes, "node", {}], "surd"], {"SurdLegend"}, {}],
        If[MemberQ[Lookup[nodes, "node", {}], "real"], {"NumericalLegend"}, {}],
        If[MemberQ[Lookup[nodes, "node", {}], "algebraic"], {"RootLegend"}, {}],
        Flatten[texDependencies /@ DeleteCases[constantScalarNode /@ Select[nodes, MemberQ[{"plus", "times", "power", "function", "complex", "algebraic"}, #["node"]] &], None]]]]
];

registerDisplayNode["FieldComponent", <|"Validate" -> (StringQ[Lookup[#, "FieldID", None]] && IntegerQ[Lookup[#, "Index", None]] && #["Index"] >= 1 &&
        displayNodeQ[Lookup[#, "Label", None]] &),
    "Notebook" -> (Subscript[renderNotebookCell[#1["Label"], #2], #1["Index"]] &),
    "TeX" -> (renderTeXNode[#1["Label"], #2] <> "_{" <> ToString[#1["Index"]] <> "}" &),
    "Dependencies" -> ({} &)|>];
registerDisplayNode["Coupling", <|"Validate" -> (StringQ[Lookup[#, "ParameterID", None]] && displayNodeQ[Lookup[#, "Label", None]] &),
    "Notebook" -> (renderNotebookCell[#1["Label"], #2] &), "TeX" -> (renderTeXNode[#1["Label"], #2] &), "Dependencies" -> ({} &)|>];
registerDisplayNode["ScalarExpression", <|
    "Validate" -> Function[node, With[{atoms = Lookup[node, "Atoms", None]},
        AssociationQ[atoms] && AssociationQ[Lookup[atoms, "Parameters", None]] && AssociationQ[Lookup[atoms, "Fields", None]] &&
            AllTrue[Values[atoms["Parameters"]], displayNodeQ] && AllTrue[Values[atoms["Fields"]], AssociationQ[#] && displayNodeQ[Lookup[#, "Label", None]] &&
                IntegerQ[Lookup[#, "Dimension", None]] &] &&
            AssociationQ[Lookup[atoms, "Slots", <||>]] && AllTrue[Values[Lookup[atoms, "Slots", <||>]], AssociationQ[#] && labelNodeQ[Lookup[#, "Label", None]] &&
                IntegerQ[Lookup[#, "Dimension", None]] &] &&
            Which[KeyExistsQ[node, "Tree"], TrueQ[validateScalarTree[node["Tree"], <|"Parameters" -> Keys[atoms["Parameters"]],
                    "Fields" -> Map[#["Dimension"] &, atoms["Fields"]], "Slots" -> Map[#["Dimension"] &, Lookup[atoms, "Slots", <||>]]|>]],
                KeyExistsQ[node, "Literal"], StringQ[node["Literal"]], True, False]]],
    "Notebook" -> (If[KeyExistsQ[#1, "Tree"], notebookScalarTree[#1["Tree"], #1["Atoms"], #2], Row[{Style[#1["Literal"], "Program"], Style[" (literal)", Gray]}]] &),
    "TeX" -> (If[KeyExistsQ[#1, "Tree"], texScalarTree[#1["Tree"], #1["Atoms"], #2]["TeX"], "\\texttt{" <> escapeTeXText[#1["Literal"]] <> "}^{\\text{lit}}"] &),
    "Dependencies" -> (If[KeyExistsQ[#, "Tree"], scalarTreeDependencyTags[#["Tree"]], {}] &)|>];

(* -------------------------------------------------------------------------
   Shared snapshot pieces
   ------------------------------------------------------------------------- *)

(*
    Summary: The display header of a document of a frozen context, or of an unbound value.
    Parameters: context — RepresentationContext or Missing; name — display name of the unbound subject.
    Options/defaults: None.
    Returns: <|"Source", "ObservedAt", "Group"|> as displayHeader, or Failure for an unbound context.
    Effects: Reads the clock.
    Failures: UnverifiedContext.
    Example: modelHeader[model["Context"], "model"]["Group"]["Order"] is the group order.
    See also: displayHeader; displayGroupData.
*)
modelHeader[context_RepresentationContext, _] := With[{data = displayGroupData[context]}, If[FailureQ[data], data, displayHeader[data]]];
modelHeader[_, name_String] := <|"Source" -> <|"StateID" -> Missing["NotBound"], "GeneratorIdentity" -> Missing["NotBound"]|>,
    "ObservedAt" -> DateString["ISODateTime"], "Group" -> <|"Name" -> name, "Order" -> Missing["NotBound"], "Generators" -> {},
        "Assignment" -> Missing["NotAssigned"], "IrrepCount" -> Missing["NotBound"]|>|>;

(*
    Summary: The display rows of fields.
    Parameters: fields — field data; context — frozen context; atoms — modelAtoms; effective — options (IrrepLabels);
        weights — optional <|field ID -> kf|> of a modular model (Stage 9).
    Options/defaults: None.
    Returns: List of <|"ID", "Name", "Label", "IrrepID", "IrrepLabel", "Dimension", "BasisID", "Components" -> FieldComponent
        nodes|>, plus "WeightLabel" (kf) and "ActualWeight" (-kf, actualFieldWeight) for a field with a modular weight.
    Effects: Read-only label data of the context (no GAP, no group change).
    Failures: None (an irrep without label data shows its dimension).
    Example: fieldRows[model["Fields"], ctx, atoms, opts][[1, "Dimension"]] is the first field's dimension.
    See also: FieldTable; ModelView.
*)
fieldRows[fields_List, context_, atoms_Association, effective_Association] := fieldRows[fields, context, atoms, effective, <||>];
fieldRows[fields_List, context_, atoms_Association, effective_Association, weights_Association] := Module[
    {data = If[MatchQ[context, _RepresentationContext], displayGroupData[context], None]},
    Map[Function[f, Join[<|"ID" -> f["ID"], "Name" -> f["Name"], "Label" -> atoms["Fields"][f["ID"]]["Label"], "IrrepID" -> f["IrrepID"],
        "IrrepLabel" -> irrepDisplayLabel[data, f["IrrepID"], f["Dimension"], effective], "Dimension" -> f["Dimension"], "BasisID" -> f["BasisID"],
        "Components" -> Table[<|"Kind" -> "FieldComponent", "FieldID" -> f["ID"], "Index" -> i, "Label" -> atoms["Fields"][f["ID"]]["Label"]|>, {i, f["Dimension"]}]|>,
        If[modularWeightQ[Lookup[weights, f["ID"], None]], <|"WeightLabel" -> weights[f["ID"]], "ActualWeight" -> actualFieldWeight[weights[f["ID"]]]|>, <||>]]],
        fields]
];

(*
    Summary: The label node of an irrep of a document's context.
    Parameters: data — display group data or None; id — irrep ID; dimension; effective — options (IrrepLabels).
    Options/defaults: None.
    Returns: A label node: the custom IrrepLabels entry, the certified T-phase or dimension label of the context.
    Effects: May extend the display spectrum memo; no GAP work.
    Failures: None.
    Example: a triplet of A4 with an assignment shows 3 with its certified T phases.
    See also: irrepLabelData; resolveDisplayLabels.
*)
irrepDisplayLabel[data_, id_String, dimension_Integer, effective_Association] := Which[
    KeyExistsQ[effective[IrrepLabels], id], labelNode[effective[IrrepLabels][id]],
    AssociationQ[data], With[{label = irrepLabelData[data, id, Automatic, effective[DisplayTimeLimit]]},
        If[FailureQ[label], <|"Kind" -> "IrrepLabel", "Dimension" -> dimension, "Phases" -> None|>,
            First[Values[resolveDisplayLabels[{<|"IrrepID" -> id, "LabelData" -> label|>}, <||>]]]]],
    True, <|"Kind" -> "IrrepLabel", "Dimension" -> dimension, "Phases" -> None|>];

(*
    Summary: The display rows of parameter records.
    Parameters: parameters — records (ID, Label, Domain, SourceAtom); atoms — modelAtoms.
    Options/defaults: None.
    Returns: List of <|"ID", "Label" -> node, "Domain", "Source" -> held spelling text or "—"|>.
    Effects: Pure.
    Failures: None.
    Example: a declared symbol lambda shows Source "lambda".
    See also: CouplingTable.
*)
parameterRows[parameters_List, atoms_Association] := Map[<|"ID" -> #["ID"], "Label" -> atoms["Parameters"][#["ID"]], "Domain" -> #["Domain"],
    "Source" -> Replace[Lookup[#, "SourceAtom", Missing[]], {HoldForm[s_] :> ToString[Unevaluated[s], InputForm], s_String :> s, _ -> "\[LongDash]"}]|> &, parameters];

(*
    Summary: Short text of an ID for table cells.
    Parameters: id — string.
    Options/defaults: None.
    Returns: A short display form: a UUID-based ID (field-, term-, coupling-, model-...) as its prefix and first eight
        hex digits with an ellipsis, a 64-digit hash as its first twelve digits, a form-slot ID as "slot:" and eight digits;
        other IDs (channel paths) unchanged.
    Effects: Pure.
    Failures: None.
    Example: idText["path:abc"] is "path:abc"; DisplayData keeps every full ID.
    See also: modelTable.
*)
idText[id_String] := Which[
    StringMatchQ[id, RegularExpression["[a-z]+-[0-9a-f]{8}-[0-9a-f]{4}-[0-9a-f]{4}-[0-9a-f]{4}-[0-9a-f]{12}"]],
        StringTake[id, StringLength[First[StringSplit[id, "-"]]] + 9] <> "\[Ellipsis]",
    StringMatchQ[id, RegularExpression["[0-9a-f]{64}"]], StringTake[id, 12] <> "\[Ellipsis]",
    StringMatchQ[id, RegularExpression["slot:[0-9a-f]{24}"]], StringTake[id, 13] <> "\[Ellipsis]",
    True, id];
idText[other_] := ToString[other];

(* -------------------------------------------------------------------------
   Document kinds
   ------------------------------------------------------------------------- *)

(*
    Summary: A Table spec (for renderTeXTable through renderRegisteredTeX) and the matching notebook section.
    Parameters: title — part title or None; fixed, columns — header cells; rows — lists of {fixed cells, cells}.
    Options/defaults: None.
    Returns: <|"TeX" -> Table spec, "Notebook" -> <|"Title", "Header", "Rows"|>|>.
    Effects: Pure.
    Failures: None.
    Example: modelTable["Fields", {"ID"}, {"Name"}, {{{"\\texttt{f}"}, {textNode["L"]}}}]["TeX"]["Columns"] is {"Name"}.
    Remarks: Text cells in the LaTeX fixed columns are escaped strings; nodes render through the registry.
    See also: renderRegisteredTeX; registeredNotebookParts.
*)
modelTable[title_, fixed_List, columns_List, rows_List, alignment_String : "c"] := <|
    "TeX" -> <|"Title" -> title, "Alignment" -> alignment, "FixedShare" -> 0.3, "Fixed" -> fixed, "Columns" -> columns,
        "Rows" -> Map[<|"Kind" -> "Row", "Fixed" -> texCells[#[[1]]], "Cells" -> #[[2]]|> &, rows]|>,
    "Notebook" -> <|"Title" -> title, "Header" -> Join[fixed, columns], "Rows" -> Map[Join[notebookCells[#[[1]]], #[[2]]] &, rows]|>|>;
texCells[cells_List] := Map[If[AssociationQ[#] && Lookup[#, "Kind", None] === "Text", escapeTeXText[#["Text"]], #] &, cells];
notebookCells[cells_List] := cells;

$ShortIDLegend = "Long IDs are shortened (\[Ellipsis]); DisplayData holds every full ID.";

(*
    Summary: Text node of an ID (for table cells).
    Parameters: id — string.
    Options/defaults: None.
    Returns: Text node.
    Effects: Pure.
    Failures: None.
    Example: idNode["field-1"]["Text"] is "field-1".
    See also: modelTable.
*)
idNode[id_] := textNode[idText[id]];

(* Fields: field table. *)
fieldTableParts[rows_List] := If[AnyTrue[rows, KeyExistsQ[#, "WeightLabel"] &],
    (* Stage 9: a modular model's fields also show their weight label kf and actual weight -kf. *)
    modelTable["fields", {"ID", "Name"}, {"Irrep", "Dim.", "kf", "Weight", "Basis", "Components"},
        Map[{{idNode[#["ID"]], textNode[#["Name"]]}, {#["IrrepLabel"], textNode[ToString[#["Dimension"]]], textNode[weightText[Lookup[#, "WeightLabel", "\[LongDash]"]]],
            textNode[weightText[Lookup[#, "ActualWeight", "\[LongDash]"]]], idNode[#["BasisID"]],
            <|"Kind" -> "Matrix", "Dimensions" -> {1, Length[#["Components"]]}, "Cells" -> {#["Components"]}|>}} &, rows], "p"],
    modelTable["fields", {"ID", "Name"}, {"Irrep", "Dim.", "Basis", "Components"},
        Map[{{idNode[#["ID"]], textNode[#["Name"]]}, {#["IrrepLabel"], textNode[ToString[#["Dimension"]]], idNode[#["BasisID"]],
            <|"Kind" -> "Matrix", "Dimensions" -> {1, Length[#["Components"]]}, "Cells" -> {#["Components"]}|>}} &, rows], "p"]];
$WeightLegend = "kf is a field's weight label; the field transforms with actual modular weight -kf, and a form Y^(k) has actual weight k.";

(* Couplings: parameter table. *)
couplingTableParts[rows_List] := modelTable["parameters", {"ID"}, {"Label", "Domain", "Source"},
    Map[{{idNode[#["ID"]]}, {#["Label"], textNode[#["Domain"]], textNode[#["Source"]]}} &, rows], "p"];

registerDisplayKind["Fields", <|"Fields" -> {"ModelID", "ModelName", "Fields"},
    "Check" -> Function[data, ListQ[data["Fields"]] && DuplicateFreeQ[Lookup[data["Fields"], "ID", {}]] &&
        AllTrue[data["Fields"], Function[r, Length[r["Components"]] === r["Dimension"] && AllTrue[Join[{r["Label"], r["IrrepLabel"]}, r["Components"]], displayNodeQ]]]],
    "Caption" -> Function[data, "Fields of the model " <> data["ModelName"] <> " over " <> ToString[data["Group"]["Name"]]],
    "TeX" -> Function[{data, settings}, <|"Tables" -> {fieldTableParts[data["Fields"]]["TeX"]},
        "Legend" -> Join[If[AnyTrue[data["Fields"], KeyExistsQ[#, "WeightLabel"] &], {$WeightLegend}, {}], {$ShortIDLegend}]|>],
    "Notebook" -> Function[{data, settings}, <|"Sections" -> {fieldTableParts[data["Fields"]]["Notebook"]},
        "Legend" -> Join[If[AnyTrue[data["Fields"], KeyExistsQ[#, "WeightLabel"] &], {$WeightLegend}, {}], {$ShortIDLegend}]|>]|>];

registerDisplayKind["Couplings", <|"Fields" -> {"Subject", "Parameters", "Value"},
    "Check" -> Function[data, ListQ[data["Parameters"]] && DuplicateFreeQ[Lookup[data["Parameters"], "ID", {}]] &&
        AllTrue[data["Parameters"], displayNodeQ[#["Label"]] &] && (data["Value"] === None || displayNodeQ[data["Value"]])],
    "Caption" -> Function[data, "Parameters of " <> data["Subject"]],
    "TeX" -> Function[{data, settings}, <|"Tables" -> Join[{couplingTableParts[data["Parameters"]]["TeX"]},
            If[data["Value"] === None, {}, {modelTable["value", {"Expression"}, {"Value"}, {{{"Value"}, {data["Value"]}}}, "p"]["TeX"]}]],
        "Legend" -> {"Parameters with the same label are distinguished by their ID.", $ShortIDLegend}|>],
    "Notebook" -> Function[{data, settings}, <|"Sections" -> Join[{couplingTableParts[data["Parameters"]]["Notebook"]},
            If[data["Value"] === None, {}, {modelTable["value", {"Expression"}, {"Value"}, {{{"Value"}, {data["Value"]}}}, "p"]["Notebook"]}]],
        "Legend" -> {}|>]|>];

(*
    Summary: The table parts of a contraction document.
    Parameters: data — document data.
    Options/defaults: None.
    Returns: modelTable result.
    Effects: Pure.
    Failures: None.
    Example: one row per raw channel with its path, polynomial, zero status and independence role.
    See also: ContractionTable.
*)
contractionTableParts[data_Association] := modelTable["channels", {"Channel"}, {"Path", "Polynomial", "Zero", "Independence"},
    Map[{{idNode[#["ChannelID"]]}, {textNode[#["Path"]], #["Polynomial"], textNode[If[TrueQ[#["Zero"]], "zero", "nonzero"]], #["Independence"]}} &,
        data["Channels"]], "p"];

registerDisplayKind["Contractions", <|"Fields" -> {"SetID", "ModelID", "TargetIrrepID", "Factors", "Channels", "IndependenceStatus", "Rank"},
    "Check" -> Function[data, ListQ[data["Channels"]] && DuplicateFreeQ[Lookup[data["Channels"], "ChannelID", {}]] &&
        AllTrue[data["Channels"], displayNodeQ[#["Polynomial"]] && displayNodeQ[#["Independence"]] &]],
    "Caption" -> Function[data, "Contractions of " <> StringRiffle[data["Factors"], " \[CircleTimes] "] <> " into the target irrep " <> data["TargetIrrepID"]],
    "TeX" -> Function[{data, settings}, <|"Tables" -> {contractionTableParts[data]["TeX"]},
        "Legend" -> {If[data["IndependenceStatus"] === "Computed", "Independence: rank " <> ToString[data["Rank"]] <> "; basis channels are marked and every channel is expressed in the basis.",
            "Independence is not computed for this set (use IndependentContractions)."]}|>],
    "Notebook" -> Function[{data, settings}, <|"Sections" -> {contractionTableParts[data]["Notebook"]},
        "Legend" -> {If[data["IndependenceStatus"] === "Computed", "Independence: rank " <> ToString[data["Rank"]] <> ".", "Independence is not computed for this set."]}|>]|>];

(*
    Summary: The table parts of a model document.
    Parameters: data — document data.
    Options/defaults: None.
    Returns: List of modelTable results (summary, fields, terms, parameters; for a modular model also the form slots).
    Effects: Pure.
    Failures: None.
    Example: a model with one term gives a terms table with one row.
    Remarks: A modular model (data "Modular", Stage 9) adds its target weight kW and binding status to the summary and a
        form-slot table (formSlotTableParts).
    See also: ModelView.
*)
modelViewParts[data_Association] := {
    modelTable["summary", {"Property"}, {"Value"}, {
        {{textNode["Model"]}, {textNode[data["Name"] <> " (" <> idText[data["ModelID"]] <> ")"]}},
        {{textNode["Target"]}, {data["TargetLabel"]}},
        {{textNode["Symmetry"]}, {textNode[data["Status"]]}},
        {{textNode["Arithmetic"]}, {textNode[data["Arithmetic"]]}},
        Sequence @@ If[AssociationQ[Lookup[data, "Modular", None]], {
            {{textNode["Target weight"]}, {textNode["kW = " <> weightText[data["Modular"]["SuperpotentialWeight"]]]}},
            {{textNode["Form bindings"]}, {textNode[data["Modular"]["BindingStatus"]]}}}, {}],
        {{textNode["Expression"]}, {data["Expression"]}}}, "p"],
    fieldTableParts[data["Fields"]],
    modelTable["terms", {"Term"}, {"Symmetry", "Arithmetic", "Value"},
        Map[{{idNode[#["TermID"]]}, {textNode[#["Symmetry"]], textNode[#["Arithmetic"]], #["Value"]}} &, data["Terms"]], "p"],
    couplingTableParts[data["Parameters"]],
    Sequence @@ If[AssociationQ[Lookup[data, "Modular", None]], {formSlotTableParts[data["Modular"]["Slots"]]}, {}]};

registerDisplayKind["Model", <|"Fields" -> {"ModelID", "Name", "TargetIrrepID", "TargetLabel", "Status", "Arithmetic", "Fields", "Expression", "Terms", "Parameters"},
    "Check" -> Function[data, displayNodeQ[data["Expression"]] && displayNodeQ[data["TargetLabel"]] && ListQ[data["Terms"]] &&
        AllTrue[data["Terms"], displayNodeQ[#["Value"]] &] && AllTrue[data["Parameters"], displayNodeQ[#["Label"]] &] &&
        AllTrue[data["Fields"], Length[#["Components"]] === #["Dimension"] &] &&
        (!KeyExistsQ[data, "Modular"] || (AssociationQ[data["Modular"]] && modularWeightQ[data["Modular"]["SuperpotentialWeight"]] && StringQ[data["Modular"]["BindingStatus"]] &&
            formSlotRowsQ[data["Modular"]["Slots"]]))],
    "Caption" -> Function[data, "Model " <> data["Name"] <> " over " <> ToString[data["Group"]["Name"]]],
    "TeX" -> Function[{data, settings}, <|"Tables" -> Map[#["TeX"] &, modelViewParts[data]],
        "Legend" -> Join[{"Symmetry is the status recorded when each term was added (AddModelTerm checks every generator); a display certifies nothing new."},
            If[KeyExistsQ[data, "Modular"], {$WeightLegend, $SlotLegend}, {}], {$ShortIDLegend}]|>],
    "Notebook" -> Function[{data, settings}, <|"Sections" -> Map[#["Notebook"] &, modelViewParts[data]],
        "Legend" -> Join[{"Symmetry is the status recorded when each term was added; a display certifies nothing new."},
            If[KeyExistsQ[data, "Modular"], {$WeightLegend, $SlotLegend}, {}]]|>]|>];

(*
    Summary: The table parts of a mass-matrix document.
    Parameters: data — document data.
    Options/defaults: None.
    Returns: List of modelTable results (matrix, properties; with a source model also the required entry weights).
    Effects: Pure.
    Failures: None.
    Example: a 3 x 3 bilinear matrix has three rows labelled by the row components.
    See also: MassMatrixView.
*)
massViewParts[data_Association] := {
    modelTable["matrix", {"Row"}, data["Columns"], MapThread[{{#1}, #2} &, {data["Rows"], data["Matrix"]}]],
    modelTable["properties", {"Property"}, {"Value"}, {
        {{textNode["Sector"]}, {textNode[data["SectorKind"] <> " " <> StringRiffle[ToString /@ data["Shape"], " \[Times] "]]}},
        {{textNode["Convention"]}, {textNode[data["ConventionText"]]}},
        {{textNode["Selected"]}, {data["Selected"]}},
        {{textNode["Remainder"]}, {data["Remainder"]}},
        {{textNode["Arithmetic"]}, {textNode[data["Arithmetic"]]}},
        {{textNode["Validation"]}, {textNode[data["Validation"]]}}}, "p"],
    (* Stage 9: with a source modular model, the actual weight every entry needs (kW - w(row) - w(column)). *)
    Sequence @@ If[MatrixQ[Lookup[data, "EntryWeights", None]],
        {modelTable["entry weights", {"Row"}, data["Columns"], MapThread[{{#1}, Map[textNode[weightText[#]] &, #2]} &, {data["Rows"], data["EntryWeights"]}]]}, {}]};

registerDisplayKind["MassMatrix", <|"Fields" -> {"SectorKind", "Convention", "ConventionText", "Shape", "Rows", "Columns", "Matrix", "Selected", "Remainder",
        "Arithmetic", "Validation"},
    "Check" -> Function[data, Dimensions[data["Matrix"], 2] === data["Shape"] && Length[data["Rows"]] === First[data["Shape"]] &&
        Length[data["Columns"]] === Last[data["Shape"]] && AllTrue[Flatten[{data["Matrix"], data["Rows"], data["Columns"], data["Selected"], data["Remainder"]}], displayNodeQ] &&
        (!KeyExistsQ[data, "EntryWeights"] || (MatrixQ[data["EntryWeights"], modularWeightQ] && Dimensions[data["EntryWeights"]] === data["Shape"]))],
    "Caption" -> Function[data, data["SectorKind"] <> " coefficient matrix, " <> data["ConventionText"]],
    "TeX" -> Function[{data, settings}, <|"Tables" -> Map[#["TeX"] &, massViewParts[data]], "Legend" -> massLegend[data]|>],
    "Notebook" -> Function[{data, settings}, <|"Sections" -> Map[#["Notebook"] &, massViewParts[data]], "Legend" -> massLegend[data]|>]|>];
massLegend[data_Association] := Join[
    If[KeyExistsQ[data, "EntryWeights"], {"Entry weights: the actual modular weight each entry needs, kW - w(row) - w(column), with w = -kf; the display does not check the entries."}, {}],
    If[TrueQ[Lookup[data, "SlotPlaceholders", False]], {"Form-slot components are shown by slot ID: this matrix carries no slot records (use MassMatrixView[model, mass] for labels and weights)."}, {}]];

(*
    Summary: The table parts of a prepared-output document.
    Parameters: data — document data.
    Options/defaults: None.
    Returns: List of modelTable results (outputs, substitutions, runtime parameters, runtime fields; the runtime form slots of a
        modular output).
    Effects: Pure.
    Failures: None.
    Example: an output with a fixed coupling lists it under substitutions and not under runtime parameters.
    See also: ModelOutputView.
*)
outputViewParts[data_Association] := {
    modelTable["outputs", {"Output"}, {"Kind", "Shape", "Arithmetic", "Value"},
        Map[{{textNode[#["Name"]]}, {textNode[#["Kind"] <> ", " <> #["Origin"]], textNode[If[#["Shape"] === {}, "scalar", StringRiffle[ToString /@ #["Shape"], " \[Times] "]]],
            textNode[#["Arithmetic"] <> If[#["Arithmetic"] === "Numerical", " (" <> precisionText[#["Precision"]] <> ")", ""]], #["Value"]}} &, data["Outputs"]], "p"],
    modelTable["substitutions", {"Parameter"}, {"Label", "Value"},
        If[data["Substitutions"] === {}, {{{textNode["none"]}, {textNode["\[LongDash]"], textNode["\[LongDash]"]}}},
            Map[{{idNode[#["ID"]]}, {#["Label"], #["Value"]}} &, data["Substitutions"]]], "p"],
    couplingTableParts[data["RuntimeParameters"]],
    fieldTableParts[data["RuntimeFields"]],
    (* Stage 9: the runtime form slots of a modular output, with their frozen bindings. *)
    Sequence @@ If[AssociationQ[Lookup[data, "Modular", None]], {formSlotTableParts[data["Modular"]["Slots"]]}, {}]};

registerDisplayKind["ModelOutput", <|"Fields" -> {"OutputID", "ModelID", "ModelName", "Outputs", "Substitutions", "RuntimeParameters", "RuntimeFields"},
    "Check" -> Function[data, ListQ[data["Outputs"]] && data["Outputs"] =!= {} && AllTrue[data["Outputs"], displayNodeQ[#["Value"]] &] &&
        AllTrue[data["Substitutions"], displayNodeQ[#["Value"]] && displayNodeQ[#["Label"]] &] &&
        (!KeyExistsQ[data, "Modular"] || (AssociationQ[data["Modular"]] && formSlotRowsQ[data["Modular"]["Slots"]] && StringQ[data["Modular"]["BindingStatus"]]))],
    "Caption" -> Function[data, "Prepared outputs of the model " <> data["ModelName"] <> " over " <> ToString[data["Group"]["Name"]]],
    "TeX" -> Function[{data, settings}, <|"Tables" -> Map[#["TeX"] &, outputViewParts[data]],
        "Legend" -> {"Substituted parameters are explicit choices of this output, not properties of the model; the runtime parameters are in Python parameter order.", $ShortIDLegend}|>],
    "Notebook" -> Function[{data, settings}, <|"Sections" -> Map[#["Notebook"] &, outputViewParts[data]],
        "Legend" -> {"Substituted parameters are explicit choices of this output, not properties of the model."}|>]|>];

(* -------------------------------------------------------------------------
   View producers
   ------------------------------------------------------------------------- *)

$ModelViewOptions = {FieldLabels -> <||>, CouplingLabels -> <||>, IrrepLabels -> <||>, FormSlotLabels -> <||>, DisplayTimeLimit -> 5, ScalarNotation -> "Standard",
    NotationStyle -> "Standard", OneByOneMatrix -> "Scalar", DefineOmega -> True, Digits -> Automatic, Caption -> Automatic, Label -> None, PageSize -> 20};

(*
    Summary: Check FieldLabels, CouplingLabels, IrrepLabels and FormSlotLabels against the IDs a document can show.
    Parameters: effective — options; fieldIDs, parameterIDs, irrepIDs — known IDs (or All); slotIDs — known form-slot IDs
        (default {}: a document without slots accepts no FormSlotLabels).
    Options/defaults: None.
    Returns: True or InvalidOption Failure.
    Effects: Pure.
    Failures: InvalidOption naming the option with unknown IDs.
    Example: FieldLabels -> <|"nope" -> "x"|> fails for a model without that field.
    See also: snapshotModelDisplay.
*)
checkModelLabels[effective_Association, fieldIDs_, parameterIDs_, irrepIDs_] := checkModelLabels[effective, fieldIDs, parameterIDs, irrepIDs, {}];
checkModelLabels[effective_Association, fieldIDs_, parameterIDs_, irrepIDs_, slotIDs_List] := Which[
    !SubsetQ[slotIDs, Keys[Lookup[effective, FormSlotLabels, <||>]]], makeFailure["InvalidOption", "FormSlotLabels names unknown form-slot IDs.", <|"Options" -> {FormSlotLabels}|>],
    !SubsetQ[fieldIDs, Keys[effective[FieldLabels]]], makeFailure["InvalidOption", "FieldLabels names unknown field IDs.", <|"Options" -> {FieldLabels}|>],
    !SubsetQ[parameterIDs, Keys[effective[CouplingLabels]]], makeFailure["InvalidOption", "CouplingLabels names unknown parameter IDs.", <|"Options" -> {CouplingLabels}|>],
    irrepIDs =!= All && !SubsetQ[irrepIDs, Keys[effective[IrrepLabels]]], makeFailure["InvalidOption", "IrrepLabels names unknown irrep IDs.", <|"Options" -> {IrrepLabels}|>],
    True, True];

(*
    Summary: The display document of a Stage 5 value or a ModelOutput.
    Parameters: x — Model, ContractionSet, CoupledExpression, MassMatrix, {Model, MassMatrix} or ModelOutput; kind —
        document kind; options — option rules of the producer.
    Options/defaults: As the producer ($ModelViewOptions).
    Returns: DisplayDocument, or Failure.
    Effects: Read-only: no GAP, no CG computation, no independence or covariance computation, no change of the value.
    Failures: Option failures; the value's own validation failure (InvalidModel, InvalidContractionSet, ...);
        UnverifiedContext; InvalidDisplayDocument.
    Example: snapshotModelDisplay[m, "Model", {}] is ModelView[m].
    Remarks: Labels are fixed in the snapshot; renderers change only appearance.
    See also: ModelView; FieldTable; ContractionTable; CouplingTable; MassMatrixView; ModelOutputView.
*)
snapshotModelDisplay[x_, kind_String, operation_String, options_List] := Module[{effective, cells},
    effective = resolveOperationOptions[ModelView, operation, options];
    If[FailureQ[effective], Return[effective]];
    effective = displayIrrepOptions[x, effective]; If[FailureQ[effective], Return[effective]];
    cells = modelDisplayCells[x, kind, effective];
    If[FailureQ[cells], cells, makeDisplayDocument[kind, cells, effective]]
];

(*
    Summary: The header and cells of one model document kind.
    Parameters: x — value; kind; effective — validated options.
    Options/defaults: None.
    Returns: Association of header and cells, or Failure.
    Effects: As snapshotModelDisplay.
    Failures: As snapshotModelDisplay.
    Example: modelDisplayCells[m, "Fields", opts]["Fields"] has one row per field.
    See also: snapshotModelDisplay.
*)
modelDisplayCells[m_Model, kind : ("Model" | "Fields" | "Couplings"), effective_Association] := Module[{model = validateModelSchema[m], header, atoms, check, fields, data,
        modular, slots},
    If[FailureQ[model], Return[model]];
    header = modelHeader[model["Context"], "model"]; If[FailureQ[header], Return[header]];
    (* Stage 9: a modular model shows its slots (labels from the slot records), weights and binding status. *)
    modular = KeyExistsQ[model, "ModularData"];
    slots = If[modular, Values[model["ModularData"]["Slots"]], {}];
    check = checkModelLabels[effective, Lookup[model["Fields"], "ID", {}], Lookup[model["Parameters"], "ID", {}],
        First[model["Context"]]["CharacterData"]["IrrepIDs"], Lookup[slots, "ID", {}]];
    If[FailureQ[check], Return[check]];
    data = displayGroupData[model["Context"]];
    atoms = modelAtoms[model["Parameters"], model["Fields"], effective, slotAtoms[slots, data, effective]];
    fields = fieldRows[model["Fields"], model["Context"], atoms, effective, If[modular, model["ModularData"]["FieldWeights"], <||>]];
    Join[header, Switch[kind,
        "Fields", <|"ModelID" -> model["ID"], "ModelName" -> model["Name"], "Fields" -> fields|>,
        "Couplings", <|"Subject" -> "the model " <> model["Name"], "Parameters" -> parameterRows[model["Parameters"], atoms], "Value" -> None|>,
        "Model", <|"ModelID" -> model["ID"], "Name" -> model["Name"], "TargetIrrepID" -> model["TargetIrrepID"],
            "TargetLabel" -> irrepDisplayLabel[data, model["TargetIrrepID"], 1, effective],
            "Status" -> If[model["TargetIrrepID"] === First[model["Context"]]["CharacterData"]["TrivialIrrepID"], "Invariant", "Covariant with the target character"] <>
                " (" <> model["Validation"]["Status"] <> ")",
            "Arithmetic" -> model["Validation"]["Arithmetic"], "Fields" -> fields,
            "Expression" -> modelExpressionNode[Total[Lookup[model["Terms"], "Value", {}]], atoms],
            "Terms" -> Map[<|"TermID" -> #["TermID"], "Symmetry" -> #["Symmetry"], "Arithmetic" -> #["Arithmetic"], "Value" -> modelExpressionNode[#["Value"], atoms]|> &,
                model["Terms"]],
            "Parameters" -> parameterRows[model["Parameters"], atoms],
            Sequence @@ If[modular, {"Modular" -> <|"SuperpotentialWeight" -> model["ModularData"]["SuperpotentialWeight"], "BindingStatus" -> bindingStatus[model],
                "Slots" -> formSlotRows[model, atoms, data, effective]|>}, {}]|>]]
];
modelDisplayCells[e_CoupledExpression, "Couplings", effective_Association] := Module[{data = validateCoupledExpression[e], fields, atoms, check},
    If[FailureQ[data], Return[data]];
    fields = Map[<|"ID" -> #, "Name" -> idText[#], "Dimension" -> Max[Cases[data["Value"], FieldComponent[#, i_Integer] :> i, Infinity]]|> &, data["FieldIDs"]];
    check = checkModelLabels[effective, data["FieldIDs"], Lookup[data["Parameters"], "ID", {}], All, Keys[Lookup[data, "FormSlots", <||>]]];
    If[FailureQ[check], Return[check]];
    atoms = modelAtoms[data["Parameters"], fields, effective, slotAtoms[Values[Lookup[data, "FormSlots", <||>]], None, effective]];
    Join[modelHeader[Missing[], "coupled term " <> data["TermID"]], <|"Subject" -> "the coupled term " <> data["TermID"] <> " (" <> data["Symmetry"] <> ")",
        "Parameters" -> parameterRows[data["Parameters"], atoms], "Value" -> modelExpressionNode[data["Value"], atoms]|>]
];
modelDisplayCells[s_ContractionSet, "Contractions", effective_Association] := Module[{data = validateContractionSet[s], context, names, fields, atoms, check, relations, basis, header},
    If[FailureQ[data], Return[data]];
    context = Lookup[data, "Context", Missing[]];
    header = modelHeader[context, "contraction set"]; If[FailureQ[header], Return[header]];
    names = Lookup[data, "FieldNames", <||>];
    fields = Map[<|"ID" -> #, "Name" -> Lookup[names, #, idText[#]], "Dimension" -> Max[Append[Cases[data["Variables"], FieldComponent[#, i_Integer] :> i], 1]]|> &, data["FieldIDs"]];
    check = checkModelLabels[effective, data["FieldIDs"], {}, All, Keys[Lookup[data, "FormSlots", <||>]]]; If[FailureQ[check], Return[check]];
    atoms = modelAtoms[{}, fields, effective, slotAtoms[Values[Lookup[data, "FormSlots", <||>]],
        If[MatchQ[context, _RepresentationContext], displayGroupData[context], None], effective]];
    basis = If[MissingQ[data["Independence"]], Missing["NotComputed"], data["Independence"]["Basis"]];
    relations = If[MissingQ[data["Independence"]], <||>, data["Independence"]["Relations"]];
    Join[header, <|"SetID" -> data["ID"], "ModelID" -> data["ModelID"], "TargetIrrepID" -> data["TargetIrrepID"],
        "Factors" -> Map[Lookup[names, #, idText[#]] &, data["Factors"]],
        "Channels" -> Map[Function[ch, <|"ChannelID" -> ch["ChannelID"], "Path" -> pathText[ch["Path"], Join[AssociationMap[idText, data["FieldIDs"]], names]], "Polynomial" -> modelExpressionNode[ch["Polynomial"], atoms],
            "Zero" -> TrueQ[ch["Zero"]],
            "Selected" -> MemberQ[Lookup[data["Channels"], "ChannelID", {}], ch["ChannelID"]],
            "Independence" -> Which[MissingQ[basis], textNode["not computed"], MemberQ[basis, ch["ChannelID"]], textNode["basis"],
                True, textNode["= " <> relationText[relations[ch["ChannelID"]]]]]|>], data["RawChannels"]],
        "IndependenceStatus" -> If[MissingQ[basis], "NotComputed", "Computed"], "Rank" -> If[MissingQ[basis], Missing["NotComputed"], data["Independence"]["Rank"]]|>]
];
modelDisplayCells[mass_MassMatrix, "MassMatrix", effective_Association] := With[{data = validateMassMatrixData[mass]},
    If[FailureQ[data], data, massDisplayCells[data, None, effective]]];
(* Stage 9: with its source modular model, a matrix shows slot labels from the model's slot records and the actual weight
   every entry needs; the fields of the matrix must be fields of that model. *)
modelDisplayCells[{m_Model, mass_MassMatrix}, "MassMatrix", effective_Association] := Module[{model = validateModelSchema[m], data = validateMassMatrixData[mass]},
    If[FailureQ[model], Return[model]]; If[FailureQ[data], Return[data]];
    If[!KeyExistsQ[model, "ModularData"], Return[makeFailure["NotModularModel", "MassMatrixView[m, mass] needs a modular model; use MassMatrixView[mass] otherwise."]]];
    If[!SubsetQ[Lookup[model["Fields"], "ID", {}], DeleteDuplicates[Cases[{data["Rows"], data["Columns"], data["InputExpression"]}, FieldComponent[id_String, _] :> id, Infinity]]] ||
            !SubsetQ[Keys[model["ModularData"]["Slots"]], DeleteDuplicates[Cases[data["InputExpression"], FormComponent[id_String, _] :> id, Infinity]]],
        Return[makeFailure["ForeignMassMatrix", "The matrix uses fields or form slots that are not in this model."]]];
    massDisplayCells[data, model, effective]
];

(*
    Summary: The header and cells of a coefficient-matrix document.
    Parameters: data — validated MassMatrix data; model — its source modular model data or None; effective — options.
    Options/defaults: As MassMatrixView.
    Returns: Association of header and cells, or Failure.
    Effects: Read-only; ValidateMassMatrix is never run.
    Failures: InvalidOption.
    Example: massDisplayCells[data, None, opts]["Shape"] is the matrix shape.
    Remarks: Without a model, form-slot components are shown by their slot ID (no slot records travel with a matrix, so
        no label is guessed from a current group); with the model, slot labels come from its slot records and
        "EntryWeights" holds kW - w(row) - w(column) (entryWeights).
    See also: MassMatrixView; slotAtoms.
*)
massDisplayCells[data_Association, model_, effective_Association] := Module[{ids, names, fields, atoms, parameters, check, node, slotIDs, slots},
    ids = DeleteDuplicates[Cases[{data["Rows"], data["Columns"], data["InputExpression"]}, FieldComponent[id_String, _] :> id, Infinity]];
    names = Lookup[data, "FieldNames", <||>];
    fields = Map[<|"ID" -> #, "Name" -> Lookup[names, #, idText[#]], "Dimension" -> Max[Cases[{data["Rows"], data["Columns"], data["InputExpression"]}, FieldComponent[#, i_Integer] :> i, Infinity]]|> &, ids];
    (* The matrix's own parameter records (D-S5 M13), plus records of couplings that appear only in the input. *)
    parameters = DeleteDuplicatesBy[Join[Lookup[data, "Parameters", {}], Map[Lookup[$CouplingRecords, #, <|"ID" -> #, "Label" -> #, "Domain" -> "Complex",
        "SourceAtom" -> Missing[]|>] &, DeleteDuplicates[Cases[data["InputExpression"], Coupling[id_String] :> id, Infinity]]]], #["ID"] &];
    slotIDs = DeleteDuplicates[Cases[data["InputExpression"], FormComponent[id_String, _] :> id, Infinity]];
    check = checkModelLabels[effective, ids, Lookup[parameters, "ID", {}], All, slotIDs]; If[FailureQ[check], Return[check]];
    slots = If[AssociationQ[model], slotAtoms[Lookup[model["ModularData"]["Slots"], slotIDs], displayGroupData[model["Context"]], effective],
        AssociationMap[<|"Label" -> Lookup[Map[labelNode, Lookup[effective, FormSlotLabels, <||>]], #, textNode[idText[#]]],
            "Dimension" -> Max[Cases[data["InputExpression"], FormComponent[#, i_Integer] :> i, Infinity]]|> &, slotIDs]];
    atoms = modelAtoms[parameters, fields, effective, slots];
    node[e_] := modelExpressionNode[e, atoms];
    Join[modelHeader[Lookup[data, "Context", Missing[]], "coefficient matrix"], <|"SectorKind" -> data["Kind"], "Convention" -> data["Convention"],
        "ConventionText" -> Switch[data["Convention"], "Bilinear", "selected = rows . M . columns", "Polynomial", "selected = x . M . x", "Half", "selected = (x . M . x)/2"],
        "Shape" -> Dimensions[data["Matrix"]], "Rows" -> (node /@ data["Rows"]), "Columns" -> (node /@ data["Columns"]),
        "Matrix" -> Map[node, data["Matrix"], {2}], "Selected" -> node[data["Selected"]], "Remainder" -> node[data["Remainder"]],
        "Arithmetic" -> Lookup[data, "Arithmetic", "Exact"] <> If[Lookup[data, "Arithmetic", "Exact"] === "Numerical",
            " (precision " <> precisionText[Lookup[data, "Precision", Missing[]]] <> ", tolerance " <> ToString[Lookup[data, "Tolerance", Missing[]], InputForm] <> ")", ""],
        "Validation" -> "Extraction only: model covariance is certified by ValidateMassMatrix, which a display never runs."|>,
        If[AssociationQ[model], <|"EntryWeights" -> entryWeights[model, data]|>, <||>],
        If[!AssociationQ[model] && slotIDs =!= {}, <|"SlotPlaceholders" -> True|>, <||>]]
];modelDisplayCells[out_ModelOutput, "ModelOutput", effective_Association] := Module[{data = validateModelOutput[out], header, atoms, check, labels, modular, group},
    If[FailureQ[data], Return[data]];
    header = modelHeader[data["Context"], "model output"]; If[FailureQ[header], Return[header]];
    (* Stage 9: a modular output labels its runtime slots from the frozen slot records it carries. *)
    modular = Lookup[data, "Modular", None];
    check = checkModelLabels[effective, Lookup[data["Fields"], "ID", {}], Lookup[data["Parameters"], "ID", {}], All,
        If[AssociationQ[modular], modular["RuntimeSlots"], {}]]; If[FailureQ[check], Return[check]];
    group = displayGroupData[data["Context"]];
    atoms = modelAtoms[data["Parameters"], data["Fields"], effective, If[AssociationQ[modular], slotAtoms[Values[modular["Slots"]], group, effective], <||>]];
    labels = atoms["Parameters"];
    Join[header, <|"OutputID" -> data["ID"], "ModelID" -> data["ModelID"], "ModelName" -> data["ModelName"],
        "Outputs" -> Map[<|"Name" -> #["Name"], "Kind" -> #["Kind"], "Origin" -> #["Origin"], "Shape" -> #["Shape"], "Arithmetic" -> #["Arithmetic"],
            "Precision" -> #["Precision"], "Value" -> If[#["Kind"] === "Scalar", <|"Kind" -> "ScalarExpression", "Tree" -> #["Trees"], "Atoms" -> atoms|>,
                <|"Kind" -> "Matrix", "Dimensions" -> #["Shape"], "Cells" -> Map[Function[t, <|"Kind" -> "ScalarExpression", "Tree" -> t, "Atoms" -> atoms|>], #["Trees"], {2}]|>]|> &,
            data["Outputs"]],
        "Substitutions" -> KeyValueMap[<|"ID" -> #1, "Label" -> labels[#1], "Value" -> <|"Kind" -> "ScalarExpression", "Tree" -> #2, "Atoms" -> atoms|>|> &, data["SubstitutionTrees"]],
        "RuntimeParameters" -> parameterRows[Select[data["Parameters"], MemberQ[data["RuntimeParameters"], #["ID"]] &], atoms],
        "RuntimeFields" -> fieldRows[Select[data["Fields"], MemberQ[data["RuntimeFields"], #["ID"]] &], data["Context"], atoms, effective],
        Sequence @@ If[AssociationQ[modular], {"Modular" -> <|"BindingStatus" -> modular["BindingStatus"], "Formal" -> ToString[modular["Formal"]["Status"]],
            "Slots" -> formSlotRows[modular["Slots"], modular["Bindings"], Lookup[data["Outputs"], "Value", {}], atoms, group, effective]|>}, {}]|>]
];
modelDisplayCells[x_, kind_String, _] := makeFailure["InvalidInput", "This value has no " <> kind <> " view.", <|"Head" -> Head[x]|>];

(*
    Summary: Text of a contraction path and of a relation.
    Parameters: path — Stage 4 path record; names — field ID -> name; coefficients — basis ID -> coefficient.
    Options/defaults: None.
    Returns: String.
    Effects: Pure.
    Failures: None.
    Example: pathText[<|"Kind" -> "Product", "Left" -> leaf, "Right" -> leaf, "ChannelID" -> "c1"|>, names] is "(L ⊗ R)[c1]".
    See also: ContractionTable.
*)
pathText[path_Association, names_Association] := Switch[Lookup[path, "Kind", None],
    "Leaf", Lookup[names, path["VectorID"], path["VectorID"]],
    "Unit", "1",
    "Product", "(" <> pathText[path["Left"], names] <> " \[CircleTimes] " <> pathText[path["Right"], names] <> ")[" <> ToString[path["ChannelID"]] <> "]",
    _, ToString[path, InputForm]];
relationText[coefficients_Association] := With[{terms = KeyValueMap[ToString[#2, InputForm] <> " \[Times] " <> #1 &, Select[coefficients, # =!= 0 &]]},
    If[terms === {}, "0", StringRiffle[terms, " + "]]];

Options[ModelView] = $ModelViewOptions;

(*
    Summary: Display snapshot of a model.
    Status: Alpha.
    Parameters: m — Model.
    Options/defaults: FieldLabels, CouplingLabels (<||>: custom labels by field / parameter ID, strings or TeXFragment),
        IrrepLabels, FormSlotLabels (<||>: custom labels by form-slot ID), DisplayTimeLimit, and the Stage 3 presentation
        options.
    Returns: DisplayDocument["Model", data]: identity and target, invariant or nontrivial-character covariant status (as
        recorded when the terms were added), arithmetic, the field table, the model expression, the terms and the
        parameter table; a modular model also shows kf and actual weights, its target weight kW, binding status and form
        slots (the FormSlotTable rows); or Failure.
    Effects: Read-only; no GAP, no CG, no covariance recomputation.
    Failures: InvalidModel; UnverifiedContext; InvalidOption.
    Example: ToNotebook[ModelView[m]] shows the field, term and parameter tables.
    See also: FieldTable; CouplingTable; ToLaTeX; ValidateModel.
*)
ModelView[m_Model, options : OptionsPattern[]] := snapshotModelDisplay[m, "Model", "ModelView", {options}];
ModelView[___] := makeFailure["InvalidInput", "ModelView expects a Model and options."];

Options[FieldTable] = $ModelViewOptions;
(*
    Summary: Display snapshot of a model's fields.
    Status: Alpha.
    Parameters: m — Model.
    Options/defaults: As ModelView.
    Returns: DisplayDocument["Fields", data] with name, field ID, irrep (label and ID), dimension, basis ID and ordered
        components of every field (with the weight label kf and actual weight -kf in a modular model); or Failure.
    Effects: Read-only.
    Failures: InvalidModel; InvalidOption.
    Example: DisplayData[FieldTable[m]]["Fields"][[1, "Name"]] is the first field's name.
    See also: ModelView.
*)
FieldTable[m_Model, options : OptionsPattern[]] := snapshotModelDisplay[m, "Fields", "FieldTable", {options}];
FieldTable[___] := makeFailure["InvalidInput", "FieldTable expects a Model and options."];

Options[ContractionTable] = $ModelViewOptions;
(*
    Summary: Display snapshot of a contraction set.
    Status: Alpha.
    Parameters: s — ContractionSet.
    Options/defaults: As ModelView (CouplingLabels unused).
    Returns: DisplayDocument["Contractions", data]: factor order with repetitions, every raw channel with its full channel
        ID, path, polynomial and zero status, and its independence role (basis, relation, or "not computed"); or Failure.
    Effects: Read-only; independence is never computed by the display.
    Failures: InvalidContractionSet; InvalidOption.
    Example: ToNotebook[ContractionTable[Contractions[m, {l, r}]]] lists one channel for two A4 triplets.
    See also: Contractions; IndependentContractions.
*)
ContractionTable[s_ContractionSet, options : OptionsPattern[]] := snapshotModelDisplay[s, "Contractions", "ContractionTable", {options}];
ContractionTable[___] := makeFailure["InvalidInput", "ContractionTable expects a ContractionSet and options."];

Options[CouplingTable] = $ModelViewOptions;
(*
    Summary: Display snapshot of the parameters of a model or a coupled term.
    Status: Alpha.
    Parameters: x — Model or CoupledExpression.
    Options/defaults: As ModelView.
    Returns: DisplayDocument["Couplings", data]: parameter ID, label, domain and held source spelling (a coupled term also
        shows its scalar value); or Failure.
    Effects: Read-only.
    Failures: InvalidModel; InvalidCoupledExpression; InvalidOption.
    Example: two couplings labelled "c" appear with distinct IDs.
    See also: ModelParameters; CouplingParameters.
*)
CouplingTable[x : (_Model | _CoupledExpression), options : OptionsPattern[]] := snapshotModelDisplay[x, "Couplings", "CouplingTable", {options}];
CouplingTable[___] := makeFailure["InvalidInput", "CouplingTable expects a Model or a CoupledExpression and options."];

Options[MassMatrixView] = $ModelViewOptions;
(*
    Summary: Display snapshot of a coefficient matrix.
    Status: Alpha.
    Parameters: mass — MassMatrix; m — optional source modular Model (Stage 9).
    Options/defaults: As ModelView.
    Returns: DisplayDocument["MassMatrix", data]: shape (a 1 x 1 matrix keeps its shape), ordered row and column variables,
        entries, convention, selected sector and remainder, and the extraction status; with m also the form-slot labels
        of m and the actual weight every entry needs (EntryWeights); or Failure.
    Effects: Read-only; ValidateMassMatrix is never run.
    Failures: InvalidMassMatrix; InvalidOption; NotModularModel, ForeignMassMatrix (fields or slots outside m).
    Example: ToLaTeX[MassMatrixView[mass]] contains the matrix rows labelled by components.
    Remarks: Without m, form-slot components show their slot ID with a placeholder legend: a matrix carries no slot
        records and no label is guessed from a current group.
    See also: ExtractBilinearMatrix; ValidateMassMatrix.
*)
MassMatrixView[mass_MassMatrix, options : OptionsPattern[]] := snapshotModelDisplay[mass, "MassMatrix", "MassMatrixView", {options}];
MassMatrixView[m_Model, mass_MassMatrix, options : OptionsPattern[]] := snapshotModelDisplay[{m, mass}, "MassMatrix", "MassMatrixView", {options}];
MassMatrixView[___] := makeFailure["InvalidInput", "MassMatrixView expects a MassMatrix (optionally after its modular model) and options."];

Options[ModelOutputView] = $ModelViewOptions;
(*
    Summary: Display snapshot of a prepared model output.
    Status: Alpha.
    Parameters: out — ModelOutput.
    Options/defaults: As ModelView.
    Returns: DisplayDocument["ModelOutput", data]: every output (kind, origin, shape, arithmetic, value), the explicit
        substitutions, the runtime parameters in Python order and the required fields; or Failure.
    Effects: Read-only.
    Failures: InvalidModelOutput; UnverifiedContext; InvalidOption.
    Example: a fixed coupling appears under substitutions, not under runtime parameters.
    See also: PrepareModelOutput; ToPython.
*)
ModelOutputView[out_ModelOutput, options : OptionsPattern[]] := snapshotModelDisplay[out, "ModelOutput", "ModelOutputView", {options}];
ModelOutputView[___] := makeFailure["InvalidInput", "ModelOutputView expects a ModelOutput and options."];

True
