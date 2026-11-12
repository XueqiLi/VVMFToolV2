(*
    :Title: Modular display nodes
    :Context: VVMFTool`Private`
    :Summary: The closed display nodes of Stage 9 (FormLabel, FormComponent, ModularExpression, QSeries, Normalization,
        Evidence): their data builders, validators, notebook and LaTeX renderers and dependency collectors, registered in
        the Stage 3 node registry.
    :Responsibilities: modularDisplayTree, validModularTreeQ, texModularTree, notebookModularTree, modularExpressionNode,
        qSeriesNode, qSeriesComponent, normalizationNode, evidenceNode, formLabelNode, formComponentNode and the node
        handlers.
    :Dependencies: DisplayData.wl (registerDisplayNode, displayNodeQ); DisplayLabels.wl (textNode, labelNode);
        LaTeXDisplay.wl (renderTeXNode, texRational, escapeTeXText); NotebookDisplay.wl (renderNotebookCell); PythonIR.wl
        (encodeScalarTree, scalarTreeValue); ModelDisplay.wl (texScalarTree, notebookScalarTree, scalarTreeDependencyTags);
        Models.wl (numericConstantQ); ModularScalars.wl ($ScalarModularNames).
    :See Also: VVMFArch/step9Plan.md (Presentation contracts); VVMFArch/implementation/step9Status.md (D-S9-6, D-S9-7).
*)

(* -------------------------------------------------------------------------
   Modular expression trees (D-S9-6)
   ------------------------------------------------------------------------- *)

$ModularIngredientTeX = <|"Eta" -> "\\eta", "E2" -> "E_{2}", "E4" -> "E_{4}", "E6" -> "E_{6}", "Delta" -> "\\Delta", "j" -> "j", "K" -> "K"|>;
$ModularIngredientNotebook = <|"Eta" -> "\[Eta]", "E2" -> Subscript["E", 2], "E4" -> Subscript["E", 4], "E6" -> Subscript["E", 6],
    "Delta" -> "\[CapitalDelta]", "j" -> Style["j", Italic], "K" -> Style["K", Italic]|>;
$NoAtoms = <|"Parameters" -> <||>, "Fields" -> <||>|>;

(*
    Summary: The display tree of a Stage 7 definition expression.
    Parameters: e — expression of the definition grammar (numbers, FormVariable, FormParameter, ModularScalarNode,
        HypergeometricKNode, MLDEComponentNode, ModularDerivativeNode, Plus, Times, Power).
    Options/defaults: None.
    Returns: Tree association with "node" one of scalar (a Stage 6 scalar tree of an exact or numerical constant),
        variable, parameter, ingredient, hypergeometric, mlde, derivative, plus, times, power or literal.
    Effects: Pure.
    Failures: None: a subexpression outside the grammar becomes a literal node (shown literally and marked).
    Example: modularDisplayTree[2 ModularScalarNode["E4", FormVariable["q"], "q"]]["node"] is "times".
    Remarks: A separate display grammar (D-S9-6): unlike the portable recipe grammar it keeps unresolved FormParameter
        atoms (Raw mode), MLDE components and derivatives, and it never evaluates or simplifies anything.
    See also: texModularTree; notebookModularTree; validModularTreeQ.
*)
modularDisplayTree[e_] := Which[
    numericConstantQ[e], With[{tree = encodeScalarTree[e, <|"Parameters" -> {}, "Fields" -> <||>|>]},
        If[FailureQ[tree], <|"node" -> "literal", "text" -> ToString[e, InputForm]|>, <|"node" -> "scalar", "tree" -> tree|>]],
    MatchQ[e, FormVariable["q" | "tau"]], <|"node" -> "variable", "name" -> First[e]|>,
    MatchQ[e, FormParameter[_String]], <|"node" -> "parameter", "id" -> First[e]|>,
    MatchQ[e, ModularScalarNode[_String, _, _]] && MemberQ[$ScalarModularNames, e[[1]]], <|"node" -> "ingredient", "name" -> e[[1]]|>,
    MatchQ[e, HypergeometricKNode[{(_Integer | _Rational) ...}, {(_Integer | _Rational) ...}, _, _]],
        <|"node" -> "hypergeometric", "a" -> Map[encodeScalarTree[#, <|"Parameters" -> {}, "Fields" -> <||>|>] &, e[[1]]],
            "b" -> Map[encodeScalarTree[#, <|"Parameters" -> {}, "Fields" -> <||>|>] &, e[[2]]]|>,
    MatchQ[e, MLDEComponentNode[_String, _String, _Integer?Positive]], <|"node" -> "mlde", "family" -> e[[1]], "seed" -> e[[2]], "component" -> e[[3]]|>,
    MatchQ[e, ModularDerivativeNode[_?modularWeightQ, _]], <|"node" -> "derivative", "weight" -> e[[1]], "arg" -> modularDisplayTree[e[[2]]]|>,
    Head[e] === Plus, <|"node" -> "plus", "args" -> Map[modularDisplayTree, List @@ e]|>,
    Head[e] === Times, <|"node" -> "times", "args" -> Map[modularDisplayTree, List @@ e]|>,
    MatchQ[e, Power[_, _]], <|"node" -> "power", "base" -> modularDisplayTree[e[[1]]], "exponent" -> modularDisplayTree[e[[2]]]|>,
    True, <|"node" -> "literal", "text" -> ToString[e, InputForm]|>];

(*
    Summary: Check a modular display tree.
    Parameters: node — tree; parameters — the known parameter IDs.
    Options/defaults: None.
    Returns: Boolean.
    Effects: Pure.
    Failures: None (False for malformed trees, unknown parameters and scalar trees that fail validateScalarTree).
    Example: validModularTreeQ[<|"node" -> "variable", "name" -> "q"|>, {}] is True.
    See also: modularDisplayTree.
*)
validModularTreeQ[node_Association, parameters_List] := Module[{keys = Sort[Keys[node]], sub},
    sub[n_] := validModularTreeQ[n, parameters];
    Switch[Lookup[node, "node", None],
        "scalar", keys === {"node", "tree"} && TrueQ[validateScalarTree[node["tree"], <|"Parameters" -> {}, "Fields" -> <||>|>]],
        "variable", keys === {"name", "node"} && MemberQ[{"q", "tau"}, node["name"]],
        "parameter", keys === {"id", "node"} && MemberQ[parameters, node["id"]],
        "ingredient", keys === {"name", "node"} && MemberQ[$ScalarModularNames, node["name"]],
        "hypergeometric", keys === {"a", "b", "node"} && ListQ[node["a"]] && ListQ[node["b"]] &&
            AllTrue[Join[node["a"], node["b"]], AssociationQ[#] && MemberQ[{"integer", "rational"}, Lookup[#, "node", None]] && TrueQ[validateScalarTree[#, Automatic]] &],
        "mlde", keys === {"component", "family", "node", "seed"} && StringQ[node["family"]] && StringQ[node["seed"]] && IntegerQ[node["component"]] && node["component"] >= 1,
        "derivative", keys === {"arg", "node", "weight"} && modularWeightQ[node["weight"]] && sub[node["arg"]],
        "plus" | "times", keys === {"args", "node"} && ListQ[node["args"]] && Length[node["args"]] >= 2 && AllTrue[node["args"], sub],
        "power", keys === {"base", "exponent", "node"} && sub[node["base"]] && sub[node["exponent"]],
        "literal", keys === {"node", "text"} && StringQ[node["text"]],
        _, False]
];
validModularTreeQ[___] := False;

(*
    Summary: Whether a modular display tree is a scalar constant, and its value.
    Parameters: node — tree.
    Options/defaults: None.
    Returns: modularConstantQ: Boolean; modularConstantValue: the exact or numerical value of a scalar node.
    Effects: Pure.
    Failures: None.
    Example: modularConstantQ[modularDisplayTree[3/2]] is True.
    See also: texModularTree.
*)
modularConstantQ[node_Association] := node["node"] === "scalar";
modularConstantValue[node_Association] := scalarTreeValue[node["tree"]];

(*
    Summary: LaTeX of a modular display tree, keeping its structure.
    Parameters: node — tree; parameters — <|parameter ID -> label node|>; settings — render settings.
    Options/defaults: None.
    Returns: <|"TeX" -> string, "Precedence" -> 1 (sum or leading minus), 2 (product) or 3 (atomic)|>.
    Effects: Pure.
    Failures: None for valid trees.
    Example: texModularTree[modularDisplayTree[ModularScalarNode["E4", FormVariable["q"], "q"]^2], <||>, s]["TeX"] is "E_{4}^{2}".
    Remarks: Ingredients are written without their argument (the coordinate is stated by the document): \eta, E_k,
        \Delta, j, K = 1728/j; the hypergeometric function is {}_pF_q(a_1, ...; b_1, ...; K) with its two parameter lists
        separated by a semicolon; MLDE solution components are written seed_i (F_i, G_i); D_k is the modular derivative.
        Numerical and exact constants use the Stage 6 scalar notation.
    See also: notebookModularTree; texScalarTree.
*)
texModularTree[node_Association, parameters_Association, settings_Association] := Module[{sub, wrap},
    sub[n_] := texModularTree[n, parameters, settings];
    wrap[r_, minimum_] := If[r["Precedence"] < minimum, "\\left(" <> r["TeX"] <> "\\right)", r["TeX"]];
    Switch[node["node"],
        "scalar", texScalarTree[node["tree"], $NoAtoms, settings],
        "variable", <|"TeX" -> If[node["name"] === "tau", "\\tau", "q"], "Precedence" -> 3|>,
        "parameter", <|"TeX" -> renderTeXNode[parameters[node["id"]], settings], "Precedence" -> 3|>,
        "ingredient", <|"TeX" -> $ModularIngredientTeX[node["name"]], "Precedence" -> 3|>,
        "hypergeometric", <|"TeX" -> "{}_{" <> ToString[Length[node["a"]]] <> "}F_{" <> ToString[Length[node["b"]]] <> "}\\left(" <>
            StringRiffle[texRational[scalarTreeValue[#]] & /@ node["a"], ", "] <> ";\\," <> StringRiffle[texRational[scalarTreeValue[#]] & /@ node["b"], ", "] <>
            ";\\,K\\right)", "Precedence" -> 3|>,
        "mlde", <|"TeX" -> node["seed"] <> "_{" <> ToString[node["component"]] <> "}", "Precedence" -> 3|>,
        "derivative", <|"TeX" -> "D_{" <> texRational[node["weight"]] <> "}\\left(" <> sub[node["arg"]]["TeX"] <> "\\right)", "Precedence" -> 3|>,
        "plus", With[{terms = sub /@ node["args"]},
            <|"TeX" -> StringJoin[MapIndexed[If[First[#2] === 1 || StringStartsQ[#1["TeX"], "-"], #1["TeX"], "+" <> #1["TeX"]] &, terms]], "Precedence" -> 1|>],
        "times", texModularProduct[node, parameters, settings],
        "power", Module[{base = sub[node["base"]], exponent = node["exponent"], value},
            value = If[modularConstantQ[exponent] && MatchQ[modularConstantValue[exponent], _Integer | _Rational], modularConstantValue[exponent], None];
            Which[
                node["base"] === <|"node" -> "scalar", "tree" -> <|"node" -> "constant", "name" -> "E"|>|>,
                    <|"TeX" -> "e^{" <> sub[exponent]["TeX"] <> "}", "Precedence" -> 3|>,
                value === 1/2, <|"TeX" -> "\\sqrt{" <> base["TeX"] <> "}", "Precedence" -> 3|>,
                NumericQ[value] && value < 0, <|"TeX" -> "\\frac{1}{" <> If[value === -1, base["TeX"], wrap[base, 3] <> "^{" <> texRational[-value] <> "}"] <> "}",
                    "Precedence" -> 3|>,
                True, <|"TeX" -> wrap[base, 3] <> "^{" <> If[NumericQ[value], texRational[value], sub[exponent]["TeX"]] <> "}", "Precedence" -> 3|>]],
        "literal", <|"TeX" -> "\\texttt{" <> escapeTeXText[node["text"]] <> "}^{\\text{lit}}", "Precedence" -> 3|>]
];

(*
    Summary: LaTeX of a product: one constant coefficient first, then the other factors, negative powers as a fraction.
    Parameters: node — times node; parameters; settings.
    Options/defaults: None.
    Returns: As texModularTree.
    Effects: Pure.
    Failures: None.
    Example: the product of -2, E4 and q^-1 renders as "-2\frac{E_{4}}{q}".
    See also: texModularTree.
*)
texModularProduct[node_Association, parameters_Association, settings_Association] := Module[{args = node["args"], constants, others, negativeQ, numerator,
        denominator, coefficient, coefficientTeX, factorTeX, body},
    constants = Select[args, modularConstantQ]; others = Select[args, !modularConstantQ[#] &];
    negativeQ[n_] := n["node"] === "power" && modularConstantQ[n["exponent"]] && MatchQ[modularConstantValue[n["exponent"]], _Integer | _Rational] &&
        modularConstantValue[n["exponent"]] < 0;
    numerator = Select[others, !negativeQ[#] &];
    denominator = Map[If[modularConstantValue[#["exponent"]] === -1, #["base"],
        <|"node" -> "power", "base" -> #["base"], "exponent" -> modularDisplayTree[-modularConstantValue[#["exponent"]]]|>] &, Select[others, negativeQ]];
    factorTeX[n_] := With[{r = texModularTree[n, parameters, settings]}, If[r["Precedence"] < 2, "\\left(" <> r["TeX"] <> "\\right)", r["TeX"]]];
    coefficient = Times @@ (modularConstantValue /@ constants);
    coefficientTeX = Which[
        constants === {} || coefficient === 1, "",
        coefficient === -1, "-",
        True, With[{t = texScalarTree[encodeScalarTree[coefficient, <|"Parameters" -> {}, "Fields" -> <||>|>], $NoAtoms, settings]["TeX"]},
            If[StringContainsQ[StringDrop[t, 1], "+" | "-"], "\\left(" <> t <> "\\right)", t]]];
    body = If[denominator === {}, StringRiffle[factorTeX /@ numerator, " "],
        "\\frac{" <> If[numerator === {}, "1", StringRiffle[factorTeX /@ numerator, " "]] <> "}{" <> StringRiffle[factorTeX /@ denominator, " "] <> "}"];
    <|"TeX" -> StringTrim[coefficientTeX <> If[coefficientTeX === "" || coefficientTeX === "-" || body === "", "", " "] <> body],
        "Precedence" -> If[StringStartsQ[coefficientTeX, "-"], 1, 2]|>
];

(*
    Summary: A notebook display expression of a modular display tree.
    Parameters: node — tree; parameters — <|ID -> label node|>; settings.
    Options/defaults: None.
    Returns: Display expression (Row, Superscript, Subscript).
    Effects: Pure.
    Failures: None for valid trees.
    Example: notebookModularTree[modularDisplayTree[FormVariable["tau"]], <||>, s] is "\[Tau]".
    Remarks: Mirrors texModularTree; nothing is evaluated.
    See also: texModularTree.
*)
notebookModularTree[node_Association, parameters_Association, settings_Association] := Module[{sub, paren},
    sub[n_] := notebookModularTree[n, parameters, settings];
    paren[n_] := If[MemberQ[{"plus", "times"}, n["node"]] || (modularConstantQ[n] && !FreeQ[n, "plus" | "complex"]), Row[{"(", sub[n], ")"}], sub[n]];
    Switch[node["node"],
        "scalar", notebookScalarTree[node["tree"], $NoAtoms, settings],
        "variable", If[node["name"] === "tau", "\[Tau]", Style["q", Italic]],
        "parameter", renderNotebookCell[parameters[node["id"]], settings],
        "ingredient", $ModularIngredientNotebook[node["name"]],
        "hypergeometric", Row[{Subscript["", Length[node["a"]]], Subscript["F", Length[node["b"]]], "(",
            Row[Riffle[scalarTreeValue /@ node["a"], ", "]], "; ", Row[Riffle[scalarTreeValue /@ node["b"], ", "]], "; ", Style["K", Italic], ")"}],
        "mlde", Subscript[Style[node["seed"], Italic], node["component"]],
        "derivative", Row[{Subscript["D", node["weight"]], "(", sub[node["arg"]], ")"}],
        "plus", Row[Riffle[sub /@ node["args"], " + "]],
        "times", Row[Riffle[paren /@ node["args"], " "]],
        "power", If[node["base"] === <|"node" -> "scalar", "tree" -> <|"node" -> "constant", "name" -> "E"|>|>,
            Superscript["\[ExponentialE]", sub[node["exponent"]]], Superscript[paren[node["base"]], sub[node["exponent"]]]],
        "literal", Row[{Style[node["text"], "Program"], Style[" (literal)", Gray]}]]
];

(*
    Summary: Legend tags of a modular display tree (from its constant subtrees).
    Parameters: node — tree.
    Options/defaults: None.
    Returns: Tags of scalarTreeDependencyTags.
    Effects: Pure.
    Failures: None.
    Example: a tree with a numerical constant needs "NumericalLegend".
    See also: scalarTreeDependencyTags.
*)
modularTreeDependencyTags[node_] := DeleteDuplicates[Flatten[Map[scalarTreeDependencyTags, Cases[{node}, a_Association /; Lookup[a, "node", None] === "scalar" :> a["tree"], Infinity]]]];

(* -------------------------------------------------------------------------
   Node builders
   ------------------------------------------------------------------------- *)

(*
    Summary: The display labels of the normalization parameters of a definition.
    Parameters: parameters — definition parameter records (ID, Label); ids — further parameter IDs without records.
    Options/defaults: None.
    Returns: <|ID -> label node|>: the declared spelling, or c_n from the ID's last segment.
    Effects: Pure.
    Failures: None.
    Example: parameterLabelNodes[{<|"ID" -> "family-1:c[2]", "Label" -> "c[2]"|>}, {}] maps the ID to the text "c[2]".
    Remarks: Labels may repeat across families; the ModularFormView parameter table lists every full ID.
    See also: modularExpressionNode.
*)
parameterLabelNodes[parameters_List, ids_List] := Join[
    AssociationMap[textNode["c" <> "_" <> Last[StringSplit[#, ":"]]] &, ids],
    AssociationThread[Lookup[parameters, "ID", {}], textNode /@ Lookup[parameters, "Label", {}]]];

(*
    Summary: The ModularExpression node of definition components.
    Parameters: components — list of definition expressions (the true vector, transforms applied); parameters —
        <|ID -> label node|>; coordinate — "q" or "tau".
    Options/defaults: None.
    Returns: <|"Kind" -> "ModularExpression", "Components" -> trees, "Parameters" -> labels, "Coordinate"|>.
    Effects: Pure.
    Failures: None.
    Example: modularExpressionNode[{1}, <||>, "q"]["Components"] is {<|"node" -> "scalar", ...|>}.
    See also: modularDisplayTree; snapshotFormDisplay.
*)
modularExpressionNode[components_List, parameters_Association, coordinate_String] := <|"Kind" -> "ModularExpression",
    "Components" -> Map[modularDisplayTree, components], "Parameters" -> KeyTake[parameters, DeleteDuplicates[Cases[components, FormParameter[id_String] :> id, {0, Infinity}]]],
    "Coordinate" -> coordinate|>;

(*
    Summary: Whether a series coefficient is established nonzero.
    Parameters: c — coefficient (exact, numerical, or polynomial in FormParameter atoms).
    Options/defaults: None.
    Returns: Boolean.
    Effects: Pure.
    Failures: None.
    Example: establishedNonzeroQ[FormParameter["f:c"]] is False; establishedNonzeroQ[2.0] is True.
    Remarks: An exact number is nonzero when it is not zero (jets store no exact zeros); a numerical one when its
        magnitude exceeds its own accuracy; an expression with unresolved parameters never is.
    See also: qSeriesComponent.
*)
establishedNonzeroQ[c_] := Which[
    !FreeQ[c, _FormParameter], False,
    !NumericQ[c], False,
    Precision[c] === Infinity, !TrueQ[PossibleZeroQ[c]],
    True, With[{a = Accuracy[c]}, Abs[c] > 0 && (a === Infinity || Log10[Abs[c]] > -a)]];

(*
    Summary: The display data of one series component.
    Parameters: terms — <|exponent -> coefficient|> (known nonzero terms); cutoff — rational or Infinity; maximum —
        MaxQTerms (positive integer or All); factor — FactorQSeries.
    Options/defaults: None.
    Returns: <|"Terms" -> {{exponent, tree}...}, "Cutoff", "Omitted" -> hidden known terms, "Factor" -> None |
        <|"Exponent" -> r, "Coefficient" -> tree | None|>|>.
    Effects: Pure.
    Failures: None.
    Example: qSeriesComponent[<|1/3 -> 2, 4/3 -> 4|>, 2, 6, True]["Factor"]["Exponent"] is 1/3.
    Remarks: Terms are in exponent order. Factoring (D-S9-7) pulls out q^r of the first known term when its coefficient
        is established nonzero, and also that coefficient c when it is not 1 and every shown coefficient is rational or
        every one numerical (the inner coefficients are then c_i/c, a display computation); inner exponents are
        e - r and the remainder is written O(q^(n - r)) inside, so the cutoff keeps its meaning. Otherwise the series is
        shown unfactored. A hidden known term is never dropped silently ("Omitted").
    See also: qSeriesNode.
*)
qSeriesComponent[terms_Association, cutoff_, maximum_, factor_] := Module[{sorted = KeySort[terms], shown, omitted, lead, c0, pull, r},
    shown = If[maximum === All, Normal[sorted], Take[Normal[sorted], UpTo[maximum]]];
    omitted = Length[sorted] - Length[shown];
    If[!TrueQ[factor] || shown === {} || !establishedNonzeroQ[shown[[1, 2]]],
        Return[<|"Terms" -> Map[{First[#], modularDisplayTree[Last[#]]} &, shown], "Cutoff" -> cutoff, "Omitted" -> omitted, "Factor" -> None|>]];
    {r, c0} = List @@ First[shown];
    pull = c0 =!= 1 && (AllTrue[Values[shown], MatchQ[#, _Integer | _Rational] &] || AllTrue[Values[shown], NumericQ[#] && Precision[#] =!= Infinity &]);
    If[r === 0 && !pull, Return[<|"Terms" -> Map[{First[#], modularDisplayTree[Last[#]]} &, shown], "Cutoff" -> cutoff, "Omitted" -> omitted, "Factor" -> None|>]];
    lead = If[pull, c0, 1];
    <|"Terms" -> Map[{First[#] - r, modularDisplayTree[If[pull, Last[#]/lead, Last[#]]]} &, shown], "Cutoff" -> cutoff, "Omitted" -> omitted,
        "Factor" -> <|"Exponent" -> r, "Coefficient" -> If[pull, modularDisplayTree[lead], None]|>|>
];

(*
    Summary: The QSeries node of validated QExpansionData.
    Parameters: data — validated QExpansionData association; parameters — <|ID -> label node|> for raw coefficients;
        maximum — MaxQTerms; factor — FactorQSeries.
    Options/defaults: None.
    Returns: <|"Kind" -> "QSeries", "Components" -> qSeriesComponent results, "Parameters", "Binding", "Arithmetic",
        "Precision"|>.
    Effects: Pure: reads only the stored data (no q-expansion is computed).
    Failures: None.
    Example: qSeriesNode[e4data, <||>, 6, True]["Components"][[1, "Cutoff"]] is the stored cutoff.
    See also: qSeriesComponent; QExpansionView.
*)
qSeriesNode[data_Association, parameters_Association, maximum_, factor_] := With[{ids = DeleteDuplicates[Cases[data["Components"], FormParameter[id_String] :> id, {0, Infinity}]]},
    <|"Kind" -> "QSeries", "Components" -> MapThread[qSeriesComponent[#1, #2, maximum, factor] &, {data["Components"], data["ComponentCutoffs"]}],
        "Parameters" -> Join[parameterLabelNodes[{}, ids], KeyTake[parameters, ids]], "Binding" -> data["Binding"], "Arithmetic" -> data["Arithmetic"],
        "Precision" -> data["Precision"]|>];

(*
    Summary: The Normalization node of a form's coefficient record.
    Parameters: coefficients — the record's Coefficients (Missing or a normalization record); parameters — <|ID -> label|>.
    Options/defaults: None.
    Returns: <|"Kind" -> "Normalization", "Status" -> "NotNeeded" | "Resolved" | "Unresolved", "ProofStatus", "Rules" ->
        {<|"ID", "Label", "Value" -> tree|>...}, "Anchor" -> text or None|>.
    Effects: Pure.
    Failures: None.
    Example: a rank-1 form gives Status "NotNeeded".
    Remarks: Normalization unknowns are form data, never physical couplings; their values are shown with the proof
        status they were stored with.
    See also: snapshotFormDisplay.
*)
normalizationNode[coefficients_, parameters_Association] := Which[
    !AssociationQ[coefficients], <|"Kind" -> "Normalization", "Status" -> "Unresolved", "ProofStatus" -> "None", "Rules" -> {}, "Anchor" -> None|>,
    coefficients["Kind"] === "NoNormalizationNeeded" || coefficients["Rules"] === {},
        <|"Kind" -> "Normalization", "Status" -> "NotNeeded", "ProofStatus" -> ToString[coefficients["ProofStatus"]], "Rules" -> {}, "Anchor" -> anchorText[coefficients]|>,
    !ListQ[coefficients["Rules"]], <|"Kind" -> "Normalization", "Status" -> "Unresolved", "ProofStatus" -> ToString[coefficients["ProofStatus"]], "Rules" -> {},
        "Anchor" -> anchorText[coefficients]|>,
    True, <|"Kind" -> "Normalization", "Status" -> "Resolved", "ProofStatus" -> ToString[coefficients["ProofStatus"]],
        "Rules" -> Map[<|"ID" -> First[#], "Label" -> Lookup[parameters, First[#], textNode[First[#]]], "Value" -> modularDisplayTree[Last[#]]|> &, coefficients["Rules"]],
        "Anchor" -> anchorText[coefficients]|>];
anchorText[c_Association] := If[c["Kind"] === "Anchor",
    "component " <> ToString[c["Component"]] <> " of " <> ToString[Lookup[c, "AnchorSeed", c["SeedID"]]] <> " at q^" <> ToString[c["Exponent"], InputForm] <>
        " equals " <> ToString[c["Value"], InputForm] <> " in frame " <> ToString[c["AnchorFrameID"]], None];

(*
    Summary: The Evidence node of a record's validation data.
    Parameters: status — status text; items — list of {label, text} pairs.
    Options/defaults: None.
    Returns: <|"Kind" -> "Evidence", "Status" -> status, "Items" -> items|>.
    Effects: Pure.
    Failures: None.
    Example: evidenceNode["Unverified", {}]["Status"] is "Unverified".
    Remarks: Evidence is reported as stored; a display certifies nothing (ValidateModularForm checks).
    See also: formEvidenceNode.
*)
evidenceNode[status_String, items_List] := <|"Kind" -> "Evidence", "Status" -> status, "Items" -> items|>;

(*
    Summary: The FormLabel node of a form or slot: Y^(k) with the actual irrep label and an optional Roman copy index.
    Parameters: weight — actual weight k; irrep — irrep label node; copy — positive integer or None.
    Options/defaults: None.
    Returns: <|"Kind" -> "FormLabel", "Symbol" -> "Y", "Weight", "Irrep", "Copy"|>.
    Effects: Pure.
    Failures: None.
    Example: formLabelNode[2, irrep, 2] renders as Y^{(2)}_{3 II}.
    Remarks: The label comes from the record's own weight and representation (v1 ModelBuildingKit's Y labels), never
        from a symbol name; the copy suffix is shown when the stored space dimension exceeds one (or is unknown).
    See also: slotLabelNode; formComponentNode.
*)
formLabelNode[weight_?modularWeightQ, irrep_Association, copy_] := <|"Kind" -> "FormLabel", "Symbol" -> "Y", "Weight" -> weight, "Irrep" -> irrep, "Copy" -> copy|>;

(*
    Summary: The FormComponent node of component i of a slot.
    Parameters: slot — slot ID; i — component index; label — the slot's label node (FormLabel, Text or RawTeX).
    Options/defaults: None.
    Returns: <|"Kind" -> "FormComponent", "SlotID", "Index", "Label"|>.
    Effects: Pure.
    Failures: None.
    Example: formComponentNode["slot:1", 2, label]["Index"] is 2.
    See also: formLabelNode.
*)
formComponentNode[slot_String, i_Integer, label_Association] := <|"Kind" -> "FormComponent", "SlotID" -> slot, "Index" -> i, "Label" -> label|>;

(* -------------------------------------------------------------------------
   Renderers
   ------------------------------------------------------------------------- *)

(*
    Summary: LaTeX and notebook renderings of a form label, optionally with a component index.
    Parameters: node — FormLabel, Text or RawTeX node; index — component index or None; settings.
    Options/defaults: None.
    Returns: texFormLabel: string; notebookFormLabel: display expression.
    Effects: Pure.
    Failures: None.
    Example: texFormLabel[formLabelNode[2, irrep3, None], 1, s] is "Y^{(2)}_{\mathbf{3},1}" for an irrep labelled 3.
    See also: formLabelNode.
*)
texFormLabel[node_Association, index_, settings_Association] := If[node["Kind"] === "FormLabel",
    node["Symbol"] <> "^{(" <> texRational[node["Weight"]] <> ")}_{" <> renderTeXNode[node["Irrep"], settings] <>
        If[IntegerQ[node["Copy"]], "\\mathrm{" <> RomanNumeral[node["Copy"]] <> "}", ""] <> If[IntegerQ[index], "," <> ToString[index], ""] <> "}",
    With[{t = renderTeXNode[node, settings]}, If[IntegerQ[index], "{" <> t <> "}_{" <> ToString[index] <> "}", t]]];
notebookFormLabel[node_Association, index_, settings_Association] := If[node["Kind"] === "FormLabel",
    Subsuperscript[node["Symbol"], Row[Join[{renderNotebookCell[node["Irrep"], settings]}, If[IntegerQ[node["Copy"]], {RomanNumeral[node["Copy"]]}, {}],
        If[IntegerQ[index], {",", index}, {}]]], Row[{"(", node["Weight"], ")"}]],
    With[{n = renderNotebookCell[node, settings]}, If[IntegerQ[index], Subscript[n, index], n]]];

(*
    Summary: LaTeX and notebook renderings of a ModularExpression node (a column for several components).
    Parameters: node; settings.
    Options/defaults: None.
    Returns: String; display expression.
    Effects: Pure.
    Failures: None.
    Example: a three-component expression renders as a pmatrix.
    See also: texModularTree.
*)
texModularExpression[node_Association, settings_Association] := With[{parts = Map[texModularTree[#, node["Parameters"], settings]["TeX"] &, node["Components"]]},
    If[Length[parts] === 1, First[parts], "\\begin{pmatrix}" <> StringRiffle[parts, "\\\\"] <> "\\end{pmatrix}"]];
notebookModularExpression[node_Association, settings_Association] := With[{parts = Map[notebookModularTree[#, node["Parameters"], settings] &, node["Components"]]},
    If[Length[parts] === 1, First[parts], MatrixForm[List /@ parts]]];

(*
    Summary: LaTeX and notebook renderings of one series term c q^e.
    Parameters: e — exponent; tree — coefficient tree; parameters; settings.
    Options/defaults: None.
    Returns: String; display expression.
    Effects: Pure.
    Failures: None.
    Example: texQTerm[1/3, modularDisplayTree[-2], <||>, s] is "-2 q^{\frac{1}{3}}".
    See also: texQSeriesComponent.
*)
texQPower[e_] := Which[e === 0, "", e === 1, "q", True, "q^{" <> texRational[e] <> "}"];
texQTerm[e_, tree_Association, parameters_Association, settings_Association] := Module[{c = texModularTree[tree, parameters, settings], power = texQPower[e]},
    Which[
        power === "", c["TeX"],
        modularConstantQ[tree] && modularConstantValue[tree] === 1, power,
        modularConstantQ[tree] && modularConstantValue[tree] === -1, "-" <> power,
        c["Precedence"] < 2 && !(c["Precedence"] === 1 && StringStartsQ[c["TeX"], "-"] && !StringContainsQ[StringDrop[c["TeX"], 1], "+" | "-"]),
            "\\left(" <> c["TeX"] <> "\\right) " <> power,
        True, c["TeX"] <> " " <> power]];
notebookQTerm[e_, tree_Association, parameters_Association, settings_Association] := Module[{c = notebookModularTree[tree, parameters, settings], power},
    power = Which[e === 0, None, e === 1, Style["q", Italic], True, Superscript[Style["q", Italic], e]];
    Which[power === None, c, modularConstantQ[tree] && modularConstantValue[tree] === 1, power,
        MemberQ[{"plus"}, tree["node"]], Row[{"(", c, ")", " ", power}], True, Row[{c, " ", power}]]];

(*
    Summary: LaTeX and notebook renderings of one QSeries component.
    Parameters: component — qSeriesComponent data; parameters; settings.
    Options/defaults: None.
    Returns: String; display expression.
    Effects: Pure.
    Failures: None.
    Example: an empty component with cutoff 3 renders as "O\left(q^{3}\right)"; with cutoff Infinity as "0".
    Remarks: Hidden known terms show "\cdots" before the remainder; an exact finite component (cutoff Infinity) has no
        remainder; in factored form the remainder is written inside with the shifted order n - r.
    See also: qSeriesComponent.
*)
texQSeriesComponent[component_Association, parameters_Association, settings_Association] := Module[{factor = component["Factor"], shift, terms, body, remainder},
    shift = If[factor === None, 0, factor["Exponent"]];
    terms = Map[texQTerm[#[[1]], #[[2]], parameters, settings] &, component["Terms"]];
    remainder = If[component["Cutoff"] === Infinity, {}, {"O\\left(q^{" <> texRational[component["Cutoff"] - shift] <> "}\\right)"}];
    body = Join[terms, If[component["Omitted"] > 0, {"\\cdots"}, {}], remainder];
    body = If[body === {}, "0", StringJoin[MapIndexed[If[First[#2] === 1 || StringStartsQ[#1, "-"], #1, "+" <> #1] &, body]]];
    If[factor === None, body,
        StringJoin[If[factor["Coefficient"] === None, "", With[{c = texModularTree[factor["Coefficient"], parameters, settings]},
                If[c["Precedence"] < 2 && !(StringStartsQ[c["TeX"], "-"] && !StringContainsQ[StringDrop[c["TeX"], 1], "+" | "-"]),
                    "\\left(" <> c["TeX"] <> "\\right)", c["TeX"]] <> " "]],
            texQPower[factor["Exponent"]], "\\left(", body, "\\right)"]]
];
notebookQSeriesComponent[component_Association, parameters_Association, settings_Association] := Module[{factor = component["Factor"], shift, items},
    shift = If[factor === None, 0, factor["Exponent"]];
    items = Join[Map[notebookQTerm[#[[1]], #[[2]], parameters, settings] &, component["Terms"]], If[component["Omitted"] > 0, {"\[CenterEllipsis]"}, {}],
        If[component["Cutoff"] === Infinity, {}, {Row[{"O(", Superscript[Style["q", Italic], component["Cutoff"] - shift], ")"}]}]];
    items = If[items === {}, {0}, items];
    If[factor === None, Row[Riffle[items, " + "]],
        Row[Join[If[factor["Coefficient"] === None, {}, {notebookModularTree[factor["Coefficient"], parameters, settings], " "}],
            If[factor["Exponent"] === 0, {}, {Superscript[Style["q", Italic], factor["Exponent"]]}], {"(", Row[Riffle[items, " + "]], ")"}]]]
];

(*
    Summary: Text of Normalization and Evidence nodes (shared by both renderers).
    Parameters: node; settings.
    Options/defaults: None.
    Returns: texNormalization/texEvidence: LaTeX; notebookNormalization/notebookEvidence: display expressions.
    Effects: Pure.
    Failures: None.
    Example: a resolved normalization renders its rules c = value and its proof status.
    See also: normalizationNode; evidenceNode.
*)
texNormalization[node_Association, settings_Association] := StringJoin[
    "\\text{" <> escapeTeXText[Switch[node["Status"], "NotNeeded", "none needed", "Resolved", "resolved", _, "unresolved"] <>
        " (" <> node["ProofStatus"] <> ")"] <> "}",
    Map[", " <> renderTeXNode[#["Label"], settings] <> " = " <> texModularTree[#["Value"], <||>, settings]["TeX"] &, node["Rules"]]];
notebookNormalization[node_Association, settings_Association] := Row[Join[
    {Switch[node["Status"], "NotNeeded", "none needed", "Resolved", "resolved", _, "unresolved"] <> " (" <> node["ProofStatus"] <> ")"},
    Flatten[Map[{", ", renderNotebookCell[#["Label"], settings], " = ", notebookModularTree[#["Value"], <||>, settings]} &, node["Rules"]]]]];
texEvidence[node_Association, settings_Association] := "\\text{" <> escapeTeXText[node["Status"] <>
    StringJoin[Map["; " <> #[[1]] <> ": " <> #[[2]] &, node["Items"]]]] <> "}";
notebookEvidence[node_Association, settings_Association] := Row[{node["Status"], StringJoin[Map["; " <> #[[1]] <> ": " <> #[[2]] &, node["Items"]]]}];

(* -------------------------------------------------------------------------
   Registration
   ------------------------------------------------------------------------- *)

(*
    Summary: Validators of the modular nodes.
    Parameters: node.
    Options/defaults: None.
    Returns: Boolean.
    Effects: Pure.
    Failures: None.
    Example: validQSeriesComponentQ[<|"Terms" -> {}, "Cutoff" -> 3, "Omitted" -> 0, "Factor" -> None|>, {}] is True.
    See also: registerDisplayNode.
*)
labelNodeQ[node_] := AssociationQ[node] && MemberQ[{"Text", "RawTeX", "FormLabel"}, Lookup[node, "Kind", None]] && displayNodeQ[node];
parameterLabelsQ[p_] := AssociationQ[p] && AllTrue[Keys[p], StringQ] && AllTrue[Values[p], displayNodeQ];
validQSeriesComponentQ[c_, parameters_List] := AssociationQ[c] && Sort[Keys[c]] === {"Cutoff", "Factor", "Omitted", "Terms"} &&
    (c["Cutoff"] === Infinity || MatchQ[c["Cutoff"], _Integer | _Rational]) && IntegerQ[c["Omitted"]] && c["Omitted"] >= 0 &&
    ListQ[c["Terms"]] && AllTrue[c["Terms"], MatchQ[#, {_Integer | _Rational, _Association}] && validModularTreeQ[#[[2]], parameters] &] &&
    OrderedQ[c["Terms"][[All, 1]]] &&
    (c["Factor"] === None || (AssociationQ[c["Factor"]] && Sort[Keys[c["Factor"]]] === {"Coefficient", "Exponent"} &&
        MatchQ[c["Factor"]["Exponent"], _Integer | _Rational] && (c["Factor"]["Coefficient"] === None || validModularTreeQ[c["Factor"]["Coefficient"], parameters]))) &&
    (c["Cutoff"] === Infinity || AllTrue[c["Terms"][[All, 1]], # + If[c["Factor"] === None, 0, c["Factor"]["Exponent"]] < c["Cutoff"] &]);

registerDisplayNode["FormLabel", <|"Validate" -> (StringQ[Lookup[#, "Symbol", None]] && modularWeightQ[Lookup[#, "Weight", None]] && displayNodeQ[Lookup[#, "Irrep", None]] &&
        (#["Copy"] === None || (IntegerQ[#["Copy"]] && #["Copy"] >= 1)) &),
    "Notebook" -> (notebookFormLabel[#1, None, #2] &), "TeX" -> (texFormLabel[#1, None, #2] &), "Dependencies" -> (texDependencies[#["Irrep"]] &)|>];
registerDisplayNode["FormComponent", <|"Validate" -> (StringQ[Lookup[#, "SlotID", None]] && IntegerQ[Lookup[#, "Index", None]] && #["Index"] >= 1 &&
        labelNodeQ[Lookup[#, "Label", None]] &),
    "Notebook" -> (notebookFormLabel[#1["Label"], #1["Index"], #2] &), "TeX" -> (texFormLabel[#1["Label"], #1["Index"], #2] &),
    "Dependencies" -> (texDependencies[#["Label"]] &)|>];
registerDisplayNode["ModularExpression", <|"Validate" -> (parameterLabelsQ[Lookup[#, "Parameters", None]] && MemberQ[{"q", "tau"}, Lookup[#, "Coordinate", None]] &&
        ListQ[Lookup[#, "Components", None]] && #["Components"] =!= {} && AllTrue[#["Components"], Function[t, validModularTreeQ[t, Keys[#["Parameters"]]]]] &),
    "Notebook" -> notebookModularExpression, "TeX" -> texModularExpression,
    "Dependencies" -> (DeleteDuplicates[Flatten[modularTreeDependencyTags /@ #["Components"]]] &)|>];
registerDisplayNode["QSeries", <|"Validate" -> (parameterLabelsQ[Lookup[#, "Parameters", None]] && ListQ[Lookup[#, "Components", None]] && #["Components"] =!= {} &&
        AllTrue[#["Components"], Function[c, validQSeriesComponentQ[c, Keys[#["Parameters"]]]]] && MemberQ[{"Exact", "Numerical"}, Lookup[#, "Arithmetic", None]] &&
        StringQ[Lookup[#, "Binding", None]] &),
    "Notebook" -> (If[Length[#1["Components"]] === 1, notebookQSeriesComponent[First[#1["Components"]], #1["Parameters"], #2],
        MatrixForm[List /@ Map[Function[c, notebookQSeriesComponent[c, #1["Parameters"], #2]], #1["Components"]]]] &),
    "TeX" -> (If[Length[#1["Components"]] === 1, texQSeriesComponent[First[#1["Components"]], #1["Parameters"], #2],
        "\\begin{pmatrix}" <> StringRiffle[Map[Function[c, texQSeriesComponent[c, #1["Parameters"], #2]], #1["Components"]], "\\\\"] <> "\\end{pmatrix}"] &),
    "Dependencies" -> (Join[DeleteDuplicates[Flatten[modularTreeDependencyTags /@ Cases[#["Components"], a_Association /; KeyExistsQ[a, "node"], Infinity]]],
        If[#["Arithmetic"] === "Numerical", {"NumericalLegend"}, {}]] &)|>];
registerDisplayNode["Normalization", <|"Validate" -> (MemberQ[{"NotNeeded", "Resolved", "Unresolved"}, Lookup[#, "Status", None]] && StringQ[Lookup[#, "ProofStatus", None]] &&
        ListQ[Lookup[#, "Rules", None]] && AllTrue[#["Rules"], AssociationQ[#] && StringQ[Lookup[#, "ID", None]] && displayNodeQ[Lookup[#, "Label", None]] &&
            validModularTreeQ[Lookup[#, "Value", None], {}] &] && (#["Anchor"] === None || StringQ[#["Anchor"]]) &),
    "Notebook" -> notebookNormalization, "TeX" -> texNormalization,
    "Dependencies" -> (DeleteDuplicates[Flatten[modularTreeDependencyTags /@ Lookup[#["Rules"], "Value", {}]]] &)|>];
registerDisplayNode["Evidence", <|"Validate" -> (StringQ[Lookup[#, "Status", None]] && ListQ[Lookup[#, "Items", None]] &&
        AllTrue[#["Items"], MatchQ[#, {_String, _String}] &] &),
    "Notebook" -> notebookEvidence, "TeX" -> texEvidence, "Dependencies" -> ({} &)|>];

True
