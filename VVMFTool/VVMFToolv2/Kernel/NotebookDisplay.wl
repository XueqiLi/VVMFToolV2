(*
    :Title: Notebook rendering of display documents
    :Context: VVMFTool`Private`
    :Summary: Notebook expressions for display nodes and documents: interactive paged views when a front end is
        present, complete static views otherwise, and self-contained static notebooks for export.
    :Responsibilities:
        - renderNotebookCell (registry dispatch), notebook node renderers, paginateDisplay,
          renderNotebookDocument, renderStaticNotebook, ToNotebook.
        - No Dynamic, callback, live group handle or cache reference in exported notebooks; raw TeX is shown as
          literal source, never evaluated.
    :Dependencies: DisplayData.wl; DisplayNotation.wl; LaTeXDisplay.wl (shared legends and summary lines).
    :See Also: VVMFArch/step3Plan.md (notebook contracts).
*)

(*
    Summary: Render one display node to a notebook expression.
    Parameters: node — registered display node; settings — render settings.
    Options/defaults: None.
    Returns: A display expression (strings, Row, Subscript, a matrix as a DisplayForm box row with stretching parentheses
        around its Grid, HoldForm), or Failure.
    Effects: Pure.
    Failures: InvalidDisplayNode.
    Example: renderNotebookCell[textNode["a"], settings] is "a".
    See also: registerDisplayNode; renderTeXNode.
*)
renderNotebookCell[node_Association, settings_Association] := If[displayNodeQ[node],
    $DisplayNodeRegistry[node["Kind"]]["Notebook"][node, settings],
    makeFailure["InvalidDisplayNode", "The display node is not registered or malformed.", <|"Kind" -> Lookup[node, "Kind", None]|>]];
renderNotebookCell[_, _] := makeFailure["InvalidDisplayNode", "Expected a display node."];

(*
    Summary: Notebook handlers of the Text, RawTeX (literal source), Scalar, Phase, Matrix and IrrepLabel nodes.
    Parameters: node — display node; settings (ScalarNotation, Digits, OneByOneMatrix).
    Options/defaults: None.
    Returns: A display expression (strings, Row, Subscript, Grid, HoldForm).
    Effects: Pure.
    Failures: None.
    Example: notebookPhaseNode[phaseDisplayNode[Exp[2 Pi I/3]], <|ScalarNotation -> "Omega"|>] is Subscript["\\[Omega]", 3].
    See also: renderNotebookCell.
*)
notebookTextNode[node_, settings_] := node["Text"];
(* Raw TeX is shown as its literal source (Program style), never parsed or evaluated. *)
notebookRawTeXNode[node_, settings_] := Style[node["Fallback"], "Program"];
notebookScalarNode[node_, settings_] := Switch[node["Form"],
    "Rational", node["Value"],
    "Radical", HoldForm @@ {node["Expression"]},
    "Cyclotomic", Row[MapIndexed[Function[{term, position}, With[{c = term[[1]], k = Numerator[term[[2]]], n = Denominator[term[[2]]]},
        Row[{If[First[position] === 1, If[c < 0, "-", ""], If[c < 0, " - ", " + "]], If[Abs[c] === 1 && term[[2]] =!= 0, "", Abs[c]],
            If[term[[2]] === 0, "", If[Lookup[settings, ScalarNotation, "Standard"] === "Omega",
                If[k === 1, Subscript["\[Omega]", n], Superscript[Subscript["\[Omega]", n], k]],
                Superscript["\[ExponentialE]", Row[{2, "\[Pi]", "\[ImaginaryI]", If[k === 1, Nothing, k], "/", n}]]]]}]]],
        node["Terms"]]],
    "Numerical", With[{digits = Lookup[settings, Digits, Automatic], available = Max[1, Floor[Replace[
            Min[Precision[Re[node["Value"]]], Precision[Im[node["Value"]]]], {MachinePrecision -> 16, Infinity -> 16}]]]},
        If[IntegerQ[digits], NumberForm[node["Value"], Min[digits, available]], node["Value"]]],
    "Root", Row[{"Root(", Row[Reverse[DeleteCases[MapIndexed[If[#1 === 0, Nothing, Row[{#1, If[First[#2] > 1, Superscript["x", First[#2] - 1], ""]}]] &,
        node["Polynomial"]], Nothing]], " + "], ", ", node["Index"], ")"}]];
notebookPhaseNode[node_, settings_] := Module[{k = Numerator[node["Phase"]], n = Denominator[node["Phase"]], m = node["Magnitude"], body},
    body = Switch[Lookup[settings, ScalarNotation, "Standard"],
        "Omega", If[k === 1, Subscript["\[Omega]", n], Superscript[Subscript["\[Omega]", n], k]],
        "Exponential", Superscript["\[ExponentialE]", Row[{2, "\[Pi]", "\[ImaginaryI]", If[k === 1, Nothing, k], "/", n}]],
        _, With[{radical = displayRadical[node["Value"]]}, If[radical =!= $Failed, Return[HoldForm @@ {radical}, Module],
            Superscript["\[ExponentialE]", Row[{2, "\[Pi]", "\[ImaginaryI]", If[k === 1, Nothing, k], "/", n}]]]]];
    (* the radical form above is of the whole value, magnitude included *)
    If[m === 1, body, Row[{m, body}]]
];
notebookMatrixNode[node_, settings_] := If[node["Dimensions"] === {1, 1} && Lookup[settings, OneByOneMatrix, "Scalar"] === "Scalar",
    renderNotebookCell[node["Cells"][[1, 1]], settings],
    (* one box row of "(", the grid and ")", as MatrixForm writes it, so the front end stretches the parentheses to the
       matrix height (a Row keeps them at text size) *)
    DisplayForm[RowBox[{"(", "\[NoBreak]", ToBoxes[Grid[Map[renderNotebookCell[#, settings] &, node["Cells"], {2}], Spacings -> {1, 0.5}]],
        "\[NoBreak]", ")"}]]];
notebookIrrepLabelNode[node_, settings_] := If[node["Phases"] === None, Style[node["Dimension"], Bold],
    Subscript[Style[node["Dimension"], Bold], Row[{"(", Row[node["Phases"], ","], ")"}]]];

(*
    Summary: Split rows into pages.
    Parameters: rows — list; size — positive integer or All.
    Options/defaults: None.
    Returns: List of pages covering every row once, in order.
    Effects: Pure.
    Failures: None.
    Example: paginateDisplay[Range[45], 20] has three pages.
    See also: renderNotebookDocument.
*)
paginateDisplay[rows_List, All] := {rows};
paginateDisplay[rows_List, size_Integer?Positive] := If[rows === {}, {{}}, Partition[rows, UpTo[size]]];

(*
    Summary: The header row and body rows of a document as notebook expressions.
    Parameters: data — validated document data; settings.
    Options/defaults: None.
    Returns: <|"Header" -> list, "Rows" -> list of lists, "Legend" -> list of strings|>, or Failure.
    Effects: Pure.
    Failures: Cell rendering failures.
    Example: notebookTableParts[DisplayData[CharacterTableView[g]], settings]["Header"][[1]] is "ID".
    See also: renderNotebookDocument; renderStaticNotebook.
*)
notebookTableParts[data_Association, settings_Association] := Module[{cell, header, rows, legend},
    cell[node_] := If[StringQ[node], node, renderNotebookCell[node, settings]];
    If[KeyExistsQ[$DisplayKindRegistry, data["Kind"]], Return[registeredNotebookParts[data, settings]]];
    {header, rows} = Switch[data["Kind"],
        "CharacterTable", {Join[irrepNameHeader[data], MapThread[Column[{If[#4 === None, #1, cell[#4]], Style["size " <> ToString[#2], Gray], Style["order " <> ToString[#3], Gray]}] &,
                {data["ClassWords"], data["ClassSizes"], data["ClassOrders"], Lookup[data, "ClassNames", ConstantArray[None, Length[data["ClassIDs"]]]]}]],
            (* Values go through scalar nodes, so ScalarNotation and Digits apply as in LaTeX. *)
            MapThread[Join[irrepNameCells[data, #1, cell], cell[scalarDisplayNode[#]] & /@ #2] &, {data["IrrepIDs"], data["Values"]}]},
        "RepresentationTable", {Join[irrepNameHeader[data], {"Dim."}, If[displayColumn[data, "Status"], {"Status", "Basis"}, {}],
                matrixColumnText /@ data["MatrixSet"]["Columns"]],
            Map[Join[irrepNameCells[data, #["IrrepID"], cell], {#["Dimension"]},
                If[displayColumn[data, "Status"], {statusBadge[#], Style[rowBasisText[#], Small]}, {}],
                If[ListQ[#["Matrices"]], expandableMatrix[cell[matrixDisplayNode[#]], Length[#], settings] & /@ #["Matrices"],
                    ConstantArray["\[LongDash]", Length[data["MatrixSet"]["Columns"]]]]] &,
                data["Rows"]]},
        "Representation", {Join[{"Label", "Dim."}, If[displayColumn[data, "Status"], {"Validation"}, {}], matrixColumnText /@ data["MatrixSet"]["Columns"]],
            {Join[{cell[representationViewLabel[data]], data["Dimension"]}, If[displayColumn[data, "Status"], {validationText[data]}, {}],
                cell[matrixDisplayNode[#]] & /@ data["Matrices"]]}},
        "GroupSummary", {{"Field", "Value"}, groupSummaryLines[data]},
        "TensorDecomposition", {{"Product", "Dim.", "Decomposition"},
            Map[{If[#["Factors"] === {}, "1", Row[Riffle[cell[data["Labels"][#]] & /@ #["Factors"], " \[CircleTimes] "]]], #["Dimension"],
                Row[Riffle[Map[Function[c, If[c["Multiplicity"] > 1, Row[{c["Multiplicity"], "\[CenterDot]", cell[data["Labels"][c["IrrepID"]]]}],
                    cell[data["Labels"][c["IrrepID"]]]]], #["Constituents"]], " \[CirclePlus] "]]} &, data["Products"]]}];
    If[!FreeQ[{header, rows}, _Failure], Return[FirstCase[{header, rows}, _Failure, Null, Infinity]]];
    legend = Join[
        If[data["Kind"] === "RepresentationTable" && displayColumn[data, "Status"] && AnyTrue[data["Rows"], #["Status"] =!= "Complete" &], {"Rows without completed matrices show their status; accepted partial matrices are not shown as completed."}, {}],
        statusLegend[data], irrepNameLegend[data],
        If[Lookup[data, "Arithmetic", "Exact"] === "Numerical" || !FreeQ[rows, _NumberForm] ||
            AnyTrue[Lookup[data, "Rows", {}], Lookup[#, "Arithmetic", "Exact"] === "Numerical" &], {"Numerical entries are approximate."}, {}],
        If[Lookup[settings, ScalarNotation, "Standard"] === "Omega" && TrueQ[Lookup[settings, DefineOmega, True]] &&
            !FreeQ[rows, Subscript["\[Omega]", _] | Superscript[Subscript["\[Omega]", _], _]],
            {"\[Omega]_a^b \[Congruent] exp(2\[Pi]\[ImaginaryI] b/a)."}, {}]];
    <|"Header" -> header, "Rows" -> rows, "Legend" -> legend|>
];
(*
    Summary: The notebook sections of a document of a registered (later-stage) kind.
    Parameters: data — validated document data; settings.
    Options/defaults: None.
    Returns: <|"Header" -> the first section's header, "Rows" -> the first section's rows, "Sections" -> {<|"Title",
        "Header", "Rows"|>...} (cells rendered), "Legend" -> strings|>, or Failure.
    Effects: Pure.
    Failures: Cell rendering failures.
    Example: a ModelView gives three sections (fields, terms, parameters).
    See also: registerDisplayKind; renderNotebookDocument; renderStaticNotebook.
*)
registeredNotebookParts[data_Association, settings_Association] := Module[{parts, cell, sections, legend},
    parts = $DisplayKindRegistry[data["Kind"]]["Notebook"][data, settings];
    If[FailureQ[parts], Return[parts]];
    cell[node_] := If[StringQ[node] || !AssociationQ[node], node, renderNotebookCell[node, settings]];
    sections = Map[<|"Title" -> Lookup[#, "Title", None], "Header" -> (cell /@ #["Header"]), "Rows" -> Map[cell, #["Rows"], {2}]|> &, parts["Sections"]];
    If[!FreeQ[sections, _Failure], Return[FirstCase[sections, _Failure, Null, Infinity]]];
    legend = Join[Lookup[parts, "Legend", {}],
        If[!FreeQ[sections, _NumberForm], {"Numerical entries are approximate."}, {}],
        If[Lookup[settings, ScalarNotation, "Standard"] === "Omega" && TrueQ[Lookup[settings, DefineOmega, True]] &&
            !FreeQ[sections, Subscript["\[Omega]", _] | Superscript[Subscript["\[Omega]", _], _]], {"\[Omega]_a^b \[Congruent] exp(2\[Pi]\[ImaginaryI] b/a)."}, {}]];
    <|"Header" -> First[sections]["Header"], "Rows" -> First[sections]["Rows"], "Sections" -> sections, "Legend" -> legend|>
];

(*
    Summary: A matrix cell of an interactive view: large matrices collapse behind an opener; static views show all.
    Parameters: expr — rendered matrix; dimension — matrix size; settings (Interactive).
    Options/defaults: Matrices of dimension above 4 collapse when the view is interactive.
    Returns: The expression, or an OpenerView.
    Effects: Pure.
    Failures: None.
    Example: expandableMatrix[m, 6, <|"Interactive" -> True|>] is an OpenerView titled "6 x 6 matrix".
    See also: renderNotebookDocument.
*)
expandableMatrix[expr_, dimension_Integer, settings_] := If[TrueQ[Lookup[settings, "Interactive", False]] && dimension > 4,
    OpenerView[{ToString[dimension] <> " \[Times] " <> ToString[dimension] <> " matrix", expr}], expr];

(*
    Summary: Notebook forms of Row and Table nodes (the node registry's notebook handlers).
    Parameters: node — Row or Table node; settings.
    Options/defaults: None.
    Returns: A list of cell expressions (Row) or a framed Grid with a caption (Table).
    Effects: Pure.
    Failures: None for valid nodes.
    Example: notebookTableNode[node, settings] is a Column of the caption and the Grid.
    See also: renderNotebookCell; renderTeXTable.
*)
notebookRowNode[node_, settings_] := Map[If[StringQ[#], #, renderNotebookCell[#, settings]] &, Join[node["Fixed"], node["Cells"]]];
notebookTableNode[node_, settings_] := Column[{Style[node["Caption"], Italic],
    Grid[Prepend[notebookRowNode[#, settings] & /@ node["Rows"], Style[If[StringQ[#], #, renderNotebookCell[#, settings]], Bold] & /@
        Join[node["Fixed"], node["Columns"]]], Frame -> All, Alignment -> Left]}];

(*
    Summary: Notebook header of a matrix column and the status badge of a representation row.
    Parameters: column — matrix-set column; row — table row.
    Options/defaults: None.
    Returns: A display expression.
    Effects: Pure.
    Failures: None.
    Example: statusBadge[<|"Status" -> "Complete"|>] is a green Style.
    See also: notebookTableParts.
*)
matrixColumnText[column_Association] := Row[{"\[Rho](", column["Name"], ")", If[KeyExistsQ[column, "Word"] && column["Word"] =!= column["Name"], " = " <> column["Word"], ""]}];
statusBadge[row_Association] := Style[row["Status"], Switch[row["Status"], "Complete", Darker[Green], "Not computed", Gray, _, Orange]];

(*
    Summary: A notebook view of a document: paged Dynamic controls with a front end, complete static otherwise.
    Parameters: data — validated document data; settings — render settings (PageSize).
    Options/defaults: None.
    Returns: A display expression, or Failure.
    Effects: Pure; the Dynamic page index is local to the returned view (no package callbacks, no group handle).
    Failures: Cell rendering failures.
    Example: renderNotebookDocument[data, settings] in a headless kernel is a static Column.
    See also: ToNotebook; renderStaticNotebook.
*)
renderNotebookDocument[data_Association, settings_Association] := Module[{parts, caption, pages, grid},
    parts = notebookTableParts[data, settings]; If[FailureQ[parts], Return[parts]];
    caption = renderNotebookCell[data["Caption"], settings];
    (* Several sections (registered kinds): every section complete, each with its title. *)
    If[Length[Lookup[parts, "Sections", {}]] > 1, Return[Column[Join[{Style[caption, Italic]},
        Flatten[Map[{If[StringQ[#["Title"]], Style[#["Title"], Bold], Nothing], Grid[Prepend[#["Rows"], Style[#, Bold] & /@ #["Header"]], Frame -> All,
            Alignment -> Left, Spacings -> {1.2, 0.8}]} &, parts["Sections"]]], Style[#, Small] & /@ parts["Legend"]], Spacings -> 1]]];
    pages = paginateDisplay[parts["Rows"], Lookup[settings, PageSize, 20]];
    grid[rows_] := Grid[Prepend[rows, Style[#, Bold] & /@ parts["Header"]], Frame -> All, Alignment -> Left, Spacings -> {1.2, 0.8}];
    If[$FrontEnd =!= Null && Length[pages] > 1,
        parts = notebookTableParts[data, Join[settings, <|"Interactive" -> True|>]]; If[FailureQ[parts], Return[parts]];
        pages = paginateDisplay[parts["Rows"], Lookup[settings, PageSize, 20]]];
    If[$FrontEnd === Null || Length[pages] === 1,
        Column[Join[{Style[caption, Italic]}, grid /@ pages, Style[#, Small] & /@ parts["Legend"]], Spacings -> 1],
        DynamicModule[{page = 1}, Column[{Style[caption, Italic],
            Row[{Button["<", page = Max[1, page - 1]], " page ", Dynamic[page], " of ", Length[pages], " ", Button[">", page = Min[Length[pages], page + 1]]}],
            Dynamic[grid[pages[[page]]]], Sequence @@ (Style[#, Small] & /@ parts["Legend"])}, Spacings -> 1]]]
];

(*
    Summary: A complete, self-contained static notebook of a document.
    Parameters: data — validated document data; settings.
    Options/defaults: PageSize organizes static sections only; every row is serialized.
    Returns: Notebook[{cells}, ...] of explicit boxes, with the exported row count in its tagging rules, or Failure.
    Effects: Pure (box conversion only).
    Failures: Cell rendering failures.
    Example: renderStaticNotebook[data, settings] has no Dynamic and no VVMFTool` symbols.
    Remarks: The notebook displays in a fresh session without evaluating package code or starting a kernel.
    See also: ExportDisplay; renderNotebookDocument.
*)
renderStaticNotebook[data_Association, settings_Association] := Module[{parts, caption, pages, cells, rows, sections},
    parts = notebookTableParts[data, settings]; If[FailureQ[parts], Return[parts]];
    caption = renderNotebookCell[data["Caption"], settings];
    sections = Lookup[parts, "Sections", {<|"Title" -> None, "Header" -> parts["Header"], "Rows" -> parts["Rows"]|>}];
    rows = Total[Length[#["Rows"]] & /@ sections];
    (* Every section's rows are serialized, paged by PageSize; a titled section starts with its title. *)
    cells = Join[{Cell[ToString[caption], "Text"]},
        Flatten[Map[Function[section, With[{sectionPages = paginateDisplay[section["Rows"], Lookup[settings, PageSize, 20]],
                total = Length[section["Rows"]]},
            Join[If[StringQ[section["Title"]], {Cell[section["Title"], "Subsection"]}, {}],
                MapIndexed[Function[{page, index}, Cell[BoxData[ToBoxes[Grid[Prepend[page, Style[#, Bold] & /@ section["Header"]],
                        Frame -> All, Alignment -> Left, Spacings -> {1.2, 0.8}], StandardForm]], "Output",
                    CellLabel -> If[Length[sectionPages] > 1, "Rows " <> ToString[(First[index] - 1) Replace[Lookup[settings, PageSize, 20], All -> total] + 1] <>
                        "\[Dash]" <> ToString[(First[index] - 1) Replace[Lookup[settings, PageSize, 20], All -> total] + Length[page]], None]]], sectionPages]]]],
            sections]],
        Cell[#, "Text"] & /@ parts["Legend"],
        {Cell["Source " <> ToString[data["Source"]["StateID"]] <> ", generator identity " <> ToString[data["Source"]["GeneratorIdentity"]] <>
            ", observed " <> data["ObservedAt"] <> "; " <> ToString[rows] <> " rows.", "Text"]}];
    cells = cells /. HoldPattern[CellLabel -> None] :> Sequence[];
    Notebook[cells, TaggingRules -> <|"VVMFDisplay" -> <|"Kind" -> data["Kind"], "Rows" -> rows,
        "SchemaVersion" -> data["SchemaVersion"]|>|>]
];

Options[ToNotebook] = {ScalarNotation -> Automatic, NotationStyle -> Automatic, OneByOneMatrix -> Automatic, DefineOmega -> Automatic,
    Digits -> Automatic, Caption -> Automatic, PageSize -> Automatic};

(*
    Summary: A notebook view of a display document.
    Status: Alpha.
    Parameters: v — DisplayDocument.
    Options/defaults: ScalarNotation, NotationStyle, OneByOneMatrix, DefineOmega, Digits, Caption, PageSize ->
        Automatic (the document's saved presentation defaults; explicit values override them).
    Returns: A display expression: paged when a front end is present and the rows exceed PageSize, otherwise a
        complete static Column; or Failure.
    Effects: Pure; no GAP work, no group access.
    Failures: InvalidDisplayDocument; InvalidOption.
    Example: ToNotebook[CharacterTableView[g]] shows every row with sizes and orders.
    See also: ExportDisplay; ToLaTeX.
*)
ToNotebook[document_DisplayDocument, options : OptionsPattern[]] := Module[{data, settings},
    data = validateDisplayDocument[document]; If[FailureQ[data], Return[data]];
    settings = displayRenderSettings[ToNotebook, "ToNotebook", data, {options}]; If[FailureQ[settings], Return[settings]];
    renderNotebookDocument[If[settings[Caption] =!= Automatic,
        Join[data, <|"Caption" -> If[StringQ[settings[Caption]], textNode[settings[Caption]], labelNode[settings[Caption]]]|>], data], settings]
];
ToNotebook[___] := makeFailure["InvalidInput", "ToNotebook expects a DisplayDocument and options."];


(*
    Summary: The irrep columns of a table of representations: index, automatic label, user label, and the ID on request.
    Parameters: data — CharacterTable, RepresentationTable or Representation document data; id — irrep ID; cell — node renderer.
    Options/defaults: None.
    Returns: irrepNameHeader: header strings; irrepNameCells: the cells of one row; displayColumn: whether a column is shown;
        representationViewLabel: the label node of a single representation (user label, else automatic, else the old label).
    Effects: Pure.
    Failures: None.
    Example: a T' character table without user labels has the header {"Index", "Label (T phases)"}.
    Remarks: Documents made before the UX update (no IrrepNames) keep their ID and Label columns (uxUpdatePlan.md 2.2).
    See also: irrepPresentation; displayColumns.
*)
displayColumn[data_Association, key_String] := TrueQ[Lookup[Lookup[data, "Columns", <|"IDs" -> True, "Status" -> True, "Auto" -> True, "User" -> False|>], key, False]];
irrepNameHeader[data_Association] := If[!KeyExistsQ[data, "IrrepNames"], {"ID", "Label"},
    Join[{"Index"}, If[displayColumn[data, "Auto"], {"Label (T phases)"}, {}], If[displayColumn[data, "User"], {"Name"}, {}],
        If[displayColumn[data, "IDs"], {"ID"}, {}]]];
irrepNameCells[data_Association, id_String, cell_] := If[!KeyExistsQ[data, "IrrepNames"], {Style[id, "Program", Small], cell[data["Labels"][id]]},
    With[{n = data["IrrepNames"][id]}, Join[{n["Index"]}, If[displayColumn[data, "Auto"], {If[n["Auto"] === None, "", cell[n["Auto"]]]}, {}],
        If[displayColumn[data, "User"], {If[n["User"] === None, "", cell[n["User"]]]}, {}], If[displayColumn[data, "IDs"], {Style[id, "Program", Small]}, {}]]]];
representationViewLabel[data_Association] := With[{names = Lookup[data, "IrrepNames", <||>]},
    If[names =!= <||> && First[names]["User"] =!= None, First[names]["User"], data["Label"]]];

(*
    Summary: Legend lines that explain the status words and the label columns shown in a document.
    Parameters: data — document data.
    Options/defaults: None.
    Returns: List of strings, one per status value or label kind that occurs.
    Effects: Pure.
    Failures: None.
    Example: a RepresentationTable with ShowStatus -> True and native exact rows explains "Native" and "Exact".
    Remarks: The user does not know the package's vocabulary, so every status word shown is explained (U4, P3).
        $StatusLegend is the single table of explanations; a unit test checks that every value the code emits has one.
    See also: displayColumns.
*)
$StatusLegend = <|
    "Complete" -> "Complete: the irrep's matrices are computed and verified.",
    "Not computed" -> "Not computed: no matrices yet (ComputeGroupRepresentations computes them).",
    "Partial: requested basis pending" -> "Partial: matrices exist, but not yet in the requested basis.",
    "Active basis differs" -> "Active basis differs: the stored matrices are not in the basis that was asked for.",
    "Native" -> "Native: the entries are rational or cyclotomic numbers and GAP verified the matrices as a homomorphism of the group whose traces are the irrep's character.",
    "ScaledNative" -> "ScaledNative: as Native, verified after a rescaling of the basis vectors.",
    "Wolfram" -> "Wolfram: the entries are algebraic numbers; Wolfram re-verifies the matrices exactly whenever they are loaded.",
    "Numerical" -> "Numerical: floating-point matrices; they are numerical evidence, not exact results.",
    "Exact" -> "Exact: the entries are exact numbers (no rounding).",
    "unitary" -> "unitary: every matrix is unitary.", "general" -> "general: no unitarity is claimed.",
    "T-diagonal" -> "T-diagonal: the matrix of the modular generator T is diagonal.",
    "Stored variant" -> "Stored variant: these are the group's own verified matrices for this irrep.",
    "Validated" -> "Validated: ValidateRepresentation checked these matrices against the group.",
    "Unvalidated" -> "Unvalidated: nothing is known yet about these matrices and the group."|>;
$GroupSummaryLegend = {
    "Availability: what is computed and stored for each kind of data of the group (Complete: all of it; Partial: part of it; NotComputed: nothing yet, it is computed when first needed).",
    "Representations: the number of irreps in each state (Complete: matrices computed and verified).",
    "GAP state: whether a GAP session of this group is saved for reuse; without one, GAP work (if any is needed) starts again from the stored data."};
statusLegend[data_Association] := Module[{words = {}},
    If[data["Kind"] === "GroupSummary", Return[$GroupSummaryLegend]];
    If[!displayColumn[data, "Status"], Return[{}]];
    Switch[data["Kind"],
        "RepresentationTable", Scan[Function[row, words = Join[words, {row["Status"]},
            If[StringQ[row["ActiveVariant"]], Join[{ToString[row["Tier"]], ToString[row["Arithmetic"]]},
                If[AssociationQ[row["BasisProperties"]], Join[{If[TrueQ[row["BasisProperties"]["Unitary"]], "unitary", "general"]},
                    If[TrueQ[Lookup[row["BasisProperties"], "TDiagonal", False]], {"T-diagonal"}, {}]], {}]], {}]]], data["Rows"]],
        "Representation", words = {data["Validation"]["Status"], ToString[Lookup[data["Validation"], "Tier", ""]], data["Arithmetic"]},
        _, Null];
    DeleteMissing[Lookup[$StatusLegend, DeleteDuplicates[words], Missing[]]]];
irrepNameLegend[data_Association] := If[!KeyExistsQ[data, "IrrepNames"], {},
    Join[If[displayColumn[data, "Auto"], If[AnyTrue[Values[data["IrrepNames"]], #["Auto"] =!= None && Lookup[#["Auto"], "Generator", None] === "T" &],
            {"Label (T phases): dimension with the phases k/n of the eigenvalues e^{2\[Pi]i k/n} of the generator T (no modular assignment: a presentation aid, not a certified modular T spectrum)."},
            {"Label (T phases): dimension with the phases k/n of the eigenvalues e^{2\[Pi]i k/n} of the modular generator T."}], {}],
        If[displayColumn[data, "User"], {"Name: the label assigned with SetIrrepLabels."}, {}]]];

True
