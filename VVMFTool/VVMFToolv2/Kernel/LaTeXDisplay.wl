(*
    :Title: LaTeX rendering of display documents
    :Context: VVMFTool`Private`
    :Summary: Semantic LaTeX for display nodes, tables and documents: escaping, standard and Paper notation,
        roots of unity (exponential/omega), matrices, long and wide tables, preambles and legends.
    :Responsibilities:
        - escapeTeXText, renderTeXNode (registry dispatch), texDependencies, renderTeXTable,
          renderTeXDocument, LaTeXPreamble, ScalarLaTeX, MatrixLaTeX, ToLaTeX.
        - Tables and matrices are built structurally; no global string substitution; entries keep their
          parentheses; nothing is compiled or executed.
    :Dependencies: DisplayData.wl; DisplayNotation.wl; DisplayLabels.wl; GroupConstruction.wl.
    :See Also: VVMFArch/step3Plan.md (LaTeX contracts); v1 VVMFTool-LaTeX.wl (replaced).
*)

$TeXPanelColumns = 8;
(* Nominal \linewidth (pt) of the Standalone page, used to turn width estimates into fractions of \linewidth. *)
$TeXNominalLineWidth = 500.;

(*
    Summary: Estimated natural width (pt, 10pt font) of a LaTeX math or text string.
    Parameters: s — LaTeX string.
    Options/defaults: None.
    Returns: Nonnegative real.
    Effects: Pure.
    Failures: None.
    Example: texStringWidth["\\frac{1}{2}"] is about 4 pt (one script-size digit).
    Remarks: A compile-free heuristic: fractions keep their longer part at script size, sub/superscripts count
        0.7, a control word counts as one glyph, binary + and - include their spacing, braces and spacing
        commands are free. Matrices are estimated structurally by texNodeWidth.
    See also: texNodeWidth; renderTeXTable.
*)
texStringWidth[s_String] /; StringContainsQ[StringReplace[s, RegularExpression["\\\\(begin|end)\\{[a-z*]+\\}"] -> ""], "\\\\"] :=
    (* Stacked lines (\\ in smallmatrix headers or multi-line cells): the widest line. *)
    Max[texStringWidth /@ StringSplit[StringReplace[s, RegularExpression["\\\\(begin|end)\\{[a-z*]+\\}"] -> ""], "\\\\"]];
texStringWidth[s_String] := Module[{t = s, previous = None, script = 0., glyphs, fractions},
    fractions = StringCount[s, RegularExpression["\\\\[dt]?frac"]];
    (* A unary minus (at the start or after an opening delimiter) has no binary spacing. *)
    t = StringReplace[t, RegularExpression["(^|[{(=]\\s*)-"] -> "$1\[Dash]"];
    t = StringReplace[t, {"\\left" -> "", "\\right" -> "", "\\," -> "", "\\;" -> "", "\\!" -> "", "\\quad" -> "MM",
        RegularExpression["\\\\(begin|end)\\{[a-z*]+\\}"] -> "", "\\text{" -> "{", "\\mathrm{" -> "{", "\\texttt{" -> "{",
        "\\mathbf{" -> "{", "\\footnotesize" -> "", "\\small" -> ""}];
    (* Roots (the radical sign, then the argument inline) and fractions (innermost first: the longer part, marked as
       script size) are reduced alternately until neither applies, so nested forms such as \frac{\sqrt{5}}{4} and
       \sqrt{\frac{5}{8}} are handled. *)
    While[t =!= previous, previous = t;
        t = StringReplace[t, RegularExpression["\\\\sqrt\\{([^{}]*)\\}"] -> "\[Sqrt]$1"];
        t = StringReplace[t, RegularExpression["\\\\[dt]?frac\\{([^{}]*)\\}\\{([^{}]*)\\}"] :>
            With[{a = "$1", b = "$2"}, "\[LeftDoubleBracket]" <> If[StringLength[a] >= StringLength[b], a, b] <> "\[RightDoubleBracket]"]]];
    (* Superscript and subscript groups. *)
    previous = None;
    While[t =!= previous, previous = t;
        t = StringReplace[t, RegularExpression["[\\^_]\\{([^{}]*)\\}"] -> "\[LeftDoubleBracket]$1\[RightDoubleBracket]"]];
    t = StringReplace[t, RegularExpression["[\\^_](\\\\[a-zA-Z]+|.)"] -> "\[LeftDoubleBracket]$1\[RightDoubleBracket]"];
    t = StringReplace[t, RegularExpression["\\\\[a-zA-Z]+"] -> "x"];
    (* Binary operators include TeX's medium math spaces (about 16 pt each); a fraction adds its null-delimiter
       space. *)
    glyphs[u_String] := Total[Characters[u] /. {"+" | "-" | "=" -> 3., "\[Sqrt]" -> 1.5, "\[Dash]" -> 1.4, "{" | "}" | " " -> 0.,
        "(" | ")" | "," | "." | "|" -> 0.6, _String -> 1.}];
    script = Total[glyphs /@ StringCases[t, "\[LeftDoubleBracket]" ~~ x : Shortest[___] ~~ "\[RightDoubleBracket]" :> x]];
    5.5 (glyphs[StringReplace[t, "\[LeftDoubleBracket]" ~~ Shortest[___] ~~ "\[RightDoubleBracket]" -> ""]] + 0.7 script + 0.5 fractions)
];

(*
    Summary: Estimated natural width (pt) of a rendered table cell.
    Parameters: cell — string or display node; settings.
    Options/defaults: None.
    Returns: Nonnegative real (0 for a cell that fails to render; the renderer reports that failure).
    Effects: Pure.
    Failures: None.
    Example: a 3 x 3 integer matrix is about 3 x 5.5 + 2 x 10 + 12 pt.
    Remarks: A matrix is the sum of its column widths (the widest entry of each column), 10 pt column
        separation and the parentheses; other nodes use texStringWidth of their LaTeX.
    See also: renderTeXTable.
*)
texNodeWidth[cell_, settings_Association] := Which[
    StringQ[cell], texStringWidth[cell],
    AssociationQ[cell] && cell["Kind"] === "Text", 5. StringLength[cell["Text"]],
    AssociationQ[cell] && cell["Kind"] === "Matrix" && !(cell["Dimensions"] === {1, 1} && Lookup[settings, OneByOneMatrix, "Scalar"] === "Scalar"),
    Total[Max /@ Transpose[Map[With[{t = renderTeXNode[#, settings]}, If[StringQ[t], texStringWidth[t], 0.]] &, cell["Cells"], {2}]]] +
        10. (Last[cell["Dimensions"]] - 1) + 12.,
    True, With[{t = renderTeXNode[cell, settings]}, If[StringQ[t], texStringWidth[t], 0.]]];

(*
    Summary: Pack variable columns into panels whose estimated widths fit the line.
    Parameters: widths — estimated natural widths of the variable columns (pt); budget — width available to the
        variable columns of one panel (pt); limit — maximum columns per panel.
    Options/defaults: None.
    Returns: List of column position lists covering every column once, in order; a column wider than the budget
        is alone in its panel.
    Effects: Pure.
    Failures: None.
    Example: widthPanels[{300, 190}, 200, 8] is {{1}, {2}}; widthPanels[{50, 50}, 200, 8] is {{1, 2}}; 25 narrow
        columns with a cap of 8 give panels of 7, 6, 6 and 6 columns.
    Remarks: Each column also needs 2\tabcolsep (12 pt).
    See also: renderTeXTable.
*)
widthPanels[widths_List, budget_, limit_Integer] := Module[{panels = {}, current = {}, used = 0., count, balanced},
    Do[With[{w = widths[[k]] + 12.},
        If[current =!= {} && (used + w > budget || Length[current] >= limit),
            AppendTo[panels, current]; current = {}; used = 0.];
        AppendTo[current, k]; used += w], {k, Length[widths]}];
    If[current =!= {} || panels === {}, AppendTo[panels, current]];
    (* Balance: the same number of panels with sizes as equal as possible, when every balanced panel still fits
       (avoids a one-column last panel when the column cap, not the width, closed the panels). *)
    count = Length[panels];
    If[count > 1,
        balanced = TakeList[Range[Length[widths]], With[{q = Quotient[Length[widths], count], r = Mod[Length[widths], count]},
            Join[ConstantArray[q + 1, r], ConstantArray[q, count - r]]]];
        If[AllTrue[balanced, Length[#] <= limit && Total[widths[[#]] + 12.] <= budget &], panels = balanced]];
    panels
];

(*
    Summary: Escape plain text for LaTeX text mode.
    Parameters: s — string.
    Options/defaults: None.
    Returns: The escaped string.
    Effects: Pure.
    Failures: None.
    Example: escapeTeXText["a_b & 50%"] is "a\\_b \\& 50\\%".
    Remarks: <, > and | are escaped too (the default OT1 font would print other glyphs); non-ASCII characters
        follow escapeTeXCharacter (Greek letters as math symbols, Latin-1 letters unchanged, others as code points).
    See also: texTextNode; escapeTeXCharacter.
*)
escapeTeXText[s_String] := StringJoin[escapeTeXCharacter /@ Characters[s]];

(* Greek letters (math italic lower case, upright upper case as LaTeX sets them) and typographic punctuation. *)
$TeXGreekNames = {"alpha", "beta", "gamma", "delta", "epsilon", "zeta", "eta", "theta", "iota", "kappa", "lambda", "mu",
    "nu", "xi", "o", "pi", "rho", "varsigma", "sigma", "tau", "upsilon", "phi", "chi", "psi", "omega"};
$TeXCharacterMap = Join[
    AssociationThread[CharacterRange[945, 969], Map[If[# === "o", "o", "\\ensuremath{\\" <> # <> "}"] &, $TeXGreekNames]],
    AssociationThread[FromCharacterCode /@ DeleteCases[Range[913, 937], 930],
        {"A", "B", "\\ensuremath{\\Gamma}", "\\ensuremath{\\Delta}", "E", "Z", "H", "\\ensuremath{\\Theta}", "I", "K",
            "\\ensuremath{\\Lambda}", "M", "N", "\\ensuremath{\\Xi}", "O", "\\ensuremath{\\Pi}", "P", "\\ensuremath{\\Sigma}", "T",
            "\\ensuremath{\\Upsilon}", "\\ensuremath{\\Phi}", "X", "\\ensuremath{\\Psi}", "\\ensuremath{\\Omega}"}],
    (* the group-name signs of the library titles (review F15, F21): the plain titles write the paper's semidirect
       product \rtimes as U+22B3, so it is rendered as \rtimes; also U+22CA, U+22C9 and congruent *)
    AssociationThread[FromCharacterCode /@ {8883, 8906, 8905, 8773}, {"\\ensuremath{\\rtimes}", "\\ensuremath{\\rtimes}",
        "\\ensuremath{\\ltimes}", "\\ensuremath{\\cong}"}],
    (* em dash, en dash, quotes, ellipsis, times, middle dot, prime, minus, <=, >=, infinity, circled times/plus *)
    AssociationThread[FromCharacterCode /@ {8212, 8211, 8216, 8217, 8220, 8221, 8230, 215, 183, 8242, 8722, 8804, 8805, 8734, 8855, 8853},
        {"---", "--", "`", "'", "``", "''", "\\ldots{}", "\\ensuremath{\\times}", "\\ensuremath{\\cdot}", "\\ensuremath{'}",
            "\\ensuremath{-}", "\\ensuremath{\\le}", "\\ensuremath{\\ge}", "\\ensuremath{\\infty}", "\\ensuremath{\\otimes}", "\\ensuremath{\\oplus}"}],
    (* subscript and superscript digits *)
    AssociationThread[FromCharacterCode /@ Range[8320, 8329], ("\\textsubscript{" <> ToString[#] <> "}" &) /@ Range[0, 9]],
    AssociationThread[FromCharacterCode /@ {8304, 185, 178, 179, 8308, 8309, 8310, 8311, 8312, 8313},
        ("\\textsuperscript{" <> ToString[#] <> "}" &) /@ Range[0, 9]]];

(*
    Summary: Escape one character for LaTeX text mode.
    Parameters: c — one-character string.
    Options/defaults: None.
    Returns: The LaTeX text for c.
    Effects: Pure.
    Failures: None.
    Example: escapeTeXCharacter[FromCharacterCode[916]] (capital delta) is "\\ensuremath{\\Delta}"; Latin-1 letters
        such as FromCharacterCode[233] are returned unchanged.
    Remarks: ASCII specials are escaped; Greek letters and common typographic symbols are mapped; other Latin-1
        letters pass through (pdfLaTeX reads UTF-8 input since 2018); any other character is shown as its code
        point, \texttt{U+XXXX}, so the document always compiles and nothing is silently dropped.
    See also: escapeTeXText.
*)
escapeTeXCharacter[c_String] := With[{code = First[ToCharacterCode[c]]}, Which[
    code < 128, Replace[c, {"\\" -> "\\textbackslash{}", "{" -> "\\{", "}" -> "\\}", "$" -> "\\$",
        "<" -> "\\textless{}", ">" -> "\\textgreater{}", "|" -> "\\textbar{}",
        "&" -> "\\&", "#" -> "\\#", "^" -> "\\textasciicircum{}", "_" -> "\\_", "%" -> "\\%", "~" -> "\\textasciitilde{}"}],
    KeyExistsQ[$TeXCharacterMap, c], $TeXCharacterMap[c],
    192 <= code <= 255 && code =!= 215 && code =!= 247, c,
    True, "\\texttt{U+" <> ToUpperCase[IntegerString[code, 16, 4]] <> "}"]];

(*
    Summary: Render one display node to LaTeX (math mode unless stated).
    Parameters: node — registered display node; settings — render settings (ScalarNotation, NotationStyle,
        OneByOneMatrix, Digits, ...).
    Options/defaults: None.
    Returns: String, or InvalidDisplayNode Failure for an unregistered or malformed node.
    Effects: Pure.
    Failures: InvalidDisplayNode.
    Example: renderTeXNode[scalarDisplayNode[1/2], settings] is "\\frac{1}{2}".
    See also: registerDisplayNode; texDependencies.
*)
renderTeXNode[node_Association, settings_Association] := If[displayNodeQ[node],
    $DisplayNodeRegistry[node["Kind"]]["TeX"][node, settings],
    makeFailure["InvalidDisplayNode", "The display node is not registered or malformed.", <|"Kind" -> Lookup[node, "Kind", None]|>]];
renderTeXNode[_, _] := makeFailure["InvalidDisplayNode", "Expected a display node."];

(*
    Summary: LaTeX handlers of Text (\text{} with escaping) and RawTeX (the supplied TeX) nodes.
    Parameters: node — Text or RawTeX node; settings.
    Options/defaults: None.
    Returns: String.
    Effects: Pure.
    Failures: None.
    Example: texTextNode[textNode["a_b"], <||>] is "\\text{a\\_b}".
    See also: renderTeXNode.
*)
texTextNode[node_, settings_] := "\\text{" <> escapeTeXText[node["Text"]] <> "}";
texRawTeXNode[node_, settings_] := node["TeX"];

(*
    Summary: LaTeX of an exact rational.
    Parameters: q — integer or rational.
    Options/defaults: None.
    Returns: String such as "-\\frac{1}{2}".
    Effects: Pure.
    Failures: None.
    Example: texRational[-3/4] is "-\\frac{3}{4}".
    See also: texScalarNode.
*)
texRational[q_Integer] := ToString[q];
texRational[q_Rational] := If[q < 0, "-", ""] <> "\\frac{" <> ToString[Abs[Numerator[q]]] <> "}{" <> ToString[Denominator[q]] <> "}";

(*
    Summary: The imaginary unit and exponential base of the notation style (i, e or the Paper macros \ii, \ee).
    Parameters: settings — render settings (NotationStyle).
    Options/defaults: None.
    Returns: String.
    Effects: Pure.
    Failures: None.
    Example: imaginaryUnitTeX[<|NotationStyle -> "Paper"|>] is "\\ii".
    See also: texPhaseNode; LaTeXPreamble.
*)
imaginaryUnitTeX[settings_] := If[Lookup[settings, NotationStyle, "Standard"] === "Paper", "\\ii", "i"];
exponentialBaseTeX[settings_] := If[Lookup[settings, NotationStyle, "Standard"] === "Paper", "\\ee", "e"];

(*
    Summary: LaTeX of a real exact radical expression (TeXForm of a real value; parentheses kept).
    Parameters: x — real exact expression.
    Options/defaults: None.
    Returns: String.
    Effects: Pure.
    Failures: None.
    Example: texRealExact[1/(1 + Sqrt[2])] contains "\\sqrt{2}".
    See also: texComplexParts.
*)
texRealExact[x_] := If[MatchQ[x, _Integer | _Rational], texRational[x], ToString[TeXForm[x]]];

(*
    Summary: LaTeX of a + b i from its real and imaginary parts, with the configured imaginary unit.
    Parameters: re, im — real parts (exact or numerical strings produced by a part renderer); partTeX —
        function rendering one real part; settings.
    Options/defaults: None.
    Returns: String.
    Effects: Pure.
    Failures: None.
    Example: texComplexParts[0, 1, texRealExact, settings] is "i".
    Remarks: The unit is inserted structurally, never found by regular expressions in TeXForm output.
    See also: texScalarNode.
*)
texComplexParts[re_, im_, partTeX_, settings_] := Module[{unit = imaginaryUnitTeX[settings], imTeX, reTeX},
    reTeX = partTeX[re];
    imTeX = Which[im == 1, unit, im == -1, "-" <> unit,
        (* An imaginary part that is itself a sum is parenthesized: (a - b) i, never a - b i. *)
        True, With[{s = partTeX[im]}, If[Head[im] === Plus, "\\left(" <> s <> "\\right)" <> unit, s <> " " <> unit]]];
    Which[im == 0, reTeX, re == 0, imTeX,
        StringStartsQ[imTeX, "-"], reTeX <> imTeX,
        True, reTeX <> "+" <> imTeX]
];

(*
    Summary: LaTeX of a numerical value with its displayed digits.
    Parameters: x — approximate number; settings (Digits).
    Options/defaults: Digits Automatic shows the value's own precision (at most 16 digits for machine numbers).
    Returns: String of decimal digits (complex values as a + b i).
    Effects: Pure.
    Failures: None.
    Example: texNumerical[0.5, settings] is "0.5".
    See also: texScalarNode.
*)
texNumerical[x_, settings_] := Module[{digits},
    (* Digits per real part: the requested Digits, never more than the part's own precision (a complex number's
       precision can exceed its parts'; NumberForm would pad with zeros). *)
    digits[part_] := With[{available = Max[1, Floor[Replace[Precision[part], {MachinePrecision -> 16, Infinity -> 16}]]]},
        Replace[Lookup[settings, Digits, Automatic], {Automatic -> available, d_Integer :> Min[d, available]}]];
    texComplexParts[Re[x], Im[x], Function[part, ToString[NumberForm[part, digits[part],
        NumberFormat -> (StringJoin[#1, If[#3 === "", "", "\\times 10^{" <> #3 <> "}"]] &)]]], settings]
];

(*
    Summary: LaTeX handler of Scalar nodes, and the dependency collectors of Scalar, Phase, Matrix and IrrepLabel nodes.
    Parameters: node — display node; settings.
    Options/defaults: None.
    Returns: String (handler) or list of legend tags (collectors).
    Effects: Pure.
    Failures: None.
    Example: texScalarDependencies[algebraicRootLabel[Root[#^5 - # - 1 &, 1]]] is {"RootLegend"}.
    See also: texDependencies; renderTeXDocument.
*)
texScalarNode[node_, settings_] := Switch[node["Form"],
    "Rational", texRational[node["Value"]],
    "Numerical", texNumerical[node["Value"], settings],
    "Radical", With[{e = node["Expression"]}, texComplexParts[ComplexExpand[Re[e]], ComplexExpand[Im[e]], texRealExact, settings]],
    "Cyclotomic", StringJoin[MapIndexed[Function[{term, position}, With[{c = term[[1]], k = Numerator[term[[2]]], n = Denominator[term[[2]]]},
        If[First[position] === 1, If[c < 0, "-", ""], If[c < 0, "-", "+"]] <>
            If[Abs[c] === 1 && term[[2]] =!= 0, "", texRational[Abs[c]]] <>
            If[term[[2]] === 0, "", If[Lookup[settings, ScalarNotation, "Standard"] === "Omega",
                "\\omega_{" <> ToString[n] <> "}" <> If[k === 1, "", "^{" <> ToString[k] <> "}"],
                exponentialBaseTeX[settings] <> "^{2\\pi " <> imaginaryUnitTeX[settings] <>
                    If[k === 1, "/" <> ToString[n], "\\," <> ToString[k] <> "/" <> ToString[n]] <> "}"]]]], node["Terms"]]],
    "Root", "\\mathrm{Root}\\bigl(" <> texPolynomial[node["Polynomial"]] <> ",\\," <> ToString[node["Index"]] <> "\\bigr)"];
texScalarDependencies[node_] := Which[node["Form"] === "Root", {"RootLegend"}, node["Form"] === "Numerical", {"NumericalLegend"},
    node["Form"] === "Cyclotomic", {"OmegaLegend"}, True, {}];

(*
    Summary: LaTeX of an integer polynomial in x from its coefficients (lowest degree first).
    Parameters: coefficients — integers.
    Options/defaults: None.
    Returns: String.
    Effects: Pure.
    Failures: None.
    Example: texPolynomial[{-1, -1, 0, 0, 0, 1}] is "x^{5}-x-1".
    See also: algebraicRootLabel.
*)
texPolynomial[coefficients_List] := Module[{terms},
    terms = Reverse[Select[MapIndexed[{#1, First[#2] - 1} &, coefficients], #[[1]] =!= 0 &]];
    StringJoin[MapIndexed[Function[{term, position}, Module[{c = term[[1]], k = term[[2]], sign, magnitude, power},
        sign = Which[c < 0, "-", First[position] === 1, "", True, "+"];
        power = Switch[k, 0, "", 1, "x", _, "x^{" <> ToString[k] <> "}"];
        magnitude = If[Abs[c] === 1 && k > 0, "", ToString[Abs[c]]];
        sign <> magnitude <> power]], terms]]
];

(*
    Summary: LaTeX of a certified root of unity m Exp[2 Pi I k/n] in the configured scalar notation.
    Parameters: node — Phase node; settings (ScalarNotation, NotationStyle).
    Options/defaults: None.
    Returns: String.
    Effects: Pure.
    Failures: None.
    Example: with ScalarNotation -> "Omega", the node of Exp[4 Pi I/3] renders "\\omega_{3}^{2}".
    Remarks: "Standard" uses an exact radical a + b i when one exists (for example -1/2 + (Sqrt[3]/2) i) and the
        exponential otherwise; the value is never changed.
    See also: texPhaseDependencies.
*)
texPhaseNode[node_, settings_] := Module[{k = Numerator[node["Phase"]], n = Denominator[node["Phase"]], m = node["Magnitude"],
        style = Lookup[settings, ScalarNotation, "Standard"], prefix, body, radical},
    prefix = If[m === 1, "", texRational[m]];
    Switch[style,
        "Omega", prefix <> "\\omega_{" <> ToString[n] <> "}" <> If[k === 1, "", "^{" <> ToString[k] <> "}"],
        "Exponential", prefix <> exponentialBaseTeX[settings] <> "^{2\\pi " <> imaginaryUnitTeX[settings] <>
            If[k === 1, "/" <> ToString[n], "\\," <> ToString[k] <> "/" <> ToString[n]] <> "}",
        _, radical = displayRadical[node["Value"]];
            If[radical =!= $Failed, texComplexParts[ComplexExpand[Re[radical]], ComplexExpand[Im[radical]], texRealExact, settings],
                texPhaseNode[node, Join[settings, <|ScalarNotation -> "Exponential"|>]]]]
];
texPhaseDependencies[node_] := {"OmegaLegend"};

(*
    Summary: LaTeX of a matrix node (pmatrix), or of its entry when 1 x 1 with OneByOneMatrix -> "Scalar".
    Parameters: node — Matrix node; settings.
    Options/defaults: None.
    Returns: String.
    Effects: Pure.
    Failures: None for valid nodes.
    Example: renderTeXNode[matrixDisplayNode[{{1, 0}, {0, -1}}], settings] is "\\begin{pmatrix}1 & 0 \\\\ 0 & -1\\end{pmatrix}".
    See also: MatrixLaTeX.
*)
texMatrixNode[node_, settings_] := If[node["Dimensions"] === {1, 1} && Lookup[settings, OneByOneMatrix, "Scalar"] === "Scalar",
    renderTeXNode[node["Cells"][[1, 1]], settings],
    "\\begin{pmatrix}" <> StringRiffle[StringRiffle[renderTeXNode[#, settings] & /@ #, " & "] & /@ node["Cells"], " \\\\ "] <> "\\end{pmatrix}"];
texMatrixDependencies[node_] := DeleteDuplicates[Flatten[texDependencies /@ Flatten[node["Cells"]]]];

(*
    Summary: LaTeX of an irrep label: bold dimension (Paper: \rep) with certified T phases as subscript.
    Parameters: node — IrrepLabel node; settings.
    Options/defaults: None.
    Returns: String.
    Effects: Pure.
    Failures: None.
    Example: a two-dimensional label with phases {0, 1/3} renders "\\mathbf{2}_{(0,\\frac{1}{3})}".
    See also: resolveDisplayLabels.
*)
texIrrepLabelNode[node_, settings_] := (If[Lookup[settings, NotationStyle, "Standard"] === "Paper", "\\rep{", "\\mathbf{"] <>
    ToString[node["Dimension"]] <> "}") <>
    If[node["Phases"] === None, "", "_{(" <> StringRiffle[texRational /@ node["Phases"], ","] <> ")}"];
texIrrepLabelDependencies[node_] := {};

(*
    Summary: The dependencies (legends, macros) a node needs.
    Parameters: node — display node.
    Options/defaults: None.
    Returns: List of dependency tags ("OmegaLegend", "RootLegend", "NumericalLegend").
    Effects: Pure.
    Failures: None ({} for invalid nodes).
    Example: texDependencies[phaseDisplayNode[Exp[2 Pi I/3]]] is {"OmegaLegend"}.
    See also: renderTeXDocument.
*)
texDependencies[node_Association] := If[displayNodeQ[node], $DisplayNodeRegistry[node["Kind"]]["Dependencies"][node], {}];
texDependencies[_] := {};

(*
    Summary: The package and macro lines a rendered document needs.
    Status: Alpha.
    Parameters: None.
    Options/defaults: NotationStyle -> "Standard" or "Paper" (adds \ii, \ee and \rep through \providecommand, so an
        existing definition is kept).
    Returns: String of \usepackage and macro lines (no \documentclass), or Failure.
    Effects: Pure.
    Failures: InvalidOption.
    Example: StringContainsQ[LaTeXPreamble[NotationStyle -> "Paper"], "\\providecommand{\\ii}"] is True.
    See also: ToLaTeX; ExportDisplay.
*)
Options[LaTeXPreamble] = {NotationStyle -> "Standard"};
LaTeXPreamble[options : OptionsPattern[]] := Module[{effective},
    effective = resolveOperationOptions[LaTeXPreamble, "LaTeXPreamble", {options}];
    If[FailureQ[effective], Return[effective]];
    texPreamble[effective]
];
LaTeXPreamble[___] := makeFailure["InvalidInput", "LaTeXPreamble expects options only."];
(*
    Summary: The package and macro lines of a notation style (LaTeXPreamble's body).
    Parameters: settings — render settings (NotationStyle).
    Options/defaults: None.
    Returns: String.
    Effects: Pure.
    Failures: None.
    Example: StringContainsQ[texPreamble[<||>], "booktabs"] is True.
    See also: LaTeXPreamble; ToLaTeX.
*)
texPreamble[settings_] := StringRiffle[Join[{"\\usepackage{amsmath}", "\\usepackage{amssymb}", "\\usepackage{booktabs}",
    "\\usepackage{longtable}", "\\usepackage{array}", "\\usepackage{adjustbox}"},
    If[Lookup[settings, NotationStyle, "Standard"] === "Paper",
        {"\\providecommand{\\ii}{\\mathrm{i}}", "\\providecommand{\\ee}{\\mathrm{e}}", "\\providecommand{\\rep}[1]{\\mathbf{#1}}"}, {}]], "\n"];

(*
    Summary: LaTeX of one exact or numerical scalar.
    Status: Alpha.
    Parameters: x — exact algebraic number or numerical value.
    Options/defaults: ScalarNotation -> "Standard" ("Exponential", "Omega" for certified roots of unity);
        NotationStyle -> "Standard" | "Paper"; Digits -> Automatic or a positive integer (numerical values only).
    Returns: String, or Failure.
    Effects: Pure; the value is never rounded, chopped or rationalized (Digits limits displayed digits only).
    Failures: UnsupportedDisplayValue (for example Pi); InvalidOption.
    Example: ScalarLaTeX[Exp[2 Pi I/3], ScalarNotation -> "Omega"] is "\\omega_{3}"; ScalarLaTeX[Surd[-1, 3]] is "-1".
    See also: MatrixLaTeX; ToLaTeX.
*)
Options[ScalarLaTeX] = {ScalarNotation -> "Standard", NotationStyle -> "Standard", Digits -> Automatic};
ScalarLaTeX[x_, options : OptionsPattern[]] := Module[{effective, node},
    effective = resolveOperationOptions[ScalarLaTeX, "ScalarLaTeX", {options}];
    If[FailureQ[effective], Return[effective]];
    node = scalarDisplayNode[x]; If[FailureQ[node], Return[node]];
    renderTeXNode[node, effective]
];
ScalarLaTeX[___] := makeFailure["InvalidInput", "ScalarLaTeX expects a scalar and options."];

(*
    Summary: LaTeX of a matrix.
    Status: Alpha.
    Parameters: m — rectangular matrix of exact algebraic or numerical scalars.
    Options/defaults: ScalarNotation; NotationStyle; Digits; OneByOneMatrix -> "Scalar" (a 1 x 1 matrix as its
        entry) or "Matrix".
    Returns: String (a pmatrix), or Failure.
    Effects: Pure; entries keep their parentheses.
    Failures: InvalidMatrix (ragged or empty); UnsupportedDisplayValue; InvalidOption.
    Example: MatrixLaTeX[{{1/(1 + Sqrt[2]), -1}, {0, Exp[2 Pi I/3]}}, ScalarNotation -> "Omega"] contains "\\omega_{3}".
    See also: ScalarLaTeX; ToLaTeX.
*)
Options[MatrixLaTeX] = {ScalarNotation -> "Standard", NotationStyle -> "Standard", Digits -> Automatic, OneByOneMatrix -> "Scalar"};
MatrixLaTeX[m_List, options : OptionsPattern[]] := Module[{effective, node},
    effective = resolveOperationOptions[MatrixLaTeX, "MatrixLaTeX", {options}];
    If[FailureQ[effective], Return[effective]];
    node = matrixDisplayNode[m]; If[FailureQ[node], Return[node]];
    renderTeXNode[node, effective]
];
MatrixLaTeX[___] := makeFailure["InvalidInput", "MatrixLaTeX expects a matrix and options."];

(*
    Summary: A common prefix of irrep or class IDs, to shorten table cells without losing identity.
    Parameters: ids — list of ID strings.
    Options/defaults: None.
    Returns: {prefix, suffixes}: prefix is everything up to the last ":" shared by every ID ("" if none).
    Effects: Pure.
    Failures: None.
    Example: idPrefix[{"c:irrep:1", "c:irrep:2"}] is {"c:irrep:", {"1", "2"}}.
    Remarks: The legend states the prefix, so every cell still determines its full ID.
    See also: renderTeXDocument.
*)
idPrefix[ids_List] := Module[{prefixes},
    If[ids === {}, Return[{"", {}}]];
    prefixes = StringReplace[#, RegularExpression["[^:]*$"] -> ""] & /@ ids;
    If[Length[DeleteDuplicates[prefixes]] === 1 && First[prefixes] =!= "",
        {First[prefixes], StringDrop[#, StringLength[First[prefixes]]] & /@ ids}, {"", ids}]
];

(*
    Summary: Render a Table node as longtable panels: headers repeat on every page; wide tables split into numbered
        column panels repeating the fixed columns; every variable cell is limited to its share of the line width.
    Parameters: node — Table node <|"Kind" -> "Table", "Fixed" -> {headers}, "Columns" -> {headers}, "Rows" -> {Row
        nodes}, "Caption" -> string (LaTeX), "Label" -> None | string, "Alignment" -> "c" | "p", "FixedShare" -> fraction
        of the line width the fixed columns take, optional "FixedSpec" -> column specifications of the fixed columns|>;
        settings.
    Options/defaults: At most $TeXPanelColumns variable columns per panel; widths are estimated against the
        nominal Standalone line width $TeXNominalLineWidth.
    Returns: String, or Failure.
    Effects: Pure.
    Failures: Rendering failures of cells.
    Example: a character table with twelve classes renders two panels, each repeating the ID and label columns.
    Remarks: No row or column is dropped. With "Alignment" -> "c" panels are width-aware (widthPanels on
        texNodeWidth estimates, 2\tabcolsep per column included), each column's cells are limited to its estimate
        plus a proportional share of the slack, so they are not scaled; only a column wider than a whole panel is
        scaled down by \adjustbox{max width=...} (the last resort). "p" gives wrapping paragraph columns for text.
    See also: splitDisplayPanels; renderTeXDocument.
*)
renderTeXTable[node_Association, settings_Association] := Module[{panels, count, render, texts, widths, budget},
    (* Width-aware panels: estimate each variable column's natural width (its header and every cell) and open a
       new panel before the estimate would exceed the width the fixed columns leave. *)
    widths = Table[Max[texNodeWidth[node["Columns"][[k]], settings], texNodeWidth[#["Cells"][[k]], settings] & /@ node["Rows"]],
        {k, Length[node["Columns"]]}];
    (* The fixed columns are estimated too: a paragraph column takes its declared width, any other its widest
       cell; each column also needs 2\tabcolsep. *)
    budget = 0.95 $TeXNominalLineWidth - Total[MapIndexed[Function[{spec, index}, 12. + With[
        {fraction = StringCases[spec, "p{" ~~ f : NumberString ~~ "\\linewidth}" :> ToExpression[f]]},
        If[fraction =!= {}, First[fraction] $TeXNominalLineWidth,
            Max[texNodeWidth[node["Fixed"][[First[index]]], settings], texNodeWidth[#["Fixed"][[First[index]]], settings] & /@ node["Rows"]]]]],
        Lookup[node, "FixedSpec", ConstantArray["l", Length[node["Fixed"]]]]]];
    budget = Max[budget, 0.25 $TeXNominalLineWidth];
    panels = If[Lookup[node, "Alignment", "c"] === "c", widthPanels[widths, budget, $TeXPanelColumns],
        splitDisplayPanels[Range[Length[node["Columns"]]], $TeXPanelColumns]];
    count = Length[panels];
    render[cell_] := Which[StringQ[cell], cell, AssociationQ[cell] && cell["Kind"] === "Text", escapeTeXText[cell["Text"]],
        AssociationQ[cell] && cell["Kind"] === "RawTeX", cell["TeX"],
        True, With[{s = renderTeXNode[cell, settings]}, If[FailureQ[s], s, "$" <> s <> "$"]]];
    texts = MapIndexed[Function[{columns, index}, Module[{header, body, fixedCount = Length[node["Fixed"]], caption, width, fit, spec,
            available, total, allot},
        (* Each column gets its estimate plus a proportional share of the slack; only a column wider than a whole
           panel is scaled (adjustbox max width, the last resort). *)
        available = budget - 12. Length[columns];
        total = Total[widths[[columns]]];
        allot = Which[columns === {}, {}, total <= available && total > 0, widths[[columns]] (available/total),
            True, ConstantArray[available/Length[columns], Length[columns]] (* single overwide column *)];
        width[k_] := ToString[NumberForm[Max[0.02, allot[[k]]/$TeXNominalLineWidth], {4, 3}]] <> "\\linewidth";
        fit[s_, k_] := If[Lookup[node, "Alignment", "c"] === "c", "\\adjustbox{max width=" <> width[k] <> "}{" <> s <> "}", s];
        spec = StringJoin[Lookup[node, "FixedSpec", ConstantArray["l", fixedCount]]] <> StringJoin[Table[If[Lookup[node, "Alignment", "c"] === "c", "c",
            ">{\\raggedright\\arraybackslash}p{" <> width[k] <> "}"], {k, Length[columns]}]];
        header = StringRiffle[Join[render /@ node["Fixed"], MapIndexed[fit[render[#1], First[#2]] &, node["Columns"][[columns]]]], " & "];
        body = StringRiffle[Map[StringRiffle[Join[render /@ #["Fixed"], MapIndexed[fit[render[#1], First[#2]] &, #["Cells"][[columns]]]], " & "] <> " \\\\" &, node["Rows"]], "\n"];
        caption = node["Caption"] <> If[count > 1, " (panel " <> ToString[First[index]] <> " of " <> ToString[count] <> ")", ""];
        "\\begin{longtable}{" <> spec <> "}\n" <>
            "\\caption{" <> caption <> "}" <> If[StringQ[node["Label"]] && First[index] === 1, "\\label{" <> node["Label"] <> "}", ""] <> "\\\\\n" <>
            "\\toprule\n" <> header <> " \\\\\n\\midrule\n\\endfirsthead\n" <>
            "\\multicolumn{" <> ToString[fixedCount + Length[columns]] <> "}{l}{\\small continued}\\\\\n\\toprule\n" <> header <>
            " \\\\\n\\midrule\n\\endhead\n\\bottomrule\n\\endfoot\n" <> body <> "\n\\end{longtable}"]], panels];
    If[!FreeQ[texts, _Failure], FirstCase[texts, _Failure, Null, Infinity], StringRiffle[texts, "\n\n"]]
];

(*
    Summary: Whether a table cell is a raw LaTeX string or a registered display node.
    Parameters: cell — any expression.
    Options/defaults: None.
    Returns: Boolean.
    Effects: Pure.
    Failures: None.
    Example: tableCellQ["ID"] is True.
    See also: registerDisplayNode; renderTeXTable.
*)
tableCellQ[cell_] := StringQ[cell] || displayNodeQ[cell];
registerDisplayNode["Row", <|"Validate" -> (ListQ[Lookup[#, "Fixed", None]] && ListQ[Lookup[#, "Cells", None]] &&
        AllTrue[Join[#["Fixed"], #["Cells"]], tableCellQ] &),
    "Notebook" -> notebookRowNode, "TeX" -> (StringRiffle[Map[Function[c, If[StringQ[c], c, renderTeXNode[c, #2]]], Join[#1["Fixed"], #1["Cells"]]], " & "] &),
    "Dependencies" -> (DeleteDuplicates[Flatten[texDependencies /@ Select[Join[#["Fixed"], #["Cells"]], AssociationQ]]] &)|>];
registerDisplayNode["Table", <|"Validate" -> Function[node, ListQ[Lookup[node, "Fixed", None]] && ListQ[Lookup[node, "Columns", None]] &&
        StringQ[Lookup[node, "Caption", None]] && ListQ[Lookup[node, "Rows", None]] &&
        AllTrue[node["Rows"], displayNodeQ[#] && #["Kind"] === "Row" && Length[#["Cells"]] === Length[node["Columns"]] &] &&
        AllTrue[Join[node["Fixed"], node["Columns"]], tableCellQ]],
    "Notebook" -> notebookTableNode, "TeX" -> renderTeXTable,
    "Dependencies" -> (DeleteDuplicates[Flatten[texDependencies /@ #["Rows"]]] &)|>];

(*
    Summary: Split column positions into panels of at most a given width.
    Parameters: columns — column positions; limit — positive integer.
    Options/defaults: None.
    Returns: List of column position lists covering every column once, in order.
    Effects: Pure.
    Failures: None.
    Example: splitDisplayPanels[Range[10], 8] is {Range[8], {9, 10}}.
    See also: renderTeXTable.
*)
splitDisplayPanels[columns_List, limit_Integer?Positive] := If[columns === {}, {{}}, Partition[columns, UpTo[limit]]];

(*
    Summary: Put the paper's TeX group title into an escaped caption (NotationStyle -> "Paper").
    Parameters: escaped — caption already escaped for TeX; group — the document's "Group" record; settings.
    Options/defaults: None.
    Returns: String.
    Effects: Pure.
    Failures: None.
    Example: with the title "$\\Gamma'_3\\cong [24,3]I$" the plain name in the caption becomes that math.
    Remarks: The paper's titles use its own macros (\\Z, \\x, \\SL), like \\rep in Paper style, so other styles keep the
        plain name.
    See also: renderTeXDocument; SetGroupTitle.
*)
texPaperTitle[escaped_String, group_Association, settings_Association] := With[{tex = Lookup[group, "TitleTeX", None], name = Lookup[group, "Name", None]},
    If[Lookup[settings, NotationStyle, "Standard"] === "Paper" && StringQ[tex] && StringQ[name] && name =!= "",
        StringReplace[escaped, escapeTeXText[name] -> "$" <> StringTrim[StringTrim[tex], "$"] <> "$", 1], escaped]];

(*
    Summary: Render a validated display document's body (tables, legends) to LaTeX.
    Parameters: data — validated document data; settings — effective render settings.
    Options/defaults: None.
    Returns: <|"Body" -> string, "Dependencies" -> tags|>, or Failure.
    Effects: Pure.
    Failures: Cell rendering failures (UnsupportedDisplayValue, InvalidDisplayNode).
    Example: renderTeXDocument[DisplayData[CharacterTableView[g]], settings]["Body"] contains a longtable.
    Remarks: Numerical data are marked approximate in the legend; the omega legend appears once when used and
        DefineOmega is True; IDs share a prefix stated in the legend.
    See also: ToLaTeX; renderTeXTable.
*)
renderTeXDocument[data_Association, settings_Association] := Module[{caption, label, spec, nodes, legend, table, prefix, deps},
    caption = Replace[renderTeXNode[data["Caption"], settings], s_String :> If[data["Caption"]["Kind"] === "Text",
        texAssignmentWords[texPaperTitle[escapeTeXText[data["Caption"]["Text"]], Lookup[data, "Group", <||>], settings],
            Lookup[Lookup[data, "Group", <||>], "Assignment", Missing[]]], s]];
    label = Lookup[settings, Label, None];
    If[KeyExistsQ[$DisplayKindRegistry, data["Kind"]], Return[renderRegisteredTeX[data, settings, caption, label]]];
    spec = Switch[data["Kind"],
        "CharacterTable", Module[{ids = idPrefix[data["IrrepIDs"]], header},
            prefix = If[displayColumn[data, "IDs"] || !KeyExistsQ[data, "IrrepNames"], ids[[1]], ""];
            header = texIrrepNameHeader[data];
            <|"FixedShare" -> 0.18, "Fixed" -> header,
                "Columns" -> MapThread[Function[{word, size, order, name},
                    "$\\begin{smallmatrix}" <> If[name === None, texWord[word], labelTeX[name["Record"]]] <> "\\\\ " <> ToString[size] <> "\\\\ " <> ToString[order] <> "\\end{smallmatrix}$"],
                    {data["ClassWords"], data["ClassSizes"], data["ClassOrders"], Lookup[data, "ClassNames", ConstantArray[None, Length[data["ClassIDs"]]]]}],
                "Rows" -> MapThread[Function[{id, short, values}, <|"Kind" -> "Row", "Fixed" -> texIrrepNameCells[data, id, short],
                    "Cells" -> (scalarDisplayNode /@ values)|>], {data["IrrepIDs"], ids[[2]], data["Values"]}]|>],
        "RepresentationTable", Module[{ids = idPrefix[data["IrrepIDs"]], header, status = displayColumn[data, "Status"]},
            prefix = If[displayColumn[data, "IDs"] || !KeyExistsQ[data, "IrrepNames"], ids[[1]], ""];
            header = texIrrepNameHeader[data];
            (* Status and basis texts wrap in paragraph columns, so the fixed share is bounded. *)
            <|"FixedShare" -> If[status, 0.55, 0.3], "FixedSpec" -> Join[ConstantArray["l", Length[header]], {"c"},
                    If[status, {">{\\raggedright\\arraybackslash}p{0.1\\linewidth}", ">{\\raggedright\\arraybackslash}p{0.12\\linewidth}"}, {}]],
                "Fixed" -> Join[header, {"Dim."}, If[status, {"Status", "Basis"}, {}]], "Columns" -> (matrixColumnHeader /@ data["MatrixSet"]["Columns"]),
                "Rows" -> MapThread[Function[{row, short}, <|"Kind" -> "Row", "Fixed" -> Join[texIrrepNameCells[data, row["IrrepID"], short],
                        {ToString[row["Dimension"]]}, If[status, {escapeTeXText[row["Status"]], "\\footnotesize " <> escapeTeXText[rowBasisText[row]]}, {}]],
                    "Cells" -> If[ListQ[row["Matrices"]], matrixDisplayNode /@ row["Matrices"],
                        ConstantArray[textNode["--"], Length[data["MatrixSet"]["Columns"]]]]|>], {data["Rows"], ids[[2]]}]|>],
        "Representation", prefix = "";
            <|"FixedShare" -> 0.3, "FixedSpec" -> Join[{"l", "c"}, If[displayColumn[data, "Status"], {">{\\raggedright\\arraybackslash}p{0.12\\linewidth}"}, {}]],
                "Fixed" -> Join[{"Label", "Dim."}, If[displayColumn[data, "Status"], {"Validation"}, {}]], "Columns" -> (matrixColumnHeader /@ data["MatrixSet"]["Columns"]),
                "Rows" -> {<|"Kind" -> "Row", "Fixed" -> Join[{representationViewLabel[data], ToString[data["Dimension"]]},
                    If[displayColumn[data, "Status"], {"\\footnotesize " <> escapeTeXText[validationText[data]]}, {}]],
                    "Cells" -> (matrixDisplayNode /@ data["Matrices"])|>}|>,
        "TensorDecomposition", prefix = "";
            Module[{label},
                label[id_] := With[{node = data["Labels"][id]},
                    If[node["Kind"] === "Text", "\\text{" <> escapeTeXText[node["Text"]] <> "}", renderTeXNode[node, settings]]];
                <|"FixedShare" -> 0.35, "Alignment" -> "p", "Fixed" -> {"Product", "Dim."}, "Columns" -> {"Decomposition"},
                    "Rows" -> Map[<|"Kind" -> "Row", "Fixed" -> {"$" <> If[#["Factors"] === {}, "\\mathbf{1}",
                            StringRiffle[label /@ #["Factors"], " \\otimes "]] <> "$", ToString[#["Dimension"]]},
                        "Cells" -> {"$" <> StringRiffle[Map[Function[c, If[c["Multiplicity"] > 1, ToString[c["Multiplicity"]] <> "\\cdot ", ""] <> label[c["IrrepID"]]],
                            #["Constituents"]], " \\oplus "] <> "$"}|> &, data["Products"]]|>],
        "GroupSummary", prefix = "";
            <|"FixedShare" -> 0.3, "Alignment" -> "p", "Fixed" -> {"Field"}, "Columns" -> {"Value"},
                "Rows" -> Map[<|"Kind" -> "Row", "Fixed" -> {escapeTeXText[First[#]]},
                    "Cells" -> {If[First[#] === "Modular assignment",
                        texAssignmentWords[escapeTeXText[Last[#]], Lookup[data["Group"], "Assignment", Missing[]]], textNode[Last[#]]]}|> &,
                    groupSummaryLines[data]]|>];
    nodes = Flatten[Join[spec["Fixed"], spec["Columns"], Flatten[{#["Fixed"], #["Cells"]} & /@ spec["Rows"]]]];
    If[!FreeQ[nodes, _Failure], Return[FirstCase[nodes, _Failure, Null, Infinity]]];
    deps = DeleteDuplicates[Flatten[texDependencies /@ Select[nodes, AssociationQ]]];
    (* The document table is a registered Table node rendered through the registry. *)
    table = renderTeXNode[Join[<|"Kind" -> "Table", "Alignment" -> "c"|>, spec, <|"Caption" -> caption, "Label" -> label|>], settings];
    If[FailureQ[table], Return[table]];
    legend = Join[
        If[prefix =!= "", {"Irrep IDs are \\texttt{" <> escapeTeXText[prefix] <> "}\\emph{n} for the listed \\texttt{n}."}, {}],
        If[data["Kind"] === "CharacterTable", {"Class columns show a representative word, the class size and the element order."}, {}],
        If[MemberQ[deps, "OmegaLegend"] && Lookup[settings, ScalarNotation, "Standard"] === "Omega" && TrueQ[Lookup[settings, DefineOmega, True]],
            {"$\\omega_a^b \\equiv " <> exponentialBaseTeX[settings] <> "^{2\\pi " <> imaginaryUnitTeX[settings] <> "\\, b/a}$."}, {}],
        If[MemberQ[deps, "RootLegend"], {"$\\mathrm{Root}(p,k)$ is the $k$-th root of $p$ in Wolfram's root ordering (real roots ascending, then complex roots)."}, {}],
        If[MemberQ[deps, "NumericalLegend"] || Lookup[data, "Arithmetic", "Exact"] === "Numerical",
            {"Numerical entries are approximate" <> If[IntegerQ[Lookup[settings, Digits, Automatic]], " (" <> ToString[settings[Digits]] <> " digits shown)", ""] <> "."}, {}],
        If[data["Kind"] === "RepresentationTable" && displayColumn[data, "Status"] && AnyTrue[data["Rows"], #["Status"] =!= "Complete" &],
            {"Rows without completed matrices show their status; accepted partial matrices are not shown as completed."}, {}],
        escapeTeXText /@ statusLegend[data], escapeTeXText /@ irrepNameLegend[data]];
    <|"Body" -> table <> If[legend === {}, "", "\n\n\\noindent{\\small " <> StringRiffle[legend, " "] <> "}"], "Dependencies" -> deps|>
];

(*
    Summary: The LaTeX body of a document of a registered (later-stage) kind.
    Parameters: data — validated document data; settings — render settings; caption — rendered caption; label —
        LaTeX label or None.
    Options/defaults: None.
    Returns: <|"Body" -> string, "Dependencies" -> tags|>, or Failure.
    Effects: Pure.
    Failures: Cell rendering failures.
    Example: a ModelView renders its field, term and parameter tables, each a longtable with the document caption
        and its part title.
    Remarks: Every table goes through the shared Table node (panels, width limits, repeated headers); the legend
        joins the kind's own lines with the shared numerical, omega and Root legends.
    See also: registerDisplayKind; renderTeXTable.
*)
renderRegisteredTeX[data_Association, settings_Association, caption_String, label_] := Module[{specs, nodes, deps, tables, legend},
    specs = $DisplayKindRegistry[data["Kind"]]["TeX"][data, settings];
    If[FailureQ[specs], Return[specs]];
    nodes = Flatten[Map[Join[#["Fixed"], #["Columns"], Flatten[{#["Fixed"], #["Cells"]} & /@ #["Rows"]]] &, specs["Tables"]]];
    If[!FreeQ[nodes, _Failure], Return[FirstCase[nodes, _Failure, Null, Infinity]]];
    deps = DeleteDuplicates[Flatten[texDependencies /@ Select[nodes, AssociationQ]]];
    tables = MapIndexed[Function[{spec, index}, renderTeXNode[Join[<|"Kind" -> "Table", "Alignment" -> "c"|>, KeyDrop[spec, "Title"],
        <|"Caption" -> caption <> If[StringQ[Lookup[spec, "Title", None]], " (" <> escapeTeXText[spec["Title"]] <> ")", ""],
            "Label" -> If[First[index] === 1, label, None]|>], settings]], specs["Tables"]];
    If[AnyTrue[tables, FailureQ], Return[FirstCase[tables, _Failure]]];
    legend = Join[escapeTeXText /@ Lookup[specs, "Legend", {}],
        If[MemberQ[deps, "OmegaLegend"] && Lookup[settings, ScalarNotation, "Standard"] === "Omega" && TrueQ[Lookup[settings, DefineOmega, True]],
            {"$\\omega_a^b \\equiv " <> exponentialBaseTeX[settings] <> "^{2\\pi " <> imaginaryUnitTeX[settings] <> "\\, b/a}$."}, {}],
        If[MemberQ[deps, "RootLegend"], {"$\\mathrm{Root}(p,k)$ is the $k$-th root of $p$ in Wolfram's root ordering (real roots ascending, then complex roots)."}, {}],
        If[MemberQ[deps, "SurdLegend"], {"$\\sqrt[n]{x}$ denotes the real $n$-th root of a real $x$; other fractional powers are principal values."}, {}],
        If[MemberQ[deps, "NumericalLegend"], {"Numerical entries are approximate" <> If[IntegerQ[Lookup[settings, Digits, Automatic]],
            " (" <> ToString[settings[Digits]] <> " digits shown)", ""] <> "."}, {}]];
    <|"Body" -> StringRiffle[tables, "\n\n"] <> If[legend === {}, "", "\n\n\\noindent{\\small " <> StringRiffle[legend, " "] <> "}"], "Dependencies" -> deps|>
];

(*
    Summary: Math-mode LaTeX of a group word given as display text ("S^3.T.S.T").
    Parameters: text — word text from wordText.
    Options/defaults: None.
    Returns: String such as "\\mathrm{S}^{3}\\mathrm{T}\\mathrm{S}\\mathrm{T}" ("1" for the identity).
    Effects: Pure.
    Failures: None.
    Example: texWord["S.T^-1"] is "\\mathrm{S}\\mathrm{T}^{-1}".
    See also: wordText.
*)
texWord[text_String] := If[text === "1", "1", StringJoin[Map[Function[token, With[{parts = StringSplit[token, "^"]},
    "\\mathrm{" <> escapeTeXText[First[parts]] <> "}" <> If[Length[parts] > 1, "^{" <> escapeTeXText[parts[[2]]] <> "}", ""]]],
    StringSplit[text, "."]]]];

(*
    Summary: Set the assignment words of an escaped caption or summary text in math.
    Parameters: escaped — text already passed through escapeTeXText; assignment — the document's assignment
        (<|"SText", "TText", ...|>) or Missing.
    Options/defaults: None.
    Returns: The text with the exact escaped substring "S = <S word>, T = <T word>" replaced by
        "$S = <texWord>$, $T = <texWord>$"; unchanged without an assignment.
    Effects: Pure.
    Failures: None.
    Example: with S = "t^-1.s.t" the caption shows $S = \mathrm{t}^{-1}\mathrm{s}\mathrm{t}$ instead of "t\textasciicircum{}-1.s.t".
    Remarks: Only the substring the caption and summary producers wrote is replaced, so no other text changes.
    See also: formatGroupCaption; groupSummaryLines; texWord.
*)
texAssignmentWords[escaped_String, assignment_] := If[!AssociationQ[assignment], escaped,
    StringReplace[escaped, "S = " <> escapeTeXText[assignment["SText"]] <> ", T = " <> escapeTeXText[assignment["TText"]] ->
        "$S = " <> texWord[assignment["SText"]] <> "$, $T = " <> texWord[assignment["TText"]] <> "$"]];

(*
    Summary: The LaTeX header of a matrix column: rho(name), with the assigned word when it differs from the name.
    Parameters: column — <|"Name", "Word" (text) or "Index"|>.
    Options/defaults: None.
    Returns: String (math mode).
    Effects: Pure.
    Failures: None.
    Example: matrixColumnHeader[<|"Name" -> "S", "Word" -> "a.b^-1"|>] is "$\\rho(\\text{S})$ = $\\mathrm{a}\\mathrm{b}^{-1}$".
    Remarks: The name is text inside math and the word is set by texWord, so no text-mode escape reaches math mode.
    See also: texWord; renderTeXDocument.
*)
matrixColumnHeader[column_Association] := "$\\rho(\\text{" <> escapeTeXText[column["Name"]] <> "})$" <>
    If[KeyExistsQ[column, "Word"] && column["Word"] =!= column["Name"], " = $" <> texWord[column["Word"]] <> "$", ""];

(*
    Summary: Short text of a representation row's basis: properties, tier and arithmetic (active or pending partial).
    Parameters: row — RepresentationTable row.
    Options/defaults: None.
    Returns: String.
    Effects: Pure.
    Failures: None.
    Example: a unitary T-diagonal native exact row gives "unitary, T-diagonal; Native, Exact"; an unverified one adds
        "; unverified".
    See also: renderTeXDocument; notebookTableParts.
*)
rowBasisText[row_Association] := Module[{describe},
    describe[properties_, tier_, arithmetic_] := If[AssociationQ[properties],
        StringRiffle[Join[{If[TrueQ[properties["Unitary"]], "unitary", "general"]}, If[TrueQ[Lookup[properties, "TDiagonal", False]], {"T-diagonal"}, {}]], ", "] <>
            If[tier === "Numerical", " (numerical); Numerical tier", "; " <> ToString[tier] <> ", " <> ToString[arithmetic]], "--"];
    Which[StringQ[row["ActiveVariant"]], describe[row["BasisProperties"], row["Tier"], row["Arithmetic"]] <>
            (* a variant that is not exactly verified says so (methodOptionsPlan.md 2C.3); a numerical tier already does *)
            Switch[Lookup[row, "VerificationStatus", "Exact"], "Unverified", "; unverified",
                "Numerical", If[row["Tier"] === "Numerical", "", "; numerically verified"], _, ""],
        AssociationQ[row["Partial"]], "partial " <> describe[row["Partial"]["BasisProperties"], row["Partial"]["Tier"], row["Partial"]["Arithmetic"]],
        True, "--"]
];

(*
    Summary: Short text of a representation view's validation evidence.
    Parameters: data — Representation document data.
    Options/defaults: None.
    Returns: String such as "Stored variant (irrep 7)" or "Unvalidated".
    Effects: Pure.
    Failures: None.
    Example: validationText[DisplayData[RepresentationView[r]]] is "Unvalidated".
    See also: renderTeXDocument.
*)
validationText[data_Association] := With[{v = data["Validation"]}, v["Status"] <>
    If[StringQ[Lookup[v, "IrrepID", None]], " (" <> Last[StringSplit[v["IrrepID"], ":"]] <> ")", ""] <>
    If[data["Arithmetic"] === "Numerical", "; numerical", ""]];

(*
    Summary: The field/value lines of a group summary.
    Parameters: data — GroupSummary document data.
    Options/defaults: None.
    Returns: List of {field, value} strings.
    Effects: Pure.
    Failures: None.
    Example: groupSummaryLines[data][[1]] is {"Name", name}.
    See also: renderTeXDocument; renderNotebookDocument.
*)
groupSummaryLines[data_Association] := Module[{group = data["Group"], available = data["AvailableData"], reps},
    reps = Counts[Lookup[Values[data["Representations"]], "Status"]];
    Join[{{"Name", ToString[group["Name"]]}, {"Order", ToString[group["Order"]]},
        {"Catalogue ID", If[MissingQ[group["CatalogueID"]], "unavailable", ToString[group["CatalogueID"], InputForm]]},
        {"Generators", StringRiffle[group["Generators"], ", "]},
        {"Modular assignment", If[AssociationQ[group["Assignment"]], "S = " <> group["Assignment"]["SText"] <> ", T = " <> group["Assignment"]["TText"] <>
            If[displayColumn[data, "IDs"], " (" <> group["Assignment"]["Identity"] <> ")", ""], "none (not a modular realization)"]}},
        KeyValueMap[{"Availability: " <> #1, availabilityText[#2]} &, available],
        {{"Representations", StringRiffle[KeyValueMap[#1 <> ": " <> ToString[#2] &, reps], "; "] <>
            If[data["RequestedBasis"] === Automatic, "", " (compared with basis " <> data["RequestedBasis"] <> ")"]},
            {"GAP state", data["GAPCache"]["State"] <> " -- " <> data["GAPCache"]["Reason"] <> " (observed " <> data["GAPCache"]["ObservedAt"] <> ")"}}]
];
(*
    Summary: Readable text of an AvailableData status: a status string, a list of subgroup queries or a query association.
    Parameters: status — string, list or association.
    Options/defaults: None.
    Returns: String.
    Effects: Pure.
    Failures: None.
    Example: availabilityText[{}] is "no queries".
    See also: groupSummaryLines.
*)
availabilityText[s_String] := s;
availabilityText[{}] := "no queries";
availabilityText[l_List] := StringRiffle[availabilityText /@ l, "; "];
availabilityText[a_Association] := StringRiffle[KeyValueMap[#1 <> " " <> availabilityText[#2] &, a], ", "];
availabilityText[other_] := ToString[other];

Options[ToLaTeX] = {ScalarNotation -> Automatic, NotationStyle -> Automatic, OneByOneMatrix -> Automatic, DefineOmega -> Automatic,
    Digits -> Automatic, Caption -> Automatic, Label -> Automatic, Standalone -> False};

(*
    Summary: Render a display document to LaTeX.
    Status: Alpha.
    Parameters: v — DisplayDocument.
    Options/defaults: ScalarNotation, NotationStyle, OneByOneMatrix, DefineOmega, Digits, Caption, Label ->
        Automatic (the document's saved presentation defaults; explicit values override them); Standalone ->
        False (a table fragment; LaTeXPreamble gives its dependencies) or True (a complete document).
    Returns: String, or Failure.
    Effects: Pure; nothing is compiled or executed.
    Failures: InvalidDisplayDocument; InvalidOption (including a label outside letters, digits, ":", "-", "_");
        UnsupportedDisplayValue.
    Example: StringStartsQ[ToLaTeX[CharacterTableView[g], Standalone -> True], "\\documentclass"] is True.
    Remarks: Renderer settings cannot change which rows or matrices the document holds.
    See also: LaTeXPreamble; ExportDisplay; ToNotebook.
*)
ToLaTeX[document_DisplayDocument, options : OptionsPattern[]] := Module[{data, settings, rendered},
    data = validateDisplayDocument[document]; If[FailureQ[data], Return[data]];
    settings = displayRenderSettings[ToLaTeX, "ToLaTeX", data, {options}]; If[FailureQ[settings], Return[settings]];
    rendered = renderTeXDocument[If[settings[Caption] =!= Automatic,
        Join[data, <|"Caption" -> If[StringQ[settings[Caption]], textNode[settings[Caption]], labelNode[settings[Caption]]]|>], data], settings];
    If[FailureQ[rendered], Return[rendered]];
    If[TrueQ[settings[Standalone]],
        "\\documentclass{article}\n\\usepackage[margin=2cm]{geometry}\n" <> texPreamble[settings] <> "\n\\begin{document}\n" <>
            rendered["Body"] <> "\n\\end{document}\n",
        rendered["Body"]]
];
ToLaTeX[___] := makeFailure["InvalidInput", "ToLaTeX expects a DisplayDocument and options."];

(*
    Summary: Effective render settings: explicit renderer options over the document's saved presentation defaults.
    Parameters: head — renderer symbol; operation — option schema name; data — document data; options — rules.
    Options/defaults: Renderer options left Automatic take the document's value.
    Returns: Settings association, or Failure.
    Effects: Pure.
    Failures: InvalidOption; UnknownOption.
    Example: ToLaTeX[v, ScalarNotation -> "Omega"] overrides the view's saved "Standard".
    See also: ToLaTeX; ToNotebook; ExportDisplay.
*)
displayRenderSettings[head_Symbol, operation_String, data_Association, options_List] := Module[{effective, saved},
    effective = resolveOperationOptions[head, operation, options]; If[FailureQ[effective], Return[effective]];
    saved = data["Presentation"];
    Association[KeyValueMap[#1 -> If[#2 === Automatic && KeyExistsQ[saved, #1] && #1 =!= Caption, saved[#1], #2] &, effective]] //
        Join[#, <|Caption -> Replace[#[Caption], Automatic -> Automatic]|>] &
];


(*
    Summary: The TeX irrep columns of a table of representations (index, automatic label, user label, ID on request).
    Parameters: data — document data; id — irrep ID; short — the ID's short form.
    Options/defaults: None.
    Returns: texIrrepNameHeader: header strings; texIrrepNameCells: the fixed cells of one row (strings and label nodes).
    Effects: Pure.
    Failures: None.
    Example: a T' table without user labels has the header {"Index", "Label"}.
    See also: irrepNameHeader; irrepPresentation.
*)
texIrrepNameHeader[data_Association] := If[!KeyExistsQ[data, "IrrepNames"], {"ID", "Label"},
    Join[{"Index"}, If[displayColumn[data, "Auto"], {"Label"}, {}], If[displayColumn[data, "User"], {"Name"}, {}], If[displayColumn[data, "IDs"], {"ID"}, {}]]];
texIrrepNameCells[data_Association, id_String, short_String] := If[!KeyExistsQ[data, "IrrepNames"],
    {"\\texttt{" <> escapeTeXText[short] <> "}", data["Labels"][id]},
    With[{n = data["IrrepNames"][id]}, Join[{ToString[n["Index"]]},
        If[displayColumn[data, "Auto"], {If[n["Auto"] === None, "", n["Auto"]]}, {}],
        If[displayColumn[data, "User"], {If[n["User"] === None, "", n["User"]]}, {}],
        If[displayColumn[data, "IDs"], {"\\texttt{" <> escapeTeXText[short] <> "}"}, {}]]]];

True
