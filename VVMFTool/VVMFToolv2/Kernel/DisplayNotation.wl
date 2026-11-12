(*
    :Title: Display notation: scalar, phase, root and matrix nodes
    :Context: VVMFTool`Private`
    :Summary: Structured display nodes for exact and numerical values; the values themselves are never
        changed, rounded or rationalized.
    :Responsibilities:
        - scalarDisplayNode: integers/rationals, certified roots of unity (Phase nodes, with a rational
          magnitude), radical expressions, algebraic roots with a defining polynomial, numerical values.
        - matrixDisplayNode: shape-checked matrices of scalar nodes.
        - Registration of the Stage 3 node kinds (Text, RawTeX, Scalar, Phase, Matrix, IrrepLabel, Table).
    :Dependencies: Diagnostics.wl; DisplayLabels.wl (certifiedRootOfUnityPhase); DisplayData.wl (registry);
        NotebookDisplay.wl and LaTeXDisplay.wl (renderers named by the registry).
    :See Also: VVMFArch/step3Plan.md (notation contracts).
*)

(*
    Summary: The display node of one scalar.
    Parameters: x — exact number or approximate number.
    Options/defaults: None.
    Returns: A Scalar node <|"Kind" -> "Scalar", "Value" -> x, "Form" -> "Rational" | "Radical" | "Root" |
        "Numerical", ...|> or a Phase node <|"Kind" -> "Phase", "Value" -> x, "Phase" -> r, "Magnitude" -> m|>
        (x = m Exp[2 Pi I r], m a positive rational, r a certified rational in [0, 1)); or UnsupportedDisplayValue
        Failure.
    Effects: Pure.
    Failures: Non-numeric or non-algebraic exact values (for example Pi).
    Example: scalarDisplayNode[Exp[2 Pi I/3]]["Phase"] is 1/3; scalarDisplayNode[Surd[-1, 3]] is the rational -1.
    Remarks: A phase is recognized only when exact equality certifies it; "Radical" keeps the exact radical form
        (entries keep their parentheses when rendered); other algebraic numbers use Root notation with their
        minimal polynomial and root index, explained in a legend.
    See also: phaseDisplayNode; matrixDisplayNode; algebraicRootLabel.
*)
(* complete results are memoized (review F19); a node computed after the budget ran out is not *)
$ScalarNodeMemo = <||>;
scalarDisplayNode[x_] := With[{key = {x, readableConductors[]}}, If[KeyExistsQ[$ScalarNodeMemo, key], $ScalarNodeMemo[key],
    Block[{$ReadableBudgetHit = False}, With[{node = scalarDisplayNodeCompute[x]},
        If[!TrueQ[$ReadableBudgetHit] && !FailureQ[node], If[Length[$ScalarNodeMemo] >= 20000, $ScalarNodeMemo = <||>]; AssociateTo[$ScalarNodeMemo, key -> node]];
        node]]]];
scalarDisplayNodeCompute[x_] := Module[{value = x, magnitude, phase, radical},
    Which[
        MatchQ[value, _Integer | _Rational], <|"Kind" -> "Scalar", "Value" -> value, "Form" -> "Rational"|>,
        NumericQ[value] && Precision[value] =!= Infinity,
            <|"Kind" -> "Scalar", "Value" -> value, "Form" -> "Numerical", "Precision" -> Precision[value]|>,
        !exactAlgebraicQ[value], makeFailure["UnsupportedDisplayValue", "Only exact algebraic numbers and numerical values are displayed.",
            <|"Value" -> value|>],
        (* degree above 8: the certified roots-of-unity sum first (readableScalar's order) *)
        algebraicDegree[value] > 8 && ListQ[withReadableBudget[cyclotomicTerms[value, readableConductors[]], 3]],
            <|"Kind" -> "Scalar", "Value" -> value, "Form" -> "Cyclotomic", "Terms" -> withReadableBudget[cyclotomicTerms[value, readableConductors[]], 3]|>,
        True,
            magnitude = RootReduce[Abs[value]];
            phase = If[MatchQ[magnitude, _Integer | _Rational] && magnitude > 0,
                certifiedRootOfUnityPhase[RootReduce[value/magnitude]], $Failed];
            If[MatchQ[phase, _Integer | _Rational] && phase =!= 0 && phase =!= 1/2,
                Return[<|"Kind" -> "Phase", "Value" -> value, "Phase" -> phase, "Magnitude" -> magnitude|>]];
            radical = displayRadical[value];
            If[radical =!= $Failed, Return[<|"Kind" -> "Scalar", "Value" -> value, "Form" -> "Radical", "Expression" -> radical|>]];
            (* no radical form: a certified sum of roots of unity when the value is cyclotomic (uxUpdatePlan.md 3) *)
            With[{terms = withReadableBudget[cyclotomicTerms[value, readableConductors[]], 3]},
                If[terms =!= $Failed, <|"Kind" -> "Scalar", "Value" -> value, "Form" -> "Cyclotomic", "Terms" -> terms|>,
                    algebraicRootLabel[value]]]]
];

(*
    Summary: An exact radical expression equal to an algebraic number, or $Failed.
    Parameters: x — exact algebraic number.
    Options/defaults: None.
    Returns: Expression free of Root objects and of principal powers of negative numbers, or $Failed.
    Effects: Pure.
    Failures: $Failed when no such form is found or equality cannot be certified.
    Example: displayRadical[Root[#^2 - 2 &, 2]] is Sqrt[2].
    Remarks: Complex values are written a + b I with real radical parts (ComplexExpand, or the radicals of the real and
        imaginary parts found separately), so no branch of a root of -1 is ever implied. The searches stay within the
        caller's readable budget ($ReadableDeadline) when one is set.
    See also: scalarDisplayNode.
*)
displayRadical[x_] := Module[{attempt, limit},
    (* The given form first (when it is already radicals), then the radicals of its real and imaginary parts (a + I b:
       e.g. Root[49 + 60 #^2 + 900 #^4 &, 2] is -1/Sqrt[10] + I Sqrt[2/15], whose radicals as one root are nested complex
       ones), then radicals of the canonical root; only pure radical expressions (Plus, Times, Power, Complex, Rational)
       whose equality is certified are accepted. Candidates are built lazily (Hold) so a found form stops the search. *)
    (* each search's limit: 5 s, or what is left of the caller's readable budget (review N1) *)
    limit[] := If[NumericQ[$ReadableDeadline], Min[5, Max[0.1, $ReadableDeadline - AbsoluteTime[]]], 5];
    attempt[candidate_] := If[radicalExpressionQ[candidate] &&
        Quiet[TimeConstrained[RootReduce[candidate - x], 5, $Failed]] === 0, candidate, $Failed];
    Catch[
        Scan[With[{c = attempt[ReleaseHold[#]]}, If[c =!= $Failed, Throw[c, displayRadical]]] &,
            {Hold[Quiet[ComplexExpand[x]]], Hold[x],
                Hold[Quiet[TimeConstrained[ToRadicals[RootReduce[Re[x]]] + I ToRadicals[RootReduce[Im[x]]], limit[], $Failed]]],
                Hold[Quiet[TimeConstrained[ComplexExpand[ToRadicals[RootReduce[x]]], limit[], $Failed]]]}];
        $Failed, displayRadical]
];

(*
    Summary: Whether an exact expression is built from radicals only.
    Parameters: e — expression.
    Options/defaults: None.
    Returns: Boolean.
    Effects: Pure.
    Failures: None.
    Example: radicalExpressionQ[(1 + Sqrt[5])/2] is True; radicalExpressionQ[Cos[Pi/7]] is False.
    Remarks: Fractional powers of negative or complex numbers are refused, so no branch choice is implied.
    See also: displayRadical.
*)
radicalExpressionQ[e_] := NumericQ[e] && FreeQ[e, Root | Surd | Pi | E | Degree | _Real] &&
    AllTrue[Cases[e, _[___], {0, Infinity}], MemberQ[{Plus, Times, Power, Complex, Rational}, Head[#]] &] &&
    (* Fractional powers only of positive real bases: no branch of a root of a negative or complex number. *)
    FreeQ[e, Power[b_, _Rational] /; !(NumericQ[b] && TrueQ[Im[b] == 0] && TrueQ[b > 0])];

(*
    Summary: The Root-notation node of an algebraic number without a usable radical form.
    Parameters: x — exact algebraic number.
    Options/defaults: None.
    Returns: <|"Kind" -> "Scalar", "Value" -> x, "Form" -> "Root", "Polynomial" -> integer coefficients (lowest
        degree first), "Index" -> k|> (x = Root[polynomial, k]).
    Effects: Pure.
    Failures: None for algebraic numbers.
    Example: algebraicRootLabel[Root[#^5 - # - 1 &, 1]]["Index"] is 1.
    Remarks: The defining polynomial and Wolfram's root index are explained in the rendered legend.
    See also: scalarDisplayNode.
*)
algebraicRootLabel[x_] := Module[{reduced = RootReduce[x], variable, polynomial},
    polynomial = If[Head[reduced] === Root, reduced[[1]][variable], MinimalPolynomial[reduced, variable]];
    <|"Kind" -> "Scalar", "Value" -> x, "Form" -> "Root",
        "Polynomial" -> CoefficientList[polynomial, variable] * Denominator[Together[polynomial]],
        "Index" -> If[Head[reduced] === Root, reduced[[2]], 1]|>
];

(*
    Summary: The display node of a certified root of unity with a rational magnitude.
    Parameters: x — exact number.
    Options/defaults: None.
    Returns: A Phase node, or $Failed when x is not m Exp[2 Pi I r] with certified rational m > 0 and r.
    Effects: Pure.
    Failures: $Failed.
    Example: phaseDisplayNode[-Exp[2 Pi I/3]]["Phase"] is 5/6.
    See also: scalarDisplayNode.
*)
phaseDisplayNode[x_] := With[{node = scalarDisplayNode[x]}, If[AssociationQ[node] && node["Kind"] === "Phase", node, $Failed]];

(*
    Summary: The display node of a matrix.
    Parameters: m — rectangular list of lists of displayable scalars.
    Options/defaults: None.
    Returns: <|"Kind" -> "Matrix", "Dimensions" -> {r, c}, "Cells" -> scalar nodes|>, or Failure.
    Effects: Pure.
    Failures: InvalidMatrix (ragged or empty input); UnsupportedDisplayValue.
    Example: matrixDisplayNode[{{1, 0}, {0, -1}}]["Dimensions"] is {2, 2}.
    Remarks: A 1 x 1 matrix stays a matrix node; OneByOneMatrix -> "Scalar" is a rendering choice.
    See also: scalarDisplayNode; MatrixLaTeX.
*)
matrixDisplayNode[m_List] := Module[{cells},
    If[!MatrixQ[m, NumericQ] || m === {} || First[m] === {},
        Return[makeFailure["InvalidMatrix", "Expected a rectangular numeric matrix."]]];
    cells = Map[scalarDisplayNode, m, {2}];
    If[!FreeQ[cells, _Failure], Return[FirstCase[cells, _Failure, Null, Infinity]]];
    <|"Kind" -> "Matrix", "Dimensions" -> Dimensions[m], "Cells" -> cells|>
];
matrixDisplayNode[_] := makeFailure["InvalidMatrix", "Expected a rectangular numeric matrix."];

(* -------------------------------------------------------------------------
   Node registration (Stage 3 kinds)
   ------------------------------------------------------------------------- *)

registerDisplayNode["Text", <|"Validate" -> (StringQ[Lookup[#, "Text", None]] &),
    "Notebook" -> notebookTextNode, "TeX" -> texTextNode, "Dependencies" -> ({} &)|>];
registerDisplayNode["RawTeX", <|"Validate" -> (StringQ[Lookup[#, "TeX", None]] && StringQ[Lookup[#, "Fallback", None]] &),
    "Notebook" -> notebookRawTeXNode, "TeX" -> texRawTeXNode, "Dependencies" -> ({} &)|>];
registerDisplayNode["Scalar", <|"Validate" -> (NumericQ[Lookup[#, "Value", None]] &&
        MemberQ[{"Rational", "Radical", "Cyclotomic", "Root", "Numerical"}, Lookup[#, "Form", None]] &&
        (#["Form"] =!= "Cyclotomic" || MatchQ[Lookup[#, "Terms", None], {{_Integer | _Rational, _Integer | _Rational} ..}]) &),
    "Notebook" -> notebookScalarNode, "TeX" -> texScalarNode, "Dependencies" -> texScalarDependencies|>];
registerDisplayNode["Phase", <|"Validate" -> (MatchQ[Lookup[#, "Phase", None], _Integer | _Rational] &&
        MatchQ[Lookup[#, "Magnitude", None], _Integer | _Rational] &),
    "Notebook" -> notebookPhaseNode, "TeX" -> texPhaseNode, "Dependencies" -> texPhaseDependencies|>];
registerDisplayNode["Matrix", <|"Validate" -> (MatchQ[Lookup[#, "Dimensions", None], {_Integer, _Integer}] &&
        Dimensions[Lookup[#, "Cells", {}], 2] === #["Dimensions"] && AllTrue[Flatten[#["Cells"]], displayNodeQ] &),
    "Notebook" -> notebookMatrixNode, "TeX" -> texMatrixNode, "Dependencies" -> texMatrixDependencies|>];
registerDisplayNode["IrrepLabel", <|"Validate" -> (IntegerQ[Lookup[#, "Dimension", None]] &&
        (#["Phases"] === None || MatchQ[#["Phases"], {(_Integer | _Rational) ..}]) &),
    "Notebook" -> notebookIrrepLabelNode, "TeX" -> texIrrepLabelNode, "Dependencies" -> texIrrepLabelDependencies|>];
registerDisplayNode["ClassLabel", <|"Validate" -> (classLabelRecordQ[Lookup[#, "Record", None]] &),
    "Notebook" -> (labelBoxes[#1["Record"]] &), "TeX" -> ("$" <> labelTeX[#1["Record"]] <> "$" &), "Dependencies" -> ({} &)|>];
(* A user-assigned irrep label (uxUpdatePlan.md 1.5): one record, rendered as boxes or TeX. *)
registerDisplayNode["UserLabel", <|"Validate" -> (irrepLabelRecordQ[Lookup[#, "Record", None]] &),
    "Notebook" -> (labelBoxes[#1["Record"]] &),
    "TeX" -> (labelTeX[#1["Record"], If[Lookup[#2, NotationStyle, "Standard"] === "Paper", "Paper", "Standard"]] &),
    "Dependencies" -> ({} &)|>];

True
