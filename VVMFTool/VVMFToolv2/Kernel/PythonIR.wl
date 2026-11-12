(*
    :Title: Typed scalar expression trees and their Python lowering
    :Context: VVMFTool`Private`
    :Summary: A closed, JSON-compatible tree grammar for model scalars (exact integers, rationals, complex numbers,
        algebraic Root values, declared-precision reals, named constants, Coupling and FieldComponent references,
        Plus/Times/Power, real Surd and a fixed set of elementary functions), its exact decoding, validation, dependency
        collection, common-subexpression extraction and lowering to NumPy or mpmath source.
    :Responsibilities: encodeScalarTree, decodeScalarTree, validateScalarTree, scalarTreeDependencies,
        scalarTreePrecision, pythonCommonSubexpressions, lowerPythonTree.
    :Dependencies: ScalarCodec.wl (encodeInteger, decodeInteger, decodeRational); RepresentationStorage.wl
        (encodeAlgebraic, decodeAlgebraic, decimalRecord, nearestMachineReal).
    :See Also: VVMFArch/step6Plan.md (typed expression compiler); VVMFArch/implementation/step6Status.md (D-S6-2, D-S6-5).
*)

(* Elementary functions of one argument the grammar accepts, by Wolfram head; names are the tree's function tags. *)
$ScalarTreeFunctions = <|Log -> "Log", Sin -> "Sin", Cos -> "Cos", Tan -> "Tan", Sinh -> "Sinh", Cosh -> "Cosh", Tanh -> "Tanh",
    Abs -> "Abs", Conjugate -> "Conjugate", Re -> "Re", Im -> "Im"|>;
$ScalarTreeConstants = <|Pi -> "Pi", E -> "E", EulerGamma -> "EulerGamma", Catalan -> "Catalan"|>;

(*
    Summary: Encode a scalar expression as a typed tree node.
    Parameters: expr — evaluated Wolfram expression; registry — <|"Parameters" -> list of Coupling IDs, "Fields" ->
        <|field ID -> dimension|>|>, optionally "Slots" -> <|form slot ID -> dimension|> (Stage 9: modular models).
    Options/defaults: None.
    Returns: Node association (JSON-compatible: strings, lists, associations), or Failure.
    Effects: Pure.
    Failures: UnsupportedExpression (a head outside the grammar, with "Path" and "Head"); UndeclaredAtom (a symbol,
        or a Coupling/FieldComponent/FormComponent not in the registry); NonfiniteConstant (Infinity, Indeterminate, ComplexInfinity);
        UnsupportedScalar (an algebraic value the codec cannot isolate).
    Example: encodeScalarTree[Sqrt[3] Coupling["c"], <|"Parameters" -> {"c"}, "Fields" -> <||>|>]["node"] is "times".
    Remarks: The tree follows the expression's own structure (Sqrt[3] stays Power[3, 1/2]), so decodeScalarTree
        reproduces it SameQ; exact numbers are never replaced by RootReduced values (D-S6-2). A Root object is
        encoded by its minimal polynomial and isolating rectangle; an approximate real keeps its own precision.
    See also: decodeScalarTree; validateScalarTree; lowerPythonTree.
*)
encodeScalarTree[expr_, registry_Association] := Catch[scalarTreeNode[expr, registry, {}], "scalarTree"];
encodeScalarTree[___] := makeFailure["InvalidInput", "Expected an expression and a registry."];

(*
    Summary: The tree node of one subexpression (encodeScalarTree's recursion).
    Parameters: x — subexpression; registry; path — positions from the root.
    Options/defaults: None.
    Returns: Node association; throws a Failure to the "scalarTree" tag.
    Effects: Pure.
    Failures: As encodeScalarTree.
    Example: scalarTreeNode[2, reg, {}] is <|"node" -> "integer", "value" -> "2"|>.
    See also: encodeScalarTree.
*)
scalarTreeNode[x_, registry_Association, path_List] := Module[{fail, recurse},
    fail[tag_, message_] := Throw[makeFailure[tag, message, <|"Path" -> path, "Head" -> ToString[Head[x], InputForm]|>], "scalarTree"];
    recurse[list_] := MapIndexed[scalarTreeNode[#1, registry, Append[path, First[#2]]] &, list];
    Which[
        IntegerQ[x], <|"node" -> "integer", "value" -> encodeInteger[x]|>,
        Head[x] === Rational, <|"node" -> "rational", "value" -> {encodeInteger[Numerator[x]], encodeInteger[Denominator[x]]}|>,
        Head[x] === Real, realTreeNode[x],
        Head[x] === Complex, <|"node" -> "complex", "re" -> scalarTreeNode[Re[x], registry, Append[path, 1]],
            "im" -> scalarTreeNode[Im[x], registry, Append[path, 2]]|>,
        KeyExistsQ[$ScalarTreeConstants, x], <|"node" -> "constant", "name" -> $ScalarTreeConstants[x]|>,
        MatchQ[x, DirectedInfinity[___] | Indeterminate | ComplexInfinity], fail["NonfiniteConstant", "The expression has an infinite or undefined constant."],
        Head[x] === Root, With[{record = encodeAlgebraic[x]},
            If[FailureQ[record], fail["UnsupportedScalar", "An algebraic Root value cannot be encoded exactly."],
                <|"node" -> "algebraic", "value" -> record|>]],
        MatchQ[x, Coupling[_String]], If[MemberQ[registry["Parameters"], First[x]], <|"node" -> "parameter", "id" -> First[x]|>,
            fail["UndeclaredAtom", "The expression uses a parameter that is not registered for this output."]],
        MatchQ[x, FieldComponent[_String, _Integer]], If[IntegerQ[Lookup[registry["Fields"], First[x], None]] && 1 <= Last[x] <= registry["Fields"][First[x]],
            <|"node" -> "field", "id" -> First[x], "index" -> encodeInteger[Last[x]]|>,
            fail["UndeclaredAtom", "The expression uses a field component that is not registered for this output."]],
        (* Stage 9 (D-S9-5): a form-slot component is an atom of the registry's "Slots"; a registry without slots (every
           finite-group model) rejects it as before. *)
        MatchQ[x, FormComponent[_String, _Integer]], If[IntegerQ[Lookup[Lookup[registry, "Slots", <||>], First[x], None]] && 1 <= Last[x] <= registry["Slots"][First[x]],
            <|"node" -> "form", "slot" -> First[x], "index" -> encodeInteger[Last[x]]|>,
            fail["UndeclaredAtom", "The expression uses a form-slot component that is not registered for this output."]],
        Head[x] === Plus, <|"node" -> "plus", "args" -> recurse[List @@ x]|>,
        Head[x] === Times, <|"node" -> "times", "args" -> recurse[List @@ x]|>,
        MatchQ[x, Power[_, _]], <|"node" -> "power", "base" -> scalarTreeNode[x[[1]], registry, Append[path, 1]],
            "exponent" -> scalarTreeNode[x[[2]], registry, Append[path, 2]]|>,
        MatchQ[x, Surd[_, _Integer?(# >= 2 &)]], <|"node" -> "surd", "base" -> scalarTreeNode[x[[1]], registry, Append[path, 1]],
            "n" -> encodeInteger[x[[2]]]|>,
        MatchQ[x, _[_]] && KeyExistsQ[$ScalarTreeFunctions, Head[x]],
            <|"node" -> "function", "name" -> $ScalarTreeFunctions[Head[x]], "args" -> recurse[List @@ x]|>,
        Head[x] === Symbol, fail["UndeclaredAtom", "The expression uses an undeclared symbol."],
        True, fail["UnsupportedExpression", "The expression uses an operation outside the supported scalar grammar."]]
];

(*
    Summary: The node of an approximate real number at its own precision.
    Parameters: x — Real.
    Options/defaults: None.
    Returns: <|"node" -> "real", "significand", "exponent", "precision" -> "MachinePrecision" | {numerator, denominator}
        of the exact precision | "Zero" (with "accuracy" -> {numerator, denominator})|>.
    Effects: Pure.
    Failures: None for finite reals.
    Example: realTreeNode[0.5]["precision"] is "MachinePrecision".
    Remarks: The record reproduces the number SameQ (review N1, N2): machine reals keep 17 significant digits;
        arbitrary-precision reals keep Ceiling[Precision] + 2 digits and their precision at full resolution (the exact
        binary value of Precision[x]), decoded with SetPrecision; an approximate zero keeps its accuracy (SetAccuracy).
        Displays and manifests claim Floor[precision] digits (scalarTreePrecision), never more than the data carry.
        Legacy records with an integer digit string still decode.
    See also: decimalRecord; decodeScalarTree; scalarTreePrecision.
*)
realTreeNode[x_Real] := Module[{p = Precision[x], record},
    Which[
        p === MachinePrecision, record = decimalRecord[x, 17];
            <|"node" -> "real", "significand" -> record["significand"], "exponent" -> record["exponent"], "precision" -> "MachinePrecision"|>,
        x == 0, <|"node" -> "real", "significand" -> "0", "exponent" -> "0", "precision" -> "Zero", "accuracy" -> exactRealRecord[Accuracy[x]]|>,
        True, record = decimalRecord[x, Ceiling[p] + 2];
            <|"node" -> "real", "significand" -> record["significand"], "exponent" -> record["exponent"], "precision" -> exactRealRecord[p]|>]
];
exactRealRecord[v_] := With[{r = SetPrecision[v, Infinity]}, {encodeInteger[Numerator[r]], encodeInteger[Denominator[r]]}];

(*
    Summary: Check a tree against the grammar and a registry.
    Parameters: node — any expression; registry — as encodeScalarTree (Automatic: references are not checked).
    Options/defaults: None.
    Returns: True, or InvalidScalarTree Failure with "Path".
    Effects: Pure.
    Failures: Unknown node kinds, extra or missing keys, malformed integers/rationals/records, unknown constants or
        function names, wrong argument counts, references outside the registry, internal temporary nodes.
    Example: validateScalarTree[<|"node" -> "eval", "code" -> "1"|>, Automatic] fails.
    Remarks: Every imported or generated tree passes here before it is decoded or lowered; no field is ever
        evaluated as source.
    See also: decodeScalarTree; encodeScalarTree.
*)
validateScalarTree[node_, registry_] := Catch[scalarTreeCheck[node, registry, {}]; True, "scalarTree"];

(*
    Summary: The recursion of validateScalarTree.
    Parameters: node; registry; path.
    Options/defaults: None.
    Returns: Null; throws an InvalidScalarTree Failure.
    Effects: Pure.
    Failures: As validateScalarTree.
    Example: scalarTreeCheck[<|"node" -> "integer", "value" -> "3"|>, Automatic, {}] returns Null.
    See also: validateScalarTree.
*)
scalarTreeCheck[node_, registry_, path_List] := Module[{fail, keys, kind},
    fail[reason_] := Throw[makeFailure["InvalidScalarTree", "The scalar expression tree is malformed.", <|"Path" -> path, "Reason" -> reason|>], "scalarTree"];
    If[!AssociationQ[node] || !StringQ[Lookup[node, "node", None]], fail["Not a node"]];
    kind = node["node"]; keys = Sort[Keys[node]];
    Switch[kind,
        "integer", If[keys =!= {"node", "value"} || !IntegerQ[decodeInteger[node["value"]]], fail["integer"]],
        "rational", If[keys =!= {"node", "value"} || !ListQ[node["value"]] || !MatchQ[decodeRational[node["value"]], _Rational], fail["rational"]],
        (* Real records are bounded before anything is decoded (review N9): an untrusted archive cannot make decoding
           allocate beyond its own size (significand and exponent strings, precision and accuracy below 10^5). *)
        "real", If[!realRecordBoundedQ[node] || !IntegerQ[decodeInteger[node["significand"]]] || !IntegerQ[decodeInteger[node["exponent"]]] ||
            !Which[
                node["precision"] === "Zero", keys === Sort[{"node", "significand", "exponent", "precision", "accuracy"}] && node["significand"] === "0" &&
                    ListQ[node["accuracy"]] && NumberQ[decodeRational[node["accuracy"]]],
                keys =!= Sort[{"node", "significand", "exponent", "precision"}], False,
                node["precision"] === "MachinePrecision", True,
                ListQ[node["precision"]], With[{p = decodeRational[node["precision"]]}, NumberQ[p] && p > 0],
                True, IntegerQ[decodeInteger[node["precision"]]] && decodeInteger[node["precision"]] >= 1],
            fail["real"]],
        "complex", If[keys =!= {"im", "node", "re"}, fail["complex"]];
            Scan[If[!MemberQ[{"integer", "rational", "real"}, Lookup[Replace[node[#], Except[_Association] -> <||>], "node", None]], fail["complex part"]] &, {"re", "im"}];
            scalarTreeCheck[node["re"], registry, Append[path, 1]]; scalarTreeCheck[node["im"], registry, Append[path, 2]],
        "algebraic", If[keys =!= {"node", "value"} || !AssociationQ[node["value"]] || FailureQ[decodeAlgebraic[node["value"]]], fail["algebraic"]],
        "constant", If[keys =!= {"name", "node"} || !MemberQ[Values[$ScalarTreeConstants], node["name"]], fail["constant"]],
        "parameter", If[keys =!= {"id", "node"} || !StringQ[node["id"]] || (registry =!= Automatic && !MemberQ[registry["Parameters"], node["id"]]),
            fail["parameter"]],
        "field", If[keys =!= {"id", "index", "node"} || !StringQ[node["id"]] || !IntegerQ[decodeInteger[node["index"]]] || decodeInteger[node["index"]] < 1 ||
            (registry =!= Automatic && !(IntegerQ[Lookup[registry["Fields"], node["id"], None]] && decodeInteger[node["index"]] <= registry["Fields"][node["id"]])),
            fail["field"]],
        "form", If[keys =!= {"index", "node", "slot"} || !StringQ[node["slot"]] || !IntegerQ[decodeInteger[node["index"]]] || decodeInteger[node["index"]] < 1 ||
            (registry =!= Automatic && !(IntegerQ[Lookup[Lookup[registry, "Slots", <||>], node["slot"], None]] && decodeInteger[node["index"]] <= registry["Slots"][node["slot"]])),
            fail["form"]],
        "plus" | "times", If[keys =!= {"args", "node"} || !ListQ[node["args"]] || Length[node["args"]] < 2, fail[kind]];
            MapIndexed[scalarTreeCheck[#1, registry, Append[path, First[#2]]] &, node["args"]],
        "power", If[keys =!= {"base", "exponent", "node"}, fail["power"]];
            scalarTreeCheck[node["base"], registry, Append[path, 1]]; scalarTreeCheck[node["exponent"], registry, Append[path, 2]],
        "surd", If[keys =!= {"base", "n", "node"} || !IntegerQ[decodeInteger[node["n"]]] || decodeInteger[node["n"]] < 2, fail["surd"]];
            scalarTreeCheck[node["base"], registry, Append[path, 1]],
        "function", If[keys =!= {"args", "name", "node"} || !MemberQ[Values[$ScalarTreeFunctions], node["name"]] || !ListQ[node["args"]] ||
            Length[node["args"]] =!= 1, fail["function"]];
            scalarTreeCheck[First[node["args"]], registry, Append[path, 1]],
        _, fail["Unknown node kind " <> kind]];
];

(*
    Summary: Rebuild the Wolfram expression of a validated tree.
    Parameters: node — tree accepted by validateScalarTree.
    Options/defaults: None.
    Returns: The expression (evaluated), or Failure for an invalid tree.
    Effects: Pure; no string is evaluated as source.
    Failures: InvalidScalarTree.
    Example: decodeScalarTree[encodeScalarTree[x, reg]] === x for every encodable x.
    Remarks: Rebuilding evaluates heads in the original order, so an evaluated input comes back SameQ; algebraic
        records decode to RootReduced Root objects, which is the canonical form Root values have after evaluation.
    See also: encodeScalarTree; validateScalarTree.
*)
decodeScalarTree[node_] := With[{valid = validateScalarTree[node, Automatic]}, If[FailureQ[valid], valid, scalarTreeValue[node]]];

(*
    Summary: The recursion of decodeScalarTree (validated input).
    Parameters: node.
    Options/defaults: None.
    Returns: Expression.
    Effects: Pure.
    Failures: None for validated trees.
    Example: scalarTreeValue[<|"node" -> "constant", "name" -> "Pi"|>] is Pi.
    See also: decodeScalarTree.
*)
scalarTreeValue[node_Association] := Switch[node["node"],
    "integer", decodeInteger[node["value"]],
    "rational", decodeRational[node["value"]],
    "real", realTreeValue[node],
    "complex", Complex[scalarTreeValue[node["re"]], scalarTreeValue[node["im"]]],
    "algebraic", decodeAlgebraic[node["value"]],
    "constant", First[Keys[Select[$ScalarTreeConstants, # === node["name"] &]]],
    "parameter", Coupling[node["id"]],
    "field", FieldComponent[node["id"], decodeInteger[node["index"]]],
    "form", FormComponent[node["slot"], decodeInteger[node["index"]]],
    "plus", Plus @@ (scalarTreeValue /@ node["args"]),
    "times", Times @@ (scalarTreeValue /@ node["args"]),
    "power", Power[scalarTreeValue[node["base"]], scalarTreeValue[node["exponent"]]],
    "surd", Surd[scalarTreeValue[node["base"]], decodeInteger[node["n"]]],
    "function", First[Keys[Select[$ScalarTreeFunctions, # === node["name"] &]]][scalarTreeValue[First[node["args"]]]]];

(*
    Summary: The approximate real of a real node at its recorded precision.
    Parameters: node — real node.
    Options/defaults: None.
    Returns: Machine real (correctly rounded) or arbitrary-precision real.
    Effects: Pure.
    Failures: None for validated nodes.
    Example: realTreeValue[realTreeNode[0.1]] === 0.1.
    See also: realTreeNode; nearestMachineReal.
*)
realTreeValue[node_Association] := With[{exact = decodeInteger[node["significand"]] 10^decodeInteger[node["exponent"]]},
    Which[
        node["precision"] === "MachinePrecision", nearestMachineReal[exact],
        node["precision"] === "Zero", SetAccuracy[0, N[decodeRational[node["accuracy"]]]],
        ListQ[node["precision"]], SetPrecision[exact, N[decodeRational[node["precision"]]]],
        True, N[exact, decodeInteger[node["precision"]]]]];

(*
    Summary: The parameters and field components a tree uses.
    Parameters: node — validated tree (temporary nodes allowed).
    Options/defaults: None.
    Returns: <|"Parameters" -> IDs (first appearance), "Fields" -> <|field ID -> sorted component indices|>, "Slots" -> <|form
        slot ID -> sorted component indices|>|>.
    Effects: Pure.
    Failures: None.
    Example: scalarTreeDependencies[encodeScalarTree[Coupling["c"] FieldComponent["f", 2], reg]]["Fields"] is <|"f" -> {2}|>.
    See also: collectOutputDependencies.
*)
scalarTreeDependencies[node_] := Module[{nodes = Cases[{node}, _Association?(KeyExistsQ[#, "node"] &), Infinity]},
    <|"Parameters" -> DeleteDuplicates[Lookup[Select[nodes, #["node"] === "parameter" &], "id", {}]],
        "Fields" -> Map[Sort[DeleteDuplicates[decodeInteger /@ Lookup[#, "index"]]] &, GroupBy[Select[nodes, #["node"] === "field" &], #["id"] &]],
        "Slots" -> Map[Sort[DeleteDuplicates[decodeInteger /@ Lookup[#, "index"]]] &, GroupBy[Select[nodes, #["node"] === "form" &], #["slot"] &]]|>
];

(*
    Summary: Whether a real record is within the decoding bounds.
    Parameters: node — real-node association.
    Options/defaults: None.
    Returns: Boolean: significand and exponent strings of at most 10^5 and 7 characters (|exponent| < 10^6), precision
        and accuracy records with at most 30 characters per integer and a value below 10^5 in magnitude.
    Effects: Pure (only string lengths and small integers are inspected).
    Failures: None.
    Example: realRecordBoundedQ[<|..., "exponent" -> "1000000000000"|>] is False.
    Remarks: The bounds are far above any value a working precision can produce and keep decoding linear in the input.
    See also: scalarTreeCheck; realTreeValue.
*)
realRecordBoundedQ[node_Association] := Module[{small},
    small[r_] := ListQ[r] && Length[r] === 2 && AllTrue[r, StringQ[#] && StringLength[#] <= 30 &] && With[{v = decodeRational[r]}, NumberQ[v] && Abs[v] < 10^5];
    StringQ[node["significand"]] && StringLength[node["significand"]] <= 10^5 && StringQ[node["exponent"]] && StringLength[node["exponent"]] <= 7 &&
        Which[node["precision"] === "MachinePrecision", True, node["precision"] === "Zero", small[Lookup[node, "accuracy", None]],
            ListQ[node["precision"]], small[node["precision"]], StringQ[node["precision"]], StringLength[node["precision"]] <= 6, True, False]
];

(*
    Summary: The lowest precision of the approximate numbers in a tree.
    Parameters: node — validated tree.
    Options/defaults: None.
    Returns: Infinity (exact), MachinePrecision, or the lowest recorded digit count.
    Effects: Pure.
    Failures: None.
    Example: scalarTreePrecision[encodeScalarTree[0.5 Coupling["c"], reg]] is MachinePrecision.
    Remarks: A machine real counts as about 16 digits, below any arbitrary-precision record of 16 or more digits. A tree
        whose only reals are approximate zeros is numerical (MachinePrecision): an approximate zero never bounds a
        precision but makes the data inexact; Infinity means there is no real node at all.
    See also: ModelOutput (per-output arithmetic status).
*)
scalarTreePrecision[node_] := Module[{reals = Cases[{node}, _Association?(Lookup[#, "node", None] === "real" &), Infinity], digits},
    If[reals === {}, Return[Infinity]];
    digits = DeleteCases[Map[Which[# === "MachinePrecision", MachinePrecision, # === "Zero", Infinity, ListQ[#], Floor[N[decodeRational[#]]],
        True, decodeInteger[#]] &, Lookup[reals, "precision"]], Infinity];
    (* Only approximate zeros: the data are still numerical (review N8, the Stage 5 dataPrecision convention). *)
    If[digits === {}, Return[MachinePrecision]];
    If[MemberQ[digits, MachinePrecision] && AllTrue[DeleteCases[digits, MachinePrecision], # >= 16 &], MachinePrecision,
        Min[Replace[digits, MachinePrecision -> 16, {1}]]]
];

(*
    Summary: Extract subtrees shared between or within output trees as named temporaries.
    Parameters: trees — list of validated trees (every scalar of every output, in order); prefix — temporary name prefix.
    Options/defaults: None.
    Returns: <|"Temporaries" -> {<|"Name", "Node", "Dependencies" -> temporary names|>...} (definition order),
        "Trees" -> trees with shared subtrees replaced by <|"node" -> "temporary", "name"|>|>.
    Effects: Pure.
    Failures: None.
    Example: two outputs containing the same Power[c, 2] share one temporary.
    Remarks: Only composite subtrees (plus, times, power, surd, function) that occur at least twice are extracted;
        identical trees denote identical values, so no branch or identity is changed. Each temporary is defined
        after the temporaries it uses (innermost first).
    See also: renderPythonModule; lowerPythonTree.
*)
pythonCommonSubexpressions[trees_List, prefix_String] := Module[{counts = <||>, count, selected, order, names, rewrite, temporaries},
    count[node_Association] := (If[MemberQ[{"plus", "times", "power", "surd", "function"}, Lookup[node, "node", None]],
            AssociateTo[counts, node -> Lookup[counts, Key[node], 0] + 1]];
        Scan[count, Select[Flatten[Values[KeyDrop[node, "node"]]], AssociationQ]]);
    count[_] := Null;
    Scan[count, trees];
    selected = Keys[Select[counts, # >= 2 &]];
    (* Smaller subtrees first, so every temporary's definition can refer to the ones inside it. *)
    order = SortBy[selected, {LeafCount, Hash}];
    names = AssociationThread[order, MapIndexed[prefix <> ToString[First[#2]] &, order]];
    rewrite[node_Association, top_] := If[!top && KeyExistsQ[names, node], <|"node" -> "temporary", "name" -> Lookup[names, Key[node]]|>,
        Association[KeyValueMap[#1 -> Which[AssociationQ[#2], rewrite[#2, False], ListQ[#2], Map[If[AssociationQ[#], rewrite[#, False], #] &, #2], True, #2] &, node]]];
    temporaries = Map[With[{definition = rewrite[#, True]},
        <|"Name" -> Lookup[names, Key[#]], "Node" -> definition,
            "Dependencies" -> DeleteDuplicates[Cases[{definition}, a_Association /; Lookup[a, "node", None] === "temporary" :> a["name"], Infinity]]|>] &, order];
    <|"Temporaries" -> temporaries, "Trees" -> Map[rewrite[#, False] &, trees]|>
];

(*
    Summary: Python source of one tree for a backend.
    Parameters: node — validated tree, possibly with temporary nodes; names — <|"Parameters" -> <|ID -> local name|>,
        "Fields" -> <|ID -> local name|>|>; backend — "NumPy" or "mpmath"; digits — decimal digits for algebraic and
        named constants (mpmath working precision plus guard digits; ignored by NumPy).
    Options/defaults: None.
    Returns: String (a fully parenthesized Python expression), or Failure.
    Effects: Pure.
    Failures: UnsupportedBackend; InvalidScalarTree (unknown node).
    Example: lowerPythonTree[<|"node" -> "power", ...|>, names, "NumPy", 16] uses _ipow for an integer exponent and
        _pow otherwise; x^2 becomes _ipow(x, 2), never the Python XOR operator.
    Remarks: Structure is preserved node for node. Powers, logarithms and the other functions call module helpers
        that first cast to complex (and normalize a negative-zero imaginary part), so a negative real base takes
        Wolfram's principal complex branch; Power[E, x] lowers to _exp(x); Surd lowers to the real root helper,
        which refuses nonreal input and even roots of negative numbers. Exact rationals are integer ratios evaluated
        at run time (correctly rounded in NumPy, at the context precision in mpmath); algebraic values and
        constants without a backend symbol are decimal literals computed from their exact definition. Parameter
        and field IDs never appear in the source: names map them to generated identifiers.
    See also: renderPythonModule; pythonCommonSubexpressions.
*)
lowerPythonTree[node_, names_Association, backend_String, digits_Integer] := If[!MemberQ[{"NumPy", "mpmath"}, backend],
    makeFailure["UnsupportedBackend", "The Python backend must be \"NumPy\" or \"mpmath\".", <|"Backend" -> backend|>],
    Catch[pythonNodeSource[node, names, backend, digits], "pythonLowering"]];

(*
    Summary: The recursion of lowerPythonTree.
    Parameters: As lowerPythonTree.
    Options/defaults: None.
    Returns: String; throws InvalidScalarTree to "pythonLowering".
    Effects: Pure.
    Failures: As lowerPythonTree.
    Example: pythonNodeSource[<|"node" -> "integer", "value" -> "-3"|>, names, "NumPy", 16] is "(-3)".
    See also: lowerPythonTree.
*)
pythonNodeSource[node_Association, names_Association, backend_String, digits_Integer] := Module[{numpy = backend === "NumPy", sub, call, ctx},
    sub[n_] := pythonNodeSource[n, names, backend, digits];
    ctx = If[numpy, "", "ctx, "];
    call[f_, args_List] := f <> "(" <> ctx <> StringRiffle[args, ", "] <> ")";
    Switch[node["node"],
        (* NumPy: integers beyond 2^53 are converted by Python's float(int), which rounds correctly to the nearest double
           (review N6: a decimal literal would round twice). *)
        "integer", Which[!numpy, "ctx.mpf(" <> node["value"] <> ")", Abs[decodeInteger[node["value"]]] <= 2^53, "(" <> node["value"] <> ")",
            True, "float(" <> node["value"] <> ")"],
        "rational", If[numpy, "(" <> node["value"][[1]] <> "/" <> node["value"][[2]] <> ")",
            "(ctx.mpf(" <> node["value"][[1]] <> ")/ctx.mpf(" <> node["value"][[2]] <> "))"],
        "real", With[{literal = node["significand"] <> "e" <> node["exponent"]}, If[numpy, "(" <> literal <> ")", "ctx.mpf(\"" <> literal <> "\")"]],
        "complex", If[numpy, "complex(" <> sub[node["re"]] <> ", " <> sub[node["im"]] <> ")", "ctx.mpc(" <> sub[node["re"]] <> ", " <> sub[node["im"]] <> ")"],
        "algebraic", With[{value = N[decodeAlgebraic[node["value"]], digits + 10]},
            If[numpy, "complex(" <> pythonDecimal[Re[value], 17] <> ", " <> pythonDecimal[Im[value], 17] <> ")",
                "ctx.mpc(ctx.mpf(\"" <> pythonDecimal[Re[value], digits + 5] <> "\"), ctx.mpf(\"" <> pythonDecimal[Im[value], digits + 5] <> "\"))"]],
        "constant", If[numpy,
            Switch[node["name"], "Pi", "_np.pi", "E", "_np.e", "EulerGamma", "_np.euler_gamma", "Catalan", "(" <> pythonDecimal[N[Catalan, 30], 17] <> ")"],
            Switch[node["name"], "Pi", "ctx.pi", "E", "ctx.e", "EulerGamma", "ctx.euler", "Catalan", "ctx.catalan"]],
        "parameter", names["Parameters"][node["id"]],
        "field", names["Fields"][node["id"]] <> "[" <> ToString[decodeInteger[node["index"]] - 1] <> "]",
        "temporary", node["name"],
        (* Form-slot values are runtime inputs of a modular module (names["Slots"], Stage 9 emission). *)
        "form", If[AssociationQ[Lookup[names, "Slots", None]] && KeyExistsQ[names["Slots"], node["slot"]],
            names["Slots"][node["slot"]] <> "[" <> ToString[decodeInteger[node["index"]] - 1] <> "]",
            Throw[makeFailure["InvalidScalarTree", "A form-slot component needs the modular emission (no slot names were given).", <|"Slot" -> node["slot"]|>], "pythonLowering"]],
        "plus", "(" <> StringRiffle[sub /@ node["args"], " + "] <> ")",
        "times", "(" <> StringRiffle[sub /@ node["args"], " * "] <> ")",
        "power", Which[
            node["base"] === <|"node" -> "constant", "name" -> "E"|>, call["_exp", {sub[node["exponent"]]}],
            node["exponent"]["node"] === "integer", call["_ipow", {sub[node["base"]], node["exponent"]["value"]}],
            True, call["_pow", {sub[node["base"]], sub[node["exponent"]]}]],
        "surd", call["_surd", {sub[node["base"]], node["n"]}],
        "function", call["_" <> ToLowerCase[node["name"]], {sub[First[node["args"]]]}],
        _, Throw[makeFailure["InvalidScalarTree", "Unknown node kind in Python lowering.", <|"Node" -> node["node"]|>], "pythonLowering"]]
];
pythonNodeSource[node_, ___] := Throw[makeFailure["InvalidScalarTree", "Expected a tree node.", <|"Node" -> node|>], "pythonLowering"];

(*
    Summary: A decimal literal of a real number with a given number of significant digits.
    Parameters: x — real number (exact or approximate); digits — positive integer.
    Options/defaults: None.
    Returns: String such as "-15e-1" (Python float and mpmath literal syntax).
    Effects: Pure.
    Failures: None for finite reals.
    Example: pythonDecimal[1/2, 17] is "5e-1".
    See also: decimalRecord.
*)
pythonDecimal[x_, digits_Integer] := With[{record = decimalRecord[x, digits]}, record["significand"] <> "e" <> record["exponent"]];

True
