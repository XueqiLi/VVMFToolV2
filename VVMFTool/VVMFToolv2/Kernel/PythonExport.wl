(*
    :Title: Python modules of prepared model outputs
    :Context: VVMFTool`Private`
    :Summary: Standalone NumPy or mpmath modules generated from a ModelOutput: validated inputs (one parameter vector
        in manifest order, full field vectors keyed by field ID), every output and an alias per output, finite
        shape-checked results, and an embedded data-literal manifest. Nothing is imported or executed here.
    :Responsibilities: pythonIdentifierQ, allocatePythonNames, pythonStringLiteral, pythonLiteral, pythonManifest,
        renderPythonModule, validatePythonArtifact; PythonArtifact, ToPython, PythonSource, PythonManifest, ExportPython.
    :Dependencies: ModelOutput.wl (validateModelOutput); PythonIR.wl (lowerPythonTree, pythonCommonSubexpressions,
        scalarTreeDependencies); DisplayExport.wl (writeDisplayArtifact).
    :See Also: VVMFArch/step6Plan.md (Python code and manifest); VVMFArch/implementation/step6Status.md (D-S6-4, D-S6-5).
*)

$PythonKeywords = {"False", "None", "True", "and", "as", "assert", "async", "await", "break", "class", "continue", "def", "del", "elif",
    "else", "except", "finally", "for", "from", "global", "if", "import", "in", "is", "lambda", "nonlocal", "not", "or", "pass", "raise",
    "return", "try", "while", "with", "yield"};
(* Names the generated module defines or uses: module API, locals of generated functions and builtins it calls. *)
$PythonReservedNames = Join[$PythonKeywords, {"manifest", "parameter_ids", "parameter_names", "number_of_parameters", "output_names", "output_shapes",
    "field_ids", "field_dimensions", "backend", "working_precision", "function_names", "evaluate", "EvaluationError", "params", "fields",
    "p", "f", "ctx", "complex", "isinstance", "len", "str", "repr", "bytes", "bytearray", "bool", "tuple", "list", "dict", "set", "frozenset",
    "range", "enumerate", "int", "float", "abs", "type", "sorted", "any", "all", "ValueError", "TypeError", "ArithmeticError",
    "ZeroDivisionError", "OverflowError", "hasattr"}];

(*
    Summary: Whether a string is a valid ASCII Python identifier that the generated module may use for a user name.
    Parameters: s — string.
    Options/defaults: None.
    Returns: Boolean.
    Effects: Pure.
    Failures: None.
    Example: pythonIdentifierQ["ELMatrix"] is True; pythonIdentifierQ["lambda"] and pythonIdentifierQ["_t1"] are False.
    Remarks: A leading underscore is reserved for generated helpers and temporaries.
    See also: allocatePythonNames.
*)
pythonIdentifierQ[s_String] := StringMatchQ[s, RegularExpression["[A-Za-z][A-Za-z0-9_]*"]] && !MemberQ[$PythonReservedNames, s];
pythonIdentifierQ[_] := False;

(*
    Summary: A deterministic identifier derived from a label.
    Parameters: label — string; prefix — prefix for labels starting with a digit or an underscore.
    Options/defaults: None.
    Returns: Identifier string (not checked for collisions).
    Effects: Pure.
    Failures: None.
    Example: pythonIdentifierFrom["3 x", "output_"] is "output_3_x"; pythonIdentifierFrom["lambda", "p_"] is "lambda_".
    See also: allocatePythonNames.
*)
pythonIdentifierFrom[label_String, prefix_String] := Module[{s = StringReplace[label, RegularExpression["[^A-Za-z0-9_]"] -> "_"]},
    If[s === "" || StringMatchQ[s, RegularExpression["_*"]], s = "x" <> s];
    If[StringMatchQ[s, RegularExpression["[0-9_].*"]], s = prefix <> s];
    If[MemberQ[$PythonReservedNames, s], s = s <> "_"];
    s
];

(*
    Summary: Allocate the generated names of outputs, parameters and fields.
    Parameters: data — validated ModelOutput data; functionNames, parameterNames — the options (partial maps);
        extra — further names the module defines (Stage 9 modular modules: $ModularModuleReserved; default {}).
    Options/defaults: Unnamed outputs use their output name, parameters their label, fields "f_" and the field name.
    Returns: <|"Functions" -> <|output -> name|>, "Parameters" -> <|ID -> name|>, "Fields" -> <|ID -> name|>|>, or Failure.
    Effects: Pure.
    Failures: InvalidOption for unknown keys, invalid or reserved identifiers, or collisions among explicit names.
    Example: two parameters labelled "c" get the names c and c_2 in model order.
    Remarks: Automatic names that would collide receive deterministic suffixes _2, _3, ... in output (or parameter)
        order and never take an explicit name; IDs never become source code.
    See also: pythonIdentifierFrom; renderPythonModule.
*)
allocatePythonNames[data_Association, functionNames_, parameterNames_] := allocatePythonNames[data, functionNames, parameterNames, {}];
allocatePythonNames[data_Association, functionNames_, parameterNames_, extra_List] := Module[{outputs = Lookup[data["Outputs"], "Name"], ids = data["RuntimeParameters"],
        labels, assign, taken, functions, parameters, fields},
    If[!AssociationQ[functionNames] || !SubsetQ[outputs, Keys[functionNames]] || !AllTrue[Values[functionNames], pythonIdentifierQ[#] && !MemberQ[extra, #] &] ||
            !DuplicateFreeQ[Values[functionNames]],
        Return[makeFailure["InvalidOption", "FunctionNames must map known output names to unique valid Python identifiers that are not reserved.",
            <|"Options" -> {FunctionNames}|>]]];
    If[!AssociationQ[parameterNames] || !SubsetQ[Lookup[data["Parameters"], "ID", {}], Keys[parameterNames]] ||
            !AllTrue[Values[parameterNames], pythonIdentifierQ[#] && !MemberQ[extra, #] &] || !DuplicateFreeQ[Values[parameterNames]],
        Return[makeFailure["InvalidOption", "ParameterNames must map known parameter IDs to unique valid Python identifiers that are not reserved.",
            <|"Options" -> {ParameterNames}|>]]];
    (* Assign automatic names in order, avoiding every explicit name and every earlier name of the same namespace. *)
    assign[keys_List, explicit_Association, base_, prefix_String, reserved_List] := Module[{used = Join[reserved, Values[explicit]], result = <||>},
        Do[If[KeyExistsQ[explicit, k], result[k] = explicit[k],
            Module[{candidate = pythonIdentifierFrom[base[k], prefix], n = 2, stem},
                stem = candidate;
                While[MemberQ[used, candidate], candidate = stem <> "_" <> ToString[n++]];
                AppendTo[used, candidate]; result[k] = candidate]], {k, keys}];
        result];
    functions = assign[outputs, functionNames, Identity, "output_", extra];
    labels = AssociationThread[Lookup[data["Parameters"], "ID", {}], Lookup[data["Parameters"], "Label", {}]];
    parameters = assign[ids, KeyTake[parameterNames, ids], labels[#] &, "p_", extra];
    taken = Join[Values[parameters], extra];
    fields = assign[data["RuntimeFields"], <||>, "f_" <> Lookup[AssociationThread[Lookup[data["Fields"], "ID", {}], Lookup[data["Fields"], "Name", {}]], #] &,
        "f_", taken];
    If[IntersectingQ[Values[parameters], Values[fields]],
        Return[makeFailure["InvalidOption", "A parameter name collides with a generated field name.", <|"Options" -> {ParameterNames}|>]]];
    <|"Functions" -> functions, "Parameters" -> parameters, "Fields" -> fields|>
];

(*
    Summary: A Python string literal of any string.
    Parameters: s — string.
    Options/defaults: None.
    Returns: A double-quoted ASCII literal: backslash, quote and control characters escaped, non-ASCII characters as
        \uXXXX or \UXXXXXXXX escapes.
    Effects: Pure.
    Failures: None.
    Example: pythonStringLiteral["a\"b\n"] is "\"a\\\"b\\n\"".
    Remarks: No user text can end the literal early, so labels and IDs cannot inject source.
    See also: pythonLiteral.
*)
pythonStringLiteral[s_String] := "\"" <> StringJoin[Map[Function[code, Which[
        code === 92, "\\\\", code === 34, "\\\"", code === 10, "\\n", code === 13, "\\r", code === 9, "\\t",
        code < 32 || code === 127, "\\x" <> IntegerString[code, 16, 2],
        code < 127, FromCharacterCode[code],
        code <= 65535, "\\u" <> IntegerString[code, 16, 4],
        True, "\\U" <> IntegerString[code, 16, 8]]], ToCharacterCode[s, "Unicode"]]] <> "\"";

(*
    Summary: A Python data literal of JSON-like Wolfram data.
    Parameters: x — association (string keys), list, string, integer, True/False/Null or Missing.
    Options/defaults: None.
    Returns: Python source of dicts, lists, strings, ints, True/False/None, or Failure for other data.
    Effects: Pure.
    Failures: UnsupportedLiteral (reals or symbolic expressions; the manifest carries exact data as strings or trees).
    Example: pythonLiteral[<|"a" -> {1, "x"}|>] is "{\"a\": [1, \"x\"]}".
    See also: pythonManifest.
*)
pythonLiteral[x_] := Catch[pythonLiteralSource[x], "pythonLiteral"];
pythonLiteralSource[x_] := Which[
    AssociationQ[x], If[!AllTrue[Keys[x], StringQ], Throw[makeFailure["UnsupportedLiteral", "Manifest keys must be strings."], "pythonLiteral"],
        "{" <> StringRiffle[KeyValueMap[pythonStringLiteral[#1] <> ": " <> pythonLiteralSource[#2] &, x], ", "] <> "}"],
    ListQ[x], "[" <> StringRiffle[pythonLiteralSource /@ x, ", "] <> "]",
    StringQ[x], pythonStringLiteral[x],
    IntegerQ[x], ToString[x],
    x === True, "True", x === False, "False", x === Null || MissingQ[x], "None",
    True, Throw[makeFailure["UnsupportedLiteral", "Only strings, integers, booleans, lists and associations are manifest data.", <|"Value" -> x|>], "pythonLiteral"]];

(*
    Summary: The manifest of a generated module.
    Parameters: data — ModelOutput data; names — allocated names; backend; precision — resolved working precision.
    Options/defaults: None.
    Returns: JSON-like association (strings, integers, lists, associations).
    Effects: Pure.
    Failures: None.
    Example: pythonManifest[...]["parameter_ids"] is data["RuntimeParameters"].
    Remarks: Identities of the source model, context, group, basis and target; every output's kind, origin, shape,
        convention, arithmetic and exact tree (after substitution); the runtime parameters with their labels and
        generated names; the substitutions with their trees; the required fields; the function names; and the
        numerical status: the module evaluates numerically and certifies nothing.
    See also: renderPythonModule; PythonManifest.
*)
pythonManifest[data_Association, names_Association, backend_String, precision_] := Module[{labels, fieldByID},
    labels = AssociationThread[Lookup[data["Parameters"], "ID", {}], data["Parameters"]];
    fieldByID = AssociationThread[Lookup[data["Fields"], "ID", {}], data["Fields"]];
    (* The package has no release version yet (alpha); the generating kernel version makes modules traceable (review N7). *)
    <|"schema" -> 1, "generator" -> "VVMFTool", "generator_version" -> "unversioned (alpha)", "wolfram_version" -> $Version, "kind" -> "ModelOutput",
        "model" -> <|"id" -> data["ModelID"], "name" -> data["ModelName"], "target_irrep" -> data["TargetIrrepID"], "context_digest" -> data["ContextDigest"],
            "source_arithmetic" -> data["SourceArithmetic"], "source_validation" -> data["SourceValidation"],
            "group" -> <|"state_id" -> data["Group"]["StateID"], "generator_identity" -> data["Group"]["GeneratorIdentity"],
                "character_identity" -> data["Group"]["CharacterIdentity"], "assignment_identity" -> data["Group"]["AssignmentIdentity"]|>|>,
        "output_id" -> data["ID"], "backend" -> backend,
        "working_precision" -> If[precision === MachinePrecision, "MachinePrecision", ToString[precision]],
        "numerical_status" -> "Numerical evaluation of the listed exact or numerical source data; exact values are not exact in Python and nothing is certified by this module.",
        "outputs" -> Map[<|"name" -> #["Name"], "function" -> names["Functions"][#["Name"]], "kind" -> #["Kind"], "origin" -> #["Origin"],
            "shape" -> #["Shape"], "convention" -> If[AssociationQ[#["Convention"]], <|"kind" -> #["Convention"]["Kind"], "convention" -> #["Convention"]["Convention"],
                "rows" -> (componentReference /@ #["Convention"]["Rows"]), "columns" -> (componentReference /@ #["Convention"]["Columns"]),
                "certificate" -> Lookup[#["Convention"], "Certificate", Null]|>, Null],
            "arithmetic" -> #["Arithmetic"], "source_precision" -> precisionText[#["Precision"]], "trees" -> #["Trees"]|> &, data["Outputs"]],
        "parameter_ids" -> data["RuntimeParameters"],
        "parameters" -> Map[<|"id" -> #, "label" -> labels[#]["Label"], "name" -> names["Parameters"][#], "domain" -> labels[#]["Domain"],
            "source" -> sourceAtomText[labels[#]["SourceAtom"]]|> &, data["RuntimeParameters"]],
        "substitutions" -> KeyValueMap[<|"id" -> #1, "label" -> labels[#1]["Label"], "value" -> #2|> &, data["SubstitutionTrees"]],
        "fields" -> Map[<|"id" -> #, "name" -> fieldByID[#]["Name"], "irrep" -> fieldByID[#]["IrrepID"],
            Sequence @@ Normal[manifestIrrepFields[Lookup[fieldByID[#], "Context", data["Group"]["StateID"]], fieldByID[#]["IrrepID"]]], "dimension" -> fieldByID[#]["Dimension"],
            "basis" -> fieldByID[#]["BasisID"], "variable" -> names["Fields"][#]|> &, data["RuntimeFields"]],
        "function_names" -> names["Functions"]|>
];

(*
    Summary: Inert text forms used by the manifest.
    Parameters: c — FieldComponent; p — precision; atom — HoldForm source spelling or Missing.
    Options/defaults: None.
    Returns: <|"field", "index"|>; precision string; spelling string or Null.
    Effects: Pure.
    Failures: None.
    Example: precisionText[Infinity] is "Exact".
    See also: pythonManifest.
*)
componentReference[FieldComponent[id_String, i_Integer]] := <|"field" -> id, "index" -> i|>;
componentReference[other_] := <|"variable" -> ToString[other, InputForm]|>;
precisionText[Infinity] := "Exact";
precisionText[MachinePrecision] := "MachinePrecision";
precisionText[p_] := ToString[p];
sourceAtomText[HoldForm[s_]] := ToString[Unevaluated[s], InputForm];
sourceAtomText[s_String] := s;
sourceAtomText[_] := Null;

(*
    Summary: The Python source of a complete standalone module.
    Parameters: data — validated ModelOutput data; names — allocated names; backend — "NumPy" | "mpmath";
        precision — MachinePrecision (NumPy) or decimal digits (mpmath); cse — Boolean (CommonSubexpressions).
    Options/defaults: None.
    Returns: <|"Source" -> string, "Manifest" -> association|>, or Failure.
    Effects: Pure.
    Failures: Lowering failures (InvalidScalarTree); UnsupportedLiteral.
    Example: renderPythonModule[d, names, "NumPy", MachinePrecision, True]["Source"] starts with a docstring and imports numpy.
    Remarks: The module defines parameter_ids, parameter_names, number_of_parameters, output_names, output_shapes,
        field_ids, field_dimensions, backend, working_precision, function_names, manifest, EvaluationError,
        evaluate(params, fields=None) (all outputs, as an ordered dict) and one alias per output with the same input
        schema. Helpers and temporaries use reserved leading-underscore names. evaluate shares common
        subexpressions across outputs; an alias computes only what its output uses. Every intermediate statement is
        guarded so that a division by zero or domain error raises EvaluationError naming the outputs it belongs to,
        and every result is checked finite and shaped. mpmath evaluation runs in a private context cloned per call at
        the working precision; the global mpmath precision is never changed.
    See also: lowerPythonTree; pythonCommonSubexpressions; ToPython.
*)
renderPythonModule[data_Association, names_Association, backend_String, precision_, cse_] := renderPythonModule[data, names, backend, precision, cse, None];
renderPythonModule[data_Association, names_Association, backend_String, precision_, cse_, modular_] := Module[
    {numpy = backend === "NumPy", digits, manifest, manifestSource, outputs = data["Outputs"], trees, positions, extracted, temporaries,
        outputTrees, lower, users, body, lines, header, helpers, inputs, functionLines, all, aliasLines, dispatch, failure, modularQ = AssociationQ[modular], y},
    digits = If[numpy, 16, precision];
    manifest = pythonManifest[data, names, backend, precision];
    (* Stage 9: a modular model module takes a point and form values; its manifest names the slots of every output and
       carries the form manifest (D-S9-11). Every other module is rendered exactly as before. *)
    If[modularQ, manifest = Join[manifest, <|"kind" -> "ModularModelOutput",
        "outputs" -> Map[Append[#, "slots" -> Select[data["Modular"]["RuntimeSlots"], Function[sid, !FreeQ[#["trees"], KeyValuePattern[{"node" -> "form", "slot" -> sid}]]]]] &,
            manifest["outputs"]], "forms" -> modular["FormManifest"]|>]];
    y = If[modularQ, "y, ", ""];
    manifestSource = pythonLiteral[manifest]; If[FailureQ[manifestSource], Return[manifestSource]];
    (* Every scalar of every output, in order, with its output index. *)
    trees = Flatten[MapIndexed[Function[{o, k}, Map[{First[k], #} &, If[o["Kind"] === "Scalar", {o["Trees"]}, Flatten[o["Trees"]]]]], outputs], 1];
    extracted = If[TrueQ[cse], pythonCommonSubexpressions[trees[[All, 2]], "_t"], <|"Temporaries" -> {}, "Trees" -> trees[[All, 2]]|>];
    temporaries = extracted["Temporaries"];
    positions = GroupBy[MapIndexed[{#1[[1]], First[#2]} &, trees], First -> Last];
    outputTrees = Map[extracted["Trees"][[#]] &, positions];
    lower[node_] := lowerPythonTree[node, names, backend, digits];
    (* The temporaries an output needs (transitively), in definition order. *)
    users = Module[{direct, closure, byName = AssociationThread[Lookup[temporaries, "Name", {}], temporaries]},
        closure[set_List] := FixedPoint[DeleteDuplicates[Join[#, Flatten[Lookup[byName, #, <||>]["Dependencies"] & /@ #]]] &, set];
        direct[k_] := DeleteDuplicates[Cases[outputTrees[k], a_Association /; Lookup[a, "node", None] === "temporary" :> a["name"], Infinity]];
        Association[Map[# -> Select[Lookup[temporaries, "Name", {}], Function[t, MemberQ[closure[direct[#]], t]]] &, Keys[outputTrees]]]];
    failure = If[!FreeQ[lower /@ Join[Lookup[temporaries, "Node", {}], Flatten[Values[outputTrees]]], _Failure],
        FirstCase[lower /@ Join[Lookup[temporaries, "Node", {}], Flatten[Values[outputTrees]]], _Failure], None];
    If[failure =!= None, Return[failure]];
    header = {
        "\"\"\"Generated by VVMFTool: numerical evaluation of the outputs " <> StringRiffle[pythonStringLiteral /@ Lookup[outputs, "Name"], ", "] <>
            " of the model " <> pythonStringLiteral[data["ModelName"]] <> ".",
        "",
        "Backend: " <> backend <> If[numpy, " (machine precision).", " (" <> ToString[precision] <> " decimal digits in a private context per call)."],
        "The exact or numerical source data are listed in `manifest`; this module evaluates them numerically and",
        "certifies nothing. Call evaluate(params, fields) or one function per output; see the manifest for the order",
        "of params and the field IDs. Do not edit by hand.",
        "\"\"\"",
        "import math as _math",
        "import numbers as _numbers",
        "from collections.abc import Mapping as _Mapping",
        If[numpy, "import numpy as _np", "import fractions as _fractions\nimport decimal as _decimal\nimport mpmath as _mpmath"],
        "",
        "manifest = " <> manifestSource,
        "parameter_ids = tuple(manifest[\"parameter_ids\"])",
        "parameter_names = tuple(p[\"name\"] for p in manifest[\"parameters\"])",
        "number_of_parameters = len(parameter_ids)",
        "output_names = tuple(o[\"name\"] for o in manifest[\"outputs\"])",
        "output_shapes = {o[\"name\"]: tuple(o[\"shape\"]) for o in manifest[\"outputs\"]}",
        "field_ids = tuple(f[\"id\"] for f in manifest[\"fields\"])",
        "field_dimensions = {f[\"id\"]: f[\"dimension\"] for f in manifest[\"fields\"]}",
        "function_names = dict(manifest[\"function_names\"])",
        "backend = " <> pythonStringLiteral[backend],
        "working_precision = " <> If[numpy, "None", ToString[precision]],
        "",
        "",
        "class EvaluationError(ArithmeticError):",
        "    \"\"\"An output is not finite or not defined at the given point (singular point, branch or domain error).\"\"\"",
        ""};
    helpers = If[numpy, {
        "def _c(x):",
        "    # complex cast; adding 0j turns a negative-zero imaginary part into +0, so -1 takes Arg = pi as in Wolfram",
        "    return _np.complex128(x) + 0j",
        "def _ipow(b, k):", "    return _c(b) ** k",
        "def _pow(b, e):", "    return _np.power(_c(b), _c(e))",
        "def _exp(x):", "    return _np.exp(_c(x))",
        "def _log(x):", "    return _np.log(_c(x))",
        "def _sin(x):", "    return _np.sin(_c(x))", "def _cos(x):", "    return _np.cos(_c(x))", "def _tan(x):", "    return _np.tan(_c(x))",
        "def _sinh(x):", "    return _np.sinh(_c(x))", "def _cosh(x):", "    return _np.cosh(_c(x))", "def _tanh(x):", "    return _np.tanh(_c(x))",
        "def _abs(x):", "    return _c(_np.abs(_c(x)))",
        "def _conjugate(x):", "    return _np.conj(_c(x))",
        "def _re(x):", "    return _c(_np.real(_c(x)))", "def _im(x):", "    return _c(_np.imag(_c(x)))",
        "def _surd(x, n):",
        "    # Wolfram Surd: the real n-th root of a real number (odd n: of any sign)",
        "    z = _c(x)",
        "    if z.imag != 0:",
        "        raise ValueError(\"Surd needs a real argument\")",
        "    if z.real < 0 and n % 2 == 0:",
        "        raise ValueError(\"Surd of a negative number needs an odd root\")",
        "    return _c(_np.sign(z.real) * _np.abs(z.real) ** (1.0 / n))",
        "def _context():",
        "    return None"}, {
        "def _context():",
        "    ctx = _mpmath.mp.clone()",
        "    ctx.dps = working_precision",
        "    return ctx",
        "def _c(ctx, x):", "    return ctx.mpc(x)",
        "def _ipow(ctx, b, k):", "    return ctx.mpc(b) ** k",
        "def _pow(ctx, b, e):", "    return ctx.power(ctx.mpc(b), e)",
        "def _exp(ctx, x):", "    return ctx.exp(x)",
        "def _log(ctx, x):", "    return ctx.log(ctx.mpc(x))",
        "def _sin(ctx, x):", "    return ctx.sin(x)", "def _cos(ctx, x):", "    return ctx.cos(x)", "def _tan(ctx, x):", "    return ctx.tan(x)",
        "def _sinh(ctx, x):", "    return ctx.sinh(x)", "def _cosh(ctx, x):", "    return ctx.cosh(x)", "def _tanh(ctx, x):", "    return ctx.tanh(x)",
        "def _abs(ctx, x):", "    return ctx.mpc(abs(x))",
        "def _conjugate(ctx, x):", "    return ctx.conj(ctx.mpc(x))",
        "def _re(ctx, x):", "    return ctx.mpc(ctx.re(x))", "def _im(ctx, x):", "    return ctx.mpc(ctx.im(x))",
        "def _surd(ctx, x, n):",
        "    # Wolfram Surd: the real n-th root of a real number (odd n: of any sign)",
        "    z = ctx.mpc(x)",
        "    if z.imag != 0:",
        "        raise ValueError(\"Surd needs a real argument\")",
        "    r = z.real",
        "    if r < 0 and n % 2 == 0:",
        "        raise ValueError(\"Surd of a negative number needs an odd root\")",
        "    root = ctx.root(abs(r), n)",
        "    return ctx.mpc(-root if r < 0 else root)"}];
    helpers = Join[helpers, {
        "def _step(outputs, compute):",
        "    try:",
        "        return compute()",
        "    except (ZeroDivisionError, OverflowError, ValueError) as error:",
        "        raise EvaluationError(\"output \" + \", \".join(repr(o) for o in outputs) + \" cannot be evaluated at this point: \" + str(error)) from None",
        ""}];
    inputs = If[numpy, {
        "def _scalar(value, where):",
        "    if isinstance(value, bool) or type(value).__name__ in (\"bool\", \"bool_\") or not isinstance(value, _numbers.Number):",
        "        raise TypeError(where + \" must be a number, not \" + type(value).__name__)",
        "    z = complex(value)",
        "    if not (_math.isfinite(z.real) and _math.isfinite(z.imag)):",
        "        raise ValueError(where + \" must be finite\")",
        "    return _c(z)"}, {
        "def _scalar(ctx, value, where):",
        "    if isinstance(value, bool) or type(value).__name__ in (\"bool\", \"bool_\") or not (isinstance(value, _numbers.Number) or hasattr(value, \"_mpf_\") or hasattr(value, \"_mpc_\")):",
        "        raise TypeError(where + \" must be a number, not \" + type(value).__name__)",
        "    if isinstance(value, _fractions.Fraction):",
        "        z = ctx.mpc(ctx.mpf(value.numerator) / value.denominator)",
        "    elif isinstance(value, _decimal.Decimal):",
        "        z = ctx.mpc(ctx.mpf(str(value)))",
        "    elif isinstance(value, _numbers.Integral):",
        "        z = ctx.mpc(int(value))",
        "    else:",
        "        z = ctx.mpc(value)",
        "    if not ctx.isfinite(z):",
        "        raise ValueError(where + \" must be finite\")",
        "    return z"}];
    inputs = Join[inputs, {
        "def _vector(" <> If[numpy, "", "ctx, "] <> "value, length, where):",
        "    if isinstance(value, (str, bytes, bytearray, set, frozenset, _Mapping)) or isinstance(value, _numbers.Number):",
        "        raise TypeError(where + \" must be a sequence of numbers\")",
        "    if getattr(value, \"ndim\", 1) != 1:",
        "        raise ValueError(where + \" must be one-dimensional\")",
        "    try:",
        "        items = list(value)",
        "    except TypeError:",
        "        raise TypeError(where + \" must be a sequence of numbers\") from None",
        "    if len(items) != length:",
        "        raise ValueError(where + \" must have \" + str(length) + \" entries, not \" + str(len(items)))",
        "    return tuple(_scalar(" <> If[numpy, "", "ctx, "] <> "v, where + \"[\" + str(i) + \"]\") for i, v in enumerate(items))",
        "def _validate_inputs(" <> If[numpy, "", "ctx, "] <> "params, fields):",
        "    p = _vector(" <> If[numpy, "", "ctx, "] <> "params, number_of_parameters, \"params\")",
        "    if not field_ids:",
        "        if fields is not None and not (isinstance(fields, _Mapping) and len(fields) == 0):",
        "            raise ValueError(\"this module takes no field values; pass fields=None\")",
        "        return p, {}",
        "    if not isinstance(fields, _Mapping):",
        "        raise TypeError(\"fields must be a mapping from field IDs to full component vectors\")",
        "    if any(not isinstance(k, str) for k in fields):",
        "        raise TypeError(\"field IDs must be strings\")",
        "    missing = [k for k in field_ids if k not in fields]",
        "    extra = sorted(k for k in fields if k not in field_dimensions)",
        "    if missing or extra:",
        "        raise ValueError(\"fields must have exactly the keys \" + repr(field_ids) + \"; missing \" + repr(missing) + \", unexpected \" + repr(extra))",
        "    return p, {k: _vector(" <> If[numpy, "", "ctx, "] <> "fields[k], field_dimensions[k], \"fields[\" + repr(k) + \"]\") for k in field_ids}",
        "def _checked_output(" <> If[numpy, "", "ctx, "] <> "value, shape, name):",
        Sequence @@ If[numpy, {
            "    array = _np.asarray(value, dtype=_np.complex128)",
            "    if array.shape != shape:",
            "        raise EvaluationError(\"output \" + repr(name) + \" has shape \" + repr(array.shape) + \", expected \" + repr(shape))",
            "    if not _np.all(_np.isfinite(array)):",
            "        raise EvaluationError(\"output \" + repr(name) + \" is not finite at this point\")",
            "    return array[()] if shape == () else array"}, {
            "    if shape == ():",
            "        values = [ctx.mpc(value)]",
            "        result = values[0]",
            "    else:",
            "        result = [[ctx.mpc(v) for v in row] for row in value]",
            "        if len(result) != shape[0] or any(len(row) != shape[1] for row in result):",
            "            raise EvaluationError(\"output \" + repr(name) + \" does not have the shape \" + repr(shape))",
            "        values = [v for row in result for v in row]",
            "    if not all(ctx.isfinite(v) for v in values):",
            "        raise EvaluationError(\"output \" + repr(name) + \" is not finite at this point\")",
            "    return result"}],
        ""}];
    (* One function body: unpack inputs, define the needed temporaries (guarded), return the outputs. *)
    body[ks_List] := Module[{needed = Select[Lookup[temporaries, "Name", {}], Function[t, AnyTrue[ks, MemberQ[users[#], t] &]]], usedParams, usedFields, text},
        text = StringRiffle[Join[lower /@ Flatten[Values[KeyTake[outputTrees, ks]]], lower /@ Lookup[Select[temporaries, MemberQ[needed, #["Name"]] &], "Node", {}]], " "];
        usedParams = Select[data["RuntimeParameters"], StringContainsQ[text, RegularExpression["\\b" <> names["Parameters"][#] <> "\\b"]] &];
        usedFields = Select[data["RuntimeFields"], StringContainsQ[text, RegularExpression["\\b" <> names["Fields"][#] <> "\\b"]] &];
        Join[
            If[data["RuntimeParameters"] === {}, {}, {"    " <> StringRiffle[names["Parameters"] /@ data["RuntimeParameters"], ", "] <> If[Length[data["RuntimeParameters"]] === 1, ",", ""] <> " = p"}],
            Map["    " <> names["Fields"][#] <> " = f[" <> pythonStringLiteral[#] <> "]" &, usedFields],
            If[modularQ, Map["    " <> names["Slots"][#] <> " = y[" <> pythonStringLiteral[#] <> "]" &,
                Select[data["Modular"]["RuntimeSlots"], StringContainsQ[text, RegularExpression["\\b" <> names["Slots"][#] <> "\\b"]] &]], {}],
            Map[Function[t, "    " <> t["Name"] <> " = _step(" <> pythonLiteral[Lookup[outputs[[#]], "Name"] & /@ Select[ks, MemberQ[users[#], t["Name"]] &]] <>
                ", lambda: " <> lower[t["Node"]] <> ")"], Select[temporaries, MemberQ[needed, #["Name"]] &]],
            Map[Function[k, With[{o = outputs[[k]], entries = lower /@ outputTrees[k]},
                "    " <> "_out" <> ToString[k] <> " = _checked_output(" <> If[numpy, "", "ctx, "] <> "_step(" <> pythonLiteral[{o["Name"]}] <> ", lambda: " <>
                    If[o["Kind"] === "Scalar", First[entries],
                        "[" <> StringRiffle[Map["[" <> StringRiffle[#, ", "] <> "]" &, Partition[entries, Last[o["Shape"]]]], ", "] <> "]"] <>
                    "), " <> pythonShapeLiteral[o["Shape"]] <> ", " <> pythonStringLiteral[o["Name"]] <> ")"]], ks]]
    ];
    functionLines = Flatten[Map[Function[k, Join[{"def _output_" <> ToString[k] <> "(p, f, " <> y <> "ctx):"},
        If[numpy, {"    with _np.errstate(all=\"ignore\"):"}, {}],
        If[numpy, ("    " <> # &) /@ body[{k}], body[{k}]],
        {If[numpy, "        ", "    "] <> "return _out" <> ToString[k], ""}]], Range[Length[outputs]]]];
    all = Join[{"def _evaluate_all(p, f, " <> y <> "ctx):"}, If[numpy, {"    with _np.errstate(all=\"ignore\"):"}, {}],
        If[numpy, ("    " <> # &) /@ body[Range[Length[outputs]]], body[Range[Length[outputs]]]],
        {If[numpy, "        ", "    "] <> "return {" <> StringRiffle[MapIndexed[pythonStringLiteral[#1["Name"]] <> ": _out" <> ToString[First[#2]] &, outputs], ", "] <> "}", ""}];
    dispatch = {"_OUTPUT_FUNCTIONS = (" <> StringRiffle[Map["_output_" <> ToString[#] &, Range[Length[outputs]]], ", "] <> If[Length[outputs] === 1, ",", ""] <> ")",
        "def _evaluate_output(index, values, field_values, " <> If[modularQ, "slot_values, ", ""] <> "ctx):",
        "    return _OUTPUT_FUNCTIONS[index](values, field_values, " <> If[modularQ, "slot_values, ", ""] <> "ctx)", ""};
    aliasLines = Join[{
        "def evaluate(params, fields=None):",
        "    \"\"\"Every output at one point, as a dict in output order.\"\"\"",
        "    ctx = _context()",
        "    p, f = _validate_inputs(" <> If[numpy, "", "ctx, "] <> "params, fields)",
        "    return _evaluate_all(p, f, ctx)", ""},
        Flatten[MapIndexed[Function[{o, k}, {
            "def " <> names["Functions"][o["Name"]] <> "(params, fields=None):",
            "    \"\"\"The output " <> StringTake[pythonStringLiteral[o["Name"]], {2, -2}] <> " at one point.\"\"\"",
            "    ctx = _context()",
            "    p, f = _validate_inputs(" <> If[numpy, "", "ctx, "] <> "params, fields)",
            "    return _evaluate_output(" <> ToString[First[k] - 1] <> ", p, f, ctx)", ""}], outputs]]];
    If[modularQ, Module[{runtime = modularRuntimeSource[], common = modularModuleSource["common"], model = modularModuleSource["model"]},
        If[AnyTrue[{runtime, common, model}, FailureQ], Return[FirstCase[{runtime, common, model}, _Failure], Module]];
        (* The docstring and imports of a modular module, then the embedded runtime before the manifest. *)
        If[header[[8]] =!= "import math as _math", Return[makeFailure["InvalidPythonArtifact", "Unexpected module header layout."], Module]];
        header = Join[{
            "\"\"\"Generated by VVMFTool: numerical evaluation of the outputs " <> StringRiffle[pythonStringLiteral /@ Lookup[outputs, "Name"], ", "] <>
                " of the modular model " <> pythonStringLiteral[data["ModelName"]] <> ".",
            "",
            "Backend: " <> backend <> If[numpy, " (machine precision).", " (" <> ToString[precision] <> " decimal digits in a private context per call)."],
            "Make a point with tau_point(tau) or q_point(q, sheet) and call evaluate(params, point, fields=None, form_values=None),",
            "evaluate_report(...) or one function per output; see the manifest for the order of params, the field IDs and the form",
            "slots (form_ids, form_descriptors; form_evaluation " <> modular["Policy"]["Mode"] <> "). Do not edit by hand.",
            "\"\"\""}, header[[8 ;; 11]], {"import re as _mm_re", "import time as _mm_time"},
            If[numpy, {"import fractions as _fractions", "import decimal as _decimal"}, {}], {"", runtime}, header[[12 ;;]], modularConstantLines["Model"]];
        aliasLines = Join[{common, model,
            "def evaluate(params, point, fields=None, form_values=None):",
            "    \"\"\"Every output at the point, as a dict in output order.\"\"\"",
            "    return _mm_model(None, params, point, fields, form_values, False)", "",
            "def evaluate_report(params, point, fields=None, form_values=None):",
            "    \"\"\"evaluate(...) with the per-form reports, the estimated final output errors, the strategy and the evidence.\"\"\"",
            "    return _mm_model(None, params, point, fields, form_values, True)", ""},
            Flatten[MapIndexed[Function[{o, k}, {
                "def " <> names["Functions"][o["Name"]] <> "(params, point, fields=None, form_values=None):",
                "    \"\"\"The output " <> StringTake[pythonStringLiteral[o["Name"]], {2, -2}] <> " at the point.\"\"\"",
                "    return _mm_model(" <> ToString[First[k] - 1] <> ", params, point, fields, form_values, False)[" <> pythonStringLiteral[o["Name"]] <> "]", ""}], outputs]]]]];
    lines = Join[header, helpers, inputs, functionLines, all, dispatch, aliasLines];
    <|"Source" -> StringRiffle[lines, "\n"] <> "\n", "Manifest" -> manifest|>
];

(*
    Summary: The Python tuple literal of an output shape.
    Parameters: shape — {} or {r, c}.
    Options/defaults: None.
    Returns: "()" or "(r, c)".
    Effects: Pure.
    Failures: None.
    Example: pythonShapeLiteral[{2, 3}] is "(2, 3)".
    See also: renderPythonModule.
*)
pythonShapeLiteral[shape_List] := "(" <> StringRiffle[ToString /@ shape, ", "] <> If[Length[shape] === 1, ",", ""] <> ")";

(*
    Summary: Validate a PythonArtifact before use.
    Parameters: a — any expression.
    Options/defaults: None.
    Returns: The data, or InvalidPythonArtifact Failure.
    Effects: Pure.
    Failures: Missing fields, an unknown backend, a source whose digest or embedded manifest disagrees with the
        record, or a function in the manifest that the source does not define.
    Example: an artifact whose Source was edited by hand fails here.
    See also: ToPython; ExportPython.
*)
validatePythonArtifact[PythonArtifact[data_Association]] := Module[{invalid, manifest},
    invalid[reason_] := makeFailure["InvalidPythonArtifact", "The Python artifact is malformed.", <|"Reason" -> reason|>];
    If[!SubsetQ[Keys[data], {"SchemaVersion", "Source", "SourceSHA256", "Manifest", "OutputID", "OutputDigest", "Backend", "WorkingPrecision", "Dependencies"}] ||
            data["SchemaVersion"] =!= 1 || !StringQ[data["Source"]] || !AssociationQ[data["Manifest"]],
        Return[invalid["Fields"]]];
    If[!MemberQ[{"NumPy", "mpmath"}, data["Backend"]] || data["Dependencies"] =!= {If[data["Backend"] === "NumPy", "numpy", "mpmath"]},
        Return[invalid["Backend"]]];
    If[IntegerString[Hash[data["Source"], "SHA256"], 16, 64] =!= data["SourceSHA256"], Return[invalid["Source digest"]]];
    manifest = pythonLiteral[data["Manifest"]];
    If[FailureQ[manifest] || !StringContainsQ[data["Source"], "\nmanifest = " <> manifest <> "\n"], Return[invalid["Embedded manifest"]]];
    (* Each module kind has its own public signature (Stage 9: modular model and form modules). *)
    If[!AllTrue[Values[Lookup[data["Manifest"], "function_names", <||>]], StringContainsQ[data["Source"], "\ndef " <> # <> Switch[Lookup[data["Manifest"], "kind", None],
            "ModularModelOutput", "(params, point, fields=None, form_values=None):", "ModularFormOutput", "(point):", _, "(params, fields=None):"]] &],
        Return[invalid["Functions"]]];
    data
];
validatePythonArtifact[___] := makeFailure["InvalidPythonArtifact", "Expected a PythonArtifact."];

Format[PythonArtifact[data_Association], StandardForm] := Interpretation[Row[{"PythonArtifact[", Lookup[data, "Backend", "?"], ", ",
    Length[Lookup[Lookup[data, "Manifest", <||>], "outputs", {}]], " outputs]"}], PythonArtifact[data]];

Options[ToPython] = {PythonBackend -> "NumPy", WorkingPrecision -> Automatic, FunctionNames -> <||>, ParameterNames -> <||>, CommonSubexpressions -> True,
    FormEvaluation -> "Embedded", ExportEvaluationMethod -> Automatic, SeriesOrder -> Automatic, AccuracyGoal -> Automatic, PrecisionGoal -> Automatic,
    MaxSeriesOrder -> 2000, TimeLimit -> 600, RequireProof -> False};

(*
    Summary: Generate a standalone Python module of a prepared model output or of prepared modular forms.
    Parameters: out — ModelOutput (finite-group or modular model) or ModularFormOutput.
    Options/defaults: PythonBackend "NumPy" (machine precision) or "mpmath"; WorkingPrecision Automatic
        (MachinePrecision for NumPy, 50 digits for mpmath; NumPy accepts only MachinePrecision, mpmath an integer of at
        least 16); FunctionNames, ParameterNames — partial maps output name / parameter ID -> identifier;
        CommonSubexpressions True. Modular outputs (Stage 9): FormEvaluation "Embedded" (the module evaluates the frozen
        bound forms) or "External" (model outputs only: the caller supplies form_values); ExportEvaluationMethod
        Automatic ("QSeries", adaptive), "FiniteSeries" (with an integer SeriesOrder, from a stored expansion or jet) or
        "Analytic" (unavailable, as in Stage 7); SeriesOrder Automatic or an integer (start order, or the finite order);
        AccuracyGoal, PrecisionGoal Automatic (half the backend digits, bounded by the source precision; explicit goals at most
        the backend digits - 2); MaxSeriesOrder
        2000; TimeLimit 600 seconds per evaluation; RequireProof False.
    Returns: PythonArtifact (source and manifest), or Failure.
    Effects: Pure; nothing is written, imported or executed.
    Failures: InvalidModelOutput; InvalidModularFormOutput; InvalidOption; UnknownOption; lowering failures;
        InapplicableOption (form options for a finite-group output; ParameterNames or CommonSubexpressions for forms);
        resolveFormExportPolicy failures (MissingBindings, UnresolvedCoefficients, FiniteJet, NotComputed,
        InsufficientOrder, UnsupportedRecipe, MethodUnavailable, IncompatibleOptions, ProofRequired).
    Example: PythonManifest[ToPython[PrepareModelOutput[m, <|"ELMatrix" -> mass|>]]]["parameter_ids"] lists the couplings.
    Remarks: Requesting more mpmath digits than the source data's precision does not add accuracy; the manifest
        records each output's source precision. A finite-group module is rendered exactly as in Stage 6. A modular model
        module defines tau_point(tau), q_point(q, sheet=0), form_ids, form_descriptors, form_evaluation,
        evaluate(params, point, fields=None, form_values=None), evaluate_report(...) and one function per output with that
        signature; a form module defines tau_point, q_point, evaluate(point), evaluate_report(point) and one function per
        form. Both embed the versioned modular runtime (Kernel/Python/modular_runtime.py and modular_module.py) and the
        portable recipes; ModularEvaluationError (a RuntimeError with a code) reports domain, order, time, accuracy and
        recipe failures.
    See also: PythonSource; PythonManifest; ExportPython; PrepareModelOutput.
*)
ToPython[out_ModelOutput, options : OptionsPattern[]] := Module[{effective, data, backend, precision, names, rendered, supplied, modular = None, records, policy, slots},
    effective = resolveOperationOptions[ToPython, "ToPython", {options}];
    If[FailureQ[effective], Return[effective]];
    data = validateModelOutput[out]; If[FailureQ[data], Return[data]];
    supplied = Keys[Association[Flatten[{options}]]];
    backend = effective[PythonBackend];
    precision = pythonPrecision[backend, effective[WorkingPrecision]]; If[FailureQ[precision], Return[precision]];
    If[!KeyExistsQ[data, "Modular"],
        With[{bad = Intersection[supplied, $ModularExportOptions]}, If[bad =!= {},
            Return[makeFailure["InapplicableOption", "Form evaluation options apply only to outputs of modular models.", <|"Options" -> bad|>]]]]];
    names = allocatePythonNames[data, effective[FunctionNames], effective[ParameterNames], If[KeyExistsQ[data, "Modular"], $ModularModuleReserved, {}]];
    If[FailureQ[names], Return[names]];
    (* Stage 9: a modular output exports its runtime slots: frozen bound records (Embedded) or caller values (External). *)
    If[KeyExistsQ[data, "Modular"],
        slots = data["Modular"]["RuntimeSlots"];
        records = Map[Join[#["Record"], <|"BindingProofStatus" -> #["Validation"]["ProofStatus"]|>] &, data["Modular"]["Bindings"]];
        policy = resolveFormExportPolicy["Model", records, data["Modular"]["Unbound"], effective, supplied, If[backend === "NumPy", 16, precision],
            data["Modular"]["Formal"]["Status"]];
        If[FailureQ[policy], Return[policy]];
        names = Append[names, "Slots" -> AssociationThread[slots, Map["_y" <> ToString[#] &, Range[Length[slots]]]]];
        modular = <|"Policy" -> policy, "FormManifest" -> Append[formManifest[policy, Association[Map[# -> If[KeyExistsQ[records, #],
                formManifestEntry[records[#], Lookup[policy["Recipes"], #, Missing[]]], slotDescriptorEntry[data["Modular"]["Slots"][#]]] &, slots]],
            If[backend === "NumPy", 16, precision]], "slot_ids" -> slots]|>];
    rendered = renderPythonModule[data, names, backend, precision, effective[CommonSubexpressions], modular];
    If[FailureQ[rendered], Return[rendered]];
    PythonArtifact[<|"SchemaVersion" -> 1, "Source" -> rendered["Source"], "SourceSHA256" -> IntegerString[Hash[rendered["Source"], "SHA256"], 16, 64],
        "Manifest" -> rendered["Manifest"], "OutputID" -> data["ID"], "OutputDigest" -> IntegerString[Hash[KeyDrop[data, "Context"], "SHA256"], 16, 64],
        "Backend" -> backend, "WorkingPrecision" -> precision, "Dependencies" -> {If[backend === "NumPy", "numpy", "mpmath"]}|>]
];
ToPython[out_ModularFormOutput, options : OptionsPattern[]] := Module[{effective, data, backend, precision, supplied, policy, names, rendered},
    effective = resolveOperationOptions[ToPython, "ToPython", {options}];
    If[FailureQ[effective], Return[effective]];
    data = validateFormOutput[out]; If[FailureQ[data], Return[data]];
    supplied = Keys[Association[Flatten[{options}]]];
    With[{bad = Intersection[supplied, {ParameterNames, CommonSubexpressions}]}, If[bad =!= {},
        Return[makeFailure["InapplicableOption", "A ModularFormOutput has no parameters or shared scalar expressions.", <|"Options" -> bad|>]]]];
    backend = effective[PythonBackend];
    precision = pythonPrecision[backend, effective[WorkingPrecision]]; If[FailureQ[precision], Return[precision]];
    policy = resolveFormExportPolicy["Forms", Map[#["Record"] &, data["Nodes"]], {}, effective, supplied, If[backend === "NumPy", 16, precision], None];
    If[FailureQ[policy], Return[policy]];
    names = allocatePythonNames[<|"Outputs" -> data["Outputs"], "RuntimeParameters" -> {}, "Parameters" -> {}, "RuntimeFields" -> {}, "Fields" -> {}|>,
        effective[FunctionNames], <||>, $ModularModuleReserved];
    If[FailureQ[names], Return[names]];
    rendered = renderFormModule[data, policy, names["Functions"], backend, precision];
    If[FailureQ[rendered], Return[rendered]];
    PythonArtifact[<|"SchemaVersion" -> 1, "Source" -> rendered["Source"], "SourceSHA256" -> IntegerString[Hash[rendered["Source"], "SHA256"], 16, 64],
        "Manifest" -> rendered["Manifest"], "OutputID" -> data["ID"], "OutputDigest" -> data["Digest"],
        "Backend" -> backend, "WorkingPrecision" -> precision, "Dependencies" -> {If[backend === "NumPy", "numpy", "mpmath"]}|>]
];

(*
    Summary: The working precision of a module, and the manifest entry of a slot without a binding (External export).
    Parameters: backend — "NumPy" | "mpmath"; value — the WorkingPrecision option; slot — slot record.
    Options/defaults: None.
    Returns: pythonPrecision: MachinePrecision or digits, or InvalidOption Failure. slotDescriptorEntry: manifest entry
        with the slot's weight, dimension, irrep, basis and assignment, no form and no recipe.
    Effects: Pure.
    Failures: InvalidOption (MachinePrecision for mpmath, digits for NumPy, fewer than 16 digits).
    Example: pythonPrecision["mpmath", Automatic] is 50.
    See also: ToPython.
*)
pythonPrecision[backend_String, value_] := Which[
    value === Automatic, If[backend === "NumPy", MachinePrecision, 50],
    backend === "NumPy" && value === MachinePrecision, MachinePrecision,
    backend === "mpmath" && IntegerQ[value] && value >= 16, value,
    True, makeFailure["InvalidOption", "WorkingPrecision must be MachinePrecision for NumPy and an integer of at least 16 for mpmath.", <|"Options" -> {WorkingPrecision}|>]];
slotDescriptorEntry[slot_Association] := <|"form_id" -> Null, "revision" -> Null, "weight" -> manifestWeight[slot["Weight"]], "dimension" -> slot["Dimension"],
    "irrep" -> slot["IrrepID"], Sequence @@ Normal[manifestIrrepFields[slot["GroupIdentity"], slot["IrrepID"]]], "basis" -> slot["BasisID"], "assignment" -> slot["AssignmentID"], "group" -> slot["GroupIdentity"], "definition_kind" -> Null,
    "normalization" -> Null, "stored_cutoff" -> Null, "evidence" -> <|"Validation" -> "Unbound", "Coefficients" -> Null, "Arithmetic" -> Null, "SourcePrecision" -> Null,
        "Status" -> "ExternallySuppliedUncheckedModularity"|>, "recipe" -> Null|>;
ToPython[___] := makeFailure["InvalidInput", "ToPython expects a ModelOutput or a ModularFormOutput and options."];

(*
    Summary: The Python source and the manifest of an artifact.
    Parameters: a — PythonArtifact.
    Options/defaults: None.
    Returns: String; association; or Failure.
    Effects: Pure.
    Failures: InvalidPythonArtifact.
    Example: StringStartsQ[PythonSource[a], "\"\"\"Generated by VVMFTool"] is True.
    See also: ToPython.
*)
PythonSource[a_PythonArtifact] := With[{data = validatePythonArtifact[a]}, If[FailureQ[data], data, data["Source"]]];
PythonSource[___] := makeFailure["InvalidInput", "PythonSource expects a PythonArtifact."];
PythonManifest[a_PythonArtifact] := With[{data = validatePythonArtifact[a]}, If[FailureQ[data], data, data["Manifest"]]];
PythonManifest[___] := makeFailure["InvalidInput", "PythonManifest expects a PythonArtifact."];

Options[ExportPython] = {Overwrite -> False};

(*
    Summary: Write a generated module to a file.
    Parameters: file — absolute path (relative paths resolve against the current directory); a — PythonArtifact.
    Options/defaults: Overwrite False (refuse an existing file) or True (replace it atomically).
    Returns: The absolute path, or Failure.
    Effects: Writes one file through a temporary sibling and a rename; nothing is imported or executed.
    Failures: InvalidPythonArtifact; ExportFailed (existing file without Overwrite, missing directory, write or rename
        failure; the old file is kept); UnknownOption.
    Example: ExportPython[FileNameJoin[{$TemporaryDirectory, "model.py"}], ToPython[out], Overwrite -> True].
    See also: ToPython; PythonSource.
*)
ExportPython[file_String, a_PythonArtifact, options : OptionsPattern[]] := Module[{effective, data},
    effective = resolveOperationOptions[ExportPython, "ExportPython", {options}];
    If[FailureQ[effective], Return[effective]];
    data = validatePythonArtifact[a]; If[FailureQ[data], Return[data]];
    If[StringLength[file] === 0, Return[makeFailure["ExportFailed", "The file name must not be empty."]]];
    writeDisplayArtifact[ExpandFileName[file], data["Source"], "Text", effective[Overwrite]]
];
ExportPython[___] := makeFailure["InvalidInput", "ExportPython expects a file name, a PythonArtifact and options."];

True
