(*
    :Title: Portable recipes of modular forms
    :Context: VVMFTool`Private`
    :Summary: The closed, JSON-compatible recipe graph of a frozen form record (analytic trees, finite jets, MLDE family
        recipes, derived and transported definitions) with its resolved coefficients substituted, its validation, and the
        portable Python runtime (Kernel/Python/modular_runtime.py) that interprets it. Nothing is ever passed as source.
    :Responsibilities: recipeNumber, radicalRecord, encodeRecipeTree, encodeFormRecipe, validateFormRecipe, modularRuntimeSource,
        modularModuleSource, formManifestEntry, formManifest, modularConstantLines, renderFormModule.
    :Dependencies: ModularFormObjects.wl (records); ModularConstructors.wl (MLDE recipes); RepresentationStorage.wl
        (decimalRecord); Models.wl (numericConstantQ).
    :See Also: VVMFArch/step9Plan.md (embedded evaluation, generated Python series engine); D-S9-1, D-S9-2.
*)

(*
    Summary: The manifest value of a modular weight.
    Parameters: k — exact rational weight.
    Options/defaults: None.
    Returns: An integer weight as itself (manifests written before rational weights are unchanged); a non-integer weight as
        the exact-rational record ["q", p, q] of recipeNumber.
    Effects: Pure.
    Failures: None.
    Example: manifestWeight[1/2] is {"q", "1", "2"}.
    See also: recipeNumber; formManifestEntry; slotDescriptorEntry.
*)
manifestWeight[k_Integer] := k;
manifestWeight[k_Rational] := {"q", ToString[Numerator[k]], ToString[Denominator[k]]};

(*
    Summary: The recipe record of a number.
    Parameters: x — exact or approximate number; digits — decimal digits for a value that is not an exact rational.
    Options/defaults: None.
    Returns: ["q", p, q] for an exact rational, ["c", re, im] for a complex value whose parts are rational records or
        ["d", decimal] real decimals (digits significant digits for exact irrational values, the value's own digits for an
        approximate one), or Failure.
    Effects: Pure.
    Failures: UnsupportedRecipe (a non-numeric or non-finite value).
    Example: recipeNumber[3/4, 30] is {"q", "3", "4"}; recipeNumber[Sqrt[2], 30] is {"c", {"d", "1.414...e0"}, {"q", "0", "1"}}.
    Remarks: Exact rationals stay exact in the runtime (Fraction); other values enter as backend numbers.
    See also: encodeRecipeTree.
*)
recipeNumber[x_, digits_Integer] := Which[
    IntegerQ[x] || Head[x] === Rational, {"q", ToString[Numerator[x]], ToString[Denominator[x]]},
    Head[x] === Complex && AllTrue[ReIm[x], IntegerQ[#] || Head[#] === Rational &], {"c", recipeNumber[Re[x], digits], recipeNumber[Im[x], digits]},
    (* Products of rational powers of rationals (radicals, roots of unity) stay exact: ["a", r, {{base, e}, ...}]. *)
    !FailureQ[radicalRecord[x]], radicalRecord[x],
    NumericQ[x] && FreeQ[N[x], DirectedInfinity | Indeterminate | ComplexInfinity],
        With[{v = If[InexactNumberQ[x] || !FreeQ[x, _Real], x, N[x, digits + 5]]},
            {"c", recipeDecimal[Re[v], digits], recipeDecimal[Im[v], digits]}],
    True, makeFailure["UnsupportedRecipe", "A recipe coefficient must be a finite number.", <|"Value" -> x|>]];
(*
    Summary: The exact radical record of a product of rational powers of rationals.
    Parameters: x — exact number.
    Options/defaults: None.
    Returns: {"a", rational record, {{base, exponent record}, ...}} (integer bases, -1 for signs and roots of unity), or
        Failure when x is not such a product.
    Effects: Pure.
    Failures: NotRadical.
    Example: radicalRecord[2 Sqrt[3]] is {"a", {"q", "2", "1"}, {{"3", {"q", "1", "2"}}}}; I is base -1 with exponent 1/2.
    Remarks: The runtime keeps these values exact (prime powers with exponents in [0, 1)), so constants that differ by a
        rational factor combine without numerical cancellation.
    See also: recipeNumber.
*)
radicalRecord[x_] := Catch[Module[{parts = If[Head[x] === Times, List @@ x, {x}], r = 1, powers = {}},
    Scan[Function[f, Which[
        IntegerQ[f] || Head[f] === Rational, r *= f,
        f === I, AppendTo[powers, {"-1", {"q", "1", "2"}}],
        f === -I, r *= -1; AppendTo[powers, {"-1", {"q", "1", "2"}}],
        MatchQ[f, Power[_Integer | _Rational, _Integer | _Rational]],
            With[{base = f[[1]], e = f[[2]]}, AppendTo[powers, {ToString[Numerator[base]], {"q", ToString[Numerator[e]], ToString[Denominator[e]]}}];
                If[Denominator[base] =!= 1, AppendTo[powers, {ToString[Denominator[base]], {"q", ToString[-Numerator[e]], ToString[Denominator[e]]}}]]],
        True, Throw[makeFailure["NotRadical", "Not a product of rational powers of rationals."], "radical"]]], parts];
    If[powers === {}, Throw[makeFailure["NotRadical", "A rational number."], "radical"]];
    {"a", {"q", ToString[Numerator[r]], ToString[Denominator[r]]}, powers}], "radical"];

recipeDecimal[x_, digits_] := If[x == 0, {"q", "0", "1"}, {"d", pythonDecimal[x, If[Precision[x] === MachinePrecision, 17, Min[digits, Max[1, Floor[Precision[x]]]] /. Infinity -> digits]]}];

(*
    Summary: The recipe tree of a scalar definition tree with resolved coefficients.
    Parameters: e — tree in FormVariable atoms, scalar nodes, numbers (FormParameter atoms already replaced); digits.
    Options/defaults: None.
    Returns: Node association (const, q, qpow, scalar, hyp, plus, times, power), or Failure.
    Effects: Pure.
    Failures: UnsupportedRecipe (unresolved FormParameter, unknown heads, a non-rational power of a series).
    Example: encodeRecipeTree[2 ModularScalarNode["E4", FormVariable["q"], "q"], 30] is a times node of a const and E4.
    Remarks: A numeric subtree becomes one const node; Exp[2 Pi I r tau] becomes qpow r (the cusp branch); the tree's own
        structure is kept, so the runtime reproduces treeSeries exactly.
    See also: encodeFormRecipe.
*)
encodeRecipeTree[e_, digits_Integer] := Catch[recipeTreeNode[e, digits], "recipe"];
recipeTreeNode[e_, digits_] := Which[
    numericConstantQ[e] || (NumericQ[e] && FreeQ[e, FormVariable | ModularScalarNode | HypergeometricKNode]),
        With[{n = recipeNumber[e, digits]}, If[FailureQ[n], Throw[n, "recipe"], <|"node" -> "const", "value" -> n|>]],
    MatchQ[e, FormVariable["q"]], <|"node" -> "q"|>,
    MatchQ[e, Power[E, _]] && !FreeQ[e, FormVariable["tau"]], With[{r = Simplify[e[[2]]/(2 Pi I FormVariable["tau"])]},
        If[MatchQ[r, _Integer | _Rational], <|"node" -> "qpow", "exponent" -> recipeNumber[r, digits]|>,
            Throw[makeFailure["UnsupportedRecipe", "The tau variable must occur as Exp[2 Pi I r tau] with rational r.", <|"Expression" -> e|>], "recipe"]]],
    MatchQ[e, ModularScalarNode[_String, _, _]], <|"node" -> "scalar", "name" -> e[[1]]|>,
    MatchQ[e, HypergeometricKNode[_List, _List, _, _]], <|"node" -> "hyp", "a" -> Map[recipeNumber[#, digits] &, e[[1]]], "b" -> Map[recipeNumber[#, digits] &, e[[2]]]|>,
    MatchQ[e, _Plus], <|"node" -> "plus", "args" -> Map[recipeTreeNode[#, digits] &, List @@ e]|>,
    MatchQ[e, _Times], <|"node" -> "times", "args" -> Map[recipeTreeNode[#, digits] &, List @@ e]|>,
    MatchQ[e, Power[_, _Integer | _Rational]], <|"node" -> "power", "base" -> recipeTreeNode[e[[1]], digits], "exponent" -> recipeNumber[e[[2]], digits]|>,
    !FreeQ[e, _FormParameter], Throw[makeFailure["UnsupportedRecipe", "A recipe needs resolved coefficients (an unresolved FormParameter remains).", <|"Expression" -> e|>], "recipe"],
    True, Throw[makeFailure["UnsupportedRecipe", "The expression is not a portable scalar recipe.", <|"Expression" -> e|>], "recipe"]];

(*
    Summary: The portable recipe of a definition with resolved coefficients.
    Parameters: definition — definition data; rules — {FormParameter[id] -> value, ...}; digits — decimal digits of
        non-rational values.
    Options/defaults: None.
    Returns: <|"kind" -> "analytic" | "jet" | "mlde" | "derived", ... , optional "transform"|>, or Failure.
    Effects: Pure.
    Failures: UnsupportedRecipe; UnresolvedCoefficients (an MLDE scale or tree coefficient without a rule).
    Example: the T' triplet's analytic definition encodes three component trees.
    Remarks: MLDE recipes keep the system, coefficients, leading G coefficients, exponents, weight, seed and the frame
        transport B^-1, with the frame scales c_1 = 1, c_i from the rules and a family key shared by F and G (one family
        node); a derived definition keeps its frozen source recipe and weight; a Transform is a final matrix.
    See also: validateFormRecipe; modularRuntimeSource.
*)
encodeFormRecipe[definition_Association, rules_List, digits_Integer] := Catch[Module[{base, numbers},
    numbers[m_] := If[ListQ[m], Map[numbers, m], With[{n = recipeNumber[m, digits]}, If[FailureQ[n], Throw[n, "formRecipe"], n]]];
    base = Switch[definition["Kind"],
        "Analytic", <|"kind" -> "analytic", "components" -> Map[With[{t = encodeRecipeTree[Expand[# /. rules], digits]}, If[FailureQ[t], Throw[t, "formRecipe"], t]] &,
            definition["Components"]]|>,
        "Jet", With[{jets = qExpansionJets[validateQExpansion[definition["Jet"]]]}, <|"kind" -> "jet", "components" -> Map[<|"terms" ->
            KeyValueMap[{recipeNumber[#1, digits], numbers[#2 /. rules]} &, #["Terms"]], "cutoff" -> If[#["Cutoff"] === Infinity, Null, recipeNumber[#["Cutoff"], digits]]|> &, jets]|>],
        "MLDE", With[{recipe = definition["Recipe"], ids = Lookup[definition["Parameters"], "ID", {}]}, Module[{scales},
            scales = Join[{1}, Map[FormParameter[#] &, ids] /. rules];
            If[!FreeQ[scales, _FormParameter], Throw[makeFailure["UnresolvedCoefficients", "An MLDE recipe needs its frame scales resolved."], "formRecipe"]];
            <|"kind" -> "mlde", "scales" -> numbers[scales], "recipe" -> <|"system" -> recipe["System"],
                "coefficients" -> Map[numbers, recipe["Coefficients"]], "g_leading" -> If[ListQ[recipe["GLeading"]], numbers[recipe["GLeading"]], Null],
                "exponents" -> numbers[recipe["Exponents"]], "weight" -> recipeNumber[recipe["Weight"], digits], "seed" -> recipe["SeedID"],
                "frame_b_inverse" -> numbers[recipe["FrameBInverse"]],
                "family_key" -> Hash[KeyTake[recipe, {"System", "Coefficients", "GLeading", "Exponents", "Weight"}], "SHA256", "HexString"]|>|>]],
        "Derived", With[{source = encodeFormRecipe[definition["Recipe"]["Source"], rules, digits]}, If[FailureQ[source], Throw[source, "formRecipe"],
            <|"kind" -> "derived", "source" -> source, "source_weight" -> recipeNumber[definition["Recipe"]["SourceWeight"], digits]|>]],
        _, Throw[makeFailure["UnsupportedRecipe", "Unknown definition kind.", <|"Kind" -> definition["Kind"]|>], "formRecipe"]];
    If[KeyExistsQ[definition, "Transform"], Append[base, "transform" -> numbers[definition["Transform"]]], base]], "formRecipe"];

(*
    Summary: Check a recipe against the closed grammar.
    Parameters: node — any expression.
    Options/defaults: None.
    Returns: True, or InvalidRecipe Failure with a path.
    Effects: Pure.
    Failures: InvalidRecipe (unknown kinds or nodes, malformed numbers, unknown scalar names or MLDE systems, shape errors).
    Example: validateFormRecipe[<|"kind" -> "analytic", "components" -> {<|"node" -> "eval"|>}|>] fails.
    Remarks: Every recipe passes here before it is written into a module.
    See also: encodeFormRecipe.
*)
validateFormRecipe[node_] := Catch[recipeCheck[node, {}]; True, "recipeCheck"];
recipeCheck[node_, path_] := Module[{fail, number, tree},
    fail[reason_] := Throw[makeFailure["InvalidRecipe", "The form recipe is malformed.", <|"Path" -> path, "Reason" -> reason|>], "recipeCheck"];
    number[x_] := If[!MatchQ[x, {"q", _String, _String} | {"d", _String} | {"c", _, _} | {"a", {"q", _String, _String}, {{_String, {"q", _String, _String}} ...}}] ||
        (First[x] === "c" && !AllTrue[Rest[x], MatchQ[#, {"q", _String, _String} | {"d", _String}] &]), fail["number"]];
    tree[t_, p_] := If[!AssociationQ[t], fail["tree"], Switch[Lookup[t, "node", None],
        "const", number[t["value"]], "q", Null, "qpow", number[t["exponent"]],
        "scalar", If[!MemberQ[{"E2", "E4", "E6", "Eta", "Delta", "j", "K"}, t["name"]], fail["scalar"]],
        "hyp", Scan[number, Join[t["a"], t["b"]]],
        "plus" | "times", If[!ListQ[t["args"]] || Length[t["args"]] < 1, fail["args"]]; MapIndexed[tree[#1, Append[p, First[#2]]] &, t["args"]],
        "power", tree[t["base"], Append[p, 1]]; If[!MatchQ[t["exponent"], {"q", _String, _String}], fail["exponent"]],
        _, fail["node"]]];
    If[!AssociationQ[node], fail["definition"]];
    Switch[Lookup[node, "kind", None],
        "analytic", MapIndexed[tree[#1, {First[#2]}] &, node["components"]],
        "jet", Scan[Function[c, Scan[(number[#[[1]]]; number[#[[2]]]) &, c["terms"]]], node["components"]],
        "mlde", If[!MemberQ[{"Cyclic4D", "NonCyclic4D", "Coupled5D"}, node["recipe"]["system"]] || !MemberQ[{"F", "G"}, node["recipe"]["seed"]], fail["mlde"]];
            Scan[number, Join[node["scales"], Flatten[node["recipe"]["frame_b_inverse"], 1], node["recipe"]["exponents"]]],
        "derived", recipeCheck[node["source"], Append[path, "source"]],
        _, fail["kind"]];
    If[KeyExistsQ[node, "transform"], Scan[number, Flatten[node["transform"], 1]]];
];

(*
    Summary: The source of the portable Python runtime library.
    Parameters: None.
    Options/defaults: None.
    Returns: String (the file Kernel/Python/modular_runtime.py), or Failure.
    Effects: Reads the package file.
    Failures: MissingRuntime.
    Example: StringContainsQ[modularRuntimeSource[], "MR_RUNTIME_VERSION = 1"] is True.
    Remarks: Embedded verbatim into generated modules (one file, no import of package code at run time).
    See also: Kernel/Python/modular_runtime.py.
*)
modularRuntimeSource[] := With[{file = FileNameJoin[{$PackageRoot, "Kernel", "Python", "modular_runtime.py"}]},
    If[FileExistsQ[file], Import[file, "Text"], makeFailure["MissingRuntime", "The modular runtime library is missing.", <|"File" -> file|>]]];

(* -------------------------------------------------------------------------
   Module emission (S9.4)
   ------------------------------------------------------------------------- *)

(* Names a modular module defines (public API) or that its embedded layers use; generated names must avoid them. *)
(* The runtime's own public names (mr_evaluate_definition, MR_RUNTIME_VERSION, ModularEvaluationError) are included: an
   output function of that name would shadow the embedded library. *)
$ModularModuleReserved = {"point", "form_values", "tau_point", "q_point", "evaluate_report", "form_ids", "form_descriptors", "form_evaluation",
    "ModularEvaluationError", "MR_RUNTIME_VERSION", "mr_evaluate_definition", "y", "b"};

(*
    Summary: One section of the modular module API (Kernel/Python/modular_module.py) with the file's header comment.
    Parameters: section — "common", "model" or "forms".
    Options/defaults: None.
    Returns: String, or Failure.
    Effects: Reads the package file.
    Failures: MissingRuntime (no file or no such section).
    Example: StringContainsQ[modularModuleSource["common"], "def tau_point(tau):"] is True.
    Remarks: Embedded verbatim, like the runtime; the sections read the module constants written before them.
    See also: renderFormModule; modularRuntimeSource.
*)
modularModuleSource[section_String] := Module[{file = FileNameJoin[{$PackageRoot, "Kernel", "Python", "modular_module.py"}], parts, sections},
    If[!FileExistsQ[file], Return[makeFailure["MissingRuntime", "The modular module library is missing.", <|"File" -> file|>]]];
    parts = StringSplit[Import[file, "Text"], "# ==== section: "];
    sections = Association[Map[With[{split = StringSplit[#, "\n", 2]}, First[split] -> "# ==== section: " <> First[split] <> "\n" <> Last[split]] &, Rest[parts]]];
    If[KeyExistsQ[sections, section], If[section === "common", First[parts], ""] <> StringTrim[sections[section], "\n" ..] <> "\n",
        makeFailure["MissingRuntime", "The modular module library has no such section.", <|"Section" -> section|>]]
];

(*
    Summary: The manifest entry of one exported form record (a form node or a bound slot).
    Parameters: record — form record (with an optional BindingProofStatus); recipe — portable recipe or Missing (External).
    Options/defaults: None.
    Returns: Association of strings, integers, lists and Null only (pythonLiteral data).
    Effects: Pure.
    Failures: None.
    Example: formManifestEntry[record, recipe]["dimension"] is the form's dimension.
    Remarks: The stored basis, assignment and weight are those the values refer to; the evidence is stored evidence
        (exportEvidence), never re-derived.
    See also: formManifest.
*)
formManifestEntry[record_Association, recipe_] := <|"form_id" -> record["ID"], "revision" -> record["Revision"], "weight" -> manifestWeight[record["Weight"]],
    "dimension" -> record["Dimension"], "irrep" -> If[StringQ[record["IrrepID"]], record["IrrepID"], Null],
    Sequence @@ Normal[manifestIrrepFields[record["Context"], record["IrrepID"]]], "basis" -> record["BasisID"],
    "assignment" -> record["AssignmentID"], "group" -> record["GroupIdentity"], "definition_kind" -> record["Definition"]["Kind"],
    "normalization" -> If[AssociationQ[record["Coefficients"]], <|"kind" -> record["Coefficients"]["Kind"],
        "anchor_frame" -> Replace[Lookup[record["Coefficients"], "AnchorFrameID", Null], _Missing -> Null]|>, Null],
    "stored_cutoff" -> If[MatchQ[record["QExpansion"], _QExpansionData], ToString[record["QExpansion"]["Cutoff"], InputForm], Null],
    "evidence" -> Map[Replace[#, _Missing -> Null] &, exportEvidence[record]],
    "recipe" -> If[AssociationQ[recipe], recipe, Null]|>;

(*
    Summary: The form manifest of a modular module.
    Parameters: policy — resolveFormExportPolicy result; entries — <|key -> formManifestEntry|>; digits — backend digits.
    Options/defaults: None.
    Returns: Association (pythonLiteral data).
    Effects: Pure.
    Failures: None.
    Example: formManifest[policy, entries, 16]["strategy"]["digits"] is 16.
    Remarks: Goals and the time limit are decimal strings (the module converts them); the error semantics are stated:
        successive approximations, no tail bound, finite-series approximations and external values as such.
    See also: renderFormModule; ToPython.
*)
formManifest[policy_Association, entries_Association, digits_Integer] := <|"runtime_version" -> 1, "evaluation" -> policy["Mode"],
    "strategy" -> <|"mode" -> policy["Mode"], "method" -> Replace[policy["Method"], _Missing -> Null], "series_order" -> If[IntegerQ[policy["SeriesOrder"]], policy["SeriesOrder"], Null],
        "accuracy_goal" -> If[NumberQ[policy["AccuracyGoal"]], pythonDecimal[policy["AccuracyGoal"], 17], Null],
        "precision_goal" -> If[NumberQ[policy["PrecisionGoal"]], pythonDecimal[policy["PrecisionGoal"], 17], Null],
        "max_series_order" -> If[IntegerQ[policy["MaxSeriesOrder"]], policy["MaxSeriesOrder"], Null],
        "time_limit" -> If[policy["TimeLimit"] === Infinity, Null, pythonDecimal[policy["TimeLimit"], 17]], "digits" -> digits,
        "require_proof" -> TrueQ[policy["RequireProof"]]|>,
    "branch_convention" -> "q^r means exp(2 pi i r tau); a q point uses 2 pi i tau = log(q) + 2 pi i sheet (principal log); no fundamental-domain reduction.",
    "error_semantics" -> Switch[{policy["Mode"], policy["Method"]},
        {"External", _}, "Form values are supplied by the caller (ExternallySuppliedUncheckedModularity); their error and the final output error are unknown (UnknownExternalError).",
        {_, "FiniteSeries"}, "Finite series approximation at the exported order (FiniteSeriesApproximation); no tail bound.",
        _, "Adaptive q-series: the estimated error is the agreement of successive approximations, never below the roundoff floor of the values (10^-(digits - 2) relative to the larger of the value and its summed terms); for model outputs it is propagated through the outputs (the previous approximation and each slot component moved by its floor along the real and the imaginary axis, never off an axis on which it lies exactly; each output's error is at least the roundoff of its value). An estimate, not a rigorous bound; goals stay at least two digits below the backend digits."],
    "entries" -> entries|>;

(*
    Summary: The module-constant lines shared by modular modules (recipes, evidence, dimensions, policy).
    Parameters: kind — "Model" or "Forms".
    Options/defaults: None.
    Returns: List of source lines.
    Effects: Pure.
    Failures: None.
    Example: modularConstantLines["Forms"] defines _MM_OUTPUT_NODES.
    See also: renderFormModule; renderPythonModule.
*)
modularConstantLines[kind_String] := Join[{
    "_MM_RECIPES = {k: e[\"recipe\"] for k, e in manifest[\"forms\"][\"entries\"].items()}",
    "_MM_EVIDENCE = {k: e[\"evidence\"] for k, e in manifest[\"forms\"][\"entries\"].items()}",
    "_MM_DIMENSIONS = {k: e[\"dimension\"] for k, e in manifest[\"forms\"][\"entries\"].items()}",
    "_MM_POLICY = dict(manifest[\"forms\"][\"strategy\"])",
    "_MM_POLICY[\"time_limit\"] = float(\"inf\") if _MM_POLICY[\"time_limit\"] is None else float(_MM_POLICY[\"time_limit\"])",
    "for _mm_key in (\"accuracy_goal\", \"precision_goal\"):",
    "    if _MM_POLICY[_mm_key] is not None:",
    "        _MM_POLICY[_mm_key] = float(_MM_POLICY[_mm_key])"},
    If[kind === "Model", {
        "form_ids = tuple(manifest[\"forms\"][\"slot_ids\"])",
        "form_descriptors = {k: {key: value for key, value in e.items() if key != \"recipe\"} for k, e in manifest[\"forms\"][\"entries\"].items()}",
        "form_evaluation = manifest[\"forms\"][\"evaluation\"]",
        "_MM_OUTPUT_SLOTS = tuple(tuple(o[\"slots\"]) for o in manifest[\"outputs\"])"}, {
        "form_ids = tuple(manifest[\"forms\"][\"entries\"])",
        "_MM_OUTPUT_NODES = tuple(o[\"node\"] for o in manifest[\"outputs\"])"}],
    {""}];

(*
    Summary: The Python source of a module evaluating a ModularFormOutput.
    Parameters: data — validated ModularFormOutput data; policy — resolveFormExportPolicy result (Embedded); functions —
        <|output name -> Python name|>; backend — "NumPy" | "mpmath"; precision — MachinePrecision or decimal digits.
    Options/defaults: None.
    Returns: <|"Source", "Manifest"|>, or Failure.
    Effects: Reads the embedded library files.
    Failures: MissingRuntime; UnsupportedLiteral.
    Example: renderFormModule[d, policy, <|"Y" -> "Y"|>, "mpmath", 60]["Source"] defines tau_point, evaluate and Y.
    Remarks: The module defines manifest, backend, working_precision, output_names, output_shapes, function_names, form_ids,
        tau_point(tau), q_point(q, sheet=0), evaluate(point) (ordered dict of vectors: NumPy shape (d,) or mpmath lists),
        evaluate_report(point) and one function per output name; ModularEvaluationError (a RuntimeError) reports time, order,
        precision, domain and recipe failures with a code; bad input types or shapes raise TypeError or ValueError.
    See also: ToPython; formManifest.
*)
renderFormModule[data_Association, policy_Association, functions_Association, backend_String, precision_] := Module[
    {numpy = backend === "NumPy", digits, manifest, manifestSource, runtime, common, forms, outputs = data["Outputs"], entries, lines},
    digits = If[numpy, 16, precision];
    runtime = modularRuntimeSource[]; If[FailureQ[runtime], Return[runtime]];
    common = modularModuleSource["common"]; If[FailureQ[common], Return[common]];
    forms = modularModuleSource["forms"]; If[FailureQ[forms], Return[forms]];
    entries = Association[KeyValueMap[#1 -> formManifestEntry[#2["Record"], Lookup[policy["Recipes"], #1, Missing[]]] &, data["Nodes"]]];
    manifest = <|"schema" -> 1, "generator" -> "VVMFTool", "generator_version" -> "unversioned (alpha)", "wolfram_version" -> $Version, "kind" -> "ModularFormOutput",
        "output_id" -> data["ID"], "digest" -> data["Digest"], "backend" -> backend,
        "working_precision" -> If[precision === MachinePrecision, "MachinePrecision", ToString[precision]],
        "outputs" -> Map[<|"name" -> #["Name"], "function" -> functions[#["Name"]], "shape" -> #["Shape"], "node" -> #["NodeID"], "form_id" -> #["FormID"],
            "revision" -> #["Revision"], "weight" -> manifestWeight[#["Weight"]], "irrep" -> If[StringQ[#["IrrepID"]], #["IrrepID"], Null],
            Sequence @@ Normal[manifestIrrepFields[#["GroupIdentity"], #["IrrepID"]]], "basis" -> #["BasisID"],
            "assignment" -> #["AssignmentID"], "group" -> #["GroupIdentity"]|> &, outputs],
        "function_names" -> functions, "forms" -> formManifest[policy, entries, digits]|>;
    manifestSource = pythonLiteral[manifest]; If[FailureQ[manifestSource], Return[manifestSource]];
    lines = Join[{
        "\"\"\"Generated by VVMFTool: portable evaluation of the modular forms " <> StringRiffle[pythonStringLiteral /@ Lookup[outputs, "Name"], ", "] <> ".",
        "",
        "Backend: " <> backend <> If[numpy, " (machine precision).", " (" <> ToString[precision] <> " decimal digits in a private context per call)."],
        "Make a point with tau_point(tau) or q_point(q, sheet) and call evaluate(point), evaluate_report(point) or one",
        "function per form. Values come from the q-series of the frozen recipes in `manifest` (embedded VVMF modular",
        "runtime); estimated errors are the agreement of successive approximations, not rigorous bounds. Do not edit by hand.",
        "\"\"\"",
        "import math as _math",
        "import numbers as _numbers",
        "import re as _mm_re",
        "import time as _mm_time",
        "import fractions as _fractions",
        "import decimal as _decimal",
        If[numpy, "import numpy as _np", "import mpmath as _mpmath"],
        "",
        runtime,
        "manifest = " <> manifestSource,
        "backend = " <> pythonStringLiteral[backend],
        "working_precision = " <> If[numpy, "None", ToString[precision]],
        "output_names = tuple(o[\"name\"] for o in manifest[\"outputs\"])",
        "output_shapes = {o[\"name\"]: tuple(o[\"shape\"]) for o in manifest[\"outputs\"]}",
        "function_names = dict(manifest[\"function_names\"])"},
        modularConstantLines["Forms"],
        {common, forms,
        "def evaluate(point):",
        "    \"\"\"Every form at the point, as a dict of component vectors in output order.\"\"\"",
        "    return _mm_forms(None, point, False)",
        "",
        "def evaluate_report(point):",
        "    \"\"\"evaluate(point) with each form's order, estimated error, status and evidence, and the strategy.\"\"\"",
        "    return _mm_forms(None, point, True)",
        ""},
        Flatten[MapIndexed[Function[{o, k}, {
            "def " <> functions[o["Name"]] <> "(point):",
            "    \"\"\"The form " <> StringTake[pythonStringLiteral[o["Name"]], {2, -2}] <> " at the point (a vector).\"\"\"",
            "    return _mm_forms(" <> ToString[First[k] - 1] <> ", point, False)[" <> pythonStringLiteral[o["Name"]] <> "]", ""}], outputs]]];
    <|"Source" -> StringRiffle[lines, "\n"] <> "\n", "Manifest" -> manifest|>
];

True
