(*
    :Title: Archives of modular forms and modular models
    :Context: VVMFTool`Private`
    :Summary: The closed archive codec of Stage 7 records (tagged values, definition trees), SaveModularFormData and
        ImportModularFormData (validated, all-or-none publication of fresh form handles), and the modular part of model
        archives (SaveModelData / ImportModelData of a Stage 8 model).
    :Responsibilities: encodeArchiveValue, decodeArchiveValue, definitionArchiveTree, decodeDefinitionArchiveTree,
        contextArchiveRecord, encodeFormArchive, validateFormArchive, rebindArchivedRecord, checkExpansionCorrespondence,
        distrustRecord, rebaseImportedRecord, decodeFormArchive, importArchiveGroup; encodeModularModelArchive,
        validateModularModelArchive, decodeModularModelArchive; SaveModularFormData, ImportModularFormData.
    :Dependencies: ModelSerialization.wl (modelGroupSource, rebindModelContext); GroupStorage.wl (writeResult, readResult,
        decodeGroupSnapshot, publishRegisteredImport, validateImportedGroup); ExportLedger.wl (registerExport,
        trustedExportRecord); PythonIR.wl (encodeScalarTree); ModularFormObjects.wl; ModularOperations.wl (expandForm,
        expansionBinding); ModularBindings.wl (checkBoundSpaceIndependence); ModularCandidates.wl (recomputeSlotRecord).
    :See Also: VVMFArch/step9Plan.md (Mathematical serialization); step9Status.md (D-S9-13, D-S9-14).
*)

$FormArchiveFormat = "VVMFToolModularForms";
$FormArchiveSchemaVersion = 1;
$ArchiveSymbols = <|"Infinity" -> Infinity, "-Infinity" -> -Infinity, "Automatic" -> Automatic, "None" -> None, "All" -> All, "MachinePrecision" -> MachinePrecision|>;
$NoRegistry = <|"Parameters" -> {}, "Fields" -> <||>|>;

(* -------------------------------------------------------------------------
   Codec
   ------------------------------------------------------------------------- *)

(*
    Summary: Encode a value of a Stage 7/8 record as JSON-compatible archive data.
    Parameters: x — strings, booleans, Null, lists, associations, rules, Missing, the symbols Infinity, -Infinity, Automatic,
        None, All, MachinePrecision, numbers (exact, algebraic, numerical), GroupWord, Rep, QExpansionData, FormComponent,
        FieldComponent, Coupling and definition expressions (FormVariable, FormParameter, ModularScalarNode,
        HypergeometricKNode, MLDEComponentNode, ModularDerivativeNode, Plus, Times, Power).
    Options/defaults: None.
    Returns: Archive data (strings, booleans, Null, lists and associations; other values as {"$" -> tag, ...}), or
        UnsupportedArchiveValue Failure with the path of the first value outside the closed grammar.
    Effects: Pure.
    Failures: UnsupportedArchiveValue (any other head, a context object, a function or source text).
    Example: encodeArchiveValue[<|"k" -> 1/2|>] is <|"$" -> "assoc", "k" -> {"k"}, "v" -> {<|"$" -> "num", ...|>}|>.
    Remarks: Numbers keep their structure and precision through the Stage 6 scalar trees (D-S6-2); nothing is ever
        archived as code or evaluated on decoding (D-S9-13).
    See also: decodeArchiveValue; definitionArchiveTree.
*)
encodeArchiveValue[x_] := Catch[archiveValue[x, {}], "archiveValue"];

(*
    Summary: Encode and decode an exact rational modular weight in an archive.
    Parameters: k — exact rational; data — archived weight.
    Options/defaults: None.
    Returns: encodeModularWeight: an integer keeps the integer string encoding (archives written before rational weights
        stay valid); a non-integer becomes the exact rational record {"q", p, q}. decodeModularWeight: the rational, or
        Failure.
    Effects: Pure.
    Failures: InvalidArchive (decode of anything else).
    Example: decodeModularWeight[encodeModularWeight[1/2]] is 1/2; encodeModularWeight[2] is "2".
    See also: encodeModularModelArchive; decodeModularModelArchive.
*)
encodeModularWeight[k_Integer] := encodeInteger[k];
encodeModularWeight[k_Rational] := {"q", encodeInteger[Numerator[k]], encodeInteger[Denominator[k]]};
decodeModularWeight[data_String] := With[{k = decodeInteger[data]}, If[IntegerQ[k], k, makeFailure["InvalidArchive", "Invalid archived weight."]]];
decodeModularWeight[{"q", p_String, q_String}] := With[{n = decodeInteger[p], d = decodeInteger[q]},
    If[IntegerQ[n] && IntegerQ[d] && d > 1 && GCD[n, d] === 1, n/d, makeFailure["InvalidArchive", "Invalid archived rational weight."]]];
decodeModularWeight[___] := makeFailure["InvalidArchive", "Invalid archived weight."];
archiveValue[x_, path_List] := Module[{fail, sub},
    fail[] := Throw[makeFailure["UnsupportedArchiveValue", "A record value is outside the archive grammar.", <|"Path" -> path, "Head" -> ToString[Head[x], InputForm]|>],
        "archiveValue"];
    sub[y_, k_] := archiveValue[y, Append[path, k]];
    Which[
        StringQ[x] || x === True || x === False || x === Null, x,
        ListQ[x], MapIndexed[sub[#1, First[#2]] &, x],
        AssociationQ[x], <|"$" -> "assoc", "k" -> MapIndexed[sub[#1, {"key", First[#2]}] &, Keys[x]], "v" -> KeyValueMap[sub[#2, #1] &, x]|>,
        MissingQ[x], <|"$" -> "missing", "v" -> MapIndexed[sub[#1, First[#2]] &, List @@ x]|>,
        MatchQ[x, _Rule], <|"$" -> "rule", "k" -> sub[x[[1]], "key"], "v" -> sub[x[[2]], "value"]|>,
        MemberQ[Values[$ArchiveSymbols], x] && !NumericQ[x] || x === MachinePrecision, <|"$" -> "sym", "v" -> First[Keys[Select[$ArchiveSymbols, # === x &]]]|>,
        MatchQ[x, GroupWord[{{_String, _Integer} ...}]], <|"$" -> "word", "v" -> Map[{#[[1]], encodeInteger[#[[2]]]} &, First[x]]|>,
        Head[x] === Rep, With[{s = repStructure[x]}, If[FailureQ[s], fail[], <|"$" -> "rep", "dimension" -> encodeInteger[s["Dimension"]], "v" -> sub[s["Matrices"], "matrices"]|>]],
        Head[x] === QExpansionData && AssociationQ[First[x]], <|"$" -> "qexp", "v" -> sub[First[x], "qexpansion"]|>,
        MatchQ[x, FormComponent[_String, _Integer]], <|"$" -> "form", "slot" -> x[[1]], "index" -> encodeInteger[x[[2]]]|>,
        MatchQ[x, FieldComponent[_String, _Integer]], <|"$" -> "field", "id" -> x[[1]], "index" -> encodeInteger[x[[2]]]|>,
        MatchQ[x, Coupling[_String]], <|"$" -> "coupling", "id" -> x[[1]]|>,
        NumericQ[x], With[{t = encodeScalarTree[x, $NoRegistry]}, If[FailureQ[t], fail[], <|"$" -> "num", "tree" -> t|>]],
        True, With[{t = Catch[definitionArchiveTree[x], "definitionTree"]}, If[FailureQ[t], fail[], <|"$" -> "expr", "tree" -> t|>]]]
];

(*
    Summary: Decode archive data written by encodeArchiveValue.
    Parameters: data — archive data.
    Options/defaults: None.
    Returns: The value, or InvalidArchive Failure with a path.
    Effects: Pure.
    Failures: InvalidArchive (unknown tags, malformed records, scalar trees that fail validateScalarTree, definition trees
        outside the grammar).
    Example: decodeArchiveValue[encodeArchiveValue[x]] === x for every supported x.
    See also: encodeArchiveValue.
*)
decodeArchiveValue[data_] := Catch[archiveDecode[data, {}], "archiveDecode"];
(* Exact key set of a tagged archive value (both sides in canonical order). *)
keysQ[data_Association, keys_List] := Sort[Keys[data]] === Sort[keys];
archiveDecode[data_, path_List] := Module[{fail, sub, tag},
    fail[reason_] := Throw[makeFailure["InvalidArchive", "The archive contains a malformed value.", <|"Path" -> path, "Reason" -> reason|>], "archiveDecode"];
    sub[y_, k_] := archiveDecode[y, Append[path, k]];
    Which[
        StringQ[data] || data === True || data === False || data === Null, data,
        ListQ[data], MapIndexed[sub[#1, First[#2]] &, data],
        !AssociationQ[data] || !StringQ[Lookup[data, "$", None]], fail["Not a tagged value"],
        True, tag = data["$"];
        Switch[tag,
            "assoc", If[!keysQ[data, {"$", "k", "v"}] || !ListQ[data["k"]] || !ListQ[data["v"]] || Length[data["k"]] =!= Length[data["v"]], fail["assoc"]];
                With[{keys = MapIndexed[sub[#1, {"key", First[#2]}] &, data["k"]]}, If[!DuplicateFreeQ[keys], fail["duplicate keys"]];
                    AssociationThread[keys, MapIndexed[sub[#1, First[#2]] &, data["v"]]]],
            "missing", If[!keysQ[data, {"$", "v"}] || !ListQ[data["v"]], fail["missing"]]; Missing @@ MapIndexed[sub[#1, First[#2]] &, data["v"]],
            "rule", If[!keysQ[data, {"$", "k", "v"}], fail["rule"]]; Rule[sub[data["k"], "key"], sub[data["v"], "value"]],
            "sym", If[!keysQ[data, {"$", "v"}] || !KeyExistsQ[$ArchiveSymbols, data["v"]], fail["symbol"]]; $ArchiveSymbols[data["v"]],
            "word", If[!keysQ[data, {"$", "v"}] || !MatchQ[data["v"], {{_String, _String} ...}] || !AllTrue[data["v"][[All, 2]], IntegerQ[decodeInteger[#]] &], fail["word"]];
                GroupWord[Map[{#[[1]], decodeInteger[#[[2]]]} &, data["v"]]],
            "rep", If[!keysQ[data, {"$", "dimension", "v"}] || !IntegerQ[decodeInteger[data["dimension"]]], fail["rep"]];
                With[{m = sub[data["v"], "matrices"]}, If[!ListQ[m] || !AllTrue[m, MatrixQ[#, NumericQ] &], fail["rep matrices"]];
                    If[m === {}, Rep[{}, decodeInteger[data["dimension"]]], Rep[m]]],
            "qexp", If[!keysQ[data, {"$", "v"}], fail["qexp"]]; With[{q = QExpansionData[sub[data["v"], "qexpansion"]]},
                If[FailureQ[validateQExpansion[q]], fail["qexp data"], q]],
            "form", If[!keysQ[data, {"$", "index", "slot"}] || !StringQ[data["slot"]] || !IntegerQ[decodeInteger[data["index"]]], fail["form"]];
                FormComponent[data["slot"], decodeInteger[data["index"]]],
            "field", If[!keysQ[data, {"$", "id", "index"}] || !StringQ[data["id"]] || !IntegerQ[decodeInteger[data["index"]]], fail["field"]];
                FieldComponent[data["id"], decodeInteger[data["index"]]],
            "coupling", If[!keysQ[data, {"$", "id"}] || !StringQ[data["id"]], fail["coupling"]]; Coupling[data["id"]],
            "num", If[!keysQ[data, {"$", "tree"}] || !TrueQ[validateScalarTree[data["tree"], $NoRegistry]], fail["number"]]; scalarTreeValue[data["tree"]],
            "expr", If[!keysQ[data, {"$", "tree"}], fail["expression"]]; With[{e = Catch[decodeDefinitionArchiveTree[data["tree"]], "definitionTree"]},
                If[FailureQ[e], fail["expression tree"], e]],
            _, fail["Unknown tag " <> tag]]]
];

(*
    Summary: The archive tree of a definition expression, and its decoding.
    Parameters: e — expression of the definition grammar; node — archive tree.
    Options/defaults: None.
    Returns: Tree association, or the expression; both throw a Failure to "definitionTree" outside the grammar.
    Effects: Pure.
    Failures: UnsupportedArchiveValue (encoding); InvalidArchive (decoding).
    Example: decodeDefinitionArchiveTree[definitionArchiveTree[FormParameter["f:c"] ModularScalarNode["E4", FormVariable["q"], "q"]]]
        returns the same expression.
    Remarks: Unlike the display tree, ingredients keep their variable and coordinate, so the decoded expression is
        SameQ to the original; numbers are Stage 6 scalar trees.
    See also: encodeArchiveValue; modularDisplayTree.
*)
definitionArchiveTree[e_] := Which[
    NumericQ[e], With[{t = encodeScalarTree[e, $NoRegistry]}, If[FailureQ[t], Throw[t, "definitionTree"], <|"node" -> "num", "tree" -> t|>]],
    MatchQ[e, FormVariable[_String]], <|"node" -> "variable", "name" -> e[[1]]|>,
    MatchQ[e, FormParameter[_String]], <|"node" -> "parameter", "id" -> e[[1]]|>,
    MatchQ[e, ModularScalarNode[_String, _, _String]], <|"node" -> "ingredient", "name" -> e[[1]], "variable" -> definitionArchiveTree[e[[2]]], "coordinate" -> e[[3]]|>,
    MatchQ[e, HypergeometricKNode[_List, _List, _, _String]], <|"node" -> "hypergeometric", "a" -> Map[definitionArchiveTree, e[[1]]], "b" -> Map[definitionArchiveTree, e[[2]]],
        "variable" -> definitionArchiveTree[e[[3]]], "coordinate" -> e[[4]]|>,
    MatchQ[e, MLDEComponentNode[_String, _String, _Integer]], <|"node" -> "mlde", "family" -> e[[1]], "seed" -> e[[2]], "component" -> encodeInteger[e[[3]]]|>,
    MatchQ[e, ModularDerivativeNode[_?modularWeightQ, _]], <|"node" -> "derivative", "weight" -> encodeModularWeight[e[[1]]], "arg" -> definitionArchiveTree[e[[2]]]|>,
    Head[e] === Plus, <|"node" -> "plus", "args" -> Map[definitionArchiveTree, List @@ e]|>,
    Head[e] === Times, <|"node" -> "times", "args" -> Map[definitionArchiveTree, List @@ e]|>,
    MatchQ[e, Power[_, _]], <|"node" -> "power", "base" -> definitionArchiveTree[e[[1]]], "exponent" -> definitionArchiveTree[e[[2]]]|>,
    True, Throw[makeFailure["UnsupportedArchiveValue", "An expression is outside the definition grammar.", <|"Head" -> ToString[Head[e], InputForm]|>], "definitionTree"]];
decodeDefinitionArchiveTree[node_] := Module[{fail, keys},
    fail[] := Throw[makeFailure["InvalidArchive", "A definition tree is malformed."], "definitionTree"];
    If[!AssociationQ[node] || !StringQ[Lookup[node, "node", None]], fail[]];
    keys = Sort[Keys[node]];
    Switch[node["node"],
        "num", If[keys =!= {"node", "tree"} || !TrueQ[validateScalarTree[node["tree"], $NoRegistry]], fail[]]; scalarTreeValue[node["tree"]],
        "variable", If[keys =!= {"name", "node"} || !MemberQ[{"q", "tau"}, node["name"]], fail[]]; FormVariable[node["name"]],
        "parameter", If[keys =!= {"id", "node"} || !StringQ[node["id"]], fail[]]; FormParameter[node["id"]],
        "ingredient", If[keys =!= {"coordinate", "name", "node", "variable"} || !MemberQ[$ScalarModularNames, node["name"]] || !MemberQ[{"q", "tau"}, node["coordinate"]], fail[]];
            ModularScalarNode[node["name"], decodeDefinitionArchiveTree[node["variable"]], node["coordinate"]],
        "hypergeometric", If[keys =!= {"a", "b", "coordinate", "node", "variable"} || !ListQ[node["a"]] || !ListQ[node["b"]] || !MemberQ[{"q", "tau"}, node["coordinate"]], fail[]];
            With[{a = Map[decodeDefinitionArchiveTree, node["a"]], b = Map[decodeDefinitionArchiveTree, node["b"]]},
                If[!AllTrue[Join[a, b], MatchQ[#, _Integer | _Rational] &], fail[]];
                HypergeometricKNode[a, b, decodeDefinitionArchiveTree[node["variable"]], node["coordinate"]]],
        "mlde", If[keys =!= {"component", "family", "node", "seed"} || !StringQ[node["family"]] || !StringQ[node["seed"]] || !IntegerQ[decodeInteger[node["component"]]], fail[]];
            MLDEComponentNode[node["family"], node["seed"], decodeInteger[node["component"]]],
        "derivative", If[keys =!= {"arg", "node", "weight"} || !modularWeightQ[decodeModularWeight[node["weight"]]], fail[]];
            ModularDerivativeNode[decodeModularWeight[node["weight"]], decodeDefinitionArchiveTree[node["arg"]]],
        "plus" | "times", If[keys =!= {"args", "node"} || !ListQ[node["args"]] || Length[node["args"]] < 2, fail[]];
            If[node["node"] === "plus", Plus, Times] @@ Map[decodeDefinitionArchiveTree, node["args"]],
        "power", If[keys =!= {"base", "exponent", "node"}, fail[]]; Power[decodeDefinitionArchiveTree[node["base"]], decodeDefinitionArchiveTree[node["exponent"]]],
        _, fail[]]
];

(*
    Summary: The archive pointer record of a frozen context: state generation, assignment and representation variants.
    Parameters: snapshot — context snapshot (First of a RepresentationContext).
    Options/defaults: None.
    Returns: <|"stateGeneration", "assignmentIdentity", "representations"|> (the context record of model archives).
    Effects: Pure.
    Failures: None.
    Example: contextArchiveRecord[First[ModularFormData[y]["Context"]]]["assignmentIdentity"] is the assignment ID.
    See also: rebindModelContext.
*)
contextArchiveRecord[snapshot_Association] := <|"stateGeneration" -> encodeInteger[snapshot["StateGeneration"]],
    "assignmentIdentity" -> Replace[Lookup[Replace[snapshot["ModularAssignment"], Except[_Association] -> <||>], "Identity", Null], _Missing -> Null],
    "representations" -> Map[<|"variants" -> Keys[#["Variants"]], "activeVariant" -> Replace[#["ActiveVariant"], _Missing -> Null],
        "acceptedPartial" -> Replace[#["AcceptedPartial"], _Missing -> Null]|> &, snapshot["Representations"]]|>;

(* -------------------------------------------------------------------------
   Form archives
   ------------------------------------------------------------------------- *)

(*
    Summary: The archive of named form records.
    Parameters: names — ordered <|name -> form ID|>; records — <|form ID -> record|>; source — modelGroupSource result.
    Options/defaults: None.
    Returns: <|"format", "schemaVersion", "group" -> snapshot, "contexts" -> <|key -> context record|>, "nodes" -> <|"ID@revision"
        -> <|"context" -> key, "record" -> encoded record without its context object|>|>, "outputs" -> {<|"name", "node"|>...}|>,
        or Failure.
    Effects: Pure.
    Failures: UnsupportedArchiveValue.
    Example: two names of one form share one node.
    Remarks: Each record is archived whole at its revision (definition, coefficients and anchor frame, stored expansion
        with its binding and cutoff, evidence and provenance); a derivative or basis change keeps its frozen source inside
        its definition; MLDE families keep their recipe and cached solution.
    See also: SaveModularFormData; decodeFormArchive.
*)
encodeFormArchive[names_Association, records_Association, source_Association] := Catch[Module[{contexts, nodes},
    contexts = <||>; nodes = <||>;
    KeyValueMap[Function[{id, record}, Module[{snapshot = First[record["Context"]], key, encoded},
        key = "context-" <> StringTake[Hash[contextArchiveRecord[snapshot], "SHA256", "HexString"], 16];
        contexts[key] = contextArchiveRecord[snapshot];
        encoded = encodeArchiveValue[KeyDrop[record, "Context"]];
        If[FailureQ[encoded], Throw[Failure[First[encoded], Join[Last[encoded], <|"FormID" -> id|>]], "formArchive"]];
        nodes[id <> "@" <> ToString[record["Revision"]]] = <|"context" -> key, "record" -> encoded|>]], records];
    <|"format" -> $FormArchiveFormat, "schemaVersion" -> $FormArchiveSchemaVersion, "group" -> source["Snapshot"], "contexts" -> contexts, "nodes" -> nodes,
        "outputs" -> KeyValueMap[<|"name" -> #1, "node" -> #2 <> "@" <> ToString[records[#2]["Revision"]]|> &, names]|>
], "formArchive"];

(*
    Summary: Check the structure of a form archive (before any group or record is touched).
    Parameters: archive — read archive data.
    Options/defaults: None.
    Returns: The archive, or InvalidFormArchive Failure.
    Effects: Pure.
    Failures: InvalidFormArchive (format, version, keys, empty or duplicate names, outputs naming absent nodes, nodes naming
        absent contexts, unused nodes, malformed context records).
    Example: an archive whose output names a missing node fails here.
    See also: ImportModularFormData.
*)
validateFormArchive[archive_] := Module[{invalid},
    invalid[reason_] := makeFailure["InvalidFormArchive", "The modular form archive is malformed.", <|"Reason" -> reason|>];
    If[!resultFieldsQ[archive, {"format", "schemaVersion", "group", "contexts", "nodes", "outputs"}] || archive["format"] =!= $FormArchiveFormat ||
            archive["schemaVersion"] =!= $FormArchiveSchemaVersion, Return[invalid["Format"]]];
    If[!AssociationQ[archive["contexts"]] || !AllTrue[Values[archive["contexts"]], Function[c, resultFieldsQ[c, {"stateGeneration", "assignmentIdentity", "representations"}] &&
            IntegerQ[decodeInteger[c["stateGeneration"]]] && (c["assignmentIdentity"] === Null || StringQ[c["assignmentIdentity"]]) && AssociationQ[c["representations"]] &&
            AllTrue[Values[c["representations"]], resultFieldsQ[#, {"variants", "activeVariant", "acceptedPartial"}] && ListQ[#["variants"]] && AllTrue[#["variants"], StringQ] &]]],
        Return[invalid["Contexts"]]];
    If[!AssociationQ[archive["nodes"]] || !AllTrue[Values[archive["nodes"]], resultFieldsQ[#, {"context", "record"}] && KeyExistsQ[archive["contexts"], #["context"]] &],
        Return[invalid["Nodes"]]];
    If[!ListQ[archive["outputs"]] || archive["outputs"] === {} || !AllTrue[archive["outputs"], resultFieldsQ[#, {"name", "node"}] && StringQ[#["name"]] &&
            StringLength[#["name"]] > 0 && KeyExistsQ[archive["nodes"], #["node"]] &] || !DuplicateFreeQ[Lookup[archive["outputs"], "name"]] ||
            Sort[Keys[archive["nodes"]]] =!= Sort[DeleteDuplicates[Lookup[archive["outputs"], "node"]]],
        Return[invalid["Outputs"]]];
    archive
];
validateFormArchive[___] := makeFailure["InvalidFormArchive", "Expected archive data."];

(*
    Summary: Bind a decoded record to a rebound context, refreshing its owner-current identities.
    Parameters: record — decoded record (no context); context — RepresentationContext of the import.
    Options/defaults: None.
    Returns: The record with Context, ContextDigest, GroupIdentity and GeneratorIdentity of the new context, or Failure.
    Effects: Representation validation of a record whose basis is not a stored variant of the context.
    Failures: ContextNotRebindable (another assignment; a representation that is not the context's variant and not a
        validated representation of the recorded irrep; an S, T action that cannot be bound).
    Example: a T' triplet record rebinds to the imported group with the same Rep and BasisID.
    Remarks: The record's assignment must be the context's; its representation either is the stored variant with the
        recorded basis identity, or (after a basis change) a validated homomorphism whose matched irrep is the recorded
        one and whose content identity is the recorded basis ID. Historical references (DerivedFrom, Provenance sources,
        frozen derived sources) are not touched.
    See also: decodeFormArchive.
*)
rebindArchivedRecord[record_Association, context_RepresentationContext] := Module[{snapshot = First[context], variant, report, fail},
    fail[reason_] := makeFailure["ContextNotRebindable", "An archived form does not fit the imported group context.", <|"Reason" -> reason, "FormID" -> Lookup[record, "ID", Missing[]]|>];
    If[!AssociationQ[snapshot["ModularAssignment"]] || snapshot["ModularAssignment"]["Identity"] =!= record["AssignmentID"], Return[fail["Assignment"]]];
    variant = If[StringQ[record["IrrepID"]], cgVariant[snapshot, record["IrrepID"]], Missing[]];
    If[!(AssociationQ[variant] && variant["Identity"] === record["BasisID"] && variant["Rep"] === record["Rep"]),
        (* the import's correspondence proof (as ImportGroupData's full mode): the full check, never a session level *)
        report = ValidateRepresentation[context, record["Rep"], Verification -> Automatic];
        If[FailureQ[report] || !TrueQ[report["Homomorphism"]] || (StringQ[record["IrrepID"]] && report["Irreducible"] =!= record["IrrepID"]) ||
                repIdentity[record["Rep"], snapshot["GeneratorNames"]] =!= record["BasisID"],
            Return[fail["Representation"]]]];
    If[FailureQ[modularGeneratorMatrix[context, record["Rep"], "S"]] || FailureQ[modularGeneratorMatrix[context, record["Rep"], "T"]], Return[fail["S,T action"]]];
    Join[record, <|"Context" -> context, "ContextDigest" -> contextDigest[snapshot], "GroupIdentity" -> snapshot["GroupIdentity"],
        "GeneratorIdentity" -> snapshot["GeneratorIdentity"]|>]
];

(*
    Summary: Check a stored q-expansion against a recomputation from the record's definition and coefficients.
    Parameters: record — rebound record.
    Options/defaults: None.
    Returns: True (nothing stored, or every stored coefficient reproduced), or ExpansionMismatch Failure.
    Effects: Temporary series (to the stored cutoff only).
    Failures: ExpansionMismatch (a coefficient, exponent or cutoff differs); expansion failures.
    Example: a forged coefficient in an archived expansion fails here.
    Remarks: The stored binding decides whether coefficients are applied (Raw keeps the parameters); exact coefficients
        must agree exactly (jetZeroQ of the difference), numerical ones within their own precision.
    See also: decodeFormArchive; expandForm.
*)
checkExpansionCorrespondence[record_Association] := Module[{stored = record["QExpansion"], data, recomputed, jets, mine},
    If[!MatchQ[stored, _QExpansionData], Return[True]];
    data = validateQExpansion[stored]; If[FailureQ[data], Return[data]];
    recomputed = expandForm[record, data["Cutoff"], data["Binding"] =!= "Raw"]; If[FailureQ[recomputed], Return[recomputed]];
    jets = qExpansionJets[First[recomputed]]; mine = qExpansionJets[data];
    If[Lookup[mine, "Cutoff"] =!= Lookup[jets, "Cutoff"] ||
            !AllTrue[Transpose[{Lookup[mine, "Terms"], Lookup[jets, "Terms"]}], Function[pair, With[{keys = Union[Keys[pair[[1]]], Keys[pair[[2]]]]},
                AllTrue[keys, Function[k, With[{a = Lookup[pair[[1]], k, 0], b = Lookup[pair[[2]], k, 0]},
                    If[InexactNumberQ[a] || InexactNumberQ[b], Abs[a - b] <= 10^(-Max[1, Min[Precision[{a, b}] /. MachinePrecision -> 15.9, 50] - 5]) Max[1, Abs[b]],
                        jetZeroQ[a - b]]]]]]]],
        makeFailure["ExpansionMismatch", "A stored q-expansion does not match its definition and coefficients.", <|"FormID" -> record["ID"]|>],
        True]
];

(*
    Summary: Remove archived claims of proof from a record or binding that is not a trusted export (D-S9-14).
    Parameters: record — form record; validation — binding Validation association.
    Options/defaults: None.
    Returns: distrustRecord: the record with Validation <|"Status" -> "Unverified", "Archived" -> old|> (recipe evidence
        moved there, so ValidateModularForm cannot reuse it) and coefficient proof statuses "Proven" replaced by
        "ArchivedUnverified" (distrustProof, at every depth); distrustBinding: the binding validation with ProofStatus "ArchivedUnverified" when it claimed
        any evidence ("Proven", "NumericalEvidence", ...) and the archived report kept under "Archived".
    Effects: Pure.
    Failures: None.
    Example: an untrusted archived "Proven" status never makes an imported form proven.
    See also: decodeFormArchive; decodeModularModelArchive.
*)
distrustRecord[record_Association] := Join[record, <|"Validation" -> <|"Status" -> "Unverified", "Archived" -> record["Validation"]|>,
    "Coefficients" -> distrustProof[record["Coefficients"]]|>];
(* Every "ProofStatus" -> "Proven" inside a coefficient record (and its nested solve result) becomes "ArchivedUnverified". *)
distrustProof[a_Association] := Association[KeyValueMap[#1 -> If[#1 === "ProofStatus" && #2 === "Proven", "ArchivedUnverified", distrustProof[#2]] &, a]];
distrustProof[l_List] := Map[distrustProof, l];
distrustProof[x_] := x;
(* An untrusted binding claim is never served: "Proven" and also a numerical report ("NumericalEvidence", ...) become
   "ArchivedUnverified", since nothing re-checks the frozen record on import (methodOptionsPlan.md 2C.5, P4). Claims that
   are already no evidence stay. *)
distrustBinding[validation_Association] := If[MemberQ[{"ArchivedUnverified", "Unchecked", "Failed", "Incomplete"}, validation["ProofStatus"]], validation,
    Join[validation, <|"ProofStatus" -> "ArchivedUnverified", "Archived" -> validation|>]];

(*
    Summary: Give a validated imported record its fresh identity.
    Parameters: record — rebound record at its archived ID and revision; path — archive file.
    Options/defaults: None.
    Returns: The record with a new ID, Revision 1, its stored expansion's source rebased to revision 1 and its rules binding
        recomputed, and Provenance SourceIdentity <|"ID", "Revision", "File"|>; or Failure.
    Effects: Allocates an ID.
    Failures: InvalidModularForm (the rebased record fails validateFormRecord).
    Example: rebaseImportedRecord[r, file]["Provenance"]["SourceIdentity"]["ID"] is the archived ID.
    Remarks: Revision 1 is the creation revision of every Stage 7 handle (the plan's "0": validateFormRecord requires at least
        1). Only owner-current references change; frozen historical sources keep their archived identities.
    See also: decodeFormArchive.
*)
rebaseImportedRecord[record_Association, path_String] := Module[{new = Join[record, <|"ID" -> "modularform-" <> CreateUUID[], "Revision" -> 1,
        "Provenance" -> Join[record["Provenance"], <|"SourceIdentity" -> <|"ID" -> record["ID"], "Revision" -> record["Revision"], "File" -> path|>|>]|>], qexp},
    qexp = record["QExpansion"];
    If[MatchQ[qexp, _QExpansionData], new["QExpansion"] = QExpansionData[Join[First[qexp], <|
        "Source" -> If[AssociationQ[qexp["Source"]], Join[qexp["Source"], <|"Revision" -> 1|>], qexp["Source"]],
        "Binding" -> If[StringStartsQ[qexp["Binding"], "Rules-"], expansionBinding[new, True], qexp["Binding"]]|>]]];
    validateFormRecord[new]
];

(*
    Summary: Decode, rebind, check and rebase every record of a validated archive (nothing is published).
    Parameters: archive — validated archive; contexts — <|key -> RepresentationContext|>; trusted — Boolean; path — file.
    Options/defaults: None.
    Returns: <|"Records" -> <|node -> new record|>, "Names" -> <|name -> node|>|>, or the first Failure.
    Effects: Representation validation and temporary series; no registry change.
    Failures: InvalidArchive; ContextNotRebindable; InvalidModularForm; ExpansionMismatch.
    Example: a two-name archive of one form gives one record.
    See also: ImportModularFormData.
*)
decodeFormArchive[archive_Association, contexts_Association, trusted_, path_String] := Catch[Module[{records},
    records = Association[KeyValueMap[Function[{node, entry}, Module[{record = decodeArchiveValue[entry["record"]], checked},
        If[FailureQ[record], Throw[record, "formImport"]];
        If[!AssociationQ[record] || Lookup[record, "ID", None] <> "@" <> ToString[Lookup[record, "Revision", None]] =!= node,
            Throw[makeFailure["InvalidFormArchive", "A node does not hold the record it names.", <|"Node" -> node|>], "formImport"]];
        checked = rebindArchivedRecord[record, contexts[entry["context"]]]; If[FailureQ[checked], Throw[checked, "formImport"]];
        checked = validateFormRecord[checked]; If[FailureQ[checked], Throw[checked, "formImport"]];
        (* The archived expansion must correspond at the archived ID and revision, before any rebasing. *)
        With[{c = checkExpansionCorrespondence[checked]}, If[FailureQ[c], Throw[c, "formImport"]]];
        checked = If[TrueQ[trusted], checked, distrustRecord[checked]];
        checked = rebaseImportedRecord[checked, path]; If[FailureQ[checked], Throw[checked, "formImport"]];
        node -> checked]], archive["nodes"]]];
    <|"Records" -> records, "Names" -> Association[Map[#["name"] -> #["node"] &, archive["outputs"]]]|>
], "formImport"];

(*
    Summary: Admit the group snapshot of an archive (trusted export or independent validation) and record the import.
    Parameters: snapshot — archived group snapshot; before — the archive's read digest; effective — import options
        (ValidationGroup and job options); operation — operation name; path — archive file.
    Options/defaults: As ImportModelData.
    Returns: <|"Group" -> Group, "Trusted" -> Boolean (a registered export admitted without a ValidationGroup)|>, or Failure.
    Effects: Publishes or validates the group (Stage 1 rules) and commits the import record.
    Failures: decodeGroupSnapshot, identity, ledger and group validation failures.
    Example: an archive saved in this kernel's ledger is trusted.
    Remarks: Extracted unchanged from ImportModelData (Stage 6), which now calls it too.
    See also: ImportModelData; ImportModularFormData.
*)
importArchiveGroup[snapshot_, before_Association, effective_Association, operation_String, path_String] := Module[{decoded, known, trusted, group, data, patch, committed},
    (* the identities first (structure only, methodOptionsPlan.md 2C.6); a registered archive's group is then read at its
       recorded group status, as ImportGroupData reads a registered file; any other is re-proved in GAP
       (validateImportedGroup), which publishes a fully checked group *)
    decoded = Block[{$GroupAcceptanceLevel = None}, decodeGroupSnapshot[snapshot]]; If[FailureQ[decoded], Return[decoded]];
    trusted = trustedExportRecord[before, decoded["Identity"]]; If[FailureQ[trusted], Return[trusted]];
    If[TrueQ[trusted] && effective[ValidationGroup] === Automatic,
        decoded = Block[{$GroupAcceptanceLevel = groupStatusLevel[trustedExportStatus[before]]}, decodeGroupSnapshot[snapshot]];
        If[FailureQ[decoded], Return[decoded]]];
    known = checkKnownGroupIdentities[decoded["Data"]]; If[FailureQ[known], Return[known]];
    group = If[TrueQ[trusted] && effective[ValidationGroup] === Automatic,
        publishRegisteredImport[decoded, before, effective],
        validateImportedGroup[decoded, effective[ValidationGroup], effective]];
    If[FailureQ[group], Return[group]];
    data = groupData[group];
    patch = <|"IrrepOrder" -> decoded["IrrepOrder"], "RepresentationCache" -> emptyRepresentationCache[decoded["CacheEpoch"]],
        Sequence @@ Normal[decoded["Presentation"]], "LastComputation" -> Join[data["LastComputation"], <|"Operation" -> operation,
            "Validation" -> If[TrueQ[trusted] && effective[ValidationGroup] === Automatic, "RegisteredExport", "GroupCorrespondence"], "SourceFile" -> path|>]|>;
    committed = commitGroup[group, data["Revision"], patch]; If[FailureQ[committed], Return[committed]];
    <|"Group" -> group, "Trusted" -> TrueQ[trusted] && effective[ValidationGroup] === Automatic|>
];

Options[SaveModularFormData] = {Overwrite -> False};

(*
    Summary: Save named modular forms as a validated mathematical archive.
    Status: Alpha.
    Parameters: forms — nonempty ordered association name -> ModularForm (the same form may appear under several names), or
        one ModularForm (saved under the name "Form"); file — target path.
    Options/defaults: Overwrite -> False.
    Returns: The absolute path, or Failure (no file is changed).
    Effects: One consistent snapshot per form; an atomic write; registers the export (its group identity) in the local
        ledger so this kernel's imports can trust it.
    Failures: InvalidInput; UnknownModularForm; MixedGroups (forms of several group states: save them separately);
        GroupUnavailable / ContextNotRebindable (the forms' group is not loaded or changed incompatibly);
        UnsupportedArchiveValue; ExportFailed (an existing file without Overwrite); write failures.
    Example: SaveModularFormData[<|"YTriplet" -> y|>, FileNameJoin[{$TemporaryDirectory, "forms.json"}], Overwrite -> True].
    Remarks: The archive holds versioned JSON data only (the group snapshot, frozen-context pointers and every record with
        its definition, coefficients, anchor frame, stored expansion and evidence); no code, no GAP state, no display
        caches. Saving never computes, expands or changes a form.
    See also: ImportModularFormData; SaveModelData.
*)
SaveModularFormData[y_ModularForm, file_String, options : OptionsPattern[]] := SaveModularFormData[<|"Form" -> y|>, file, options];
SaveModularFormData[forms_Association, file_String, options : OptionsPattern[]] := Module[{effective, records, states, source, archive, path, written, registered, ids},
    effective = resolveOperationOptions[SaveModularFormData, "SaveModularFormData", {options}]; If[FailureQ[effective], Return[effective]];
    If[StringLength[file] === 0, Return[makeFailure["SaveFailed", "The archive filename must not be empty."]]];
    If[forms === <||> || !AllTrue[Keys[forms], StringQ[#] && StringLength[#] > 0 &] || !AllTrue[Values[forms], Head[#] === ModularForm &],
        Return[makeFailure["InvalidInput", "SaveModularFormData expects a nonempty association of names to modular forms."]]];
    ids = Map[First, forms];
    records = AssociationMap[snapshotForm[ModularForm[#]] &, DeleteDuplicates[Values[ids]]];
    If[AnyTrue[records, FailureQ], Return[FirstCase[Values[records], _Failure]]];
    states = DeleteDuplicates[Map[#["GroupIdentity"] &, Values[records]]];
    If[Length[states] > 1, Return[makeFailure["MixedGroups", "The forms belong to several group states; save each group's forms in its own archive.", <|"States" -> states|>]]];
    (* The group snapshot must rebind every form's frozen context. *)
    source = None;
    Do[With[{s = modelGroupSource[First[record["Context"]]]}, If[FailureQ[s], Return[s, Module]];
        If[source === None, source = s, If[s["Decoded"]["Identity"] =!= source["Decoded"]["Identity"],
            Return[makeFailure["MixedGroups", "The forms' contexts resolve to different group states."], Module]]]], {record, Values[records]}];
    archive = encodeFormArchive[ids, records, source]; If[FailureQ[archive], Return[archive]];
    path = ExpandFileName[file];
    If[FileType[path] === File && !TrueQ[effective[Overwrite]], Return[makeFailure["ExportFailed", "The target exists; use Overwrite -> True to replace it.", <|"File" -> path|>]]];
    written = writeResult[path, archive]; If[FailureQ[written], Return[written]];
    registered = registerExport[path, source["Decoded"]["Identity"], written, groupIdentityBindings[source["Decoded"]["Data"]],
        subgroupClassWitnesses[source["Decoded"]["Data"]],
        cgWeakestStatus[Join[{groupRecordsStatus[source["Decoded"]["Data"]]}, formVerificationStatus /@ Values[records]]],
        groupVerificationStatus[source["Decoded"]["Data"]]];
    If[FailureQ[registered], Failure[registered[[1]], Join[registered[[2]], <|"SavedFile" -> path|>]], path]
];
SaveModularFormData[___] := makeFailure["InvalidInput", "SaveModularFormData expects named modular forms (or one ModularForm), a file name and options."];

Options[ImportModularFormData] = Join[Options[RestoreGAPState], {ValidationGroup -> Automatic}];

(*
    Summary: Import a modular form archive as fresh, independent form handles.
    Status: Alpha.
    Parameters: file — archive path.
    Options/defaults: ValidationGroup -> Automatic (a registered export of this kernel's ledger is trusted; otherwise the
        group is validated independently, as ImportModelData) and the GAP job options.
    Returns: Ordered association name -> new ModularForm (names of one archived form share one new handle), or Failure.
    Effects: Admits the group (Stage 1 rules); after every record has been decoded, rebound, checked (representation,
        assignment, record schema, stored-expansion correspondence) and rebased, publishes all new forms at once (all or
        none).
    Failures: FileUnavailable; ImportChanged; InvalidFormArchive; InvalidArchive; group admission failures;
        ContextNotRebindable; ExpansionMismatch; InvalidModularForm.
    Example: imported = ImportModularFormData[file]; QExpansionView[imported["YTriplet"]].
    Remarks: New handles never alias an existing form; they start at revision 1 with their imported computational state
        (a stored expansion is current and viewable at once) and record the archived ID and revision as SourceIdentity.
        Archived proof claims are kept only for a trusted export; otherwise they are moved under "Archived" and the form is
        Unverified (D-S9-14).
    See also: SaveModularFormData; ImportModelData.
*)
ImportModularFormData[file_String, options : OptionsPattern[]] := Module[{effective, path},
    effective = resolveOperationOptions[ImportModularFormData, "ImportModularFormData", {options}]; If[FailureQ[effective], Return[effective]];
    If[StringLength[file] === 0, Return[makeFailure["FileUnavailable", "The archive filename must not be empty."]]];
    path = ExpandFileName[file];
    withProgress[effective, "ImportModularFormData", Function[Null, Module[{before, archive, after, valid, admitted, contexts, decoded, handles},
        before = fileDigest[path]; If[FailureQ[before], Return[before]];
        archive = readResult[path]; If[FailureQ[archive], Return[archive]];
        after = fileDigest[path];
        If[before =!= after, Return[makeFailure["ImportChanged", "The archive changed while being read."]]];
        valid = validateFormArchive[archive]; If[FailureQ[valid], Return[valid]];
        admitted = importArchiveGroup[archive["group"], before, effective, "ImportModularFormData", path]; If[FailureQ[admitted], Return[admitted]];
        contexts = Map[rebindModelContext[<|"context" -> #|>, admitted["Group"]] &, archive["contexts"]];
        If[AnyTrue[contexts, FailureQ], Return[FirstCase[Values[contexts], _Failure]]];
        decoded = decodeFormArchive[archive, contexts, admitted["Trusted"], path]; If[FailureQ[decoded], Return[decoded]];
        (* All or none: every record is complete before any is published, and they are published in one registry update
           that an abort cannot interrupt. *)
        AbortProtect[AssociateTo[$ModularFormRecords, Map[#["ID"] -> # &, Values[decoded["Records"]]]]];
        handles = Map[ModularForm[#["ID"]] &, decoded["Records"]];
        Map[handles[#] &, decoded["Names"]]
    ]]]
];
ImportModularFormData[___] := makeFailure["InvalidInput", "ImportModularFormData expects an archive filename and options."];

(* -------------------------------------------------------------------------
   Modular model archives (the "modular" part of SaveModelData / ImportModelData)
   ------------------------------------------------------------------------- *)

(*
    Summary: The modular part of a model archive.
    Parameters: model — validated modular model data.
    Options/defaults: None.
    Returns: <|"assignmentID", "fieldWeights", "superpotentialWeight", "slotNamespaceID", "spaces", "slots", "bindings" -> <|slot ->
        <|"binding", "record"|>|>, "slotCouplings"|> (archive data), or Failure.
    Effects: Pure.
    Failures: UnsupportedArchiveValue.
    Example: an unbound model archives its slots with no bindings.
    Remarks: Bindings are archived as frozen values (their records without the context object), independently of whether
        the source forms are still live; per-space independence evidence and assignment words are recomputed on import.
    See also: decodeModularModelArchive; SaveModelData.
*)
encodeModularModelArchive[model_Association] := Catch[Module[{md = model["ModularData"], enc},
    enc[x_, where_] := With[{v = encodeArchiveValue[x]}, If[FailureQ[v], Throw[Failure[First[v], Join[Last[v], <|"Where" -> where|>]], "modularArchive"], v]];
    Join[<|"assignmentID" -> md["AssignmentID"], "fieldWeights" -> enc[md["FieldWeights"], "FieldWeights"], "superpotentialWeight" -> encodeModularWeight[md["SuperpotentialWeight"]],
        "slotNamespaceID" -> md["SlotNamespaceID"], "spaces" -> enc[md["Spaces"], "Spaces"], "slots" -> enc[md["Slots"], "Slots"],
        "bindings" -> Association[KeyValueMap[#1 -> <|"binding" -> enc[KeyDrop[#2, "Record"], #1], "record" -> enc[KeyDrop[#2["Record"], "Context"], #1]|> &, md["Bindings"]]],
        "slotCouplings" -> enc[md["SlotCouplings"], "SlotCouplings"]|>,
        (* only models with supplied spaces carry the key, so earlier archives keep their exact form *)
        If[Lookup[md, "SuppliedSpaces", <||>] === <||>, <||>, <|"suppliedSpaces" -> enc[md["SuppliedSpaces"], "SuppliedSpaces"]|>]]
], "modularArchive"];

(*
    Summary: Check the structure of the modular part of a model archive.
    Parameters: record — the "modular" value.
    Options/defaults: None.
    Returns: Boolean.
    Effects: Pure.
    Failures: None.
    Example: a binding without its record is rejected.
    See also: validateModelArchive.
*)
validateModularModelArchive[record_] := (resultFieldsQ[record, {"assignmentID", "fieldWeights", "superpotentialWeight", "slotNamespaceID", "spaces", "slots", "bindings",
        "slotCouplings"}] || resultFieldsQ[record, {"assignmentID", "fieldWeights", "superpotentialWeight", "slotNamespaceID", "spaces", "slots", "bindings",
        "slotCouplings", "suppliedSpaces"}]) && StringQ[record["assignmentID"]] && StringQ[record["slotNamespaceID"]] && modularWeightQ[decodeModularWeight[record["superpotentialWeight"]]] &&
    AssociationQ[record["bindings"]] && AllTrue[Values[record["bindings"]], resultFieldsQ[#, {"binding", "record"}] &];

(*
    Summary: The slot IDs of a modular archive (for the tree registry of its terms and matrices).
    Parameters: record — the "modular" value.
    Options/defaults: None.
    Returns: List of slot IDs, or {} when the slots do not decode.
    Effects: Pure.
    Failures: None.
    Example: an L.R.Y archive has one slot ID.
    See also: validateModelArchive.
*)
archivedSlotIDs[record_] := With[{slots = decodeArchiveValue[Lookup[Replace[record, Except[_Association] -> <||>], "slots", Null]]},
    If[AssociationQ[slots] && AllTrue[Keys[slots], StringQ], Keys[slots], {}]];

(*
    Summary: Rebuild the modular data of an imported model in its rebound context.
    Parameters: record — the "modular" value; data — the imported model data so far (fields, context, terms without slots);
        context — rebound RepresentationContext; trusted — Boolean (registered export).
    Options/defaults: None.
    Returns: <|"ModularData" -> modular data, "Slots" -> rebuilt slot records|>, or Failure.
    Effects: Representation validation, dimension cache reads, temporary series (independence evidence).
    Failures: InvalidArchive; InvalidModelArchive (an assignment other than the context's, a slot that recomputes to another
        ID); ContextNotRebindable; InvalidModularForm; ExpansionMismatch; checkBoundSpaceIndependence failures.
    Example: an archived bound T' model rebuilds one slot and one binding with recomputed evidence.
    Remarks: Owner-current identities (context digest, group and generator identities, assignment words) come from the new
        context; slots are recomputed in the archived namespace and must keep their IDs; each frozen binding record is
        rebound, checked against its stored expansion, and loses archived proof claims unless the export is trusted;
        per-space independence is recomputed with BindModularForms' defaults (WorkingPrecision 40, SeriesOrder Automatic).
    See also: ImportModelData; recomputeSlotRecord; checkBoundSpaceIndependence.
*)
decodeModularModelArchive[record_Association, data_Association, context_RepresentationContext, trusted_] := Catch[Module[
    {snapshot = First[context], digest, fail, weights, spaces, slots, rebuilt, bindings, couplings, md, model, evidence},
    fail[reason_] := Throw[makeFailure["InvalidModelArchive", "The modular part of the model archive does not match its context.", <|"Reason" -> reason|>], "modularImport"];
    digest = contextDigest[snapshot];
    If[!AssociationQ[snapshot["ModularAssignment"]] || snapshot["ModularAssignment"]["Identity"] =!= record["assignmentID"], fail["Assignment"]];
    {weights, spaces, slots, couplings} = Map[decodeArchiveValue, Lookup[record, {"fieldWeights", "spaces", "slots", "slotCouplings"}]];
    If[AnyTrue[{weights, spaces, slots, couplings}, FailureQ], Throw[FirstCase[{weights, spaces, slots, couplings}, _Failure], "modularImport"]];
    If[!AllTrue[{weights, spaces, slots, couplings}, AssociationQ] || Keys[weights] =!= Lookup[data["Fields"], "ID", {}] || !AllTrue[Values[weights], modularWeightQ], fail["Weights"]];
    md = <|"SchemaVersion" -> 1, "AssignmentID" -> record["assignmentID"], "AssignmentWords" -> KeyTake[snapshot["ModularAssignment"], {"S", "T"}],
        "FieldWeights" -> weights, "ActualFieldWeights" -> Map[actualFieldWeight, weights], "SuperpotentialWeight" -> decodeModularWeight[record["superpotentialWeight"]],
        "SlotNamespaceID" -> record["slotNamespaceID"], "Spaces" -> spaces, "Slots" -> <||>, "Bindings" -> <||>, "SlotCouplings" -> couplings|>;
    (* supplied spaces precede the slot recomputation: their slots exist only through them *)
    If[KeyExistsQ[record, "suppliedSpaces"], With[{supplied = decodeArchiveValue[record["suppliedSpaces"]]},
        If[FailureQ[supplied], Throw[supplied, "modularImport"]]; If[!AssociationQ[supplied], fail["SuppliedSpaces"]];
        md["SuppliedSpaces"] = supplied]];
    model = Join[data, <|"ModularData" -> md|>];
    (* Slots are recomputed in the archived namespace and the new context; their IDs must not change. *)
    rebuilt = Association[KeyValueMap[Function[{id, slot}, With[{r = If[AssociationQ[slot], recomputeSlotRecord[model, Join[slot, <|"ContextDigest" -> digest|>]], slot]},
        If[!AssociationQ[r] || r["ID"] =!= id, fail["Slot " <> id], id -> r]]], slots]];
    md["Slots"] = rebuilt; model["ModularData"] = md;
    bindings = Association[KeyValueMap[Function[{id, entry}, Module[{binding = decodeArchiveValue[entry["binding"]], frozen = decodeArchiveValue[entry["record"]], checked},
        If[FailureQ[binding], Throw[binding, "modularImport"]]; If[FailureQ[frozen], Throw[frozen, "modularImport"]];
        If[!KeyExistsQ[rebuilt, id] || !AssociationQ[binding] || !AssociationQ[frozen] || Lookup[binding, "SlotID", None] =!= id, fail["Binding " <> id]];
        checked = rebindArchivedRecord[frozen, context]; If[FailureQ[checked], Throw[checked, "modularImport"]];
        checked = validateFormRecord[checked]; If[FailureQ[checked], Throw[checked, "modularImport"]];
        With[{c = checkExpansionCorrespondence[checked]}, If[FailureQ[c], Throw[c, "modularImport"]]];
        If[!TrueQ[trusted], checked = distrustRecord[checked]];
        id -> Join[binding, <|"Record" -> checked, "FormID" -> checked["ID"], "Revision" -> checked["Revision"],
            "Validation" -> If[TrueQ[trusted], binding["Validation"], distrustBinding[binding["Validation"]]]|>]]], record["bindings"]]];
    md["Bindings"] = bindings; model["ModularData"] = md;
    (* Independence evidence is recomputed, never read. *)
    evidence = Association[Map[Function[space, With[{bound = Select[Values[rebuilt], #["SpaceID"] === space && KeyExistsQ[bindings, #["ID"]] &]},
        space -> checkBoundSpaceIndependence[model, bound, KeyTake[bindings, Lookup[bound, "ID"]], <|SeriesOrder -> Automatic, WorkingPrecision -> 40|>]]],
        DeleteDuplicates[Lookup[Select[Values[rebuilt], KeyExistsQ[bindings, #["ID"]] &], "SpaceID", {}]]]];
    If[AnyTrue[evidence, FailureQ], Throw[FirstCase[Values[evidence], _Failure], "modularImport"]];
    md["BindingEvidence"] = evidence;
    <|"ModularData" -> md, "Slots" -> rebuilt|>
], "modularImport"];

True
