(*
    :Title: Mathematical model archives
    :Context: VVMFTool`Private`
    :Summary: SaveModelData/ImportModelData: versioned JSON archives of a model (fields, parameters, terms, frozen
        context) and named coefficient matrices, with the model's group embedded as a mathematical group snapshot. The
        archive's bytes are registered in the independent export ledger; import admits the group as ImportGroupData does
        (registered bytes, or actual native correspondence), rebinds the frozen context and revalidates everything.
    :Responsibilities: modelGroupSource, encodeModelArchive, validateModelArchive, rebindModelContext, decodeModelArchive,
        archive codecs of precisions, tolerances and parameter records; SaveModelData, ImportModelData.
    :Dependencies: PythonIR.wl (encodeScalarTree, decodeScalarTree, validateScalarTree); GroupSnapshots.wl (groupSnapshot,
        decodeGroupSnapshot); GroupStorage.wl (publishRegisteredImport, validateImportedGroup); ExportLedger.wl;
        ArtifactIO.wl; Representation.wl (contextSnapshot, bindRepContext, contextDigest); Models.wl; Couplings.wl;
        MassMatrices.wl.
    :See Also: VVMFArch/step6Plan.md (Mathematical JSON round trips); VVMFArch/implementation/step6Status.md (D-S6-1, D-S6-3).
*)

$ModelArchiveFormat = "VVMFToolModel";
$ModelArchiveSchemaVersion = 1;

(* -------------------------------------------------------------------------
   Small codecs
   ------------------------------------------------------------------------- *)

(*
    Summary: Encode and decode a precision or tolerance value of a model record.
    Parameters: x — Infinity, MachinePrecision, Automatic, None, Missing[...] or a number; record — its encoding.
    Options/defaults: None.
    Returns: "Infinity" | "MachinePrecision" | "Automatic" | "None" | <|"missing" -> reason|> | scalar tree; decoding gives the value
        back, or Failure.
    Effects: Pure.
    Failures: UnsupportedScalar (a value outside these forms); InvalidModelArchive (decoding).
    Example: decodeArchiveNumber[encodeArchiveNumber[10^-20]] is 10^-20.
    See also: encodeModelArchive.
*)
encodeArchiveNumber[x_] := Which[
    x === Infinity, "Infinity", x === MachinePrecision, "MachinePrecision", x === Automatic, "Automatic", x === None, "None",
    MissingQ[x], <|"missing" -> If[Length[x] > 0 && StringQ[First[x]], First[x], ""]|>,
    NumericQ[x], encodeScalarTree[x, <|"Parameters" -> {}, "Fields" -> <||>|>],
    True, makeFailure["UnsupportedScalar", "A precision or tolerance is not encodable.", <|"Value" -> x|>]];
decodeArchiveNumber[record_] := Which[
    record === "Infinity", Infinity, record === "MachinePrecision", MachinePrecision, record === "Automatic", Automatic, record === "None", None,
    AssociationQ[record] && Keys[record] === {"missing"} && StringQ[record["missing"]], If[record["missing"] === "", Missing[], Missing[record["missing"]]],
    AssociationQ[record], decodeScalarTree[record],
    True, makeFailure["InvalidModelArchive", "A precision or tolerance record is malformed."]];

(*
    Summary: The inert source spelling of a parameter record.
    Parameters: atom — the record's SourceAtom (HoldForm of a declared symbol, an imported spelling string, or Missing).
    Options/defaults: None.
    Returns: String or Null.
    Effects: Pure (the held symbol is never evaluated).
    Failures: None.
    Example: parameterSourceText[HoldForm[lambda]] is "lambda".
    Remarks: D-S6-3: archives store the spelling as text; an imported parameter that is new to the kernel keeps the text
        as its SourceAtom (no symbol is created or evaluated).
    See also: encodeModelArchive; decodeParameterRecords.
*)
parameterSourceText[HoldForm[s_]] := ToString[Unevaluated[s], InputForm];
parameterSourceText[s_String] := s;
parameterSourceText[_] := Null;

(* -------------------------------------------------------------------------
   Saving
   ------------------------------------------------------------------------- *)

(*
    Summary: Whether a context's representation variant and a group's stored variant hold the same data.
    Parameters: mine — the context's variant record; theirs — the group's variant record (or <||>).
    Options/defaults: None.
    Returns: Boolean: equal Identity, Arithmetic and Tier, and SameQ matrices for exact variants or matrices within
        10^-(digits - 2) for numerical ones (decoded numerical matrices are rounded at their stored precision).
    Effects: Pure.
    Failures: None.
    Example: a forged 20-digit copy of an exact variant carrying the exact variant's identity does not match.
    See also: modelGroupSource.
*)
variantDataMatchQ[mine_Association, theirs_Association] := Module[{a = repMatrices[Lookup[mine, "Rep", Rep[{}]]], b = repMatrices[Lookup[theirs, "Rep", Rep[{}]]], digits},
    If[Lookup[mine, "Identity", None] =!= Lookup[theirs, "Identity", Missing[]] || Lookup[mine, "Arithmetic", None] =!= Lookup[theirs, "Arithmetic", None] ||
            Lookup[mine, "Tier", None] =!= Lookup[theirs, "Tier", None] || Dimensions[a] =!= Dimensions[b], Return[False]];
    If[!inexactDataQ[{a, b}], Return[a === b]];
    digits = Min[Replace[dataPrecision /@ {a, b}, {MachinePrecision -> 16, Infinity -> 50}, {1}]];
    Max[Append[Abs[N[Flatten[a - b]]], 0]] <= 10^-(digits - 2)
];
variantDataMatchQ[___] := False;

(*
    Summary: The live group whose accepted state can stand for a model's frozen context in an archive.
    Parameters: snapshot — the model's context snapshot.
    Options/defaults: None.
    Returns: <|"Group" -> Group, "Snapshot" -> group snapshot (no retained-state reference, no CG data), "Decoded" -> decoded
        snapshot|>, or Failure.
    Effects: Reads the group registry; no GAP work.
    Failures: GroupUnavailable (no live group of the model's state in this kernel); ContextNotRebindable (the live group's
        state cannot rebind the context: different generators or characters, an earlier state generation, a different
        modular assignment, or a frozen representation variant that the group no longer has).
    Example: after ChangeGroupRepBasis the group still stores the old variants, so a model frozen before the change is
        saved with the group's current state.
    Remarks: D-S6-1. The snapshot is the group's current accepted state (a valid native envelope exists only for it); the
        frozen context is a subset of that state (old variants stay stored), so the archive records which variants and
        pointers the context had.
    See also: SaveModelData; rebindModelContext.
*)
modelGroupSource[snapshot_Association] := Module[{candidates, assignment, result = None, reasons = {}},
    candidates = Select[Keys[$GroupRegistry], $GroupRegistry[#]["StateID"] === snapshot["GroupIdentity"] &];
    If[candidates === {}, Return[makeFailure["GroupUnavailable", "The model's group is not loaded in this kernel; import or build it before saving the model.",
        <|"StateID" -> snapshot["GroupIdentity"]|>]]];
    assignment = Lookup[Replace[snapshot["ModularAssignment"], Except[_Association] -> <||>], "Identity", None];
    Do[Module[{group = Group[id], native, decoded, data, missing},
            native = groupSnapshot[group]; If[FailureQ[native], AppendTo[reasons, native]; Continue[]];
            native = Join[KeyDrop[native, {"cgData", "cgCacheEpoch"}], <|"gapCache" -> Null|>];
            decoded = Block[{$GroupAcceptanceLevel = groupAcceptanceLevel[group]}, decodeGroupSnapshot[native]]; If[FailureQ[decoded], AppendTo[reasons, decoded]; Continue[]];
            data = decoded["Data"];
            (* A variant must match in data, not only in identity (review N5): arithmetic, tier and matrices (exactly, or
               within the stored precision for numerical variants). *)
            missing = Select[Flatten[KeyValueMap[Function[{irrep, entry}, Map[{irrep, #, entry["Variants"][#]} &, Keys[entry["Variants"]]]],
                snapshot["Representations"]], 1], !variantDataMatchQ[#[[3]], Lookup[Lookup[Lookup[data["Representations"], #[[1]], <||>], "Variants", <||>], #[[2]], <||>]] &];
            If[data["GeneratorIdentity"] =!= snapshot["GeneratorIdentity"] || data["CharacterData"] =!= snapshot["CharacterData"] ||
                    !IntegerQ[snapshot["StateGeneration"]] || snapshot["StateGeneration"] > data["StateGeneration"] ||
                    Lookup[Replace[data["ModularAssignment"], Except[_Association] -> <||>], "Identity", None] =!= assignment || missing =!= {},
                AppendTo[reasons, <|"Group" -> id, "MissingVariants" -> missing[[All, 1 ;; 2]]|>]; Continue[]];
            result = <|"Group" -> group, "Snapshot" -> native, "Decoded" -> decoded|>; Break[]],
        {id, candidates}];
    If[AssociationQ[result], result,
        makeFailure["ContextNotRebindable", "No loaded state of the model's group can rebind its frozen context (a changed modular assignment or missing representation variants); save the model before such a change or recreate it.",
            <|"Reasons" -> reasons|>]]
];

(*
    Summary: The archive record of a model and named coefficient matrices.
        A modular model (Stage 9) adds "modular" (encodeModularModelArchive) and its terms name their slots.
    Parameters: model — validated model data; masses — <|name -> validated MassMatrix data|>; source — modelGroupSource result.
    Options/defaults: None.
    Returns: JSON association (resultJSONQ), or Failure.
    Effects: Pure.
    Failures: Tree encoding failures (UnsupportedExpression, UndeclaredAtom, NonfiniteConstant, UnsupportedScalar) with the
        term, mass or entry named.
    Example: encodeModelArchive[model, <||>, source]["model"]["fields"][[1]]["id"] is the first field's ID.
    Remarks: Expressions are typed trees of their own structure (D-S6-2), so decoding is SameQ for exact data; field,
        parameter, term and model IDs are kept; nothing executable, no live handle and no generated code is stored.
    See also: SaveModelData; decodeModelArchive.
*)
encodeModelArchive[model_Association, masses_Association, source_Association] := Catch[Module[
    {snapshot = First[model["Context"]], registry, tree, number, terms, fields, parameters, massRecords, context, modular},
    registry = <|"Parameters" -> Lookup[model["Parameters"], "ID", {}], "Fields" -> AssociationThread[Lookup[model["Fields"], "ID", {}], Lookup[model["Fields"], "Dimension", {}]]|>;
    (* Stage 9: a modular model's trees use its form slots; its modular data are archived beside the model. *)
    If[KeyExistsQ[model, "ModularData"], registry["Slots"] = Map[#["Dimension"] &, model["ModularData"]["Slots"]];
        modular = encodeModularModelArchive[model]; If[FailureQ[modular], Throw[modular, "modelArchive"]]];
    tree[x_, where_] := With[{t = encodeScalarTree[x, registry]}, If[FailureQ[t], Throw[Failure[First[t], Join[Last[t], <|"Where" -> where|>]], "modelArchive"], t]];
    number[x_, where_] := With[{t = encodeArchiveNumber[x]}, If[FailureQ[t], Throw[Failure[First[t], Join[Last[t], <|"Where" -> where|>]], "modelArchive"], t]];
    context = <|"stateGeneration" -> encodeInteger[snapshot["StateGeneration"]],
        "assignmentIdentity" -> Replace[Lookup[Replace[snapshot["ModularAssignment"], Except[_Association] -> <||>], "Identity", Null], _Missing -> Null],
        "representations" -> Map[<|"variants" -> Keys[#["Variants"]], "activeVariant" -> Replace[#["ActiveVariant"], _Missing -> Null],
            "acceptedPartial" -> Replace[#["AcceptedPartial"], _Missing -> Null]|> &, snapshot["Representations"]]|>;
    fields = Map[<|"id" -> #["ID"], "name" -> #["Name"], "irrepID" -> #["IrrepID"], "basisID" -> #["BasisID"]|> &, model["Fields"]];
    parameters = Map[<|"id" -> #["ID"], "label" -> #["Label"], "domain" -> #["Domain"], "source" -> parameterSourceText[#["SourceAtom"]]|> &, model["Parameters"]];
    terms = Map[Function[t, Join[<|"termID" -> t["TermID"], "arithmetic" -> t["Arithmetic"], "precision" -> number[t["Precision"], t["TermID"]],
            "tolerance" -> number[t["Tolerance"], t["TermID"]], "fieldIDs" -> Replace[t["FieldIDs"], Except[_List] -> Null],
            "targetIrrepID" -> Replace[t["TargetIrrepID"], Except[_String] -> Null], "contextBound" -> StringQ[t["ContextDigest"]],
            "parameterIDs" -> Lookup[t["Parameters"], "ID", {}],
            "terms" -> Map[<|"expression" -> tree[#["Expression"], t["TermID"]], "channel" -> Replace[#["Channel"], Except[_String] -> Null],
                "coefficient" -> tree[#["Coefficient"], t["TermID"]]|> &, t["Terms"]],
            "value" -> tree[t["Value"], t["TermID"]]|>,
            If[KeyExistsQ[t, "Policy"], <|"policy" -> t["Policy"]|>, <||>],
            If[KeyExistsQ[t, "Relations"], <|"relations" -> Map[Map[tree[#, t["TermID"]] &, #] &, t["Relations"]]|>, <||>],
            (* A modular term names its slots; their records are the model's (rebuilt on import). *)
            If[KeyExistsQ[t, "FormSlots"], <|"formSlots" -> Keys[t["FormSlots"]], "namespace" -> t["Namespace"]|>, <||>],
            (* a term status weaker than Exact (absent reads "Exact") *)
            If[MemberQ[{"Numerical", "Unverified"}, Lookup[t, "VerificationStatus", "Exact"]], <|"verificationStatus" -> t["VerificationStatus"]|>, <||>]]], model["Terms"]];
    massRecords = Association[KeyValueMap[Function[{name, d}, name -> <|"kind" -> d["Kind"], "convention" -> d["Convention"],
        "arithmetic" -> Lookup[d, "Arithmetic", "Exact"], "precision" -> number[Lookup[d, "Precision", Infinity], name],
        "tolerance" -> number[Lookup[d, "Tolerance", Missing["Exact"]], name],
        "rows" -> Map[tree[#, name] &, d["Rows"]], "columns" -> Map[tree[#, name] &, d["Columns"]],
        "matrix" -> Map[tree[#, name] &, d["Matrix"], {2}], "selected" -> tree[d["Selected"], name], "remainder" -> tree[d["Remainder"], name],
        "input" -> tree[d["InputExpression"], name], "rowFields" -> Replace[d["RowFields"], Except[_List] -> Null],
        "columnFields" -> Replace[d["ColumnFields"], Except[_List] -> Null], "fieldNames" -> Lookup[d, "FieldNames", <||>],
        "contextBound" -> MatchQ[Lookup[d, "Context", Missing[]], _RepresentationContext]|>], masses]];
    <|"format" -> $ModelArchiveFormat, "schemaVersion" -> $ModelArchiveSchemaVersion, "group" -> source["Snapshot"], "context" -> context,
        "model" -> <|"id" -> model["ID"], "name" -> model["Name"], "targetIrrepID" -> model["TargetIrrepID"], "targetBasisID" -> model["TargetBasisID"],
            "arithmetic" -> model["Arithmetic"], "precision" -> number[model["Precision"], "model"], "tolerance" -> number[model["Tolerance"], "model"],
            "fields" -> fields, "parameters" -> parameters, "terms" -> terms|>,
        "massMatrices" -> massRecords,
        Sequence @@ If[KeyExistsQ[model, "ModularData"], {"modular" -> modular}, {}]|>
], "modelArchive"];

Options[SaveModelData] = {MassMatrices -> <||>, Overwrite -> False};

(*
    Summary: Save a model and named coefficient matrices as a mathematical JSON archive.
        A modular model (Stage 9) is saved with its formal slots, per-slot factors and frozen bindings; a matrix whose entries
        have inconsistent modular weights is refused (InconsistentWeight).
    Status: Alpha.
    Parameters: m — Model; file — destination (relative paths resolve against the current directory).
    Options/defaults: MassMatrices <||> — an ordered association of names to MassMatrix values, each certified against m;
        Overwrite False (refuse an existing file) or True (replace it atomically).
    Returns: The absolute path, or Failure (a ledger failure carries SavedFile).
    Effects: Validates the model and every matrix, writes the archive atomically and registers its bytes in the independent
        export ledger with the embedded group's identities; no GAP work.
    Failures: InvalidModel; model validation failures; InvalidOption (MassMatrices); NotCovariant / ValidateMassMatrix failures;
        GroupUnavailable; ContextNotRebindable; tree encoding failures; SaveFailed; ExportFailed (existing file without
        Overwrite); ledger failures.
    Example: SaveModelData[m, FileNameJoin[{$TemporaryDirectory, "a4_model.json"}], MassMatrices -> <|"ELMatrix" -> mass|>, Overwrite -> True].
    Remarks: The archive contains the group's mathematical snapshot (no retained GAP state, no CG data), the frozen
        context's representation pointers and generation, the model's fields, parameters (with their spelling as text) and
        terms, and the matrices, all as inert typed data; no live handle, executable source, workspace or Python code.
    See also: ImportModelData; SaveGroupData; ToPython.
*)
SaveModelData[m_Model, file_String, options : OptionsPattern[]] := Module[{effective, model, validation, masses, certificates, source, archive, path,
        written, registered},
    effective = resolveOperationOptions[SaveModelData, "SaveModelData", {options}];
    If[FailureQ[effective], Return[effective]];
    If[StringLength[file] === 0, Return[makeFailure["SaveFailed", "The archive filename must not be empty."]]];
    model = validateModelSchema[m]; If[FailureQ[model], Return[model]];
    validation = ValidateModel[m]; If[FailureQ[validation], Return[validation]];
    If[!TrueQ[validation["Covariant"]], Return[makeFailure["NotCovariant", "The model does not validate; it cannot be archived."]]];
    If[!AllTrue[Values[effective[MassMatrices]], MatchQ[#, _MassMatrix] &],
        Return[makeFailure["InvalidOption", "MassMatrices must map names to MassMatrix values.", <|"Options" -> {MassMatrices}|>]]];
    certificates = Map[ValidateMassMatrix[m, #] &, effective[MassMatrices]];
    If[AnyTrue[certificates, FailureQ], Return[FirstCase[Values[certificates], _Failure]]];
    If[!AllTrue[certificates, TrueQ[#["Covariant"]] &], Return[makeFailure["NotCovariant", "A mass matrix does not transform covariantly in this model.",
        <|"MassMatrices" -> Keys[Select[certificates, !TrueQ[#["Covariant"]] &]]|>]]];
    If[AnyTrue[certificates, #["Status"] === "InconsistentWeight" &], Return[makeFailure["InconsistentWeight", "A mass matrix does not have the modular weights the model requires.",
        <|"MassMatrices" -> Keys[Select[certificates, #["Status"] === "InconsistentWeight" &]]|>]]];
    masses = Map[validateMassMatrixData, effective[MassMatrices]];
    source = modelGroupSource[First[model["Context"]]]; If[FailureQ[source], Return[source]];
    archive = encodeModelArchive[model, masses, source]; If[FailureQ[archive], Return[archive]];
    (* the statuses ValidateModel established, read back as bounds on import (methodOptionsPlan.md 2C.1): the model's and
       each term's at its save-time check (an unchecked term is checked by this save, bounded by its sources) *)
    If[validation["VerificationStatus"] =!= "Exact", archive["model", "verificationStatus"] = validation["VerificationStatus"]];
    With[{numerical = model["Arithmetic"] === "Numerical" || MemberQ[Lookup[model["Terms"], "Arithmetic", {}], "Numerical"],
            byTerm = AssociationThread[Lookup[model["Terms"], "TermID", {}], model["Terms"]]},
        archive["model", "terms"] = Map[Function[t, With[{status = checkedTermStatus[byTerm[t["termID"]], numerical || byTerm[t["termID"]]["Arithmetic"] === "Numerical"]},
            If[status === "Exact", KeyDrop[t, "verificationStatus"], Join[t, <|"verificationStatus" -> status|>]]]], archive["model", "terms"]]];
    path = ExpandFileName[file];
    If[FileType[path] === File && !TrueQ[effective[Overwrite]],
        Return[makeFailure["ExportFailed", "The target exists; use Overwrite -> True to replace it.", <|"File" -> path|>]]];
    written = writeResult[path, archive]; If[FailureQ[written], Return[written]];
    registered = registerExport[path, source["Decoded"]["Identity"], written, groupIdentityBindings[source["Decoded"]["Data"]],
        subgroupClassWitnesses[source["Decoded"]["Data"]],
        cgWeakestStatus[Join[{groupRecordsStatus[source["Decoded"]["Data"]], validation["VerificationStatus"]}, Lookup[Values[certificates], "VerificationStatus", {}]]],
        groupVerificationStatus[source["Decoded"]["Data"]]];
    If[FailureQ[registered], Failure[registered[[1]], Join[registered[[2]], <|"SavedFile" -> path|>]], path]
];
SaveModelData[___] := makeFailure["InvalidInput", "SaveModelData expects a Model, a file name and options."];

(* -------------------------------------------------------------------------
   Importing
   ------------------------------------------------------------------------- *)

(*
    Summary: Check the archive grammar before anything is decoded or admitted.
        The optional "modular" part (Stage 9) is checked by validateModularModelArchive and its slots bound the trees.
    Parameters: archive — JSON data read from the file.
    Options/defaults: None.
    Returns: The archive, or InvalidModelArchive Failure with a reason.
    Effects: Pure.
    Failures: Wrong format or schema version; missing or extra keys; malformed IDs, labels, pointers or records; trees outside
        the grammar or the archive's own registry (validateScalarTree).
    Example: an archive whose matrix entry has node "eval" fails here.
    Remarks: No string is evaluated; every expression is a tree checked against the archive's fields and parameters.
    See also: ImportModelData; decodeModelArchive.
*)
validateModelArchive[archive_] := Module[{invalid, model, registry, treeQ, numberQ},
    invalid[reason_] := makeFailure["InvalidModelArchive", "The model archive is malformed.", <|"Reason" -> reason|>];
    (* "modular" is optional: Stage 6 archives have no modular part (Stage 9). *)
    If[!AssociationQ[archive] || !(resultFieldsQ[archive, {"format", "schemaVersion", "group", "context", "model", "massMatrices"}] ||
            resultFieldsQ[archive, {"format", "schemaVersion", "group", "context", "model", "massMatrices", "modular"}]) || archive["format"] =!= $ModelArchiveFormat ||
            archive["schemaVersion"] =!= $ModelArchiveSchemaVersion, Return[invalid["Format"]]];
    If[!resultFieldsQ[archive["context"], {"stateGeneration", "assignmentIdentity", "representations"}] ||
            !IntegerQ[decodeInteger[archive["context"]["stateGeneration"]]] || !(archive["context"]["assignmentIdentity"] === Null || StringQ[archive["context"]["assignmentIdentity"]]) ||
            !AssociationQ[archive["context"]["representations"]] ||
            !AllTrue[Values[archive["context"]["representations"]], resultFieldsQ[#, {"variants", "activeVariant", "acceptedPartial"}] && ListQ[#["variants"]] &&
                AllTrue[#["variants"], StringQ] && (#["activeVariant"] === Null || MemberQ[#["variants"], #["activeVariant"]]) &&
                (#["acceptedPartial"] === Null || MemberQ[#["variants"], #["acceptedPartial"]]) &],
        Return[invalid["Context"]]];
    model = archive["model"];
    (* "verificationStatus" (model and terms) is optional: a recorded status (methodOptionsPlan.md 2C.1) *)
    If[!resultFieldsQ[KeyDrop[model, "verificationStatus"], {"id", "name", "targetIrrepID", "targetBasisID", "arithmetic", "precision", "tolerance", "fields", "parameters", "terms"}] ||
            (KeyExistsQ[model, "verificationStatus"] && !verificationStatusQ[model["verificationStatus"]]) ||
            !AllTrue[Lookup[model, {"id", "name", "targetIrrepID", "targetBasisID"}], StringQ] || !MemberQ[{"Exact", "Numerical"}, model["arithmetic"]] ||
            !ListQ[model["fields"]] || !AllTrue[model["fields"], resultFieldsQ[#, {"id", "name", "irrepID", "basisID"}] && AllTrue[Values[#], StringQ] &] ||
            !DuplicateFreeQ[Lookup[model["fields"], "id", {}]] ||
            !ListQ[model["parameters"]] || !AllTrue[model["parameters"], resultFieldsQ[#, {"id", "label", "domain", "source"}] && StringQ[#["id"]] && StringQ[#["label"]] &&
                StringQ[#["domain"]] && (#["source"] === Null || StringQ[#["source"]]) &] || !DuplicateFreeQ[Lookup[model["parameters"], "id", {}]] ||
            !ListQ[model["terms"]],
        Return[invalid["Model"]]];
    (* Field dimensions are known only from the context; component indices are bounded here and checked against the rebuilt fields later. *)
    registry = <|"Parameters" -> Lookup[model["parameters"], "id", {}], "Fields" -> AssociationThread[Lookup[model["fields"], "id", {}], ConstantArray[10^9, Length[model["fields"]]]]|>;
    If[KeyExistsQ[archive, "modular"],
        If[!TrueQ[validateModularModelArchive[archive["modular"]]], Return[invalid["Modular"]]];
        registry["Slots"] = AssociationThread[archivedSlotIDs[archive["modular"]], 10^9]];
    treeQ[t_] := TrueQ[validateScalarTree[t, registry]];
    numberQ[r_] := !FailureQ[decodeArchiveNumber[r]];
    If[!AllTrue[model["terms"], Function[t, AssociationQ[t] && SubsetQ[Keys[t], {"termID", "arithmetic", "precision", "tolerance", "fieldIDs", "targetIrrepID",
            "contextBound", "parameterIDs", "terms", "value"}] && SubsetQ[{"termID", "arithmetic", "precision", "tolerance", "fieldIDs", "targetIrrepID", "contextBound",
            "parameterIDs", "terms", "value", "policy", "relations", "formSlots", "namespace", "verificationStatus"}, Keys[t]] &&
            (!KeyExistsQ[t, "verificationStatus"] || verificationStatusQ[t["verificationStatus"]]) &&
            (!KeyExistsQ[t, "formSlots"] || (ListQ[t["formSlots"]] && SubsetQ[Keys[Lookup[registry, "Slots", <||>]], t["formSlots"]] && StringQ[Lookup[t, "namespace", None]])) && StringQ[t["termID"]] && MemberQ[{"Exact", "Numerical"}, t["arithmetic"]] &&
            numberQ[t["precision"]] && numberQ[t["tolerance"]] && BooleanQ[t["contextBound"]] && ListQ[t["parameterIDs"]] && SubsetQ[registry["Parameters"], t["parameterIDs"]] &&
            ListQ[t["terms"]] && AllTrue[t["terms"], resultFieldsQ[#, {"expression", "channel", "coefficient"}] && treeQ[#["expression"]] && treeQ[#["coefficient"]] &&
                (#["channel"] === Null || StringQ[#["channel"]]) &] && treeQ[t["value"]] &&
            (!KeyExistsQ[t, "relations"] || (AssociationQ[t["relations"]] && AllTrue[Values[t["relations"]], AssociationQ[#] && AllTrue[Values[#], treeQ] &]))]] ||
            !DuplicateFreeQ[Lookup[model["terms"], "termID", {}]],
        Return[invalid["Terms"]]];
    If[!AssociationQ[archive["massMatrices"]] || !AllTrue[Values[archive["massMatrices"]], Function[d, resultFieldsQ[d, {"kind", "convention", "arithmetic", "precision",
            "tolerance", "rows", "columns", "matrix", "selected", "remainder", "input", "rowFields", "columnFields", "fieldNames", "contextBound"}] &&
            MemberQ[{"Bilinear", "Quadratic"}, d["kind"]] && MemberQ[{"Bilinear", "Polynomial", "Half"}, d["convention"]] && MemberQ[{"Exact", "Numerical"}, d["arithmetic"]] &&
            numberQ[d["precision"]] && numberQ[d["tolerance"]] && ListQ[d["rows"]] && ListQ[d["columns"]] && AllTrue[Join[d["rows"], d["columns"]], treeQ] &&
            MatrixQ[d["matrix"], AssociationQ] && AllTrue[Flatten[d["matrix"]], treeQ] && AllTrue[{d["selected"], d["remainder"], d["input"]}, treeQ] &&
            AssociationQ[d["fieldNames"]] && BooleanQ[d["contextBound"]]]],
        Return[invalid["Mass matrices"]]];
    archive
];
validateModelArchive[___] := makeFailure["InvalidModelArchive", "Expected archive data."];

(*
    Summary: Rebuild and bind the frozen context of an archive to an admitted group.
    Parameters: archive — validated archive; group — live Group admitted from the archive's snapshot.
    Options/defaults: None.
    Returns: RepresentationContext registered in this kernel, or Failure.
    Effects: Registers one context binding (bindRepContext).
    Failures: ContextNotRebindable (a saved variant or pointer the group does not have, a later generation than the
        group's, another assignment); UnverifiedContext (bindRepContext's own checks).
    Example: a model saved before ChangeGroupRepBasis rebinds to the imported group, which still stores the old variants.
    Remarks: The context is the imported group's context snapshot with the saved state generation, the saved irreps
        restricted to their saved variants, and the saved active/partial pointers; bindRepContext then requires every
        variant to be one the group accepted.
    See also: modelGroupSource; bindRepContext.
*)
rebindModelContext[archive_Association, group_Group] := Module[{data = groupData[group], saved = archive["context"], snapshot, representations, generation},
    If[FailureQ[data], Return[data]];
    generation = decodeInteger[saved["stateGeneration"]];
    If[Replace[Lookup[Replace[data["ModularAssignment"], Except[_Association] -> <||>], "Identity", Null], _Missing -> Null] =!= saved["assignmentIdentity"] ||
            generation > data["StateGeneration"] ||
            !AllTrue[Normal[saved["representations"]], KeyExistsQ[data["Representations"], First[#]] &&
                SubsetQ[Keys[data["Representations"][First[#]]["Variants"]], Last[#]["variants"]] &],
        Return[makeFailure["ContextNotRebindable", "The archive's frozen context does not fit the admitted group state."]]];
    representations = Association[KeyValueMap[Function[{irrep, pointers}, irrep -> Join[data["Representations"][irrep],
        <|"Variants" -> KeyTake[data["Representations"][irrep]["Variants"], pointers["variants"]],
            "ActiveVariant" -> Replace[pointers["activeVariant"], Null -> Missing["NotComputed"]],
            "AcceptedPartial" -> Replace[pointers["acceptedPartial"], Null -> Missing["NotComputed"]]|>]], saved["representations"]]];
    snapshot = Join[contextSnapshot[data], contextPresentation[data], <|"StateGeneration" -> generation, "Representations" -> representations|>];
    bindRepContext[snapshot, group]
];

(*
    Summary: The parameter records of an archive, reusing the kernel's records of the same IDs.
    Parameters: records — archive parameter records.
    Options/defaults: None.
    Returns: <|"Records" -> list of parameter records (archive order), "New" -> records to register|>, or ParameterConflict.
    Effects: Pure (registration happens after the whole import validates).
    Failures: ParameterConflict when a known ID has another label, domain or source spelling.
    Example: importing a model into the kernel that saved it reuses the original records (with their HoldForm source).
    Remarks: D-S6-3: an ID unknown to the kernel becomes a record whose SourceAtom is the spelling string; no symbol is
        created.
    See also: decodeModelArchive.
*)
decodeParameterRecords[records_List] := Module[{decoded, new = {}, conflict = None},
    decoded = Map[Function[r, With[{known = Lookup[$CouplingRecords, r["id"], None]},
        Which[
            AssociationQ[known] && known["Label"] === r["label"] && known["Domain"] === r["domain"] && parameterSourceText[known["SourceAtom"]] === r["source"], known,
            AssociationQ[known], (conflict = r["id"]; known),
            True, With[{record = <|"Atom" -> Coupling[r["id"]], "ID" -> r["id"], "Label" -> r["label"], "Domain" -> r["domain"],
                "SourceAtom" -> If[r["source"] === Null, Missing[], r["source"]]|>}, AppendTo[new, record]; record]]]], records];
    If[conflict =!= None, makeFailure["ParameterConflict", "An archive parameter ID is already used with another label, domain or source in this kernel.",
        <|"ParameterID" -> conflict|>], <|"Records" -> decoded, "New" -> new|>]
];

(* The mass matrices of an archive, decoded (their checks are the caller's). *)
decodeArchivedMasses[archive_Association, byID_Association, context_RepresentationContext] :=
    Association[KeyValueMap[Function[{name, d}, name -> MassMatrix[<|"SchemaVersion" -> 1, "Kind" -> d["kind"], "Convention" -> d["convention"],
        "InputExpression" -> decodeScalarTree[d["input"]], "Selected" -> decodeScalarTree[d["selected"]], "Remainder" -> decodeScalarTree[d["remainder"]],
        "Matrix" -> Map[decodeScalarTree, d["matrix"], {2}], "Rows" -> Map[decodeScalarTree, d["rows"]], "Columns" -> Map[decodeScalarTree, d["columns"]],
        "Dimensions" -> Dimensions[d["matrix"], 2],
        "Parameters" -> Lookup[byID, DeleteDuplicates[Cases[Map[decodeScalarTree, d["matrix"], {2}], Coupling[id_String] :> id, Infinity]]],
        "RowFields" -> Replace[d["rowFields"], Null -> Missing["NotKnown"]], "ColumnFields" -> Replace[d["columnFields"], Null -> Missing["NotKnown"]],
        "FieldNames" -> d["fieldNames"], "Context" -> If[TrueQ[d["contextBound"]], context, Missing["NotKnown"]], "Arithmetic" -> d["arithmetic"],
        "Precision" -> decodeArchiveNumber[d["precision"]], "Tolerance" -> decodeArchiveNumber[d["tolerance"]]|>]], archive["massMatrices"]]];

(*
    Summary: A model archive imported with Verification -> None: nothing recomputed (methodOptionsPlan.md 2C.4, 2C.5).
    Parameters: data — the decoded model data; terms — decoded terms; m — the archive's model record; archive; byID —
        parameter records; context; trusted — a registered export of this kernel.
    Options/defaults: None.
    Returns: <|"Model", "MassMatrices"|> (decodeModelArchive adds "NewParameters"), or Failure.
    Effects: Pure.
    Failures: InvalidModel (validateModelSchema).
    Example: an untrusted archive imported with Verification -> None gives a model whose status is "Unverified".
    Remarks: A trusted export keeps its recorded statuses (absent: "Exact") and the covariance it was saved with; any other
        file's terms read Symmetry "Unchecked" and status "Unverified", its model and matrices "Unverified".
    See also: decodeModelArchive; ImportModelData.
*)
unverifiedModelImport[data_Association, terms_List, m_Association, archive_Association, byID_Association, context_RepresentationContext, trusted_] := Module[
    {model, masses, decodedTerms, status},
    decodedTerms = Map[Function[t, Join[t, If[trusted,
        <|"Symmetry" -> If[t["Arithmetic"] === "Numerical" || m["arithmetic"] === "Numerical", "Covariant (numerical)", "Covariant"]|>,
        (* unchecked: a later ValidateModel takes its level bounded by the recorded status (as for a term added unchecked) *)
        <|"Symmetry" -> "Unchecked", "VerificationStatus" -> "Unverified", "InputStatus" -> Lookup[t, "VerificationStatus", "Exact"]|>]]], terms];
    status = If[trusted, cgWeakestStatus[Join[{Lookup[m, "verificationStatus", "Exact"]}, Lookup[#, "VerificationStatus", "Exact"] & /@ decodedTerms]], "Unverified"];
    model = Model[Join[data, <|"Terms" -> decodedTerms, "Validation" -> <|"Status" -> If[trusted && status =!= "Unverified",
            If[status === "Numerical" || m["arithmetic"] === "Numerical", "Covariant (numerical)", "Covariant"], "Unverified"],
        "Arithmetic" -> m["arithmetic"], "VerificationStatus" -> status|>|>]];
    If[FailureQ[validateModelSchema[model]], Return[validateModelSchema[model]]];
    masses = Map[MassMatrix[Join[First[#], <|"VerificationStatus" -> cgWeakestStatus[{Lookup[First[#], "VerificationStatus", "Exact"], status}]|>]] &,
        decodeArchivedMasses[archive, byID, context]];
    <|"Model" -> model, "MassMatrices" -> masses|>
];

(*
    Summary: The model and coefficient matrices of a validated archive in a bound context.
        trusted (default False): a registered export keeps archived binding proof claims (Stage 9, decodeModularModelArchive).
    Parameters: archive — validated archive; context — rebindModelContext result; level — the import's Verification
        (default Automatic; "Exact"/"Numerical" the level of the recomputed covariance; None: not recomputed, the records
        keep their recorded statuses for a trusted export and are "Unverified" otherwise).
    Options/defaults: None.
    Returns: <|"Model" -> Model, "MassMatrices" -> <|name -> MassMatrix|>, "NewParameters" -> records|>, or Failure.
    Effects: Pure (parameter records are registered by the caller after success).
    Failures: InvalidModelArchive (a field whose basis is not the context's active variant, a target basis mismatch, values
        that disagree with their terms); ParameterConflict; validateModelSchema/ValidateModel/ValidateMassMatrix failures;
        NotCovariant.
    Example: decodeModelArchive[archive, ctx]["Model"] has the saved model ID and field IDs.
    Remarks: Model covariance and every matrix's source, closure, reconstruction and covariance are recomputed; the saved
        symmetry and validation statuses are not trusted.
    See also: ImportModelData; encodeModelArchive.
*)
decodeModelArchive[archive_Association, context_RepresentationContext] := decodeModelArchive[archive, context, False];
decodeModelArchive[archive_Association, context_RepresentationContext, trusted_, level_ : Automatic] := Catch[Module[
    {snapshot = First[context], digest, m = archive["model"], parameters, byID, fields, fieldByID, target, terms, data, model, validation, masses, certificates, fail, modular = None},
    fail[reason_] := Throw[makeFailure["InvalidModelArchive", "The model archive does not match its context.", <|"Reason" -> reason|>], "modelImport"];
    digest = contextDigest[snapshot];
    parameters = decodeParameterRecords[m["parameters"]]; If[FailureQ[parameters], Throw[parameters, "modelImport"]];
    byID = AssociationThread[Lookup[parameters["Records"], "ID", {}], parameters["Records"]];
    fields = Map[Function[f, With[{variant = cgVariant[snapshot, f["irrepID"]]},
        If[!AssociationQ[variant] || variant["Identity"] =!= f["basisID"], fail["Field " <> f["id"] <> " basis"]];
        <|"SchemaVersion" -> 1, "ID" -> f["id"], "Name" -> f["name"], "IrrepID" -> f["irrepID"], "Dimension" -> variant["Dimension"], "Rep" -> variant["Rep"],
            "BasisID" -> variant["Identity"], "Arithmetic" -> variant["Arithmetic"], "Context" -> context, "ContextDigest" -> digest,
            "Components" -> Table[FieldComponent[f["id"], i], {i, variant["Dimension"]}]|>]], m["fields"]];
    fieldByID = AssociationThread[Lookup[fields, "ID", {}], fields];
    target = cgVariant[snapshot, m["targetIrrepID"]];
    If[!AssociationQ[target] || target["Identity"] =!= m["targetBasisID"], fail["Target basis"]];
    (* Stage 9: rebuild the modular data (slots, frozen bindings, recomputed evidence) before the terms that use them. *)
    If[KeyExistsQ[archive, "modular"],
        modular = decodeModularModelArchive[archive["modular"], <|"SchemaVersion" -> 1, "ID" -> m["id"], "Name" -> m["name"], "Context" -> context,
            "ContextDigest" -> digest, "Fields" -> fields, "TargetIrrepID" -> m["targetIrrepID"], "Terms" -> {}, "Parameters" -> {}|>, context, trusted];
        If[FailureQ[modular], Throw[modular, "modelImport"]]];
    terms = Map[Function[t, Join[<|"SchemaVersion" -> 1, "TermID" -> t["termID"],
            "Terms" -> Map[<|"Expression" -> decodeScalarTree[#["expression"]], "Channel" -> Replace[#["channel"], Null -> Missing["NoChannel"]],
                "Coefficient" -> decodeScalarTree[#["coefficient"]]|> &, t["terms"]],
            "Value" -> decodeScalarTree[t["value"]], "Parameters" -> Lookup[byID, t["parameterIDs"]],
            "FieldIDs" -> Replace[t["fieldIDs"], Null -> Missing["Unknown"]], "TargetIrrepID" -> Replace[t["targetIrrepID"], Null -> Missing["Unknown"]],
            "ContextDigest" -> If[TrueQ[t["contextBound"]], digest, Missing["Unknown"]], "Symmetry" -> "Unverified", "Arithmetic" -> t["arithmetic"],
            "Precision" -> decodeArchiveNumber[t["precision"]], "Tolerance" -> decodeArchiveNumber[t["tolerance"]]|>,
            If[KeyExistsQ[t, "policy"], <|"Policy" -> t["policy"]|>, <||>],
            If[KeyExistsQ[t, "relations"], <|"Relations" -> Map[Map[decodeScalarTree, #] &, t["relations"]]|>, <||>],
            If[KeyExistsQ[t, "formSlots"] && AssociationQ[modular], <|"FormSlots" -> KeyTake[modular["Slots"], t["formSlots"]], "Namespace" -> t["namespace"]|>, <||>],
            (* a recorded term status bounds the recomputed one (ValidateModel takes the weakest) *)
            If[KeyExistsQ[t, "verificationStatus"], <|"VerificationStatus" -> t["verificationStatus"]|>, <||>]]], m["terms"]];
    If[!AllTrue[terms, AssociationQ[validateCoupledExpression[CoupledExpression[#]]] &], fail["A term's value does not match its parts"]];
    data = <|"SchemaVersion" -> 1, "ID" -> m["id"], "Name" -> m["name"], "Context" -> context, "ContextDigest" -> digest, "Fields" -> fields,
        "TargetIrrepID" -> m["targetIrrepID"], "TargetRep" -> target["Rep"], "TargetBasisID" -> target["Identity"], "Terms" -> terms,
        "Parameters" -> parameters["Records"], "Arithmetic" -> m["arithmetic"], "Precision" -> decodeArchiveNumber[m["precision"]],
        "Tolerance" -> decodeArchiveNumber[m["tolerance"]], "Validation" -> <|"Status" -> "Unverified", "Arithmetic" -> m["arithmetic"]|>|>;
    If[AssociationQ[modular], data["ModularData"] = modular["ModularData"]];
    (* Verification -> None (methodOptionsPlan.md 2C.4): nothing is recomputed; a trusted export keeps its recorded
       statuses (2C.5), any other file's records are "Unverified" *)
    If[level === None, Throw[With[{unverified = unverifiedModelImport[data, terms, m, archive, byID, context, TrueQ[trusted]]},
        If[FailureQ[unverified], unverified, Join[unverified, <|"NewParameters" -> parameters["New"]|>]]], "modelImport"]];
    (* Covariance is recomputed, never read: each term and the whole model. *)
    validation = ValidateModel[Model[Join[data, <|"Terms" -> Map[Join[#, <|"Symmetry" -> "Covariant"|>] &, terms]|>]], Verification -> level];
    If[FailureQ[validation], Throw[validation, "modelImport"]];
    If[!TrueQ[validation["Covariant"]], Throw[makeFailure["NotCovariant", "The archived model does not validate.", <|"ModelID" -> m["id"]|>], "modelImport"]];
    data["Terms"] = Map[Join[#, <|"Symmetry" -> If[#["Arithmetic"] === "Numerical" || m["arithmetic"] === "Numerical" || level === "Numerical", "Covariant (numerical)", "Covariant"]|>,
        If[level === "Numerical", <|"VerificationStatus" -> cgWeakestStatus[{Lookup[#, "VerificationStatus", "Exact"], "Numerical"}]|>, <||>]] &, terms];
    data["Validation"] = <|"Status" -> validation["Status"],
        "Arithmetic" -> If[validation["Status"] === "Covariant (numerical)", "Numerical", m["arithmetic"]],
        (* recomputed from the inputs and terms; a recorded model status can only lower it *)
        "VerificationStatus" -> cgWeakestStatus[{validation["VerificationStatus"], Lookup[m, "verificationStatus", "Exact"]}]|>;
    model = Model[data];
    If[FailureQ[validateModelSchema[model]], Throw[validateModelSchema[model], "modelImport"]];
    masses = decodeArchivedMasses[archive, byID, context];
    certificates = Map[ValidateMassMatrix[model, #, Verification -> level] &, masses];
    If[AnyTrue[certificates, FailureQ], Throw[FirstCase[Values[certificates], _Failure], "modelImport"]];
    If[!AllTrue[certificates, TrueQ[#["Covariant"]] && #["Status"] =!= "InconsistentWeight" &], Throw[makeFailure["NotCovariant", "An archived mass matrix does not validate.",
        <|"MassMatrices" -> Keys[Select[certificates, !TrueQ[#["Covariant"]] || #["Status"] === "InconsistentWeight" &]]|>], "modelImport"]];
    <|"Model" -> model, "MassMatrices" -> masses, "NewParameters" -> parameters["New"]|>
], "modelImport"];

Options[ImportModelData] = Join[Options[RestoreGAPState], {ValidationGroup -> Automatic, Verification -> Automatic}];

(*
    Summary: Import a model archive: its group, frozen context, model and coefficient matrices, all revalidated.
        A modular model (Stage 9) is rebuilt with recomputed slots and independence evidence; archived proof claims of
        bindings are kept only for a trusted export. Group admission is importArchiveGroup (shared with ImportModularFormData).
    Status: Alpha.
    Parameters: file — archive filename (relative paths resolve against the current directory).
    Options/defaults: ValidationGroup Automatic or an accepted Group (as ImportGroupData); common GAP options;
        Verification -> Automatic (the model and matrices recomputed in their arithmetic), "Exact", "Numerical" (the level
        of those checks) or None (not recomputed: a trusted export keeps its recorded statuses, another file's model is
        "Unverified"). It governs the archive's own records only: a registered archive's group is read at its recorded group
        status, any other is re-proved in GAP (methodOptionsStatus.md, final review F-E).
    Returns: <|"Model" -> Model, "MassMatrices" -> <|name -> MassMatrix|>, "Group" -> the admitted Group|>, or Failure.
    Effects: Reads the file twice around its digest; admits the embedded group like ImportGroupData (registered archive
        bytes: no GAP; otherwise native correspondence with typed construction or ValidationGroup); binds the rebuilt context;
        registers parameter records that are new to the kernel after everything validated.
    Failures: FileUnavailable; ImportChanged; InvalidJSON; InvalidModelArchive; group snapshot and import failures
        (InvalidSnapshot, StateConflict, ImportNeedsValidationGroup, ...); ContextNotRebindable; UnverifiedContext;
        ParameterConflict; model and matrix validation failures.
    Example: ImportModelData[SaveModelData[m, path]]["Model"] has the same model, field, term and parameter IDs as m.
    Remarks: The admitted group is a fresh handle (accepted group data follow the ImportGroupData rules even when the model
        then fails validation); no imported string is evaluated, no GAP source or workspace is executed, and a forged
        certificate or status is never trusted. The result also carries the admitted Group (an addition to the plan's
        two keys) so later work can continue in it.
    See also: SaveModelData; ImportGroupData.
*)
ImportModelData[file_String, options : OptionsPattern[]] := Module[{effective, path},
    effective = resolveOperationOptions[ImportModelData, "ImportModelData", {options}];
    If[FailureQ[effective], Return[effective]];
    If[StringLength[file] === 0, Return[makeFailure["FileUnavailable", "The archive filename must not be empty."]]];
    path = ExpandFileName[file];
    withProgress[effective, "ImportModelData", Function[Null, Module[{before, archive, after, valid, admitted, group, context, result},
        before = fileDigest[path]; If[FailureQ[before], Return[before]];
        archive = readResult[path]; If[FailureQ[archive], Return[archive]];
        after = fileDigest[path];
        If[before =!= after, Return[makeFailure["ImportChanged", "The archive changed while being read."]]];
        valid = validateModelArchive[archive]; If[FailureQ[valid], Return[valid]];
        (* Group admission is shared with ImportModularFormData (importArchiveGroup, Stage 9). *)
        admitted = importArchiveGroup[archive["group"], before, effective, "ImportModelData", path]; If[FailureQ[admitted], Return[admitted]];
        group = admitted["Group"];
        context = rebindModelContext[archive, group]; If[FailureQ[context], Return[context]];
        result = decodeModelArchive[archive, context, admitted["Trusted"], effective[Verification]]; If[FailureQ[result], Return[result]];
        Scan[AssociateTo[$CouplingRecords, #["ID"] -> #] &, result["NewParameters"]];
        <|"Model" -> result["Model"], "MassMatrices" -> result["MassMatrices"], "Group" -> group|>
    ]]]
];
ImportModelData[___] := makeFailure["InvalidInput", "ImportModelData expects an archive filename and options."];

True
