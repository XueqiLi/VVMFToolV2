(*
    :Title: Prepared modular outputs
    :Context: VVMFTool`Private`
    :Summary: Immutable export snapshots of Stage 7 forms (ModularFormOutput) and the modular part of a Stage 6 ModelOutput
        prepared from a Stage 8 model: the used form slots, their frozen bindings, and the formal and binding status axes.
    :Responsibilities: extendModularModelOutput, validateModularOutputRecord, formOutputNode, prepareFormOutputData,
        validateFormOutput; PrepareModularFormOutput, ModularFormOutput.
    :Dependencies: ModelOutput.wl (prepareOutputData calls extendModularModelOutput; validateModelOutput calls
        validateModularOutputRecord); ModularFormObjects.wl (snapshotForm, validateFormRecord); ModularModels.wl
        (bindingStatus).
    :See Also: VVMFArch/step9Plan.md (Prepared modular models and Python contracts); step9Status.md (D-S9-10).
*)

(* -------------------------------------------------------------------------
   Modular model outputs
   ------------------------------------------------------------------------- *)

(*
    Summary: The modular record of a ModelOutput prepared from a modular model.
    Parameters: model — validated modular model data; dependencies — collectOutputDependencies of the built outputs;
        validation — the ValidateModel report of the model; normalized — the normalized output records (unused, kept
        for symmetry with the caller).
    Options/defaults: None.
    Returns: <|"SchemaVersion", "AssignmentID", "AssignmentWords", "FieldWeights", "ActualFieldWeights", "SuperpotentialWeight",
        "SlotNamespaceID", "Formal" -> <|"Status", "Covariant", "ModularWeight"|>, "ModelBindingStatus", "RuntimeSlots" (used
        slot IDs, model order), "SlotDimensions", "Slots" (frozen slot records), "Bindings" (frozen binding records of used
        bound slots), "BindingStatus" (over the used slots: NoForms, Unbound, Partial, Full), "Unbound"|>.
    Effects: Pure.
    Failures: None.
    Example: the L.R.Y output of an unbound T' model has one runtime slot and BindingStatus "Unbound".
    Remarks: Only slots reachable from the selected outputs (after explicit substitutions) are recorded; an unrelated
        unbound slot does not affect this output. Bindings are copied as frozen values (D-S8-8), so later form updates
        or rebinding never reach a prepared output; fixed normalization constants stay inside the bound records and never
        become physical parameters (D-S9-10).
    See also: prepareOutputData; validateModularOutputRecord.
*)
extendModularModelOutput[model_Association, dependencies_Association, validation_Association, normalized_] := Module[
    {md = model["ModularData"], used, bindings},
    used = Select[Keys[md["Slots"]], KeyExistsQ[Lookup[dependencies, "Slots", <||>], #] &];
    bindings = KeyTake[md["Bindings"], used];
    <|"SchemaVersion" -> 1, "AssignmentID" -> md["AssignmentID"], "AssignmentWords" -> md["AssignmentWords"], "FieldWeights" -> md["FieldWeights"],
        "ActualFieldWeights" -> md["ActualFieldWeights"], "SuperpotentialWeight" -> md["SuperpotentialWeight"], "SlotNamespaceID" -> md["SlotNamespaceID"],
        "Formal" -> <|"Status" -> validation["Status"], "Covariant" -> validation["Covariant"], "ModularWeight" -> Lookup[validation, "ModularWeight", Missing["NotReported"]]|>,
        "ModelBindingStatus" -> bindingStatus[model], "RuntimeSlots" -> used, "SlotDimensions" -> Map[#["Dimension"] &, KeyTake[md["Slots"], used]],
        "Slots" -> KeyTake[md["Slots"], used], "Bindings" -> bindings, "BindingStatus" -> usedBindingStatus[used, bindings],
        "Unbound" -> Select[used, !KeyExistsQ[bindings, #] &]|>
];
usedBindingStatus[used_List, bindings_Association] := Which[used === {}, "NoForms", Length[bindings] === 0, "Unbound",
    Length[bindings] === Length[used], "Full", True, "Partial"];

(*
    Summary: Check the modular record of a ModelOutput against its trees.
    Parameters: record — the "Modular" value; dependencies — collectOutputDependencies of the output's trees.
    Options/defaults: None.
    Returns: True, or False for any inconsistency.
    Effects: Pure.
    Failures: None (False).
    Example: a record whose RuntimeSlots omit a slot used by a tree is rejected.
    Remarks: Runtime slots are exactly the slots the trees use; every slot record has its ID, dimension and components;
        every binding belongs to a runtime slot, names its slot, and holds a valid form record of the slot's weight,
        dimension and basis; the binding status and unbound list follow from the bindings.
    See also: validateModelOutput; extendModularModelOutput.
*)
validateModularOutputRecord[record_Association, dependencies_Association] := Module[{used = Lookup[record, "RuntimeSlots", None], slots, bindings},
    slots = Lookup[record, "Slots", None]; bindings = Lookup[record, "Bindings", None];
    ListQ[used] && AssociationQ[slots] && AssociationQ[bindings] && Lookup[record, "SchemaVersion", None] === 1 &&
        DuplicateFreeQ[used] && Sort[used] === Sort[Keys[Lookup[dependencies, "Slots", <||>]]] && Keys[slots] === used &&
        Lookup[record, "SlotDimensions", None] === Map[Lookup[#, "Dimension", None] &, slots] &&
        AllTrue[used, Function[id, With[{s = slots[id]}, AssociationQ[s] && s["ID"] === id && IntegerQ[s["Dimension"]] && modularWeightQ[s["Weight"]] &&
            Lookup[s, "Components", None] === Table[FormComponent[id, i], {i, s["Dimension"]}] &&
            Max[Append[dependencies["Slots"][id], 0]] <= s["Dimension"]]]] &&
        SubsetQ[used, Keys[bindings]] &&
        AllTrue[Keys[bindings], Function[id, With[{b = bindings[id], s = slots[id]}, AssociationQ[b] && b["SlotID"] === id && StringQ[b["FormID"]] &&
            IntegerQ[b["Revision"]] && AssociationQ[validateFormRecord[b["Record"]]] && b["Record"]["ID"] === b["FormID"] && b["Record"]["Revision"] === b["Revision"] &&
            b["Record"]["Weight"] === s["Weight"] && b["Record"]["Dimension"] === s["Dimension"] && b["Record"]["BasisID"] === s["BasisID"]]]] &&
        record["BindingStatus"] === usedBindingStatus[used, bindings] && record["Unbound"] === Select[used, !KeyExistsQ[bindings, #] &]
];
validateModularOutputRecord[___] := False;

(* -------------------------------------------------------------------------
   Standalone form outputs
   ------------------------------------------------------------------------- *)

(*
    Summary: The dependency node of one frozen form record.
    Parameters: record — form record.
    Options/defaults: None.
    Returns: <|"NodeID" -> "ID@revision", "FormID", "Revision", "Record", "ContentDigest", "Evidence" -> <|"Validation",
        "Coefficients", "Arithmetic", "Normalization"|>|>.
    Effects: Pure.
    Failures: None.
    Example: formOutputNode[ModularFormData[y]]["NodeID"] is y["ID"] <> "@" <> ToString[y["Revision"]].
    Remarks: The content digest identifies the record's content (the live context object excluded; its ContextDigest is
        included); it is content identity, not a proof of modularity. Missing coefficients or expansions stay Missing.
    See also: prepareFormOutputData.
*)
formOutputNode[record_Association] := <|"NodeID" -> record["ID"] <> "@" <> ToString[record["Revision"]], "FormID" -> record["ID"], "Revision" -> record["Revision"],
    "Record" -> record, "ContentDigest" -> formContentDigest[record],
    "Evidence" -> <|"Validation" -> Lookup[record["Validation"], "Status", Missing["NotReported"]],
        "Coefficients" -> If[AssociationQ[record["Coefficients"]], record["Coefficients"]["ProofStatus"], Missing["Unresolved"]],
        "Arithmetic" -> record["Arithmetic"],
        "Normalization" -> If[AssociationQ[record["Coefficients"]], KeyTake[record["Coefficients"], {"Kind", "AnchorFrameID", "Component", "Exponent", "Value"}], Missing["Unresolved"]]|>|>;
formContentDigest[record_Association] := Hash[KeyDrop[record, "Context"], "SHA256", "HexString"];

(*
    Summary: The data of a ModularFormOutput.
    Parameters: forms — ordered association name -> ModularForm.
    Options/defaults: None.
    Returns: <|"SchemaVersion", "ID", "Outputs" -> {<|"Name", "Shape" -> {d}, "NodeID", "FormID", "Revision", "Weight", "IrrepID",
        "BasisID", "AssignmentID", "GroupIdentity"|>...}, "Nodes" -> <|NodeID -> formOutputNode|>, "Digest"|>, or Failure.
    Effects: One registry read per distinct form; no computation (no expansion, coefficient solve or validation).
    Failures: InvalidInput (an empty association, a name that is not a nonempty string, a value that is not a
        ModularForm, with its name); UnknownModularForm.
    Example: prepareFormOutputData[<|"Y" -> y, "Z" -> y|>]["Nodes"] has one node.
    Remarks: Every output is a vector (shape {d}, also for d = 1). A form under several names shares one node; distinct
        form objects stay distinct nodes even with equal content. Different realizations keep their own group, assignment
        and basis identities per output.
    See also: PrepareModularFormOutput; validateFormOutput.
*)
prepareFormOutputData[forms_Association] := Module[{records, nodes, outputs},
    If[forms === <||>, Return[makeFailure["InvalidInput", "PrepareModularFormOutput needs a nonempty association of names to modular forms."]]];
    If[!AllTrue[Keys[forms], StringQ[#] && StringLength[#] > 0 &], Return[makeFailure["InvalidInput", "Output names must be nonempty strings."]]];
    With[{bad = Select[Keys[forms], Head[forms[#]] =!= ModularForm &]},
        If[bad =!= {}, Return[makeFailure["InvalidInput", "Every output must be a ModularForm.", <|"Names" -> bad|>]]]];
    records = AssociationMap[snapshotForm, DeleteDuplicates[Values[forms]]];
    If[AnyTrue[records, FailureQ], Return[FirstCase[Values[records], _Failure]]];
    nodes = Association[Map[#["NodeID"] -> # &, formOutputNode /@ Values[records]]];
    outputs = KeyValueMap[Function[{name, y}, With[{r = records[y]}, <|"Name" -> name, "Shape" -> {r["Dimension"]}, "NodeID" -> r["ID"] <> "@" <> ToString[r["Revision"]],
        "FormID" -> r["ID"], "Revision" -> r["Revision"], "Weight" -> r["Weight"], "IrrepID" -> r["IrrepID"], "BasisID" -> r["BasisID"],
        "AssignmentID" -> r["AssignmentID"], "GroupIdentity" -> r["GroupIdentity"]|>]], forms];
    <|"SchemaVersion" -> 1, "ID" -> "formoutput-" <> CreateUUID[], "Outputs" -> outputs, "Nodes" -> nodes, "Digest" -> formOutputDigest[outputs, nodes]|>
];
formOutputDigest[outputs_List, nodes_Association] := Hash[{outputs, Map[#["ContentDigest"] &, nodes]}, "SHA256", "HexString"];

(*
    Summary: Validate a ModularFormOutput before use.
    Parameters: out — any expression.
    Options/defaults: None.
    Returns: The data, or InvalidModularFormOutput Failure.
    Effects: Pure.
    Failures: Missing fields, duplicate or empty names, outputs naming absent nodes, nodes whose record fails
        validateFormRecord or disagrees with its ID, revision, content digest or the output's shape and identities, unused
        nodes, or a digest that does not match the content.
    Example: an output whose stored record was edited by hand fails here.
    See also: PrepareModularFormOutput.
*)
validateFormOutput[ModularFormOutput[data_Association]] := Module[{invalid, outputs, nodes},
    invalid[reason_] := makeFailure["InvalidModularFormOutput", "The modular form output is malformed.", <|"Reason" -> reason|>];
    If[!SubsetQ[Keys[data], {"SchemaVersion", "ID", "Outputs", "Nodes", "Digest"}] || data["SchemaVersion"] =!= 1 || !ListQ[data["Outputs"]] ||
            data["Outputs"] === {} || !AssociationQ[data["Nodes"]], Return[invalid["Fields"]]];
    outputs = data["Outputs"]; nodes = data["Nodes"];
    If[!AllTrue[outputs, AssociationQ[#] && StringQ[Lookup[#, "Name", None]] && StringLength[#["Name"]] > 0 &] || !DuplicateFreeQ[Lookup[outputs, "Name"]],
        Return[invalid["Names"]]];
    If[!AllTrue[Keys[nodes], Function[id, With[{n = nodes[id]}, AssociationQ[n] && AssociationQ[Lookup[n, "Record", None]] &&
            AssociationQ[validateFormRecord[n["Record"]]] && n["NodeID"] === id && n["FormID"] === n["Record"]["ID"] && n["Revision"] === n["Record"]["Revision"] &&
            id === n["FormID"] <> "@" <> ToString[n["Revision"]] && n["ContentDigest"] === formContentDigest[n["Record"]]]]], Return[invalid["Nodes"]]];
    If[!AllTrue[outputs, Function[o, KeyExistsQ[nodes, o["NodeID"]] && With[{r = nodes[o["NodeID"]]["Record"]},
            o["Shape"] === {r["Dimension"]} && o["FormID"] === r["ID"] && o["Revision"] === r["Revision"] && o["Weight"] === r["Weight"] &&
                o["BasisID"] === r["BasisID"] && o["AssignmentID"] === r["AssignmentID"] && o["IrrepID"] === r["IrrepID"]]]], Return[invalid["Outputs"]]];
    If[Sort[Keys[nodes]] =!= Sort[DeleteDuplicates[Lookup[outputs, "NodeID"]]], Return[invalid["Unused nodes"]]];
    If[data["Digest"] =!= formOutputDigest[outputs, nodes], Return[invalid["Digest"]]];
    data
];
validateFormOutput[___] := makeFailure["InvalidModularFormOutput", "Expected a ModularFormOutput."];

(*
    Summary: Immutable export snapshot of named modular forms.
    Status: Alpha.
    Fields: SchemaVersion, ID, Outputs (name, shape {d}, node, form ID and revision, weight, irrep, basis, assignment and
        group identities), Nodes (frozen records with content digests and evidence), Digest.
    Returns: ModularFormOutput[data]; out["Outputs"] reads a field.
    Identity/mutation: A value; later coefficient, expansion or group changes never alter it.
    Example: PrepareModularFormOutput[<|"YTriplet" -> y|>]["Outputs"][[1, "Shape"]] is {3}.
    See also: PrepareModularFormOutput; ToPython.
*)
ModularFormOutput[data_Association][property_String] := Lookup[data, property, Missing["NotAvailable", property]];
Format[ModularFormOutput[data_Association], StandardForm] := Interpretation[Row[{"ModularFormOutput[", Short[Lookup[Lookup[data, "Outputs", {}], "Name", {}], 1], "]"}],
    ModularFormOutput[data]];

Options[PrepareModularFormOutput] = {};

(*
    Summary: Prepare named modular forms for export.
    Status: Alpha.
    Parameters: forms — nonempty ordered association from output names to ModularForm values (the same form may appear
        under several names).
    Options/defaults: None.
    Returns: ModularFormOutput, or Failure.
    Effects: One consistent snapshot per form; no q-expansion, coefficient solve, validation or GAP.
    Failures: InvalidInput; UnknownModularForm; UnknownOption.
    Example: formOut = PrepareModularFormOutput[<|"YTriplet" -> y|>]; ToPython[formOut].
    Remarks: Unresolved coefficients or a missing expansion are kept as Missing; whether a snapshot can be exported for
        evaluation is decided by ToPython (Embedded requirements), not here.
    See also: ModularFormOutput; ToPython; SaveModularFormData.
*)
PrepareModularFormOutput[forms_Association, options : OptionsPattern[]] := Module[{effective, data},
    effective = resolveOperationOptions[PrepareModularFormOutput, "PrepareModularFormOutput", {options}]; If[FailureQ[effective], Return[effective]];
    data = prepareFormOutputData[forms];
    If[FailureQ[data], data, ModularFormOutput[data]]
];
PrepareModularFormOutput[___] := makeFailure["InvalidInput", "PrepareModularFormOutput expects an association of names to modular forms."];

(* -------------------------------------------------------------------------
   Export policy (ToPython of modular outputs)
   ------------------------------------------------------------------------- *)

$ModularExportOptions = {FormEvaluation, ExportEvaluationMethod, SeriesOrder, AccuracyGoal, PrecisionGoal, MaxSeriesOrder, TimeLimit, RequireProof};

(*
    Summary: Whether a definition (or a frozen source inside it) is a finite jet.
    Parameters: definition — definition data.
    Options/defaults: None.
    Returns: Boolean.
    Effects: Pure.
    Failures: None.
    Example: the derivative of a finite-jet form is finite.
    See also: resolveFormExportPolicy.
*)
finiteDefinitionQ[definition_Association] := definition["Kind"] === "Jet" ||
    (definition["Kind"] === "Derived" && finiteDefinitionQ[definition["Recipe"]["Source"]]);

(*
    Summary: The decimal precision of the numerical data of a form record (Infinity when exact).
    Parameters: record — form record.
    Options/defaults: None.
    Returns: Infinity, MachinePrecision or a positive number.
    Effects: Pure.
    Failures: None.
    Example: a form with fitted 40-digit coefficients has source precision 40.
    See also: resolveFormExportPolicy.
*)
recordSourcePrecision[record_Association] := With[{numbers = Cases[{Lookup[Replace[record["Coefficients"], _Missing -> <||>], "Rules", {}],
        Lookup[record["Definition"], "Components", {}], repMatrices[record["Rep"]], Lookup[record["Definition"], "Transform", {}]}, _Real | _Complex?InexactNumberQ, Infinity]},
    If[numbers === {}, Infinity, Min[Precision /@ numbers]]];

(*
    Summary: The export policy of the modular part of a ToPython call: mode, method, goals, limits, and one portable recipe
        per form record (Embedded), or the slot descriptors only (External).
    Parameters: kind — "Forms" (ModularFormOutput) or "Model" (modular ModelOutput); records — <|key -> form record|> (form
        nodes, or the bound records of the runtime slots); unbound — runtime slot IDs without a binding (models); effective —
        validated ToPython options; supplied — the option symbols the caller gave explicitly; digits — backend digits (16
        for NumPy, the working precision for mpmath); formal — the model's formal status or None.
    Options/defaults: FormEvaluation "Embedded"; ExportEvaluationMethod Automatic ("QSeries"); SeriesOrder Automatic;
        AccuracyGoal, PrecisionGoal Automatic (half the backend digits, bounded by the source precision); MaxSeriesOrder
        2000; TimeLimit 600 (seconds per evaluation, including every slot and refinement); RequireProof False.
    Returns: <|"Mode", "Method", "SeriesOrder", "AccuracyGoal", "PrecisionGoal", "MaxSeriesOrder", "TimeLimit", "RequireProof",
        "Recipes" -> <|key -> recipe|> (Embedded), "Evidence" -> <|key -> <|"Validation", "Coefficients", "Arithmetic",
        "SourcePrecision", "Status"|>|>|>, or Failure.
    Effects: Pure: no expansion, coefficient solve or validation is run.
    Failures: InapplicableOption (External for a ModularFormOutput; an evaluation option with External; goals with
        FiniteSeries); IncompatibleOptions (RequireProof with External); MethodUnavailable (Analytic, as in Stage 7);
        InvalidOption (FiniteSeries without an integer SeriesOrder, an order above MaxSeriesOrder, a goal above the backend
        digits); MissingBindings (a runtime slot without a binding, Embedded; External is the route); UnresolvedCoefficients;
        FiniteJet (a finite jet in QSeries mode: use FiniteSeries with SeriesOrder); NotComputed / InsufficientOrder
        (FiniteSeries without a stored expansion or jet reaching the order); StaleExpansion; UnsupportedRecipe; ProofRequired.
    Example: resolveFormExportPolicy["Forms", <|id -> record|>, {}, opts, {}, 16, None]["Method"] is "QSeries".
    Remarks: FiniteSeries uses the stored expansion (or the jet) as a finite approximation with no tail bound; export never
        computes or stores an expansion. RequireProof reads only stored evidence: a standalone record's Validation status
        (never upgraded by display or export) and its coefficient proof, a binding's Stage 7 proof status and the model's
        exact formal covariance.
    See also: ToPython; encodeFormRecipe; storedExpansionData.
*)
resolveFormExportPolicy[kind_String, records_Association, unbound_List, effective_Association, supplied_List, digits_, formal_] := Module[
    {mode = effective[FormEvaluation], method, order, goals, recipes, evidence, fail, recipeFor},
    fail[tag_, message_, extra_ : <||>] := Throw[makeFailure[tag, message, extra], "exportPolicy"];
    Catch[
        If[kind === "Forms" && mode === "External", fail["InapplicableOption", "A ModularFormOutput is exported with FormEvaluation -> \"Embedded\"; External applies to modular model outputs.",
            <|"Options" -> {FormEvaluation}|>]];
        If[mode === "External",
            If[TrueQ[effective[RequireProof]], fail["IncompatibleOptions", "RequireProof cannot be satisfied by externally supplied form values.", <|"Options" -> {RequireProof, FormEvaluation}|>]];
            With[{bad = Intersection[supplied, {ExportEvaluationMethod, SeriesOrder, AccuracyGoal, PrecisionGoal, MaxSeriesOrder}]},
                If[bad =!= {}, fail["InapplicableOption", "Series options do not apply to FormEvaluation -> \"External\".", <|"Options" -> bad|>]]];
            Throw[<|"Mode" -> "External", "Method" -> Missing["External"], "SeriesOrder" -> Missing["External"], "AccuracyGoal" -> Missing["External"],
                "PrecisionGoal" -> Missing["External"], "MaxSeriesOrder" -> Missing["External"], "TimeLimit" -> effective[TimeLimit], "RequireProof" -> False,
                "Recipes" -> <||>, "Evidence" -> Map[exportEvidence, records]|>, "exportPolicy"]];
        method = Replace[effective[ExportEvaluationMethod], Automatic -> "QSeries"];
        If[method === "Analytic", fail["MethodUnavailable", "No analytic branch-continuation evaluator is implemented (as in Stage 7); use \"QSeries\" or \"FiniteSeries\".",
            <|"Options" -> {ExportEvaluationMethod}|>]];
        order = effective[SeriesOrder];
        If[method === "FiniteSeries",
            If[!IntegerQ[order], fail["InvalidOption", "FiniteSeries needs an explicit integer SeriesOrder.", <|"Options" -> {SeriesOrder}|>]];
            With[{bad = Intersection[supplied, {AccuracyGoal, PrecisionGoal}]},
                If[bad =!= {}, fail["InapplicableOption", "A finite series has no accuracy guarantee; AccuracyGoal and PrecisionGoal do not apply.", <|"Options" -> bad|>]]]];
        If[IntegerQ[order] && order > effective[MaxSeriesOrder], fail["InvalidOption", "SeriesOrder exceeds MaxSeriesOrder.", <|"Options" -> {SeriesOrder, MaxSeriesOrder}|>]];
        If[kind === "Model" && unbound =!= {}, fail["MissingBindings", "Every form slot of the selected outputs needs a binding for FormEvaluation -> \"Embedded\"; bind forms or use \"External\".",
            <|"SlotIDs" -> unbound|>]];
        goals = Map[Function[g, With[{value = effective[g]}, Which[
            method === "FiniteSeries", Missing["FiniteSeriesApproximation"],
            value === Automatic, Max[1, Floor[Min[digits, Min[Append[recordSourcePrecision /@ Values[records], Infinity]] /. MachinePrecision -> 15.9]/2]],
            (* At the digit count two approximations can agree bit for bit (no information about the error). *)
            value > digits - 2, fail["InvalidOption", "An accuracy or precision goal must stay at least two digits below the backend digits.", <|"Options" -> {g}|>],
            True, value]]], <|"AccuracyGoal" -> AccuracyGoal, "PrecisionGoal" -> PrecisionGoal|>];
        recipeFor[key_, record_] := Module[{coefficients = record["Coefficients"], rules, recipe, stored},
            rules = Which[
                !AssociationQ[coefficients], fail["UnresolvedCoefficients", "The form's relative coefficients are not resolved; use ModularFormGetCoeff before exporting.", <|"Key" -> key|>],
                coefficients["Kind"] === "NoNormalizationNeeded" || coefficients["Rules"] === {}, {},
                ListQ[coefficients["Rules"]], Map[FormParameter[First[#]] -> Last[#] &, coefficients["Rules"]],
                True, fail["UnresolvedCoefficients", "The form's relative coefficients are not resolved; use ModularFormGetCoeff before exporting.", <|"Key" -> key|>]];
            recipe = Which[
                method === "QSeries" && finiteDefinitionQ[record["Definition"]],
                    fail["FiniteJet", "A finite jet cannot be extended: export it with ExportEvaluationMethod -> \"FiniteSeries\" and SeriesOrder.", <|"Key" -> key|>],
                method === "QSeries", encodeFormRecipe[record["Definition"], rules, digits + 10],
                record["Definition"]["Kind"] === "Jet",
                    If[validateQExpansion[record["Definition"]["Jet"]]["Cutoff"] < order,
                        fail["InsufficientOrder", "The finite jet does not reach the requested SeriesOrder.", <|"Key" -> key, "Cutoff" -> validateQExpansion[record["Definition"]["Jet"]]["Cutoff"]|>]];
                    encodeFormRecipe[record["Definition"], rules, digits + 10],
                True,
                    stored = storedExpansionData[record];
                    Which[FailureQ[stored], Throw[stored, "exportPolicy"],
                        MissingQ[stored], fail["NotComputed", "FiniteSeries uses the stored q-expansion: compute it first with ModularFormQExp (before binding, for a model).", <|"Key" -> key|>],
                        stored["Binding"] === "Raw" && record["Definition"]["Parameters"] =!= {}, fail["UnresolvedCoefficients", "The stored q-expansion keeps unresolved coefficients (raw binding).", <|"Key" -> key|>],
                        stored["Cutoff"] < order, fail["InsufficientOrder", "The stored q-expansion does not reach the requested SeriesOrder.", <|"Key" -> key, "Cutoff" -> stored["Cutoff"]|>]];
                    encodeFormRecipe[<|"Kind" -> "Jet", "Jet" -> QExpansionData[stored]|>, {}, digits + 10]];
            If[FailureQ[recipe], fail[First[recipe], Lookup[Last[recipe], "MessageTemplate", "The definition has no portable recipe."] <>
                If[kind === "Model", " Use FormEvaluation -> \"External\" to supply the form values.", ""], Join[KeyDrop[Last[recipe], "MessageTemplate"], <|"Key" -> key|>]]];
            With[{valid = validateFormRecipe[recipe]}, If[FailureQ[valid], Throw[valid, "exportPolicy"]]];
            recipe];
        recipes = Association[KeyValueMap[#1 -> recipeFor[#1, #2] &, records]];
        evidence = Map[exportEvidence, records];
        If[TrueQ[effective[RequireProof]],
            With[{unproven = Keys[Select[records, !proofEvidenceQ[#] &]]},
                If[unproven =!= {} || (kind === "Model" && formal =!= "Covariant"),
                    fail["ProofRequired", "RequireProof needs stored proofs for every exported form (and exact formal covariance of the model); numerical or unverified evidence is not a proof.",
                        <|"Unproven" -> unproven, "Formal" -> formal|>]]]];
        <|"Mode" -> "Embedded", "Method" -> method, "SeriesOrder" -> order, "AccuracyGoal" -> goals["AccuracyGoal"], "PrecisionGoal" -> goals["PrecisionGoal"],
            "MaxSeriesOrder" -> effective[MaxSeriesOrder], "TimeLimit" -> effective[TimeLimit], "RequireProof" -> TrueQ[effective[RequireProof]],
            "Recipes" -> recipes, "Evidence" -> evidence|>,
        "exportPolicy"]
];

(*
    Summary: The stored evidence of a form record (or a binding's frozen record) for manifests, and whether it is a proof.
    Parameters: record — form record, possibly with a "BindingProofStatus" from its model binding.
    Options/defaults: None.
    Returns: exportEvidence: <|"Validation", "Coefficients", "Arithmetic", "SourcePrecision", "Status"|> (strings, Missing kept as
        Missing); proofEvidenceQ: Boolean.
    Effects: Pure.
    Failures: None.
    Example: a freshly constructed form gives Validation "Unverified" and proofEvidenceQ False.
    Remarks: A binding's Stage 7 proof status replaces the record's own Validation status (the binding ran the checks); a
        record's own status is the one it was created or derived with (display and export never upgrade it).
    See also: resolveFormExportPolicy.
*)
exportEvidence[record_Association] := <|"Validation" -> ToString[Lookup[record, "BindingProofStatus", Lookup[record["Validation"], "Status", "Unverified"]]],
    "Coefficients" -> If[AssociationQ[record["Coefficients"]], ToString[record["Coefficients"]["ProofStatus"]], Missing["Unresolved"]],
    "Arithmetic" -> record["Arithmetic"], "SourcePrecision" -> precisionText[recordSourcePrecision[record]],
    "Status" -> If[proofEvidenceQ[record], "Proven", "NumericalOrUnverified"]|>;
proofEvidenceQ[record_Association] := Lookup[record, "BindingProofStatus", Lookup[record["Validation"], "Status", "Unverified"]] === "Proven" &&
    AssociationQ[record["Coefficients"]] && MemberQ[{"NotApplicable", "Proven"}, record["Coefficients"]["ProofStatus"]];

True
