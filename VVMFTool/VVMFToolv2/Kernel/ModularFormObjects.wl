(*
    :Title: Modular-form definitions, records and registry
    :Context: VVMFTool`Private`
    :Summary: Held parsing of form definitions into inert trees (D-S7-7), the ModularForm registry with revisioned atomic
        updates (D-S7-2), the normalization record shape (D-S7-4), manual creation and the property accessors.
    :Responsibilities: parseFormDefinition, heldDefinitionViolations, definitionTreeViolations, validateFormDefinition,
        formContextData, makeFormRecord, validateFormRecord, snapshotForm, commitFormUpdate, initialNormalization,
        applyFormCoefficients; FormVariable, FormParameter, ModularFormDefinition, ModularForm, CreateModularForm,
        ModularFormData, ModularFormRep, ModularFormWeight, ModularFormExpression, ModularFormValue, ModularFormCoefficients.
    :Dependencies: ModularSeries.wl (QExpansionData); Representation.wl (resolveRepContext, contextDigest,
        modularGeneratorMatrix); CGData.wl (cgVariant); RepVectors.wl (vectorContext); Models.wl (numericConstantQ).
    :See Also: VVMFArch/step7Plan.md (object contract); VVMFArch/implementation/step7Status.md D-S7-1, D-S7-2, D-S7-4, D-S7-7.
*)

(* Inert atoms: the independent variable of a definition and its relative-normalization unknowns (D-S7-1). They never
   evaluate, and N leaves their arguments alone. *)
SetAttributes[{FormVariable, FormParameter}, NHoldAll];
Format[FormVariable[c_String], StandardForm] := Interpretation[Style[c, Italic], FormVariable[c]];
Format[FormParameter[id_String], StandardForm] := Interpretation[Subscript["c", Last[StringSplit[id, ":"]]], FormParameter[id]];

If[!AssociationQ[$ModularFormRecords], $ModularFormRecords = <||>];

(* Heads a definition may contain before evaluation (held check) and after it (tree check). *)
$DefinitionHeldHeads = {List, Plus, Times, Power, Sqrt, Exp, Rational, Complex, ScalarModularExpression, HypergeometricK,
    FormVariable, FormParameter, ModularScalarNode, HypergeometricKNode};
$DefinitionTreeHeads = {Plus, Times, Power, Exp, FormVariable, FormParameter, ModularScalarNode, HypergeometricKNode};

(*
    Summary: Symbols of a held definition that are neither admitted heads nor numeric constants.
    Parameters: held — Hold[expression] after the variable and parameters were replaced.
    Options/defaults: None.
    Returns: <|"Undeclared" -> user symbols (HoldForm), "Forbidden" -> System symbols that are not admitted (HoldForm)|>.
    Effects: Pure (nothing is evaluated).
    Failures: None.
    Example: Hold[{a FormVariable["q"]}] has Undeclared {HoldForm[a]}; Hold[{Print[1]}] has Forbidden {HoldForm[Print]}.
    Remarks: Admitted: the heads in $DefinitionHeldHeads, symbols with the Constant attribute and I, strings and numbers,
        and System functions with the NumericFunction attribute (pure). Nothing outside this list can run, because the
        expression is released only after the check.
    See also: parseFormDefinition.
*)
heldDefinitionViolations[held_Hold] := Module[{classified},
    classified = DeleteDuplicates[DeleteCases[Cases[held, s_Symbol :> {HoldForm[s], definitionSymbolClass[s]}, {0, Infinity}, Heads -> True],
        {HoldForm[Hold], _}]];
    <|"Undeclared" -> Cases[classified, {h_, "Undeclared"} :> h], "Forbidden" -> Cases[classified, {h_, "Forbidden"} :> h]|>
];
SetAttributes[definitionSymbolClass, HoldAll];
definitionSymbolClass[s_Symbol] := Which[
    MemberQ[$DefinitionHeldHeads, Unevaluated[s]], "Admitted",
    Context[Unevaluated[s]] === "System`" && (MemberQ[Attributes[Unevaluated[s]], Constant] || MemberQ[Attributes[Unevaluated[s]], NumericFunction] ||
        SymbolName[Unevaluated[s]] === "I"), "Admitted",
    Context[Unevaluated[s]] === "System`", "Forbidden",
    True, "Undeclared"];

(*
    Summary: Leaves and heads of an evaluated definition tree outside the definition domain.
    Parameters: e — evaluated component expression.
    Options/defaults: None.
    Returns: List of offending subexpressions ({} for a valid tree).
    Effects: Pure.
    Failures: None.
    Example: definitionTreeViolations[FormVariable["q"]^(1/24) + 2] is {}.
    Remarks: A numeric constant (numericConstantQ) is a leaf; FormVariable, FormParameter and scalar-ingredient nodes are
        leaves; Plus, Times, Power and Exp combine valid trees; NumericFunction System heads only combine constants.
    See also: parseFormDefinition; scalarDomainViolations.
*)
definitionTreeViolations[e_] := Which[
    numericConstantQ[e], {},
    MatchQ[e, FormVariable["q" | "tau"] | FormParameter[_String]], {},
    MatchQ[e, _ModularScalarNode | _HypergeometricKNode], scalarNodeViolations[e],
    MatchQ[e, MLDEComponentNode[_String, _String, _Integer?Positive]], {},
    MatchQ[e, ModularDerivativeNode[_?modularWeightQ, _]], definitionTreeViolations[e[[2]]],
    MatchQ[e, _Plus | _Times | _Power | _Exp], DeleteDuplicates[Flatten[definitionTreeViolations /@ (List @@ e)]],
    True, {e}];

(*
    Summary: Parse a held definition into an immutable definition record (D-S7-7).
    Parameters: components — held components (literal list or a symbol with an OwnValue); variable — held symbol;
        options — held option rules (Coordinate, NormalizationParameters, FamilyID).
    Options/defaults: Coordinate "q" or "tau"; NormalizationParameters {} (held symbols or indexed atoms); FamilyID
        Automatic (a new family; constructors pass theirs so joint F/G recipes share unknowns).
    Returns: Definition data <|"SchemaVersion" -> 1, "DefinitionID", "Kind" -> "Analytic", "Coordinate", "VariableLabel",
        "Components" -> inert trees, "Dimension", "Parameters" -> {<|"ID", "Label"|>...}, "FamilyID", "Jet" -> Missing|>,
        or Failure.
    Effects: Pure; nothing in the user's expression is evaluated before every symbol was checked.
    Failures: InvalidDefinition (not a vector, executable symbols, forbidden heads, a bound symbol with DownValues,
        SubValues or UpValues, bad options); UndeclaredSymbol (free symbols, named in "Symbols"); InvalidOption.
    Example: parseFormDefinition[Hold[{c q^(1/3)}], Hold[q], Hold[NormalizationParameters -> {c}]] has one parameter.
    Remarks: The variable and the declared parameters are replaced inside the held expression by FormVariable and
        FormParameter atoms, so assignments to those symbols (before or after) never change the definition. Labels are
        the declared spellings; parameter IDs are FamilyID <> ":" <> label.
    See also: ModularFormDefinition; heldDefinitionViolations; definitionTreeViolations.
*)
parseFormDefinition[components_Hold, variable_Hold, options_Hold] := Module[
    {rules, coordinate, declared, family, heldList, values, parameters, replaced, violations, tree, bad, symbol, varLabel},
    rules = Cases[options, (Rule | RuleDelayed)[name_Symbol, value_] :> {HoldForm[name], Hold[value]}, {1}];
    If[Length[rules] =!= Length[options] ||
            !SubsetQ[{HoldForm[Coordinate], HoldForm[NormalizationParameters], HoldForm[FamilyID]}, rules[[All, 1]]] ||
            !DuplicateFreeQ[rules[[All, 1]]],
        Return[makeFailure["InvalidOption", "ModularFormDefinition accepts Coordinate, NormalizationParameters and FamilyID.", <|"Options" -> rules[[All, 1]]|>]]];
    rules = Association[Rule @@@ rules];
    (* Option values are held literals: nothing is evaluated before it is checked. *)
    coordinate = Lookup[rules, HoldForm[Coordinate], Hold["q"]];
    If[!MatchQ[coordinate, Hold["q" | "tau"]], Return[makeFailure["InvalidOption", "Coordinate must be the literal \"q\" or \"tau\".", <|"Options" -> {Coordinate}|>]]];
    coordinate = First[coordinate];
    family = Lookup[rules, HoldForm[FamilyID], Hold[Automatic]];
    If[!MatchQ[family, Hold[_String | Automatic]], Return[makeFailure["InvalidOption", "FamilyID must be a literal string or Automatic.", <|"Options" -> {FamilyID}|>]]];
    family = Replace[First[family], Automatic :> "family-" <> CreateUUID[]];
    declared = Lookup[rules, HoldForm[NormalizationParameters], Hold[{}]];
    If[!MatchQ[declared, Hold[_List]], Return[makeFailure["InvalidOption", "NormalizationParameters must be a literal list of symbols.", <|"Options" -> {NormalizationParameters}|>]]];
    declared = List @@ Map[HoldForm, declared /. Hold[{x___}] :> Hold[x]];
    If[!MatchQ[variable, Hold[_Symbol]], Return[makeFailure["InvalidDefinition", "The variable must be a symbol."]]];
    varLabel = variable /. Hold[s_] :> SymbolName[Unevaluated[s]];
    If[!DuplicateFreeQ[declared] || !AllTrue[declared, MatchQ[#, HoldForm[_Symbol | _Symbol[(_Integer | _String) ...]]] &&
                FreeQ[#, _Pattern | _Blank | _BlankSequence | _BlankNullSequence | _Optional | _Condition | _PatternTest | _Alternatives |
                    _Repeated | _RepeatedNull | _Except | _Verbatim | _HoldPattern, {0, Infinity}, Heads -> True] &] ||
            MemberQ[declared, variable /. Hold[s_] :> HoldForm[s]],
        Return[makeFailure["InvalidOption", "NormalizationParameters must be a duplicate-free list of symbols or indexed atoms, distinct from the variable.",
            <|"Options" -> {NormalizationParameters}|>]]];
    (* The components: a literal list, or a symbol bound to one by an OwnValue (read held). *)
    heldList = Which[
        MatchQ[components, Hold[_List]], components,
        MatchQ[components, Hold[_Symbol]],
            symbol = components;
            If[symbol /. Hold[s_] :> (DownValues[s] =!= {} || SubValues[s] =!= {} || UpValues[s] =!= {}),
                Return[makeFailure["InvalidDefinition", "A bound definition variable must have only a stored value (no DownValues, SubValues or UpValues)."]]];
            values = symbol /. Hold[s_] :> OwnValues[s];
            If[values === {}, Return[makeFailure["InvalidDefinition", "The components must be a list or a symbol whose value is a list."]]];
            Extract[values, {1, 2}, Hold],
        True, Return[makeFailure["InvalidDefinition", "The components must be a list or a symbol whose value is a list."]]];
    If[!MatchQ[heldList, Hold[_List]], Return[makeFailure["InvalidDefinition", "The components must resolve to a list (a vector, length one for a scalar form)."]]];
    (* Parameter IDs are family-scoped; labels are the declared spellings. Indexed atoms are replaced before bare symbols. *)
    parameters = Map[Function[d, With[{label = d /. HoldForm[x_] :> ToString[Unevaluated[x], InputForm]},
        <|"ID" -> family <> ":" <> label, "Label" -> label, "Held" -> d|>]], declared];
    parameters = SortBy[parameters, If[MatchQ[#["Held"], HoldForm[_Symbol]], 1, 0] &];
    replaced = heldList /. Append[Map[(#["Held"] /. HoldForm[x_] :> (HoldPattern[x] -> FormParameter[#["ID"]])) &, parameters],
        variable /. Hold[s_] :> (HoldPattern[s] -> FormVariable[coordinate])];
    parameters = KeyDrop[#, "Held"] & /@ parameters;
    violations = heldDefinitionViolations[replaced];
    If[violations["Forbidden"] =!= {}, Return[makeFailure["InvalidDefinition", "The definition contains executable or unsupported heads.", <|"Heads" -> violations["Forbidden"]|>]]];
    If[violations["Undeclared"] =!= {}, Return[makeFailure["UndeclaredSymbol", "Declare coefficient parameters with NormalizationParameters; the definition may only use its variable, numeric constants and scalar modular ingredients.",
        <|"Symbols" -> violations["Undeclared"]|>]]];
    tree = ReleaseHold[replaced];
    If[!ListQ[tree] || tree === {}, Return[makeFailure["InvalidDefinition", "The components must evaluate to a nonempty list."]]];
    bad = DeleteDuplicates[Flatten[definitionTreeViolations /@ tree]];
    If[bad =!= {}, Return[makeFailure["InvalidDefinition", "The definition contains unsupported expressions.", <|"Expressions" -> bad|>]]];
    <|"SchemaVersion" -> 1, "DefinitionID" -> "definition-" <> CreateUUID[], "Kind" -> "Analytic", "Coordinate" -> coordinate,
        "VariableLabel" -> varLabel, "Components" -> tree, "Dimension" -> Length[tree],
        "Parameters" -> Select[parameters, !FreeQ[tree, FormParameter[#["ID"]]] &], "FamilyID" -> family, "Jet" -> Missing["NotAJet"]|>
];
parseFormDefinition[___] := makeFailure["InvalidDefinition", "Expected held components, a held variable and held options."];

SetAttributes[ModularFormDefinition, HoldAllComplete];

(*
    Summary: An immutable parsed modular-form definition.
    Status: Alpha.
    Signatures: ModularFormDefinition[components, variable, opts]; ModularFormDefinition[qexp] (an explicitly finite jet).
    Parameters: components — literal list of component expressions, or a symbol bound to one; variable — the independent
        symbol; qexp — QExpansionData or a symbol bound to it.
    Options/defaults: Coordinate -> "q" (or "tau"); NormalizationParameters -> {} (declared coefficient symbols);
        FamilyID -> Automatic.
    Returns: ModularFormDefinition[<|...|>] (inert data), or Failure.
    Effects: Nothing in the arguments is evaluated before every symbol is checked; no symbol is defined.
    Failures: InvalidDefinition; UndeclaredSymbol; InvalidOption; InvalidSeries.
    Example: ModularFormDefinition[{ScalarModularExpression["E4", q]}, q].
    Remarks: The definition is the authoritative recipe; creating a form does not claim modularity.
    See also: CreateModularForm; parseFormDefinition.
*)
ModularFormDefinition[components_, variable_, options___] /; !AssociationQ[Unevaluated[components]] := With[
    {data = parseFormDefinition[Hold[components], Hold[variable], Hold[options]]},
    If[FailureQ[data], data, ModularFormDefinition[data]]];
(* ModularFormDefinition holds its arguments: built data is injected with With, never as an unevaluated call. *)
ModularFormDefinition[qexp_QExpansionData] := With[{data = validateQExpansion[qexp]},
    If[FailureQ[data], data, With[{d = jetDefinitionData[qexp, data]}, ModularFormDefinition[d]]]];
ModularFormDefinition[symbol_Symbol] /; MatchQ[OwnValues[symbol], {_ :> _QExpansionData}] && DownValues[symbol] === {} :=
    With[{qexp = symbol}, With[{data = validateQExpansion[qexp]}, If[FailureQ[data], data, With[{d = jetDefinitionData[qexp, data]}, ModularFormDefinition[d]]]]];

(*
    Summary: Definition data of an explicitly finite jet.
    Parameters: qexp — QExpansionData; data — its validated data.
    Options/defaults: None.
    Returns: Definition data with Kind "Jet", the jet and no parameters.
    Effects: Pure.
    Failures: None.
    Example: jetDefinitionData[e4jet, data]["Kind"] is "Jet".
    Remarks: A jet defines only its known coefficients; higher ones are never invented.
    See also: ModularFormDefinition.
*)
jetDefinitionData[qexp_QExpansionData, data_Association] := <|"SchemaVersion" -> 1, "DefinitionID" -> "definition-" <> CreateUUID[],
    "Kind" -> "Jet", "Coordinate" -> "q", "VariableLabel" -> "q", "Components" -> Missing["FiniteJet"], "Dimension" -> data["Dimension"],
    "Parameters" -> {}, "FamilyID" -> "family-" <> CreateUUID[], "Jet" -> qexp|>;

(*
    Summary: Validate definition data before use.
    Parameters: d — any expression.
    Options/defaults: None.
    Returns: The data association, or InvalidDefinition Failure.
    Effects: Pure.
    Failures: InvalidDefinition.
    Example: validateFormDefinition[ModularFormDefinition[<||>]] fails.
    See also: parseFormDefinition.
*)
validateFormDefinition[ModularFormDefinition[data_Association]] := If[
    SubsetQ[Keys[data], {"SchemaVersion", "DefinitionID", "Kind", "Coordinate", "VariableLabel", "Components", "Dimension", "Parameters", "FamilyID", "Jet"}] &&
        data["SchemaVersion"] === 1 && MemberQ[{"Analytic", "Jet", "MLDE", "Derived"}, data["Kind"]] && MemberQ[{"q", "tau"}, data["Coordinate"]] &&
        IntegerQ[data["Dimension"]] && data["Dimension"] >= 1 && StringQ[data["FamilyID"]] &&
        (!KeyExistsQ[data, "Transform"] || (MatrixQ[data["Transform"], NumericQ] && Dimensions[data["Transform"]] === {data["Dimension"], data["Dimension"]})) &&
        ListQ[data["Parameters"]] && AllTrue[data["Parameters"], AssociationQ[#] && StringQ[#["ID"]] && StringQ[#["Label"]] &] &&
        Which[data["Kind"] === "Jet", AssociationQ[validateQExpansion[data["Jet"]]] && validateQExpansion[data["Jet"]]["Dimension"] === data["Dimension"],
            data["Kind"] === "Analytic", ListQ[data["Components"]] && Length[data["Components"]] === data["Dimension"] &&
                DeleteDuplicates[Flatten[definitionTreeViolations /@ data["Components"]]] === {} &&
                Sort[DeleteDuplicates[Cases[data["Components"], FormParameter[id_] :> id, {0, Infinity}]]] === Sort[Lookup[data["Parameters"], "ID", {}]],
            True, AssociationQ[Lookup[data, "Recipe", Missing[]]]],
    data, makeFailure["InvalidDefinition", "Malformed ModularFormDefinition."]];
validateFormDefinition[___] := makeFailure["InvalidDefinition", "Expected a ModularFormDefinition."];

(*
    Summary: The frozen context data a form record binds to.
    Parameters: c — Group or RepresentationContext; irrep — irrep ID, or a Rep (raw coefficient solving).
    Options/defaults: None.
    Returns: <|"Context", "Snapshot", "IrrepID" (or Missing), "Rep", "BasisID", "Dimension", "Arithmetic", "S", "T",
        "Assignment"|>, or Failure.
    Effects: Freezing a group registers its context binding.
    Failures: UnverifiedContext; MissingModularAssignment; InvalidIrrep; MissingRepresentations; GeneratorBindingMismatch.
    Example: formContextData[g, t]["Dimension"] is 3 for a triplet.
    Remarks: The group is provenance only: the record keeps the frozen context and the actual Rep, never a live lookup.
    See also: makeFormRecord.
*)
formContextData[c_, irrep_] := Module[{context = vectorContext[c], snapshot, variant, rep, s, t, assignment},
    If[FailureQ[context], Return[context]];
    snapshot = resolveRepContext[context]; If[FailureQ[snapshot], Return[snapshot]];
    assignment = snapshot["ModularAssignment"];
    If[!AssociationQ[assignment], Return[makeFailure["MissingModularAssignment", "Modular forms need an S,T assignment; use AssignModularGenerators or BuildModularGroup."]]];
    If[StringQ[irrep],
        If[!MemberQ[snapshot["CharacterData"]["IrrepIDs"], irrep], Return[makeFailure["InvalidIrrep", "Unknown irrep ID.", <|"IrrepIDs" -> {irrep}|>]]];
        variant = cgVariant[snapshot, irrep];
        If[MissingQ[variant], Return[makeFailure["MissingRepresentations", "The irrep has no accepted matrices; compute them first.", <|"IrrepIDs" -> {irrep}|>]]];
        rep = variant["Rep"],
        (* a raw Rep is identified by its realization identity (canonical entries), so a readable copy, the canonical
           form and an archived raw-Rep record share one BasisID (uxUpdatePlan.md 3, review N3) *)
        rep = irrep; variant = <|"Identity" -> With[{id = Quiet[repIdentity[rep, snapshot["GeneratorNames"]]]},
                If[StringQ[id], id, "rep-" <> Hash[repMatrices[rep], "SHA256", "HexString"]]],
            "Arithmetic" -> If[inexactDataQ[repMatrices[rep]], "Numerical", "Exact"]|>];
    s = modularGeneratorMatrix[context, rep, "S"]; If[FailureQ[s], Return[s]];
    t = modularGeneratorMatrix[context, rep, "T"]; If[FailureQ[t], Return[t]];
    <|"Context" -> context, "Snapshot" -> snapshot, "IrrepID" -> If[StringQ[irrep], irrep, Missing["RawRepresentation"]], "Rep" -> rep,
        "BasisID" -> variant["Identity"], "Dimension" -> Length[s], "Arithmetic" -> variant["Arithmetic"], "S" -> s, "T" -> t, "Assignment" -> assignment|>
];

(*
    Summary: Admissibility check rho(S^2) = e^{i Pi k} for a nonzero form of weight k.
    Parameters: s — S matrix; k — exact rational weight.
    Options/defaults: None.
    Returns: True, False, or "Undecidable" (numerical matrices whose residual is not clearly zero or nonzero).
    Effects: Pure.
    Failures: None.
    Example: the T' doublets have rho(S^2) = -1, so only odd weights are allowed; eta (k = 1/2) needs rho(S^2) = i.
    Remarks: F(-1/tau) = (-tau)^k rho(S) F(tau) on the principal branch applied twice gives rho(S)^2 = e^{i Pi k}
        (fractionalWeightPlan.md); for integer k this is the parity (-1)^k.
    See also: makeFormRecord; ModularDimension.
*)
formParityQ[s_?MatrixQ, k_?modularWeightQ] := With[{r = s . s - Exp[I Pi k] IdentityMatrix[Length[s]]},
    If[inexactDataQ[s], Which[Max[Abs[N[Flatten[r]]]] < 10^-8, True, Max[Abs[N[Flatten[r]]]] > 10^-4, False, True, "Undecidable"],
        AllTrue[Flatten[r], TrueQ[Quiet[TimeConstrained[RootReduce[#], 30, $Failed]] === 0] &]]];

(*
    Summary: The data of a new ModularForm record.
    Parameters: ctx — formContextData; weight — exact rational; definition — validated definition data; extra — association of
        record fields supplied by the creator (Method, Coefficients, Provenance, Family/Seed data).
    Options/defaults: None.
    Returns: Record association (D-S7-2), or Failure.
    Effects: Allocates an ID (the record is not registered).
    Failures: ShapeMismatch (definition dimension differs from the representation); ParityMismatch (rho(S^2) is not
        e^{i Pi k}); UndecidableParity; InvalidWeight.
    Example: makeFormRecord[ctx, 4, e4def, <||>]["Weight"] is 4.
    Remarks: Status starts "Unverified": creation never claims modularity. Expression is the human-facing tree, Value the
        computational recipe; the QExpansion property is separate and starts Missing["NotComputed"].
    See also: CreateModularForm; validateFormRecord.
*)
makeFormRecord[ctx_Association, weight_, definition_Association, extra_Association] := Module[{parity},
    If[!modularWeightQ[weight], Return[makeFailure["InvalidWeight", "The weight must be an exact rational (an integer or, for example, 1/2)."]]];
    If[definition["Dimension"] =!= ctx["Dimension"],
        Return[makeFailure["ShapeMismatch", "The definition has a different number of components than the representation.",
            <|"Components" -> definition["Dimension"], "Dimension" -> ctx["Dimension"]|>]]];
    parity = formParityQ[ctx["S"], weight];
    If[parity === "Undecidable", Return[makeFailure["UndecidableParity", "rho(S^2) = e^{i Pi k} could not be decided for the numerical representation."]]];
    If[!parity, Return[makeFailure["ParityMismatch", "A nonzero form of weight k needs rho(S^2) = e^{i Pi k} on its representation.", <|"Weight" -> weight|>]]];
    Join[<|"SchemaVersion" -> 1, "ID" -> "modularform-" <> CreateUUID[], "Revision" -> 1, "Context" -> ctx["Context"],
        "ContextDigest" -> contextDigest[ctx["Snapshot"]], "GroupIdentity" -> ctx["Snapshot"]["GroupIdentity"],
        "GeneratorIdentity" -> ctx["Snapshot"]["GeneratorIdentity"], "AssignmentID" -> ctx["Assignment"]["Identity"],
        "AssignmentWords" -> KeyTake[ctx["Assignment"], {"S", "T"}], "IrrepID" -> ctx["IrrepID"], "Rep" -> ctx["Rep"], "BasisID" -> ctx["BasisID"],
        "Weight" -> weight, "Dimension" -> ctx["Dimension"], "Definition" -> definition,
        "Expression" -> Lookup[definition, "Components"], "Value" -> <|"Kind" -> definition["Kind"], "Coordinate" -> definition["Coordinate"]|>,
        "QExpansion" -> Missing["NotComputed"], "Coefficients" -> Missing["Unresolved"],
        "Arithmetic" -> If[ctx["Arithmetic"] === "Numerical" || inexactDataQ[Lookup[definition, "Components"]], "Numerical", "Exact"],
        "Validation" -> <|"Status" -> "Unverified"|>, "Method" -> "Manual", "Provenance" -> <|"Source" -> "CreateModularForm"|>|>, extra]
];

(*
    Summary: Validate a form record (registry entry or candidate update).
    Parameters: data — record association.
    Options/defaults: None.
    Returns: The record, or InvalidModularForm Failure.
    Effects: Pure.
    Failures: InvalidModularForm (missing keys, bad revision, dimension or definition inconsistent with the Rep, an invalid
        QExpansion or normalization record).
    Example: a record whose Rep has another dimension fails.
    See also: commitFormUpdate.
*)
validateFormRecord[data_Association] := If[
    SubsetQ[Keys[data], {"SchemaVersion", "ID", "Revision", "Context", "ContextDigest", "GroupIdentity", "GeneratorIdentity", "AssignmentID",
        "IrrepID", "Rep", "BasisID", "Weight", "Dimension", "Definition", "Expression", "Value", "QExpansion", "Coefficients", "Arithmetic",
        "Validation", "Method", "Provenance"}] &&
        data["SchemaVersion"] === 1 && StringQ[data["ID"]] && IntegerQ[data["Revision"]] && data["Revision"] >= 1 && modularWeightQ[data["Weight"]] &&
        Length[repMatrices[data["Rep"]]] > 0 && Length[First[repMatrices[data["Rep"]]]] === data["Dimension"] &&
        With[{d = data["Definition"]}, AssociationQ[validateFormDefinition[ModularFormDefinition[d]]]] && data["Definition"]["Dimension"] === data["Dimension"] &&
        (MissingQ[data["QExpansion"]] || (AssociationQ[validateQExpansion[data["QExpansion"]]] && validateQExpansion[data["QExpansion"]]["Dimension"] === data["Dimension"])) &&
        (MissingQ[data["Coefficients"]] || normalizationRecordQ[data["Coefficients"]]) && MemberQ[{"Exact", "Numerical"}, data["Arithmetic"]],
    data, makeFailure["InvalidModularForm", "Malformed modular-form record."]];
validateFormRecord[___] := makeFailure["InvalidModularForm", "Expected a record association."];

(*
    Summary: Whether a coefficient record has the D-S7-4 shape.
    Parameters: r — any expression.
    Options/defaults: None.
    Returns: Boolean.
    Effects: Pure.
    Failures: None.
    Example: normalizationRecordQ[<|"Kind" -> "NoNormalizationNeeded", "Rules" -> {}, ...|>] is True.
    Remarks: Anchor records name the frame (AnchorFrameID, FrameRep, FrameFromStored), FamilyID, SeedID, Component,
        rational Exponent and nonzero Value; Rules map FormParameter IDs to values; ProofStatus is recorded.
    See also: initialNormalization.
*)
normalizationRecordQ[r_] := AssociationQ[r] && KeyExistsQ[r, "Kind"] && KeyExistsQ[r, "Rules"] && KeyExistsQ[r, "ProofStatus"] &&
    Switch[r["Kind"],
        "NoNormalizationNeeded", r["Rules"] === {} && MatrixQ[r["FrameFromStored"]],
        "Anchor", SubsetQ[Keys[r], {"AnchorFrameID", "FrameRep", "FrameFromStored", "FamilyID", "SeedID", "Component", "Exponent", "Value"}] &&
            MatrixQ[r["FrameFromStored"]] && IntegerQ[r["Component"]] && MatchQ[r["Exponent"], _Integer | _Rational] && !TrueQ[r["Value"] == 0] &&
            (r["Rules"] === Missing["Unresolved"] || (ListQ[r["Rules"]] && AllTrue[r["Rules"], MatchQ[#, _String -> _] &])),
        _, False];

(*
    Summary: The initial coefficient record of a manual definition.
    Parameters: definition — definition data; ctx — formContextData; options — validated CreateModularForm options.
    Options/defaults: None.
    Returns: NoNormalizationNeeded for a definition without parameters (its written scale is kept); for a parameterized
        definition the anchor resolved by resolveNormalizationAnchor (ModularNormalization.wl); or Failure.
    Effects: Pure.
    Failures: NormalizationUnavailable until the anchor resolver is loaded; anchor failures.
    Example: initialNormalization[e4def, ctx, opts]["Kind"] is "NoNormalizationNeeded".
    See also: CreateModularForm; resolveNormalizationAnchor.
*)
initialNormalization[definition_Association, ctx_Association, options_Association] := If[definition["Parameters"] === {},
    <|"Kind" -> "NoNormalizationNeeded", "Rules" -> {}, "FrameFromStored" -> IdentityMatrix[ctx["Dimension"]], "ProofStatus" -> "NotApplicable"|>,
    If[DownValues[resolveNormalizationAnchor] === {},
        makeFailure["NormalizationUnavailable", "Parameterized definitions need the normalization anchor resolver."],
        resolveNormalizationAnchor[definition, ctx, options]]];

(*
    Summary: Register, snapshot and update registry records.
    Parameters: record — validated record; y — ModularForm; id — record ID; revision — the revision the update was built
        from; patch — association of replaced fields.
    Options/defaults: None.
    Returns: registerForm: ModularForm[id]. snapshotForm: the record, or Failure. commitFormUpdate: the new record, or
        Failure (new Coefficients reset the Validation "Status" to "Unverified"). commitFormValidation[id, revision,
        status]: the record with a stronger Validation "Status" at the same revision, or Failure.
    Effects: registerForm and commitFormUpdate write $ModularFormRecords; nothing else.
    Failures: UnknownModularForm; RevisionConflict (the stored revision changed since the update was built);
        InvalidModularForm (the candidate does not validate); ImmutableField (ID, Weight, Rep, Definition, Context or
        BasisID in a patch).
    Example: commitFormUpdate[id, 1, <|"QExpansion" -> qexp|>]["Revision"] is 2.
    Remarks: An update is all or nothing: a failed or conflicting candidate leaves the stored record unchanged. Aliases
        of one ID observe committed updates.
    See also: ModularFormQExp; ModularFormGetCoeff.
*)
registerForm[record_Association] := (AssociateTo[$ModularFormRecords, record["ID"] -> record]; ModularForm[record["ID"]]);
snapshotForm[ModularForm[id_String]] := Lookup[$ModularFormRecords, id, makeFailure["UnknownModularForm", "No modular form with this ID exists in this kernel.", <|"ID" -> id|>]];
snapshotForm[___] := makeFailure["UnknownModularForm", "Expected a ModularForm."];
commitFormUpdate[id_String, revision_Integer, patch_Association] := Module[{current = Lookup[$ModularFormRecords, id, Missing[]], candidate},
    If[MissingQ[current], Return[makeFailure["UnknownModularForm", "No modular form with this ID exists in this kernel.", <|"ID" -> id|>]]];
    If[current["Revision"] =!= revision, Return[makeFailure["RevisionConflict", "The form changed since this update was computed; recompute it.",
        <|"ID" -> id, "Expected" -> revision, "Stored" -> current["Revision"]|>]]];
    If[IntersectingQ[Keys[patch], {"ID", "Weight", "Rep", "Definition", "Context", "BasisID", "Dimension", "Revision"}],
        Return[makeFailure["ImmutableField", "An update cannot change a form's identity, weight, representation or definition."]]];
    candidate = validateFormRecord[Join[current, patch, <|"Revision" -> revision + 1|>,
        (* new coefficients void a recorded validation result (it was for the old ones, methodOptionsPlan.md 2C.3) *)
        If[KeyExistsQ[patch, "Coefficients"] && !KeyExistsQ[patch, "Validation"],
            <|"Validation" -> Join[Lookup[current, "Validation", <||>], <|"Status" -> "Unverified"|>]|>, <||>]]];
    If[FailureQ[candidate], Return[candidate]];
    AssociateTo[$ModularFormRecords, id -> candidate];
    candidate
];
(* A ValidateModularForm result recorded in the form without a new revision (user decision 2026-10-13): only the
   Validation "Status" changes, only upward, only for the revision that was validated; bindings that pin the revision
   stay valid. *)
commitFormValidation[id_String, revision_Integer, status_String] := Module[{current = Lookup[$ModularFormRecords, id, Missing[]], candidate, stored},
    If[MissingQ[current], Return[makeFailure["UnknownModularForm", "No modular form with this ID exists in this kernel.", <|"ID" -> id|>]]];
    If[current["Revision"] =!= revision, Return[makeFailure["RevisionConflict", "The form changed since it was validated; validate it again.",
        <|"ID" -> id, "Expected" -> revision, "Stored" -> current["Revision"]|>]]];
    stored = Lookup[Lookup[current, "Validation", <||>], "Status", "Unverified"];
    If[cgStatusRank[formValidationStatusRank[status]] <= cgStatusRank[formValidationStatusRank[stored]], Return[current]];
    candidate = validateFormRecord[Join[current, <|"Validation" -> Join[Lookup[current, "Validation", <||>], <|"Status" -> status|>]|>]];
    If[FailureQ[candidate], Return[candidate]];
    AssociateTo[$ModularFormRecords, id -> candidate];
    candidate
];

(*
    Summary: Apply a form's resolved coefficient rules to an expression.
    Parameters: record — form record; expr — expression in FormParameter atoms; apply — ApplyCoefficients value.
    Options/defaults: None.
    Returns: The expression with FormParameter atoms replaced (apply True), unchanged (False or no parameters), or
        Missing["UnresolvedCoefficients", ids] when apply is True and coefficients are not resolved.
    Effects: Pure.
    Failures: None.
    Example: a form whose rules are {"f:c" -> 2} gives 2 for FormParameter["f:c"].
    Remarks: No unresolved coefficient is silently set to one.
    See also: ModularFormExpression; ModularFormValue.
*)
applyFormCoefficients[record_Association, expr_, apply_] := Module[{ids = Lookup[record["Definition"]["Parameters"], "ID", {}], rules},
    If[!TrueQ[apply] || ids === {}, Return[expr]];
    rules = Lookup[Replace[record["Coefficients"], _Missing -> <||>], "Rules", Missing[]];
    If[!ListQ[rules] || !SubsetQ[Keys[rules], ids], Return[Missing["UnresolvedCoefficients", ids]]];
    expr /. Map[FormParameter[First[#]] -> Last[#] &, rules]
];

Options[CreateModularForm] = {Normalization -> Automatic};

(*
    Summary: A modular-form object from a manual definition.
    Status: Alpha.
    Parameters: c — Group or RepresentationContext with an S,T assignment; irrep — irrep ID; k — exact rational weight
        (an integer or, for example, 1/2); definition — ModularFormDefinition.
    Options/defaults: Normalization -> Automatic (the manual-input anchor policy; NoNormalizationNeeded without parameters).
    Returns: ModularForm[id], or Failure.
    Effects: Freezes the group context; registers the record.
    Failures: Option failures; context failures; InvalidDefinition; ShapeMismatch; ParityMismatch; InvalidWeight;
        normalization failures.
    Example: CreateModularForm[c, trivial, 4, ModularFormDefinition[{ScalarModularExpression["E4", q]}, q]].
    Remarks: Creation checks shape, the accepted representation and parity, never modularity: the status is Unverified.
        Available at every dimension (manual research construction).
    See also: ModularFormDefinition; ConstructModularForms.
*)
CreateModularForm[c : (_Group | _RepresentationContext), irrep_String, k_, definition_ModularFormDefinition, options : OptionsPattern[]] := Module[
    {effective, ctx, def, record, coefficients},
    effective = resolveOperationOptions[CreateModularForm, "CreateModularForm", {options}]; If[FailureQ[effective], Return[effective]];
    def = validateFormDefinition[definition]; If[FailureQ[def], Return[def]];
    ctx = formContextData[c, irrep]; If[FailureQ[ctx], Return[ctx]];
    record = makeFormRecord[ctx, k, def, <||>]; If[FailureQ[record], Return[record]];
    coefficients = initialNormalization[def, ctx, effective]; If[FailureQ[coefficients], Return[coefficients]];
    record = validateFormRecord[Join[record, <|"Coefficients" -> coefficients|>]]; If[FailureQ[record], Return[record]];
    registerForm[record]
];
CreateModularForm[c : (_Group | _RepresentationContext), i_Integer, rest___] := withIrreps[c, {i}, CreateModularForm[c, #, rest] &];
CreateModularForm[___] := makeFailure["InvalidInput", "CreateModularForm expects a Group or RepresentationContext, an irrep ID, an exact rational weight, a ModularFormDefinition and options."];

(*
    Summary: Accessors of a ModularForm.
    Status: Alpha.
    Signatures: ModularFormData[y]; ModularFormRep[y]; ModularFormWeight[y]; ModularFormExpression[y, opts];
        ModularFormValue[y, opts]; ModularFormCoefficients[y]; y["Property"].
    Parameters: y — ModularForm.
    Options/defaults: ApplyCoefficients -> True (Expression, Value).
    Returns: The immutable record snapshot; the actual frozen Rep; the weight; the component trees (coefficients applied,
        or the raw parameterized definition); the computational recipe <|"Kind", "Coordinate", "Components" or "Jet"|>;
        the coefficient record or Missing["Unresolved"]; a record field.
    Effects: Pure.
    Failures: UnknownModularForm; option failures; Missing["UnresolvedCoefficients", ids] with ApplyCoefficients -> True
        and unresolved coefficients.
    Example: ModularFormWeight[y] is 4 for the E4 form.
    Remarks: Properties cannot be assigned; updates go through validated operations. A snapshot is a value: later
        updates of the form do not change it.
    See also: CreateModularForm; ModularFormQExp.
*)
ModularFormData[y_ModularForm] := snapshotForm[y];
ModularFormRep[y_ModularForm] := With[{r = snapshotForm[y]}, If[FailureQ[r], r, r["Rep"]]];
ModularFormWeight[y_ModularForm] := With[{r = snapshotForm[y]}, If[FailureQ[r], r, r["Weight"]]];
ModularFormCoefficients[y_ModularForm] := With[{r = snapshotForm[y]}, If[FailureQ[r], r, r["Coefficients"]]];
Options[ModularFormExpression] = {ApplyCoefficients -> True};
ModularFormExpression[y_ModularForm, options : OptionsPattern[]] := Module[{r = snapshotForm[y], effective},
    If[FailureQ[r], Return[r]];
    effective = resolveOperationOptions[ModularFormExpression, "ModularFormExpression", {options}]; If[FailureQ[effective], Return[effective]];
    If[MissingQ[r["Expression"]], r["Expression"], applyFormCoefficients[r, r["Expression"], effective[ApplyCoefficients]]]];
Options[ModularFormValue] = {ApplyCoefficients -> True};
ModularFormValue[y_ModularForm, options : OptionsPattern[]] := Module[{r = snapshotForm[y], effective, components},
    If[FailureQ[r], Return[r]];
    effective = resolveOperationOptions[ModularFormValue, "ModularFormValue", {options}]; If[FailureQ[effective], Return[effective]];
    If[r["Definition"]["Kind"] === "Jet", Return[<|"Kind" -> "Jet", "Coordinate" -> "q", "Jet" -> r["Definition"]["Jet"]|>]];
    components = applyFormCoefficients[r, Lookup[r["Definition"], "Components", Missing["NoComponents"]], effective[ApplyCoefficients]];
    If[MissingQ[components], components, Join[r["Value"], <|"Components" -> components|>]]];
(y : ModularForm[id_String])[property_String] := With[{r = snapshotForm[y]}, If[FailureQ[r], r, Lookup[r, property, Missing["UnknownProperty", property]]]];
ModularFormData[___] := makeFailure["InvalidInput", "Expected a ModularForm."];
ModularFormRep[___] := makeFailure["InvalidInput", "Expected a ModularForm."];
ModularFormWeight[___] := makeFailure["InvalidInput", "Expected a ModularForm."];
ModularFormCoefficients[___] := makeFailure["InvalidInput", "Expected a ModularForm."];
ModularFormExpression[___] := makeFailure["InvalidInput", "Expected a ModularForm and options."];
ModularFormValue[___] := makeFailure["InvalidInput", "Expected a ModularForm and options."];

Format[ModularForm[id_String], StandardForm] := Interpretation[Row[{"ModularForm[", With[{r = Lookup[$ModularFormRecords, id, <||>]},
    Row[{"weight ", Lookup[r, "Weight", "?"], ", dimension ", Lookup[r, "Dimension", "?"]}]], "]"}], ModularForm[id]];

True
