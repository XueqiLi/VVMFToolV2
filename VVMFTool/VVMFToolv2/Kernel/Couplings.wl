(*
    :Title: Couplings and coupled expressions
    :Context: VVMFTool`Private`
    :Summary: Inert Coupling parameters with stable records, coupled terms built from contraction channels or from
        arbitrary scalar expressions, user coefficient expressions with declared parameter symbols, and parameter merging.
    :Responsibilities: newCoupling, resolveCouplingParameters, coupleChannelData, coupleExpressionData,
        mergeParameterRecords, validateCoupledExpression; Coupling, CoupledExpression, CoupleContractions, CoupleExpressions,
        CouplingParameters, CoupledExpressionValue.
    :Dependencies: Contractions.wl (validateContractionSet, independenceData); Models.wl (modelPolynomialCheck,
        zeroCoefficientQ).
    :See Also: VVMFArch/step5Plan.md (CoupleContractions, CoupleExpressions, parameters).
*)

(* Kernel-local parameter records by ID, so a reused Coupling atom keeps its metadata, and a label counter. *)
If[!AssociationQ[$CouplingRecords], $CouplingRecords = <||>];
If[!IntegerQ[$CouplingLabelCounter], $CouplingLabelCounter = 0];

(*
    Summary: A fresh parameter with its record.
    Parameters: label — display label (Automatic: the prefix and a fresh number); prefix; source — HoldForm of a declared
        user symbol or Missing[].
    Options/defaults: None.
    Returns: Parameter record <|"Atom" -> Coupling[ID], "ID", "Label", "Domain" -> "Complex", "SourceAtom"|>.
    Effects: Registers the record in $CouplingRecords.
    Failures: None.
    Example: newCoupling[Automatic, "c", Missing[]]["Label"] is "c<n>" with a fresh n (made unique against declared labels,
        review M19).
    See also: resolveCouplingParameters.
*)
newCoupling[label_, prefix_String, source_] := Module[{id = "coupling-" <> CreateUUID[], record},
    record = <|"Atom" -> Coupling[id], "ID" -> id, "Label" -> If[label === Automatic, uniqueParameterLabel[prefix <> ToString[++$CouplingLabelCounter]], label],
        "Domain" -> "Complex", "SourceAtom" -> source|>;
    AssociateTo[$CouplingRecords, id -> record];
    record
];

(*
    Summary: A display label for a newly declared parameter that no other parameter of this kernel carries.
    Parameters: spelling — the declared symbol's InputForm text.
    Options/defaults: None.
    Returns: spelling, or spelling <> "_" <> n with the smallest free n >= 2.
    Effects: Pure (reads the parameter registry).
    Failures: None.
    Example: declaring lambda in two separate terms gives the labels "lambda" and "lambda_2".
    Remarks: Each declaration makes a new parameter (identity is explicit, D-S5-5); a parameter is shared between terms
        only through its Coupling atom (CouplingParameters), so a repeated spelling gets a distinguishable label
        (review M9).
    See also: resolveCouplingParameters.
*)
uniqueParameterLabel[spelling_String] := Module[{labels = Lookup[Values[$CouplingRecords], "Label", {}], n = 2},
    If[!MemberQ[labels, spelling], Return[spelling]];
    While[MemberQ[labels, spelling <> "_" <> ToString[n]], n++];
    spelling <> "_" <> ToString[n]
];

(*
    Summary: Coefficients and expressions with declared user atoms as inert Coupling atoms, and their parameter records.
    Parameters: coefficients — Automatic or a list of user expressions; count — number of terms; declarations — list of
        user symbols / indexed scalar atoms (ParameterSymbols); prefix — CouplingPrefix; expressions — the term's
        expressions (contraction polynomials or supplied expressions).
    Options/defaults: None.
    Returns: <|"Coefficients" -> expressions in Coupling atoms, "Expressions" -> the expressions with declared atoms
        replaced, "Parameters" -> records in first-appearance order (coefficient 1, expression 1, coefficient 2, ...)|>,
        or Failure.
    Effects: Registers new parameter records (one per declaration actually used).
    Failures: InvalidOption (wrong count, duplicate, non-atom or pattern declarations); FieldDependentCoupling (a coefficient
        containing a field component); UndeclaredSymbol (a coefficient leaf outside the scalar domain: symbols, indexed
        atoms, strings, foreign atoms; an indexed atom headed by a declared symbol but not declared itself);
        UnknownCoupling (a Coupling atom without a record in this kernel).
    Example: Automatic with count 2 gives two fresh couplings; CoupleExpressions[{alpha x . y}, ParameterSymbols -> {alpha}]
        turns alpha into a parameter of the expression.
    Remarks: Declared atoms are replaced in the coefficients and in the expressions (review M4) by fresh Coupling atoms
        whose records keep the held source spelling, so later definitions on the user symbol cannot rewrite a stored
        term; an indexed atom is replaced before its bare head. An existing Coupling atom shares that parameter.
    See also: CoupleContractions; CoupleExpressions; uniqueParameterLabel.
*)
resolveCouplingParameters[coefficients_, count_Integer, declarations_List, prefix_String, expressions_List] := Module[
    {supplied, used, bare, misused, rules, replace, records, replacedCoefficients, replacedExpressions, violations, atoms},
    (* Declarations are literal atoms: symbols or indexed atoms without pattern objects (review M18). *)
    If[!DuplicateFreeQ[declarations] || !AllTrue[declarations, MatchQ[#, _Symbol | _Symbol[___]] && !NumericQ[#] && !MemberQ[$InertAtomHeads, Head[#]] &&
            FreeQ[#, _Pattern | _Blank | _BlankSequence | _BlankNullSequence | _Optional | _Condition | _PatternTest | _Alternatives |
                _Repeated | _RepeatedNull | _Except | _Verbatim | _HoldPattern, {0, Infinity}, Heads -> True] &],
        Return[makeFailure["InvalidOption", "ParameterSymbols must be a duplicate-free list of symbols or indexed atoms without patterns; package atoms (Coupling, FieldComponent, VectorComponent) cannot be declared; share an existing parameter through its Coupling atom.", <|"Options" -> {ParameterSymbols}|>]]];
    If[coefficients =!= Automatic && (!ListQ[coefficients] || Length[coefficients] =!= count),
        Return[makeFailure["InvalidOption", "Couplings must list one coefficient per retained term.", <|"Expected" -> count|>]]];
    supplied = {If[coefficients === Automatic, {}, coefficients], expressions};
    (* Only declarations that occur become parameters; indexed atoms are replaced before bare symbols. *)
    used = Select[declarations, !AtomQ[#] && !FreeQ[supplied, #] &];
    (* A bare declaration counts only where it occurs outside the declared indexed atoms. *)
    bare = Select[declarations, AtomQ[#] && !FreeQ[supplied /. Map[# -> Null &, used], #] &];
    used = Join[used, bare];
    (* A declared bare symbol may not head an indexed atom that is not itself declared (kk declared, kk[1] used). *)
    misused = DeleteDuplicates[Cases[supplied, x : h_[___] /; MemberQ[bare, Unevaluated[h]] && !MemberQ[used, x], {0, Infinity}, Heads -> True]];
    If[misused =!= {}, Return[makeFailure["UndeclaredSymbol", "Indexed atoms whose head is a declared symbol must be declared themselves.",
        <|"Symbols" -> (HoldForm /@ misused)|>]]];
    rules = Map[Function[d, d -> newCoupling[uniqueParameterLabel[ToString[Unevaluated[d], InputForm]], prefix, HoldForm[d]]], used];
    replace[x_] := x /. Map[First[#] -> Last[#]["Atom"] &, rules];
    replacedCoefficients = If[coefficients === Automatic,
        Lookup[Table[newCoupling[Automatic, prefix, Missing[]], {count}], "Atom", {}], replace[coefficients]];
    replacedExpressions = replace[expressions];
    If[!FreeQ[replacedCoefficients, _FieldComponent | _FormComponent], Return[makeFailure["FieldDependentCoupling", "Explicit couplings must not contain field or form components."]]];
    violations = DeleteDuplicates[Flatten[scalarDomainViolations /@ replacedCoefficients]];
    If[violations =!= {}, Return[undeclaredSymbolFailure[violations, "Coefficients"]]];
    atoms = DeleteDuplicates[Cases[Riffle[replacedCoefficients, replacedExpressions], Coupling[_String], {0, Infinity}]];
    If[!AllTrue[atoms, KeyExistsQ[$CouplingRecords, First[#]] &],
        Return[makeFailure["UnknownCoupling", "A Coupling atom has no parameter record in this kernel."]]];
    records = Lookup[$CouplingRecords, First /@ atoms];
    <|"Coefficients" -> replacedCoefficients, "Expressions" -> replacedExpressions, "Parameters" -> records|>
];
resolveCouplingParameters[___] := makeFailure["InvalidInput", "Expected coefficients, a count, declarations, a prefix and expressions."];

(*
    Summary: Merge parameter record lists in first-appearance order.
    Parameters: lists — list of record lists.
    Options/defaults: None.
    Returns: Merged record list, or ParameterConflict Failure.
    Effects: Pure.
    Failures: ParameterConflict when one ID carries different metadata.
    Example: mergeParameterRecords[{{a}, {a, b}}] is {a, b}.
    See also: addTermData.
*)
mergeParameterRecords[lists_List] := Module[{merged = <||>, conflict = None},
    Do[Which[!KeyExistsQ[merged, r["ID"]], merged[r["ID"]] = r,
            merged[r["ID"]] =!= r, conflict = r["ID"]], {r, Flatten[lists, 1]}];
    If[conflict =!= None, makeFailure["ParameterConflict", "One parameter appears with different metadata.", <|"ParameterID" -> conflict|>], Values[merged]]
];

(*
    Summary: Build coupled-expression data from expressions, coefficients and identities.
    Parameters: expressions; channels — source channel IDs (or Missing); resolved — from resolveCouplingParameters;
        identity — <|"FieldIDs", "TargetIrrepID", "ContextDigest", "Symmetry", "Arithmetic", "Precision", "Tolerance"|>.
    Options/defaults: None.
    Returns: CoupledExpression data with a fresh TermID.
    Effects: Allocates the term ID.
    Failures: None.
    Example: coupledData[{x y}, {"path:1"}, <|"Coefficients" -> {c}, ...|>, id]["Value"] is c x y.
    See also: coupleChannelData; coupleExpressionData.
*)
coupledData[expressions_List, channels_List, resolved_Association, identity_Association] := Join[<|"SchemaVersion" -> 1,
    "TermID" -> "term-" <> CreateUUID[],
    "Terms" -> MapThread[<|"Expression" -> #1, "Channel" -> #2, "Coefficient" -> #3|> &, {expressions, channels, resolved["Coefficients"]}],
    "Value" -> Expand[resolved["Coefficients"] . expressions], "Parameters" -> resolved["Parameters"]|>, identity];

(*
    Summary: Coupled data of a contraction set under a channel policy.
    Parameters: data — validated set data; options — effective options (ChannelPolicy, Couplings, CouplingPrefix, ParameterSymbols held).
    Options/defaults: ChannelPolicy "Independent" (the independent basis) or "AllChannels" (every provably nonzero channel,
        with the linear relations reported).
    Returns: CoupledExpression data, or Failure.
    Effects: Registers parameters.
    Failures: Independence and coupling failures.
    Example: the A4 bilinear set gives one term with one coupling.
    See also: CoupleContractions.
*)
coupleChannelData[data_Association, policy_String, coefficients_, declarations_, prefix_String] := Module[{independent, channels, resolved, term},
    (* Approximate coefficients need a numerical set (review M20): an exact term must reconstruct exactly. *)
    If[data["Arithmetic"] === "Exact" && ListQ[coefficients] && inexactDataQ[coefficients],
        Return[makeFailure["NumericalInput", "Approximate couplings need a set with Arithmetic -> \"Numerical\"."]]];
    (* Approximate coefficients bound the term's precision (review M26): the term never claims more digits than its
       coefficients carry, and its tolerance is never tighter than that precision supports. *)
    term = If[data["Arithmetic"] === "Numerical" && ListQ[coefficients] && inexactDataQ[coefficients],
        With[{s = arithmeticSettings["Numerical", data["Precision"], Automatic, dataPrecision[coefficients]]},
            <|"Precision" -> s["Precision"], "Tolerance" -> Max[s["Tolerance"], data["Tolerance"]]|>],
        <|"Precision" -> data["Precision"], "Tolerance" -> data["Tolerance"]|>];
    independent = If[MissingQ[data["Independence"]], independenceData[data], data];
    If[FailureQ[independent], Return[independent]];
    channels = If[policy === "Independent",
        Select[independent["Channels"], MemberQ[independent["Independence"]["Basis"], #["ChannelID"]] &],
        Select[independent["Channels"], !TrueQ[#["Zero"]] &]];
    resolved = resolveCouplingParameters[coefficients, Length[channels], declarations, prefix, Lookup[channels, "Polynomial", {}]];
    If[FailureQ[resolved], Return[resolved]];
    Join[coupledData[resolved["Expressions"], Lookup[channels, "ChannelID", {}], resolved,
        <|"FieldIDs" -> data["FieldIDs"], "TargetIrrepID" -> data["TargetIrrepID"], "ContextDigest" -> data["ContextDigest"],
            "Symmetry" -> "Covariant (by construction)", "Arithmetic" -> data["Arithmetic"], "Precision" -> term["Precision"], "Tolerance" -> term["Tolerance"],
            (* the channels' statuses (methodOptionsPlan.md 2C.2) *)
            "VerificationStatus" -> contractionChannelsStatus[channels]|>],
        <|"Policy" -> policy, "Relations" -> independent["Independence"]["Relations"]|>,
        (* A modular set's slot records and namespace travel with the term (Stage 8); AddModelTerm recomputes them. *)
        KeyTake[data, {"FormSlots", "Namespace"}]]
];

(*
    Summary: Coupled data of arbitrary scalar expressions.
    Parameters: expressions — list; options as coupleChannelData plus arithmetic settings.
    Options/defaults: None.
    Returns: CoupledExpression data with Symmetry "Unverified", or Failure.
    Effects: Registers parameters.
    Failures: Coupling failures; NumericalInput (approximate expressions with exact arithmetic).
    Example: two nonzero expressions give two couplings; a proved zero is omitted.
    Remarks: No field, target or context identity is known; AddModelTerm validates covariance.
    See also: CoupleExpressions.
*)
coupleExpressionData[expressions_List, coefficients_, declarations_, prefix_String, settings_Association] := Module[{kept, resolved, components},
    If[settings["Arithmetic"] === "Exact" && inexactDataQ[{expressions, If[ListQ[coefficients], coefficients, {}]}],
        Return[makeFailure["NumericalInput", "Approximate expressions or couplings need Arithmetic -> \"Numerical\"."]]];
    kept = Select[Expand /@ expressions, !(# === 0 || (settings["Arithmetic"] =!= "Exact" && TrueQ[zeroCoefficientQ[#, settings]])) &];
    resolved = resolveCouplingParameters[coefficients, Length[kept], declarations, prefix, kept];
    If[FailureQ[resolved], Return[resolved]];
    components = DeleteDuplicates[Cases[resolved["Expressions"], _FieldComponent, {0, Infinity}]];
    coupledData[resolved["Expressions"], ConstantArray[Missing["NoChannel"], Length[kept]], resolved,
        <|"FieldIDs" -> DeleteDuplicates[First /@ components], "TargetIrrepID" -> Missing["Unknown"], "ContextDigest" -> Missing["Unknown"],
            "Symmetry" -> "Unverified", "VerificationStatus" -> "Unverified", "Arithmetic" -> settings["Arithmetic"],
            "Precision" -> If[settings["Arithmetic"] === "Exact", Infinity, settings["Precision"]], "Tolerance" -> settings["Tolerance"]|>]
];

(*
    Summary: Validate a CoupledExpression before use.
    Parameters: e — any expression.
    Options/defaults: None.
    Returns: Its data, or InvalidCoupledExpression Failure.
    Effects: Pure.
    Failures: Missing fields; a stored value that differs from the sum of its terms; parameters without records.
    Example: a CoupledExpression whose Value was edited by hand fails here.
    See also: AddModelTerm.
*)
(*
    Summary: Whether a coupled expression's stored value is the sum of its terms.
    Parameters: data — coupled-expression data.
    Options/defaults: None.
    Returns: True or False.
    Effects: Pure.
    Failures: None.
    Example: a numerical term whose difference expands to 0. passes; an edited exact Value fails.
    Remarks: Exact terms need an exact zero difference; numerical terms accept a difference that Chop removes at their
        declared tolerance.
    See also: validateCoupledExpression.
*)
valueMatchesTermsQ[data_Association] := With[{difference = Expand[data["Value"] - Total[Map[#["Coefficient"] #["Expression"] &, data["Terms"]]]]},
    difference === 0 || (data["Arithmetic"] === "Numerical" && NumericQ[data["Tolerance"]] && Chop[difference, data["Tolerance"]] === 0)];

validateCoupledExpression[CoupledExpression[data_Association]] := If[
    SubsetQ[Keys[data], {"SchemaVersion", "TermID", "Terms", "Value", "Parameters", "FieldIDs", "TargetIrrepID", "ContextDigest", "Symmetry",
        "Arithmetic", "Precision", "Tolerance"}] && data["SchemaVersion"] === 1 && StringQ[data["TermID"]] &&
        AllTrue[data["Terms"], SubsetQ[Keys[#], {"Expression", "Channel", "Coefficient"}] &] &&
        valueMatchesTermsQ[data] &&
        AllTrue[data["Parameters"], SubsetQ[Keys[#], {"Atom", "ID", "Label", "Domain", "SourceAtom"}] && #["Atom"] === Coupling[#["ID"]] &] &&
        SubsetQ[Lookup[data["Parameters"], "ID", {}], First /@ DeleteDuplicates[Cases[data["Value"], _Coupling, {0, Infinity}]]],
    data, makeFailure["InvalidCoupledExpression", "Malformed or inconsistent CoupledExpression."]];
validateCoupledExpression[___] := makeFailure["InvalidCoupledExpression", "Expected a CoupledExpression."];

Options[CoupleContractions] = {ChannelPolicy -> "Independent", Couplings -> Automatic, CouplingPrefix -> "c", ParameterSymbols -> {}};

(*
    Summary: A coupled term from a contraction set: one fresh coupling per retained channel.
    Parameters: set — ContractionSet.
    Options/defaults: ChannelPolicy "Independent" (default; the independent basis) or "AllChannels" (every provably nonzero
        channel; relations reported); Couplings Automatic or explicit coefficient expressions; CouplingPrefix "c";
        ParameterSymbols {} (user symbols or indexed atoms used in Couplings).
    Returns: CoupledExpression with a fresh TermID, or Failure.
    Effects: Registers parameters; the input set is unchanged.
    Failures: InvalidContractionSet; InvalidOption; UnknownOption; FieldDependentCoupling; UndeclaredSymbol; independence failures.
    Example: CouplingParameters[CoupleContractions[Contractions[m, {l, r}]]] has one record.
    Remarks: Declared symbols are replaced by inert Coupling atoms whose records keep the held source spelling, so later
        definitions on those symbols cannot change a stored term. Each declaration makes a new parameter; a spelling
        that already labels a parameter in this kernel gets a suffixed label (lambda_2); share a parameter between terms
        through its Coupling atom.
    See also: Contractions; AddModelTerm; CoupleExpressions.
*)
CoupleContractions[set_ContractionSet, options : OptionsPattern[]] := Module[{data = validateContractionSet[set], effective, result},
    If[FailureQ[data], Return[data]];
    effective = resolveOperationOptions[CoupleContractions, "CoupleContractions", {options}];
    If[FailureQ[effective], Return[effective]];
    result = coupleChannelData[data, effective[ChannelPolicy], effective[Couplings], effective[ParameterSymbols], effective[CouplingPrefix]];
    If[FailureQ[result], result, CoupledExpression[result]]
];
CoupleContractions[___] := makeFailure["InvalidInput", "CoupleContractions expects a ContractionSet and options."];

Options[CoupleExpressions] = {Couplings -> Automatic, CouplingPrefix -> "c", ParameterSymbols -> {}, Arithmetic -> "Exact", WorkingPrecision -> 50,
    Tolerance -> Automatic};

(*
    Summary: A coupled term from arbitrary scalar expressions: one coefficient per nonzero expression.
    Parameters: expressions — list of scalar expressions.
    Options/defaults: Couplings Automatic or a coefficient list; CouplingPrefix "c"; ParameterSymbols {}; Arithmetic "Exact",
        WorkingPrecision, Tolerance.
    Returns: CoupledExpression with Symmetry "Unverified", or Failure.
    Effects: Registers parameters.
    Failures: InvalidOption; UnknownOption; InapplicableOption (Tolerance with exact arithmetic); FieldDependentCoupling;
        UndeclaredSymbol; NumericalInput.
    Example: CoupleExpressions[{x1^2, x2^2}, Couplings -> {alpha, beta}, ParameterSymbols -> {alpha, beta}].
    Remarks: Only proved zero expressions are omitted; no polynomial independence is claimed; AddModelTerm validates
        covariance when the term joins a model. Declared ParameterSymbols are replaced in the coefficients and in the
        expressions themselves (CoupleExpressions[{alpha x . y}, ParameterSymbols -> {alpha}] makes alpha a parameter).
    See also: CoupleContractions; AddModelTerm.
*)
CoupleExpressions[expressions_List, options : OptionsPattern[]] := Module[{effective, settings, result},
    effective = resolveOperationOptions[CoupleExpressions, "CoupleExpressions", {options}];
    If[FailureQ[effective], Return[effective]];
    (* The data's own precision bounds the term's settings (review M20): machine-precision input gives machine settings. *)
    settings = arithmeticSettings[effective[Arithmetic], effective[WorkingPrecision], effective[Tolerance],
        dataPrecision[{expressions, If[ListQ[effective[Couplings]], effective[Couplings], {}]}]];
    If[FailureQ[settings], Return[settings]];
    (* Coefficient data are used as given (no CG amplification): the tolerance must only be within their accuracy. *)
    settings = checkedTolerance[settings, False];
    If[FailureQ[settings], Return[settings]];
    result = coupleExpressionData[expressions, effective[Couplings], effective[ParameterSymbols], effective[CouplingPrefix], settings];
    If[FailureQ[result], result, CoupledExpression[result]]
];
CoupleExpressions[___] := makeFailure["InvalidInput", "CoupleExpressions expects a list of expressions and options."];

(*
    Summary: The parameter records of a coupled term.
    Parameters: e — CoupledExpression.
    Options/defaults: None.
    Returns: List of records in first-appearance order, or Failure.
    Effects: Pure.
    Failures: InvalidCoupledExpression.
    Example: CouplingParameters[term][[1, "Label"]] is "c1" for a first generated coupling.
    See also: ModelParameters.
*)
CouplingParameters[e_CoupledExpression] := With[{data = validateCoupledExpression[e]}, If[FailureQ[data], data, data["Parameters"]]];
CouplingParameters[___] := makeFailure["InvalidInput", "CouplingParameters expects a CoupledExpression."];

(*
    Summary: The scalar value of a coupled term.
    Parameters: e — CoupledExpression.
    Options/defaults: None.
    Returns: Expression in field components and inert Coupling atoms, or Failure.
    Effects: Pure.
    Failures: InvalidCoupledExpression.
    Example: CoupledExpressionValue[CoupleExpressions[{x}]] is Coupling[id] x.
    See also: ModelExpression.
*)
CoupledExpressionValue[e_CoupledExpression] := With[{data = validateCoupledExpression[e]}, If[FailureQ[data], data, data["Value"]]];
CoupledExpressionValue[___] := makeFailure["InvalidInput", "CoupledExpressionValue expects a CoupledExpression."];

Format[CoupledExpression[data_Association], StandardForm] := Interpretation[Row[{"CoupledExpression[", Length[Lookup[data, "Terms", {}]], " terms, ",
    Lookup[data, "Symmetry", "?"], "]"}], CoupledExpression[data]];

True
