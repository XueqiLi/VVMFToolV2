(*
    :Title: Finite-group models
    :Context: VVMFTool`Private`
    :Summary: Immutable models (fields, a degree-one target, terms and parameters in one frozen context), exact
        coefficient-domain checks and all-generator polynomial covariance by simultaneous substitution.
    :Responsibilities: modelPolynomialCheck, parameterKernels, zeroCoefficientQ, validatePolynomialCovariance,
        makeModelData, validateModelSchema, addTermData; Model, CreateModel, AddModelTerm, ModelExpression,
        ModelParameters, ValidateModel.
    :Dependencies: Fields.wl; Couplings.wl (validateCoupledExpression, mergeParameterRecords); CGData.wl (cgVariant).
    :See Also: VVMFArch/step5Plan.md (Model, AddModelTerm, ValidateModel).
*)

(*
    Summary: Check that an expression is a polynomial in known field components with field-independent scalar coefficients.
    Parameters: expr — expression; components — the registered component atoms.
    Options/defaults: None.
    Returns: <|"Variables" -> components present|>, or Failure.
    Effects: Pure.
    Failures: UnknownComponent (a FieldComponent of an unregistered field); UndeclaredSymbol (a free symbol that is not a
        numeric constant; user parameters must be declared and appear as Coupling atoms); NonPolynomial; NonfiniteCoefficient.
    Example: modelPolynomialCheck[Coupling["c"] FieldComponent["f", 1]^2, {FieldComponent["f", 1]}] passes.
    Remarks: Numeric constants such as Pi pass; functions of Coupling atoms are scalar coefficients.
    See also: validatePolynomialCovariance; AddModelTerm.
*)
modelPolynomialCheck[expr_, components_List] := Module[{present, violations, foreign},
    If[!FreeQ[expr, ComplexInfinity | Indeterminate | _DirectedInfinity],
        Return[makeFailure["NonfiniteCoefficient", "The expression has an undefined or infinite coefficient."]]];
    (* Form-slot components are formal variables like field components (D-S8-2): they must be registered too. *)
    present = DeleteDuplicates[Cases[expr, _FieldComponent | _FormComponent, {0, Infinity}]];
    If[!SubsetQ[components, present],
        Return[makeFailure["UnknownComponent", "The expression uses components of fields or form slots that are not registered in the model.",
            <|"Components" -> Complement[present, components]|>]]];
    (* Whitelist (review M3): every leaf is a numeric constant, a field component or a parameter atom. *)
    violations = scalarDomainViolations[expr];
    foreign = Select[violations, MatchQ[#, _VectorComponent | _FieldComponent] &];
    If[foreign =!= {}, Return[makeFailure["UnknownComponent", "The expression uses component atoms that are not field components of the model.",
        <|"Components" -> foreign|>]]];
    If[violations =!= {}, Return[undeclaredSymbolFailure[violations, "Scalar coefficients"]]];
    If[!PolynomialQ[expr, present], Return[makeFailure["NonPolynomial", "The expression is not polynomial in the field components."]]];
    <|"Variables" -> present|>
];

(*
    Summary: Whether an expression is a numeric constant whose symbols are all mathematical constants.
    Parameters: e — expression.
    Options/defaults: None.
    Returns: Boolean.
    Effects: Pure.
    Failures: None.
    Example: numericConstantQ[Sqrt[2] Pi] is True; with NumericQ[m] ^= True, numericConstantQ[m] is False (review M17).
    Remarks: NumericQ alone admits symbols given a NumericQ upvalue; those are parameters in disguise. Symbol leaves (heads
        excluded) must have the Constant attribute (Pi, E, EulerGamma, Catalan, ...); the internals of Root and
        AlgebraicNumber objects are not inspected.
    See also: scalarDomainViolations.
*)
numericConstantQ[e_] := NumericQ[e] && AllTrue[Cases[{e /. {_Root -> 1, _AlgebraicNumber -> 1}}, _Symbol, Infinity, Heads -> False],
    MemberQ[Attributes[#], Constant] &];

(*
    Summary: Whether an expression carries approximate numbers, and the precision those numbers support.
    Parameters: e — any expression (scalars, matrices, records of them).
    Options/defaults: None.
    Returns: inexactDataQ: Boolean. dataPrecision: Infinity (exact data), MachinePrecision (any machine number, or only
        approximate zeros) or the lowest precision of the nonzero approximate numbers, rounded down to whole digits (a
        WorkingPrecision value).
    Effects: Pure.
    Failures: None.
    Example: inexactDataQ[1.5 + 2. I] is True (a Complex atom hides its parts from _Real); dataPrecision[{1.`20, 0``20}]
        is 20; dataPrecision[{1, Sqrt[2]}] is Infinity.
    Remarks: One predicate for every approximate-input gate (review M26): InexactNumberQ sees approximate Real and Complex
        atoms. An approximate zero has Precision 0, so it never bounds a precision; it still makes the data inexact.
    See also: makeModelData; extractionSettings; coupleChannelData.
*)
inexactDataQ[e_] := !FreeQ[e, _?InexactNumberQ];
dataPrecision[e_] := Module[{numbers = Cases[{e}, _?InexactNumberQ, {0, Infinity}], precisions},
    If[numbers === {}, Return[Infinity]];
    precisions = Precision /@ Select[numbers, # != 0 &];
    If[precisions === {} || MemberQ[precisions, MachinePrecision], MachinePrecision, Floor[Min[precisions]]]];

(*
    Summary: The precision supported by the representation data of a model: its fields' and its target's matrices.
    Parameters: model — model data (or an association with "Fields" and "TargetRep").
    Options/defaults: None.
    Returns: Infinity for exact matrices, else as dataPrecision.
    Effects: Pure.
    Failures: None.
    Example: a model over a field whose accepted variant is a 20-digit numerical representation has data precision 20.
    Remarks: Stage 2 stores numerical-tier variants; a model over them is numerical (review M25, plan line 104).
    See also: makeModelData; numericalModelView.
*)
modelDataPrecision[model_Association] := dataPrecision[{Map[repMatrices, Lookup[model["Fields"], "Rep", {}]], repMatrices[model["TargetRep"]]}];

(*
    Summary: Check a numerical tolerance against the accuracy its data can support.
    Parameters: settings — arithmeticSettings association; dataBoundedQ — True when the precision is bounded by
        numerical-tier representation matrices that feed CG and covariance computations (error amplification); False
        for coefficient data used as given.
    Options/defaults: None.
    Returns: settings, or Failure["InvalidOption"] naming the minimum tolerance.
    Effects: Pure.
    Failures: InvalidOption.
    Example: a 24-digit field model with Tolerance -> 10^-40 fails; exact data at 30 digits accept Tolerance -> 10^-20.
    Remarks: One rule (review M30): a tolerance is never below 10^-digits of the effective precision, and when
        numerical-tier representation data bound the precision it is never below the automatic tolerance
        10^-Floor[digits/2] there, so a freshly built record never fails its own residual check. Exact settings pass
        unchanged.
    See also: automaticTolerance; numericalModelView; buildContractionSet.
*)
checkedTolerance[settings_Association, dataBoundedQ_] := Module[{minimum},
    If[settings["Arithmetic"] =!= "Numerical", Return[settings]];
    minimum = If[TrueQ[dataBoundedQ], automaticTolerance[settings["Precision"]], 10^(-precisionDigits[settings["Precision"]])];
    If[settings["Tolerance"] >= minimum, settings,
        makeFailure["InvalidOption", "Tolerance is tighter than the data support at this precision; use a larger Tolerance or more precise data.",
            <|"Options" -> {Tolerance}, "Tolerance" -> settings["Tolerance"], "MinimumTolerance" -> minimum, "Precision" -> settings["Precision"]|>]]];
precisionDigits[p_] := If[p === MachinePrecision, 16, Floor[p]];
automaticTolerance[p_] := 10^(-Floor[precisionDigits[p]/2]);

(* Inert atoms of the package: never declarable parameters (review M27). *)
$InertAtomHeads = {Coupling, FieldComponent, VectorComponent, FormParameter, FormVariable, FormComponent};

(*
    Summary: The subexpressions of a scalar that are outside the coefficient domain.
    Parameters: e — expression.
    Options/defaults: None.
    Returns: List of maximal offending subexpressions ({} when e is in the domain).
    Effects: Pure.
    Failures: None.
    Example: scalarDomainViolations[k[1] FieldComponent["f", 1]] is {k[1]}; Sqrt[2] Sin[Coupling["c"]] has none.
    Remarks: The domain is a whitelist (review M3): a numeric constant (numericConstantQ: NumericQ with only Constant symbols,
        including Pi and Root objects, whose internals are not inspected), FieldComponent[_String, _Integer], Coupling[_String], and Plus, Times, Power or a
        NumericFunction head applied to members of the domain. Symbols, indexed atoms, strings, Failure objects and
        foreign inert atoms (VectorComponent) are reported.
    See also: modelPolynomialCheck; resolveCouplingParameters.
*)
scalarDomainViolations[e_] := Which[
    MatchQ[e, FieldComponent[_String, _Integer] | Coupling[_String] | FormComponent[_String, _Integer]], {},
    numericConstantQ[e], {},
    !AtomQ[e] && (MatchQ[e, _Plus | _Times | _Power] || (Head[Head[e]] === Symbol && MemberQ[Attributes[Evaluate[Head[e]]], NumericFunction])),
        DeleteDuplicates[Flatten[scalarDomainViolations /@ (List @@ e)]],
    True, {e}];

(*
    Summary: The UndeclaredSymbol failure for scalar-domain violations, naming what can be declared and what cannot (review M22b).
    Parameters: violations — non-empty list from scalarDomainViolations; what — the subject of the message ("Coefficients").
    Options/defaults: None.
    Returns: Failure["UndeclaredSymbol", <|"Symbols", "Declarable", "Foreign"|>].
    Effects: Pure.
    Failures: None (it builds the failure).
    Example: undeclaredSymbolFailure[{Coupling["id"][1]}, "Coefficients"] says the leaf cannot be declared.
    Remarks: Declarable leaves are user symbols and indexed atoms with a symbol head (other than Coupling); everything else
        (Coupling[id][k], strings, inert atoms of other kinds) is foreign and cannot be fixed by a declaration.
    See also: scalarDomainViolations; resolveCouplingParameters.
*)
undeclaredSymbolFailure[violations_List, what_String] := Module[{declarable, foreign},
    declarable = Select[violations, MatchQ[#, _Symbol | _Symbol[___]] && !MemberQ[$InertAtomHeads, Head[#]] &];
    foreign = Complement[violations, declarable];
    makeFailure["UndeclaredSymbol", StringJoin[what, " must be numbers, numeric functions or declared parameters.",
            If[declarable =!= {}, " Declare the symbols and indexed atoms in \"Declarable\" with ParameterSymbols.", ""],
            If[foreign =!= {}, " The atoms in \"Foreign\" (for example a Coupling atom applied to arguments, a string or another package's atom) cannot be declared; remove them.", ""]],
        <|"Symbols" -> (HoldForm /@ violations), "Declarable" -> (HoldForm /@ declarable), "Foreign" -> (HoldForm /@ foreign)|>]];

(*
    Summary: The parameter kernels of scalar coefficients: Coupling atoms and maximal non-polynomial subexpressions containing them.
    Parameters: expr — scalar coefficient expression.
    Options/defaults: None.
    Returns: {kernel -> fresh variable, ...}.
    Effects: Pure.
    Failures: None.
    Example: parameterKernels[Coupling["a"] + Sin[Coupling["b"]]] gives kernels Coupling["a"] and Sin[Coupling["b"]].
    Remarks: Treating the kernels as independent variables is sound for proving a coefficient zero (a polynomial identity
        in independent kernels holds for every value); identities between kernels (Sin^2 + Cos^2) are not used, so such
        cases are reported undecidable rather than certified.
    See also: zeroCoefficientQ.
*)
parameterKernels[expr_] := With[{kernels = DeleteDuplicates[kernelLeaves[expr]]},
    Thread[kernels -> Array[parameterKernelVariable, Length[kernels]]]];

(*
    Summary: The maximal parameter-dependent subexpressions that are not polynomial operations (parameterKernels' walk).
    Parameters: e — expression.
    Options/defaults: None.
    Returns: List of kernels (Coupling atoms and maximal non-polynomial subexpressions containing them), with repeats.
    Effects: Pure.
    Failures: None.
    Example: kernelLeaves[Coupling["a"]^2 + Sin[Coupling["b"]]] is {Coupling["a"], Sin[Coupling["b"]]}; a negative power such as
        1/Coupling["a"] is itself a kernel (review M16), so coefficients stay polynomial in the kernels.
    Remarks: A top-level recursion with indexed private variables (parameterKernelVariable[k]) replaces the earlier local
        recursive function and its Unique/temporary symbols, which were never released (review M13).
    See also: parameterKernels.
*)
kernelLeaves[e_] := Which[
    FreeQ[e, _Coupling], {},
    MatchQ[e, _Plus | _Times], Flatten[kernelLeaves /@ (List @@ e)],
    MatchQ[e, Power[_, _Integer?Positive]], kernelLeaves[First[e]],
    True, {e}];

(*
    Summary: Decide that a scalar coefficient (in parameters and exact constants) is zero.
    Parameters: c — coefficient; settings — arithmetic settings.
    Options/defaults: None.
    Returns: True, False, or "Undecidable".
    Effects: Pure.
    Failures: None.
    Example: zeroCoefficientQ[Coupling["a"] (Sqrt[2]^2 - 2), exact] is True.
    Remarks: Exact: the coefficient is expanded as a polynomial in parameter kernels and every numeric coefficient
        must RootReduce to 0 (zero is then proved). A nonzero coefficient decides False when every kernel is a parameter
        (independent variables) or a numerical witness shows the function is not identically zero; otherwise, and when a
        numeric part cannot be decided in time, the result is "Undecidable". Numerical: magnitudes at the tolerance.
    See also: parameterKernels; validatePolynomialCovariance.
*)
zeroCoefficientQ[c_, settings_Association] := Module[{rules, poly, coefficients, decided},
    If[c === 0, Return[True]];
    rules = parameterKernels[c];
    poly = Expand[c /. rules];
    If[!PolynomialQ[poly, Values[rules]], Return["Undecidable"]];
    coefficients = If[rules === {}, {poly}, Values[CoefficientRules[poly, Values[rules]]]];
    If[settings["Arithmetic"] =!= "Exact",
        (* Numerical: zero within the tolerance; nonzero only when every kernel is a parameter or a witness at the working
           precision exceeds the tolerance (review M15: dependent kernels may cancel identically). *)
        Return[Which[
            !AllTrue[coefficients, NumericQ], "Undecidable",
            AllTrue[coefficients, Abs[N[#]] <= settings["Tolerance"] &], True,
            AllTrue[Keys[rules], Head[#] === Coupling &], False,
            numericalWitnessQ[c, settings], False,
            True, "Undecidable"]]];
    (* Exact arithmetic never decides on approximate data (review M25): CoefficientRules drops approximate zeros, so an
       inexact coefficient could look "all zero". *)
    If[inexactDataQ[c], Return["Undecidable"]];
    decided = Map[If[!NumericQ[#], "Undecidable", numericZeroDecision[#]] &, coefficients];
    Which[
        AllTrue[decided, TrueQ], True,
        MemberQ[decided, "Undecidable"], "Undecidable",
        (* Independent kernels prove zeros, but a nonzero polynomial in dependent kernels (Sin, Cos of one parameter)
           may still vanish: nonzero is decided structurally only when every kernel is a parameter, else by a witness. *)
        AllTrue[Keys[rules], Head[#] === Coupling &], False,
        nonzeroWitnessQ[c], False,
        True, "Undecidable"]
];

(*
    Summary: Decide whether one numeric constant is zero, exactly.
    Parameters: c — numeric constant (no parameters).
    Options/defaults: None.
    Returns: True (proved zero), False (proved nonzero) or "Undecidable".
    Effects: Pure.
    Failures: None.
    Example: numericZeroDecision[Sqrt[2]^2 - 2] is True; numericZeroDecision[Sqrt[2] - 1] is False;
        numericZeroDecision[Log[2] + Log[3] - Log[6]] is "Undecidable".
    Remarks: RootReduce decides algebraic numbers only (review M1): a nonzero RootReduce result proves nonzero when the
        constant is algebraic; any other constant is nonzero only when a 60-digit evaluation is clearly away from zero
        (precision above 30 digits and magnitude above 10^-30); a transcendental equality is never decided from
        RootReduce's failure to simplify it.
    See also: zeroCoefficientQ; nonzeroWitnessQ.
*)
numericZeroDecision[c_] := Module[{r = Quiet[TimeConstrained[RootReduce[c], 30, $Failed]], v},
    Which[
        r === 0, True,
        r =!= $Failed && TrueQ[Quiet[TimeConstrained[exactAlgebraicQ[c], 30, False]]], False,
        True, v = Quiet[N[c, 60]];
            If[NumberQ[v] && Precision[v] > 30 && Abs[v] > 10^-30, False, "Undecidable"]]
];

(*
    Summary: Certify that a scalar coefficient in parameters is not identically zero by a numerical witness.
    Parameters: c — coefficient expression in Coupling atoms and exact constants.
    Options/defaults: None.
    Returns: True when the coefficient evaluates far from zero at pseudorandom complex rational parameter values, else False.
    Effects: Pure (seeded).
    Failures: None.
    Example: nonzeroWitnessQ[Sin[Coupling["a"]]] is True; nonzeroWitnessQ[Sin[Coupling["a"]]^2 + Cos[Coupling["a"]]^2 - 1] is False.
    Remarks: A function that is nonzero at one point is not identically zero; the value is computed at 60 digits and must
        exceed 10^-30, so a cancellation artefact cannot pass.
    See also: zeroCoefficientQ.
*)
nonzeroWitnessQ[c_] := Module[{couplings = DeleteDuplicates[Cases[c, _Coupling, {0, Infinity}]], values, v},
    values = BlockRandom[Table[RandomInteger[{1, 97}]/RandomInteger[{2, 89}] + I RandomInteger[{1, 97}]/RandomInteger[{2, 89}], {Length[couplings]}],
        RandomSeeding -> Hash[{"nonzeroWitness", c}]];
    v = Quiet[N[c /. Thread[couplings -> values], 60]];
    NumberQ[v] && Precision[v] > 30 && Abs[v] > 10^-30
];

(*
    Summary: A numerical witness that a numerical coefficient in parameters is nonzero beyond the declared tolerance.
    Parameters: c — coefficient (approximate constants, parameters); settings — numerical arithmetic settings.
    Options/defaults: None.
    Returns: Boolean.
    Effects: Pure (seeded).
    Failures: None.
    Example: numericalWitnessQ[Sin[Coupling["a"]], s30] is True; for Sin^2 + Cos^2 - 1 it is False.
    Remarks: The coefficient is evaluated at the seeded parameter point of nonzeroWitnessQ at the working precision and
        must be a number exceeding the tolerance.
    See also: zeroCoefficientQ; nonzeroWitnessQ.
*)
numericalWitnessQ[c_, settings_Association] := Module[{couplings = DeleteDuplicates[Cases[c, _Coupling, {0, Infinity}]], values, v},
    values = BlockRandom[Table[RandomInteger[{1, 97}]/RandomInteger[{2, 89}] + I RandomInteger[{1, 97}]/RandomInteger[{2, 89}], {Length[couplings]}],
        RandomSeeding -> Hash[{"nonzeroWitness", c}]];
    v = Quiet[N[c /. Thread[couplings -> values], Replace[settings["Precision"], Infinity -> 50]]];
    NumberQ[v] && Abs[v] > settings["Tolerance"]
];

(*
    Summary: Check covariance of a scalar polynomial under every recorded generator.
    Parameters: model — validated model data; expr — expression in the model's field components.
    Options/defaults: None.
    Returns: <|"Covariant" -> True|False, "Generator" -> index of the first failing generator or None,
        "Checked" -> number of generators, "Arithmetic"|>, or Failure (domain failures; UndecidableCovariance).
    Effects: Pure.
    Failures: modelPolynomialCheck failures; UndecidableCovariance when a required coefficient equality cannot be proved.
    Example: the A4 triplet invariant x . y is covariant; x1 y2 alone is not.
    Remarks: For generator i every field's components are replaced simultaneously, x -> D_f(g_i) . x (one rule list, so a
        repeated field transforms consistently), and the difference with chi_target(g_i) expr must vanish coefficient by
        coefficient in the field components.
    See also: AddModelTerm; ValidateModel.
*)
validatePolynomialCovariance[model_Association, expr_] := Module[{components, check, settings, generators, chi, outcomes},
    components = modelComponents[model];
    check = modelPolynomialCheck[expr, components];
    If[FailureQ[check], Return[check]];
    settings = modelSettings[model];
    generators = Length[repMatrices[model["TargetRep"]]];
    chi = repMatrices[model["TargetRep"]][[All, 1, 1]];
    (* Coefficients are taken over every registered component (review M2): the substitution x -> D.x introduces
       components absent from expr, which must be polynomial variables, never parts of a "coefficient". Every
       generator is checked, so the verdict does not depend on generator order. *)
    outcomes = Table[Module[{rules, difference, coefficients, decided},
            rules = modelGeneratorRules[model, i];
            difference = Expand[(expr /. rules) - chi[[i]] expr];
            (* Exact settings refuse inexact data before CoefficientRules, which drops approximate zeros (review M25); in
               numerical settings a dropped 0``n is zero at the data's precision. *)
            If[settings["Arithmetic"] === "Exact" && inexactDataQ[difference], Return["Undecidable", Module]];
            coefficients = If[components === {}, {difference}, Values[CoefficientRules[difference, components]]];
            decided = zeroCoefficientQ[#, settings] & /@ coefficients;
            Which[MemberQ[decided, False], False, MemberQ[decided, "Undecidable"], "Undecidable", True, True]],
        {i, generators}];
    Which[
        MemberQ[outcomes, False], <|"Covariant" -> False, "Generator" -> First[FirstPosition[outcomes, False]], "Checked" -> generators,
            "Arithmetic" -> settings["Arithmetic"]|>,
        MemberQ[outcomes, "Undecidable"], makeFailure["UndecidableCovariance", "A coefficient equality required for covariance could not be proved.",
            <|"Generator" -> First[FirstPosition[outcomes, "Undecidable"]]|>],
        True, <|"Covariant" -> True, "Generator" -> None, "Checked" -> generators, "Arithmetic" -> settings["Arithmetic"]|>]
];

(*
    Summary: The arithmetic settings of a model.
    Parameters: model — model data.
    Options/defaults: None.
    Returns: arithmeticSettings association.
    Effects: Pure.
    Failures: None.
    Example: modelSettings[m]["Arithmetic"] is "Exact" by default.
    See also: CreateModel.
*)
modelSettings[model_Association] := If[model["Arithmetic"] === "Exact", arithmeticSettings["Exact", 50, Automatic, Infinity],
    arithmeticSettings["Numerical", model["Precision"], model["Tolerance"], model["Precision"]]];

(*
    Summary: Build a new model's data.
    Parameters: context — RepresentationContext; fields — validated field data; effective — validated options.
    Options/defaults: Name "Model"; TargetIrrep Automatic (the recorded trivial irrep) or a degree-one irrep ID; Arithmetic,
        WorkingPrecision, Tolerance.
    Returns: Model data association, or Failure.
    Effects: Allocates a model ID.
    Failures: ContextMismatch (a field from another frozen context); DuplicateField (repeated field ID or name);
        InvalidTarget (unknown or higher-dimensional target); MissingRepresentations (target without accepted matrices).
        NumericalInput (representation matrices with fewer than 16 digits).
    Example: makeModelData[ctx, {l, r}, opts]["Terms"] is {}.
    See also: CreateModel.
*)
makeModelData[context_RepresentationContext, fields_List, effective_Association] := Module[{snapshot = First[context], target, variant, precision, settings},
    If[AnyTrue[fields, #["ContextDigest"] =!= contextDigest[snapshot] &],
        Return[makeFailure["ContextMismatch", "Every field must belong to the model's frozen context (same group, generators and bases)."]]];
    If[!DuplicateFreeQ[Lookup[fields, "ID", {}]] || !DuplicateFreeQ[Lookup[fields, "Name", {}]],
        Return[makeFailure["DuplicateField", "Field IDs and names must be unique in a model; repeat a field in a contraction instead."]]];
    target = If[effective[TargetIrrep] === Automatic, snapshot["CharacterData"]["TrivialIrrepID"], effective[TargetIrrep]];
    If[!MemberQ[snapshot["CharacterData"]["IrrepIDs"], target] ||
            snapshot["CharacterData"]["Degrees"][[First[FirstPosition[snapshot["CharacterData"]["IrrepIDs"], target]]]] =!= 1,
        Return[makeFailure["InvalidTarget", "The model target must be an irrep of degree one.", <|"TargetIrrep" -> target|>]]];
    variant = cgVariant[snapshot, target];
    If[MissingQ[variant], Return[makeFailure["MissingRepresentations", "The target irrep has no accepted matrices; compute them and take a new context.",
        <|"IrrepIDs" -> {target}|>]]];
    (* Numerical-tier field or target variants make the model numerical at the precision they support (review M25,
       plan line 104): no exact certificate is ever issued from approximate transformation matrices. *)
    precision = modelDataPrecision[<|"Fields" -> fields, "TargetRep" -> variant["Rep"]|>];
    If[NumericQ[precision] && precision =!= MachinePrecision && precision < 16,
        Return[makeFailure["NumericalInput", "The fields' representation matrices carry fewer than 16 digits.", <|"Precision" -> precision|>]]];
    settings = If[effective[Arithmetic] === "Exact" && precision === Infinity, <|"Arithmetic" -> "Exact", "Precision" -> effective[WorkingPrecision]|>,
        checkedTolerance[arithmeticSettings["Numerical", effective[WorkingPrecision], effective[Tolerance], precision], precision =!= Infinity]];
    If[FailureQ[settings], Return[settings]];
    <|"SchemaVersion" -> 1, "ID" -> "model-" <> CreateUUID[], "Name" -> effective[Name], "Context" -> context,
        "ContextDigest" -> contextDigest[snapshot], "Fields" -> fields, "TargetIrrepID" -> target, "TargetRep" -> variant["Rep"],
        "TargetBasisID" -> variant["Identity"], "Terms" -> {}, "Parameters" -> {}, "Arithmetic" -> settings["Arithmetic"],
        "Precision" -> settings["Precision"], "Tolerance" -> effective[Tolerance],
        "Validation" -> <|"Status" -> "Covariant", "Arithmetic" -> settings["Arithmetic"],
            (* the inputs' status: group, field and target variants, arithmetic (methodOptionsPlan.md 2C.2) *)
            "VerificationStatus" -> modelInputsStatus[snapshot, Lookup[fields, "IrrepID", {}], target, settings["Arithmetic"]]|>|>
];

(* The status of a model's inputs: the group, the field and target variants of its context, its arithmetic. *)
modelInputsStatus[snapshot_, irreps_List, target_, arithmetic_] := cgWeakestStatus[Join[{groupVerificationStatus[snapshot],
        variantVerificationStatus[cgVariant[snapshot, target]], If[arithmetic === "Numerical", "Numerical", "Exact"]},
    variantVerificationStatus[cgVariant[snapshot, #]] & /@ irreps]];

(* The verification status of a model: stored in its Validation, else by its covariance status (models made before
   statuses existed). *)
modelVerificationStatus[model_Association] := Lookup[Lookup[model, "Validation", <||>], "VerificationStatus",
    Switch[Lookup[Lookup[model, "Validation", <||>], "Status", "Covariant"], "Covariant", "Exact", "Covariant (numerical)", "Numerical", _, "Unverified"]];
(* The status a term carries once its covariance is checked: a CoupleExpressions term (Symmetry "Unverified" before the
   check, status "Unverified" only for that reason) takes the check's level; a term added unchecked (Symmetry
   "Unchecked", Verification -> None) takes the check's level bounded by the status it had before (its "InputStatus":
   its channels', never raised by a covariance check); a contraction term keeps its channels' status. *)
checkedTermStatus[term_Association, numerical_] := cgWeakestStatus[{Switch[Lookup[term, "Symmetry", None],
        "Unverified", "Exact", "Unchecked", Lookup[term, "InputStatus", "Unverified"], _, Lookup[term, "VerificationStatus", "Exact"]],
    If[TrueQ[numerical], "Numerical", "Exact"]}];

(*
    Summary: Validate a model's schema and its fields before use.
    Parameters: m — any expression.
    Options/defaults: None.
    Returns: The model data, or InvalidModel/field/context Failure.
    Effects: Pure.
    Failures: Missing fields, fields that fail validateField, a target that is not the context's degree-one variant, terms
        that fail validateCoupledExpression, repeated term IDs, or parameter records that differ from the ordered merge of
        the terms' parameters.
    Example: a Model whose Terms were replaced by hand fails here when a term is malformed.
    Remarks: Shape only; ValidateModel recomputes covariance (a self-reported status is never evidence). The target
        basis identity must be the context variant's. A value validated before in this kernel is recognized by its
        hash and only its context binding is checked again.
    See also: ValidateModel.
*)
validateModelSchema[Model[data_Association]] := Module[{fields, snapshot, variant, key},
    If[!SubsetQ[Keys[data], {"SchemaVersion", "ID", "Name", "Context", "ContextDigest", "Fields", "TargetIrrepID", "TargetRep", "TargetBasisID",
            "Terms", "Parameters", "Arithmetic", "Precision", "Tolerance", "Validation"}] || data["SchemaVersion"] =!= 1,
        Return[makeFailure["InvalidModel", "Malformed Model."]]];
    (* A model value already validated in this kernel only needs its context binding again (review M13). *)
    key = Hash[data, "SHA256"];
    If[KeyExistsQ[$ModelSchemaMemo, key], Return[With[{bound = resolveRepContext[data["Context"]]}, If[FailureQ[bound], bound, data]]]];
    fields = validateField[Field[#]] & /@ data["Fields"];
    If[AnyTrue[fields, FailureQ], Return[FirstCase[fields, _Failure]]];
    snapshot = resolveRepContext[data["Context"]];
    If[FailureQ[snapshot], Return[snapshot]];
    variant = cgVariant[snapshot, data["TargetIrrepID"]];
    If[contextDigest[snapshot] =!= data["ContextDigest"] || MissingQ[variant] || variant["Rep"] =!= data["TargetRep"] ||
            variant["Identity"] =!= data["TargetBasisID"] ||
            !AllTrue[data["Terms"], AssociationQ[validateCoupledExpression[CoupledExpression[#]]] &] ||
            !DuplicateFreeQ[Lookup[data["Terms"], "TermID", {}]] || !StringQ[data["Name"]] || !MemberQ[{"Exact", "Numerical"}, data["Arithmetic"]] ||
            (data["Arithmetic"] === "Exact" && modelDataPrecision[data] =!= Infinity) ||
            mergeParameterRecords[Lookup[data["Terms"], "Parameters", {}]] =!= data["Parameters"],
        Return[makeFailure["InvalidModel", "The model's target, context, terms or parameter records are inconsistent."]]];
    (* A modular model's weights, namespace and registered slots are checked too (Stage 8). *)
    If[KeyExistsQ[data, "ModularData"], With[{modular = validateModularModelData[data]}, If[FailureQ[modular], Return[modular]]]];
    If[Length[$ModelSchemaMemo] >= 1024, $ModelSchemaMemo = <||>];
    AssociateTo[$ModelSchemaMemo, key -> True];
    data
];
validateModelSchema[___] := makeFailure["InvalidModel", "Expected a Model."];
(* Bounded kernel-local memo of validated model data (by hash); pure recomputable data. *)
If[!AssociationQ[$ModelSchemaMemo], $ModelSchemaMemo = <||>];

(*
    Summary: A new model with one more validated term.
    Parameters: model — validated model data; term — validated CoupledExpression data; level — Verification of the
        covariance check (default Automatic: the arithmetic; "Exact": InapplicableOption when numerical; "Numerical": the
        numerical view; None: not checked, the term's Symmetry reads "Unchecked" and the model's Status "Unverified").
    Options/defaults: None.
    Returns: New model data, or Failure.
    Effects: Pure (the input model is unchanged).
    Failures: DuplicateTerm (the TermID is already in the model); ContextMismatch / TargetMismatch (a term built for
        another context or target); UnknownField (recorded field IDs outside the model); parameter conflicts (mergeParameterRecords); covariance failures (NotCovariant,
        UndecidableCovariance) and domain failures of the term's expression.
    Example: addTermData[m, t]["Terms"] ends with t.
    Remarks: A term whose arithmetic is numerical makes the model's status Numerical; exact terms keep their exact
        certificate but the whole model then has no exact certificate.
    See also: AddModelTerm; validatePolynomialCovariance.
*)
addTermData[model_Association, term_Association, level_ : Automatic] := Module[{covariance, parameters, numerical, symmetry, status},
    If[MemberQ[Lookup[model["Terms"], "TermID", {}], term["TermID"]],
        Return[makeFailure["DuplicateTerm", "The term is already in the model; construct a separate term to add it again.", <|"TermID" -> term["TermID"]|>]]];
    If[StringQ[term["ContextDigest"]] && term["ContextDigest"] =!= model["ContextDigest"],
        Return[makeFailure["ContextMismatch", "The term was built in another frozen context."]]];
    If[StringQ[term["TargetIrrepID"]] && term["TargetIrrepID"] =!= model["TargetIrrepID"],
        Return[makeFailure["TargetMismatch", "The term was built for another target irrep."]]];
    If[ListQ[term["FieldIDs"]] && !SubsetQ[Lookup[model["Fields"], "ID", {}], term["FieldIDs"]],
        Return[makeFailure["UnknownField", "The term uses fields that are not registered in the model.",
            <|"Unknown" -> Complement[term["FieldIDs"], Lookup[model["Fields"], "ID", {}]]|>]]];
    parameters = mergeParameterRecords[{model["Parameters"], term["Parameters"]}];
    If[FailureQ[parameters], Return[parameters]];
    numerical = model["Arithmetic"] === "Numerical" || term["Arithmetic"] === "Numerical";
    If[level === "Exact" && numerical, Return[makeFailure["InapplicableOption",
        "Verification -> \"Exact\" cannot prove the covariance of a numerical term or model; use Automatic, \"Numerical\" or None.", <|"Options" -> {Verification}|>]]];
    (* the covariance check at the call's Verification level (methodOptionsPlan.md 2C.4); None adds the term unchecked *)
    If[level =!= None,
        covariance = validatePolynomialCovariance[If[numerical || level === "Numerical", numericalModelView[model, {term}], model], term["Value"]];
        If[FailureQ[covariance], Return[covariance]];
        If[!covariance["Covariant"], Return[makeFailure["NotCovariant", "The term does not transform with the model's target character.",
            <|"Generator" -> covariance["Generator"], "TermID" -> term["TermID"]|>]]]];
    symmetry = Which[level === None, "Unchecked", numerical || level === "Numerical", "Covariant (numerical)", True, "Covariant"];
    status = If[level === None, "Unverified", checkedTermStatus[term, numerical || level === "Numerical"]];
    Join[model, <|"Terms" -> Append[model["Terms"], Join[term, <|"Symmetry" -> symmetry, "VerificationStatus" -> status|>,
            (* an unchecked term remembers the status of its sources, which a later covariance check cannot raise *)
            If[level === None, <|"InputStatus" -> Switch[Lookup[term, "Symmetry", None], "Unverified", "Exact",
                "Unchecked", Lookup[term, "InputStatus", "Unverified"], _, Lookup[term, "VerificationStatus", "Exact"]]|>, <||>]]],
        "Parameters" -> parameters,
        "Validation" -> <|"Status" -> Which[symmetry === "Unchecked" || model["Validation"]["Status"] === "Unverified", "Unverified",
                symmetry === "Covariant (numerical)" || model["Validation"]["Status"] === "Covariant (numerical)", "Covariant (numerical)", True, "Covariant"],
            "Arithmetic" -> If[numerical, "Numerical", model["Arithmetic"]],
            "VerificationStatus" -> cgWeakestStatus[{modelVerificationStatus[model], status}]|>|>]
];

(*
    Summary: The numerical view of a model used to check numerical terms.
    Parameters: model — model data; terms — the terms being checked (data associations).
    Options/defaults: None.
    Returns: The model data with Arithmetic "Numerical", the lowest finite declared precision (50 when none is declared)
        and the loosest declared numerical tolerance (Automatic when none is declared).
    Effects: Pure.
    Failures: None.
    Example: an exact model with a term declared at WorkingPrecision 30, Tolerance 10^-20 is checked at 30 digits with
        tolerance 10^-20.
    Remarks: Residuals are judged by the tolerances the numerical data were declared with, never by the exact model's
        defaults; the result is a numerical status only.
    See also: addTermData; ValidateModel.
*)
numericalModelView[model_Association, terms_List] := Module[{numerical = Select[terms, #["Arithmetic"] === "Numerical" &], precisions, tolerances},
    (* The representation data bound the view's precision too (review M25). *)
    precisions = Select[Join[{model["Precision"], modelDataPrecision[model]}, Lookup[numerical, "Precision", {}]], NumericQ[#] && # < Infinity &];
    tolerances = Select[Join[If[model["Arithmetic"] === "Numerical", {model["Tolerance"]}, {}], Lookup[numerical, "Tolerance", {}]], NumericQ];
    (* A tolerance declared for more digits than the view has does not survive it (review M30): when the view's precision
       is below a declared precision, or is bounded by the fields' data, the automatic tolerance at the view's precision
       is a floor. *)
    With[{precision = If[precisions === {}, 50, Min[precisions]],
            declared = Select[Join[If[model["Arithmetic"] === "Numerical", {model["Precision"]}, {}], Lookup[numerical, "Precision", {}]], NumericQ[#] && # < Infinity &]},
        Join[model, <|"Arithmetic" -> "Numerical", "Precision" -> precision,
            "Tolerance" -> Which[
                tolerances === {}, Automatic,
                modelDataPrecision[model] =!= Infinity || AnyTrue[declared, N[#] > N[precision] &], Max[Append[tolerances, automaticTolerance[precision]]],
                True, Max[tolerances]]|>]]
];

Options[CreateModel] = {Name -> "Model", TargetIrrep -> Automatic, Arithmetic -> "Exact", WorkingPrecision -> 50, Tolerance -> Automatic};

(*
    Summary: An empty model of fields over a group or frozen context.
    Parameters: c — Group or RepresentationContext; fields — list of Field values (may be empty).
    Options/defaults: Name "Model"; TargetIrrep Automatic (trivial) or an explicit degree-one irrep ID; Arithmetic "Exact",
        WorkingPrecision, Tolerance.
    Returns: Model with expression zero, or Failure.
    Effects: Freezing a group registers its context.
    Failures: Option failures; ContextMismatch; DuplicateField; InvalidTarget; MissingRepresentations; InvalidField.
    Example: ModelExpression[CreateModel[g, {l, r}]] is 0.
    Remarks: With a Group, the model takes the fields' frozen context when the group only advanced its state
        generation since (modelContextForGroup); a changed basis or assignment is a ContextMismatch.
        Fields or a target over numerical-tier variants make the model numerical at the precision of their matrices
        (makeModelData, review M25).
    See also: AddModelTerm; Contractions; ModelExpression.
*)
CreateModel[c : (_Group | _RepresentationContext), fields_List, options : OptionsPattern[]] := Module[{effective, context, data},
    effective = resolveOperationOptions[CreateModel, "CreateModel", {options}];
    If[FailureQ[effective], Return[effective]];
    effective = resolveIrrepOptions[c, effective]; If[FailureQ[effective], Return[effective]];
    data = validateField /@ fields;
    If[AnyTrue[data, FailureQ], Return[FirstCase[data, _Failure]]];
    context = If[Head[c] === Group, modelContextForGroup[c, data, effective[TargetIrrep]], vectorContext[c]];
    If[FailureQ[context], Return[context]];
    With[{model = makeModelData[context, data, effective]}, If[FailureQ[model], model, Model[model]]]
];

(*
    Summary: The frozen context of a model created from a live group and fields.
    Parameters: group — live Group; fields — validated field data; target — TargetIrrep option value.
    Options/defaults: None.
    Returns: The group's current context, or the fields' own context when the group's state generation advanced
        without a mathematical change (review M14); or Failure.
    Effects: Freezing the group registers its context binding.
    Failures: UnverifiedContext; ContextMismatch when the fields' context is a different representation state of the
        group (a changed basis, variant or modular assignment), naming the remedy.
    Example: after a native GAP CG route advanced g's StateGeneration, CreateModel[g, {l, r}] uses l's context.
    Remarks: A native GAP route runs a worker query on the live group, which advances its StateGeneration (part of the
        context digest) without changing characters, assignment or representations. The fields' context is used when
        the group identity, generator identity, character data, assignment identity and the active variant identity of
        every field irrep and of the target are unchanged; a value built in one context is never mixed with another.
    See also: CreateModel; staleBasisFailure.
*)
modelContextForGroup[group_Group, fields_List, target_] := Module[{current = freezeContext[group], digests, then, now, irreps, sameQ},
    If[FailureQ[current] || fields === {}, Return[current]];
    digests = DeleteDuplicates[Lookup[fields, "ContextDigest", {}]];
    If[digests === {contextDigest[First[current]]}, Return[current]];
    If[Length[digests] > 1, Return[makeFailure["ContextMismatch", "The fields were created in different frozen contexts (different representation states of the group, or different groups); create them in one context, or build the model in one field context with CreateModel[RepresentationContext of the fields, ...]."]]];
    then = resolveRepContext[First[fields]["Context"]]; If[FailureQ[then], Return[then]];
    now = First[current];
    irreps = DeleteDuplicates[Append[Lookup[fields, "IrrepID", {}], If[target === Automatic, now["CharacterData"]["TrivialIrrepID"], target]]];
    sameQ = then["GroupIdentity"] === now["GroupIdentity"] && then["GeneratorIdentity"] === now["GeneratorIdentity"] &&
        then["CharacterData"] === now["CharacterData"] &&
        Lookup[Replace[then["ModularAssignment"], Except[_Association] -> <||>], "Identity", None] ===
            Lookup[Replace[now["ModularAssignment"], Except[_Association] -> <||>], "Identity", None] &&
        AllTrue[irreps, Lookup[Replace[cgVariant[then, #], _Missing -> <||>], "Identity", None] === Lookup[Replace[cgVariant[now, #], _Missing -> <||>], "Identity", None] &];
    If[then["GroupIdentity"] =!= now["GroupIdentity"],
        Return[makeFailure["ContextMismatch", "The fields were created for a different group; create fields of this group, or build the model over the fields' own group or context."]]];
    If[sameQ, First[fields]["Context"],
        makeFailure["ContextMismatch", "The fields were created in an earlier representation state of this group (a basis, variant or modular assignment changed since). Create new fields in the current state, or build the model in the fields' context with CreateModel[RepresentationContext of the fields, ...].",
            <|"IrrepIDs" -> Select[irreps, Lookup[Replace[cgVariant[then, #], _Missing -> <||>], "Identity", None] =!= Lookup[Replace[cgVariant[now, #], _Missing -> <||>], "Identity", None] &]|>]]
];
CreateModel[___] := makeFailure["InvalidInput", "CreateModel expects a Group or RepresentationContext, a list of fields and options."];

(*
    Summary: A new model with a covariant term added.
    Parameters: m — Model; term — CoupledExpression.
    Options/defaults: Verification -> Automatic (the covariance in the model arithmetic), "Exact" (InapplicableOption for
        numerical data), "Numerical" (checked in the numerical view) or None (added unchecked: the term's Symmetry reads
        "Unchecked", the model's Validation Status and both statuses "Unverified"; ValidateModel checks it later, bounded by
        the term's sources).
    Returns: New Model, or Failure (the input model is unchanged either way).
    Effects: Pure.
    Failures: InvalidModel; InvalidCoupledExpression; DuplicateTerm; ContextMismatch; TargetMismatch; UnknownComponent;
        UndeclaredSymbol; NonPolynomial; NotCovariant; UndecidableCovariance; ParameterConflict.
    Example: ModelParameters[AddModelTerm[m, CoupleContractions[Contractions[m, {l, r}]]]] has one coupling.
    See also: CoupleContractions; CoupleExpressions; ValidateModel.
*)
Options[AddModelTerm] = {Verification -> Automatic};
AddModelTerm[m_Model, term_CoupledExpression, options : OptionsPattern[]] := Module[{model = validateModelSchema[m], data, result, effective},
    If[FailureQ[model], Return[model]];
    effective = resolveOperationOptions[AddModelTerm, "AddModelTerm", {options}]; If[FailureQ[effective], Return[effective]];
    data = validateCoupledExpression[term]; If[FailureQ[data], Return[data]];
    (* A modular model registers the term's slots and checks the total weight too (Stage 8). *)
    result = If[KeyExistsQ[model, "ModularData"], addModularTermData[model, data, effective[Verification]], addTermData[model, data, effective[Verification]]];
    If[FailureQ[result], result, Model[result]]
];
AddModelTerm[___] := makeFailure["InvalidInput", "AddModelTerm expects a Model, a CoupledExpression and options."];

(*
    Summary: The scalar expression of a model: the exact sum of its terms.
    Parameters: m — Model.
    Options/defaults: None.
    Returns: Expression in field components and inert Coupling atoms (0 for no terms), or Failure.
    Effects: Pure.
    Failures: InvalidModel.
    Example: ModelExpression[CreateModel[g, {}]] is 0.
    Remarks: No overall scale is removed.
    See also: ModelParameters; ExtractBilinearMatrix.
*)
ModelExpression[m_Model] := With[{model = validateModelSchema[m]}, If[FailureQ[model], model, Total[Lookup[model["Terms"], "Value", {}]]]];
ModelExpression[___] := makeFailure["InvalidInput", "ModelExpression expects a Model."];

(*
    Summary: The parameter records of a model in first-appearance order.
    Parameters: m — Model.
    Options/defaults: None.
    Returns: List of <|"Atom" -> Coupling[ID], "ID", "Label", "Domain", "SourceAtom"|>, or Failure.
    Effects: Pure.
    Failures: InvalidModel.
    Example: Length[ModelParameters[model2]] is 1 for the A4 bilinear example.
    See also: ModelExpression; CouplingParameters.
*)
ModelParameters[m_Model] := With[{model = validateModelSchema[m]}, If[FailureQ[model], model, model["Parameters"]]];
ModelParameters[___] := makeFailure["InvalidInput", "ModelParameters expects a Model."];

(*
    Summary: Recompute the covariance of a model and of each of its terms.
    Parameters: m — Model.
    Options/defaults: The model's arithmetic; Verification -> Automatic (the model's arithmetic), "Exact" (exact checks;
        InapplicableOption for a numerical model) or "Numerical" (every check in the numerical view); None is InvalidOption.
    Returns: <|"ModelID", "Covariant" -> Boolean, "Status" -> "Covariant" | "Covariant (numerical)" | "NotCovariant",
        "Terms" -> TermID -> covariance report, "Generators" -> number checked, "Precision", "Tolerance" (the whole-model
        settings; Missing["Exact"] for an exact model)|>, or Failure.
    Effects: Pure.
    Failures: InvalidModel; UndecidableCovariance.
    Example: ValidateModel[model2]["Covariant"] is True.
    Remarks: Nothing stored in the model is trusted. Exact terms of an exact model are checked exactly (their reports
        say "Arithmetic" -> "Exact"); numerical terms and, when any term is numerical, the whole sum are checked with
        the declared numerical tolerances and give a numerical status, never an exact certificate.
    See also: AddModelTerm; validatePolynomialCovariance.
*)
Options[ValidateModel] = {Verification -> Automatic};
ValidateModel[m_Model, options : OptionsPattern[]] := Module[{model = validateModelSchema[m], effective, level, numerical, settingsModel, terms, whole, allowed},
    If[FailureQ[model], Return[model]];
    effective = resolveOperationOptions[ValidateModel, "ValidateModel", {options}]; If[FailureQ[effective], Return[effective]];
    level = effective[Verification];
    numerical = model["Arithmetic"] === "Numerical" || MemberQ[Lookup[model["Terms"], "Arithmetic", {}], "Numerical"];
    allowed = checkLevelQ["ValidateModel", level, numerical]; If[FailureQ[allowed], Return[allowed]];
    numerical = numerical || level === "Numerical";
    settingsModel = If[numerical, numericalModelView[model, model["Terms"]], model];
    (* Each term is checked in its own arithmetic: exact terms keep exact checks; the whole sum uses the numerical view. *)
    terms = AssociationMap[Function[t, validatePolynomialCovariance[
        If[model["Arithmetic"] === "Numerical" || t["Arithmetic"] === "Numerical" || level === "Numerical", numericalModelView[model, {t}], model], t["Value"]]], model["Terms"]];
    terms = KeyMap[#["TermID"] &, terms];
    If[AnyTrue[terms, FailureQ], Return[FirstCase[Values[terms], _Failure]]];
    whole = validatePolynomialCovariance[settingsModel, Total[Lookup[model["Terms"], "Value", {}]]];
    If[FailureQ[whole], Return[whole]];
    Join[<|"ModelID" -> model["ID"], "Covariant" -> whole["Covariant"] && AllTrue[terms, #["Covariant"] &],
        "Status" -> Which[!whole["Covariant"], "NotCovariant", numerical, "Covariant (numerical)", True, "Covariant"],
        "Terms" -> terms, "Generators" -> whole["Checked"],
        (* the status the checks establish, bounded by the inputs and the terms' sources (methodOptionsPlan.md 2C.2) *)
        "VerificationStatus" -> cgWeakestStatus[Join[{modelInputsStatus[First[model["Context"]], Lookup[model["Fields"], "IrrepID", {}],
                model["TargetIrrepID"], model["Arithmetic"]], If[numerical, "Numerical", "Exact"],
                (* slots of a space the user supplied (SupplyModularFormSpace) are the user's assertion *)
                If[KeyExistsQ[model, "ModularData"], suppliedSlotsStatus[model], "Exact"]},
            checkedTermStatus[#, numerical || #["Arithmetic"] === "Numerical"] & /@ model["Terms"]]],
        "Precision" -> modelSettings[settingsModel]["Precision"], "Tolerance" -> Replace[modelSettings[settingsModel]["Tolerance"], None -> Missing["Exact"]]|>,
        (* Modular models (Stage 8): the formal checks above include the slots; the total weight of every monomial and the
           binding status are reported separately (formal covariance never implies analytic evidence). *)
        If[KeyExistsQ[model, "ModularData"], <|"ModularWeight" -> With[{v = monomialWeightViolations[Total[Lookup[model["Terms"], "Value", {}]], model,
                model["ModularData"]["SuperpotentialWeight"]]}, If[v === {}, "Homogeneous", <|"Status" -> "Inhomogeneous", "Violations" -> Take[v, UpTo[3]]|>]],
            "SuperpotentialWeight" -> model["ModularData"]["SuperpotentialWeight"], "BindingStatus" -> bindingStatus[model]|>, <||>]]
];
ValidateModel[___] := makeFailure["InvalidInput", "ValidateModel expects a Model and options."];

Format[Model[data_Association], StandardForm] := Interpretation[Row[{"Model[", Lookup[data, "Name", "?"], ", ", Length[Lookup[data, "Fields", {}]],
    " fields, ", Length[Lookup[data, "Terms", {}]], " terms]"}], Model[data]];

True
