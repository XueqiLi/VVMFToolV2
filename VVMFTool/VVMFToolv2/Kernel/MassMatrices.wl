(*
    :Title: Coefficient (mass) matrices
    :Context: VVMFTool`Private`
    :Summary: Bilinear and quadratic coefficient matrices of scalar polynomials with explicit row/column variables, the
        retained remainder, both quadratic conventions, and model-aware validation (source model, closed multiplets,
        reconstruction and P^T M' Q = chi M covariance with transformed spectators).
    :Responsibilities: resolveMatrixVariables, extractBilinearData, extractQuadraticData, validateMassMatrixData,
        listTransformation, validateMatrixCovariance; MassMatrix, ExtractBilinearMatrix, ExtractQuadraticMatrix, MatrixValues,
        ValidateMassMatrix.
    :Dependencies: Models.wl (validateModelSchema, zeroCoefficientQ, modelSettings); Fields.wl (validateField).
    :See Also: VVMFArch/step5Plan.md (mass-matrix conventions).
*)

(*
    Summary: Fresh local variables for the row/column atoms.
    Parameters: rows, cols — variable lists (cols may be None for quadratic extraction).
    Options/defaults: None.
    Returns: <|"Rows" -> fresh, "Columns" -> fresh or None, "Forward" -> rules atom -> fresh, "Backward" -> rules fresh -> atom|>,
        or Failure.
    Effects: Pure: the fresh variables are indexed private atoms matrixExtractionVariable[k] (no symbol is created); no
        global variable is evaluated or changed.
    Failures: InvalidVariables (empty, duplicate, numeric or overlapping lists).
    Example: resolveMatrixVariables[{x1, x2}, {y1}]["Rows"] has two fresh symbols.
    See also: extractBilinearData; extractQuadraticData.
*)
resolveMatrixVariables[rows_List, cols_] := Module[{all = Join[rows, If[cols === None, {}, cols]], fresh},
    If[rows === {} || (cols =!= None && cols === {}) || !DuplicateFreeQ[rows] || (cols =!= None && (!DuplicateFreeQ[cols] || IntersectingQ[rows, cols])) ||
            AnyTrue[all, NumericQ[#] || MatchQ[#, _List] &],
        Return[makeFailure["InvalidVariables", "Rows and columns must be nonempty lists of distinct non-numeric variables, and disjoint for bilinear extraction."]]];
    fresh = Array[matrixExtractionVariable, Length[all]];
    <|"Rows" -> fresh[[;; Length[rows]]], "Columns" -> If[cols === None, None, fresh[[Length[rows] + 1 ;;]]],
        "Forward" -> Thread[all -> fresh], "Backward" -> Thread[fresh -> all]|>
];

(*
    Summary: Whether a residual expression vanishes in the declared arithmetic.
    Parameters: expr — residual (polynomial in field components, parameters and functions of parameters); settings —
        <|"Arithmetic", "Tolerance", ...|>.
    Options/defaults: None.
    Returns: Boolean.
    Effects: Pure.
    Failures: None.
    Example: residualZeroQ[0.5 x y - 0.5 x y, numerical] is True; residualZeroQ[10^-30 x, exact] is False.
    Remarks: Exact arithmetic needs an exact zero after Expand. Numerical arithmetic needs every coefficient (over all
        variables of the residual) to be numeric with magnitude at most the declared tolerance (review M5).
    See also: validateMassMatrixData; ValidateMassMatrix.
*)
residualZeroQ[expr_, settings_Association] := Module[{e = Expand[expr], variables, coefficients},
    If[e === 0, Return[True]];
    If[settings["Arithmetic"] =!= "Numerical", Return[False]];
    variables = Variables[e];
    coefficients = If[variables === {}, {e}, Values[CoefficientRules[e, variables]]];
    AllTrue[coefficients, NumericQ[#] && Abs[N[#]] <= settings["Tolerance"] &]
];

(*
    Summary: The arithmetic settings of an extraction from its options and its input expression.
    Parameters: expr — input expression; effective — validated extraction options.
    Options/defaults: Arithmetic "Exact" (default) or "Numerical", WorkingPrecision, Tolerance.
    Returns: arithmeticSettings association, or NumericalInput Failure (approximate input under exact arithmetic).
    Effects: Pure.
    Failures: NumericalInput.
    Example: extractionSettings[0.5 x y, <|Arithmetic -> "Exact", ...|>] fails NumericalInput.
    Remarks: An extraction takes an expression, not a model, so it cannot inherit a model's arithmetic: numerical input
        needs Arithmetic -> "Numerical" explicitly (plan line 102).
    See also: ExtractBilinearMatrix; ExtractQuadraticMatrix.
*)
extractionSettings[expr_, effective_Association] := arithmeticSettings[effective[Arithmetic], effective[WorkingPrecision], effective[Tolerance],
    dataPrecision[expr]];

(*
    Summary: The degree-(1,1) part of an expression in row and column variables as a matrix.
    Parameters: expr — scalar expression; rows, cols — variables; requirePure — Boolean.
    Options/defaults: None.
    Returns: <|"Kind" -> "Bilinear", "Matrix", "Selected", "Remainder", "Rows", "Columns", "Convention" -> "Bilinear"|>, or Failure.
    Effects: Pure.
    Failures: InvalidOption (RequirePure not a Boolean); InvalidVariables; NonPolynomial (non-polynomial dependence on a row or column variable); ImpureSector
        (requirePure with a nonzero remainder).
    Example: extractBilinearData[a x1 y1 + b x2 y1 + z, {x1, x2}, {y1}, False]["Matrix"] is {{a}, {b}} with remainder z.
    Remarks: selected == rows . M . cols exactly; other variables stay in the entries (spectators).
    See also: ExtractBilinearMatrix.
*)
extractBilinearData[expr_, rows_List, cols_List, requirePure_, settings_Association : <|"Arithmetic" -> "Exact"|>] := Module[{vars, e, rules, selected, matrix, remainder},
    If[!BooleanQ[requirePure], Return[makeFailure["InvalidOption", "RequirePure must be True or False."]]];
    vars = resolveMatrixVariables[rows, cols]; If[FailureQ[vars], Return[vars]];
    e = Expand[expr /. vars["Forward"]];
    If[!PolynomialQ[e, Join[vars["Rows"], vars["Columns"]]],
        Return[makeFailure["NonPolynomial", "The expression is not polynomial in the row and column variables."]]];
    rules = CoefficientRules[e, Join[vars["Rows"], vars["Columns"]]];
    rules = Select[rules, Total[First[#][[;; Length[rows]]]] === 1 && Total[First[#][[Length[rows] + 1 ;;]]] === 1 &];
    matrix = ConstantArray[0, {Length[rows], Length[cols]}];
    Scan[Function[r, matrix[[First[FirstPosition[First[r][[;; Length[rows]]], 1]], First[FirstPosition[First[r][[Length[rows] + 1 ;;]], 1]]]] += Last[r]], rules];
    selected = Expand[vars["Rows"] . matrix . vars["Columns"]];
    remainder = Expand[e - selected];
    If[TrueQ[requirePure] && !residualZeroQ[remainder, settings], Return[makeFailure["ImpureSector", "The expression has terms outside the bilinear sector (RequirePure -> True)."]]];
    <|"Kind" -> "Bilinear", "Matrix" -> (matrix /. vars["Backward"]), "Selected" -> (selected /. vars["Backward"]), "Remainder" -> (remainder /. vars["Backward"]),
        "Rows" -> rows, "Columns" -> cols, "Convention" -> "Bilinear"|>
];

(*
    Summary: The degree-2 part of an expression in the given variables as a symmetric matrix.
    Parameters: expr; vars; convention — "Polynomial" (selected == x . M . x) or "Half" (selected == (x . M . x)/2);
        requirePure.
    Options/defaults: None.
    Returns: <|"Kind" -> "Quadratic", "Matrix", "Selected", "Remainder", "Rows", "Columns" -> rows, "Convention"|>, or Failure.
    Effects: Pure.
    Failures: InvalidVariables; NonPolynomial; ImpureSector; InvalidOption (convention, or RequirePure not a Boolean).
    Example: a x1^2 + b x1 x2 + c x2^2 gives {{a, b/2}, {b/2, c}} (Polynomial) and twice that (Half).
    Remarks: Diagonal entries are the x_i^2 coefficients and off-diagonal ones half the x_i x_j coefficients
        (MakeMassMatrixSym's convention); no complex conjugation.
    See also: ExtractQuadraticMatrix.
*)
extractQuadraticData[expr_, vars_List, convention_, requirePure_, settings_Association : <|"Arithmetic" -> "Exact"|>] := Module[{fresh, e, rules, matrix, selected, remainder, n = Length[vars]},
    If[!MemberQ[{"Polynomial", "Half"}, convention], Return[makeFailure["InvalidOption", "QuadraticConvention must be \"Polynomial\" or \"Half\"."]]];
    If[!BooleanQ[requirePure], Return[makeFailure["InvalidOption", "RequirePure must be True or False."]]];
    fresh = resolveMatrixVariables[vars, None]; If[FailureQ[fresh], Return[fresh]];
    e = Expand[expr /. fresh["Forward"]];
    If[!PolynomialQ[e, fresh["Rows"]], Return[makeFailure["NonPolynomial", "The expression is not polynomial in the variables."]]];
    rules = Select[CoefficientRules[e, fresh["Rows"]], Total[First[#]] === 2 &];
    matrix = ConstantArray[0, {n, n}];
    Scan[Function[r, With[{positions = Flatten[Position[First[r], _?Positive, {1}]]},
            If[Length[positions] === 1, matrix[[positions[[1]], positions[[1]]]] += Last[r],
                matrix[[positions[[1]], positions[[2]]]] += Last[r]/2; matrix[[positions[[2]], positions[[1]]]] += Last[r]/2]]], rules];
    selected = Expand[fresh["Rows"] . matrix . fresh["Rows"]];
    remainder = Expand[e - selected];
    If[TrueQ[requirePure] && !residualZeroQ[remainder, settings], Return[makeFailure["ImpureSector", "The expression has terms outside the quadratic sector (RequirePure -> True)."]]];
    <|"Kind" -> "Quadratic", "Matrix" -> (If[convention === "Half", 2 matrix, matrix] /. fresh["Backward"]), "Selected" -> (selected /. fresh["Backward"]),
        "Remainder" -> (remainder /. fresh["Backward"]), "Rows" -> vars, "Columns" -> vars, "Convention" -> convention|>
];

(*
    Summary: Wrap extraction data as a MassMatrix with field, parameter and arithmetic identities.
    Parameters: expr — input expression; data — extraction data; fields — <|"Rows" -> field IDs or Missing, "Columns" -> ...,
        "FieldNames" -> <|ID -> name|>, "Context" -> frozen context or Missing|>; settings — extraction arithmetic settings.
    Options/defaults: None.
    Returns: MassMatrix, or UnknownCoupling Failure.
    Effects: Pure.
    Failures: UnknownCoupling (a Coupling atom of the matrix without a parameter record in this kernel).
    Example: MatrixValues of the result is data["Matrix"].
    Remarks: Parameters are the records of the matrix's couplings in first-appearance order (review M13); Arithmetic,
        Precision and Tolerance are the extraction's (review M5); FieldNames and Context are recorded for fields (D-S5-8).
    See also: ExtractBilinearMatrix.
*)
makeMassMatrix[expr_, data_Association, fields_Association, settings_Association : <|"Arithmetic" -> "Exact", "Precision" -> Infinity, "Tolerance" -> None|>] := Module[{atoms, records},
    atoms = DeleteDuplicates[Cases[data["Matrix"], Coupling[_String], {0, Infinity}]];
    records = Lookup[$CouplingRecords, First /@ atoms, Missing[]];
    If[MemberQ[records, _Missing], Return[makeFailure["UnknownCoupling", "A Coupling atom of the matrix has no parameter record in this kernel."]]];
    MassMatrix[Join[<|"SchemaVersion" -> 1, "InputExpression" -> expr, "Dimensions" -> Dimensions[data["Matrix"]], "Parameters" -> records,
        "RowFields" -> fields["Rows"], "ColumnFields" -> fields["Columns"], "FieldNames" -> Lookup[fields, "FieldNames", <||>],
        "Context" -> Lookup[fields, "Context", Missing["NotKnown"]], "Arithmetic" -> settings["Arithmetic"],
        "Precision" -> Lookup[settings, "Precision", Infinity], "Tolerance" -> Replace[Lookup[settings, "Tolerance", None], None -> Missing["Exact"]],
        (* the status of the fields' variants and the arithmetic (methodOptionsPlan.md 2C.2); the source model's status
           enters at ValidateMassMatrix *)
        "VerificationStatus" -> cgWeakestStatus[Join[{If[settings["Arithmetic"] === "Numerical", "Numerical", "Exact"]},
            If[MatchQ[Lookup[fields, "Context", Missing[]], _RepresentationContext],
                Join[{groupVerificationStatus[First[fields["Context"]]]},
                    variantVerificationStatus[cgVariant[First[fields["Context"]], #]] & /@ Lookup[fields, "IrrepIDs", {}]], {}]]]|>, data]]
];

(*
    Summary: Validate a MassMatrix's schema and reconstruction.
    Parameters: m — any expression.
    Options/defaults: None.
    Returns: The data, or InvalidMassMatrix Failure.
    Effects: Pure.
    Failures: Missing fields; shapes that disagree with the variables; a selected expression or remainder that does not
        reconstruct the input (rows . M . cols, or x . M . x with the convention factor), exactly or, for a numerical
        extraction, within its declared tolerance.
    Example: a MassMatrix whose Matrix was edited by hand fails here.
    See also: ValidateMassMatrix.
*)
validateMassMatrixData[MassMatrix[data_Association]] := Module[{factor},
    If[!SubsetQ[Keys[data], {"SchemaVersion", "Kind", "InputExpression", "Selected", "Remainder", "Matrix", "Rows", "Columns", "Convention"}] ||
            data["SchemaVersion"] =!= 1 || !MatrixQ[data["Matrix"]] || Dimensions[data["Matrix"]] =!= {Length[data["Rows"]], Length[data["Columns"]]} ||
            !AssociationQ[Lookup[data, "FieldNames", <||>]] || !MatchQ[Lookup[data, "Context", Missing[]], _Missing | _RepresentationContext] ||
            !MemberQ[{"Exact", "Numerical"}, Lookup[data, "Arithmetic", "Exact"]],
        Return[makeFailure["InvalidMassMatrix", "Malformed MassMatrix."]]];
    factor = If[data["Convention"] === "Half", 1/2, 1];
    If[!residualZeroQ[factor data["Rows"] . data["Matrix"] . data["Columns"] - data["Selected"], massSettings[data]] ||
            !residualZeroQ[data["Selected"] + data["Remainder"] - data["InputExpression"], massSettings[data]],
        Return[makeFailure["InvalidMassMatrix", "The matrix, selected sector and remainder do not reconstruct the input expression."]]];
    data
];

(*
    Summary: The arithmetic settings recorded in a MassMatrix.
    Parameters: data — MassMatrix data.
    Options/defaults: A matrix without recorded arithmetic is exact.
    Returns: <|"Arithmetic", "Tolerance"|>.
    Effects: Pure.
    Failures: None.
    Example: massSettings[data]["Arithmetic"] is "Exact" for an exact extraction.
    See also: residualZeroQ.
*)
massSettings[data_Association] := <|"Arithmetic" -> Lookup[data, "Arithmetic", "Exact"], "Tolerance" -> Replace[Lookup[data, "Tolerance", None], _Missing -> None]|>;
validateMassMatrixData[___] := makeFailure["InvalidMassMatrix", "Expected a MassMatrix."];

(*
    Summary: The transformation of an ordered variable list made of whole field multiplets under one generator.
    Parameters: list — component atoms; model — model data; i — generator index.
    Options/defaults: None.
    Returns: Matrix T with list -> T . list (block-diagonal in field order, permuted to the list order), or Failure.
    Effects: Pure.
    Failures: NonClosedFieldSelection (an unknown component, or a field whose components are not all present once).
    Example: for the concatenation of a doublet and a singlet T is block-diagonal 2 + 1.
    See also: validateMatrixCovariance.
*)
listTransformation[list_List, model_Association, i_Integer] := Module[{fields, byID, position},
    byID = AssociationThread[Lookup[model["Fields"], "ID", {}], model["Fields"]];
    If[!AllTrue[list, MatchQ[#, FieldComponent[_String, _Integer]] && KeyExistsQ[byID, First[#]] &],
        Return[makeFailure["NonClosedFieldSelection", "Every variable must be a component of a registered model field."]]];
    fields = DeleteDuplicates[First /@ list];
    If[!AllTrue[fields, Function[fid, Sort[Select[list, First[#] === fid &]] === Sort[byID[fid]["Components"]]]],
        Return[makeFailure["NonClosedFieldSelection", "The variables must contain whole field multiplets, each component once."]]];
    position = AssociationThread[list, Range[Length[list]]];
    Normal[SparseArray[Flatten[Table[With[{f = byID[First[list[[k]]]], a = Last[list[[k]]]},
        Table[{k, position[FieldComponent[f["ID"], b]]} -> repMatrices[f["Rep"]][[i, a, b]], {b, f["Dimension"]}]], {k, Length[list]}]],
        {Length[list], Length[list]}]]
];

(*
    Summary: Check P_i^T . M(transformed spectators) . Q_i == chi_target(i) M for every generator.
    Parameters: model — model data; data — validated mass data.
    Options/defaults: The model's arithmetic.
    Returns: <|"Covariant" -> Boolean, "Generator" -> first failing index or None|>, or Failure.
    Effects: Pure.
    Failures: NonClosedFieldSelection; UndecidableCovariance.
    Example: the A4 bilinear invariant's matrix passes with P = Q = the triplet matrices.
    Remarks: A transpose, not an adjoint: x . M . y with x -> P x, y -> Q y gives x . P^T M Q . y. Spectator components in M are
        transformed with every model field's matrices simultaneously; coefficients are taken over every model component
        and every generator is checked, so the verdict does not depend on which components occur or on generator order.
    See also: ValidateMassMatrix.
*)
validateMatrixCovariance[model_Association, data_Association] := Module[{settings = modelSettings[model], chi, components, outcomes},
    chi = repMatrices[model["TargetRep"]][[All, 1, 1]];
    (* Coefficients over every model component (review M2), every generator checked. *)
    components = modelComponents[model];
    outcomes = Table[Module[{p = listTransformation[data["Rows"], model, i], q = listTransformation[data["Columns"], model, i], rules, transformed, difference,
            coefficients, decided},
            If[FailureQ[p], Return[p, Module]]; If[FailureQ[q], Return[q, Module]];
            rules = modelGeneratorRules[model, i];
            transformed = data["Matrix"] /. rules;
            difference = Expand[Transpose[p] . transformed . q - chi[[i]] data["Matrix"]];
            (* Exact settings refuse inexact data before CoefficientRules drops approximate zeros (review M25). *)
            If[settings["Arithmetic"] === "Exact" && inexactDataQ[difference], Return["Undecidable", Module]];
            coefficients = Flatten[Map[If[components === {}, {#}, Values[CoefficientRules[#, components]] /. {} -> {0}] &, Flatten[difference]]];
            decided = zeroCoefficientQ[#, settings] & /@ coefficients;
            Which[MemberQ[decided, False], False, MemberQ[decided, "Undecidable"], "Undecidable", True, True]],
        {i, Length[chi]}];
    Which[
        AnyTrue[outcomes, FailureQ], FirstCase[outcomes, _Failure],
        MemberQ[outcomes, False], <|"Covariant" -> False, "Generator" -> First[FirstPosition[outcomes, False]]|>,
        MemberQ[outcomes, "Undecidable"], makeFailure["UndecidableCovariance", "A matrix covariance equality could not be proved.",
            <|"Generator" -> First[FirstPosition[outcomes, "Undecidable"]]|>],
        True, <|"Covariant" -> True, "Generator" -> None|>]
];

Options[ExtractBilinearMatrix] = {RequirePure -> False, Arithmetic -> "Exact", WorkingPrecision -> 50, Tolerance -> Automatic};

(*
    Summary: The bilinear coefficient matrix of an expression in row and column variables.
    Parameters: expr — scalar expression; rows, cols — variable lists, or left, right — Field values (their components).
    Options/defaults: RequirePure False (the remainder is kept) or True (fail unless the remainder is zero); Arithmetic
        "Exact" (default) or "Numerical" with WorkingPrecision and Tolerance.
    Returns: MassMatrix with selected == rows . M . cols and the remainder, or Failure.
    Effects: Pure.
    Failures: InvalidVariables; NonPolynomial; ImpureSector; InvalidOption; UnknownOption; InapplicableOption;
        NumericalInput (approximate coefficients with exact arithmetic); InvalidField; UnknownCoupling.
    Example: MatrixValues[ExtractBilinearMatrix[ModelExpression[m2], l, r]] is a 3 x 3 matrix for two A4 triplets.
    Remarks: The extraction takes an expression, not a model, so a numerical model's matrix needs Arithmetic ->
        "Numerical"; reconstruction and RequirePure are then judged within the tolerance. Fields record their names
        and frozen context in the matrix. The matrix's "VerificationStatus" covers the extraction arithmetic and, for
        fields, their variants and group; plain variable lists carry no context, so their status reflects the arithmetic
        only. The expression's source is not known here: ValidateMassMatrix against the source model gives the full status.
    See also: ExtractQuadraticMatrix; ValidateMassMatrix; MatrixValues.
*)
ExtractBilinearMatrix[expr_, left_Field, right_Field, options : OptionsPattern[]] := Module[{l = validateField[left], r = validateField[right], effective, settings, data},
    If[FailureQ[l], Return[l]]; If[FailureQ[r], Return[r]];
    effective = resolveOperationOptions[ExtractBilinearMatrix, "ExtractBilinearMatrix", {options}]; If[FailureQ[effective], Return[effective]];
    settings = extractionSettings[expr, effective]; If[FailureQ[settings], Return[settings]];
    data = extractBilinearData[expr, l["Components"], r["Components"], effective[RequirePure], settings];
    If[FailureQ[data], data, makeMassMatrix[expr, data, <|"Rows" -> {l["ID"]}, "Columns" -> {r["ID"]},
        "FieldNames" -> <|l["ID"] -> l["Name"], r["ID"] -> r["Name"]|>, "Context" -> l["Context"], "IrrepIDs" -> {l["IrrepID"], r["IrrepID"]}|>, settings]]
];
ExtractBilinearMatrix[expr_, rows_List, cols_List, options : OptionsPattern[]] := Module[{effective, settings, data},
    effective = resolveOperationOptions[ExtractBilinearMatrix, "ExtractBilinearMatrix", {options}]; If[FailureQ[effective], Return[effective]];
    settings = extractionSettings[expr, effective]; If[FailureQ[settings], Return[settings]];
    data = extractBilinearData[expr, rows, cols, effective[RequirePure], settings];
    If[FailureQ[data], data, makeMassMatrix[expr, data, <|"Rows" -> Missing["NotKnown"], "Columns" -> Missing["NotKnown"]|>, settings]]
];
ExtractBilinearMatrix[___] := makeFailure["InvalidInput", "ExtractBilinearMatrix expects an expression and two variable lists or two fields."];

Options[ExtractQuadraticMatrix] = {QuadraticConvention -> "Polynomial", RequirePure -> False, Arithmetic -> "Exact", WorkingPrecision -> 50, Tolerance -> Automatic};

(*
    Summary: The symmetric quadratic coefficient matrix of an expression.
    Parameters: expr; components — variable list, or field — a Field (its components).
    Options/defaults: QuadraticConvention "Polynomial" (selected == x . M . x) or "Half" (selected == (x . M . x)/2, the
        Hessian); RequirePure False; Arithmetic "Exact" (default) or "Numerical" with WorkingPrecision and Tolerance.
    Returns: MassMatrix, or Failure.
    Effects: Pure.
    Failures: InvalidVariables; NonPolynomial; ImpureSector; InvalidOption; UnknownOption; InapplicableOption;
        NumericalInput; InvalidField; UnknownCoupling.
    Example: MatrixValues[ExtractQuadraticMatrix[q, f, QuadraticConvention -> "Half"]] is twice the Polynomial matrix.
    See also: ExtractBilinearMatrix; MatrixValues.
*)
ExtractQuadraticMatrix[expr_, field_Field, options : OptionsPattern[]] := Module[{f = validateField[field], effective, settings, data},
    If[FailureQ[f], Return[f]];
    effective = resolveOperationOptions[ExtractQuadraticMatrix, "ExtractQuadraticMatrix", {options}]; If[FailureQ[effective], Return[effective]];
    settings = extractionSettings[expr, effective]; If[FailureQ[settings], Return[settings]];
    data = extractQuadraticData[expr, f["Components"], effective[QuadraticConvention], effective[RequirePure], settings];
    If[FailureQ[data], data, makeMassMatrix[expr, data, <|"Rows" -> {f["ID"]}, "Columns" -> {f["ID"]}, "FieldNames" -> <|f["ID"] -> f["Name"]|>,
        "Context" -> f["Context"], "IrrepIDs" -> {f["IrrepID"]}|>, settings]]
];
ExtractQuadraticMatrix[expr_, components_List, options : OptionsPattern[]] := Module[{effective, settings, data},
    effective = resolveOperationOptions[ExtractQuadraticMatrix, "ExtractQuadraticMatrix", {options}]; If[FailureQ[effective], Return[effective]];
    settings = extractionSettings[expr, effective]; If[FailureQ[settings], Return[settings]];
    data = extractQuadraticData[expr, components, effective[QuadraticConvention], effective[RequirePure], settings];
    If[FailureQ[data], data, makeMassMatrix[expr, data, <|"Rows" -> Missing["NotKnown"], "Columns" -> Missing["NotKnown"]|>, settings]]
];
ExtractQuadraticMatrix[___] := makeFailure["InvalidInput", "ExtractQuadraticMatrix expects an expression and a variable list or a field."];

(*
    Summary: The matrix of a MassMatrix.
    Parameters: mass — MassMatrix.
    Options/defaults: None.
    Returns: Matrix, or Failure.
    Effects: Pure.
    Failures: InvalidMassMatrix.
    Example: Dimensions[MatrixValues[mass]] is {3, 3} for two triplets.
    See also: ExtractBilinearMatrix; ExtractQuadraticMatrix.
*)
MatrixValues[mass_MassMatrix] := With[{data = validateMassMatrixData[mass]}, If[FailureQ[data], data, data["Matrix"]]];
MatrixValues[___] := makeFailure["InvalidInput", "MatrixValues expects a MassMatrix."];

(*
    Summary: Certify that a coefficient matrix was derived from a model and transforms covariantly.
    Parameters: m — Model; mass — MassMatrix.
    Options/defaults: Verification -> Automatic (the model's arithmetic), "Exact" (InapplicableOption for a numerical
        model) or "Numerical" (the source and covariance checks in the model's numerical view); None is InvalidOption.
    Returns: <|"ModelID", "Sector" -> kind, dimensions and convention, "Reconstruction" -> True, "Covariant" -> Boolean,
        "Generator", "Status" -> "Covariant" | "Covariant (numerical)" | "NotCovariant", "Arithmetic", "Precision",
        "Tolerance" (Missing["Exact"] for an exact model)|>, or Failure.
    Effects: Pure.
    Failures: InvalidModel; InvalidMassMatrix (also recorded row/column fields that differ from the variables);
        SourceModelMismatch (the input expression is not the model's expression); NonClosedFieldSelection (partial
        multiplets or unknown components); UndecidableCovariance.
    Example: ValidateMassMatrix[model2, mass]["Covariant"] is True for the A4 bilinear example.
    Remarks: The whole model expression must be the input; the selected sector is checked by reconstruction, then
        P_i^T M(transformed spectators) Q_i == chi(i) M on every generator (P = Q for quadratic matrices). The source and
        covariance checks use the model's own settings (review M21): exact equality for an exact model, the model's
        numerical view and its declared tolerance when the model or any of its terms is numerical (numerical status only,
        never an exact certificate, review M5). The matrix's own tolerance governs only its reconstruction. The report
        states the precision and tolerance used.
    See also: ExtractBilinearMatrix; ValidateModel.
*)
Options[ValidateMassMatrix] = {Verification -> Automatic};
ValidateMassMatrix[m_Model, mass_MassMatrix, options : OptionsPattern[]] := Module[{model = validateModelSchema[m], data = validateMassMatrixData[mass], numerical, view, settings,
        rederived, rowsOK, covariance, effective, allowed},
    If[FailureQ[model], Return[model]]; If[FailureQ[data], Return[data]];
    effective = resolveOperationOptions[ValidateMassMatrix, "ValidateMassMatrix", {options}]; If[FailureQ[effective], Return[effective]];
    (* The source and covariance checks use the model's own arithmetic and tolerance, never the matrix's (review M21): an
       exact model requires the exact model expression; the matrix's declared tolerance governs only its own
       reconstruction (validateMassMatrixData). *)
    numerical = model["Arithmetic"] === "Numerical" || MemberQ[Lookup[model["Terms"], "Arithmetic", {}], "Numerical"];
    allowed = checkLevelQ["ValidateMassMatrix", effective[Verification], numerical]; If[FailureQ[allowed], Return[allowed]];
    numerical = numerical || effective[Verification] === "Numerical";
    view = If[numerical, numericalModelView[model, model["Terms"]], model];
    settings = modelSettings[view];
    If[!residualZeroQ[data["InputExpression"] - Total[Lookup[model["Terms"], "Value", {}]], settings],
        Return[makeFailure["SourceModelMismatch", "The matrix was not extracted from this model's expression.", <|"ModelID" -> model["ID"]|>]]];
    (* The sector is re-derived from the input expression with the model's settings (review M24): the record's own
       tolerance and its internal consistency never certify the matrix, selected part or remainder. *)
    rederived = If[data["Kind"] === "Quadratic", extractQuadraticData[data["InputExpression"], data["Rows"], data["Convention"], False, settings],
        extractBilinearData[data["InputExpression"], data["Rows"], data["Columns"], False, settings]];
    If[FailureQ[rederived], Return[rederived]];
    If[rederived["Convention"] =!= data["Convention"] || Dimensions[rederived["Matrix"]] =!= Dimensions[data["Matrix"]] ||
            !AllTrue[Flatten[{rederived["Matrix"] - data["Matrix"], rederived["Selected"] - data["Selected"], rederived["Remainder"] - data["Remainder"]}],
                residualZeroQ[#, settings] &],
        Return[makeFailure["InvalidMassMatrix", "The matrix, selected sector or remainder differ from the sector of the input expression at the model's arithmetic.",
            <|"ModelID" -> model["ID"]|>]]];
    (* Recorded field identities must be the fields of the row and column variables (review M10). *)
    rowsOK = AllTrue[{{"RowFields", "Rows"}, {"ColumnFields", "Columns"}}, Function[pair, With[{recorded = Lookup[data, pair[[1]], Missing[]]},
        !ListQ[recorded] || (AllTrue[data[pair[[2]]], MatchQ[#, FieldComponent[_String, _Integer]] &] &&
            DeleteDuplicates[First /@ data[pair[[2]]]] === recorded)]]];
    If[!rowsOK, Return[makeFailure["InvalidMassMatrix", "The recorded row or column fields differ from the matrix variables."]]];
    covariance = validateMatrixCovariance[view, data];
    If[FailureQ[covariance], Return[covariance]];
    (* Modular models (Stage 8): entrywise required weights, each entry and the remainder checked monomial by monomial. *)
    With[{modular = If[KeyExistsQ[model, "ModularData"], validateModularMassData[model, data], <||>]},
        Join[<|"ModelID" -> model["ID"], "Sector" -> <|"Kind" -> data["Kind"], "Dimensions" -> Dimensions[data["Matrix"]], "Convention" -> data["Convention"]|>,
            "Reconstruction" -> True, "Covariant" -> covariance["Covariant"], "Generator" -> covariance["Generator"],
            "Status" -> Which[!covariance["Covariant"], "NotCovariant", modular =!= <||> && modular["ModularWeight"] =!= "Homogeneous", "InconsistentWeight",
                numerical, "Covariant (numerical)", True, "Covariant"],
            "Arithmetic" -> If[numerical, "Numerical", "Exact"], "Precision" -> settings["Precision"],
            "Tolerance" -> Replace[settings["Tolerance"], None -> Missing["Exact"]],
            "VerificationStatus" -> cgWeakestStatus[{modelVerificationStatus[model], Lookup[data, "VerificationStatus", "Exact"],
                If[numerical, "Numerical", "Exact"]}]|>, modular]]
];
ValidateMassMatrix[___] := makeFailure["InvalidInput", "ValidateMassMatrix expects a Model, a MassMatrix and options."];

Format[MassMatrix[data_Association], StandardForm] := Interpretation[Row[{"MassMatrix[", Lookup[data, "Kind", "?"], " ", Lookup[data, "Dimensions", "?"], "]"}],
    MassMatrix[data]];

True
