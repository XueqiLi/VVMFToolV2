(*
    :Title: Tensor decomposition view
    :Context: VVMFTool`Private`
    :Summary: A read-only DisplayDocument of tensor-product decompositions (kind "TensorDecomposition"), built from the
        character table alone: no matrices, no GAP, no change to the group or its caches.
    :Responsibilities: snapshotTensorDecomposition, TensorDecompositionView.
    :Dependencies: TensorCharacters.wl (tensorMultiplicities); DisplayData.wl (makeDisplayDocument, displayHeader,
        irrepLabelData); DisplayLabels.wl (displayGroupData, resolveDisplayLabels).
    :See Also: VVMFArch/step4Plan.md (TensorDecompositionView); VVMFArch/step3Plan.md (display contracts).
*)

Options[TensorDecompositionView] = {LabelStyle -> Automatic, IrrepLabels -> <||>, DisplayTimeLimit -> 5, ScalarNotation -> "Standard",
    NotationStyle -> "Standard", OneByOneMatrix -> "Scalar", DefineOmega -> True, Digits -> Automatic, Caption -> Automatic,
    Label -> None, PageSize -> 20};

(*
    Summary: The decomposition rows of the requested products.
    Parameters: data — display group data (Group or context); products — All, one ID list, or a list of ID lists;
        effective — validated options.
    Options/defaults: All means every unordered pair of irreps (presentation order, i <= j).
    Returns: <|"Products" -> {<|"Factors", "Dimension", "Constituents" -> {<|"IrrepID", "Multiplicity", "Dimension"|>...}|>...},
        "IrrepIDs", "LabelData", "Labels"|>, or Failure.
    Effects: Pure (the kernel-local character-product memo may be filled; no group or cache change).
    Failures: CharactersUnavailable; InvalidIrrep; InvalidInput for malformed products.
    Example: for A4, the product {t, t} lists 1, 1', 1'' once and t twice.
    See also: TensorDecompositionView; tensorMultiplicities.
*)
snapshotTensorDecomposition[data_Association, products_, effective_Association] := Module[
    {characters = data["CharacterData"], order, lists, degrees, rows, ids, labelData},
    If[!AssociationQ[characters] || Length[characters["IrrepIDs"]] =!= Length[characters["ClassIDs"]],
        Return[makeFailure["CharactersUnavailable", "The view needs the complete character table."]]];
    order = Lookup[data, "IrrepOrder", characters["IrrepIDs"]];
    lists = Which[products === All, Flatten[Table[{order[[i]], order[[j]]}, {i, Length[order]}, {j, i, Length[order]}], 1],
        ListQ[products] && AllTrue[products, StringQ], {products},
        ListQ[products] && products =!= {} && AllTrue[products, ListQ[#] && AllTrue[#, StringQ] &], products,
        True, Return[makeFailure["InvalidInput", "Products must be All, a list of irrep IDs or a list of such lists."]]];
    degrees = AssociationThread[characters["IrrepIDs"], characters["Degrees"]];
    rows = Map[Function[factors, With[{m = tensorMultiplicities[characters, factors]},
            If[FailureQ[m], m, <|"Factors" -> factors, "Dimension" -> Times @@ Lookup[degrees, factors],
                "Constituents" -> Map[<|"IrrepID" -> #, "Multiplicity" -> m[#], "Dimension" -> degrees[#]|> &, Select[order, m[#] > 0 &]]|>]]],
        lists];
    If[AnyTrue[rows, FailureQ], Return[FirstCase[rows, _Failure]]];
    ids = Select[order, MemberQ[Join[Flatten[lists], Flatten[Lookup[#["Constituents"], "IrrepID"] & /@ rows]], #] &];
    If[!SubsetQ[characters["IrrepIDs"], Keys[effective[IrrepLabels]]],
        Return[makeFailure["InvalidOption", "IrrepLabels names unknown irrep IDs.", <|"Options" -> {IrrepLabels}|>]]];
    labelData = AssociationMap[irrepLabelData[data, #, effective[LabelStyle], effective[DisplayTimeLimit]] &, ids];
    If[AnyTrue[Values[labelData], FailureQ], Return[FirstCase[Values[labelData], _Failure]]];
    (* irreps are named by user label > automatic label > index (uxUpdatePlan.md P2, U7) *)
    <|"Products" -> rows, "IrrepIDs" -> ids, "LabelData" -> labelData,
        "Labels" -> Map[#["Display"] &, irrepPresentation[data, ids, labelData, effective[IrrepLabels]]]|>
];

(*
    Summary: A display document of tensor-product decompositions.
    Parameters: c — Group or RepresentationContext; products — All (every unordered pair, default), one list of irrep IDs,
        or a list of such lists.
    Options/defaults: LabelStyle, IrrepLabels, DisplayTimeLimit and the presentation options of the Stage 3 views.
    Returns: DisplayDocument["TensorDecomposition", data], or Failure.
    Effects: Read-only: no matrices, no GAP, no group or cache change.
    Failures: Option failures; UnverifiedContext; CharactersUnavailable; InvalidIrrep.
    Example: ToNotebook[TensorDecompositionView[g, {t, t}]] shows t (x) t = 1 + 1' + 1'' + 2 t.
    Remarks: Rows list each product's dimension and its constituents with multiplicities in presentation order;
        render with ToNotebook, ToLaTeX or ExportDisplay.
    See also: TensorDecomposition; ToLaTeX; ToNotebook.
*)
TensorDecompositionView[c : (_Group | _RepresentationContext), products : Except[_Rule | _RuleDelayed] : All, options : OptionsPattern[]] := Module[
    {effective, data, snapshot, resolved},
    effective = resolveOperationOptions[TensorDecompositionView, "TensorDecompositionView", {options}];
    If[FailureQ[effective], Return[effective]];
    effective = resolveIrrepOptions[c, effective]; If[FailureQ[effective], Return[effective]];
    data = displayGroupData[c]; If[FailureQ[data], Return[data]];
    resolved = resolveIrrepArguments[c, products]; If[FailureQ[resolved], Return[resolved]];
    snapshot = snapshotTensorDecomposition[data, resolved, effective];
    If[FailureQ[snapshot], Return[snapshot]];
    makeDisplayDocument["TensorDecomposition", Join[displayHeader[data], snapshot], effective]
];
TensorDecompositionView[___] := makeFailure["InvalidInput", "TensorDecompositionView expects a Group or RepresentationContext, products and options."];

True
