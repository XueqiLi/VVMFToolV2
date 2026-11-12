(*
    :Title: Display labels, certified T phases and captions
    :Context: VVMFTool`Private`
    :Summary: ID-safe irrep labels, a read-only local certified T spectrum, matrix-set selection and truthful
        captions for display documents.
    :Responsibilities:
        - certifiedRootOfUnityPhase: exact certification of a root-of-unity phase (shared with Stage 2).
        - localDisplaySpectrum: T phases from a T-diagonal variant, a kernel-local memo, or exact nullities of
          T - Exp[2 Pi I k/n] I (no GAP, no group change, bounded by DisplayTimeLimit).
        - displayLabelData / RepresentationLabelData, resolveDisplayLabels, resolveMatrixSet,
          formatGroupCaption.
    :Dependencies: Diagnostics.wl; GroupObject.wl (groupData); Representation.wl (wordMatrix, repIdentity,
        resolveRepContext); RepresentationValidation.wl (exact field helpers); GroupConstruction.wl
        (resolveOperationOptions).
    :See Also: VVMFArch/step3Plan.md; VVMFArch/implementation/step3Status.md (D-S3-2).
*)

(*
    Summary: Certify an exact root of unity z as Exp[2 Pi I r] with a rational r in [0, 1).
    Parameters: z — exact number (or approximate number); n — Automatic, or a positive integer that the
        order of z divides (r is then k/n).
    Options/defaults: n Automatic rationalizes the numerical phase.
    Returns: The rational r (exact z), the real phase in [0, 1) (approximate z), or $Failed when z is not the
        proposed root of unity.
    Effects: Pure.
    Failures: $Failed.
    Example: certifiedRootOfUnityPhase[Exp[2 Pi I/3]] is 1/3; certifiedRootOfUnityPhase[Sqrt[2]] is $Failed.
    Remarks: A numerical estimate only proposes r; exact equality (RootReduce) accepts it. Orders above 10^6
        are refused.
    See also: localDisplaySpectrum; tConventionQ.
*)
certifiedRootOfUnityPhase[z_, n_ : Automatic] := Module[{approximate, r},
    If[!NumericQ[z], Return[$Failed]];
    If[Precision[z] =!= Infinity, Return[Mod[Arg[z]/(2 Pi), 1]]];
    approximate = Mod[Arg[N[z, 40]]/(2 Pi), 1];
    r = Mod[If[IntegerQ[n] && n > 0, Round[approximate n]/n, Rationalize[approximate, 10^-30]], 1];
    (* Orders beyond 10^6 are not roots of unity of a finite group handled here; a value like 3/5 + 4/5 I
       (modulus one, not a root of unity) rationalizes to a huge denominator and is refused without work. *)
    If[MatchQ[r, _Integer | _Rational] && Denominator[r] <= 10^6 &&
        Quiet[TimeConstrained[RootReduce[z - Exp[2 Pi I r]], 10, $Failed]] === 0, r, $Failed]
];

$DisplaySpectrumMemo = <||>;

(*
    Summary: Read-only certified T phases of a representation for display labels.
    Parameters: data — accepted group data (read only); matrices — native (cyclotomic) or visible generator
        matrices of an accepted representation of the group; key — memo key {realization identity,
        GeneratorIdentity, assignment identity} or None; diagonalQ — True when the variant is known to have
        diagonal T under the current assignment; limit — seconds (DisplayTimeLimit).
    Options/defaults: None.
    Returns: <|"Phases" -> phases k/n (one per basis vector, ascending), "Route" -> "Diagonal" | "Memo" |
        "Local"|>, or Failure (MissingModularAssignment, UnsupportedArithmetic, SpectrumUnavailable, TimeLimit).
    Effects: Reads and extends only the kernel-local display memo; no GAP work, no group change, no new
        certificate.
    Failures: As listed; callers fall back to dimension/ID labels unless TPhases was requested explicitly.
    Example: the SL2Reps irreps of 24-3I have diagonal T; their phases come from the diagonal.
    Remarks: T has finite order dividing the group order n, so it is diagonalizable and the multiplicity of
        Exp[2 Pi I k/n] is the exact nullity of T - Exp[2 Pi I k/n] I; numerical eigenvalues propose the k,
        exact nullities certify them, and they must cover the dimension (step3Status.md D-S3-2).
    See also: certifiedRootOfUnityPhase; displayLabelData.
*)
localDisplaySpectrum[data_Association, matrices_List, key_, diagonalQ_, limit_] := Module[{assignment, names, n, result, tWord},
    assignment = Lookup[data, "ModularAssignment", Missing["NotAssigned"]];
    (* without an assignment, the phases of a generator named T (a presentation aid, uxUpdatePlan.md 2.2) *)
    tWord = Which[AssociationQ[assignment], assignment["T"],
        MemberQ[Lookup[data["Generators"], "Name", {}], "T"], GroupWord[{{"T", 1}}],
        True, Return[makeFailure["MissingModularAssignment", "The group has no modular S,T assignment and no generator named T."]]];
    If[key =!= None && KeyExistsQ[$DisplaySpectrumMemo, key], Return[<|"Phases" -> $DisplaySpectrumMemo[key], "Route" -> "Memo"|>]];
    If[Precision[matrices] =!= Infinity, Return[makeFailure["UnsupportedArithmetic", "Exact phases need exact matrices."]]];
    names = Lookup[data["Generators"], "Name", {}]; n = data["Order"];
    If[!IntegerQ[n] || n < 1, Return[makeFailure["SpectrumUnavailable", "The group order is not recorded."]]];
    result = TimeConstrained[Module[{t, d, phases, candidates, field, counts},
        t = wordMatrix[repFromMatrices[matrices, Length[First[matrices, {{1}}]]], tWord, names];
        If[!MatrixQ[t], Return[makeFailure["SpectrumUnavailable", "The T word cannot be evaluated."], Module]];
        d = Length[t];
        If[TrueQ[diagonalQ] && DiagonalMatrixQ[t],
            phases = certifiedRootOfUnityPhase[#, n] & /@ Diagonal[t];
            If[MemberQ[phases, $Failed], Return[makeFailure["SpectrumUnavailable", "A diagonal entry is not a root of unity."], Module]];
            Return[<|"Phases" -> Sort[phases], "Route" -> "Diagonal"|>, Module]];
        candidates = DeleteDuplicates[Mod[Round[n Mod[Arg[#]/(2 Pi), 1]], n] & /@ Eigenvalues[N[t, 30]]];
        field = exactField[Join[Flatten[t], Exp[2 Pi I #/n] & /@ candidates]];
        counts = Association[Map[# -> (d - fieldRank[field, fieldEmbed[field, t - Exp[2 Pi I #/n] IdentityMatrix[d]]]) &, candidates]];
        If[Total[Values[counts]] =!= d, Return[makeFailure["SpectrumUnavailable", "The certified eigenspaces do not cover the dimension."], Module]];
        <|"Phases" -> Sort[Flatten[KeyValueMap[ConstantArray[#1/n, #2] &, counts]]], "Route" -> "Local"|>],
        limit, makeFailure["TimeLimit", "The optional T-phase label exceeded DisplayTimeLimit."]];
    If[AssociationQ[result] && key =!= None && result["Route"] =!= "Memo",
        If[Length[$DisplaySpectrumMemo] >= 512, $DisplaySpectrumMemo = <||>];
        $DisplaySpectrumMemo[key] = result["Phases"]];
    result
];
localDisplaySpectrum[___] := makeFailure["SpectrumUnavailable", "Expected group data, matrices, key, diagonal flag and limit."];

(*
    Summary: Find the stored variant of a group whose realization identity matches a representation.
    Parameters: data — accepted group data; rep — Rep.
    Options/defaults: None.
    Returns: <|"IrrepID", "VariantID", "Variant"|>, or None.
    Effects: Pure.
    Failures: None.
    Example: storedVariantMatch[data, GroupRepresentation[g, id]]["IrrepID"] is id.
    See also: displayLabelData; snapshotRepDisplay.
*)
storedVariantMatch[data_Association, rep_Rep] := Module[{names, identity, exact},
    names = Lookup[data["Generators"], "Name", {}];
    exact = Precision[repMatrices[rep]] === Infinity;
    identity = If[exact, repIdentity[rep, names], None];
    Catch[
        KeyValueMap[Function[{id, entry}, KeyValueMap[Function[{variantID, variant},
            If[If[exact, variant["Identity"] === identity, variant["Rep"] === rep],
                Throw[<|"IrrepID" -> id, "VariantID" -> variantID, "Variant" -> variant|>, storedVariantMatch]]],
            Lookup[entry, "Variants", <||>]]], Lookup[data, "Representations", <||>]];
        None, storedVariantMatch]
];

(*
    Summary: Label data of a representation of an accepted group or context, read-only.
    Parameters: data — accepted group data (or a bound context snapshot with the same fields); rep — Rep;
        style — Automatic, "ID", "Dimension" or "TPhases"; limit — DisplayTimeLimit.
    Options/defaults: None.
    Returns: <|"Dimension", "IrrepID" (or Missing), "TPhases" (or Missing), "Arithmetic", "UniqueID" (the
        stored variant's realization identity, or Missing), "Style" (the style actually used)|>, or Failure when
        style is "TPhases" and no certified spectrum is available.
    Effects: May extend the kernel-local spectrum memo; no GAP work and no group change.
    Failures: SpectrumUnavailable/MissingModularAssignment/TimeLimit/UnsupportedArithmetic for explicit TPhases.
    Example: displayLabelData[data, GroupRepresentation[g, id], Automatic, 5]["IrrepID"] is id.
    Remarks: Phases are a display convention, never an irrep identifier; the IrrepID stays the identity.
        Only a stored variant (accepted evidence) or a cached validation naming the irrep binds a Rep to an
        irrep; an unmatched value keeps Missing IrrepID and no phases.
    See also: localDisplaySpectrum; RepresentationLabelData.
*)
displayLabelData[data_Association, rep_Rep, style_, limit_] := Module[
    {match, dimension, arithmetic, irrep, spectrum, used, key, matrices, assignment, diagonalQ},
    dimension = RepDim[rep]; match = storedVariantMatch[data, rep];
    arithmetic = If[AssociationQ[match], Lookup[match["Variant"], "Arithmetic", "Exact"],
        If[Precision[repMatrices[rep]] === Infinity, "Exact", "Numerical"]];
    irrep = If[AssociationQ[match], match["IrrepID"], validatedIrrep[data, rep]];
    assignment = Lookup[data, "ModularAssignment", Missing["NotAssigned"]];
    spectrum = If[MemberQ[{Automatic, "TPhases"}, style] && (AssociationQ[assignment] || MemberQ[Lookup[data["Generators"], "Name", {}], "T"]) &&
            StringQ[irrep] && arithmetic === "Exact",
        matrices = If[AssociationQ[match] && !MissingQ[Lookup[match["Variant"], "NativeMatrices", Missing[]]],
            match["Variant"]["NativeMatrices"], repMatrices[rep]];
        key = If[AssociationQ[match], {match["Variant"]["Identity"], data["GeneratorIdentity"],
            If[AssociationQ[assignment], assignment["Identity"], "generator:T"]}, None];
        diagonalQ = AssociationQ[match] && AssociationQ[assignment] && TrueQ[match["Variant"]["BasisProperties"]["TDiagonal"]] &&
            match["Variant"]["BasisProperties"]["AssignmentIdentity"] === assignment["Identity"];
        localDisplaySpectrum[data, matrices, key, diagonalQ, limit],
        Which[!AssociationQ[assignment], makeFailure["MissingModularAssignment", "The group has no modular S,T assignment."],
            !StringQ[irrep], makeFailure["SpectrumUnavailable", "The representation is not bound to an irrep of the group."],
            True, makeFailure["UnsupportedArithmetic", "Exact phases need an exact representation."]]];
    If[style === "TPhases" && FailureQ[spectrum], Return[spectrum]];
    used = Which[style === "TPhases", "TPhases", style === Automatic && AssociationQ[spectrum], "TPhases",
        style === Automatic, "Dimension", True, style];
    <|"Dimension" -> dimension, "IrrepID" -> If[StringQ[irrep], irrep, Missing["NotBound"]],
        "TPhases" -> If[AssociationQ[spectrum], spectrum["Phases"], Missing["NotAvailable"]],
        "Arithmetic" -> arithmetic,
        "UniqueID" -> If[AssociationQ[match], match["Variant"]["Identity"], Missing["NotBound"]],
        "Style" -> used, "PhaseGenerator" -> If[AssociationQ[assignment], "ModularT", "T"]|>
];

(*
    Summary: The irrep named by an existing cached validation of a representation, read-only.
    Parameters: data — accepted group data; rep — Rep.
    Options/defaults: None.
    Returns: The irrep ID of a cached ValidateRepresentation result, or None.
    Effects: Pure (reads the derived cache; never validates).
    Failures: None.
    Example: after ValidateRepresentation[g, r], validatedIrrep[groupData[g], r] is that result's Irreducible.
    See also: displayLabelData; snapshotRepDisplay.
*)
validatedIrrep[data_Association, rep_Rep] := validationEvidence[data, rep] /. {
    evidence_Association :> Replace[Lookup[evidence, "Irreducible", None], Except[_String] -> None], _ -> None};
(*
    Summary: The cached ValidateRepresentation result of a representation on a live group, read-only.
    Parameters: data — group data; rep — Rep.
    Options/defaults: None.
    Returns: The cached result association, or None.
    Effects: Pure.
    Failures: None.
    Example: validationEvidence[groupData[g], r] after ValidateRepresentation[g, r] returns that result.
    See also: validatedIrrep; RepresentationView.
*)
validationEvidence[data_Association, rep_Rep] := Module[{entries, hash},
    entries = Lookup[Lookup[Lookup[data, "RepresentationCache", <||>], "Entries", <||>], "Unitarity", <||>];
    hash = Hash[rep, "SHA256"];
    SelectFirst[Normal[entries], MatchQ[First[#], {"Validate", hash, ___}] &, None] /. {(_ -> v_) :> v}
];

Options[RepresentationLabelData] = {LabelStyle -> Automatic, DisplayTimeLimit -> 5};

(*
    Summary: Label data of a representation of a group or context.
    Status: Alpha.
    Parameters: c — live Group or bound RepresentationContext; r — Rep with one matrix per recorded generator.
    Options/defaults: LabelStyle -> Automatic ("ID", "Dimension", "TPhases"); DisplayTimeLimit -> 5 seconds for
        the optional local phase certification.
    Returns: <|"Dimension", "IrrepID", "TPhases", "Arithmetic", "UniqueID", "Style"|> (Missing where unbound or
        unavailable), or Failure.
    Effects: Read-only: no GAP process, no group or cache change, no new validation; a kernel-local display
        memo may be extended.
    Failures: UnverifiedContext, GeneratorBindingMismatch, InvalidOption; with LabelStyle -> "TPhases",
        MissingModularAssignment, SpectrumUnavailable, UnsupportedArithmetic or TimeLimit.
    Example: RepresentationLabelData[g, GroupRepresentation[g, id]]["TPhases"] lists certified phases k/n.
    Remarks: T phases are a display convention; distinct irrep IDs stay distinct even when dimensions and
        spectra coincide.
    See also: RepresentationTable; RepresentationTSpectrum.
*)
RepresentationLabelData[context : (_Group | _RepresentationContext), rep_Rep, options : OptionsPattern[]] := Module[
    {effective, data},
    effective = resolveOperationOptions[RepresentationLabelData, "RepresentationLabelData", {options}];
    If[FailureQ[effective], Return[effective]];
    data = displayGroupData[context]; If[FailureQ[data], Return[data]];
    If[NumberOfGenerator[rep] =!= Length[data["Generators"]],
        Return[makeFailure["GeneratorBindingMismatch", "The representation does not have one matrix per recorded generator."]]];
    displayLabelData[data, rep, effective[LabelStyle], effective[DisplayTimeLimit]]
];
RepresentationLabelData[context : (_Group | _RepresentationContext), k_Integer, options : OptionsPattern[]] :=
    With[{rep = irrepActiveRep[context, k]}, Which[FailureQ[rep], rep,
        MissingQ[rep], makeFailure["MissingRepresentation", "The irrep has no computed representation.", <|"Index" -> k|>],
        True, RepresentationLabelData[context, rep, options]]];
RepresentationLabelData[___] := makeFailure["InvalidInput", "RepresentationLabelData expects a Group or RepresentationContext, a Rep and options."];

(*
    Summary: Read-only group data for display from a live group or a bound context.
    Parameters: context — Group or RepresentationContext.
    Options/defaults: None.
    Returns: An association with the fields displays read (StateID, GeneratorIdentity, Generators, Order,
        CharacterData, ModularAssignment, Representations, IrrepOrder, RepresentationCache, Revision,
        StateGeneration, Name, CatalogueID, AvailableData, GAPCachePath, GAPCacheMetadata), or Failure.
    Effects: Pure read; a context is resolved through its kernel binding (never validated anew).
    Failures: UnverifiedContext; unknown groups.
    Example: displayGroupData[g]["Order"] equals g["Order"].
    See also: snapshotGroupDisplay; snapshotRepDisplay.
*)
displayGroupData[group_Group] := groupData[group];
displayGroupData[context_RepresentationContext] := Module[{snapshot},
    snapshot = resolveRepContext[context]; If[FailureQ[snapshot], Return[snapshot]];
    <|"StateID" -> snapshot["GroupIdentity"], "GeneratorIdentity" -> snapshot["GeneratorIdentity"],
        "Generators" -> MapThread[<|"ID" -> #1, "Name" -> #2|> &, {snapshot["GeneratorIDs"], snapshot["GeneratorNames"]}],
        "Order" -> snapshot["Order"], "CharacterData" -> snapshot["CharacterData"],
        "ModularAssignment" -> snapshot["ModularAssignment"], "Representations" -> snapshot["Representations"],
        "StateGeneration" -> snapshot["StateGeneration"], "Construction" -> snapshot["Construction"],
        Sequence @@ Normal[KeyTake[Replace[presentationData[context], _Failure -> <||>], {"IrrepOrder", "IrrepLabels", "ClassLabels", "ClassOrder"}]]|>
];
displayGroupData[___] := makeFailure["UnverifiedContext", "Expected a Group or a RepresentationContext."];

(*
    Summary: Resolve the matrix columns a representation view shows.
    Parameters: spec — MatrixSet value; data — display group data or None (bare Rep); count — number of
        recorded generators (matrices).
    Options/defaults: Automatic: the assigned S, T for a group with a modular assignment, the recorded
        generators otherwise.
    Returns: <|"Kind" -> "Generators" | "Modular", "Columns" -> {<|"Name", "Word" or "Index"|>...}|>, or Failure.
    Effects: Pure.
    Failures: MissingModularAssignment ("Modular" without an assignment); InvalidMatrixSet (unknown names,
        names without a context, indices out of range, duplicates, "Modular" for a bare Rep).
    Example: resolveMatrixSet["Generators", None, 3] gives columns g1, g2, g3 by index.
    Remarks: A bare Rep never receives invented S,T roles.
    See also: snapshotRepDisplay; RepresentationTable.
*)
resolveMatrixSet[spec_, data_, count_Integer] := Module[{names, assignment},
    names = If[AssociationQ[data], Lookup[data["Generators"], "Name", {}], None];
    assignment = If[AssociationQ[data], Lookup[data, "ModularAssignment", Missing["NotAssigned"]], Missing["NotAssigned"]];
    Which[
        spec === "Modular" && !AssociationQ[data],
            makeFailure["InvalidMatrixSet", "MatrixSet -> \"Modular\" needs a group or context with a modular assignment."],
        spec === "Modular" && !AssociationQ[assignment],
            makeFailure["MissingModularAssignment", "MatrixSet -> \"Modular\" requires a modular S,T assignment."],
        spec === "Modular" || (spec === Automatic && AssociationQ[assignment]),
            <|"Kind" -> "Modular", "Columns" -> {<|"Name" -> "S", "Word" -> assignment["S"]|>, <|"Name" -> "T", "Word" -> assignment["T"]|>}|>,
        spec === Automatic || spec === "Generators",
            <|"Kind" -> "Generators", "Columns" -> If[names === None,
                Table[<|"Name" -> "g" <> ToString[i], "Index" -> i|>, {i, count}],
                MapIndexed[<|"Name" -> #1, "Index" -> First[#2]|> &, names]]|>,
        ListQ[spec] && AllTrue[spec, StringQ] && names =!= None && SubsetQ[names, spec],
            <|"Kind" -> "Generators", "Columns" -> (<|"Name" -> #, "Index" -> First[FirstPosition[names, #]]|> & /@ spec)|>,
        ListQ[spec] && AllTrue[spec, IntegerQ[#] && 1 <= # <= count &],
            <|"Kind" -> "Generators", "Columns" -> (<|"Name" -> If[names === None, "g" <> ToString[#], names[[#]]], "Index" -> #|> & /@ spec)|>,
        True, makeFailure["InvalidMatrixSet", "MatrixSet names recorded generators of a group or context, or indices of a bare representation.",
            <|"MatrixSet" -> spec|>]]
];

(*
    Summary: Evaluate the selected matrix columns of a representation.
    Parameters: rep — Rep; set — resolveMatrixSet result; names — recorded generator names ({} for a bare Rep).
    Options/defaults: None.
    Returns: List of matrices in column order, or Failure.
    Effects: Pure; a modular column evaluates its assigned word on the given matrices (no new representation
        is constructed).
    Failures: InvalidWord.
    Example: selectedMatrices[r, <|"Kind" -> "Generators", "Columns" -> {<|"Name" -> "g1", "Index" -> 1|>}|>, {}] is {GeneratorMatrix[r, 1]}.
    See also: resolveMatrixSet.
*)
selectedMatrices[rep_Rep, set_Association, names_List] := Module[{matrices},
    matrices = Map[Function[column, If[KeyExistsQ[column, "Index"], repMatrices[rep][[column["Index"]]],
        wordMatrix[rep, column["Word"], names]]], set["Columns"]];
    If[AnyTrue[matrices, FailureQ], FirstCase[matrices, _Failure], matrices]
];

(*
    Summary: Resolve display labels of irreps: custom labels first, then the label style.
    Parameters: rows — list of <|"IrrepID", "LabelData"|>; custom — IrrepLabels association.
    Options/defaults: None.
    Returns: Association irrep ID -> label node (Text, RawTeX or IrrepLabel).
    Effects: Pure.
    Failures: None (custom labels are validated with the options).
    Example: a custom string label becomes an escaped Text node; TPhases style an IrrepLabel node.
    Remarks: Tables keep a separate ID column, so labels never replace identities.
    See also: displayLabelData.
*)
resolveDisplayLabels[rows_List, custom_Association] := Association[Map[Function[row,
    row["IrrepID"] -> Which[
        KeyExistsQ[custom, row["IrrepID"]], labelNode[custom[row["IrrepID"]]],
        row["LabelData"]["Style"] === "TPhases", <|"Kind" -> "IrrepLabel", "Dimension" -> row["LabelData"]["Dimension"],
            "Phases" -> row["LabelData"]["TPhases"]|>,
        row["LabelData"]["Style"] === "ID", textNode[row["IrrepID"]],
        True, <|"Kind" -> "IrrepLabel", "Dimension" -> row["LabelData"]["Dimension"], "Phases" -> None|>]], rows]];

(*
    Summary: The presentation of irreps in a document: index, user label, automatic label and the P2 display label.
    Parameters: data — group data or context presentation (IrrepOrder, IrrepLabels); ids — irrep IDs; labelData — irrep
        ID -> displayLabelData; custom — IrrepLabels option (irrep ID -> string or TeXFragment) overriding stored labels.
    Options/defaults: None.
    Returns: Association irrep ID -> <|"Index" -> k, "User" -> label node or None, "Auto" -> IrrepLabel node or None,
        "Display" -> the user label, else the automatic label, else the index as text|> (uxUpdatePlan.md P2).
    Effects: Pure.
    Failures: None.
    Example: for T' labelled 2'' at index 6, irrepPresentation[...][id]["Display"] is the UserLabel node of 2''.
    Remarks: An automatic label exists only with certified phases (of the modular T, or of a generator named T); a
        dimension alone is not a label (the dimension has its own column).
    See also: resolveDisplayLabels; labelBoxes.
*)
irrepPresentation[data_Association, ids_List, labelData_Association, custom_Association] := Module[
    {order = Lookup[data, "IrrepOrder", data["CharacterData"]["IrrepIDs"]], stored = Lookup[data, "IrrepLabels", <||>]},
    AssociationMap[Function[id, Module[{user, auto, ld = Lookup[labelData, id, <||>], index = First[FirstPosition[order, id, {0}, {1}]]},
        user = Which[KeyExistsQ[custom, id], labelNode[custom[id]], KeyExistsQ[stored, id], <|"Kind" -> "UserLabel", "Record" -> stored[id]|>, True, None];
        auto = If[AssociationQ[ld] && ListQ[Lookup[ld, "TPhases", None]],
            Join[<|"Kind" -> "IrrepLabel", "Dimension" -> ld["Dimension"], "Phases" -> ld["TPhases"]|>,
                If[Lookup[ld, "PhaseGenerator", "ModularT"] === "T", <|"Generator" -> "T"|>, <||>]], None];
        <|"Index" -> index, "User" -> user, "Auto" -> auto,
            "Display" -> Which[user =!= None, user, auto =!= None, auto, True, textNode[ToString[index]]]|>]], ids]];

(*
    Summary: Text and label nodes: an escaped Text node, or a RawTeX node for a TeXFragment (with a literal notebook fallback).
    Parameters: s — string or TeXFragment.
    Options/defaults: None.
    Returns: A Text or RawTeX node.
    Effects: Pure.
    Failures: None.
    Example: labelNode[TeXFragment["\\alpha"]]["Kind"] is "RawTeX".
    See also: resolveDisplayLabels; TeXFragment.
*)
textNode[s_String] := <|"Kind" -> "Text", "Text" -> s|>;
labelNode[s_String] := textNode[s];
labelNode[TeXFragment[s_String]] := <|"Kind" -> "RawTeX", "TeX" -> s, "Fallback" -> s|>;

(*
    Summary: A truthful caption for a display document.
    Parameters: data — document data (kind, group name/order, catalogue ID, assignment, selection).
    Options/defaults: None.
    Returns: A Text node.
    Effects: Pure.
    Failures: None.
    Example: a character table of "Group of order 24" with an assignment names both.
    Remarks: A group without an assignment is never called modular; an absent catalogue ID is not
        fabricated; the assignment identity distinguishes realizations of one abstract group.
    See also: renderTeXDocument; renderNotebookDocument.
*)
formatGroupCaption[data_Association] := Module[{group = data["Group"], subject, assignment},
    (* A registered later-stage kind writes its own caption. *)
    If[KeyExistsQ[$DisplayKindRegistry, data["Kind"]], Return[textNode[$DisplayKindRegistry[data["Kind"]]["Caption"][data]]]];
    subject = Switch[data["Kind"],
        "CharacterTable", "Character table of ",
        "RepresentationTable", "Irreducible representations of ",
        "GroupSummary", "Summary of ",
        "TensorDecomposition", "Tensor product decompositions of ",
        _, "Representation of "];
    assignment = Lookup[group, "Assignment", Missing[]];
    textNode[subject <> ToString[group["Name"]] <>
        If[StringQ[group["Name"]] && StringStartsQ[group["Name"], "Group of order "] || !IntegerQ[group["Order"]], "",
            " (order " <> ToString[group["Order"]] <> ")"] <>
        (* no internal identities in captions (UX update U1/U4): the GAP ID and the S, T words only *)
        If[MatchQ[Lookup[group, "CatalogueID", Missing[]], {_Integer, _Integer}], ", GAP ID [" <> StringRiffle[ToString /@ group["CatalogueID"], ","] <> "]", ""] <>
        If[AssociationQ[assignment], "; modular S = " <> assignment["SText"] <> ", T = " <> assignment["TText"], ""] <>
        Switch[data["Kind"],
            "RepresentationTable", "; " <> ToString[Length[data["Rows"]]] <> " of " <> ToString[group["IrrepCount"]] <> " irreps",
            _, ""] <>
        (* a weakly verified group says so (methodOptionsPlan.md 2C.6) *)
        If[StringQ[Lookup[group, "VerificationStatus", None]], "; verification: " <> group["VerificationStatus"], ""] <> "."]
];

True
