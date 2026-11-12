(*
    :Title: Irreps by index
    :Context: VVMFTool`Private`
    :Summary: The presentation of a group or context (irrep order, labels, class order) and the resolution of irrep
        indices to irrep IDs at the API boundary (uxUpdatePlan.md 1.1-1.3).
    :Responsibilities: liveContextGroupState, presentationData, irrepOrder, irrepIndexOf, irrepFromIndex,
        irrepIntegerQ, resolveIrrepArguments, withIrreps, irrepActiveRep, cgIrrepOrder, resolveIrrepOptions, displayIrrepOptions, irrepPlainName, manifestIrrepFields.
    :Dependencies: GroupObject.wl ($GroupRegistry, groupData, irrepOrderQ); Representation.wl (resolveRepContext,
        contextPresentation).
    :See Also: VVMFArch/uxUpdatePlan.md (P1: indices are views, IDs are identities).
*)

(*
    Summary: The live registered group state that presents a context.
    Parameters: snapshot — a resolved context snapshot.
    Options/defaults: None.
    Returns: The registry state of the group the context was frozen from (its SourceInstanceID), else of any live
        group with the context's GroupIdentity (state ID), else None.
    Effects: Reads $GroupRegistry.
    Failures: None.
    Example: liveContextGroupState[First[RepresentationContext[g]]]["InstanceID"] is g's instance ID while g is live.
    Remarks: The state ID is kept by ReorderGroupIrreps and label changes, so a context frozen earlier follows the
        group's current order and labels (uxUpdatePlan.md 1.1, review N2).
    See also: presentationData.
*)
liveContextGroupState[snapshot_Association] := Module[{source = Lookup[snapshot, "SourceInstanceID", None], state},
    state = If[StringQ[source], Lookup[$GroupRegistry, source, None], None];
    If[AssociationQ[state] && state["StateID"] === snapshot["GroupIdentity"], Return[state]];
    SelectFirst[Values[$GroupRegistry], #["StateID"] === snapshot["GroupIdentity"] &, None]
];

(*
    Summary: The presentation data of a group or context.
    Parameters: c — Group or RepresentationContext.
    Options/defaults: None.
    Returns: <|"IrrepOrder", "IrrepLabels", "ClassLabels", "ClassOrder", "CharacterData"|>, or Failure.
    Effects: Reads the registry; resolves a context through its kernel binding.
    Failures: InvalidGroup; UnverifiedContext.
    Example: presentationData[g]["IrrepOrder"] === g["IrrepOrder"].
    Remarks: A context uses its live group's presentation (liveContextGroupState), else its own presentation keys,
        each checked (an order that is not a permutation of the irrep IDs falls back to the canonical order, labels of
        unknown IDs are dropped), since presentation keys are outside the context digest.
    See also: irrepOrder; contextPresentation.
*)
presentationData[group_Group] := With[{data = groupData[group]}, If[FailureQ[data], data,
    Join[contextPresentation[data], <|"CharacterData" -> data["CharacterData"]|>]]];
presentationData[context_RepresentationContext] := Module[{snapshot = resolveRepContext[context], live, source, characters},
    If[FailureQ[snapshot], Return[snapshot]];
    characters = snapshot["CharacterData"];
    live = liveContextGroupState[snapshot];
    source = If[AssociationQ[live], contextPresentation[live], snapshot];
    <|"IrrepOrder" -> With[{order = Lookup[source, "IrrepOrder", None]},
            If[ListQ[order] && Sort[order] === Sort[characters["IrrepIDs"]] && DuplicateFreeQ[order], order, characters["IrrepIDs"]]],
        "IrrepLabels" -> KeyTake[Replace[Lookup[source, "IrrepLabels", <||>], Except[_Association] -> <||>], characters["IrrepIDs"]],
        "ClassLabels" -> KeyTake[Replace[Lookup[source, "ClassLabels", <||>], Except[_Association] -> <||>], characters["ClassIDs"]],
        "ClassOrder" -> With[{order = Lookup[source, "ClassOrder", None]},
            If[ListQ[order] && Sort[order] === Sort[characters["ClassIDs"]] && DuplicateFreeQ[order], order, characters["ClassIDs"]]],
        "CharacterData" -> characters|>
];
presentationData[___] := makeFailure["UnverifiedContext", "Expected a Group or a RepresentationContext."];

(*
    Summary: The irrep order of a group or context, and an irrep's index in it.
    Parameters: c — Group or RepresentationContext; id — irrep ID.
    Options/defaults: None.
    Returns: irrepOrder: list of irrep IDs, or Failure. irrepIndexOf: 1-based position, or Missing["NotAvailable"].
    Effects: As presentationData.
    Failures: As presentationData.
    Example: irrepIndexOf[g, First[g["IrrepOrder"]]] is 1.
    See also: irrepFromIndex.
*)
irrepOrder[c_] := With[{p = presentationData[c]}, If[FailureQ[p], p, p["IrrepOrder"]]];
irrepIndexOf[c_, id_String] := With[{order = irrepOrder[c]},
    If[ListQ[order], Replace[FirstPosition[order, id, {Missing["NotAvailable"]}, {1}], {k_} :> k], Missing["NotAvailable"]]];

(*
    Summary: The irrep ID at an index.
    Parameters: c — Group or RepresentationContext; k — integer index (1-based position in the irrep order).
    Options/defaults: None.
    Returns: The irrep ID, or Failure.
    Effects: As presentationData.
    Failures: InvalidIrrep (out of range); context failures.
    Example: irrepFromIndex[g, 1] === First[g["IrrepOrder"]].
    See also: resolveIrrepArguments.
*)
irrepFromIndex[c_, k_Integer] := With[{order = irrepOrder[c]}, Which[
    FailureQ[order], order,
    1 <= k <= Length[order], order[[k]],
    True, makeFailure["InvalidIrrep", "The irrep index " <> ToString[k] <> " is out of range 1.." <> ToString[Length[order]] <> ".",
        <|"Index" -> k, "Count" -> Length[order]|>]]];

(*
    Summary: Whether irrep arguments contain an index, and their resolution to IDs.
    Parameters: x — an irrep argument: an ID, an index, a list or nested lists of them (pairs, products, selections), or
        anything else (All, a Rep, Automatic) which is left unchanged; c — Group or RepresentationContext.
    Options/defaults: None.
    Returns: irrepIntegerQ: True when an integer occurs in x. resolveIrrepArguments: x with every integer replaced by its
        irrep ID, or the first Failure.
    Effects: As presentationData.
    Failures: InvalidIrrep; context failures.
    Example: resolveIrrepArguments[g, {{1, 2}, {2, 2}}] gives the ID pairs of the first two irreps.
    See also: withIrreps.
*)
irrepIntegerQ[x_] := !FreeQ[x, _Integer, {0, Infinity}, Heads -> False];
resolveIrrepArguments[c_, x_] := Catch[x /. k_Integer :> With[{id = irrepFromIndex[c, k]}, If[FailureQ[id], Throw[id, "irrepIndex"], id]], "irrepIndex"];

(*
    Summary: Call a function with irrep arguments resolved from indices to IDs.
    Parameters: c — Group or RepresentationContext; args — list of irrep arguments; f — function applied to the resolved
        arguments.
    Options/defaults: None.
    Returns: f @@ resolved arguments, or the first resolution Failure.
    Effects: Those of f.
    Failures: InvalidIrrep; context failures.
    Example: GroupRepresentation[g, 4] is withIrreps[g, {4}, GroupRepresentation[g, #] &].
    Remarks: Used by the index overloads of every public function that takes irreps (uxUpdatePlan.md 1.3); the
        overload condition irrepIntegerQ keeps the ID-only calls on their original definitions.
    See also: resolveIrrepArguments.
*)
withIrreps[c_, args_List, f_] := With[{resolved = resolveIrrepArguments[c, args]}, If[FailureQ[resolved], resolved, f @@ resolved]];

(*
    Summary: The active representation of an irrep of a group or context.
    Parameters: c — Group or RepresentationContext; spec — irrep index or ID.
    Options/defaults: None.
    Returns: The active variant's Rep, Missing["NotComputed"], or Failure.
    Effects: As presentationData.
    Failures: InvalidIrrep; InvalidIrrepID; context failures.
    Example: irrepActiveRep[g, 4] === GroupRepresentation[g, 4].
    Remarks: Lets views accept an irrep index where they take a Rep (RepresentationView, RepresentationLabelData).
    See also: GroupRepresentation.
*)
irrepActiveRep[group_Group, spec_] := GroupRepresentation[group, spec];
irrepActiveRep[context_RepresentationContext, spec_] := Module[{snapshot = resolveRepContext[context], id, entry},
    If[FailureQ[snapshot], Return[snapshot]];
    id = If[IntegerQ[spec], irrepFromIndex[context, spec], spec]; If[FailureQ[id], Return[id]];
    If[!MemberQ[snapshot["CharacterData"]["IrrepIDs"], id],
        Return[makeFailure["InvalidIrrepID", "The irrep ID does not belong to this group.", <|"ID" -> id|>]]];
    entry = Lookup[snapshot["Representations"], id, None];
    If[AssociationQ[entry] && StringQ[entry["ActiveVariant"]], entry["Variants"][entry["ActiveVariant"]]["Rep"], Missing["NotComputed"]]
];

(*
    Summary: The irrep order of the live group a CG result belongs to.
    Parameters: data — CGData association.
    Options/defaults: None.
    Returns: The live group's irrep order, or Failure when the group is not loaded in this kernel.
    Effects: Reads $GroupRegistry.
    Failures: GroupNotLoaded.
    Example: cgIrrepOrder[First[cg]] === g["IrrepOrder"] for a CG result of g.
    See also: CGIntertwiners.
*)
cgIrrepOrder[data_Association] := With[{state = SelectFirst[Values[$GroupRegistry], #["StateID"] === Lookup[data["Context"], "GroupIdentity", None] &, None]},
    If[AssociationQ[state], state["IrrepOrder"],
        makeFailure["GroupNotLoaded", "The CG result's group is not loaded in this kernel; name the target by its irrep ID."]]];

(*
    Summary: Resolve irrep indices in the options that name irreps.
    Parameters: c — Group or RepresentationContext; effective — validated options.
    Options/defaults: None.
    Returns: effective with every index in TargetIrreps, TargetIrrep, TargetRepresentations (keys), IrrepLabels (keys)
        and RowOrder replaced by its irrep ID, or the first Failure.
    Effects: As presentationData.
    Failures: InvalidIrrep; context failures.
    Example: resolveIrrepOptions[g, <|TargetIrreps -> {1, 2}|>][TargetIrreps] lists the IDs of the first two irreps.
    Remarks: An integer permutation as RowOrder gives the order old[[perm]] of the group's irrep order.
    See also: resolveIrrepArguments.
*)
resolveIrrepOptions[c_, effective_Association] := Catch[Module[{e = effective, r},
    r[x_] := With[{v = resolveIrrepArguments[c, x]}, If[FailureQ[v], Throw[v, "irrepOptions"], v]];
    Do[If[KeyExistsQ[e, key] && irrepIntegerQ[e[key]], e[key] = r[e[key]]], {key, {TargetIrreps, TargetIrrep, RowOrder}}];
    Do[If[KeyExistsQ[e, key] && AssociationQ[e[key]] && irrepIntegerQ[Keys[e[key]]], e[key] = KeyMap[r, e[key]]],
        {key, {TargetRepresentations, IrrepLabels}}];
    e], "irrepOptions"];

(*
    Summary: Resolve indices in the IrrepLabels option of a model or form display.
    Parameters: x — the displayed value (Model, ContractionSet, MassMatrix, ModelOutput, ModularForm, a list or
        association of forms, ...); effective — validated options.
    Options/defaults: None.
    Returns: effective with IrrepLabels keyed by irrep ID, or Failure.
    Effects: Reads the form registry for ModularForm handles.
    Failures: InvalidOption (index keys for a value without a group context); InvalidIrrep.
    Example: displayIrrepOptions[m, <|IrrepLabels -> <|4 -> "2''"|>|>] keys the label by the ID of m's irrep 4.
    See also: resolveIrrepOptions.
*)
displayIrrepOptions[x_, effective_Association] := Module[{context},
    If[!KeyExistsQ[effective, IrrepLabels] || !AssociationQ[effective[IrrepLabels]] || !irrepIntegerQ[Keys[effective[IrrepLabels]]], Return[effective]];
    context = Which[
        MatchQ[x, _ModularForm], Lookup[Replace[snapshotForm[x], _Failure -> <||>], "Context", None],
        MatchQ[x, {__ModularForm} | <|(_ -> _ModularForm) ..|>], Lookup[Replace[snapshotForm[First[x]], _Failure -> <||>], "Context", None],
        True, FirstCase[x, _RepresentationContext, None, {0, Infinity}]];
    If[!MatchQ[context, _RepresentationContext],
        Return[makeFailure["InvalidOption", "IrrepLabels keyed by irrep index needs a value with a group context; key them by irrep ID.", <|"Options" -> {IrrepLabels}|>]]];
    resolveIrrepOptions[context, effective]
];

(*
    Summary: The plain-text name of an irrep: its user label, else its automatic label (dimension and T phases), else its
        index (uxUpdatePlan.md P2).
    Parameters: c — Group or RepresentationContext, or the GroupIdentity (state ID) of a CG result; id — irrep ID.
    Options/defaults: None.
    Returns: String such as "2''" or "4", or the ID when no presentation is available.
    Effects: As presentationData; for a state ID, reads the registry.
    Failures: None.
    Example: irrepPlainName[g, id] is "2'" after SetIrrepLabel[g, id, "2'"], and "2(0,1/3)" without a user label.
    See also: irrepPresentation; VectorComponents.
*)
irrepPlainName[c : (_Group | _RepresentationContext), id_String] := With[{p = presentationData[c]}, Which[
    FailureQ[p], id,
    KeyExistsQ[p["IrrepLabels"], id], labelPlainText[p["IrrepLabels"][id]],
    StringQ[automaticLabelText[c, id]], automaticLabelText[c, id],
    MemberQ[p["IrrepOrder"], id], ToString[First[FirstPosition[p["IrrepOrder"], id]]],
    True, id]];
irrepPlainName[stateID_String, id_String] := With[{state = SelectFirst[Values[$GroupRegistry], #["StateID"] === stateID &, None]},
    If[AssociationQ[state], irrepPlainName[Group[state["InstanceID"]], id], id]];
(* The automatic label as text: the dimension with the T phases, e.g. "2(0,1/3)"; None when no phases are available
   (display memo of RepresentationLabelData; no GAP). *)
automaticLabelText[c_, id_String] := Module[{k = irrepIndexOf[c, id], data},
    If[!IntegerQ[k], Return[None]];
    data = Quiet[RepresentationLabelData[c, k]];
    If[AssociationQ[data] && ListQ[data["TPhases"]] && IntegerQ[data["Dimension"]],
        ToString[data["Dimension"]] <> "(" <> StringRiffle[ToString[#, InputForm] & /@ data["TPhases"], ","] <> ")", None]];

(*
    Summary: The manifest fields that name an irrep for generated Python (uxUpdatePlan.md 1.6, review F20).
    Parameters: source — Group, RepresentationContext or state ID; id — irrep ID (or anything else).
    Options/defaults: None.
    Returns: <|"irrep_index" -> integer or Null, "irrep_label" -> plain text or Null|>.
    Effects: Reads the presentation (live group when available).
    Failures: None.
    Example: manifestIrrepFields[ctx, id]["irrep_index"] is the irrep's index.
    See also: irrepPlainName.
*)
manifestIrrepFields[source_, id_String] := Module[{order = Which[
        MatchQ[source, _Group | _RepresentationContext], Replace[irrepOrder[source], _Failure -> {}],
        StringQ[source], Lookup[Replace[SelectFirst[Values[$GroupRegistry], #["StateID"] === source &, <||>], Except[_Association] -> <||>], "IrrepOrder", {}],
        True, {}]},
    <|"irrep_index" -> Replace[FirstPosition[order, id, {Null}, {1}], {k_} :> k],
        "irrep_label" -> If[MemberQ[order, id], irrepPlainName[source, id], Null]|>];
manifestIrrepFields[___] := <|"irrep_index" -> Null, "irrep_label" -> Null|>;
