(*
    :Title: Public subgroup queries
    :Context: VVMFTool`Private`
    :Summary: Request embedded subgroup collections independently of modular assignments.
    :Responsibilities: Stable query keys, cache reuse, public options and builder integration.
    :Dependencies: GroupEnrichment.wl; SubgroupValidation.wl; GAP/Subgroups.g.
    :See Also: VVMFArch/step1Plan.md; GroupElementWords.
*)

Options[GroupSubgroups] = Join[Options[RestoreGAPState], {WordRecovery -> Automatic, Method -> Automatic,
    SubgroupKind -> "ConjugacyClasses", SubgroupOrder -> All, SubgroupIndex -> All,
    SubgroupDescriptions -> False, Verification -> Automatic}];

(*
    Summary: Identify a subgroup query by its mathematical selection, independently of method.
    Parameters: options — validated GroupSubgroups settings.
    Options/defaults: Descriptions enrich the same query identity; All filters encode as null.
    Returns: Exact native query record; malformed settings are the public validator's responsibility.
    Effects: Pure; the SHA256 key identifies selection and does not establish provenance.
    Failures: Requires the documented validated options precondition.
    Example: changing GAP to ClassExpansion leaves an All-subgroup query's ID unchanged.
    See also: GroupSubgroups; decodeSubgroupQuery.
*)
subgroupQuery[options_Association] := Module[{selection},
    selection = <|"kind" -> options[SubgroupKind],
        "order" -> If[options[SubgroupOrder] === All, Null, encodeInteger[options[SubgroupOrder]]],
        "index" -> If[options[SubgroupIndex] === All, Null, encodeInteger[options[SubgroupIndex]]]|>;
    Join[<|"id" -> subgroupSelectionID[options[SubgroupKind], options[SubgroupOrder], options[SubgroupIndex]]|>, selection,
        <|"descriptions" -> options[SubgroupDescriptions]|>]
];

(*
    Summary: Obtain complete embedded subgroup classes, all subgroups, or normal subgroups.
    Status: Alpha.
    Parameters: group — live finite Group; no modular assignment or representation matrices are required.
    Options/defaults: SubgroupKind->ConjugacyClasses, order/index filters->All, descriptions->False;
        Method and GroupModel default Automatic; common execution/retention settings apply.
    Returns: Query association with Items, Kind, Filters, Complete, Descriptions and Provenance, or Failure.
    Effects: Enriches the same group through verified GAP state. Compatible complete cache wins
        before method computation; missing descriptions are added without replacing embeddings.
    Failures: Invalid options, method/kind mismatch, resources, embedding recovery or description failure.
    Example: GroupSubgroups[g, SubgroupKind->"Normal", SubgroupOrder->4] returns a complete
        filtered collection, including an explicit empty Items list when none exist.
    Remarks: A class-mode item is the chosen representative, expressed by its GeneratorWords
        and ConjugacyClassSize. All mode preserves each distinct actual embedding.
    See also: GroupElementWords; BuildGroup; StoreGAPState.
*)
GroupSubgroups[group_Group, options : OptionsPattern[]] := Module[{effective, accepted, query, cached, result},
    effective = resolveOperationOptions[GroupSubgroups, "GroupSubgroups", {options}];
    If[FailureQ[effective], Return[effective]];
    With[{allowed = proofComputationLevelQ["GroupSubgroups", effective[Verification]]}, If[FailureQ[allowed], Return[allowed]]];
    accepted = groupData[group]; If[FailureQ[accepted], Return[accepted]];
    query = subgroupQuery[effective];
    cached = If[AssociationQ[accepted["SubgroupData"]],
        Lookup[accepted["SubgroupData"], query["id"], Missing["NotComputed"]], Missing["NotComputed"]];
    If[AssociationQ[cached] && (cached["Kind"] =!= effective[SubgroupKind] ||
        cached["Filters"] =!= <|"Order" -> effective[SubgroupOrder], "Index" -> effective[SubgroupIndex]|>),
        Return[makeFailure["StateConflict", "The stored subgroup query does not match the requested selection."]]];
    If[AssociationQ[cached] && TrueQ[cached["Complete"]] &&
        (!TrueQ[effective[SubgroupDescriptions]] || cached["Descriptions"] === "Complete"), Return[cached]];
    result = runGroupEnrichment[group, "GroupSubgroups", <|"subgroupQuery" -> query|>, effective];
    If[FailureQ[result], result, group["SubgroupData"][query["id"]]]
];
GroupSubgroups[___] := makeFailure["InvalidInput", "Expected a live group and subgroup query options."];

(* The common builder call supplies its latest accepted temporary source to this adapter. *)
AssociateTo[$BuilderEnrichments, ComputeSubgroups -> Function[{group, options},
    GroupSubgroups[group, Sequence @@ Normal[KeyTake[options, Keys[$OperationDefaults["GroupSubgroups"]]]]]]];

True
