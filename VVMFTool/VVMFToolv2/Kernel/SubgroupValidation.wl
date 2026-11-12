(*
    :Title: Embedded subgroup result validation
    :Context: VVMFTool`Private`
    :Summary: Decode exact subgroup queries without confusing descriptions with embeddings.
    :Responsibilities: Query filters, identities, exact invariants and monotone enrichment.
    :Dependencies: ResultValidation.wl scalar/word helpers at evaluation time.
    :See Also: GAP/Subgroups.g; GroupSubgroups; Schemas/GroupResult.md.
*)

(*
    Summary: Derive the public cache key from the complete subgroup selection.
    Parameters: kind — validated kind string; order/index — All or positive integer filters.
    Options/defaults: No optional parameters; descriptions and algorithm choices do not change selection.
    Returns: Stable subgroup query ID string.
    Effects: Pure.
    Failures: Caller must validate the selection domains before calling.
    Example: subgroupSelectionID["Normal", All, All] differs from the All-subgroup key.
    See also: subgroupQuery; decodeGroupSnapshot; GroupSubgroups.
*)
subgroupSelectionID[kind_String, order_, index_] := "subgroups-" <> IntegerString[Hash[
    <|"kind" -> kind, "order" -> If[order === All, Null, encodeInteger[order]],
        "index" -> If[index === All, Null, encodeInteger[index]]|>, "SHA256"], 16, 64];

(*
    Summary: Decode one complete subgroup query and its embedded generator-word records.
    Parameters: data — native query/items/completeness/provenance; order — finite parent order;
        generators — validated native ID/name records; stateID — accepted parent identity.
    Options/defaults: Missing descriptions decode to Missing[NotComputed], never empty strings.
    Returns: Public query association or InvalidSubgroups Failure.
    Effects: Pure exact schema/arithmetic checks; no native computation or trust issuance.
    Failures: Malformed filters, IDs, words, orders/indices/class sizes, duplicates or descriptions.
    Example: an empty computed query has Items->{}, Complete->True and explicit filters.
    Remarks: Native producer/provenance separately establishes embeddings, conjugacy and completeness.
    See also: decodeSubgroupData; decodeResultWord; validateGroupResult.
*)
decodeSubgroupQuery[data_, order_Integer, generators_List, stateID_String] := Module[
    {query, filters, provenance, items, decoded = {}, subgroupOrder, index, classSize, words,
        description, result, id, kind, failure = None},
    If[!resultFieldsQ[data, {"query", "items", "complete", "provenance"}] || data["complete"] =!= True ||
        !ListQ[data["items"]], Return[makeFailure["InvalidSubgroups", "Expected a complete subgroup query record."]]];
    query = data["query"]; provenance = data["provenance"];
    If[!resultFieldsQ[query, {"id", "kind", "order", "index", "descriptions"}] ||
        !resultIDsQ[{query["id"]}] || !MemberQ[{"ConjugacyClasses", "All", "Normal"}, query["kind"]] ||
        !MemberQ[{True, False}, query["descriptions"]],
        Return[makeFailure["InvalidSubgroups", "Invalid subgroup query identity or kind."]]];
    filters = Replace[#, Null -> All] & /@ KeyTake[query, {"order", "index"}];
    filters = If[# === All, All, decodeInteger[#]] & /@ filters;
    If[!AllTrue[Values[filters], # === All || (IntegerQ[#] && # > 0) &],
        Return[makeFailure["InvalidSubgroups", "Invalid subgroup order/index filter."]]];
    If[!resultFieldsQ[provenance, {"stateID", "requestID", "method", "model"}] ||
        provenance["stateID"] =!= stateID || !resultIDsQ[{provenance["requestID"]}] ||
        !MemberQ[{"GAP", "ClassExpansion", "ClassFilter"}, provenance["method"]] ||
        !MemberQ[{"Original", "Permutation", "PC"}, provenance["model"]] ||
        (query["kind"] === "ConjugacyClasses" && provenance["method"] =!= "GAP") ||
        (query["kind"] === "All" && provenance["method"] === "ClassFilter") ||
        (query["kind"] === "Normal" && provenance["method"] === "ClassExpansion"),
        Return[makeFailure["InvalidSubgroups", "The subgroup provenance does not match the query."]]];
    Do[
        If[!resultFieldsQ[item, {"id", "generatorWords", "order", "index", "normal", "classID", "classSize", "description"}] ||
            !resultIDsQ[{item["id"], item["classID"]}] || !ListQ[item["generatorWords"]] ||
            !MemberQ[{True, False}, item["normal"]],
            failure = makeFailure["InvalidSubgroups", "Malformed embedded subgroup record."]; Break[]];
        {subgroupOrder, index, classSize} = decodeInteger /@ Lookup[item, {"order", "index", "classSize"}];
        If[!AllTrue[{subgroupOrder, index, classSize}, IntegerQ[#] && # > 0 &] ||
            subgroupOrder index =!= order || !Divisible[index, classSize] ||
            (classSize === 1) =!= item["normal"] ||
            (query["kind"] === "Normal" && !item["normal"]) ||
            (filters["order"] =!= All && subgroupOrder =!= filters["order"]) ||
            (filters["index"] =!= All && index =!= filters["index"]),
            failure = makeFailure["InvalidSubgroups", "Subgroup invariants or filters are inconsistent."]; Break[]];
        words = decodeResultWord[#, generators] & /@ item["generatorWords"];
        If[AnyTrue[words, FailureQ], failure = makeFailure["InvalidSubgroups", "Invalid subgroup generator words."]; Break[]];
        description = item["description"];
        If[If[query["descriptions"], !StringQ[description], description =!= Null],
            failure = makeFailure["InvalidSubgroups", "Description availability disagrees with the query."]; Break[]];
        AppendTo[decoded, <|"SubgroupID" -> item["id"], "GeneratorWords" -> words,
            "Order" -> subgroupOrder, "Index" -> index, "Normal" -> item["normal"],
            "ConjugacyClassID" -> item["classID"], "ConjugacyClassSize" -> classSize,
            "Description" -> If[description === Null, Missing["NotComputed"], description]|>],
        {item, data["items"]}];
    If[FailureQ[failure], Return[failure]];
    If[!DuplicateFreeQ[Lookup[decoded, "SubgroupID", {}]] ||
        (query["kind"] === "ConjugacyClasses" && !DuplicateFreeQ[Lookup[decoded, "ConjugacyClassID", {}]]),
        Return[makeFailure["InvalidSubgroups", "A query repeats a subgroup embedding or representative class."]]];
    <|"QueryID" -> query["id"], "Items" -> decoded, "Kind" -> query["kind"],
        "Filters" -> <|"Order" -> filters["order"], "Index" -> filters["index"]|>, "Complete" -> True,
        "Descriptions" -> If[query["descriptions"], "Complete", "NotComputed"],
        "Provenance" -> provenance|>
];
decodeSubgroupQuery[___] := makeFailure["InvalidSubgroups", "Expected typed subgroup query data."];

(*
    Summary: Decode all retained subgroup queries with consistent shared embedding/class IDs.
    Parameters: data — null or a native query list; order/generators/stateID — finite parent context.
    Options/defaults: Null becomes Missing[NotComputed]; a computed empty query is preserved.
    Returns: Association keyed by query identity or InvalidSubgroups Failure.
    Effects: Pure; repeated IDs across queries must retain the same mathematical embedding data.
    Failures: Duplicate query IDs, conflicting embedding fields or inconsistent class metadata.
    Example: the three conjugate C2 subgroups of S3 share a class ID and description, not an embedding ID.
    See also: decodeSubgroupQuery; subgroupDataExtendsQ.
*)
decodeSubgroupData[Null, order_Integer, generators_List, stateID_String] := Missing["NotComputed"];
decodeSubgroupData[data_List, order_Integer, generators_List, stateID_String] := Module[
    {queries, items, groups, fields, classGroups},
    queries = decodeSubgroupQuery[#, order, generators, stateID] & /@ data;
    If[AnyTrue[queries, FailureQ], Return[First[Select[queries, FailureQ]]]];
    If[!DuplicateFreeQ[Lookup[queries, "QueryID", {}]],
        Return[makeFailure["InvalidSubgroups", "Subgroup query identities must be distinct."]]];
    items = Flatten[Lookup[queries, "Items", {}], 1];
    groups = GatherBy[items, #["SubgroupID"] &];
    fields = {"SubgroupID", "GeneratorWords", "Order", "Index", "Normal", "ConjugacyClassID", "ConjugacyClassSize"};
    If[AnyTrue[groups, Length[DeleteDuplicates[KeyTake[#, fields] & /@ #]] =!= 1 &],
        Return[makeFailure["InvalidSubgroups", "A subgroup identity has conflicting embedded data."]]];
    classGroups = GatherBy[items, #["ConjugacyClassID"] &];
    fields = {"Order", "Index", "Normal", "ConjugacyClassSize"};
    If[AnyTrue[classGroups, Length[DeleteDuplicates[KeyTake[#, fields] & /@ #]] =!= 1 ||
        Length[DeleteDuplicates[Select[Lookup[#, "Description"], StringQ]]] > 1 &],
        Return[makeFailure["InvalidSubgroups", "Subgroup class metadata or descriptions disagree."]]];
    Association[(#["QueryID"] -> #) & /@ queries]
];
decodeSubgroupData[___] := makeFailure["InvalidSubgroups", "Expected null or a subgroup query list."];

(*
    Summary: Check that subgroup enrichment preserves every previously accepted query and embedding.
    Parameters: candidate/accepted — decoded query associations or Missing[NotComputed].
    Options/defaults: Adding queries and filling absent descriptions are allowed.
    Returns: Boolean; general metadata/provenance does not change embedding correspondence.
    Effects: Pure.
    Failures: Removed/reordered items, changed IDs/words/filters or altered/dropped descriptions return False.
    Example: description enrichment keeps the original class representatives and their order.
    See also: publishGroupEnrichment; decodeSubgroupData.
*)
subgroupDataExtendsQ[candidate_, accepted_Missing] := AssociationQ[candidate] || candidate === accepted;
subgroupDataExtendsQ[candidate_Association, accepted_Association] := ContainsAll[Keys[candidate], Keys[accepted]] &&
    AllTrue[Keys[accepted], Function[id, With[{old = accepted[id], new = candidate[id]},
        KeyTake[old, {"QueryID", "Kind", "Filters", "Complete"}] ===
            KeyTake[new, {"QueryID", "Kind", "Filters", "Complete"}] &&
        Length[old["Items"]] === Length[new["Items"]] &&
        (old["Descriptions"] =!= "Complete" || new["Descriptions"] === "Complete") &&
        And @@ MapThread[Function[{a, b}, KeyDrop[a, "Description"] === KeyDrop[b, "Description"] &&
            (MissingQ[a["Description"]] || a["Description"] === b["Description"])], {old["Items"], new["Items"]}]
    ]]];
subgroupDataExtendsQ[___] := False;

True
