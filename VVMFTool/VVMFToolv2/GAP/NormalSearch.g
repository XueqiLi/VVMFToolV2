# Title: Bounded normal-subgroup searches of supplied presentations
# Summary: Search an fp parent without requiring it to be finite; certify finite quotients.
# Dependencies: Groups.g, Serialization.g; optional GAP package lins.
# See also: https://gap-packages.github.io/LINS/doc/chap2.html and chap3.html.

# Summary: Construct a presentation with its original generator alphabet, without a finiteness test.
# Parameters/defaults: spec is a typed presentation; no options or executable source.
# Returns: Parent/free groups, recorded generators and exact relators, or structured failure.
# Effects: Allocates finitely presented groups only; does not enumerate the parent.
# Failures: Malformed names/relators or nonpresentation input.
# Example: a one-generator empty-relator presentation represents the infinite cyclic group.
# See also: VVMF_NormalByIndex; finite construction in VVMF_Construct.
VVMF_PresentedGroup := function(spec)
    local free, state, relators, group;
    if not IsRecord(spec) or not IsBound(spec.type) or spec.type <> "presentation" or
        not IsBound(spec.names) or not VVMF_NamesQ(spec.names) or
        not IsBound(spec.relators) or not IsList(spec.relators) then
        return VVMF_Failure("InvalidPresentation","Expected a supplied typed presentation.");
    fi;
    free := FreeGroup(spec.names);
    state := rec(group := free, names := spec.names, generators := GeneratorsOfGroup(free));
    relators := List(spec.relators, word -> VVMF_Word(state,word));
    if ForAny(relators,VVMF_IsFailure) then
        return VVMF_Failure("InvalidPresentation","A parent relator is malformed.");
    fi;
    group := free / relators;
    return rec(group := group, names := spec.names, generators := GeneratorsOfGroup(group),
        free := free, relators := relators, construction := spec);
end;

# Summary: Initialize an up-to-index search with the unique subgroup of index one.
# Parameters/defaults: graph is a new LINS graph; no options.
# Returns: Nothing; sets the graph's selected-node collection.
# Effects: Includes the parent as a result, rather than waiting for a discovery callback.
# Failures: Internal callback; caller supplies a valid LINS graph.
# Example: an up-to-one search contains its parent even though no new node is discovered.
# See also: VVMF_NormalStopGraph; LINS InitGraph option.
VVMF_NormalInitGraph := function(graph)
    graph!.ComputedNormalSubgroups := [ValueGlobal("LinsRoot")(graph)];
end;

# Summary: Collect a newly found node and stop only after one result beyond the requested cap.
# Parameters/defaults: graph,parent,node are the LINS callback arguments; graph.VVMF_ResultCap
# is a positive integer or infinity supplied by the owning search.
# Returns: true when the lookahead proves truncation, otherwise false.
# Effects: Appends distinct nodes to the graph's computed collection.
# Failures: Internal callback with a valid initialized graph; no external input.
# Example: cap=1 stops on the second result, so an exhausted one-result search is complete.
# See also: VVMF_NormalInitGraph; VVMF_NormalByIndex.
VVMF_NormalStopGraph := function(graph,parent,node)
    if not node in graph!.ComputedNormalSubgroups then Add(graph!.ComputedNormalSubgroups,node); fi;
    return Length(graph!.ComputedNormalSubgroups) > graph!.VVMF_ResultCap;
end;

# Summary: Certify an embedded normal subgroup and its finite quotient on the parent's generators.
# Parameters/defaults: state is VVMF_PresentedGroup output; subgroup is a LINS result;
# index is its positive index; small requests GAP SmallGeneratingSet.
# Returns: Exact index, subgroup-generator words and quotient presentation, or Failure.
# Effects: May reduce a generating set, test subgroup equality and compute the quotient order/map.
# Failures: Wrong index, failed normality, changed subgroup under reduction, word or quotient mismatch.
# Example: the index-three subgroup of the infinite cyclic parent has quotient relator a^3.
# Remarks: Returned generators generate the subgroup itself, not merely its normal closure.
# Adding them to the parent relators presents the quotient because normality is checked.
# SmallGeneratingSet is not a claim of a minimal generating set.
# See also: FactorCosetAction; VVMF_WordSyllables.
VVMF_NormalItem := function(state,subgroup,index,small)
    local generators, generated, words, i, quotient, map, images, check, relators;
    if not IsRecord(state) or not IsBound(state.group) or not IsGroup(subgroup) or
        not IsPosInt(index) or not IsBool(small) then
        return VVMF_Failure("InvalidNormalSubgroup","Expected a presented parent and subgroup request.");
    fi;
    if not IsSubgroup(state.group,subgroup) or Index(state.group,subgroup) <> index or
        not IsNormal(state.group,subgroup) then
        return VVMF_Failure("InvalidNormalSubgroup","The actual normal subgroup or index failed verification.");
    fi;
    if small then generators := SmallGeneratingSet(subgroup);
    else generators := GeneratorsOfGroup(subgroup); fi;
    generated := Subgroup(state.group,generators);
    if generated <> subgroup then
        return VVMF_Failure("InvalidNormalSubgroup","Reduction changed the embedded subgroup.");
    fi;
    words := List(generators, element -> VVMF_WordSyllables(UnderlyingElement(element),state.names));
    if ForAny(words,VVMF_IsFailure) then
        return VVMF_Failure("WordRecoveryFailed","Cannot encode the subgroup's ambient words.");
    fi;
    for i in [1..Length(words)] do
        if VVMF_Word(state,words[i]) <> generators[i] then
            return VVMF_Failure("WordRecoveryFailed","A subgroup word changed its ambient element.");
        fi;
    od;
    relators := Concatenation(state.construction.relators,words);
    quotient := VVMF_PresentedGroup(rec(type := "presentation",names := state.names,relators := relators));
    if VVMF_IsFailure(quotient) then return quotient; fi;
    if IsEmpty(state.generators) then
        map := GroupHomomorphismByImages(state.group,Group(()),[],[]);
    else map := FactorCosetAction(state.group,subgroup); fi;
    if map = fail or Size(Image(map)) <> index or Kernel(map) <> subgroup then
        return VVMF_Failure("InvalidQuotient","The native quotient map failed verification.");
    fi;
    images := List(state.generators,element -> Image(map,element));
    check := GroupHomomorphismByImages(quotient.group,Image(map),quotient.generators,images);
    if check = fail or Size(quotient.group) <> index or not IsBijective(check) then
        return VVMF_Failure("InvalidQuotient","The returned quotient relators do not give the prescribed quotient.");
    fi;
    return rec(index := String(index),generatorWords := words,generatorSemantics := "Subgroup",
        quotientPresentation := quotient.construction);
end;

# Summary: Compute all or a capped selection of normal subgroups at a bounded index.
# Parameters/defaults: request has presentation, bound decimal string, indexMode Exact/UpTo,
# maxResults positive decimal string or fail (uncapped), and smallGenerators Boolean.
# Returns: Search state containing parent, graph, selected subgroups and exact result, or Failure.
# Effects: Loads lins, runs one sequential algorithm and verifies every returned quotient.
# Failures: Invalid request, unavailable dependency, unsupported library bound or invalid results.
# Resource interruption is owned by the enclosing process; it never implies Complete=true.
# Example: <a | > at exact index 3 has one normal subgroup and a C3 quotient.
# Remarks: Capped searches ask for one extra result to distinguish a complete boundary case.
# Index one is handled explicitly: the LINS exact-index callback does not visit the root.
# No Size/IsFinite call is made on the potentially infinite parent.
# See also: LINS LowIndexNormalSubgroupsSearchForIndex; VVMF_NormalItem.
VVMF_NormalByIndex := function(request)
    local state, bound, cap, graph, nodes, subgroups, items, complete, options, i, result;
    if not IsRecord(request) or not IsBound(request.presentation) or not IsBound(request.bound) or
        not IsBound(request.indexMode) or not request.indexMode in ["Exact","UpTo"] or
        not IsBound(request.maxResults) or not IsBound(request.smallGenerators) or
        not IsBool(request.smallGenerators) then
        return VVMF_Failure("InvalidNormalSearch","Invalid bounded normal-subgroup request.");
    fi;
    bound := VVMF_DecodeInteger(request.bound);
    if request.maxResults = fail then cap := infinity;
    else cap := VVMF_DecodeInteger(request.maxResults); fi;
    if VVMF_IsFailure(bound) or not IsPosInt(bound) or
        (cap <> infinity and (VVMF_IsFailure(cap) or not IsPosInt(cap))) then
        return VVMF_Failure("InvalidNormalSearch","The bound and result cap must be positive integers.");
    fi;
    state := VVMF_PresentedGroup(request.presentation);
    if VVMF_IsFailure(state) then return state; fi;
    if LoadPackage("lins") = fail then
        return VVMF_Failure("DependencyUnavailable","Bounded normal-subgroup search requires LINS.");
    fi;
    if not IsBoundGlobal("LINS_MaxIndex") or bound > ValueGlobal("LINS_MaxIndex") then
        return VVMF_Failure("UnsupportedIndexBound","The bound exceeds the installed LINS completeness range.");
    fi;
    if bound = 1 then
        graph := fail;
        subgroups := [state.group];
    elif request.indexMode = "Exact" then
        graph := ValueGlobal("LowIndexNormalSubgroupsSearchForIndex")(state.group,bound,cap+1);
        nodes := ValueGlobal("ComputedNormalSubgroups")(graph);
        subgroups := List(nodes,ValueGlobal("Grp"));
    else
        options := rec(InitGraph := function(value)
                VVMF_NormalInitGraph(value); value!.VVMF_ResultCap := cap;
            end, DoTerminate := VVMF_NormalStopGraph);
        graph := ValueGlobal("LowIndexNormalSubgroupsSearch")(state.group,bound,options);
        nodes := ValueGlobal("ComputedNormalSubgroups")(graph);
        subgroups := List(nodes,ValueGlobal("Grp"));
    fi;
    complete := Length(subgroups) <= cap;
    if not complete then subgroups := subgroups{[1..cap]}; fi;
    items := [];
    for i in [1..Length(subgroups)] do
        result := VVMF_NormalItem(state,subgroups[i],Index(state.group,subgroups[i]),request.smallGenerators);
        if VVMF_IsFailure(result) then return result; fi;
        if (request.indexMode = "Exact" and result.index <> request.bound) or
            VVMF_DecodeInteger(result.index) > bound then
            return VVMF_Failure("InvalidNormalSearch","A search result has an unrequested index.");
        fi;
        Add(items,result);
    od;
    result := rec(presentation := request.presentation,bound := request.bound,indexMode := request.indexMode,
        maxResults := request.maxResults,smallGenerators := request.smallGenerators,
        complete := complete,capReached := not complete,items := items,method := "LINS",
        linsVersion := PackageInfo("lins")[1].Version);
    return rec(parent := state,graph := graph,subgroups := subgroups,result := result);
end;

# Summary: Run a bounded search and atomically write its independently checked mathematical result.
# Parameters/defaults: request includes requestID and operation NormalSubgroupsByIndex;
# resultPath is a new coordinator-owned path. Parent need not be finite.
# Returns: resultReady packet or reported structured failure.
# Effects: Runs LINS, writes inert JSON and emits one nonce-matched completion packet.
# Failures: Search/validation/write failures never emit resultReady; native errors terminate the worker.
# Example: the coordinator accepts the artifact only after the matching resultReady packet.
# Remarks: This value-returning search owns no finite Group object or retained group workspace.
# See also: VVMF_NormalByIndex; VVMF_WriteJSON; Kernel/NormalSearch.wl.
VVMF_RunNormalSearch := function(request,resultPath)
    local state, envelope, written, packet;
    if not IsRecord(request) or not IsBound(request.requestID) or not IsString(request.requestID) or
        not IsBound(request.operation) or request.operation <> "NormalSubgroupsByIndex" then
        return ValueGlobal("VVMF_ProtocolFailure")(
            VVMF_Failure("InvalidNormalSearch","Expected a bounded-search request identity."),rec());
    fi;
    state := VVMF_NormalByIndex(request);
    if VVMF_IsFailure(state) then return ValueGlobal("VVMF_ProtocolFailure")(state,request); fi;
    envelope := rec(schemaVersion := 1,requestID := request.requestID,operation := request.operation,
        result := state.result,producer := ValueGlobal("VVMF_Producer")());
    written := ValueGlobal("VVMF_WriteJSON")(resultPath,envelope);
    if VVMF_IsFailure(written) then return ValueGlobal("VVMF_ProtocolFailure")(written,request); fi;
    packet := rec(type := "resultReady",requestID := request.requestID,resultPath := resultPath);
    ValueGlobal("VVMF_Emit")(packet);
    return packet;
end;
