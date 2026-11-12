# Title: Optional finite subgroup queries
# Summary: Compute embedded subgroups with stable identities and descriptions shared by conjugacy class.
# Dependencies: Groups, Serialization, CharacterTransfer, ResultExport; original finite group and recorded generators.
# Contracts: Computation occurs in a verified model and returns embeddings in the original group.
# See also: https://gap-system.github.io/gap/doc/ref/chap39_mj.html

# Summary: Validate and decode one finite subgroup query.
# Parameters/defaults: query has id, kind, order/index decimal strings or fail, and descriptions.
# Returns: Decoded query record, or InvalidSubgroupQuery.
# Effects: Pure; no subgroup or description computation.
# Failures: Extra/missing fields, unsupported kind, invalid filter or nonboolean descriptions.
# Example: kind="Normal", order="4", index=fail selects normal subgroups of order four.
# See also: VVMF_Subgroups; VVMF_ExportSubgroups.
VVMF_SubgroupQuery := function(query)
    local decoded, key, value;
    if not IsRecord(query) or Set(RecNames(query)) <> ["descriptions","id","index","kind","order"] or
        not IsString(query.id) or Length(query.id) = 0 or
        not query.kind in ["ConjugacyClasses","All","Normal"] or
        not query.descriptions in [true,false] then
        return VVMF_Failure("InvalidSubgroupQuery","Malformed subgroup query.");
    fi;
    decoded := ShallowCopy(query);
    for key in ["order","index"] do
        if query.(key) <> fail then
            value := VVMF_DecodeInteger(query.(key));
            if VVMF_IsFailure(value) or value < 1 then
                return VVMF_Failure("InvalidSubgroupQuery","Subgroup filters must be positive integers or null.");
            fi;
            decoded.(key) := value;
        fi;
    od;
    return decoded;
end;

# Summary: Find or register one actual embedded subgroup in an owned candidate.
# Parameters/defaults: state has mutable subgroup registries and request identities; subgroup is in G.
# Returns: Registry index or invalid-embedding/word failure.
# Effects: Recovers words once per embedding; computes a conjugacy-class identity/size once per class.
# Failures: Out-of-group embeddings or words that do not generate the actual subgroup.
# Example: distinct order-two subgroups of S3 have different IDs but the same class ID.
# Remarks: Caller supplies candidate-owned registry lists so failures cannot mutate accepted queries.
# See also: VVMF_Subgroups; VVMF_EncodeWords.
VVMF_RegisterSubgroup := function(state,subgroup)
    local position, words, class, order, id;
    if not IsGroup(subgroup) or not IsSubgroup(state.group,subgroup) then
        return VVMF_Failure("InvalidSubgroup","Expected a subgroup embedded in the original group.");
    fi;
    position := PositionProperty(state.subgroupRegistry,entry -> entry.group = subgroup);
    if position <> fail then return position; fi;
    words := VVMF_EncodeWords(state,GeneratorsOfGroup(subgroup));
    if VVMF_IsFailure(words) then return words; fi;
    if Group(List(words,word -> VVMF_Word(state,word)),One(state.group)) <> subgroup then
        return VVMF_Failure("InvalidSubgroup","Exported generators do not recover the subgroup embedding.");
    fi;
    order := Size(subgroup);
    class := PositionProperty(state.subgroupClasses,entry -> entry.order = order and
        IsConjugate(state.group,entry.group,subgroup));
    if class = fail then
        id := Concatenation(state.stateID,":subgroup-class:",state.requestID,":",String(Length(state.subgroupClasses)+1));
        Add(state.subgroupClasses,rec(id := id,group := subgroup,order := order,
            size := Index(state.group,Normalizer(state.group,subgroup)),description := fail));
        class := Length(state.subgroupClasses);
    fi;
    id := Concatenation(state.stateID,":subgroup:",state.requestID,":",String(Length(state.subgroupRegistry)+1));
    Add(state.subgroupRegistry,rec(id := id,group := subgroup,words := words,class := class));
    return Length(state.subgroupRegistry);
end;

# Summary: Compute a complete filtered collection using an explicitly selected native route.
# Parameters/defaults: state is finite and identified; query is VVMF_SubgroupQuery input;
# method is GAP, ClassExpansion or ClassFilter; model is Original, Permutation or PC.
# Returns: A complete query record, or a structured failure without replacing existing queries.
# Effects: Enumerates only requested kinds, transports subgroup generators through a verified
# model map, and caches descriptions once per conjugacy class only when requested.
# Failures: Inapplicable methods/models, malformed filters or failed embedding-word recovery.
# Example: ClassExpansion returns all six embedded subgroups of S3; class mode returns four.
# Remarks: Native GAP exceptions terminate the isolated worker. The coordinator owns time/memory
# bounds and retries. A complete empty filtered collection is distinct from uncomputed data.
# See also: ConjugacyClassesSubgroups; AllSubgroups; NormalSubgroups; VVMF_ExportSubgroups.
VVMF_Subgroups := function(state,query,method,modelName)
    local decoded, model, groups, classes, candidate, indices, subgroup, original, position,
        class, result, prior;
    decoded := VVMF_SubgroupQuery(query);
    if VVMF_IsFailure(decoded) then return decoded; fi;
    if not method in ["GAP","ClassExpansion","ClassFilter"] or
        (decoded.kind = "ConjugacyClasses" and method <> "GAP") or
        (decoded.kind = "All" and not method in ["GAP","ClassExpansion"]) or
        (decoded.kind = "Normal" and not method in ["GAP","ClassFilter"]) then
        return VVMF_Failure("InapplicableMethod","The subgroup route does not supply this query kind.");
    fi;
    if not IsRecord(state) or not IsBound(state.group) or not IsBound(state.stateID) or
        not IsBound(state.requestID) then
        return VVMF_Failure("InvalidState","An identified finite group is required.");
    fi;
    if IsBound(state.subgroupQueries) then
        prior := PositionProperty(state.subgroupQueries,entry -> entry.query.id = query.id);
        if prior <> fail then
            result := StructuralCopy(state.subgroupQueries[prior]);
            if result.query.kind <> query.kind or result.query.order <> query.order or
                result.query.index <> query.index then
                return VVMF_Failure("StateConflict","A subgroup query identity cannot change filters.");
            fi;
            if result.query.descriptions or not query.descriptions then return result; fi;
            classes := List(state.subgroupClasses,ShallowCopy);
            for position in result.indices do
                class := state.subgroupRegistry[position].class;
                if classes[class].description = fail then
                    classes[class].description := StructureDescription(classes[class].group);
                    if not IsString(classes[class].description) then
                        return VVMF_Failure("DescriptionFailed","No subgroup description was produced.");
                    fi;
                fi;
            od;
            result.query.descriptions := true;
            candidate := StructuralCopy(state.subgroupQueries);
            candidate[prior] := result;
            state.subgroupQueries := candidate;
            state.subgroupClasses := classes;
            return result;
        fi;
    fi;
    model := VVMF_Model(state,modelName);
    if VVMF_IsFailure(model) then return model; fi;
    if decoded.kind = "ConjugacyClasses" then
        groups := List(ConjugacyClassesSubgroups(model.group),Representative);
    elif decoded.kind = "All" and method = "GAP" then
        groups := AllSubgroups(model.group);
    elif decoded.kind = "All" then
        groups := Concatenation(List(ConjugacyClassesSubgroups(model.group),Elements));
    elif method = "GAP" then
        groups := NormalSubgroups(model.group);
    else
        classes := Filtered(ConjugacyClassesSubgroups(model.group),class -> Size(class) = 1);
        groups := List(classes,Representative);
    fi;
    groups := Filtered(groups,subgroup -> (decoded.order = fail or Size(subgroup) = decoded.order) and
        (decoded.index = fail or Index(model.group,subgroup) = decoded.index));
    candidate := ShallowCopy(state);
    candidate.subgroupRegistry := [];
    candidate.subgroupClasses := [];
    candidate.subgroupQueries := [];
    if IsBound(state.subgroupRegistry) then
        candidate.subgroupRegistry := List(state.subgroupRegistry,ShallowCopy);
        candidate.subgroupClasses := List(state.subgroupClasses,ShallowCopy);
        candidate.subgroupQueries := StructuralCopy(state.subgroupQueries);
    fi;
    indices := [];
    for subgroup in groups do
        original := Group(List(GeneratorsOfGroup(subgroup),
            element -> PreImagesRepresentative(model.fromOriginal,element)),One(state.group));
        if decoded.kind = "Normal" and not IsNormal(state.group,original) then
            return VVMF_Failure("InvalidSubgroup","A normal-subgroup route returned a nonnormal embedding.");
        fi;
        position := VVMF_RegisterSubgroup(candidate,original);
        if VVMF_IsFailure(position) then return position; fi;
        Add(indices,position);
        class := candidate.subgroupRegistry[position].class;
        if query.descriptions and candidate.subgroupClasses[class].description = fail then
            candidate.subgroupClasses[class].description := StructureDescription(original);
            if not IsString(candidate.subgroupClasses[class].description) then
                return VVMF_Failure("DescriptionFailed","No subgroup structure description was produced.");
            fi;
        fi;
    od;
    if Length(Set(indices)) <> Length(indices) then
        return VVMF_Failure("InvalidSubgroup","The route returned repeated subgroup embeddings.");
    fi;
    result := rec(query := StructuralCopy(query),indices := indices,complete := true,
        provenance := rec(stateID := state.stateID,requestID := state.requestID,method := method,model := modelName));
    prior := PositionProperty(candidate.subgroupQueries,entry -> entry.query.id = query.id);
    if prior = fail then Add(candidate.subgroupQueries,result);
    else
        if candidate.subgroupQueries[prior].query.kind <> query.kind or
            candidate.subgroupQueries[prior].query.order <> query.order or
            candidate.subgroupQueries[prior].query.index <> query.index or
            Set(candidate.subgroupQueries[prior].indices) <> Set(indices) then
            return VVMF_Failure("StateConflict","A completed subgroup query cannot change its embeddings or filters.");
        fi;
        result.indices := candidate.subgroupQueries[prior].indices;
        candidate.subgroupQueries[prior] := result;
    fi;
    state.subgroupRegistry := candidate.subgroupRegistry;
    state.subgroupClasses := candidate.subgroupClasses;
    state.subgroupQueries := candidate.subgroupQueries;
    return result;
end;

# Summary: Revalidate and serialize all accepted subgroup queries without losing embeddings.
# Parameters/defaults: state is an identified group with optional subgroup registries.
# Returns: fail when uncomputed, a list of complete typed query records, or a validation failure.
# Effects: Evaluates generator words and checks actual subgroup/class invariants; no descriptions
# are newly computed during export. Each class-mode item is its chosen embedded representative.
# Failures: Changed native embeddings, class correspondence, missing requested descriptions or
# inconsistent filters/completeness cannot produce a successful envelope.
# Example: an empty computed normal-order-four query exports items=[] and complete=true.
# See also: VVMF_Subgroups; ResultExport.g; Schemas/GroupResult.md.
VVMF_ExportSubgroups := function(state)
    local results, query, decoded, items, index, entry, class, order, normal, item, words;
    if not IsBound(state.subgroupQueries) then return fail; fi;
    results := [];
    for query in state.subgroupQueries do
        decoded := VVMF_SubgroupQuery(query.query);
        if VVMF_IsFailure(decoded) then return decoded; fi;
        items := [];
        for index in query.indices do
            entry := state.subgroupRegistry[index];
            class := state.subgroupClasses[entry.class];
            words := List(entry.words,word -> VVMF_Word(state,word));
            if ForAny(words,VVMF_IsFailure) or
                Group(words,One(state.group)) <> entry.group or
                not IsConjugate(state.group,class.group,entry.group) or
                Index(state.group,Normalizer(state.group,entry.group)) <> class.size then
                return VVMF_Failure("InvalidSubgroup","Stored subgroup words or class correspondence changed.");
            fi;
            order := Size(entry.group);
            normal := IsNormal(state.group,entry.group);
            if (decoded.order <> fail and order <> decoded.order) or
                (decoded.index <> fail and state.order / order <> decoded.index) or
                (decoded.kind = "Normal" and not normal) then
                return VVMF_Failure("InvalidSubgroup","Stored subgroup does not satisfy the query filters.");
            fi;
            item := rec(id := entry.id,generatorWords := List(entry.words,word -> VVMF_WordIDs(state,word)),
                order := String(order),index := String(state.order/order),normal := normal,
                classID := class.id,classSize := String(class.size),description := fail);
            if decoded.descriptions then
                if not IsString(class.description) then
                    return VVMF_Failure("DescriptionFailed","A requested subgroup description is absent.");
                fi;
                item.description := class.description;
            fi;
            Add(items,item);
        od;
        if query.complete <> true or Length(Set(List(items,item -> item.id))) <> Length(items) or
            (decoded.kind = "ConjugacyClasses" and
                Length(Set(List(items,item -> item.classID))) <> Length(items)) then
            return VVMF_Failure("InvalidSubgroup","The query contains duplicate items/classes or is incomplete.");
        fi;
        Add(results,rec(query := StructuralCopy(query.query),items := items,complete := true,
            provenance := StructuralCopy(query.provenance)));
    od;
    return results;
end;

# Summary: Restore certified subgroup embeddings through a previously proven generator map.
# Parameters/defaults: state is rebound to accepted generator identities; source is fail or a
# validated, independently trusted exported subgroup-query list. No source text is executed.
# Returns: true or a correspondence failure, with preceding query state preserved on failure.
# Effects: Rebuilds actual subgroups from saved words, verifies order/normality/classes and
# restores existing subgroup/class IDs and descriptions without enumerating the subgroup lattice.
# Failures: Changed embeddings, conflicting IDs, invariants or unequal native reexport.
# Example: an evicted S3 workspace recovers the six saved embeddings with unchanged IDs.
# Remarks: Completeness is transported through the established group isomorphism. This helper
# cannot establish completeness or provenance for an arbitrary imported collection by itself.
# See also: VVMF_RebindGroup; VVMF_RegisterSubgroup; VVMF_ExportSubgroups.
VVMF_RestoreSubgroups := function(state,source)
    local candidate, query, decoded, indices, item, elements, subgroup, position, known,
        classCount, class, entry, words, exported;
    if source = fail then return true; fi;
    if not IsList(source) then return VVMF_Failure("InvalidSubgroup","Expected retained subgroup query data."); fi;
    candidate := ShallowCopy(state);
    candidate.subgroupRegistry := [];
    candidate.subgroupClasses := [];
    candidate.subgroupQueries := [];
    if not IsBound(candidate.requestID) then candidate.requestID := "reconstruction"; fi;
    for query in source do
        decoded := VVMF_SubgroupQuery(query.query);
        if VVMF_IsFailure(decoded) then return decoded; fi;
        indices := [];
        for item in query.items do
            elements := List(item.generatorWords,word -> VVMF_ResultWord(candidate,word));
            if ForAny(elements,VVMF_IsFailure) then
                return VVMF_Failure("InvalidSubgroup","A retained subgroup generator word is invalid.");
            fi;
            subgroup := Group(elements,One(state.group));
            known := PositionProperty(candidate.subgroupRegistry,entry -> entry.group = subgroup);
            classCount := Length(candidate.subgroupClasses);
            position := VVMF_RegisterSubgroup(candidate,subgroup);
            if VVMF_IsFailure(position) then return position; fi;
            entry := candidate.subgroupRegistry[position];
            class := candidate.subgroupClasses[entry.class];
            if known = fail then
                if ForAny([1..Length(candidate.subgroupRegistry)],i -> i <> position and
                    candidate.subgroupRegistry[i].id = item.id) then
                    return VVMF_Failure("InvalidSubgroup","A retained subgroup ID describes different embeddings.");
                fi;
                entry.id := item.id;
                entry.words := List(item.generatorWords,word -> List(word,
                    pair -> [state.names[Position(state.generatorIDs,pair[1])],pair[2]]));
            elif entry.id <> item.id then
                return VVMF_Failure("InvalidSubgroup","The same embedding has conflicting retained identities.");
            fi;
            if entry.class > classCount then
                if ForAny([1..Length(candidate.subgroupClasses)],i -> i <> entry.class and
                    candidate.subgroupClasses[i].id = item.classID) then
                    return VVMF_Failure("InvalidSubgroup","A retained class ID describes nonconjugate subgroups.");
                fi;
                class.id := item.classID;
            elif class.id <> item.classID then
                return VVMF_Failure("InvalidSubgroup","Conjugate embeddings have conflicting class identities.");
            fi;
            if Size(subgroup) <> VVMF_DecodeInteger(item.order) or
                Index(state.group,subgroup) <> VVMF_DecodeInteger(item.index) or
                IsNormal(state.group,subgroup) <> item.normal or
                class.size <> VVMF_DecodeInteger(item.classSize) then
                return VVMF_Failure("InvalidSubgroup","A retained subgroup invariant failed in the reconstructed group.");
            fi;
            if item.description <> fail then
                if not IsString(item.description) or
                    (class.description <> fail and class.description <> item.description) then
                    return VVMF_Failure("InvalidSubgroup","Retained descriptions disagree within a subgroup class.");
                fi;
                class.description := item.description;
            fi;
            Add(indices,position);
        od;
        Add(candidate.subgroupQueries,rec(query := StructuralCopy(query.query),indices := indices,
            complete := query.complete,provenance := StructuralCopy(query.provenance)));
    od;
    exported := VVMF_ExportSubgroups(candidate);
    if VVMF_IsFailure(exported) then return exported; fi;
    if exported <> source then
        return VVMF_Failure("InvalidSubgroup","Reconstructed subgroup data differ from the accepted collection.");
    fi;
    state.subgroupRegistry := candidate.subgroupRegistry;
    state.subgroupClasses := candidate.subgroupClasses;
    state.subgroupQueries := candidate.subgroupQueries;
    return true;
end;

# Summary: Recognize the exact library AllSubgroups body whose work is class expansion.
# Parameters/defaults: implementation is a GAP function; no options.
# Returns: true only for an identical function rendering, otherwise false.
# Effects: Pure; never executes the supplied function.
# Failures: Unknown, changed or opaque functions conservatively return false.
# Example: GAP 4.15.1 AllSubgroups returns true; an arbitrary replacement returns false.
# Remarks: The reference body is GAP lib/teaching.g's implementation. It is used only
# to avoid redundant algorithm attempts, never to parse or certify mathematical data.
# See also: Kernel/GroupJobs.wl groupDescriptors.
VVMF_AllSubgroupsClassExpansionQ := function(implementation)
    if not IsFunction(implementation) then return false; fi;
    return String(implementation) = String(function(G)
        local cl;
        cl:=ConjugacyClassesSubgroups(G);
        if Sum(cl,Size)>10^5 then
            Info(InfoPerformance,1,"G has ",Sum(cl,Size),
                " subgroups. Writing them all down\n",
                "takes lots of memory and time. Use `ConjugacyClassesSubgroups' to get\n",
                "classes up to conjugaction action, this will be more efficient!");
        fi;
        return Concatenation(List(cl,AsSSortedList));
    end);
end;
