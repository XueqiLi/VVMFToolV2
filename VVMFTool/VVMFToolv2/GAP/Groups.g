# Title: Finite-group construction and computational models
# Summary: Preserve recorded generators and verified maps independently of group labels.
# Dependencies: Diagnostics.g, Scalars.g; smallgrp for catalogue construction/identification.
# Contracts: Caller supplies the typed schema from GroupInput.wl. Algorithms run only
# inside an owned, resource-bounded worker. Finiteness may require substantial computation.
# See also: VVMFArch/step1Plan.md; GAP reference chapters 39, 43 and 47.

# Summary: Validate the ordered unique names used by typed group inputs.
# Parameters: names is a list of strings.
# Returns: Boolean, including true for an empty generating set.
# Effects: Pure; invalid types return false.
# Example: VVMF_NamesQ(["a","b_2"]) = true.
# See also: VVMF_Construct; VVMF_Word.
VVMF_NamesQ := function(names)
    local letters, allowed;
    letters := "abcdefghijklmnopqrstuvwxyzABCDEFGHIJKLMNOPQRSTUVWXYZ";
    allowed := Concatenation(letters, "0123456789_");
    return IsList(names) and Length(Set(names)) = Length(names) and
        ForAll(names, name -> IsString(name) and Length(name) > 0 and
            name[1] in letters and ForAll(name, char -> char in allowed));
end;

# Summary: Evaluate typed syllables in exactly the recorded ordered generators.
# Parameters: state has group, names and generators; syllables is a list of name/exponent pairs.
# Returns: An actual group element or structured failure.
# Effects: Pure except GAP's ordinary group-element caches.
# Failures: Unknown generator, malformed pair or noncanonical exponent string.
# Example: VVMF_Word(state,[]) = One(state.group).
# Remarks: The identity is One(group), including for matrices over nontrivial rings.
# See also: VVMF_Construct; word recovery in Serialization.g.
VVMF_Word := function(state, syllables)
    local word, syllable, position, exponent;
    if not IsRecord(state) or not IsBound(state.group) or
        not IsBound(state.names) or not IsBound(state.generators) or not IsList(syllables) then
        return VVMF_Failure("InvalidWord", "Expected recorded generators and word syllables.");
    fi;
    word := One(state.group);
    for syllable in syllables do
        if not IsList(syllable) or Length(syllable) <> 2 or not IsString(syllable[1]) then
            return VVMF_Failure("InvalidWord", "Malformed word syllable.");
        fi;
        position := Position(state.names, syllable[1]);
        exponent := VVMF_DecodeInteger(syllable[2]);
        if position = fail or VVMF_IsFailure(exponent) then
            return VVMF_Failure("InvalidWord", "Unknown generator or invalid exponent.");
        fi;
        word := word * state.generators[position]^exponent;
    od;
    return word;
end;

# Summary: Validate generation/finiteness and create the common base-state record.
# Parameters: group is a GAP group, generators the recorded ordered elements, names
# the same-length name list, construction the retained input record.
# Returns: State with ok=true, group/order/generators/models; or structured failure.
# Effects: May compute finiteness, size and an available catalogue ID; initializes models.
# Failures: Wrong types, nongenerating lists, nonfinite group. Undecided calculations
# remain subject to the worker time/resource limit, never returned as a finite group.
# Example: VVMF_FinishConstruction(Group(()),[],[],rec(type:="permutation")).order = 1.
# See also: VVMF_Construct; VVMF_ConstructRaw; VVMF_Model.
VVMF_FinishConstruction := function(group, generators, names, construction)
    local state, order, catalogueID;
    if not IsGroup(group) or not IsList(generators) or not VVMF_NamesQ(names) or
        Length(generators) <> Length(names) then
        return VVMF_Failure("InvalidConstruction", "Expected a group and matching recorded generators.");
    fi;
    if not ForAll(generators, x -> x in group) then
        return VVMF_Failure("InvalidGenerators", "A recorded generator is outside the supplied group.");
    fi;
    if not IsFinite(group) then
        return VVMF_Failure("NonfiniteGroup", "The supplied group is not finite.");
    fi;
    if Group(generators, One(group)) <> group then
        return VVMF_Failure("NongeneratingList", "The recorded elements do not generate the group.");
    fi;
    order := Size(group);
    if not IsInt(order) or order < 1 then
        return VVMF_Failure("InvalidOrder", "A positive finite group order was not established.");
    fi;
    catalogueID := fail;
    if IsBound(IdGroupsAvailable) and IdGroupsAvailable(order) then
        catalogueID := IdGroup(group);
    fi;
    state := rec(ok := true, group := group, generators := ShallowCopy(generators),
        names := ShallowCopy(names), construction := construction, order := order,
        catalogueID := catalogueID, models := rec(), revision := 0);
    state.models.Original := rec(group := group, fromOriginal := IdentityMapping(group),
        generators := ShallowCopy(generators), verified := true);
    return state;
end;

# Summary: Construct exact matrices in their declared GAP coefficient domain.
# Parameters: spec is a validated matrix schema with domain and scalar-encoded matrices.
# Returns: rec(group,generators), or structured failure.
# Effects: Constructs matrices/group; no finiteness claim is made by this helper.
# Failures: Unsupported/invalid domain, matrix shape, scalar membership or invertibility.
# Example: a unipotent 2 by 2 matrix over IntegersMod(4) has order 4, not infinite order.
# Remarks: Every finite-domain entry is explicitly multiplied by One(ring); passing
# the ring to ImmutableMatrix alone does not coerce ordinary integer entries.
# See also: VVMF_Construct; MatrixGroupSpecification in Kernel/GroupInput.wl.
VVMF_MatrixInput := function(spec)
    local domain, dimension, ring, matrices, matrix, decoded, row, values, value, determinant;
    domain := spec.domain;
    if not IsRecord(domain) or not IsBound(domain.Type) or
        not IsBound(domain.Dimension) or not IsInt(domain.Dimension) or domain.Dimension < 1 then
        return VVMF_Failure("InvalidDomain", "Missing or invalid matrix dimension.");
    fi;
    dimension := domain.Dimension;
    if domain.Type = "Rationals" then ring := Rationals;
    elif domain.Type = "Cyclotomics" then ring := Cyclotomics;
    elif domain.Type = "PrimeField" then
        if not IsBound(domain.Characteristic) or not IsInt(domain.Characteristic) or
            domain.Characteristic < 2 or not IsPrimeInt(domain.Characteristic) then
            return VVMF_Failure("InvalidDomain", "Expected a prime characteristic.");
        fi;
        ring := GF(domain.Characteristic);
    elif domain.Type = "IntegersMod" then
        if not IsBound(domain.Modulus) or not IsInt(domain.Modulus) or domain.Modulus < 2 then
            return VVMF_Failure("InvalidDomain", "Expected a modulus of at least two.");
        fi;
        ring := ZmodnZ(domain.Modulus);
    else
        return VVMF_Failure("UnsupportedDomain", "Unsupported matrix coefficient domain.");
    fi;
    matrices := [];
    for matrix in spec.generators do
        if not IsList(matrix) or Length(matrix) <> dimension or
            not ForAll(matrix, row -> IsList(row) and Length(row) = dimension) then
            return VVMF_Failure("InvalidMatrix", "Generator matrices must share the declared dimension.");
        fi;
        decoded := [];
        for row in matrix do
            values := [];
            for value in row do
                value := VVMF_DecodeScalar(value);
                if VVMF_IsFailure(value) then return value; fi;
                if domain.Type in ["PrimeField", "IntegersMod"] then
                    if not IsInt(value) then
                        return VVMF_Failure("InvalidDomain", "Finite-domain inputs require integer entries.");
                    fi;
                    value := value * One(ring);
                elif domain.Type = "Rationals" and not IsRat(value) then
                    return VVMF_Failure("InvalidDomain", "A matrix entry is not rational.");
                fi;
                Add(values, value);
            od;
            Add(decoded, values);
        od;
        matrix := ImmutableMatrix(ring, decoded);
        determinant := DeterminantMat(matrix);
        if not IsUnit(ring, determinant) then
            return VVMF_Failure("NoninvertibleGenerator", "A matrix determinant is not a unit.");
        fi;
        Add(matrices, matrix);
    od;
    return rec(group := Group(matrices, IdentityMat(dimension, ring)), generators := matrices);
end;

# Summary: Construct a group from an executable-free typed specification.
# Parameters: spec follows GroupInput.wl's validated JSON schema.
# Returns: Finite base state or structured failure; required characters are computed later.
# Effects: May load smallgrp and run finite-group construction/identification algorithms.
# Failures: Invalid schema/catalogue index, unsupported domain, nonfinite construction.
# Example: VVMF_Construct(rec(type:="catalogue",catalogue:="CyclicGroup",key:="3")).order = 3.
# Remarks: No source evaluation occurs. Original relators and recorded generator order
# remain available even when later algorithms use isomorphic computational models.
# See also: VVMF_FinishConstruction; VVMF_Model; BuildGroup in the stage-1 plan.
VVMF_Construct := function(spec)
    local group, generators, names, free, state, relators, key, decoded, cycles,
        permutation, images, cycle, points, degree, i, family;
    if not IsRecord(spec) or not IsBound(spec.type) then
        return VVMF_Failure("InvalidSpecification", "Expected a typed construction record.");
    fi;
    if spec.type = "catalogue" then
        if not IsBound(spec.catalogue) or not IsBound(spec.key) then
            return VVMF_Failure("InvalidSpecification", "Missing catalogue fields.");
        fi;
        if spec.catalogue = "SmallGroup" then
            if not IsList(spec.key) or Length(spec.key) <> 2 then
                return VVMF_Failure("InvalidCatalogueKey", "Expected order and catalogue index.");
            fi;
            key := List(spec.key, VVMF_DecodeInteger);
            if ForAny(key, VVMF_IsFailure) or Minimum(key) < 1 then
                return VVMF_Failure("InvalidCatalogueKey", "Invalid order or catalogue index.");
            fi;
            if LoadPackage("smallgrp") = fail or not SmallGroupsAvailable(key[1]) then
                return VVMF_Failure("CatalogueUnavailable", "The requested small-group catalogue is unavailable.");
            fi;
            if key[2] > NumberSmallGroups(key[1]) then
                return VVMF_Failure("InvalidCatalogueKey", "Catalogue index is out of range.");
            fi;
            group := SmallGroup(key[1], key[2]);
        else
            key := VVMF_DecodeInteger(spec.key);
            if VVMF_IsFailure(key) or key < 0 then
                return VVMF_Failure("InvalidCatalogueKey", "Invalid catalogue parameter.");
            fi;
            if spec.catalogue = "SymmetricGroup" then group := SymmetricGroup(key);
            elif spec.catalogue = "AlternatingGroup" then group := AlternatingGroup(key);
            elif spec.catalogue = "CyclicGroup" and key > 0 then group := CyclicGroup(key);
            elif spec.catalogue = "DihedralGroup" and key > 0 and IsEvenInt(key) then
                group := DihedralGroup(key);
            else return VVMF_Failure("InvalidCatalogueKey", "Unknown catalogue or invalid parameter.");
            fi;
        fi;
        generators := GeneratorsOfGroup(group);
        names := List([1..Length(generators)], i -> Concatenation("g", String(i)));
    else
        if not IsBound(spec.names) or not VVMF_NamesQ(spec.names) then
            return VVMF_Failure("InvalidGenerators", "Invalid recorded generator names.");
        fi;
        names := spec.names;
        if spec.type = "presentation" then
            if not IsBound(spec.relators) or not IsList(spec.relators) then
                return VVMF_Failure("InvalidPresentation", "Expected a relator list.");
            fi;
            free := FreeGroup(names);
            state := rec(group := free, names := names, generators := GeneratorsOfGroup(free));
            relators := List(spec.relators, word -> VVMF_Word(state, word));
            if ForAny(relators, VVMF_IsFailure) then
                return VVMF_Failure("InvalidPresentation", "Invalid relator words.");
            fi;
            group := free / relators;
            generators := GeneratorsOfGroup(group);
        elif spec.type = "permutation" then
            if not IsBound(spec.generators) or not IsList(spec.generators) or
                Length(spec.generators) <> Length(names) or not IsBound(spec.degree) then
                return VVMF_Failure("InvalidSpecification", "Invalid permutation schema.");
            fi;
            degree := VVMF_DecodeInteger(spec.degree);
            if VVMF_IsFailure(degree) or degree < 0 then
                return VVMF_Failure("InvalidPermutation", "Invalid permutation degree.");
            fi;
            generators := [];
            for permutation in spec.generators do
                if not IsList(permutation) or not ForAll(permutation, IsList) then
                    return VVMF_Failure("InvalidPermutation", "Invalid cycle data.");
                fi;
                cycles := List(permutation, cycle -> List(cycle, VVMF_DecodeInteger));
                points := Concatenation(cycles);
                if ForAny(points, VVMF_IsFailure) or
                    not ForAll(points, x -> x > 0 and x <= degree) or
                    Length(Set(points)) <> Length(points) or ForAny(cycles, IsEmpty) then
                    return VVMF_Failure("InvalidPermutation", "Cycles must be disjoint in the declared degree.");
                fi;
                images := [1..degree];
                for cycle in cycles do
                    for i in [1..Length(cycle)] do
                        images[cycle[i]] := cycle[(i mod Length(cycle)) + 1];
                    od;
                od;
                Add(generators, PermList(images));
            od;
            group := Group(generators, ());
        elif spec.type = "matrix" then
            if not IsBound(spec.generators) or not IsList(spec.generators) or
                Length(spec.generators) <> Length(names) or not IsBound(spec.domain) then
                return VVMF_Failure("InvalidSpecification", "Invalid matrix schema.");
            fi;
            decoded := VVMF_MatrixInput(spec);
            if VVMF_IsFailure(decoded) then return decoded; fi;
            group := decoded.group;
            generators := decoded.generators;
        else
            return VVMF_Failure("InvalidSpecification", "Unsupported typed group construction.");
        fi;
    fi;
    return VVMF_FinishConstruction(group, generators, names, spec);
end;

# Summary: Accept an explicitly executed GAP recipe's group and ordered generators.
# Parameters: group/generators are recipe outputs; names/metadata are validated caller data.
# Returns: Checked finite base state or structured failure.
# Effects: Same finite-generation checks as typed construction; does not execute code itself.
# Failures: Wrong outputs, nongenerating or nonfinite inputs.
# Example: VVMF_ConstructRaw(Group((1,2)),[(1,2)],["a"],rec(type:="gapCode")).order = 2.
# See also: VVMF_FinishConstruction; explicit BuildGroupFromGAP interface.
VVMF_ConstructRaw := function(group, generators, names, metadata)
    return VVMF_FinishConstruction(group, generators, names, metadata);
end;

# Summary: Retain a checked isomorphic computational model without changing original generators.
# Parameters: state is an accepted finite base state; model is Original, Permutation or PC.
# Returns: Model record with checked original-to-model map and ordered images, or failure.
# Effects: Adds a verified model to state.models only after all checks succeed.
# Failures: Unknown model, inapplicable nonsolvable PC request, unavailable or invalid map.
# Example: VVMF_Model(state,"Permutation").verified = true.
# Remarks: Native isomorphisms must be bijective and preserve each recorded generator's
# inverse image. A model's abstract catalogue ID is never used as correspondence evidence.
# See also: VVMF_Construct; class transport in Characters.g.
VVMF_Model := function(state, model)
    local map, group, generators, candidate;
    if not IsRecord(state) or not IsBound(state.models) or
        not model in ["Original", "Permutation", "PC"] then
        return VVMF_Failure("InvalidModel", "Expected a finite state and supported model name.");
    fi;
    if IsBound(state.models.(model)) then return state.models.(model); fi;
    if model = "Permutation" then
        map := IsomorphismPermGroup(state.group);
    else
        if not IsSolvableGroup(state.group) then
            return VVMF_Failure("InapplicableModel", "A nonsolvable finite group has no pc-group model.");
        fi;
        map := IsomorphismPcGroup(state.group);
    fi;
    if map = fail or not IsGroupHomomorphism(map) or not IsBijective(map) then
        return VVMF_Failure("ModelMapFailed", "No verified model isomorphism was obtained.");
    fi;
    group := Image(map);
    generators := List(state.generators, g -> Image(map, g));
    if Size(group) <> state.order or Group(generators, One(group)) <> group or
        List(generators, g -> PreImagesRepresentative(map, g)) <> state.generators then
        return VVMF_Failure("ModelMapFailed", "Recorded generator correspondence failed.");
    fi;
    candidate := rec(group := group, generators := generators, fromOriginal := map, verified := true);
    state.models.(model) := candidate;
    return candidate;
end;
