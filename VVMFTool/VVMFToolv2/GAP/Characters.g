# Title: Bound exact ordinary characters
# Summary: Native character algorithms, verified class transport and complete/partial checks.
# Dependencies: Groups.g, Scalars.g; InduceReduce only for the explicit Unger route.
# Conventions: Rows are ordinary complex irreducible characters; columns are the original
# group's actual conjugacy classes. A numerical table alone is not binding evidence.
# See also: GAP reference chapters 71/72; ctblgrp.gd and ctblsolv.gd.

# Summary: Transport conjugacy classes through a verified group isomorphism.
# Parameters: source/model are finite groups; map is a source-to-model isomorphism.
# Returns: Source-class to model-class index list, or structured failure.
# Effects: May compute/cache conjugacy classes.
# Failures: Wrong map domain/image, nonbijection, class membership/size/order mismatch.
# Example: VVMF_AlignClasses(g,g,IdentityMapping(g)) = [1..NrConjugacyClasses(g)].
# See also: VVMF_CheckCharacters; VVMF_Model.
VVMF_AlignClasses := function(source, model, map)
    local sourceClasses, modelClasses, permutation, class, image, position;
    if not IsGroup(source) or not IsGroup(model) or not IsGeneralMapping(map) or
        not IsGroupHomomorphism(map) or Source(map) <> source or
        Image(map) <> model or not IsBijective(map) then
        return VVMF_Failure("InvalidClassMap", "A group isomorphism with the required domain/image is missing.");
    fi;
    sourceClasses := ConjugacyClasses(source);
    modelClasses := ConjugacyClasses(model);
    if Length(sourceClasses) <> Length(modelClasses) then
        return VVMF_Failure("InvalidClassMap", "Conjugacy-class counts differ.");
    fi;
    permutation := [];
    for class in sourceClasses do
        image := Image(map, Representative(class));
        position := PositionProperty(modelClasses, target -> image in target);
        if position = fail or Size(class) <> Size(modelClasses[position]) or
            Order(Representative(class)) <> Order(Representative(modelClasses[position])) then
            return VVMF_Failure("InvalidClassMap", "Conjugacy-class correspondence failed.");
        fi;
        Add(permutation, position);
    od;
    if Set(permutation) <> [1..Length(modelClasses)] then
        return VVMF_Failure("InvalidClassMap", "The class transport is not bijective.");
    fi;
    return permutation;
end;

# Summary: Reuse certified native tables or supported character formulas/constructions.
# Parameters: group is finite.
# Returns: Native group-bound character list, or InapplicableMethod.
# Effects: May compute linear characters or combine already supported factor tables.
# Failures: General groups without an applicable known-table construction return a failure;
# no unrelated character algorithm is silently selected.
# Example: Length(VVMF_KnownCharacters(CyclicGroup(5))) = 5.
# Remarks: Supported formulas are finite abelian linear characters and direct products
# whose factors recursively qualify. Product projections/embeddings are checked on
# generators before multiplying factor characters on transported class representatives.
# See also: VVMF_Characters; VVMF_CheckCharacters.
VVMF_KnownCharacters := function(group)
    local table, info, factors, factorCharacters, projections, embeddings, classes,
        factorClasses, rows, tuple, values, representative, value, position, i, generator;
    if not IsGroup(group) or not IsFinite(group) then
        return VVMF_Failure("InapplicableMethod", "Known tables require a finite group.");
    fi;
    table := CharacterTable(group);
    if HasIrr(table) then return Irr(table); fi;
    if IsAbelian(group) then return LinearCharacters(group); fi;
    if not HasDirectProductInfo(group) then
        return VVMF_Failure("InapplicableMethod", "No verified known-table construction is available.");
    fi;
    info := DirectProductInfo(group);
    if not IsBound(info.groups) then
        return VVMF_Failure("InapplicableMethod", "No concrete direct-product factors are recorded.");
    fi;
    factors := info.groups;
    factorCharacters := List(factors, VVMF_KnownCharacters);
    if ForAny(factorCharacters, VVMF_IsFailure) then
        return VVMF_Failure("InapplicableMethod", "A direct-product factor has no supported known table.");
    fi;
    projections := List([1..Length(factors)], i -> Projection(group, i));
    embeddings := List([1..Length(factors)], i -> Embedding(group, i));
    if Product(List(factors, Size)) <> Size(group) then
        return VVMF_Failure("InvalidConstruction", "Direct-product factor orders do not match.");
    fi;
    for generator in GeneratorsOfGroup(group) do
        value := One(group);
        for i in [1..Length(factors)] do
            if Image(projections[i]) <> factors[i] then
                return VVMF_Failure("InvalidConstruction", "A factor projection is not surjective.");
            fi;
            value := value * Image(embeddings[i], Image(projections[i], generator));
        od;
        if value <> generator then
            return VVMF_Failure("InvalidConstruction", "Direct-product generator correspondence failed.");
        fi;
    od;
    classes := ConjugacyClasses(table);
    factorClasses := List(factorCharacters, chars -> ConjugacyClasses(UnderlyingCharacterTable(chars[1])));
    rows := [];
    for tuple in Cartesian(factorCharacters) do
        values := [];
        for representative in List(classes, Representative) do
            value := 1;
            for i in [1..Length(factors)] do
                position := PositionProperty(factorClasses[i],
                    class -> Image(projections[i], representative) in class);
                if position = fail then
                    return VVMF_Failure("InvalidClassMap", "A product class did not map to a factor class.");
                fi;
                value := value * ValuesOfClassFunction(tuple[i])[position];
            od;
            Add(values, value);
        od;
        Add(rows, Character(table, values));
    od;
    return rows;
end;

# The state's character-check mode (methodOptionsPlan.md 2C.6): "Full" (default) or "TransportOnly" (a weakly built
# table: the production transport and the structural checks only). Persistent: every re-run of the check reads it.
VVMF_CharacterCheckMode := function(state)
    if IsRecord(state) and IsBound(state.characterCheck) and state.characterCheck = "TransportOnly" then
        return "TransportOnly";
    fi;
    return "Full";
end;

# Summary: Validate native provenance, exact character invariants and completeness.
# Parameters: state is the original finite group; candidate supplies native group/table,
# characters, original-to-native map, class permutation, aligned values and claimed status.
# Returns: Checked candidate with status Complete/Partial and identity/degrees/sizes/orders,
# or structured failure. A partial result never satisfies mandatory group publication.
# Effects: Computes group/table class data as needed; otherwise does not mutate state.
# Failures: Naked arrays, wrong native table/group, untransported columns, malformed rows,
# failed exact orthogonality/degrees/class totals, or a false Complete claim.
# Example: VVMF_CheckCharacters(state,candidate).status = "Partial" for four SL(2,3) characters.
# Remarks: Characterhood comes from the native algorithm/construction and retained binding.
# Orthogonality supplements this provenance; it does not prove characterhood by itself. In the state's mode
# "TransportOnly" (VVMF_CharacterCheckMode) the second alignment, the row comparison and orthogonality are skipped;
# the export then claims "TransportOnly" instead of true.
# See also: VVMF_Characters; VVMF_AlignClasses; VVMF_MergeCharacters.
VVMF_CheckCharacters := function(state, candidate)
    local required, table, native, classes, sizes, orders, identity, permutation,
        nativeValues, values, degrees, row, other, i, j, product, complete, result, full;
    required := ["group","table","characters","fromOriginal","classMap","values","method","model"];
    if not IsRecord(state) or not IsBound(state.group) or not IsRecord(candidate) or
        not ForAll(required, key -> IsBound(candidate.(key))) then
        return VVMF_Failure("UnboundCharacterData", "Native group/table provenance is required.");
    fi;
    table := candidate.table;
    native := candidate.characters;
    if not IsOrdinaryTable(table) or not HasUnderlyingGroup(table) or
        not IsIdenticalObj(UnderlyingGroup(table), candidate.group) or not IsList(native) or
        not ForAll(native, chi -> IsClassFunction(chi) and IsCharacter(chi) and
            IsIdenticalObj(UnderlyingCharacterTable(chi), table)) or
        ConjugacyClasses(table) <> ConjugacyClasses(candidate.group) then
        return VVMF_Failure("UnboundCharacterData", "Characters are not bound to the declared native group/table.");
    fi;
    full := VVMF_CharacterCheckMode(state) = "Full";
    if full then
        permutation := VVMF_AlignClasses(state.group, candidate.group, candidate.fromOriginal);
        if VVMF_IsFailure(permutation) then return permutation; fi;
        if candidate.classMap <> permutation then
            return VVMF_Failure("InvalidClassMap", "The supplied class permutation is not the actual transport.");
        fi;
        nativeValues := List(native, ValuesOfClassFunction);
        if not ForAll(nativeValues, row -> Length(row) = Length(permutation)) then
            return VVMF_Failure("InvalidCharacters", "Native character row dimensions are invalid.");
        fi;
        values := List(nativeValues, row -> row{permutation});
        if values <> candidate.values then
            return VVMF_Failure("UnboundCharacterData", "Supplied rows disagree with native characters on their actual classes.");
        fi;
    else
        # TransportOnly: the production transport's rows, shape-checked only (no second alignment, no row comparison)
        values := candidate.values;
        if not IsList(values) or not ForAll(values, row -> IsList(row) and Length(row) = Length(ConjugacyClasses(state.group))) then
            return VVMF_Failure("InvalidCharacters", "Character row dimensions are invalid.");
        fi;
    fi;
    classes := ConjugacyClasses(state.group);
    sizes := List(classes, Size);
    orders := List(classes, class -> Order(Representative(class)));
    identity := PositionProperty(classes, class -> One(state.group) in class);
    if identity = fail or Sum(sizes) <> state.order or
        not ForAll(sizes, size -> IsInt(size) and size > 0) then
        return VVMF_Failure("InvalidClasses", "The conjugacy classes do not form the finite group.");
    fi;
    degrees := List(values, row -> row[identity]);
    if not ForAll(degrees, degree -> IsInt(degree) and degree > 0) then
        return VVMF_Failure("InvalidCharacters", "Character degrees must be positive integers.");
    fi;
    if full then
        for i in [1..Length(values)] do
            for j in [1..i] do
                product := Sum([1..Length(classes)],
                    k -> sizes[k] * values[i][k] * ComplexConjugate(values[j][k])) / state.order;
                if (i = j and product <> 1) or (i <> j and product <> 0) then
                    return VVMF_Failure("InvalidCharacters", "Exact character orthogonality failed.");
                fi;
            od;
        od;
    fi;
    complete := Length(values) = Length(classes) and Sum(List(degrees,x -> x^2)) = state.order and
        Number(values,row -> ForAll(row,x -> x = 1)) = 1;
    if IsBound(candidate.status) and candidate.status = "Complete" and not complete then
        return VVMF_Failure("IncompleteCharacters", "A partial table was incorrectly claimed complete.");
    fi;
    result := ShallowCopy(candidate);
    if complete then result.status := "Complete"; else result.status := "Partial"; fi;
    result.ok := true;
    result.degrees := degrees;
    result.classSizes := sizes;
    result.classOrders := orders;
    result.identityClass := identity;
    return result;
end;

# Summary: Merge independently checked aligned character rows into one coherent native table.
# Parameters: state is a finite state; checked is a candidate verified by VVMF_CheckCharacters.
# Returns: Revalidated merged candidate; complete and partial remain distinct.
# Effects: On success advances state.characterData; failed verification leaves it intact.
# Failures: Invalid candidate or incompatible previously stored rows; exact checks are rerun.
# Example: partial Conlon characters followed by DixonSchneider yield a complete SL(2,3) table.
# Remarks: Row equality is exact on actual original classes, not degree-based. This transfers
# mathematical characters, not worker workspaces; the coordinator must checkpoint the state.
# See also: VVMF_CheckCharacters; VVMF_Characters.
VVMF_MergeCharacters := function(state, checked)
    local rows, table, candidate, merged;
    checked := VVMF_CheckCharacters(state, checked);
    if VVMF_IsFailure(checked) then return checked; fi;
    rows := ShallowCopy(checked.values);
    if IsBound(state.characterData) then
        merged := VVMF_CheckCharacters(state,state.characterData);
        if VVMF_IsFailure(merged) then return merged; fi;
        rows := Concatenation(merged.values, Filtered(rows,row -> not row in merged.values));
    fi;
    table := CharacterTable(state.group);
    candidate := rec(group := state.group, table := table,
        characters := List(rows,row -> Character(table,row)), values := rows,
        fromOriginal := IdentityMapping(state.group),
        classMap := [1..Length(ConjugacyClasses(state.group))],
        method := checked.method, model := "Original");
    if IsBound(checked.computationModel) then candidate.computationModel := checked.computationModel;
    else candidate.computationModel := checked.model; fi;
    merged := VVMF_CheckCharacters(state,candidate);
    if not VVMF_IsFailure(merged) then state.characterData := merged; fi;
    return merged;
end;

# Summary: Run one explicitly selected native character algorithm on one verified model.
# Parameters: state is finite; method is a registered string; request.model names its model.
# Returns: Checked complete/partial characters merged into coherent original-group state.
# Effects: Runs one algorithm, may load InduceReduce, caches certified model/character data.
# Failures: Invalid/unavailable/inapplicable method/model or invalid native result.
# Example: VVMF_Characters(state,"Conlon",rec(model:="Original")).status can be "Partial".
# Remarks: Explicit routes do not silently switch algorithms. Timeouts/errors are isolated
# by the job coordinator. Compatible complete characterData is reusable regardless of method.
# See also: VVMF_CheckCharacters; VVMF_KnownCharacters; VVMF_MergeCharacters.
VVMF_Characters := function(state, method, request)
    local model, group, characters, table, permutation, candidate, unique, character, fresh;
    if not IsRecord(request) or not IsBound(request.model) or
        not request.model in ["Original","Permutation","PC"] or
        not method in ["DixonSchneider","Unger","Conlon","BaumClausen","KnownTable","GAP"] then
        return VVMF_Failure("InvalidMethod", "Expected one explicit character route and model.");
    fi;
    # The request's characterCheck (2C.6): "TransportOnly" for a weak build of a new table; "Full" on a weakly built
    # table re-runs the full check on the state's own character objects and raises the mode when it passes.
    if IsBound(request.characterCheck) and not request.characterCheck in ["Full", "TransportOnly"] then
        return VVMF_Failure("InvalidRequest", "Unknown character check mode.");
    fi;
    if IsRecord(state) and IsBound(state.characterData) and state.characterData.status = "Complete" then
        if IsBound(request.characterCheck) and request.characterCheck = "Full" and VVMF_CharacterCheckMode(state) = "TransportOnly" then
            # Native character objects (the workspace kept): the full check on them. Rows transferred into a rebuilt state
            # (method "Transfer") prove nothing by themselves: a fresh native computation in a copy must give the same rows.
            if state.characterData.method = "Transfer" then
                fresh := StructuralCopy(state);
                Unbind(fresh.characterData); fresh.characterCheck := "Full";
                character := VVMF_Characters(fresh, method, rec(model := request.model));
                if VVMF_IsFailure(character) then return character; fi;
                if character.status <> "Complete" or Set(character.values) <> Set(state.characterData.values) then
                    return VVMF_Failure("InvalidCharacters", "A fresh native computation does not reproduce the weakly built table.");
                fi;
            fi;
            state.characterCheck := "Full";
            character := VVMF_CheckCharacters(state, state.characterData);
            if VVMF_IsFailure(character) then state.characterCheck := "TransportOnly"; fi;
            return character;
        fi;
        return VVMF_CheckCharacters(state,state.characterData);
    fi;
    if IsBound(request.characterCheck) and request.characterCheck = "TransportOnly" and not IsBound(state.characterData) then
        state.characterCheck := "TransportOnly";
    fi;
    model := VVMF_Model(state,request.model);
    if VVMF_IsFailure(model) then return model; fi;
    group := model.group;
    if method in ["Conlon","BaumClausen"] and not IsSolvableGroup(group) then
        return VVMF_Failure("InapplicableMethod", "This character algorithm requires a solvable group.");
    fi;
    if method = "DixonSchneider" then characters := IrrDixonSchneider(group);
    elif method = "Unger" then
        if LoadPackage("InduceReduce") = fail then
            return VVMF_Failure("MethodUnavailable", "Unger requires the InduceReduce package.");
        fi;
        characters := ValueGlobal("IrrUnger")(group);
    elif method = "Conlon" then characters := IrrConlon(group);
    elif method = "BaumClausen" then characters := IrrBaumClausen(group);
    elif method = "KnownTable" then characters := VVMF_KnownCharacters(group);
    else characters := Irr(group);
    fi;
    if VVMF_IsFailure(characters) then return characters; fi;
    if not IsList(characters) or characters = [] then
        return VVMF_Failure("IncompleteCharacters", "The algorithm returned no native characters.");
    fi;
    # GAP 4.15.1 IrrConlon can return repeated native characters (for example S3).
    # Preserve first occurrence, comparing exact native characters before completeness checks.
    unique := [];
    for character in characters do
        if not character in unique then Add(unique, character); fi;
    od;
    characters := unique;
    table := UnderlyingCharacterTable(characters[1]);
    permutation := VVMF_AlignClasses(state.group,group,model.fromOriginal);
    if VVMF_IsFailure(permutation) then return permutation; fi;
    candidate := rec(group := group, table := table, characters := characters,
        fromOriginal := model.fromOriginal, classMap := permutation,
        values := List(characters,chi -> ValuesOfClassFunction(chi){permutation}),
        method := method, model := request.model);
    return VVMF_MergeCharacters(state,candidate);
end;
