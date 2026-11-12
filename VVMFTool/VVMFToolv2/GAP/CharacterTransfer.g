# Title: Verified character transfer between sibling worker states
# Summary: Incorporate already certified mathematical rows into one coherent native state.
# Dependencies: Diagnostics, Scalars, Groups, Characters; coordinator-owned source provenance.
# See also: Kernel/GAPJobs.wl; Driver.g; VVMF_CheckCharacters.

# Summary: Evaluate an exported stable-ID word on the state's recorded ordered generators.
# Parameters/defaults: state supplies names and generatorIDs; syllables is an exported word.
# Returns: Actual group element or InvalidResultWord failure.
# Effects: Pure group evaluation, including membership and exponent checks in VVMF_Word.
# Failures: Invalid shape, unknown generator ID or invalid exponent.
# Example: [] evaluates to One(state.group), including a trivial group's empty generating list.
# See also: VVMF_WordIDs; VVMF_TransferCharacters.
VVMF_ResultWord := function(state,syllables)
    local names, pair, position;
    if not IsRecord(state) or not IsBound(state.generatorIDs) or
        not IsList(syllables) or not ForAll(syllables,pair -> IsList(pair) and Length(pair) = 2) then
        return VVMF_Failure("InvalidResultWord","Expected a stable-ID word and recorded generators.");
    fi;
    names := [];
    for pair in syllables do
        position := Position(state.generatorIDs,pair[1]);
        if position = fail then
            return VVMF_Failure("InvalidResultWord","Unknown generator identity in transferred word.");
        fi;
        Add(names,[state.names[position],pair[2]]);
    od;
    return VVMF_Word(state,names);
end;

# Summary: Merge certified source characters after evaluating their class words in this state.
# Parameters/defaults: state is a restored sibling of the source; source is an envelope admitted
# by the coordinator from a verified native checkpoint, never an arbitrary mathematical import.
# Returns: Revalidated merged native character record, or a transfer/correspondence failure.
# Effects: Evaluates source representatives, establishes a bijective class map, decodes exact
# values and merges rows while preserving the destination's existing row order/identity.
# Failures: Changed state/construction/generators, nonbijective classes, wrong sizes/orders,
# malformed scalars, or failed character invariants leave state.characterData unchanged.
# Example: transfer a sibling's Dixon result into a state already holding partial Conlon rows.
# Remarks: Characterhood provenance is established before this helper is called. Calling
# Character(table,values) does not prove arbitrary imported values are characters. The word map
# below establishes actual class correspondence; no binary workspaces are merged.
# See also: VVMF_MergeCharacters; VVMF_ResultWord; coordinator checkpointRecord.
VVMF_TransferCharacters := function(state,source)
    local required, data, classes, elements, permutation, i, row, decoded, rows,
        sizes, orders, table, candidate, checked;
    required := ["stateID","generatorIdentity","construction","generators","order","characterData"];
    if not IsRecord(state) or not IsBound(state.stateID) or not IsRecord(source) or
        not ForAll(required,key -> IsBound(source.(key))) or
        source.stateID <> state.stateID or source.generatorIdentity <> state.generatorIdentity or
        source.construction <> state.construction or source.order <> String(state.order) or
        source.generators <> List([1..Length(state.names)],
            i -> rec(id := state.generatorIDs[i],name := state.names[i])) then
        return VVMF_Failure("StateConflict","Transferred characters do not belong to this recorded state.");
    fi;
    data := source.characterData;
    # A weakly built source table stays weak in the rebound state (methodOptionsPlan.md 2C.6): its claim level is copied.
    if IsBound(source.binding) and IsRecord(source.binding) and IsBound(source.binding.nativeCharactersVerified) and
        source.binding.nativeCharactersVerified = "TransportOnly" and not IsBound(state.characterData) then
        state.characterCheck := "TransportOnly";
    fi;
    required := ["identity","values","classSizes","classOrders","classRepresentativeWords"];
    if not IsRecord(data) or not ForAll(required,key -> IsBound(data.(key))) or
        not IsList(data.values) or not IsList(data.classSizes) or not IsList(data.classOrders) or
        not IsList(data.classRepresentativeWords) or
        (IsBound(state.characterIdentity) and data.identity <> state.characterIdentity) then
        return VVMF_Failure("InvalidCharacters","Malformed or incompatible transferred character data.");
    fi;
    classes := ConjugacyClasses(state.group);
    if Length(data.classSizes) <> Length(classes) or Length(data.classOrders) <> Length(classes) or
        Length(data.classRepresentativeWords) <> Length(classes) or
        not ForAll(data.values,row -> IsList(row) and Length(row) = Length(classes)) then
        return VVMF_Failure("InvalidClasses","Transferred class dimensions do not match the group.");
    fi;
    elements := List(data.classRepresentativeWords,word -> VVMF_ResultWord(state,word));
    if ForAny(elements,VVMF_IsFailure) then
        return VVMF_Failure("InvalidClassMap","A transferred class word is invalid.");
    fi;
    permutation := List(elements,element -> PositionProperty(classes,class -> element in class));
    if Set(permutation) <> [1..Length(classes)] then
        return VVMF_Failure("InvalidClassMap","Transferred representatives do not cover each class once.");
    fi;
    sizes := List(data.classSizes,VVMF_DecodeInteger);
    orders := List(data.classOrders,VVMF_DecodeInteger);
    if sizes <> List(permutation,i -> Size(classes[i])) or orders <> List(elements,Order) then
        return VVMF_Failure("InvalidClassMap","Transferred class sizes or element orders disagree.");
    fi;
    decoded := List(data.values,row -> List(row,VVMF_DecodeScalar));
    if ForAny(decoded,row -> ForAny(row,VVMF_IsFailure)) then
        return VVMF_Failure("InvalidCharacters","Transferred values contain an invalid exact scalar.");
    fi;
    rows := List(decoded,row -> List([1..Length(classes)],i -> row[Position(permutation,i)]));
    table := CharacterTable(state.group);
    candidate := rec(group := state.group,table := table,characters := List(rows,row -> Character(table,row)),
        values := rows,fromOriginal := IdentityMapping(state.group),
        classMap := [1..Length(classes)],method := "Transfer",model := "Original");
    checked := VVMF_CheckCharacters(state,candidate);
    if VVMF_IsFailure(checked) then return checked; fi;
    return VVMF_MergeCharacters(state,checked);
end;
