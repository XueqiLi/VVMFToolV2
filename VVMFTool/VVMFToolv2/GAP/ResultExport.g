# Title: Versioned mathematical result envelopes
# Summary: Export exact finite-group data and identities without executable expressions.
# Dependencies: Diagnostics.g, Scalars.g, Groups.g, Serialization.g, Characters.g, GroupData.g.
# See also: Schemas/GroupResult.md; Driver.g owns result/checkpoint publication.

# Summary: Attach or advance coordinator-issued state identities.
# Parameters: state is an owned finite candidate; request supplies nonempty requestID,
# stateID, generatorIdentity, operation and a canonical stateGeneration string.
# Returns: true or structured failure.
# Effects: On success records the request and generation; existing mathematical IDs cannot change.
# Failures: Invalid fields, changed identity, stale/nonconsecutive generation.
# Example: a new Construct request starts at generation "0"; its Characters request uses "1".
# See also: VVMF_Export; the coordinator's revision check.
VVMF_SetIdentity := function(state, request)
    local required, generation;
    required := ["requestID","stateID","generatorIdentity","operation"];
    if not IsRecord(state) or not IsBound(state.group) or not IsRecord(request) or
        not ForAll(required,key -> IsBound(request.(key)) and IsString(request.(key)) and
            Length(request.(key)) > 0) or not IsBound(request.stateGeneration) then
        return VVMF_Failure("InvalidRequest", "Required request identities are missing.");
    fi;
    generation := VVMF_DecodeInteger(request.stateGeneration);
    if VVMF_IsFailure(generation) or generation < 0 then
        return VVMF_Failure("InvalidRequest", "Invalid state generation.");
    fi;
    if IsBound(state.stateID) then
        if state.stateID <> request.stateID or state.generatorIdentity <> request.generatorIdentity then
            return VVMF_Failure("StateConflict", "Mathematical or generator identity changed.");
        fi;
        if generation <> state.generation + 1 then
            return VVMF_Failure("StateConflict", "The request does not advance the accepted generation once.");
        fi;
    elif generation <> 0 then
        return VVMF_Failure("StateConflict", "A new state must begin at generation zero.");
    fi;
    if IsBound(state.generatorIDs) and
        (not IsList(state.generatorIDs) or Length(state.generatorIDs) <> Length(state.names) or
            not ForAll(state.generatorIDs,id -> IsString(id) and Length(id) > 0) or
            Length(Set(state.generatorIDs)) <> Length(state.generatorIDs)) then
        return VVMF_Failure("InvalidIdentity", "Stored generator identities are malformed.");
    fi;
    state.stateID := request.stateID;
    state.generatorIdentity := request.generatorIdentity;
    if not IsBound(state.generatorIDs) then
        state.generatorIDs := List([1..Length(state.names)],
            i -> Concatenation(request.generatorIdentity,":generator:",String(i)));
    fi;
    state.generation := generation;
    state.requestID := request.requestID;
    state.operation := request.operation;
    return true;
end;

# Summary: Replace names in already verified word syllables by stable generator IDs.
# Parameters: state has recorded names/IDs; word is a name/exponent-string syllable list.
# Returns: ID/exponent-string list, or structured failure.
# Effects: Pure; does not change word order or exponents.
# Failures: Unknown names or malformed/invalid words.
# Example: a word [["a","-2"]] uses state.generatorIDs[Position(state.names,"a")].
# See also: VVMF_EncodeWord; Schemas/GroupResult.md.
VVMF_WordIDs := function(state, word)
    local checked;
    if not IsRecord(state) or not IsBound(state.generatorIDs) then
        return VVMF_Failure("InvalidIdentity", "Generator identities are missing.");
    fi;
    checked := VVMF_Word(state, word);
    if VVMF_IsFailure(checked) then return checked; fi;
    return List(word, syllable -> [state.generatorIDs[Position(state.names,syllable[1])],syllable[2]]);
end;

# Summary: Record the exact GAP build and currently loaded package versions.
# Parameters/defaults: None.
# Returns: JSON-compatible producer record.
# Effects: Reads GAPInfo only; does not load extra packages.
# Failures: Requires a normally initialized GAP runtime.
# Example: VVMF_Producer().gapVersion = GAPInfo.Version.
# See also: CheckGAP; checkpoint compatibility validation.
VVMF_Producer := function()
    local packages, name;
    packages := rec();
    for name in RecNames(GAPInfo.PackagesLoaded) do
        packages.(name) := GAPInfo.PackagesLoaded.(name)[2];
    od;
    return rec(gapVersion := GAPInfo.Version, kernelVersion := GAPInfo.KernelVersion,
        buildVersion := GAPInfo.BuildVersion, architecture := GAPInfo.Architecture,
        buildDateTime := GAPInfo.BuildDateTime, packages := packages);
end;

# Summary: Produce one exact result envelope for the current owned candidate state.
# Parameters: state has coordinator identities; request matches its active request/generation.
# Returns: Schema-2 envelope, or structured failure. representationData is fail without stored
# representations; otherwise VVMF_ExportRepresentations rechecks and exports every variant.
# Effects: May recover class words and establish a character identity for the first result;
# the first complete table pins its words/IDs/row order in state.boundCharacterData so later
# exports and recovery routes reuse them. Rechecks every retained modular pair natively.
# Failures: Request mismatch, invalid native characters, absent identity, failed word recovery.
# Example: a character-only result has characterData plus elements=null and status="Complete".
# Remarks: Binding booleans document native checks; the Wolfram coordinator separately
# establishes owned-producer provenance. No JSON field makes an arbitrary import trusted.
# See also: VVMF_CheckCharacters; Schemas/GroupResult.md; VVMF_PrepareCheckpoint.
VVMF_Export := function(state, request)
    local envelope, catalogue, generators, data, checked, classes, words, classIDs,
        irrepIDs, trivial, identity, certificate, elements, subgroups, descriptions, representations;
    if not IsRecord(state) or not IsBound(state.requestID) or not IsRecord(request) or
        not IsBound(request.requestID) or request.requestID <> state.requestID or
        not IsBound(request.stateID) or request.stateID <> state.stateID or
        not IsBound(request.generatorIdentity) or request.generatorIdentity <> state.generatorIdentity or
        not IsBound(request.stateGeneration) or request.stateGeneration <> String(state.generation) or
        not IsBound(request.operation) or request.operation <> state.operation then
        return VVMF_Failure("StateConflict", "The export request does not identify this candidate state.");
    fi;
    generators := List([1..Length(state.names)],
        i -> rec(id := state.generatorIDs[i], name := state.names[i]));
    catalogue := fail;
    if state.catalogueID <> fail then catalogue := List(state.catalogueID,String); fi;
    envelope := rec(schemaVersion := 2, requestID := state.requestID, stateID := state.stateID,
        generatorIdentity := state.generatorIdentity, stateGeneration := String(state.generation),
        operation := state.operation, status := "BaseReady", construction := state.construction,
        generators := generators, order := String(state.order), catalogueID := catalogue,
        characterData := fail, elements := fail, subgroupData := fail, modularAssignment := fail,
        representationData := fail,
        availableData := rec(Characters := "NotComputed", Elements := "NotComputed",
            Subgroups := [], Representations := "NotComputed", Descriptions := "NotComputed"),
        producer := VVMF_Producer(),
        binding := rec(kind := "FiniteGroup", stateID := state.stateID,
            generatorIdentity := state.generatorIdentity, finiteGroupVerified := true,
            generatorsVerified := true),
        diagnostics := rec(operation := request.operation));
    if IsBoundGlobal("VVMF_AllSubgroupsClassExpansionQ") then
        envelope.diagnostics.allSubgroupsUsesClasses :=
            ValueGlobal("VVMF_AllSubgroupsClassExpansionQ")(AllSubgroups);
    fi;
    if IsBound(state.modularAssignment) then
        checked := VVMF_CheckST(state,state.modularAssignment.sWord,state.modularAssignment.tWord);
        if VVMF_IsFailure(checked) then return checked; fi;
        envelope.modularAssignment := rec(identity := state.modularAssignment.identity,
            sWord := VVMF_WordIDs(state,state.modularAssignment.sWord),
            tWord := VVMF_WordIDs(state,state.modularAssignment.tWord),verified := true);
        if VVMF_STCheckMode(state) = "Skip" then envelope.modularAssignment.verified := "Unverified"; fi;
    fi;
    if IsBound(state.elementWords) then
        elements := List(state.elementWords,word -> VVMF_Word(state,word));
        if ForAny(elements,VVMF_IsFailure) or Length(elements) <> state.order or
            Length(Set(elements)) <> state.order then
            return VVMF_Failure("InvalidElements","Stored element words do not enumerate the finite group.");
        fi;
        envelope.elements := List(state.elementWords,word -> VVMF_WordIDs(state,word));
        envelope.availableData.Elements := "Complete";
    fi;
    if IsBound(state.subgroupQueries) then
        # The owning optional-data adapter loads after this module, before the driver runs.
        subgroups := ValueGlobal("VVMF_ExportSubgroups")(state);
        if VVMF_IsFailure(subgroups) then return subgroups; fi;
        envelope.subgroupData := subgroups;
        envelope.availableData.Subgroups := List(subgroups,entry -> rec(QueryID := entry.query.id,
            Status := "Complete",Descriptions := "NotComputed"));
        for trivial in [1..Length(subgroups)] do
            if subgroups[trivial].query.descriptions then
                envelope.availableData.Subgroups[trivial].Descriptions := "Complete";
            fi;
        od;
        descriptions := List(subgroups,entry -> entry.query.descriptions);
        if true in descriptions then
            envelope.availableData.Descriptions := "Complete";
            if false in descriptions then envelope.availableData.Descriptions := "Partial"; fi;
        fi;
    fi;
    if request.operation = "GroupSubgroups" then
        if not IsBound(request.subgroupQuery) then return VVMF_Failure("InvalidRequest","A subgroup query is required."); fi;
        envelope.diagnostics.subgroupQueryID := request.subgroupQuery.id;
    fi;
    if request.operation = "GroupWordOrder" then
        if not IsBound(request.word) then return VVMF_Failure("InvalidRequest","An order word is required."); fi;
        checked := VVMF_WordOrder(state,request.word);
        if VVMF_IsFailure(checked) then return checked; fi;
        envelope.diagnostics.wordOrder := rec(word := VVMF_WordIDs(state,request.word),order := String(checked));
    fi;
    if request.operation = "CGNative" and IsBound(state.cgNativeResult) then
        envelope.diagnostics.cgNative := state.cgNativeResult;
    fi;
    if request.operation = "CG" and IsBoundGlobal("VVMF_CGMirrorSummary") then
        envelope.diagnostics.cgMirror := ValueGlobal("VVMF_CGMirrorSummary")(state);
    fi;
    if not IsBound(state.characterData) then return envelope; fi;
    if request.operation = "CheckGeneratorMap" then
        checked := ValueGlobal("VVMF_MapRequest")(state,request);
        if VVMF_IsFailure(checked) then return checked; fi;
        envelope.diagnostics.generatorMap := checked;
    fi;
    if request.operation = "Decompose" then
        if not IsBound(state.decompositionResult) then
            return VVMF_Failure("InvalidRequest","The requested decomposition is absent.");
        fi;
        envelope.diagnostics.decomposition := state.decompositionResult;
    fi;
    checked := VVMF_CheckCharacters(state,state.characterData);
    if VVMF_IsFailure(checked) then return checked; fi;
    if IsBound(state.characterIdentity) then
        if IsBound(request.characterIdentity) and request.characterIdentity <> state.characterIdentity then
            return VVMF_Failure("StateConflict", "The existing character identity cannot change.");
        fi;
        identity := state.characterIdentity;
    else
        if not IsBound(request.characterIdentity) or not IsString(request.characterIdentity) or
            Length(request.characterIdentity) = 0 then
            return VVMF_Failure("InvalidIdentity", "The first character result requires an identity.");
        fi;
        identity := request.characterIdentity;
    fi;
    if IsBound(state.boundCharacterData) then
        # Accepted class words, IDs and row order are fixed correspondence data. Later
        # attempts may recover new words by any route, but never re-derive these.
        data := VVMF_AlignedCharacters(state,checked);
        if VVMF_IsFailure(data) then return data; fi;
    else
        classes := ConjugacyClasses(state.group);
        words := VVMF_EncodeWords(state,List(classes,Representative));
        if VVMF_IsFailure(words) then return words; fi;
        words := List(words,word -> VVMF_WordIDs(state,word));
        if ForAny(words,VVMF_IsFailure) then
            return VVMF_Failure("WordRecoveryFailed", "A class word has invalid generator identities.");
        fi;
        classIDs := List([1..Length(classes)],i -> Concatenation(identity,":class:",String(i)));
        irrepIDs := List([1..Length(checked.values)],i -> Concatenation(identity,":irrep:",String(i)));
        trivial := PositionProperty(checked.values,row -> ForAll(row,x -> x = 1));
        if trivial <> fail then trivial := irrepIDs[trivial]; fi;
        data := rec(identity := identity, irrepIDs := irrepIDs, classIDs := classIDs,
            values := List(checked.values,row -> List(row,VVMF_EncodeScalar)),
            classSizes := List(checked.classSizes,String), classOrders := List(checked.classOrders,String),
            classRepresentativeWords := words, identityClassID := classIDs[checked.identityClass],
            trivialIrrepID := trivial, degrees := List(checked.degrees,String));
        # Pin only a complete table: a partial one must still accept merged rows.
        if checked.status = "Complete" then
            state.boundCharacterData := StructuralCopy(data);
        fi;
    fi;
    if (state.construction.type = "catalogue" or IsBound(state.generatorPresentation)) and checked.status = "Complete" then
        certificate := VVMF_GeneratorPresentation(state);
        if VVMF_IsFailure(certificate) then return certificate; fi;
        envelope.binding.generatorPresentation := certificate;
    fi;
    envelope.characterData := data;
    if IsBound(state.boundCharacterData) and IsBoundGlobal("VVMF_ExportRepresentations") then
        # The owning representation module loads before this export runs in a worker.
        representations := ValueGlobal("VVMF_ExportRepresentations")(state);
        if VVMF_IsFailure(representations) then return representations; fi;
        envelope.representationData := representations;
        envelope.availableData.Representations := ValueGlobal("VVMF_RepAvailability")(state);
        if request.operation = "Representations" and IsBound(state.representationOutcomes) then
            envelope.diagnostics.representationOutcomes := state.representationOutcomes;
        fi;
    fi;
    envelope.status := checked.status;
    envelope.availableData.Characters := checked.status;
    envelope.binding.kind := "NativeGroupCharacters";
    envelope.binding.characterIdentity := identity;
    envelope.binding.classWordsVerified := true;
    # the claims follow the state's character-check mode (methodOptionsPlan.md 2C.6)
    if VVMF_CharacterCheckMode(state) = "Full" then
        envelope.binding.classTransportVerified := true;
        envelope.binding.nativeCharactersVerified := true;
    else
        envelope.binding.classTransportVerified := "TransportOnly";
        envelope.binding.nativeCharactersVerified := "TransportOnly";
    fi;
    envelope.diagnostics.method := checked.method;
    envelope.diagnostics.model := checked.model;
    if IsBound(checked.computationModel) then envelope.diagnostics.model := checked.computationModel; fi;
    state.characterIdentity := identity;
    return envelope;
end;
