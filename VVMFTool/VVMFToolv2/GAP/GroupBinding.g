# Title: Recorded-generator correspondence after typed reconstruction
# Summary: Reattach accepted portable data only through a proven generator isomorphism.
# Dependencies: Groups, Serialization, Characters, GroupData, CharacterTransfer.
# Contracts: source is coordinator-certified mathematical data, never an unvalidated import.
# See also: Kernel/GroupEnrichment.wl; Schemas/GroupResult.md.

# Summary: Match a retained character ordering against the actual native classes and rows.
# Parameters/defaults: state has boundCharacterData; checked is VVMF_CheckCharacters output.
# Returns: Original character record with its IDs/words/order, or a correspondence failure.
# Effects: Computes native conjugacy-class membership; leaves accepted data unchanged.
# Failures: Missing classes, changed sizes/orders or unequal character values.
# Example: a reconstructed C5 keeps each original irrep ID even if native classes reorder.
# See also: VVMF_RebindGroup; VVMF_Export.
VVMF_AlignedCharacters := function(state,checked)
    local data, classes, elements, positions, values, native;
    data := state.boundCharacterData;
    classes := ConjugacyClasses(state.group);
    elements := List(data.classRepresentativeWords,word -> VVMF_ResultWord(state,word));
    if ForAny(elements,VVMF_IsFailure) then
        return VVMF_Failure("InvalidClassMap","A retained class word is invalid.");
    fi;
    positions := List(elements,element -> PositionProperty(classes,class -> element in class));
    if Length(positions) <> Length(classes) or Set(positions) <> [1..Length(classes)] or
        List(data.classSizes,VVMF_DecodeInteger) <> List(positions,i -> Size(classes[i])) or
        List(data.classOrders,VVMF_DecodeInteger) <> List(elements,Order) then
        return VVMF_Failure("InvalidClassMap","Retained classes do not correspond to native classes.");
    fi;
    values := List(data.values,row -> List(row,VVMF_DecodeScalar));
    native := List(checked.values,row -> row{positions});
    if Set(values) <> Set(native) or Length(values) <> Length(native) then
        return VVMF_Failure("InvalidCharacterMap","Retained characters differ from the native bound rows.");
    fi;
    return StructuralCopy(data);
end;

# Summary: Bind a freshly reconstructed typed group to independently accepted group data.
# Parameters/defaults: state is VVMF_Construct output; source is a complete, trusted envelope.
# Returns: true or a correspondence failure. Raw construction is never replayed here.
# Effects: Installs the old mathematical identities, transfers certified characters through
# a checked class bijection, and revalidates the explicit modular assignment when present.
# Failures: Construction/order/names disagreement, absent catalogue presentation, failed
# relators, class transport, modular assignment or representation re-verification (native
# witnesses are rebuilt from exact images). Caller discards this candidate on failure.
# Example: reconstructing A5 verifies the original generator presentation before transferring rows.
# Remarks: Equal catalogue IDs alone are insufficient. Literal permutation/matrix input or
# the same quotient presentation determines generators; catalogue input additionally uses
# a presentation previously certified by a bijective map in the original owned worker.
# A surjection from that proven finite presentation to a generated group of equal order
# establishes the required isomorphism. The envelope's provenance is supplied by the caller.
# See also: VVMF_GeneratorPresentation; VVMF_TransferCharacters; VVMF_AlignedCharacters.
VVMF_RebindGroup := function(state,source)
    local names, certificate, relators, checked, assignment;
    if not IsRecord(state) or not IsBound(state.construction) or not IsRecord(source) or
        not ForAll(["construction","order","generators","stateID","generatorIdentity",
            "stateGeneration","characterData","status","binding","modularAssignment"],
            key -> IsBound(source.(key))) or source.status <> "Complete" or
        state.construction <> source.construction or source.order <> String(state.order) or
        not IsRecord(source.characterData) or not IsList(source.generators) then
        return VVMF_Failure("StateConflict","Reconstruction does not match the accepted finite construction.");
    fi;
    if not source.construction.type in ["catalogue","presentation","permutation","matrix"] then
        return VVMF_Failure("ExplicitRebuildRequired","Retained executable source requires an explicit rebuild.");
    fi;
    names := List(source.generators,entry -> entry.name);
    if names <> state.names then
        return VVMF_Failure("InvalidGeneratorMap","Reconstruction changed the recorded generators.");
    fi;
    if source.construction.type = "catalogue" and
        (not IsRecord(source.binding) or not IsBound(source.binding.generatorPresentation)) then
        return VVMF_Failure("InvalidGeneratorMap","The catalogue generators have no certified presentation.");
    fi;
    if IsRecord(source.binding) and IsBound(source.binding.generatorPresentation) then
        certificate := source.binding.generatorPresentation;
        if not IsRecord(certificate) or not IsBound(certificate.type) or
            certificate.type <> "presentation" or not IsBound(certificate.names) or
            certificate.names <> names or not IsBound(certificate.relators) or
            not IsList(certificate.relators) then
            return VVMF_Failure("InvalidGeneratorMap","Malformed recorded-generator presentation.");
        fi;
        relators := List(certificate.relators,word -> VVMF_Word(state,word));
        if ForAny(relators,VVMF_IsFailure) or not ForAll(relators,element -> element = One(state.group)) then
            return VVMF_Failure("InvalidGeneratorMap","Rebuilt generators do not satisfy the certified relations.");
        fi;
        state.generatorPresentation := StructuralCopy(certificate);
    fi;
    state.stateID := source.stateID;
    state.generatorIdentity := source.generatorIdentity;
    state.generatorIDs := List(source.generators,entry -> entry.id);
    state.generation := VVMF_DecodeInteger(source.stateGeneration);
    checked := VVMF_TransferCharacters(state,source);
    if VVMF_IsFailure(checked) then return checked; fi;
    state.characterIdentity := source.characterData.identity;
    state.boundCharacterData := StructuralCopy(source.characterData);
    checked := VVMF_AlignedCharacters(state,checked);
    if VVMF_IsFailure(checked) then return checked; fi;
    if source.modularAssignment <> fail then
        assignment := source.modularAssignment;
        # a skipped S,T check stays skipped in the rebound state (methodOptionsPlan.md 2C.6)
        if IsBound(assignment.verified) and assignment.verified = "Unverified" then state.stCheck := "Skip"; fi;
        checked := VVMF_AssignST(state,rec(identity := assignment.identity,
            sWord := List(assignment.sWord,pair -> [names[Position(state.generatorIDs,pair[1])],pair[2]]),
            tWord := List(assignment.tWord,pair -> [names[Position(state.generatorIDs,pair[1])],pair[2]])));
        if VVMF_IsFailure(checked) then return checked; fi;
    fi;
    if IsBound(source.elements) and source.elements <> fail then
        state.elementWords := List(source.elements,word -> List(word,
            pair -> [names[Position(state.generatorIDs,pair[1])],pair[2]]));
        checked := List(state.elementWords,word -> VVMF_Word(state,word));
        if ForAny(checked,VVMF_IsFailure) or Length(checked) <> state.order or
            Length(Set(checked)) <> state.order then
            return VVMF_Failure("InvalidElements","Retained element words do not enumerate the rebuilt group.");
        fi;
    fi;
    if IsBound(source.subgroupData) and source.subgroupData <> fail then
        checked := ValueGlobal("VVMF_RestoreSubgroups")(state,source.subgroupData);
        if VVMF_IsFailure(checked) then return checked; fi;
    fi;
    # Native representation witnesses are rebuilt from their exact images and re-verified (D6),
    # after the assignment is restored so exported basis properties are reproduced exactly.
    if IsBound(source.representationData) and source.representationData <> fail then
        checked := ValueGlobal("VVMF_ImportRepresentations")(state,source.representationData);
        if VVMF_IsFailure(checked) then return checked; fi;
    fi;
    return true;
end;

# Summary: Prove that the recorded generator presentation presents the group (final review H-1).
# Parameters/defaults: state, a rebound state with its order and, optionally, generatorPresentation.
# Returns: true, or InvalidGeneratorMap failure.
# Effects: Bounded coset enumeration of the presented group over the trivial subgroup.
# Failures: InvalidGeneratorMap when the presented group's order differs from the group's or the enumeration exceeds its
# bound (an infinite or much larger presented group; a valid presentation needing more than max(100000, 64 |G|) cosets is
# refused too: the group then stays unraised, never wrongly raised).
# Example: the certificate <g1, g2 | g1^3, g2^3> of A4 is refused (it presents an infinite group).
# Remarks: VVMF_RebindGroup checks only that the relators hold in the rebuilt group: a surjection from the presented
# group. Equal orders make it an isomorphism. The rebind's contract trusts a certificate from a verified source; an
# unverified import's certificate is proved here before ValidateGroup raises the group.
# See also: VVMF_RebindGroup; VVMF_GeneratorPresentation.
VVMF_ProveGeneratorPresentation := function(state)
    local certificate, free, generators, relators, table;
    if not IsBound(state.generatorPresentation) then return true; fi;
    certificate := state.generatorPresentation;
    free := FreeGroup(state.names);
    generators := GeneratorsOfGroup(free);
    relators := List(certificate.relators, word -> List(word, syllable -> [Position(state.names, syllable[1]), VVMF_DecodeInteger(syllable[2])]));
    if ForAny(relators, word -> ForAny(word, s -> s[1] = fail or VVMF_IsFailure(s[2]))) then
        return VVMF_Failure("InvalidGeneratorMap", "Malformed recorded-generator presentation.");
    fi;
    relators := List(relators, word -> Product(List(word, s -> generators[s[1]]^s[2]), One(free)));
    table := CosetTableFromGensAndRels(generators, relators, [] : max := Maximum(100000, 64 * state.order), silent := true);
    if table = fail or Length(table[1]) <> state.order then
        return VVMF_Failure("InvalidGeneratorMap", "The recorded generator presentation does not present a group of this order.");
    fi;
    return true;
end;
