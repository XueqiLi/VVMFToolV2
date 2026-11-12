# Title: Independent validation of unregistered mathematical snapshots
# Summary: Match imported claims against an actual accepted finite group before reusing any data.
# Dependencies: Groups, GroupBinding, Characters, GroupData, Subgroups and Serialization.
# Contracts: Wolfram checks the complete input schema; state has independently bound complete characters.
# See also: ImportGroupData in VVMFArch/step1Plan.md; Schemas/GroupSnapshot.md.

# Summary: Check reused subgroup-class IDs against independent accepted embedded witnesses.
# Parameters/defaults: state is the verified imported candidate; witnesses is a coordinator-owned
# list of StateID, GeneratorIdentity, ClassID and named generator Words records, possibly empty.
# Returns: true or StateConflict/InvalidSubgroup failure.
# Effects: Evaluates inert words in the actual group and tests subgroup conjugacy; no mutation.
# Failures: Mismatched scope, invalid words or a known class ID attached to a nonconjugate subgroup.
# Example: two distinct order-two V4 subgroups cannot exchange known class IDs, even with new item IDs.
# Remarks: The independent ledger or accepted live group supplies witnesses, never imported fields.
# Different representatives in the same conjugacy class remain valid.
# See also: VVMF_ValidateImported; knownSubgroupClassWitnesses; IsConjugate.
VVMF_CheckImportedSubgroupClasses := function(state,witnesses)
    local witness, position, elements, subgroup;
    if not IsList(witnesses) then
        return VVMF_Failure("InvalidSubgroup","Expected independent subgroup-class witnesses.");
    fi;
    for witness in witnesses do
        if not IsRecord(witness) or Set(RecNames(witness)) <>
            ["ClassID","GeneratorIdentity","StateID","Words"] or
            witness.StateID <> state.stateID or witness.GeneratorIdentity <> state.generatorIdentity then
            return VVMF_Failure("StateConflict","A class witness has a different group/generator scope.");
        fi;
        if not IsBound(state.subgroupClasses) then
            return VVMF_Failure("StateConflict","The imported subgroup class is absent.");
        fi;
        position := PositionProperty(state.subgroupClasses,entry -> entry.id = witness.ClassID);
        if position = fail then return VVMF_Failure("StateConflict","The imported subgroup class is absent."); fi;
        elements := List(witness.Words,word -> VVMF_Word(state,word));
        if ForAny(elements,VVMF_IsFailure) then return VVMF_Failure("InvalidSubgroup","A class witness word is invalid."); fi;
        subgroup := Group(elements,One(state.group));
        if not IsConjugate(state.group,state.subgroupClasses[position].group,subgroup) then
            return VVMF_Failure("StateConflict","An imported class identity refers to a different subgroup conjugacy class.");
        fi;
    od;
    return true;
end;

# Summary: Check the imported construction and any generator certificate against actual recorded generators.
# Parameters/defaults: state is independently accepted; source is a schema-checked untrusted envelope.
# Returns: true or a construction/generator/certificate failure.
# Effects: May independently construct typed input/certificate and verify a prescribed isomorphism.
# Failures: Order/name mismatch, unrelated explicit recipe, false certificate or nongenerating map.
# Example: an imported cyclic presentation must map its named generator bijectively to the actual one.
# Remarks: An imported certificate's order is computed independently; its stored order/flag is not proof.
# Raw code is never executed. Raw validation requires an independently accepted identical explicit recipe.
# See also: VVMF_ValidateImported; VVMF_Construct; GroupHomomorphismByImages.
VVMF_ImportConstruction := function(state,source)
    local built, map, certificate;
    if not IsRecord(state) or not IsBound(state.group) or not IsRecord(source) or
        not IsBound(source.generators) or not IsBound(source.order) or not IsBound(source.construction) or
        not IsBound(source.binding) or not IsRecord(source.binding) or
        List(source.generators,entry -> entry.name) <> state.names or
        source.order <> String(state.order) then
        return VVMF_Failure("InvalidImportCorrespondence","Imported order or recorded generators differ.");
    fi;
    if source.construction.type = "gapCode" then
        if source.construction <> state.construction then
            return VVMF_Failure("ImportNeedsValidationGroup","Raw source requires an accepted group built from the same explicit recipe.");
        fi;
    elif source.construction <> state.construction then
        built := VVMF_Construct(source.construction);
        if VVMF_IsFailure(built) then return built; fi;
        if built.names <> state.names or built.order <> state.order then
            return VVMF_Failure("InvalidImportCorrespondence","The imported construction has different recorded generators or order.");
        fi;
        map := GroupHomomorphismByImages(built.group,state.group,built.generators,state.generators);
        if map = fail or not IsBijective(map) then
            return VVMF_Failure("InvalidImportCorrespondence","No prescribed construction isomorphism exists.");
        fi;
    fi;
    if source.catalogueID <> fail and
        (state.catalogueID = fail or source.catalogueID <> List(state.catalogueID,String)) then
        return VVMF_Failure("InvalidImportCorrespondence","The claimed catalogue identity differs from the actual group.");
    fi;
    if source.construction.type = "catalogue" and not IsBound(source.binding.generatorPresentation) then
        return VVMF_Failure("InvalidGeneratorMap","A catalogue snapshot requires a recorded-generator certificate.");
    fi;
    if IsBound(source.binding.generatorPresentation) then
        certificate := VVMF_Construct(source.binding.generatorPresentation);
        if VVMF_IsFailure(certificate) then return certificate; fi;
        if certificate.names <> state.names or certificate.order <> state.order then
            return VVMF_Failure("InvalidGeneratorMap","The independently constructed generator certificate has the wrong order or alphabet.");
        fi;
        map := GroupHomomorphismByImages(certificate.group,state.group,
            certificate.generators,state.generators);
        if map = fail or not IsBijective(map) then
            return VVMF_Failure("InvalidGeneratorMap","The imported certificate does not preserve recorded generators.");
        fi;
    fi;
    return true;
end;

# Summary: Verify completeness and descriptions of imported subgroup selections independently.
# Parameters/defaults: state has actual group and imported generator IDs; source is the decoded
# subgroup query list or fail. All source fields are untrusted despite valid schema.
# Returns: true or an InvalidSubgroup/DescriptionFailed failure.
# Effects: Enumerates each requested selection anew using the native GAP route, compares actual
# embeddings (or a bijection of conjugacy classes) and recomputes supplied descriptions.
# Failures: Missing/extra/duplicate embeddings, repeated classes or false descriptions.
# Example: deleting one member of a claimed complete all-subgroup list is rejected.
# Remarks: VVMF_RestoreSubgroups alone cannot prove completeness; this check precedes it.
# See also: VVMF_Subgroups; VVMF_RestoreSubgroups; VVMF_ValidateImported.
VVMF_ImportSubgroups := function(state,source)
    local query, fresh, expected, actual, elements, subgroup, item, match, positions, i, result;
    if source = fail then return true; fi;
    if not IsList(source) then return VVMF_Failure("InvalidSubgroup","Expected imported subgroup queries."); fi;
    for query in source do
        fresh := ShallowCopy(state);
        fresh.subgroupRegistry := [];
        fresh.subgroupClasses := [];
        fresh.subgroupQueries := [];
        result := VVMF_Subgroups(fresh,query.query,"GAP","Original");
        if VVMF_IsFailure(result) then return result; fi;
        expected := List(result.indices,index -> fresh.subgroupRegistry[index].group);
        actual := [];
        for item in query.items do
            elements := List(item.generatorWords,word -> VVMF_ResultWord(state,word));
            if ForAny(elements,VVMF_IsFailure) then
                return VVMF_Failure("InvalidSubgroup","An imported subgroup word is invalid.");
            fi;
            subgroup := Group(elements,One(state.group));
            if item.description <> fail and StructureDescription(subgroup) <> item.description then
                return VVMF_Failure("DescriptionFailed","An imported subgroup description differs from the actual native group.");
            fi;
            Add(actual,subgroup);
        od;
        if Length(actual) <> Length(expected) or Length(Set(actual)) <> Length(actual) then
            return VVMF_Failure("InvalidSubgroup","The imported selection is incomplete or repeats an embedding.");
        fi;
        if query.query.kind = "ConjugacyClasses" then
            positions := List(actual,subgroup -> PositionProperty(expected,
                representative -> IsConjugate(state.group,representative,subgroup)));
            if Set(positions) <> [1..Length(expected)] then
                return VVMF_Failure("InvalidSubgroup","The imported subgroup representatives do not cover distinct native classes.");
            fi;
        elif Set(actual) <> Set(expected) then
            return VVMF_Failure("InvalidSubgroup","The imported subgroup embeddings differ from the complete native selection.");
        fi;
    od;
    return true;
end;

# Summary: Bind every imported mathematical claim to an independently accepted actual finite group.
# Parameters/defaults: state has a native complete character result; source is an unregistered,
# schema-checked complete JSON envelope. Neither source flags nor identities prove correspondence.
# Returns: A new candidate state with the imported mathematical IDs/orderings, or structured failure.
# Effects: Verifies actual construction, classes and complete character rows, elements, S/T and
# subgroup selections; candidate receives only data whose checks succeed. Accepted state is unchanged.
# Failures: Wrong rows on actual class words (including orthogonal but wrongly assigned C5 columns),
# false generator certificates, optional data or catalogue identities are rejected, as are
# representation variants that fail re-verification on the actual group.
# Example: a permuted row/class ordering with consistently transported words retains its saved IDs.
# Remarks: Character rows are compared against actual native bound characters, never certified by
# constructing Character(table,values) from the imported array. No executable recipe is evaluated.
# See also: VVMF_AlignedCharacters; VVMF_ImportConstruction; VVMF_ImportSubgroups.
VVMF_ValidateImported := function(state,source)
    local checked, candidate, key, assignment, words, elements;
    if not IsRecord(source) or not IsBound(source.status) or source.status <> "Complete" or
        not IsRecord(state) or not IsBound(state.characterData) then
        return VVMF_Failure("InvalidImportCorrespondence","Import requires an actual complete character computation.");
    fi;
    checked := VVMF_CheckCharacters(state,state.characterData);
    if VVMF_IsFailure(checked) or checked.status <> "Complete" then
        return VVMF_Failure("InvalidImportCorrespondence","The validation group has no complete native-bound character table.");
    fi;
    # a weakly built table proves nothing about another one (methodOptionsPlan.md 2C.6)
    if VVMF_CharacterCheckMode(state) <> "Full" then
        return VVMF_Failure("InvalidImportCorrespondence","A weakly built group cannot validate an import.");
    fi;
    checked := VVMF_ImportConstruction(state,source);
    if VVMF_IsFailure(checked) then return checked; fi;
    candidate := ShallowCopy(state);
    for key in ["boundCharacterData","generatorPresentation","elementWords","modularAssignment",
        "subgroupRegistry","subgroupClasses","subgroupQueries","generatorMap","mapTargets",
        "representations","representationRelators","stPresentation","representationOutcomes"] do
        if IsBound(candidate.(key)) then Unbind(candidate.(key)); fi;
    od;
    candidate.generatorIDs := List(source.generators,entry -> entry.id);
    candidate.boundCharacterData := StructuralCopy(source.characterData);
    checked := VVMF_AlignedCharacters(candidate,VVMF_CheckCharacters(state,state.characterData));
    if VVMF_IsFailure(checked) then return checked; fi;
    candidate.stateID := source.stateID;
    candidate.generatorIdentity := source.generatorIdentity;
    candidate.generation := VVMF_DecodeInteger(source.stateGeneration);
    candidate.characterIdentity := source.characterData.identity;
    candidate.construction := StructuralCopy(source.construction);
    if source.catalogueID = fail then candidate.catalogueID := fail;
    else candidate.catalogueID := List(source.catalogueID,VVMF_DecodeInteger); fi;
    if IsBound(source.binding.generatorPresentation) then
        candidate.generatorPresentation := StructuralCopy(source.binding.generatorPresentation);
    fi;
    if source.elements <> fail then
        elements := List(source.elements,word -> VVMF_ResultWord(candidate,word));
        if ForAny(elements,VVMF_IsFailure) or Length(elements) <> candidate.order or
            Length(Set(elements)) <> candidate.order then
            return VVMF_Failure("InvalidElements","Imported words do not enumerate the actual finite group.");
        fi;
        candidate.elementWords := List(source.elements,word -> List(word,
            pair -> [candidate.names[Position(candidate.generatorIDs,pair[1])],pair[2]]));
    fi;
    if source.modularAssignment <> fail then
        assignment := source.modularAssignment;
        checked := VVMF_AssignST(candidate,rec(identity := assignment.identity,
            sWord := List(assignment.sWord,pair -> [candidate.names[Position(candidate.generatorIDs,pair[1])],pair[2]]),
            tWord := List(assignment.tWord,pair -> [candidate.names[Position(candidate.generatorIDs,pair[1])],pair[2]])));
        if VVMF_IsFailure(checked) then return checked; fi;
    fi;
    checked := VVMF_ImportSubgroups(candidate,source.subgroupData);
    if VVMF_IsFailure(checked) then return checked; fi;
    checked := VVMF_RestoreSubgroups(candidate,source.subgroupData);
    if VVMF_IsFailure(checked) then return checked; fi;
    # Every imported representation variant is re-verified on the actual group (D7).
    if IsBound(source.representationData) and source.representationData <> fail then
        checked := ValueGlobal("VVMF_ImportRepresentations")(candidate,source.representationData);
        if VVMF_IsFailure(checked) then return checked; fi;
    fi;
    return candidate;
end;
