# Title: Prescribed maps between recorded finite-group generators
# Summary: Check exactly the supplied generator images and recover verified inverse words.
# Dependencies: Groups.g, Serialization.g; caller owns finite verified source/target states.
# Contracts: Abstract group isomorphism never substitutes a different prescribed map.
# See also: VVMFArch/step1Plan.md CheckGeneratorMap; GAP lib/ghom.gd.

# Summary: Recover a map target through its independently certified recorded-generator presentation.
# Parameters/defaults: source owns a worker-local mapTargets cache; specification contains
# stateID, generatorIdentity, order and presentation, supplied by the trusted coordinator.
# Returns: A verified finite target state with corresponding ordered names, or failure.
# Effects: Constructs once per target generator identity and retains the actual state/maps.
# Failures: Malformed fields, conflicting identity/certificate or unequal finite order.
# Example: a certified matrix-group target is reconstructed without executing its GAP recipe.
# Remarks: The caller establishes certificate provenance against the accepted target group.
# This is not an untrusted JSON import validator. Same-order abstract groups alone do not
# supply the prescribed generator correspondence; the certified presentation supplies it.
# See also: VVMF_GeneratorPresentation; VVMF_MapRequest; CheckGeneratorMap in step1Plan.md.
VVMF_MapTarget := function(source,specification)
    local order, target, identity, entry;
    if not IsRecord(source) or not IsBound(source.group) or not IsRecord(specification) or
        Set(RecNames(specification)) <> ["generatorIdentity","order","presentation","stateID"] or
        not ForAll([specification.stateID,specification.generatorIdentity],value ->
            IsString(value) and Length(value)>0) or not IsRecord(specification.presentation) or
        not IsBound(specification.presentation.type) or specification.presentation.type <> "presentation" then
        return VVMF_Failure("InvalidGeneratorMap","A certified target presentation and identity are required.");
    fi;
    order := VVMF_DecodeInteger(specification.order);
    if VVMF_IsFailure(order) or order < 1 then
        return VVMF_Failure("InvalidGeneratorMap","The target has no positive certified finite order.");
    fi;
    identity := specification.generatorIdentity;
    if IsBound(source.mapTargets) and IsBound(source.mapTargets.(identity)) then
        entry := source.mapTargets.(identity);
        if entry.specification <> specification then
            return VVMF_Failure("StateConflict","A cached target has a different generator certificate.");
        fi;
        return entry.state;
    fi;
    target := VVMF_Construct(specification.presentation);
    if VVMF_IsFailure(target) then return target; fi;
    if target.order <> order then
        return VVMF_Failure("InvalidGeneratorMap","The certified presentation has a different finite order.");
    fi;
    target.stateID := specification.stateID;
    target.generatorIdentity := identity;
    if not IsBound(source.mapTargets) then source.mapTargets := rec(); fi;
    source.mapTargets.(identity) := rec(specification := StructuralCopy(specification),state := target);
    return target;
end;

# Summary: Verify a prescribed homomorphism and its injectivity/surjectivity.
# Parameters/defaults: source/target are verified finite states with ordered generators;
# imageWords gives one target named word per source generator. Each state's dataModel
# defaults to its Original model. Source word-recovery settings govern inverse output.
# Returns: A JSON-safe record of homomorphism/injective/surjective/isomorphism booleans,
# supplied imageWords and inverseImageWords (fail unless isomorphic), or structured failure.
# Effects: Retains the native map, target state and exact summary in source.generatorMap
# only after all checks pass; models and word maps can populate ordinary attribute caches.
# Failures: Invalid words/arity, model correspondence, inconsistent kernel/image data and
# inverse recovery leave the previous accepted map unchanged. Native GAP errors/timeouts
# belong to the owned worker boundary and never become mathematical false.
# Example: C6 -> C3 sending the recorded generator to the target generator is surjective
# and not injective; C2 -> C3 with that image is not a homomorphism.
# Remarks: Only the checked GroupHomomorphismByImages constructor's fail is a mathematical
# negative. Model images/preimages preserve the supplied generator correspondence.
# Inverse words are checked through both the source model and the actual native map.
# See also: VVMF_Model; VVMF_EncodeWords; GAP reference GroupHomomorphismByImages.
VVMF_Map := function(source,target,imageWords)
    local sourceModel, targetModel, images, modelImages, mapping, result, kernel, image,
        injective, surjective, preimages, words, evaluated;
    if not IsRecord(source) or not IsRecord(target) or
        not ForAll([source,target],state -> IsBound(state.group) and IsBound(state.models) and
            IsBound(state.models.Original) and IsBound(state.generators) and IsBound(state.order)) or
        not IsList(imageWords) or Length(imageWords) <> Length(source.generators) then
        return VVMF_Failure("InvalidGeneratorMap","Supply one target word per recorded source generator.");
    fi;
    sourceModel := source.models.Original;
    targetModel := target.models.Original;
    if IsBound(source.dataModel) then sourceModel := source.dataModel; fi;
    if IsBound(target.dataModel) then targetModel := target.dataModel; fi;
    if VVMF_IsFailure(sourceModel) then return sourceModel; fi;
    if VVMF_IsFailure(targetModel) then return targetModel; fi;
    images := List(imageWords,word -> VVMF_Word(target,word));
    if ForAny(images,VVMF_IsFailure) then return First(images,VVMF_IsFailure); fi;
    modelImages := List(images,element -> Image(targetModel.fromOriginal,element));
    mapping := GroupHomomorphismByImages(sourceModel.group,targetModel.group,
        sourceModel.generators,modelImages);
    result := rec(homomorphism := false,injective := false,surjective := false,
        isomorphism := false,imageWords := StructuralCopy(imageWords),inverseImageWords := fail);
    if mapping <> fail then
        if not IsGroupHomomorphism(mapping) or
            List(sourceModel.generators,element -> Image(mapping,element)) <> modelImages then
            return VVMF_Failure("InvalidGeneratorMap","The native map changed a prescribed generator image.");
        fi;
        kernel := Kernel(mapping);
        image := Image(mapping);
        if Size(kernel)*Size(image) <> source.order or not IsSubgroup(targetModel.group,image) then
            return VVMF_Failure("InvalidGeneratorMap","Kernel and image do not describe the supplied finite map.");
        fi;
        injective := Size(kernel) = 1;
        surjective := image = targetModel.group;
        if IsInjective(mapping) <> injective or IsSurjective(mapping) <> surjective then
            return VVMF_Failure("InvalidGeneratorMap","Native map flags disagree with its kernel and image.");
        fi;
        result.homomorphism := true;
        result.injective := injective;
        result.surjective := surjective;
        result.isomorphism := injective and surjective;
        if result.isomorphism then
            preimages := List(targetModel.generators,element -> PreImagesRepresentative(mapping,element));
            if fail in preimages then
                return VVMF_Failure("InvalidGeneratorMap","A bijection has a missing inverse generator image.");
            fi;
            preimages := List(preimages,element -> PreImagesRepresentative(sourceModel.fromOriginal,element));
            if fail in preimages then
                return VVMF_Failure("InvalidGeneratorMap","An inverse image could not return to the recorded source.");
            fi;
            words := VVMF_EncodeWords(source,preimages);
            if VVMF_IsFailure(words) then return words; fi;
            evaluated := List(words,word -> VVMF_Word(source,word));
            if evaluated <> preimages or
                List(evaluated,element -> Image(mapping,Image(sourceModel.fromOriginal,element))) <>
                    targetModel.generators then
                return VVMF_Failure("InvalidGeneratorMap","Recovered inverse words failed actual map verification.");
            fi;
            result.inverseImageWords := words;
        fi;
    fi;
    source.generatorMap := rec(target := target,map := mapping,result := StructuralCopy(result));
    return result;
end;

# Summary: Check the requested map against a certified target and the chosen computational model.
# Parameters/defaults: source is the verified source group; request has targetGroup, imageWords,
# and the explicit model. Source dataModel has already been selected by the driver.
# Returns: JSON-safe map report with both group/generator identities and target names, or failure.
# Effects: Reuses target construction/models and retains the successful native map on source.
# Failures: Missing request fields, target correspondence, inapplicable model or map verification.
# Example: a repeated request to the same target reuses source.mapTargets instead of rebuilding.
# See also: VVMF_MapTarget; VVMF_Map; GAP/Driver.g.
VVMF_MapRequest := function(source,request)
    local target, model, result;
    if not IsRecord(source) or not IsBound(source.stateID) or not IsBound(source.generatorIdentity) or
        not IsRecord(request) or not ForAll(["targetGroup","imageWords","model"],key -> IsBound(request.(key))) then
        return VVMF_Failure("InvalidGeneratorMap","The map request is incomplete.");
    fi;
    target := VVMF_MapTarget(source,request.targetGroup);
    if VVMF_IsFailure(target) then return target; fi;
    model := VVMF_Model(target,request.model);
    if VVMF_IsFailure(model) then return model; fi;
    target.dataModel := model;
    result := VVMF_Map(source,target,request.imageWords);
    if VVMF_IsFailure(result) then return result; fi;
    result.sourceStateID := source.stateID;
    result.sourceGeneratorIdentity := source.generatorIdentity;
    result.targetStateID := target.stateID;
    result.targetGeneratorIdentity := target.generatorIdentity;
    result.targetNames := ShallowCopy(target.names);
    result.targetOrder := String(target.order);
    return result;
end;

