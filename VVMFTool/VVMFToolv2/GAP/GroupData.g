# Title: Finite-group enrichment
# Summary: Validate and retain explicit modular generator assignments on the actual group.
# Dependencies: Diagnostics.g, Groups.g; finite generated state established by construction.
# See also: ResultExport.g; VVMFArch/step1Plan.md.

# The state's S,T check mode (methodOptionsPlan.md 2C.4): "Full" (default) or "Skip" (AssignModularGenerators at None:
# the words are evaluated, the relations, centrality and generation are not proved). Persistent like characterCheck.
VVMF_STCheckMode := function(state)
    if IsRecord(state) and IsBound(state.stCheck) and state.stCheck = "Skip" then return "Skip"; fi;
    return "Full";
end;

# Summary: Verify an explicit modular generator pair in the actual finite group.
# Parameters/defaults: state is a constructed finite group; sWord/tWord are ordered name words.
# Returns: rec(S,T) with actual elements, or a specific structured failure. No options.
# Effects: Only ordinary GAP attribute caches; does not change the accepted assignment.
# Failures: Invalid words, (ST)^3<>S^4, noncentral S^2, or failure to generate all of G.
# Example: S=(1,2)(3,4), T=(1,2,3) defines a valid pair in A4.
# Remarks: The relations are those of the cover B = <S,T | S^2 central, (ST)^3 = S^4> (the braid group B3;
# fractionalWeightPlan.md): finite quotients of SL(2,Z) are the case S^4 = 1 (then (ST)^3 = 1), metaplectic quotients
# have S^8 = 1, and cover groups carry forms of rational weight (rho(S^2) = e^{i Pi k}). The cover order is Order(S^4).
# Checks use One(G), including exact finite-ring matrix identities. Matrix images
# in a nonfaithful representation are not used as evidence about the whole group. In the state's mode "Skip"
# (VVMF_STCheckMode) only the words are evaluated; the export then claims verified "Unverified".
# See also: VVMF_AssignST; VVMF_Word.
VVMF_CheckST := function(state,sWord,tWord)
    local s, t, one;
    if not IsRecord(state) or not IsBound(state.group) or not IsGroup(state.group) or
        not IsBound(state.generators) then
        return VVMF_Failure("InvalidState","A constructed finite group is required.");
    fi;
    s := VVMF_Word(state,sWord);
    if VVMF_IsFailure(s) then return s; fi;
    t := VVMF_Word(state,tWord);
    if VVMF_IsFailure(t) then return t; fi;
    if VVMF_STCheckMode(state) = "Skip" then return rec(S := s,T := t); fi;
    one := One(state.group);
    if (s*t)^3 <> s^4 then
        return VVMF_Failure("InvalidModularGenerators","The proposed pair does not satisfy (ST)^3=S^4.");
    fi;
    if not ForAll(state.generators,g -> s^2*g = g*s^2) then
        return VVMF_Failure("InvalidModularGenerators","The proposed S^2 is not central in the group.");
    fi;
    if Group([s,t],one) <> state.group then
        return VVMF_Failure("NongeneratingModularPair","The proposed S,T do not generate the entire group.");
    fi;
    return rec(S := s,T := t);
end;

# Summary: Enumerate every actual group element as a verified recorded-generator word.
# Parameters/defaults: state is finite and generated; word strategy/budget come from the request.
# Returns: Named word list, or word-recovery failure; the trivial result is [[]].
# Effects: Enumerates Elements once and stores words after exact membership/coverage checks.
# Failures: Recovery errors preserve a preceding complete element collection.
# Example: VVMF_Elements(state) has length 12 for A4, irrespective of an S,T assignment.
# See also: VVMF_EncodeWords; VVMF_Export.
VVMF_Elements := function(state)
    local elements, words, model;
    if not IsRecord(state) or not IsBound(state.group) or not IsBound(state.order) then
        return VVMF_Failure("InvalidState","A finite constructed state is required.");
    fi;
    if IsBound(state.elementWords) then return state.elementWords; fi;
    model := state.models.Original;
    if IsBound(state.dataModel) then model := state.dataModel; fi;
    elements := List(Elements(model.group),element -> PreImagesRepresentative(model.fromOriginal,element));
    words := VVMF_EncodeWords(state,elements);
    if VVMF_IsFailure(words) then return words; fi;
    if Length(words) <> state.order or List(words,word -> VVMF_Word(state,word)) <> elements then
        return VVMF_Failure("InvalidElements","Element words do not cover the actual group.");
    fi;
    state.elementWords := words;
    return words;
end;

# Summary: Compute the exact order of one explicit recorded-generator word.
# Parameters/defaults: state is finite; word is a name/exponent-string syllable list.
# Returns: Positive integer or InvalidWord/InvalidState failure.
# Effects: Native attribute caching only; no modular assignment is required.
# Failures: Malformed or unknown generator words are not interpreted as identity.
# Example: the empty word has order one in every supported coefficient domain.
# See also: VVMF_Word; GroupWordOrder.
VVMF_WordOrder := function(state,word)
    local element;
    element := VVMF_Word(state,word);
    if VVMF_IsFailure(element) then return element; fi;
    if IsBound(state.dataModel) then element := Image(state.dataModel.fromOriginal,element); fi;
    return Order(element);
end;

# Summary: Commit a validated explicit modular assignment to one owned candidate state.
# Parameters/defaults: state is a constructed finite candidate; assignment contains exactly
# identity (nonempty string), sWord and tWord (ordered name/exponent-string lists). No options.
# Returns: true or structured failure; failed assignment preserves the preceding record.
# Effects: Sets state.modularAssignment only after all group-level checks pass.
# Failures: Invalid schema, words, relations, centrality or generation.
# Example: distinct valid pairs receive distinct identities even for the same abstract group.
# See also: VVMF_CheckST; VVMF_Export; the unscheduled discovery/classification TODOs.
VVMF_AssignST := function(state,assignment)
    local checked;
    if not IsRecord(assignment) or Set(RecNames(assignment)) <> ["identity","sWord","tWord"] or
        not IsString(assignment.identity) or Length(assignment.identity) = 0 then
        return VVMF_Failure("InvalidModularAssignment","Expected assignment identity and explicit S,T words.");
    fi;
    checked := VVMF_CheckST(state,assignment.sWord,assignment.tWord);
    if VVMF_IsFailure(checked) then return checked; fi;
    state.modularAssignment := StructuralCopy(assignment);
    return true;
end;
