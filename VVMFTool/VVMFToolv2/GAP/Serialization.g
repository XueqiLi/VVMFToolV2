# Title: Verified words in recorded generators
# Summary: Recover portable ordered words from native maps, with a bounded Cayley fallback.
# Dependencies: Groups.g, Scalars.g; the caller's worker resource limits.
# See also: https://gap-system.github.io/gap/doc/ref/chap39_mj.html

# Summary: Recover the direct epimorphism on the exact recorded ordered generators.
# Parameters: state is a verified finite construction state.
# Returns: Cached word-map record, or structured failure.
# Effects: May construct/cache a free-group epimorphism; no element enumeration is requested.
# Failures: Invalid state or a map whose generator images do not match the recorded order.
# Example: VVMF_WordMap(state).kind is "Epimorphism" for a permutation construction.
# Remarks: For a presentation in its natural generators, the underlying associative word
# already supplies the quotient preimage. No printed mapping form is inspected.
# See also: VVMF_FpWordMap; VVMF_EncodeWord.
VVMF_WordMap := function(state)
    local recordedGroup, map, correspondence, candidate;
    if not IsRecord(state) or not IsBound(state.group) or
        not IsBound(state.generators) or not IsBound(state.names) then
        return VVMF_Failure("WordRecoveryFailed", "Missing recorded group generators.");
    fi;
    if IsBound(state.wordMap) then return state.wordMap; fi;
    if IsFpGroup(state.group) and state.generators = GeneratorsOfGroup(state.group) then
        candidate := rec(kind := "Presentation");
    else
        recordedGroup := Group(state.generators, One(state.group));
        if GeneratorsOfGroup(recordedGroup) <> state.generators then
            return VVMF_Failure("WordRecoveryFailed", "The native group reordered recorded generators.");
        fi;
        map := EpimorphismFromFreeGroup(recordedGroup : names := state.names);
        if map = fail then return VVMF_Failure("WordRecoveryFailed", "No free-group epimorphism."); fi;
        correspondence := MappingGeneratorsImages(map);
        if correspondence[1] <> GeneratorsOfGroup(Source(map)) or
            correspondence[2] <> state.generators then
            return VVMF_Failure("WordRecoveryFailed", "The free-group map has different generator order.");
        fi;
        candidate := rec(kind := "Epimorphism", map := map);
    fi;
    state.wordMap := candidate;
    return candidate;
end;

# Summary: Construct a presentation map using exactly the recorded generators.
# Parameters: state is a verified finite construction state.
# Returns: Cached rec(kind:="FPIsomorphism",map:=...) or structured failure.
# Effects: Computes a presentation and installs only a verified word map.
# Failures: No isomorphism, wrong generator order, invalid state.
# Example: VVMF_FpWordMap(state).kind = "FPIsomorphism" after a successful conversion.
# Remarks: The native mapping can be a composition; Image is used independently of storage.
# See also: VVMF_WordMap; GAP reference section 47.11-2.
VVMF_FpWordMap := function(state)
    local map, target;
    if not IsRecord(state) or not IsBound(state.group) or not IsBound(state.generators) then
        return VVMF_Failure("WordRecoveryFailed", "Missing group for presentation conversion.");
    fi;
    map := IsomorphismFpGroupByGenerators(state.group, state.generators);
    if map = fail or not IsBijective(map) then
        return VVMF_Failure("WordRecoveryFailed", "No presentation isomorphism was obtained.");
    fi;
    target := Image(map);
    if List(state.generators, g -> Image(map, g)) <> GeneratorsOfGroup(target) then
        return VVMF_Failure("WordRecoveryFailed", "Presentation generator correspondence failed.");
    fi;
    state.wordMap := rec(kind := "FPIsomorphism", map := map);
    return state.wordMap;
end;

# Summary: Convert an associative word to named JSON syllables.
# Parameters: word is a GAP associative word on the recorded alphabet; names is its name list.
# Returns: Ordered {name,decimalExponent} pairs, or structured failure.
# Effects: Pure; uses syllable accessors, never printing/parsing.
# Failures: Nonword input or an index outside the recorded alphabet.
# Example: VVMF_WordSyllables(FreeGroup("a").1^-2,["a"]) = [["a","-2"]].
# See also: VVMF_EncodeWord; VVMF_Word.
VVMF_WordSyllables := function(word, names)
    local result, i, index;
    if not IsAssocWord(word) or not VVMF_NamesQ(names) then
        return VVMF_Failure("WordRecoveryFailed", "Expected an associative word and recorded names.");
    fi;
    result := [];
    for i in [1..NumberSyllables(word)] do
        index := GeneratorSyllable(word, i);
        if index < 1 or index > Length(names) then
            return VVMF_Failure("WordRecoveryFailed", "Word alphabet does not match recorded generators.");
        fi;
        Add(result, [names[index], String(ExponentSyllable(word, i))]);
    od;
    return result;
end;

# Summary: Recover words by a bounded breadth-first Cayley graph search.
# Parameters: state is finite; targets are actual group elements; budget supplies positive
# maxElements and maxMilliseconds, in addition to the enclosing worker's hard memory limit.
# Returns: Words matching targets in order, or structured resource/input failure.
# Effects: Allocates a visited-element dictionary and predecessor tree up to maxElements.
# Failures: Out-of-group targets, malformed budget, exhausted CPU-time/element bounds.
# Example: VVMF_WordSearch(state,[One(state.group)],
#     rec(maxElements:=1,maxMilliseconds:=1000)) = [[]].
# Remarks: Stores predecessor edges rather than a complete word at every vertex; stops as
# soon as the targets are found. It never calls Elements or Factorization.
# See also: VVMF_EncodeWord; the shared worker memory/time budget in step1Plan.md.
VVMF_WordSearch := function(state, targets, budget)
    local elements, parents, edges, visited, frontier, steps, stepNames, start, i,
        candidate, position, pending, targetPositions, words, path, current, j;
    if not IsRecord(state) or not IsBound(state.group) or not IsList(targets) or
        not IsRecord(budget) or not IsBound(budget.maxElements) or
        not IsInt(budget.maxElements) or budget.maxElements < 1 or
        not IsBound(budget.maxMilliseconds) or not IsInt(budget.maxMilliseconds) or
        budget.maxMilliseconds < 1 then
        return VVMF_Failure("InvalidWordBudget", "Expected positive bounded word-search resources.");
    fi;
    if not ForAll(targets, x -> x in state.group) then
        return VVMF_Failure("InvalidElement", "A word-search target is outside the group.");
    fi;
    elements := [One(state.group)];
    parents := [0];
    edges := [fail];
    visited := NewDictionary(One(state.group), true, state.group);
    AddDictionary(visited, elements[1], 1);
    steps := Concatenation(state.generators, List(state.generators, Inverse));
    stepNames := Concatenation(List(state.names, name -> [name,"1"]),
        List(state.names, name -> [name,"-1"]));
    frontier := 1;
    start := Runtime();
    targetPositions := List(targets, x -> LookupDictionary(visited, x));
    while fail in targetPositions and frontier <= Length(elements) do
        for i in [1..Length(steps)] do
            if Runtime() - start >= budget.maxMilliseconds then
                return VVMF_Failure("Timeout", "The bounded word search exhausted its CPU budget.");
            fi;
            candidate := elements[frontier] * steps[i];
            if LookupDictionary(visited, candidate) = fail then
                if Length(elements) >= budget.maxElements then
                    return VVMF_Failure("WordSearchLimit", "The word search exhausted its element budget.");
                fi;
                Add(elements, candidate);
                Add(parents, frontier);
                Add(edges, stepNames[i]);
                AddDictionary(visited, candidate, Length(elements));
                targetPositions := List(targets, x -> LookupDictionary(visited, x));
                if not fail in targetPositions then break; fi;
            fi;
        od;
        frontier := frontier + 1;
    od;
    if fail in targetPositions then
        return VVMF_Failure("WordRecoveryFailed", "Recorded generators did not reach every target.");
    fi;
    words := [];
    for position in targetPositions do
        path := [];
        current := position;
        while parents[current] <> 0 do
            Add(path, edges[current]);
            current := parents[current];
        od;
        Add(words, Reversed(path));
    od;
    if List(words, word -> VVMF_Word(state, word)) <> targets then
        return VVMF_Failure("WordRecoveryFailed", "Cayley word verification failed.");
    fi;
    return words;
end;

# Summary: Recover and verify a word for an actual element in the original group.
# Parameters: state is an accepted construction state; element belongs to state.group.
# Returns: Typed syllable list whose evaluation equals element, or structured failure.
# Effects: May cache native word maps; bounded fallback uses state.wordRecoveryBudget.
# Options/defaults: state.wordRecoveryStrategy defaults to Native; FP bypasses the native
# preimage route and Cayley uses only the explicitly bounded graph search.
# Failures: Wrong-group target, invalid native correspondence or exhausted fallback budget.
# Example: VVMF_EncodeWord(state,One(state.group)) = [].
# Remarks: Native preimages are followed by a presentation-isomorphism fallback when the
# native method returns fail, then by bounded Cayley search. A native GAP error terminates
# the isolated attempt; the coordinator must retry with another recovery route/model.
# See also: VVMF_WordMap; VVMF_FpWordMap; VVMF_WordSearch.
VVMF_EncodeWord := function(state, element)
    local mapping, word, result, attempt, strategy, attempts;
    if not IsRecord(state) or not IsBound(state.group) or not element in state.group then
        return VVMF_Failure("InvalidElement", "Expected an element of the recorded group.");
    fi;
    strategy := "Native";
    if IsBound(state.wordRecoveryStrategy) then strategy := state.wordRecoveryStrategy; fi;
    if not strategy in ["Native","FP","Cayley"] then
        return VVMF_Failure("InvalidWordStrategy", "Unknown word recovery strategy.");
    fi;
    if element = One(state.group) then return []; fi;
    if strategy = "Cayley" then
        if not IsBound(state.wordRecoveryBudget) then
            return VVMF_Failure("InvalidWordBudget", "Cayley recovery requires explicit bounded resources.");
        fi;
        result := VVMF_WordSearch(state,[element],state.wordRecoveryBudget);
        if VVMF_IsFailure(result) then return result; fi;
        return result[1];
    fi;
    if strategy = "FP" then
        mapping := VVMF_FpWordMap(state);
        attempts := [1];
    else
        mapping := VVMF_WordMap(state);
        attempts := [1,2];
    fi;
    for attempt in attempts do
        word := fail;
        if not VVMF_IsFailure(mapping) then
            if mapping.kind = "Presentation" then
                word := UnderlyingElement(element);
            elif mapping.kind = "Epimorphism" then
                word := PreImagesRepresentative(mapping.map, element);
            elif mapping.kind = "FPIsomorphism" then
                word := UnderlyingElement(Image(mapping.map, element));
            fi;
        fi;
        if word <> fail then
            result := VVMF_WordSyllables(word, state.names);
            if not VVMF_IsFailure(result) and VVMF_Word(state, result) = element then
                return result;
            fi;
        fi;
        if attempt = 1 and strategy = "Native" then mapping := VVMF_FpWordMap(state); fi;
    od;
    if IsBound(state.wordRecoveryBudget) then
        result := VVMF_WordSearch(state, [element], state.wordRecoveryBudget);
        if VVMF_IsFailure(result) then return result; fi;
        return result[1];
    fi;
    return VVMF_Failure("WordRecoveryFailed", "No valid native word and no bounded fallback budget.");
end;

# Summary: Recover an ordered collection of words, sharing one Cayley traversal when selected.
# Parameters/defaults: state is finite with the same strategy/budget as VVMF_EncodeWord;
# elements is an ordered list of actual elements. No options.
# Returns: Parallel list of verified named syllables, or structured failure.
# Effects: Native routes cache maps; Cayley uses one bounded predecessor tree for all targets.
# Failures: Invalid list, any invalid element/recovery or missing/exhausted Cayley budget.
# Example: VVMF_EncodeWords(state,[One(state.group),state.generators[1]]) preserves that order.
# See also: VVMF_EncodeWord; VVMF_WordSearch; VVMF_Export.
VVMF_EncodeWords := function(state,elements)
    local words;
    if not IsRecord(state) or not IsBound(state.group) or not IsList(elements) then
        return VVMF_Failure("InvalidElement", "Expected finite state and an element list.");
    fi;
    if IsBound(state.wordRecoveryStrategy) and state.wordRecoveryStrategy = "Cayley" then
        if not IsBound(state.wordRecoveryBudget) then
            return VVMF_Failure("InvalidWordBudget", "Cayley recovery requires explicit bounded resources.");
        fi;
        return VVMF_WordSearch(state,elements,state.wordRecoveryBudget);
    fi;
    words := List(elements,element -> VVMF_EncodeWord(state,element));
    if ForAny(words,VVMF_IsFailure) then return First(words,VVMF_IsFailure); fi;
    return words;
end;

# Summary: Certify the exact recorded generators by a finite presentation.
# Parameters/defaults: state is a verified finite construction; no options.
# Returns: Named typed presentation, or WordRecoveryFailed.
# Effects: Caches a presentation only after a bijective native map checks every generator.
# Failures: A missing map or changed generator order cannot supply a certificate.
# Example: a SmallGroup catalogue entry retains its generator relations for reconstruction.
# Remarks: The certificate's proven order comes from the owned original group, not from
# an imported claim. A later group of that order satisfying these relators and generated
# by the corresponding elements is isomorphic through those precise generators.
# See also: VVMF_FpWordMap; VVMF_RebindGroup in GroupBinding.g.
VVMF_GeneratorPresentation := function(state)
    local map, target, relators, certificate;
    if not IsRecord(state) or not IsBound(state.group) or not IsBound(state.generators) or
        not IsBound(state.names) then
        return VVMF_Failure("WordRecoveryFailed","A finite recorded generating set is required.");
    fi;
    if IsBound(state.generatorPresentation) then return state.generatorPresentation; fi;
    if state.order = 1 then
        relators := List(state.names,name -> [[name,"1"]]);
    elif IsFpGroup(state.group) and state.generators = GeneratorsOfGroup(state.group) then
        relators := List(RelatorsOfFpGroup(state.group),word -> VVMF_WordSyllables(word,state.names));
    else
        map := IsomorphismFpGroupByGenerators(state.group,state.generators);
        if map = fail or not IsBijective(map) then
            return VVMF_Failure("WordRecoveryFailed","No generator presentation isomorphism was obtained.");
        fi;
        target := Image(map);
        if List(state.generators,g -> Image(map,g)) <> GeneratorsOfGroup(target) then
            return VVMF_Failure("WordRecoveryFailed","The presentation changed recorded generator correspondence.");
        fi;
        relators := List(RelatorsOfFpGroup(target),word -> VVMF_WordSyllables(word,state.names));
    fi;
    if ForAny(relators,VVMF_IsFailure) or
        not ForAll(relators,word -> VVMF_Word(state,word) = One(state.group)) then
        return VVMF_Failure("WordRecoveryFailed","The generator presentation has invalid relators.");
    fi;
    certificate := rec(type := "presentation",names := ShallowCopy(state.names),relators := relators);
    state.generatorPresentation := certificate;
    return certificate;
end;
