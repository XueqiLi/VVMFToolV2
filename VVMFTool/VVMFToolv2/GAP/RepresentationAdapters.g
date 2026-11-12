# Title: Native representation construction routes
# Summary: Adapters producing candidate generator images from GAP and package algorithms.
# Dependencies: Diagnostics, Scalars, Groups, CharacterTransfer (VVMF_ResultWord), GroupData,
# Dependencies (VVMF_Guarded, VVMF_UseAtlasRep); REPSN, SL2Reps and AtlasRep are loaded on demand.
# Contracts: adapters return images of the recorded generators (or candidate lists); they never
# accept anything themselves. Every result is verified by VVMF_VerifyRep in Representations.g.
# See also: GAP/Representations.g; VVMF_Model; VVMFArch/step2Plan.md (concrete algorithm adapters).

# Summary: Multiply generator images along a letter representation.
# Parameters/defaults: images are invertible matrices; letters are signed 1-based positions; dimension d.
# Returns: The d by d product matrix.
# Effects: Pure.
# Failures: Caller supplies valid positions.
# Example: VVMF_LetterMatrix([[[0,1],[1,0]]],[1,1],2) = IdentityMat(2).
# See also: VVMF_RepRelators; VVMF_WordMatrix.
VVMF_LetterMatrix := function(images, letters, dimension)
    local product, letter;
    product := IdentityMat(dimension);
    for letter in letters do
        if letter > 0 then product := product * images[letter];
        else product := product * images[-letter]^-1; fi;
    od;
    return product;
end;

# Summary: Pull a model representation back to images of the recorded generators.
# Parameters/defaults: state; model; rho is a general mapping defined on model.group.
# Returns: List of image matrices (one per recorded generator).
# Effects: Pure evaluation through GAP's mapping operations (works for composed mappings).
# Failures: Caller guards the call; malformed mappings raise errors caught by VVMF_Guarded.
# Example: Dixon on the Permutation model gives images of the original generators.
# See also: VVMF_Model; VVMF_Representations.
VVMF_RepImages := function(state, model, rho)
    return List(state.generators, g -> Immutable(Image(rho, Image(model.fromOriginal, g))));
end;

# Summary: Candidate images of SL(2,Z) irreps whose own S,T map to the assigned S,T words.
# Parameters/defaults: state with an explicit modular assignment.
# Returns: List of image lists, one per candidate that defines a homomorphism of the actual group,
# or InapplicableMethod/DependencyUnavailable failure.
# Effects: May load sl2reps; caches the S,T presentation in state for this assignment.
# Failures: No assignment; package unavailable; errors in the package calls.
# Example: for 24-3I the degree-two SL(2,Z/3) irreps give candidates.
# Remarks: SL2Reps uses S = [[0,1],[-1,0]] and T = [[1,1],[0,1]]; the candidate's S and T are
# assigned to the group's S and T words exactly (no S^-1 substitution). Levels are the divisors of
# the order of the assigned T; level one supplies the trivial representation.
# See also: VVMF_Representations; VVMF_CheckST.
VVMF_SL2Candidates := function(state)
    local s, t, iso, relators, words, candidates, n, irreps, irrep, images, generatorWords;
    if not IsBound(state.modularAssignment) then
        return VVMF_Failure("InapplicableMethod", "SL2Reps requires an explicit S,T assignment.");
    fi;
    if LoadPackage("sl2reps") <> true then
        return VVMF_Failure("DependencyUnavailable", "The SL2Reps package is unavailable.");
    fi;
    s := VVMF_Word(state, state.modularAssignment.sWord);
    t := VVMF_Word(state, state.modularAssignment.tWord);
    if not IsBound(state.stPresentation) or state.stPresentation.identity <> state.modularAssignment.identity then
        iso := VVMF_Guarded(function() return IsomorphismFpGroupByGenerators(state.group, [s, t]); end);
        if not iso.ok or iso.value = fail then
            return VVMF_Failure("InapplicableMethod", "No presentation on the assigned S,T was obtained.");
        fi;
        state.stPresentation := rec(identity := state.modularAssignment.identity,
            relators := List(RelatorsOfFpGroup(Range(iso.value)), LetterRepAssocWord),
            generatorWords := List(state.generators, g -> LetterRepAssocWord(UnderlyingElement(Image(iso.value, g)))));
    fi;
    relators := state.stPresentation.relators;
    generatorWords := state.stPresentation.generatorWords;
    candidates := [];
    for n in DivisorsInt(Order(t)) do
        if n = 1 then irreps := [rec(S := [[1]], T := [[1]], degree := 1)];
        else
            irreps := VVMF_Guarded(function() return ValueGlobal("SL2IrrepsOfLevel")(n); end);
            if not irreps.ok then return irreps; fi;
            irreps := irreps.value;
        fi;
        for irrep in irreps do
            if ForAll(relators, letters -> VVMF_LetterMatrix([irrep.S, irrep.T], letters, irrep.degree) =
                    IdentityMat(irrep.degree)) then
                Add(candidates, List(generatorWords, letters -> Immutable(VVMF_LetterMatrix([irrep.S, irrep.T], letters, irrep.degree))));
            fi;
        od;
    od;
    return candidates;
end;

# Summary: Read the explicit subgroup (and optional subgroup representation) of MethodData.
# Parameters/defaults: state; model; methodData with subgroupGenerators (stable-ID words) and optional
# representation (one exact scalar-record matrix per subgroup generator).
# Returns: rec(group, generators, representation) on the model, representation fail when absent;
# or InvalidMethodData failure.
# Effects: Evaluates the words; builds the subgroup's homomorphism when matrices are supplied.
# Failures: Invalid words, a trivial generating list, malformed matrices, or matrices that are not a
# representation of the subgroup on those generators.
# Example: MethodData with the words of (1,2,3),(1,2)(3,4) gives A4 inside S4.
# See also: VVMF_SubgroupRepresentation.
VVMF_MethodSubgroup := function(state, model, methodData)
    local elements, generators, group, matrices, hom;
    if not IsRecord(methodData) or not IsBound(methodData.subgroupGenerators) or
        not IsList(methodData.subgroupGenerators) or methodData.subgroupGenerators = [] then
        return VVMF_Failure("InvalidMethodData", "MethodData requires nonempty subgroup generator words.");
    fi;
    elements := List(methodData.subgroupGenerators, word -> VVMF_ResultWord(state, word));
    if ForAny(elements, VVMF_IsFailure) then
        return VVMF_Failure("InvalidMethodData", "A subgroup generator word is invalid.");
    fi;
    generators := List(elements, e -> Image(model.fromOriginal, e));
    group := Subgroup(model.group, generators);
    if not IsBound(methodData.representation) or methodData.representation = fail then
        return rec(group := group, generators := generators, representation := fail);
    fi;
    matrices := methodData.representation;
    if not IsList(matrices) or Length(matrices) <> Length(generators) then
        return VVMF_Failure("InvalidMethodData", "Expected one subgroup matrix per subgroup generator.");
    fi;
    matrices := List(matrices, m -> List(m, row -> List(row, VVMF_DecodeScalar)));
    if ForAny(Flat(matrices), VVMF_IsFailure) or not ForAll(matrices, IsMatrix) then
        return VVMF_Failure("InvalidMethodData", "Invalid subgroup representation matrices.");
    fi;
    hom := VVMF_Guarded(function() return GroupHomomorphismByImages(group,
        Group(matrices, IdentityMat(Length(matrices[1]))), generators, matrices); end);
    if not hom.ok or hom.value = fail then
        return VVMF_Failure("InvalidMethodData", "The supplied matrices do not represent the subgroup.");
    fi;
    return rec(group := group, generators := generators, representation := hom.value);
end;

# Summary: Evaluate an induced representation in coset-block coordinates.
# Parameters/defaults: group G; subgroup H; rhoH a representation of H; x an element of G.
# Returns: The block matrix with block (i,j) = rhoH(h) where t_i x = h t_j for the right transversal t.
# Effects: Computes a right transversal (cached by GAP).
# Failures: Caller supplies a subgroup and a representation mapping on it.
# Example: inducing the trivial representation of H gives the permutation matrix of x on cosets.
# Remarks: This is a homomorphism (blocks multiply along cosets) whose trace is the induced
# character; the matrices are unitary whenever rhoH is unitary, because they are block permutations
# of unitary blocks.
# See also: VVMF_SubgroupRepresentation (InducedUnitary).
VVMF_InducedMatrix := function(group, subgroup, rhoH, x)
    local transversal, n, d, matrix, i, j, y, h, block, r, c;
    transversal := RightTransversal(group, subgroup);
    n := Length(transversal);
    d := Length(Image(rhoH, One(subgroup)));
    matrix := NullMat(n * d, n * d);
    for i in [1..n] do
        y := transversal[i] * x;
        j := PositionCanonical(transversal, y);
        h := y * transversal[j]^-1;
        block := Image(rhoH, h);
        for r in [1..d] do
            for c in [1..d] do matrix[(i - 1) * d + r][(j - 1) * d + c] := block[r][c]; od;
        od;
    od;
    return matrix;
end;

# Summary: Find a subgroup and irreducible character inducing chi, by bounded low-index search.
# Parameters/defaults: group G; chi an irreducible character of G.
# Returns: rec(group := H, character := psi) with Induced(psi) = chi exactly, or InapplicableMethod.
# Effects: Computes subgroups of index at most chi(1) up to conjugacy and their character tables.
# Failures: No proper subgroup of index dividing the degree induces chi (chi not monomial there).
# Example: every irreducible character of a supersolvable group is induced from a linear one.
# See also: VVMF_SubgroupRepresentation.
VVMF_InducingPair := function(group, chi)
    local subgroup, index, psi;
    for subgroup in LowIndexSubgroups(group, chi[1]) do
        index := Index(group, subgroup);
        if index > 1 and chi[1] mod index = 0 then
            for psi in Irr(subgroup) do
                if psi[1] = chi[1] / index and InducedClassFunction(psi, group) = chi then
                    return rec(group := subgroup, character := psi);
                fi;
            od;
        fi;
    od;
    return VVMF_Failure("InapplicableMethod", "No low-index subgroup induces this character.");
end;

# Summary: Find a subgroup to which chi restricts irreducibly (maximal or normal subgroups).
# Parameters/defaults: group G; chi irreducible; normal — Boolean.
# Returns: rec(group := H, character := phi), or InapplicableMethod failure.
# Effects: Computes maximal subgroups (normal = false) or normal subgroups (normal = true).
# Failures: No proper subgroup of the searched kind with irreducible restriction.
# Example: an irreducible character of S_n restricting irreducibly to A_n.
# See also: VVMF_SubgroupRepresentation.
VVMF_ExtendingPair := function(group, chi, normal)
    local candidates, subgroup, phi;
    if normal then
        candidates := Filtered(NormalSubgroups(group), n -> Size(n) < Size(group) and Size(n) > 1);
        SortBy(candidates, n -> -Size(n));
    else
        candidates := List(ConjugacyClassesMaximalSubgroups(group), Representative);
    fi;
    for subgroup in candidates do
        phi := RestrictedClassFunction(chi, subgroup);
        if IsIrreducibleCharacter(phi) then return rec(group := subgroup, character := phi); fi;
    od;
    return VVMF_Failure("InapplicableMethod", "No proper subgroup restricts this character irreducibly.");
end;

# Summary: Character of a representation of a subgroup, from traces on its classes.
# Parameters/defaults: subgroup H; rhoH a representation of H.
# Returns: The class function of H afforded by rhoH.
# Effects: Computes conjugacy classes of H.
# Failures: None for representation mappings.
# Example: the trivial representation affords the trivial character.
# See also: VVMF_SubgroupRepresentation.
VVMF_AffordedCharacter := function(subgroup, rhoH)
    return ClassFunction(subgroup, List(ConjugacyClasses(subgroup), c -> TraceMat(Image(rhoH, Representative(c)))));
end;

# Summary: Images of one irrep through subgroup routes: CharacterSubgroup, Induction, InducedUnitary,
# Extension or NormalExtension.
# Parameters/defaults: state; model; method; chi — the requested irreducible character on model.group;
# methodData — fail or rec(subgroupGenerators, optional representation).
# Returns: Images of the recorded generators, or InapplicableMethod/InvalidMethodData/DependencyUnavailable.
# Effects: May load REPSN; runs bounded subgroup searches when no MethodData subgroup is supplied.
# Failures: A supplied subgroup equal to the whole group (InvalidMethodData, except for
# CharacterSubgroup); a subgroup whose (supplied or found) character does not induce chi or restrict
# to an irreducible character; a non-normal subgroup for NormalExtension; a nonunitary supplied subgroup
# representation for InducedUnitary; missing REPSN for the routes using it.
# Example: A4 irreducible of degree 3 is induced from a linear character of V4.
# Remarks: Reducible inductions are rejected before construction (Induced(psi) = chi exactly) and the
# result is still verified on the actual group. Induction uses REPSN's InducedSubgroupRepresentation;
# InducedUnitary builds coset-block coordinates from a unitary subgroup representation (linear
# characters directly, otherwise unitary Dixon on the subgroup). Subgroup work is on a different,
# smaller group, so recursion never returns to the same missing irrep.
# See also: VVMF_InducedMatrix; VVMF_InducingPair; VVMF_ExtendingPair; step2Plan.md adapters.
VVMF_SubgroupRepresentation := function(state, model, method, chi, methodData)
    local group, supplied, subgroup, rhoH, psi, pair, rho, repsn;
    group := model.group;
    repsn := method <> "InducedUnitary";
    if repsn and LoadPackage("repsn") <> true then
        return VVMF_Failure("DependencyUnavailable", "The REPSN package is unavailable.");
    fi;
    supplied := fail;
    if methodData <> fail and IsBound(methodData.subgroupGenerators) then
        supplied := VVMF_MethodSubgroup(state, model, methodData);
        if VVMF_IsFailure(supplied) then return supplied; fi;
        # Induction and extension need a proper subgroup (REPSN's normal extension would not terminate
        # for H = G); a character subgroup equal to G is the linear case handled by REPSN.
        if method <> "CharacterSubgroup" and Size(supplied.group) = Size(group) then
            return VVMF_Failure("InvalidMethodData", "Induction and extension require a proper subgroup.");
        fi;
    fi;
    if method = "CharacterSubgroup" then
        if supplied = fail then rho := ValueGlobal("CharacterSubgroupRepresentation")(chi);
        elif not ValueGlobal("IsCharacterSubgroup")(chi, supplied.group) then
            return VVMF_Failure("InapplicableMethod", "The supplied subgroup is not a character subgroup of chi.");
        else rho := ValueGlobal("CharacterSubgroupRepresentation")(chi, supplied.group); fi;
        return VVMF_RepImages(state, model, rho);
    fi;
    if method in ["Induction", "InducedUnitary"] then
        if supplied = fail then
            pair := VVMF_InducingPair(group, chi);
            if VVMF_IsFailure(pair) then return pair; fi;
            subgroup := pair.group; psi := pair.character; rhoH := fail;
        else
            subgroup := supplied.group; rhoH := supplied.representation;
            if rhoH <> fail then
                psi := VVMF_AffordedCharacter(subgroup, rhoH);
                if InducedClassFunction(psi, group) <> chi then
                    return VVMF_Failure("InapplicableMethod", "The supplied representation does not induce chi.");
                fi;
            else
                psi := First(Irr(subgroup), p -> p[1] * Index(group, subgroup) = chi[1] and
                    InducedClassFunction(p, group) = chi);
                if psi = fail then return VVMF_Failure("InapplicableMethod", "No character of the subgroup induces chi."); fi;
            fi;
        fi;
        if method = "Induction" then
            if rhoH = fail then rhoH := ValueGlobal("IrreducibleAffordingRepresentation")(psi); fi;
            return VVMF_RepImages(state, model, ValueGlobal("InducedSubgroupRepresentation")(group, rhoH));
        fi;
        if rhoH = fail then
            if psi[1] = 1 then
                rhoH := GroupHomomorphismByImages(subgroup, Group(List(GeneratorsOfGroup(subgroup), g -> [[g^psi]])),
                    GeneratorsOfGroup(subgroup), List(GeneratorsOfGroup(subgroup), g -> [[g^psi]]));
            else
                rhoH := IrreducibleRepresentationsDixon(subgroup, psi : unitary);
            fi;
        fi;
        if not ForAll(GeneratorsOfGroup(subgroup), g -> Image(rhoH, g) * TransposedMat(ComplexConjugate(Image(rhoH, g))) =
                IdentityMat(psi[1])) then
            return VVMF_Failure("InapplicableMethod", "InducedUnitary requires a unitary subgroup representation.");
        fi;
        return List(state.generators, g -> Immutable(VVMF_InducedMatrix(group, subgroup, rhoH, Image(model.fromOriginal, g))));
    fi;
    if method in ["Extension", "NormalExtension"] then
        if supplied = fail then
            pair := VVMF_ExtendingPair(group, chi, method = "NormalExtension");
            if VVMF_IsFailure(pair) then return pair; fi;
            subgroup := pair.group; rhoH := fail;
        else
            subgroup := supplied.group; rhoH := supplied.representation;
            if method = "NormalExtension" and not IsNormal(group, subgroup) then
                return VVMF_Failure("InapplicableMethod", "NormalExtension requires a normal subgroup.");
            fi;
        fi;
        psi := RestrictedClassFunction(chi, subgroup);
        if not IsIrreducibleCharacter(psi) then
            return VVMF_Failure("InapplicableMethod", "The character does not restrict irreducibly to the subgroup.");
        fi;
        if rhoH = fail then rhoH := ValueGlobal("IrreducibleAffordingRepresentation")(psi);
        elif VVMF_AffordedCharacter(subgroup, rhoH) <> psi then
            return VVMF_Failure("InapplicableMethod", "The supplied representation does not afford the restriction.");
        fi;
        if method = "Extension" then rho := ValueGlobal("ExtendedRepresentation")(chi, rhoH);
        else rho := ValueGlobal("ExtendedRepresentationNormal")(chi, rhoH); fi;
        return VVMF_RepImages(state, model, rho);
    fi;
    return VVMF_Failure("InvalidRequest", "Unknown subgroup representation route.");
end;

# Summary: Candidate images from the Baum-Clausen monomial representations of a solvable model.
# Parameters/defaults: state; model with a solvable group.
# Returns: List of candidate image lists, or InapplicableMethod/AdapterError failure.
# Effects: Computes BaumClausenInfo of the model group.
# Failures: Nonsolvable models. Irreps outside the computed factor group (nontrivial kernel) have
# no candidate; the caller reports them as not produced by this route.
# Example: all irreps of SL(2,3) except those not covered by its kernel quotient.
# Remarks: Images of pcgs elements are E(exponent)^lin for linear representations and monomial
# matrices with entry (r, perm[r]) = E(exponent)^diag[perm[r]] for nonlinear ones; a recorded
# generator's image is the product of pcgs images to the exponents of its pc expression.
# See also: BaumClausenInfo in ctblsolv.gd; VVMF_Representations.
VVMF_BaumClausenCandidates := function(state, model)
    local info, root, pcgs, exponents, monomial, reps, rep, candidates;
    if not IsSolvableGroup(model.group) then
        return VVMF_Failure("InapplicableMethod", "Baum-Clausen requires a solvable group.");
    fi;
    info := VVMF_Guarded(function() return BaumClausenInfo(model.group); end);
    if not info.ok then return info; fi;
    info := info.value;
    root := E(info.exponent);
    pcgs := info.pcgs;
    exponents := List(state.generators, g -> ExponentsOfPcElement(pcgs, Image(model.fromOriginal, g)));
    monomial := function(record)
        local d, matrix, r;
        d := Length(record.perm);
        matrix := NullMat(d, d);
        for r in [1..d] do matrix[r][record.perm[r]] := root^record.diag[record.perm[r]]; od;
        return matrix;
    end;
    reps := Concatenation(List(info.lin, lin -> List(lin, x -> [[root^x]])),
        List(info.nonlin, rep -> List(rep, monomial)));
    candidates := [];
    for rep in reps do
        Add(candidates, List(exponents, e -> Immutable(Product([1..Length(e)], i -> rep[i]^e[i], rep[1]^0))));
    od;
    return candidates;
end;

# Summary: Candidate images from local characteristic-zero AtlasRep data with a verified group map.
# Parameters/defaults: state; model; methodData — fail or rec(atlasName, optional representationNumber).
# Returns: List of candidate image lists, or InapplicableMethod/DependencyUnavailable failure.
# Effects: Loads AtlasRep with remote access disabled; computes IsomorphismGroups from the model group
# to each Atlas matrix group.
# Failures: No Atlas name (MethodData, or derivable for catalogue alternating/symmetric groups); no
# characteristic-zero data stored locally (DependencyUnavailable, never downloaded); no isomorphism.
# Example: A5 with its local degree-3, 4 and 5 data (Q(sqrt5) and integral) gives candidates.
# Remarks: The name never establishes correspondence: images come from an actual isomorphism to the
# Atlas group, and every candidate is verified on the recorded generators. Galois conjugates of each
# candidate are added, because the chosen isomorphism can differ from the standard-generator one by
# an automorphism that exchanges conjugate characters (A5's two degree-three irreps).
# See also: VVMF_UseAtlasRep; AllAtlasGeneratingSetInfos; step2Plan.md AtlasRep adapter.
VVMF_AtlasCandidates := function(state, model, methodData)
    local ready, name, construction, infos, info, generators, iso, candidates, missing, images, conjugate, k;
    ready := VVMF_UseAtlasRep();
    if VVMF_IsFailure(ready) then return ready; fi;
    construction := state.construction;
    if methodData <> fail and IsBound(methodData.atlasName) then name := methodData.atlasName;
    elif IsBound(construction.catalogue) and construction.catalogue in ["AlternatingGroup", "SymmetricGroup"] then
        name := Concatenation(construction.catalogue{[1]}, construction.key);
    else
        return VVMF_Failure("InapplicableMethod", "AtlasRep requires MethodData naming the Atlas group.");
    fi;
    infos := VVMF_Guarded(function() return ValueGlobal("AllAtlasGeneratingSetInfos")(name, Characteristic, 0); end);
    if not infos.ok then return infos; fi;
    infos := infos.value;
    if methodData <> fail and IsBound(methodData.representationNumber) then
        infos := Filtered(infos, i -> String(i.repnr) = methodData.representationNumber);
    fi;
    if infos = [] then return VVMF_Failure("InapplicableMethod", "AtlasRep has no characteristic-zero data for this name."); fi;
    candidates := []; missing := 0;
    for info in infos do
        generators := VVMF_Guarded(function() return ValueGlobal("AtlasGenerators")(info); end);
        if not generators.ok or generators.value = fail then missing := missing + 1;
        else
            iso := VVMF_Guarded(function() return IsomorphismGroups(model.group,
                Group(generators.value.generators)); end);
            if iso.ok and iso.value <> fail then
                images := List(state.generators, g -> Immutable(Image(iso.value, Image(model.fromOriginal, g))));
                # The isomorphism is determined only up to automorphisms, which can permute Galois
                # conjugate characters; the Galois conjugates of the matrices are representations too.
                for k in PrimeResidues(Maximum(1, Conductor(Flat(images)))) do
                    conjugate := List(images, m -> Immutable(List(m, row -> List(row, x -> GaloisCyc(x, k)))));
                    if not conjugate in candidates then Add(candidates, conjugate); fi;
                od;
            fi;
        fi;
    od;
    if candidates = [] and missing = Length(infos) then
        return VVMF_Failure("DependencyUnavailable", "The Atlas data are not stored locally; they are never downloaded.");
    fi;
    return candidates;
end;
