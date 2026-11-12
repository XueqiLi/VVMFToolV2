# Title: Verified irreducible representation matrices
# Summary: Construct, verify, store, export and transfer native representations of the recorded generators.
# Dependencies: Diagnostics, Scalars, Groups, Characters, CharacterTransfer, GroupData, Dependencies
# (VVMF_Guarded), RepresentationAdapters (construction routes, VVMF_LetterMatrix, VVMF_RepImages);
# RepresentationBasis (unitarization and T diagonalization; loaded after this module and reached through
# ValueGlobal).
# Contracts: state has complete bound characters (boundCharacterData). Representations are keyed by
# stable irrep ID; a variant stores native images N of the recorded generators (its witness) and, for a
# scaled variant, real cyclotomic scales sigma (visible matrices L N L^-1, L^2 = DiagonalMat(sigma)),
# with an optional derivation rec(witness, conjugator) (N = C W C^-1 for the witness variant's images W).
# See also: Kernel/RepresentationStorage.wl; VVMFArch/step2Plan.md; VVMFArch/implementation/step2Status.md.

# Summary: Return the relators of a finite presentation on the recorded generators, cached in state.
# Parameters/defaults: state is a constructed finite state.
# Returns: List of letter representations (signed generator positions), or fail when unavailable.
# Effects: Computes IsomorphismFpGroupByGenerators once and stores state.representationRelators.
# Failures: A failing presentation computation returns fail; callers then use GroupHomomorphismByImages.
# Example: for C5 on one generator the relators include [1,1,1,1,1].
# Remarks: A matrix assignment on the generators is a representation exactly when every relator of
# a complete presentation of the actual group evaluates to the identity (plan:193).
# See also: VVMF_VerifyRep.
VVMF_RepRelators := function(state)
    local iso;
    if IsBound(state.representationRelators) then return state.representationRelators; fi;
    if Length(state.generators) = 0 then state.representationRelators := []; return []; fi;
    iso := VVMF_Guarded(function() return IsomorphismFpGroupByGenerators(state.group, state.generators); end);
    if not iso.ok or iso.value = fail then return fail; fi;
    state.representationRelators := List(RelatorsOfFpGroup(Range(iso.value)), LetterRepAssocWord);
    return state.representationRelators;
end;

# Summary: Evaluate a name-syllable word on generator images.
# Parameters/defaults: state supplies names; images one matrix per recorded generator; word is a
# list of [name, exponent string] pairs; dimension d.
# Returns: Product matrix, or InvalidWord failure.
# Effects: Pure.
# Failures: Unknown names or noncanonical exponents.
# Example: the empty word gives IdentityMat(d).
# See also: VVMF_Word; VVMF_ResultWordMatrix.
VVMF_WordMatrix := function(state, images, word, dimension)
    local product, pair, position, exponent;
    product := IdentityMat(dimension);
    for pair in word do
        position := Position(state.names, pair[1]);
        exponent := VVMF_DecodeInteger(pair[2]);
        if position = fail or VVMF_IsFailure(exponent) then
            return VVMF_Failure("InvalidWord", "Unknown generator or invalid exponent.");
        fi;
        product := product * images[position]^exponent;
    od;
    return product;
end;

# Summary: Evaluate a stable-generator-ID word on generator images.
# Parameters/defaults: state supplies generatorIDs; images, word (ID syllables) and dimension.
# Returns: Product matrix, or InvalidResultWord failure.
# Effects: Pure.
# Failures: Unknown generator IDs or invalid exponents.
# Example: class representative words of bound characters are ID words.
# See also: VVMF_ResultWord; VVMF_RepTraces.
VVMF_ResultWordMatrix := function(state, images, word, dimension)
    local names, pair, position;
    names := [];
    for pair in word do
        position := Position(state.generatorIDs, pair[1]);
        if position = fail then return VVMF_Failure("InvalidResultWord", "Unknown generator identity."); fi;
        Add(names, [state.names[position], pair[2]]);
    od;
    return VVMF_WordMatrix(state, images, names, dimension);
end;

# Summary: Read one bound irreducible character row by stable irrep ID.
# Parameters/defaults: state has boundCharacterData; irrepID is a string.
# Returns: rec(index, degree, values, words) with exact decoded values on the bound class words.
# Effects: Pure.
# Failures: Missing bound characters or an unknown irrep ID.
# Example: VVMF_BoundRow(state, id).degree is the character degree.
# See also: VVMF_VerifyRep; VVMF_Export.
VVMF_BoundRow := function(state, irrepID)
    local data, index;
    if not IsBound(state.boundCharacterData) then
        return VVMF_Failure("UnboundCharacterData", "Representations require bound complete characters.");
    fi;
    data := state.boundCharacterData;
    index := Position(data.irrepIDs, irrepID);
    if index = fail then return VVMF_Failure("InvalidIrrepID", "The irrep ID is not in the bound character table."); fi;
    return rec(index := index, degree := VVMF_DecodeInteger(data.degrees[index]),
        values := List(data.values[index], VVMF_DecodeScalar), words := data.classRepresentativeWords);
end;

# Summary: Check that images afford the bound character on every bound class word.
# Parameters/defaults: state, irrepID and one image per recorded generator.
# Returns: true or WrongCharacter/InvalidRepresentation failure.
# Effects: Pure matrix evaluation.
# Failures: A trace differing from the bound value on any class.
# Example: swapping two same-degree irreps' images fails this check.
# See also: VVMF_VerifyRep; VVMF_ExportRepresentations.
VVMF_RepTraces := function(state, irrepID, images)
    local row, k, matrix;
    row := VVMF_BoundRow(state, irrepID);
    if VVMF_IsFailure(row) then return row; fi;
    for k in [1..Length(row.words)] do
        matrix := VVMF_ResultWordMatrix(state, images, row.words[k], row.degree);
        if VVMF_IsFailure(matrix) then return matrix; fi;
        if TraceMat(matrix) <> row.values[k] then
            return VVMF_Failure("WrongCharacter", "The matrices do not afford the bound character.");
        fi;
    od;
    return true;
end;

# Summary: Verify that generator images form a representation affording one bound irreducible character.
# Parameters/defaults: state (complete bound characters); irrepID; images, one per recorded generator.
# Returns: true, or InvalidRepresentation/WrongCharacter failure.
# Effects: May compute and cache the relator presentation.
# Failures: Wrong image count, shapes, noncyclotomic or singular matrices, a relator not mapped to
# the identity (not a homomorphism of the actual group), or wrong class traces.
# Example: verified Dixon images of an A5 irrep return true.
# Remarks: The homomorphism check uses a complete presentation on the recorded generators, so a
# pair satisfying only universal modular relations of a different quotient is rejected. The
# zero-generator trivial group has no images; its only irrep has degree one.
# See also: VVMF_RepRelators; VVMF_RepTraces; VVMF_AdmitVariant.
VVMF_VerifyRep := function(state, irrepID, images)
    local row, d, relators, hom;
    row := VVMF_BoundRow(state, irrepID);
    if VVMF_IsFailure(row) then return row; fi;
    d := row.degree;
    if not IsList(images) or Length(images) <> Length(state.generators) then
        return VVMF_Failure("InvalidRepresentation", "Expected one matrix per recorded generator.");
    fi;
    if Length(images) = 0 then
        if d <> 1 then return VVMF_Failure("InvalidRepresentation", "The trivial group has only degree one."); fi;
        return true;
    fi;
    if not ForAll(images, m -> IsMatrix(m) and Length(m) = d and ForAll(m, r -> Length(r) = d) and
        ForAll(m, r -> ForAll(r, IsCyc))) then
        return VVMF_Failure("InvalidRepresentation", "Images must be square cyclotomic matrices of the character degree.");
    fi;
    if ForAny(images, m -> DeterminantMat(m) = 0) then
        return VVMF_Failure("InvalidRepresentation", "Generator images must be invertible.");
    fi;
    # Class traces first: they reject most candidate/irrep pairs far more cheaply than relators.
    hom := VVMF_RepTraces(state, irrepID, images);
    if VVMF_IsFailure(hom) then return hom; fi;
    relators := VVMF_RepRelators(state);
    if relators = fail then
        hom := VVMF_Guarded(function() return GroupHomomorphismByImages(state.group,
            Group(images, IdentityMat(d)), state.generators, images); end);
        if not hom.ok or hom.value = fail then
            return VVMF_Failure("InvalidRepresentation", "The images do not define a homomorphism of the group.");
        fi;
    elif ForAny(relators, letters -> VVMF_LetterMatrix(images, letters, d) <> IdentityMat(d)) then
        return VVMF_Failure("InvalidRepresentation", "The images do not satisfy the group's relators.");
    fi;
    return true;
end;

# Summary: Test whether a stored variant is an inert (Wolfram-exact or Numerical) record.
# Parameters/defaults: variant, a stored variant record.
# Returns: Boolean.
# Effects: Pure.
# Failures: None.
# Example: a variant stored by the Inert method or imported with tier "Wolfram" is inert.
# Remarks: Inert variants carry their exported record unchanged (record) and no images; GAP never
# computes with them (R1: Wolfram verifies them at acceptance and correspondence import, the receipt
# covers them afterwards).
# See also: VVMF_InertRecordCheck; VVMF_ExportRepresentations.
VVMF_InertVariantQ := variant -> IsRecord(variant) and IsBound(variant.inert) and variant.inert = true;

# Summary: The recorded verification status of an inert record ("Exact" when none is recorded).
# Parameters/defaults: data, an inert variant record.
# Returns: "Exact", "Numerical" or "Unverified".
# Effects: Pure.
# Failures: None.
# Example: VVMF_InertStatus(rec(tier := "Wolfram")) is "Exact".
# See also: VVMF_InertRecordCheck; VVMF_RepProperties.
VVMF_InertStatus := function(data)
    if IsBound(data.verificationStatus) then return data.verificationStatus; fi;
    return "Exact";
end;

# Summary: Check the structure of an inert variant record (no arithmetic).
# Parameters/defaults: state (bound characters); irrepID; data, an exported variant record with tier
# "Wolfram" (arithmetic "Exact") or "Numerical" (arithmetic "Numerical" and a precision string).
# Returns: true, or InvalidRepresentation failure.
# Effects: Pure.
# Failures: Wrong tier/arithmetic, image count, shapes, entries that are not tagged records, or malformed
# sourceMethod, basisProperties or derivation fields.
# Example: a Wolfram-tier record of one 2 by 2 matrix per generator passes.
# Remarks: Entries are Wolfram scalar records (algebraic or numerical) that GAP stores and exports as is. An optional
# verificationStatus ("Exact", "Numerical", "Unverified") is kept and re-exported with the record (C7: a variant
# admitted at Numerical or None lives in GAP only as such an inert record).
# See also: VVMF_InertVariantQ; Kernel/RepresentationStorage.wl decodeRepVariant.
VVMF_InertRecordCheck := function(state, irrepID, data)
    local row, d, invalid, shapeQ;
    row := VVMF_BoundRow(state, irrepID);
    if VVMF_IsFailure(row) then return row; fi;
    d := row.degree;
    invalid := VVMF_Failure("InvalidRepresentation", "Malformed inert representation variant.");
    shapeQ := m -> IsList(m) and Length(m) = d and ForAll(m, r -> IsList(r) and Length(r) = d and ForAll(r, IsRecord));
    if not IsRecord(data) or not IsBound(data.tier) or not data.tier in ["Wolfram", "Numerical"] or
        not IsBound(data.arithmetic) or not IsBound(data.matrices) or not IsBound(data.sourceMethod) or
        not IsBound(data.basisProperties) then
        return invalid;
    fi;
    if (data.tier = "Wolfram" and data.arithmetic <> "Exact") or (data.tier = "Numerical" and
        (data.arithmetic <> "Numerical" or not IsBound(data.precision) or not IsString(data.precision))) then
        return invalid;
    fi;
    if not IsList(data.matrices) or Length(data.matrices) <> Length(state.generators) or
        not ForAll(data.matrices, shapeQ) then
        return invalid;
    fi;
    if not IsRecord(data.sourceMethod) or not IsBound(data.sourceMethod.method) or not IsString(data.sourceMethod.method) or
        not IsBound(data.sourceMethod.model) or not IsString(data.sourceMethod.model) or
        not IsRecord(data.basisProperties) or not IsBound(data.basisProperties.unitary) or
        not data.basisProperties.unitary in [true, false] or not IsBound(data.basisProperties.tDiagonal) or
        not IsBound(data.basisProperties.assignmentIdentity) then
        return invalid;
    fi;
    # an optional recorded verification status (methodOptionsPlan.md 2C, C7): the vocabulary only
    if IsBound(data.verificationStatus) and not data.verificationStatus in ["Exact", "Numerical", "Unverified"] then
        return invalid;
    fi;
    if IsBound(data.derivation) and (not IsRecord(data.derivation) or not IsBound(data.derivation.witness) or
        not IsString(data.derivation.witness) or not IsBound(data.derivation.conjugator) or
        not shapeQ(data.derivation.conjugator)) then
        return invalid;
    fi;
    return true;
end;

# Summary: Store an inert variant record under a new or reused variant ID.
# Parameters/defaults: state; irrepID; data, a checked inert record.
# Returns: rec(variant := ID, added := true), or failure.
# Effects: Adds to state.representations; never changes the active or partial pointers.
# Failures: As VVMF_InertRecordCheck.
# Example: a Supplied Wolfram-tier record is stored as "Supplied-User".
# Remarks: A record with the same tier and matrices as a stored inert variant reuses it. IDs are
# <method>-<model> with a numeric suffix when taken.
# See also: VVMF_Representations (method Inert); VVMF_AdmitScaledVariant.
VVMF_AdmitInertVariant := function(state, irrepID, data)
    local checked, entry, id, suffix;
    checked := VVMF_InertRecordCheck(state, irrepID, data);
    if VVMF_IsFailure(checked) then return checked; fi;
    if not IsBound(state.representations) then state.representations := rec(); fi;
    if not IsBound(state.representations.(irrepID)) then
        state.representations.(irrepID) := rec(variants := rec(), activeVariant := fail, acceptedPartial := fail);
    fi;
    entry := state.representations.(irrepID);
    # a stored record is reused only with the same tier, matrices and recorded status (a weak record never merges with
    # a verified one)
    id := First(RecNames(entry.variants), name -> VVMF_InertVariantQ(entry.variants.(name)) and
        entry.variants.(name).record.tier = data.tier and entry.variants.(name).record.matrices = data.matrices and
        VVMF_InertStatus(entry.variants.(name).record) = VVMF_InertStatus(data));
    if id = fail then
        id := Concatenation(data.sourceMethod.method, "-", data.sourceMethod.model);
        suffix := 1;
        while IsBound(entry.variants.(id)) do
            suffix := suffix + 1;
            id := Concatenation(data.sourceMethod.method, "-", data.sourceMethod.model, "-", String(suffix));
        od;
        entry.variants.(id) := rec(inert := true, record := Immutable(data), images := fail, scales := fail,
            derivation := fail, method := data.sourceMethod.method, model := data.sourceMethod.model);
    fi;
    return rec(variant := id, added := true);
end;

# Summary: Compute the actual basis properties of a verified variant.
# Parameters/defaults: state; variant, a record with images and optional scales (or a bare list of
# images); dimension d.
# Returns: rec(unitary, tDiagonal, assignmentIdentity); the latter two are fail without an assignment.
# Effects: Pure.
# Failures: None for verified images.
# Example: images of a permutation-matrix representation are unitary.
# Remarks: Unitarity is checked on every recorded generator with exact conjugate transposes: for a
# scaled variant as N^dagger S N = S (VVMF_ScaledUnitaryQ). T-diagonality evaluates the assigned T word on
# N (a diagonal scaling does not change it); it is recomputed on every export (R6).
# See also: VVMF_ExportRepresentations; VVMF_ScaledUnitaryQ.
VVMF_RepProperties := function(state, variant, d)
    local unitary, t, images, scales, stored;
    # Inert variants: the properties Wolfram verified; T-diagonality counts only under the assignment it
    # was verified for (R6), and a Numerical variant, or one whose recorded status is weaker than Exact (C8),
    # never outranks (rank -1: active only when chosen).
    if VVMF_InertVariantQ(variant) then
        stored := variant.record.basisProperties;
        if not IsBound(state.modularAssignment) then
            return rec(unitary := stored.unitary, tDiagonal := fail, assignmentIdentity := fail,
                numerical := variant.record.tier = "Numerical" or VVMF_InertStatus(variant.record) <> "Exact");
        fi;
        return rec(unitary := stored.unitary, tDiagonal := stored.tDiagonal = true and
            stored.assignmentIdentity = state.modularAssignment.identity,
            assignmentIdentity := state.modularAssignment.identity, numerical := variant.record.tier = "Numerical" or VVMF_InertStatus(variant.record) <> "Exact");
    fi;
    if IsRecord(variant) then images := variant.images; else images := variant; fi;
    if IsRecord(variant) and IsBound(variant.scales) then scales := variant.scales; else scales := fail; fi;
    if scales = fail then
        unitary := ForAll(images, m -> m * TransposedMat(ComplexConjugate(m)) = IdentityMat(d));
    else
        unitary := ValueGlobal("VVMF_ScaledUnitaryQ")(images, scales);
    fi;
    if not IsBound(state.modularAssignment) then
        return rec(unitary := unitary, tDiagonal := fail, assignmentIdentity := fail);
    fi;
    t := VVMF_WordMatrix(state, images, state.modularAssignment.tWord, d);
    return rec(unitary := unitary, tDiagonal := IsDiagonalMat(t),
        assignmentIdentity := state.modularAssignment.identity);
end;

# Summary: Rank of basis properties: -1 numerical, 0 general, 1 unitary, 2 unitary with diagonal T.
# Parameters/defaults: props from VVMF_RepProperties.
# Returns: 0, 1 or 2.
# Effects: Pure.
# Failures: None.
# Example: a unitary variant without an assignment has rank 1.
# See also: VVMF_AdmitScaledVariant; VVMF_RepSatisfied.
VVMF_BasisRank := function(props)
    if IsBound(props.numerical) and props.numerical then return -1; fi;
    if not props.unitary then return 0; fi;
    if props.tDiagonal = true then return 2; fi;
    return 1;
end;

# Summary: Rank a requested basis needs: "General" 0, "Unitary" 1, "UnitaryTDiagonal" 2.
# Parameters/defaults: basis string.
# Returns: 0, 1 or 2.
# Effects: Pure.
# Failures: None; unknown names give 0.
# Example: VVMF_RequiredRank("Unitary") = 1.
# See also: VVMF_BasisRank.
VVMF_RequiredRank := basis -> Position(["General", "Unitary", "UnitaryTDiagonal"], basis) - 1;

# Summary: Store a verified (possibly scaled) variant and apply the active/partial rules.
# Parameters/defaults: state; irrepID; record rec(images, scales := list or fail, derivation := rec(witness,
# conjugator) or fail); source rec(method, model); basis "General", "Unitary", "UnitaryTDiagonal", or "None"
# (store the variant and leave the pointers to the caller).
# Returns: rec(variant := ID, added := Boolean), or verification failure.
# Effects: Adds to state.representations; may set activeVariant or acceptedPartial.
# Failures: Verification failures leave the state unchanged; scales must be real cyclotomics.
# Example: under a unitary request a verified nonunitary variant becomes acceptedPartial.
# Remarks: Identical images and scales reuse their variant. New IDs are <method>-<model>, with a numeric
# suffix when taken by different data (randomized routes). Ranks order the bases (general < unitary <
# unitary with diagonal T). Under a General request the first variant becomes active. Otherwise a variant
# becomes active when it has rank at least one, outranks the active variant and the active variant is
# below the requested rank; a general variant never demotes a unitary active variant and becomes the
# accepted partial when nothing is active. A partial that becomes active, or any partial beside a unitary
# active variant, is cleared.
# See also: VVMF_VerifyRep; VVMF_AdmitVariant; step2Status.md representation state rules.
VVMF_AdmitScaledVariant := function(state, irrepID, record, source, basis)
    local checked, entry, id, suffix, d, scales, derivation, variant, rank, activeRank;
    checked := VVMF_VerifyRep(state, irrepID, record.images);
    if VVMF_IsFailure(checked) then return checked; fi;
    scales := fail; derivation := fail;
    if IsBound(record.scales) then scales := record.scales; fi;
    if IsBound(record.derivation) then derivation := record.derivation; fi;
    if scales <> fail and (not IsList(scales) or Length(scales) <> Length(record.images[1]) or
        not ForAll(scales, x -> IsCyc(x) and x <> 0 and ComplexConjugate(x) = x) or scales[1] <> 1) then
        return VVMF_Failure("InvalidRepresentation", "Scales must be nonzero real cyclotomics with the first equal to one.");
    fi;
    if not IsBound(state.representations) then state.representations := rec(); fi;
    if not IsBound(state.representations.(irrepID)) then
        state.representations.(irrepID) := rec(variants := rec(), activeVariant := fail, acceptedPartial := fail);
    fi;
    entry := state.representations.(irrepID);
    id := First(RecNames(entry.variants), name -> entry.variants.(name).images = record.images and
        entry.variants.(name).scales = scales);
    if id = fail then
        id := Concatenation(source.method, "-", source.model);
        suffix := 1;
        while IsBound(entry.variants.(id)) do
            suffix := suffix + 1;
            id := Concatenation(source.method, "-", source.model, "-", String(suffix));
        od;
        entry.variants.(id) := rec(images := Immutable(record.images), scales := Immutable(scales),
            derivation := Immutable(derivation), method := source.method, model := source.model);
    fi;
    d := VVMF_BoundRow(state, irrepID).degree;
    variant := entry.variants.(id);
    # An explicit mutation admits first and sets the pointers itself (replaceActive, atomic commits).
    if basis = "None" then return rec(variant := id, added := true); fi;
    rank := VVMF_BasisRank(VVMF_RepProperties(state, variant, d));
    activeRank := -1;
    if entry.activeVariant <> fail then
        activeRank := VVMF_BasisRank(VVMF_RepProperties(state, entry.variants.(entry.activeVariant), d));
    fi;
    if basis = "General" then
        if entry.activeVariant = fail or activeRank < 0 then entry.activeVariant := id; fi;
    elif rank >= 1 then
        if rank > activeRank and activeRank < VVMF_RequiredRank(basis) then entry.activeVariant := id; fi;
    elif entry.activeVariant = fail and entry.acceptedPartial = fail then
        entry.acceptedPartial := id;
    fi;
    # An active variant supersedes a partial it reproduces; a unitary active variant clears any partial.
    if entry.acceptedPartial <> fail and (entry.acceptedPartial = entry.activeVariant or
        (entry.activeVariant <> fail and VVMF_RepProperties(state, entry.variants.(entry.activeVariant), d).unitary)) then
        entry.acceptedPartial := fail;
    fi;
    return rec(variant := id, added := true);
end;

# Summary: Store verified native images as a variant (VVMF_AdmitScaledVariant without scales).
# Parameters/defaults: state; irrepID; images; source rec(method, model); basis.
# Returns: As VVMF_AdmitScaledVariant.
# Effects: As VVMF_AdmitScaledVariant.
# Failures: As VVMF_AdmitScaledVariant.
# Example: under a unitary request a verified nonunitary variant becomes acceptedPartial.
# See also: VVMF_AdmitScaledVariant.
VVMF_AdmitVariant := function(state, irrepID, images, source, basis)
    return VVMF_AdmitScaledVariant(state, irrepID, rec(images := images, scales := fail, derivation := fail), source, basis);
end;

# Summary: Store computed images matched by their class traces only, as an inert record with a weak status (C7).
# Parameters/defaults: state; irrepID; images, one cyclotomic matrix per recorded generator; source rec(method,
# model); basis (the request's, or "None" for an explicit mutation); status "Numerical" or "Unverified".
# Returns: rec(variant := ID, added := true), or a failure.
# Effects: Adds an inert Wolfram-tier record carrying the status; makes it active by the admission rank rule with
# variants ranked by their basis properties (the request is at the weak level), never under "None".
# Failures: InvalidRepresentation (shape, noncyclotomic or singular images); WrongCharacter (traces).
# Example: under request.verify = "Traces" a Dixon candidate of the right character is stored inert, unproved.
# Remarks: The relator (homomorphism) proof of VVMF_VerifyRep is skipped: that is what Verification -> None or
# "Numerical" skips in GAP (methodOptionsPlan.md 2C.4); GAP never computes with the record afterwards.
# See also: VVMF_VerifyRep; VVMF_AdmitInertVariant; VVMF_InertStatus.
VVMF_AdmitTracedVariant := function(state, irrepID, images, source, basis, status)
    local row, d, traces, props, record, admitted, entry, traceRank, rank, activeRank;
    row := VVMF_BoundRow(state, irrepID);
    if VVMF_IsFailure(row) then return row; fi;
    d := row.degree;
    if not IsList(images) or Length(images) <> Length(state.generators) or Length(images) = 0 or
        not ForAll(images, m -> IsMatrix(m) and Length(m) = d and ForAll(m, r -> Length(r) = d) and ForAll(m, r -> ForAll(r, IsCyc))) or
        ForAny(images, m -> DeterminantMat(m) = 0) then
        return VVMF_Failure("InvalidRepresentation", "Images must be invertible square cyclotomic matrices of the character degree.");
    fi;
    traces := VVMF_RepTraces(state, irrepID, images);
    if VVMF_IsFailure(traces) then return traces; fi;
    props := VVMF_RepProperties(state, images, d);
    record := rec(tier := "Wolfram", arithmetic := "Exact",
        matrices := List(images, m -> List(m, r -> List(r, ValueGlobal("VVMF_EncodeRepScalar")))),
        sourceMethod := rec(method := source.method, model := source.model),
        basisProperties := rec(unitary := props.unitary, tDiagonal := props.tDiagonal, assignmentIdentity := props.assignmentIdentity),
        verificationStatus := status);
    admitted := VVMF_AdmitInertVariant(state, irrepID, record);
    if VVMF_IsFailure(admitted) then return admitted; fi;
    entry := state.representations.(irrepID);
    if basis = "None" then return admitted; fi;
    # The request is at the weak level, so variants are ranked by their basis properties (a weak inert variant counts
    # as its properties, a Numerical-tier one stays -1): the admission rule of VVMF_AdmitScaledVariant at that level.
    traceRank := function(variant)
        local p;
        p := ShallowCopy(VVMF_RepProperties(state, variant, d));
        if VVMF_InertVariantQ(variant) and variant.record.tier <> "Numerical" then p.numerical := false; fi;
        return VVMF_BasisRank(p);
    end;
    rank := traceRank(entry.variants.(admitted.variant));
    activeRank := -1;
    if entry.activeVariant <> fail then activeRank := traceRank(entry.variants.(entry.activeVariant)); fi;
    if entry.activeVariant = fail or (basis = "General" and activeRank < 0) or
        (rank > activeRank and activeRank < VVMF_RequiredRank(basis)) then
        entry.activeVariant := admitted.variant;
    fi;
    return admitted;
end;

# Summary: Test whether an irrep already has an active variant satisfying the requested basis.
# Parameters/defaults: state; irrepID; basis "General", "Unitary" or "UnitaryTDiagonal".
# Returns: Boolean.
# Effects: Pure.
# Failures: None.
# Example: after a unitary Dixon run the irrep satisfies both "Unitary" and "General".
# See also: VVMF_Representations; VVMF_BasisRank.
VVMF_RepSatisfied := function(state, irrepID, basis)
    local entry;
    if not IsBound(state.representations) or not IsBound(state.representations.(irrepID)) then return false; fi;
    entry := state.representations.(irrepID);
    if entry.activeVariant = fail then return false; fi;
    return VVMF_BasisRank(VVMF_RepProperties(state, entry.variants.(entry.activeVariant),
        VVMF_BoundRow(state, irrepID).degree)) >= VVMF_RequiredRank(basis);
end;

# Summary: Transport a bound irreducible character to a verified computational model.
# Parameters/defaults: state; model record from VVMF_Model; irrepID.
# Returns: Character of CharacterTable(model.group), or failure.
# Effects: Computes conjugacy classes of both groups.
# Failures: Unknown irrep ID or a model class without a bound original class.
# Example: VVMF_ModelCharacter(state, VVMF_Model(state,"Permutation"), id)[1] is the degree.
# See also: VVMF_Model; VVMF_Representations.
VVMF_ModelCharacter := function(state, model, irrepID)
    local row, elements, table, values, class, preimage, k;
    row := VVMF_BoundRow(state, irrepID);
    if VVMF_IsFailure(row) then return row; fi;
    elements := List(row.words, word -> VVMF_ResultWord(state, word));
    table := CharacterTable(model.group);
    values := [];
    for class in ConjugacyClasses(table) do
        preimage := PreImagesRepresentative(model.fromOriginal, Representative(class));
        k := PositionProperty(elements, e -> IsConjugate(state.group, e, preimage));
        if k = fail then return VVMF_Failure("InvalidClassMap", "A model class has no bound original class."); fi;
        Add(values, row.values[k]);
    od;
    return Character(table, values);
end;

# Summary: Candidate generator images for the linear character of a degree-one irrep.
# Parameters/defaults: state; irrepID of a degree-one bound character.
# Returns: List of 1 by 1 matrices (empty for no generators), or InapplicableMethod failure.
# Effects: Pure.
# Failures: A nonlinear character.
# Example: the sign character of S3 maps a transposition to [[-1]].
# See also: VVMF_Representations.
VVMF_LinearCharacterImages := function(state, irrepID)
    local row, elements, images, g, k;
    row := VVMF_BoundRow(state, irrepID);
    if VVMF_IsFailure(row) then return row; fi;
    if row.degree <> 1 then return VVMF_Failure("InapplicableMethod", "LinearCharacter applies to degree-one irreps."); fi;
    elements := List(row.words, word -> VVMF_ResultWord(state, word));
    images := [];
    for g in state.generators do
        k := PositionProperty(elements, e -> IsConjugate(state.group, e, g));
        Add(images, [[row.values[k]]]);
    od;
    return images;
end;

# Summary: Seconds remaining until a wall-clock deadline in nanoseconds since the epoch.
# Parameters/defaults: deadline — nanoseconds since the epoch, or infinity.
# Returns: A positive integer number of seconds (at least 1), or infinity.
# Effects: Reads the wall clock.
# Failures: None.
# Example: VVMF_SecondsLeft(infinity) = infinity.
# See also: VVMF_TimedGuarded; VVMF_Representations.
VVMF_SecondsLeft := function(deadline)
    if deadline = infinity then return infinity; fi;
    return Maximum(1, QuoInt(deadline - NanosecondsSinceEpoch(), 1000000000));
end;

# Summary: The variant record of an explicit representation mutation.
# Parameters/defaults: state; irrepID; method "Supplied", "BasisChange" or "DerivedNative"; request with
# supplied := rec(irrepID -> request-scalar matrices), basisChange := rec(irrepID -> rec(witness,
# matrix)) or derived := rec(irrepID -> rec(witness, conjugator, scales)).
# Returns: rec(record := rec(images, scales, derivation), source := rec(method, model)), or failure.
# Effects: Pure.
# Failures: InvalidRequest (missing or malformed data); InapplicableMethod (a witness that is not a plain
# native variant); UnprovedIdentity (derived scales that do not give unitary matrices).
# Example: a basis change b of a native variant W gives images b W b^-1 derived from W.
# Remarks: Admission verifies every record like any native variant (relators, class traces), so a
# supplied matrix set of another character is WrongCharacter. A basis change or a Wolfram unitarization
# (conjugator C = L^dagger, scales sigma = D of the LDL-adjoint factorization) is recomputed here as
# N = C W C^-1 from the stored witness, so nothing unverified is stored.
# See also: VVMF_Representations; VVMF_AdmitScaledVariant.
VVMF_MutationRecord := function(state, irrepID, method, request)
    local data, witness, images, conjugator, scales;
    if method = "Supplied" then
        if not IsBound(request.supplied) or not IsBound(request.supplied.(irrepID)) then
            return VVMF_Failure("InvalidRequest", "Supplied matrices are required.");
        fi;
        images := List(request.supplied.(irrepID), ValueGlobal("VVMF_DecodeRequestMatrix"));
        if ForAny(images, VVMF_IsFailure) then return First(images, VVMF_IsFailure); fi;
        return rec(record := rec(images := images, scales := fail, derivation := fail),
            source := rec(method := "Supplied", model := "User"));
    fi;
    if method = "BasisChange" then
        if not IsBound(request.basisChange) then return VVMF_Failure("InvalidRequest", "A basis change is required."); fi;
        data := request.basisChange;
    else
        if not IsBound(request.derived) then return VVMF_Failure("InvalidRequest", "A derived transformation is required."); fi;
        data := request.derived;
    fi;
    if not IsRecord(data) or not IsBound(data.(irrepID)) or not IsBound(data.(irrepID).witness) then
        return VVMF_Failure("InvalidRequest", "A witness and transformation are required.");
    fi;
    data := data.(irrepID);
    if not IsBound(state.representations) or not IsBound(state.representations.(irrepID)) or
        not IsBound(state.representations.(irrepID).variants.(data.witness)) then
        return VVMF_Failure("InvalidRequest", "The witness variant is not stored.");
    fi;
    witness := state.representations.(irrepID).variants.(data.witness);
    if VVMF_InertVariantQ(witness) or witness.scales <> fail then
        return VVMF_Failure("InapplicableMethod", "The witness must be a native (unscaled) variant.");
    fi;
    if method = "BasisChange" then
        conjugator := ValueGlobal("VVMF_DecodeRequestMatrix")(data.matrix); scales := fail;
    else
        conjugator := ValueGlobal("VVMF_DecodeRequestMatrix")(data.conjugator);
        scales := List(data.scales, VVMF_DecodeScalar);
        if ForAny(scales, VVMF_IsFailure) then return VVMF_Failure("InvalidRequest", "Invalid scales."); fi;
    fi;
    if VVMF_IsFailure(conjugator) or Length(conjugator) <> Length(witness.images[1]) or DeterminantMat(conjugator) = 0 then
        return VVMF_Failure("InvalidRequest", "The transformation must be an invertible matrix of the degree.");
    fi;
    images := List(witness.images, w -> conjugator * w * conjugator^-1);
    if scales <> fail then
        if not ValueGlobal("VVMF_ScaledUnitaryQ")(images, scales) then
            return VVMF_Failure("UnprovedIdentity", "The derived scales do not give unitary matrices.");
        fi;
        scales := scales / scales[1];
        if ForAll(scales, x -> x = 1) then scales := fail; fi;
    fi;
    return rec(record := rec(images := images, scales := scales, derivation := rec(witness := data.witness, conjugator := conjugator)),
        source := rec(method := method, model := data.witness));
end;

# Summary: Compute requested missing irreps with one explicitly selected native method and model.
# Parameters/defaults: state; request with method, model and representationRequest =
# rec(irrepIDs, basis) (basis "General", "Unitary" or "UnitaryTDiagonal"), optional
# softDeadlineMilliseconds (wall clock from this call's start), optional methodData
# (subgroupGenerators/representation for subgroup routes; atlasName and representationNumber for
# AtlasRep; randomSeed reseeds each randomized construction child with seed + the irrep's position in the bound
# character table (independent of partitioning), so runs
# stay reproducible while retries can differ), optional unitarize ("Automatic", "BSGSAverage" or "GroupAverage": phase 2, a general route's
# verified output is also unitarized), phaseOrder/phaseConvention for TDiagonalize, and for explicit
# mutations supplied/basisChange/derived data (VVMF_MutationRecord) or inert (irrep ID -> Wolfram-verified
# inert record, method Inert), replaceActive (irrep IDs whose new
# variant becomes active), atomicCommit (activate all selected irreps or fail with AtomicTransformFailed),
# force (transform already satisfied irreps) and, for constructions, verify ("Full", default, or "Traces": the
# trace match only, the variant stored inert with verificationStatus "Unverified" or the request's
# verificationStatus, and no GAP unitarization; VVMF_AdmitTracedVariant).
# Methods "Unitarize" and "TDiagonalize" transform an irrep's existing variant of smallest conductor
# instead of constructing one: Unitarize gives a scaled unitary variant; TDiagonalize (which needs a
# modular assignment) gives a unitary variant with diagonal T, starting from a unitary witness's own
# form or from an invariant form of a general witness.
# Returns: true when at least one variant was added or every requested irrep is already satisfied;
# otherwise InapplicableMethod (no applicable irrep) or RepresentationMethodFailed.
# Effects: Adds verified variants; under a General request promotes an irrep's accepted partial to
# active (outcome "PromotedPartial") before any construction; records per-irrep outcomes in
# state.representationOutcomes.
# Failures: Invalid requests, unknown IDs, unavailable packages; per-irrep adapter errors are data.
# Example: VVMF_Representations(state, rec(method:="Dixon", model:="Original",
#     representationRequest:=rec(irrepIDs:=ids, basis:="General"))) = true for A5.
# Remarks: Each construction runs in a guarded child limited to the time left before the soft
# deadline, and after the soft deadline no new irrep is started, so the attempt saves its verified
# subset before the hard deadline even when one irrep's route does not terminate (D5). Routes returning all
# irreps store only requested missing IDs.
# See also: VVMF_AdmitVariant; VVMF_Guarded; step2Plan.md adapters.
VVMF_Representations := function(state, request)
    local methods, method, spec, ids, basis, model, start, deadline, outcomes, pending, id,
        result, candidates, added, used, tried, methodData, images, position, share, unitarize, options,
        admitUnitarized, witness, variant, degree, seed, reseed, replaceActive, atomicCommit, admission, admitted, mutation,
        activate, witnessMode, verifyMode, weakStatus, admitComputed;
    methods := ["LinearCharacter", "SL2Reps", "DixonUnitary", "BaumClausen", "InducedUnitary", "Dixon",
        "REPSN", "CharacterSubgroup", "Induction", "Extension", "NormalExtension", "AtlasRep", "GAP",
        "Unitarize", "TDiagonalize", "Supplied", "BasisChange", "DerivedNative", "Inert"];
    if not IsRecord(request) or not IsBound(request.method) or not request.method in methods or
        not IsBound(request.representationRequest) or not IsRecord(request.representationRequest) then
        return VVMF_Failure("InvalidRequest", "Expected a representation method and request.");
    fi;
    method := request.method;
    spec := request.representationRequest;
    if not IsBound(spec.irrepIDs) or not IsList(spec.irrepIDs) or not IsBound(spec.basis) or
        not spec.basis in ["Unitary", "General", "UnitaryTDiagonal"] then
        return VVMF_Failure("InvalidRequest", "Expected irrep IDs and a General, Unitary or UnitaryTDiagonal basis.");
    fi;
    unitarize := fail;
    if IsBound(request.unitarize) then
        if not request.unitarize in ["Automatic", "BSGSAverage", "GroupAverage"] then
            return VVMF_Failure("InvalidRequest", "Unknown unitarization method.");
        fi;
        unitarize := request.unitarize;
    fi;
    witnessMode := "Automatic";
    if IsBound(request.witness) then
        if not request.witness in ["Automatic", "Active", "SmallestConductor"] then
            return VVMF_Failure("InvalidRequest", "Unknown witness variant choice.");
        fi;
        witnessMode := request.witness;
    fi;
    # Verification of computed variants (methodOptionsPlan.md 2C.4): "Full" (VVMF_VerifyRep, default) or "Traces" (the
    # trace match only; the variant is stored inert with verificationStatus, C7). Constructions only.
    verifyMode := "Full"; weakStatus := "Unverified";
    if IsBound(request.verify) then
        if not request.verify in ["Full", "Traces"] then return VVMF_Failure("InvalidRequest", "Unknown verify mode."); fi;
        verifyMode := request.verify;
        if verifyMode = "Traces" then
            if method in ["Unitarize", "TDiagonalize", "Supplied", "BasisChange", "DerivedNative", "Inert"] then
                return VVMF_Failure("InvalidRequest", "verify Traces applies to constructions only.");
            fi;
            if IsBound(request.verificationStatus) then
                if not request.verificationStatus in ["Numerical", "Unverified"] then
                    return VVMF_Failure("InvalidRequest", "Unknown weak verification status.");
                fi;
                weakStatus := request.verificationStatus;
            fi;
            # GAP's unitarizer would make a native variant from unproved images: not in this mode
            unitarize := fail;
        fi;
    fi;
    admitComputed := function(id, images, source, basis)
        if verifyMode = "Traces" then return VVMF_AdmitTracedVariant(state, id, images, source, basis, weakStatus); fi;
        return VVMF_AdmitVariant(state, id, images, source, basis);
    end;
    options := rec(phaseOrder := "Ascending", phaseConvention := "None");
    if IsBound(request.phaseOrder) then options.phaseOrder := request.phaseOrder; fi;
    if IsBound(request.phaseConvention) then options.phaseConvention := request.phaseConvention; fi;
    # Explicit mutations: replaceActive names irreps whose new variant becomes active whatever its rank;
    # atomicCommit admits every result first and activates all selected irreps only if each one succeeded;
    # force treats already satisfied irreps as pending (a transform of existing entries).
    replaceActive := [];
    if IsBound(request.replaceActive) then replaceActive := request.replaceActive; fi;
    atomicCommit := IsBound(request.atomicCommit) and request.atomicCommit = true;
    admission := spec.basis;
    if atomicCommit or replaceActive <> [] then admission := "None"; fi;
    admitted := rec();
    if (spec.basis = "UnitaryTDiagonal" or method = "TDiagonalize") and not IsBound(state.modularAssignment) then
        return VVMF_Failure("MissingModularAssignment", "A T-diagonal basis requires a modular S,T assignment.");
    fi;
    ids := spec.irrepIDs;
    basis := spec.basis;
    if not IsBound(state.boundCharacterData) or not ForAll(ids, id -> id in state.boundCharacterData.irrepIDs) then
        return VVMF_Failure("InvalidIrrepID", "Every requested irrep ID must belong to the bound character table.");
    fi;
    model := VVMF_Model(state, request.model);
    if VVMF_IsFailure(model) then return model; fi;
    start := NanosecondsSinceEpoch();
    deadline := infinity;
    if IsBound(request.softDeadlineMilliseconds) then
        deadline := start + 1000000 * VVMF_DecodeInteger(request.softDeadlineMilliseconds);
    fi;
    # The candidate state shares records with its restored source; never mutate the source's.
    if IsBound(state.representations) then state.representations := StructuralCopy(state.representations); fi;
    outcomes := rec();
    added := 0;
    # A general request is met by an accepted general partial: promote it without recomputation.
    if basis = "General" and IsBound(state.representations) then
        for id in ids do
            if IsBound(state.representations.(id)) and state.representations.(id).activeVariant = fail and
                state.representations.(id).acceptedPartial <> fail then
                state.representations.(id).activeVariant := state.representations.(id).acceptedPartial;
                state.representations.(id).acceptedPartial := fail;
                outcomes.(id) := "PromotedPartial";
                added := added + 1;
            fi;
        od;
    fi;
    if IsBound(request.force) and request.force = true then pending := ShallowCopy(ids);
    else pending := Filtered(ids, id -> not VVMF_RepSatisfied(state, id, basis)); fi;
    for id in Difference(ids, pending) do
        if not IsBound(outcomes.(id)) then outcomes.(id) := "AlreadySatisfied"; fi;
    od;
    methodData := fail; seed := fail;
    if IsBound(request.methodData) and IsRecord(request.methodData) then
        methodData := ShallowCopy(request.methodData);
        # An explicit random seed reseeds randomized constructions; adapters never see it.
        if IsBound(methodData.randomSeed) then
            seed := VVMF_DecodeInteger(methodData.randomSeed);
            if VVMF_IsFailure(seed) or seed < 1 then return VVMF_Failure("InvalidRequest", "Invalid random seed."); fi;
            Unbind(methodData.randomSeed);
        fi;
        if RecNames(methodData) = [] then methodData := fail; fi;
    fi;
    reseed := function(offset)
        if seed <> fail then
            Reset(GlobalMersenneTwister, seed + offset); Reset(GlobalRandomSource, seed + offset);
        fi;
    end;
    # Admit the unitarized form of a just-admitted general variant (phase 2), derived from it.
    admitUnitarized := function(id, witnessName, unitarized)
        if VVMF_IsFailure(unitarized) then return unitarized; fi;
        return VVMF_AdmitScaledVariant(state, id, rec(images := unitarized.images, scales := unitarized.scales,
            derivation := rec(witness := witnessName, conjugator := unitarized.conjugator)),
            rec(method := Concatenation(method, "+", unitarized.formMethod), model := request.model), basis);
    end;
    if pending = [] then
        # Nothing left to construct.
    elif method in ["Unitarize", "TDiagonalize"] then
        for position in [1..Length(pending)] do
            id := pending[position];
            if NanosecondsSinceEpoch() > deadline then outcomes.(id) := "SoftDeadline"; continue; fi;
            witness := ValueGlobal("VVMF_WitnessVariantMode")(state, id, fail, witnessMode);
            if witness = fail then outcomes.(id) := "NoWitness"; continue; fi;
            variant := state.representations.(id).variants.(witness);
            degree := VVMF_BoundRow(state, id).degree;
            share := VVMF_SecondsLeft(deadline);
            if share <> infinity then share := Maximum(1, QuoInt(share, Length(pending) - position + 1)); fi;
            result := VVMF_TimedGuarded(share, function()
                local props, form, invariant;
                if method = "Unitarize" then
                    if unitarize = fail then unitarize := "Automatic"; fi;
                    return ValueGlobal("VVMF_Unitarize")(state, variant.images, degree, unitarize, fail);
                fi;
                props := VVMF_RepProperties(state, variant, degree);
                if props.unitary and variant.scales = fail then form := IdentityMat(degree);
                elif props.unitary then form := DiagonalMat(variant.scales);
                else
                    if unitarize = fail then unitarize := "Automatic"; fi;
                    invariant := ValueGlobal("VVMF_InvariantForm")(state, variant.images, degree, unitarize);
                    if VVMF_IsFailure(invariant) then return invariant; fi;
                    form := invariant.form;
                fi;
                return ValueGlobal("VVMF_TDiagonalize")(state, variant.images, degree, form, options);
            end);
            if result.ok and not VVMF_IsFailure(result.value) then
                images := result.value;
                result := VVMF_Guarded(function()
                    local label;
                    label := method;
                    if IsBound(images.formMethod) then label := Concatenation(method, "+", images.formMethod); fi;
                    return VVMF_AdmitScaledVariant(state, id, rec(images := images.images, scales := images.scales,
                        derivation := rec(witness := witness, conjugator := images.conjugator)),
                        rec(method := label, model := witness), admission);
                end);
            fi;
            if not result.ok then outcomes.(id) := result.tag;
            elif VVMF_IsFailure(result.value) then outcomes.(id) := result.value.tag;
            else added := added + 1; outcomes.(id) := "Added"; admitted.(id) := result.value.variant; fi;
        od;
    elif method = "Inert" then
        # Wolfram-verified records (R1): stored without arithmetic; pointers follow replaceActive/atomicCommit.
        for id in pending do
            if not IsBound(request.inert) or not IsRecord(request.inert) or not IsBound(request.inert.(id)) then
                outcomes.(id) := "InvalidRequest"; continue;
            fi;
            result := VVMF_Guarded(function() return VVMF_AdmitInertVariant(state, id, request.inert.(id)); end);
            if not result.ok then outcomes.(id) := result.tag;
            elif VVMF_IsFailure(result.value) then outcomes.(id) := result.value.tag;
            else added := added + 1; outcomes.(id) := "Added"; admitted.(id) := result.value.variant; fi;
        od;
    elif method in ["Supplied", "BasisChange", "DerivedNative"] then
        for id in pending do
            result := VVMF_Guarded(function() return VVMF_MutationRecord(state, id, method, request); end);
            if result.ok and not VVMF_IsFailure(result.value) then
                mutation := result.value;
                result := VVMF_Guarded(function()
                    return VVMF_AdmitScaledVariant(state, id, mutation.record, mutation.source, admission); end);
            fi;
            if not result.ok then outcomes.(id) := result.tag;
            elif VVMF_IsFailure(result.value) then outcomes.(id) := result.value.tag;
            else added := added + 1; outcomes.(id) := "Added"; admitted.(id) := result.value.variant; fi;
        od;
    elif method in ["GAP", "SL2Reps", "BaumClausen", "AtlasRep"] then
        # Routes producing a list of candidate representations; match each to requested IDs.
        # Candidates are computed in a timed child bounded by the soft deadline; verification and state
        # changes happen here, in the worker.
        result := VVMF_TimedGuarded(VVMF_SecondsLeft(deadline), function()
            reseed(0);
            if method = "GAP" then
                return List(IrreducibleRepresentations(model.group), rho -> VVMF_RepImages(state, model, rho));
            elif method = "SL2Reps" then return VVMF_SL2Candidates(state);
            elif method = "BaumClausen" then return VVMF_BaumClausenCandidates(state, model);
            fi;
            return VVMF_AtlasCandidates(state, model, methodData);
        end);
        if result.ok then candidates := result.value; else candidates := result; fi;
        if VVMF_IsFailure(candidates) then
            # The candidate computation is one timed step for all irreps: a timeout is the route's.
            for id in pending do
                if candidates.tag = "IrrepTimeout" then outcomes.(id) := "RouteTimeout";
                else outcomes.(id) := candidates.tag; fi;
            od;
        else
            used := [];
            for id in pending do
                if NanosecondsSinceEpoch() > deadline then outcomes.(id) := "SoftDeadline"; continue; fi;
                # One guarded step per irrep: an error while matching cannot end the worker.
                result := VVMF_Guarded(function()
                    local candidate, admitted;
                    for candidate in [1..Length(candidates)] do
                        if not candidate in used then
                            admitted := admitComputed(id, candidates[candidate],
                                rec(method := method, model := request.model), basis);
                            if not VVMF_IsFailure(admitted) then
                                Add(used, candidate);
                                return rec(tag := "Added", images := candidates[candidate], variant := admitted.variant);
                            fi;
                        fi;
                    od;
                    return rec(tag := "NoMatchingCandidate");
                end);
                if not result.ok then outcomes.(id) := result.tag;
                else
                    outcomes.(id) := result.value.tag;
                    if result.value.tag = "Added" then
                        added := added + 1;
                        if unitarize <> fail then
                            # Phase 2: unitarize the matched candidate in a child bounded by the time left.
                            variant := result.value;
                            degree := VVMF_BoundRow(state, id).degree;
                            result := VVMF_TimedGuarded(VVMF_SecondsLeft(deadline), function()
                                return ValueGlobal("VVMF_Unitarize")(state, variant.images, degree, unitarize, fail);
                            end);
                            if result.ok then result := VVMF_Guarded(function()
                                return admitUnitarized(id, variant.variant, result.value); end); fi;
                            if not result.ok then outcomes.(id) := result.tag;
                            elif VVMF_IsFailure(result.value) then outcomes.(id) := result.value.tag; fi;
                        fi;
                    fi;
                fi;
            od;
        fi;
    else
        if method in ["REPSN", "CharacterSubgroup", "Induction", "Extension", "NormalExtension"] and
            LoadPackage("repsn") <> true then
            for id in pending do outcomes.(id) := "DependencyUnavailable"; od;
            pending := [];
        fi;
        for position in [1..Length(pending)] do
            id := pending[position];
            if NanosecondsSinceEpoch() > deadline then outcomes.(id) := "SoftDeadline"; continue; fi;
            # Each remaining irrep gets an equal share of the time left, so one nonterminating route
            # cannot starve the others.
            share := VVMF_SecondsLeft(deadline);
            if share <> infinity then share := Maximum(1, QuoInt(share, Length(pending) - position + 1)); fi;
            # One construction per irrep in a timed child (bounded by its time share), then guarded
            # verification and admission here; errors and timeouts are data.
            result := VVMF_TimedGuarded(share, function()
                local images, chi, unitarized;
                # The irrep's position in the bound table, so results do not depend on how the missing
                # irreps are partitioned among workers.
                reseed(Position(state.boundCharacterData.irrepIDs, id));
                if method = "LinearCharacter" then
                    images := VVMF_LinearCharacterImages(state, id);
                else
                    chi := VVMF_ModelCharacter(state, model, id);
                    if VVMF_IsFailure(chi) then return chi; fi;
                    if method = "Dixon" then
                        images := VVMF_RepImages(state, model, IrreducibleRepresentationsDixon(model.group, chi));
                    elif method = "DixonUnitary" then
                        images := VVMF_RepImages(state, model, IrreducibleRepresentationsDixon(model.group, chi : unitary));
                    elif method = "REPSN" then
                        images := VVMF_RepImages(state, model, ValueGlobal("IrreducibleAffordingRepresentation")(chi));
                    else
                        images := VVMF_SubgroupRepresentation(state, model, method, chi, methodData);
                    fi;
                fi;
                # Phase 2: the unitarized form is computed in the same child (verified on admission).
                unitarized := fail;
                if unitarize <> fail and not VVMF_IsFailure(images) then
                    unitarized := ValueGlobal("VVMF_Unitarize")(state, images, Length(images[1]), unitarize, fail);
                fi;
                return rec(images := images, unitarized := unitarized);
            end);
            if result.ok and VVMF_IsFailure(result.value) then outcomes.(id) := result.value.tag;
            elif result.ok and VVMF_IsFailure(result.value.images) then outcomes.(id) := result.value.images.tag;
            elif not result.ok then outcomes.(id) := result.tag;
            else
                images := result.value;
                # The general variant is kept even when its unitarization fails (then its tag is reported).
                result := VVMF_Guarded(function()
                    local admitted, scaled;
                    admitted := admitComputed(id, images.images, rec(method := method, model := request.model), basis);
                    if VVMF_IsFailure(admitted) then return rec(tag := admitted.tag, added := false); fi;
                    if images.unitarized = fail then return rec(tag := "Added", added := true); fi;
                    scaled := admitUnitarized(id, admitted.variant, images.unitarized);
                    if VVMF_IsFailure(scaled) then return rec(tag := scaled.tag, added := true); fi;
                    return rec(tag := "Added", added := true);
                end);
                if not result.ok then outcomes.(id) := result.tag;
                else
                    outcomes.(id) := result.value.tag;
                    if result.value.added then added := added + 1; fi;
                fi;
            fi;
        od;
    fi;
    state.representationOutcomes := outcomes;
    # Explicit activation: every selected irrep (atomicCommit: all or none) makes its new variant active; a
    # replaced active variant stays stored, and the partial is cleared.
    activate := Filtered(RecNames(admitted), id -> atomicCommit or id in replaceActive);
    if atomicCommit and Set(RecNames(admitted)) <> Set(pending) then
        return VVMF_Failure("AtomicTransformFailed", "Not every selected irrep was transformed; no active variant changed.");
    fi;
    for id in activate do
        state.representations.(id).activeVariant := admitted.(id);
        state.representations.(id).acceptedPartial := fail;
    od;
    if added > 0 or pending = [] then return true; fi;
    tried := List(pending, id -> outcomes.(id));
    # A deterministic candidate route that produced no matching representation does not apply.
    if ForAll(tried, tag -> tag in ["InapplicableMethod", "DependencyUnavailable", "NoMatchingCandidate"]) then
        if ForAll(tried, tag -> tag = "DependencyUnavailable") then
            return VVMF_Failure("DependencyUnavailable", "A required package or data file is unavailable.");
        fi;
        return VVMF_Failure("InapplicableMethod", "The method does not apply to any requested irrep.");
    fi;
    return VVMF_Failure("RepresentationMethodFailed", "The method produced no verified requested irrep.");
end;

# Summary: Encode one representation matrix entry: cyclotomic data plus its minimal polynomial.
# Parameters/defaults: value is a GAP cyclotomic.
# Returns: VVMF_EncodeScalar's record; a nonrational value additionally carries minimalPolynomial,
# the primitive integer coefficients (lowest degree first, positive leading coefficient) of its
# minimal polynomial over the rationals.
# Effects: Pure.
# Failures: Noncyclotomic values fail as in VVMF_EncodeScalar.
# Example: VVMF_EncodeRepScalar(E(4)).minimalPolynomial = ["1","0","1"].
# Remarks: Representation constructions (for example unitary Dixon) produce entries of small degree
# embedded in cyclotomic fields of large conductor (1320 for A5); the consumer derives the exact
# canonical value from this polynomial by exact root isolation instead of reducing a sum over all
# conductor-th roots of unity. The exact cyclotomic data remain the native value.
# See also: VVMF_DecodeRepScalar; Kernel/RepresentationStorage.wl decodeNativeRepScalar.
VVMF_EncodeRepScalar := function(value)
    local record, coefficients;
    record := VVMF_EncodeScalar(value);
    if VVMF_IsFailure(record) or IsRat(value) then return record; fi;
    coefficients := CoefficientsOfUnivariatePolynomial(MinimalPolynomial(Rationals, value));
    coefficients := coefficients * Lcm(List(coefficients, DenominatorRat));
    coefficients := coefficients / Gcd(coefficients);
    if coefficients[Length(coefficients)] < 0 then coefficients := -coefficients; fi;
    record.minimalPolynomial := List(coefficients, String);
    return record;
end;

# Summary: Decode a representation matrix entry and check its declared minimal polynomial.
# Parameters/defaults: data is a VVMF_EncodeRepScalar record.
# Returns: The exact cyclotomic, or InvalidScalar failure.
# Effects: Pure.
# Failures: Invalid cyclotomic data, or a minimal polynomial field that is missing for an irrational
# value, present for a rational one, or different from the value's actual minimal polynomial.
# Example: VVMF_DecodeRepScalar(VVMF_EncodeRepScalar(E(5))) = E(5).
# See also: VVMF_EncodeRepScalar; VVMF_DecodeScalar.
VVMF_DecodeRepScalar := function(data)
    local plain, value;
    if not IsRecord(data) then return VVMF_Failure("InvalidScalar", "Expected a scalar record."); fi;
    plain := ShallowCopy(data);
    if IsBound(plain.minimalPolynomial) then Unbind(plain.minimalPolynomial); fi;
    value := VVMF_DecodeScalar(plain);
    if VVMF_IsFailure(value) then return value; fi;
    if VVMF_EncodeRepScalar(value) <> data then
        return VVMF_Failure("InvalidScalar", "The declared minimal polynomial does not match the value.");
    fi;
    return value;
end;

# Summary: Export stored representations as schema-2 representationData.
# Parameters/defaults: state with bound characters.
# Returns: Record keyed by irrep ID, fail when there are no representations, or a failure.
# Effects: Rechecks every variant's class traces against the bound rows (R2) and recomputes basis
# properties with the current assignment. Scaled variants export tier "ScaledNative" with their scales;
# derived variants export derivation rec(witness, conjugator).
# Failures: A stored variant that no longer affords its bound character; active/partial pointers that
# violate the decoder's invariants (InvalidRepresentation).
# Example: an A5 state with all five irreps exports five entries.
# See also: VVMF_Export; VVMF_RepAvailability; Kernel/RepresentationStorage.wl decoder.
VVMF_ExportRepresentations := function(state)
    local data, id, entry, variants, name, variant, checked, props, d;
    if not IsBound(state.representations) or RecNames(state.representations) = [] then return fail; fi;
    data := rec();
    for id in RecNames(state.representations) do
        entry := state.representations.(id);
        d := VVMF_BoundRow(state, id);
        if VVMF_IsFailure(d) then return d; fi;
        d := d.degree;
        variants := rec();
        for name in RecNames(entry.variants) do
            variant := entry.variants.(name);
            if VVMF_InertVariantQ(variant) then
                # The stored record as received, with basis properties for the current assignment.
                props := VVMF_RepProperties(state, variant, d);
                variants.(name) := ShallowCopy(variant.record);
                variants.(name).basisProperties := rec(unitary := props.unitary, tDiagonal := props.tDiagonal,
                    assignmentIdentity := props.assignmentIdentity);
                continue;
            fi;
            checked := VVMF_RepTraces(state, id, variant.images);
            if VVMF_IsFailure(checked) then return checked; fi;
            props := VVMF_RepProperties(state, variant, d);
            props := rec(unitary := props.unitary, tDiagonal := props.tDiagonal, assignmentIdentity := props.assignmentIdentity);
            variants.(name) := rec(tier := "Native", arithmetic := "Exact",
                matrices := List(variant.images, m -> List(m, row -> List(row, VVMF_EncodeRepScalar))),
                sourceMethod := rec(method := variant.method, model := variant.model),
                basisProperties := props);
            if IsBound(variant.scales) and variant.scales <> fail then
                variants.(name).tier := "ScaledNative";
                variants.(name).scales := List(variant.scales, VVMF_EncodeRepScalar);
            fi;
            if IsBound(variant.derivation) and variant.derivation <> fail then
                variants.(name).derivation := rec(witness := variant.derivation.witness,
                    conjugator := List(variant.derivation.conjugator, row -> List(row, VVMF_EncodeRepScalar)));
            fi;
        od;
        # The pointer invariants the Wolfram decoder enforces: a partial is a nonunitary variant that is
        # not active and never coexists with a unitary active variant.
        if entry.acceptedPartial <> fail and (entry.acceptedPartial = entry.activeVariant or
            variants.(entry.acceptedPartial).basisProperties.unitary or
            (entry.activeVariant <> fail and variants.(entry.activeVariant).basisProperties.unitary)) then
            return VVMF_Failure("InvalidRepresentation", "Inconsistent active and accepted-partial variants.");
        fi;
        data.(id) := rec(dimension := String(d), generatorIdentity := state.generatorIdentity,
            variants := variants, activeVariant := entry.activeVariant, acceptedPartial := entry.acceptedPartial);
    od;
    return data;
end;

# Summary: Group-level representation availability.
# Parameters/defaults: state with bound characters.
# Returns: "NotComputed", "Partial" or "Complete".
# Effects: Pure.
# Failures: None.
# Example: all irreps active gives "Complete" (user decision: an accepted active matrix set each).
# See also: VVMF_Export; representationAvailability in Kernel/RepresentationStorage.wl.
VVMF_RepAvailability := function(state)
    local ids;
    if not IsBound(state.representations) or RecNames(state.representations) = [] then return "NotComputed"; fi;
    ids := state.boundCharacterData.irrepIDs;
    if ForAll(ids, id -> IsBound(state.representations.(id)) and state.representations.(id).activeVariant <> fail) then
        return "Complete";
    fi;
    return "Partial";
end;

# Summary: Decode an exported matrix of representation scalars.
# Parameters/defaults: matrix, a list of rows of VVMF_EncodeRepScalar records.
# Returns: The cyclotomic matrix, or InvalidRepresentation failure.
# Effects: Pure.
# Failures: Malformed rows or entries.
# Example: VVMF_DecodeRepMatrix([[VVMF_EncodeRepScalar(E(4))]]) = [[E(4)]].
# See also: VVMF_ImportRepresentations; VVMF_DecodeRepScalar.
VVMF_DecodeRepMatrix := function(matrix)
    local decoded;
    if not IsList(matrix) or not ForAll(matrix, IsList) then
        return VVMF_Failure("InvalidRepresentation", "Invalid exact matrix.");
    fi;
    decoded := List(matrix, row -> List(row, VVMF_DecodeRepScalar));
    if ForAny(Flat(decoded), VVMF_IsFailure) then
        return VVMF_Failure("InvalidRepresentation", "Invalid exact matrix entry.");
    fi;
    return decoded;
end;

# Summary: Re-verify and attach exported representation data in this state.
# Parameters/defaults: state with bound characters; data is exported representationData; optional third
# argument, a list of irrep IDs whose incoming active variant is adopted whatever its rank (sibling transfer
# of explicit re-derivations; default none).
# Returns: true, or UnsupportedRepresentationData/InvalidRepresentation/RepresentationConflict failure.
# Effects: Adds variants under their exported IDs; the active variant follows the admission rules
# (adopted when none is active or when it outranks this state's active variant: general < unitary <
# unitary with diagonal T; otherwise this state's active basis is kept). Failed imports leave
# state.representations unchanged.
# Inert (Wolfram, Numerical) variants are stored as received after a structural check (Wolfram verifies
# them on correspondence import; R1).
# Failures: Unknown tiers, malformed inert records, wrong dimensions or generator identity, a variant
# that fails homomorphism or trace verification here, invalid scales, a derivation whose witness is
# missing or whose conjugator does not map the witness to the variant, or a variant ID already bound to
# other data.
# Example: a sibling worker's verified irreps are merged into the coherent state (D3).
# Remarks: Used for sibling transfer (D3), typed reconstruction (D6) and correspondence import (D7).
# Derivations are checked after all variants of an entry are attached, since a witness may be listed
# after the variant derived from it.
# See also: VVMF_TransferRepresentations; VVMF_RebindGroup; VVMF_ValidateImported.
VVMF_ImportRepresentations := function(state, data, arg...)
    local previous, restore, id, entry, target, name, variant, images, scales, derivation, checked, d, witness,
        rank, replaceActive;
    # Optional: irrep IDs whose incoming active variant is adopted whatever its rank (sibling transfer of an
    # explicit re-derivation, for example a partition of a forced phase-4 T diagonalization).
    replaceActive := [];
    if Length(arg) > 0 and IsList(arg[1]) then replaceActive := arg[1]; fi;
    if not IsRecord(data) then
        return VVMF_Failure("InvalidRepresentation", "Expected exported representation data.");
    fi;
    # Work on a copy: a worker's candidate state shares records with its restored source.
    if IsBound(state.representations) then
        previous := state.representations;
        state.representations := StructuralCopy(previous);
    else previous := fail; fi;
    # Any failure restores the previous representation state before returning.
    restore := function(failure)
        if previous = fail then Unbind(state.representations); else state.representations := previous; fi;
        return failure;
    end;
    rank := function(target, name, d)
        if name = fail then return -1; fi;
        return VVMF_BasisRank(VVMF_RepProperties(state, target.variants.(name), d));
    end;
    if not IsBound(state.representations) then state.representations := rec(); fi;
    for id in RecNames(data) do
        entry := data.(id);
        d := VVMF_BoundRow(state, id);
        if VVMF_IsFailure(d) then return restore(d); fi;
        d := d.degree;
        if not IsRecord(entry) or not IsBound(entry.dimension) or entry.dimension <> String(d) or
            not IsBound(entry.generatorIdentity) or entry.generatorIdentity <> state.generatorIdentity or
            not IsBound(entry.variants) or not IsRecord(entry.variants) or
            not IsBound(entry.activeVariant) or not IsBound(entry.acceptedPartial) then
            return restore(VVMF_Failure("InvalidRepresentation", "Representation entry identity or dimension mismatch."));
        fi;
        if not IsBound(state.representations.(id)) then
            state.representations.(id) := rec(variants := rec(), activeVariant := fail, acceptedPartial := fail);
        fi;
        target := state.representations.(id);
        for name in RecNames(entry.variants) do
            variant := entry.variants.(name);
            if IsRecord(variant) and IsBound(variant.tier) and variant.tier in ["Wolfram", "Numerical"] then
                # Inert: structure only; Wolfram verifies these on correspondence import (R1).
                checked := VVMF_InertRecordCheck(state, id, variant);
                if VVMF_IsFailure(checked) then return restore(checked); fi;
                if IsBound(target.variants.(name)) and (not VVMF_InertVariantQ(target.variants.(name)) or
                    target.variants.(name).record.tier <> variant.tier or target.variants.(name).record.matrices <> variant.matrices or
                    VVMF_InertStatus(target.variants.(name).record) <> VVMF_InertStatus(variant)) then
                    return restore(VVMF_Failure("RepresentationConflict", "A variant ID is already bound to different matrices."));
                fi;
                if not IsBound(target.variants.(name)) then
                    target.variants.(name) := rec(inert := true, record := Immutable(variant), images := fail, scales := fail,
                        derivation := fail, method := variant.sourceMethod.method, model := variant.sourceMethod.model);
                fi;
                continue;
            fi;
            if not IsRecord(variant) or not IsBound(variant.tier) or not variant.tier in ["Native", "ScaledNative"] or
                (variant.tier = "ScaledNative") <> IsBound(variant.scales) then
                return restore(VVMF_Failure("UnsupportedRepresentationData", "Unknown representation variant tier."));
            fi;
            images := List(variant.matrices, VVMF_DecodeRepMatrix);
            if ForAny(images, VVMF_IsFailure) then return restore(First(images, VVMF_IsFailure)); fi;
            checked := VVMF_VerifyRep(state, id, images);
            if VVMF_IsFailure(checked) then return restore(checked); fi;
            scales := fail;
            if IsBound(variant.scales) then
                scales := List(variant.scales, VVMF_DecodeRepScalar);
                if not IsList(variant.scales) or Length(scales) <> d or ForAny(scales, VVMF_IsFailure) or
                    not ForAll(scales, x -> x <> 0 and ComplexConjugate(x) = x) or scales[1] <> 1 or ForAll(scales, x -> x = 1) then
                    return restore(VVMF_Failure("InvalidRepresentation", "Invalid scales of a scaled variant."));
                fi;
            fi;
            derivation := fail;
            if IsBound(variant.derivation) then
                if not IsRecord(variant.derivation) or not IsBound(variant.derivation.witness) or
                    not IsString(variant.derivation.witness) or not IsBound(variant.derivation.conjugator) then
                    return restore(VVMF_Failure("InvalidRepresentation", "Invalid derivation of a variant."));
                fi;
                derivation := rec(witness := variant.derivation.witness,
                    conjugator := VVMF_DecodeRepMatrix(variant.derivation.conjugator));
                if VVMF_IsFailure(derivation.conjugator) then return restore(derivation.conjugator); fi;
            fi;
            if IsBound(target.variants.(name)) and (VVMF_InertVariantQ(target.variants.(name)) or target.variants.(name).images <> images or
                target.variants.(name).scales <> scales) then
                return restore(VVMF_Failure("RepresentationConflict", "A variant ID is already bound to different matrices."));
            fi;
            target.variants.(name) := rec(images := Immutable(images), scales := Immutable(scales),
                derivation := Immutable(derivation), method := variant.sourceMethod.method, model := variant.sourceMethod.model);
        od;
        # Derivations: the witness is a variant of this irrep and the conjugator maps it to the variant.
        for name in RecNames(entry.variants) do
            derivation := target.variants.(name).derivation;
            if derivation <> fail then
                if not IsBound(target.variants.(derivation.witness)) or not IsMatrix(derivation.conjugator) or
                    Length(derivation.conjugator) <> d or DeterminantMat(derivation.conjugator) = 0 then
                    return restore(VVMF_Failure("InvalidRepresentation", "A derivation's witness is missing or its conjugator is invalid."));
                fi;
                witness := target.variants.(derivation.witness).images;
                if List(witness, w -> derivation.conjugator * w * derivation.conjugator^-1) <> target.variants.(name).images then
                    return restore(VVMF_Failure("InvalidRepresentation", "A derivation's conjugator does not map its witness to the variant."));
                fi;
            fi;
        od;
        if entry.activeVariant <> fail then
            if not IsBound(entry.variants.(entry.activeVariant)) then
                return restore(VVMF_Failure("InvalidRepresentation", "The active variant is not among the variants."));
            fi;
            # Admission rules: adopt when none is active or when the incoming active variant outranks this
            # state's active variant; otherwise keep this state's active basis (the variant is kept).
            if target.activeVariant = fail or id in replaceActive or
                rank(target, entry.activeVariant, d) > rank(target, target.activeVariant, d) then
                target.activeVariant := entry.activeVariant;
                if id in replaceActive then target.acceptedPartial := fail; fi;
            fi;
        fi;
        if entry.acceptedPartial <> fail and target.acceptedPartial = fail and
            IsBound(target.variants.(entry.acceptedPartial)) and rank(target, target.activeVariant, d) < 1 and
            target.activeVariant <> entry.acceptedPartial then
            target.acceptedPartial := entry.acceptedPartial;
        fi;
        if target.acceptedPartial <> fail and (target.acceptedPartial = target.activeVariant or
            (target.activeVariant <> fail and rank(target, target.activeVariant, d) >= 1)) then
            target.acceptedPartial := fail;
        fi;
    od;
    return true;
end;

# Summary: Merge a verified sibling checkpoint's representations into this state.
# Parameters/defaults: state is the destination; source is the coordinator-admitted envelope; optional
# third argument, irrep IDs whose incoming active variant replaces this state's (VVMF_ImportRepresentations).
# Returns: true or an import/conflict failure.
# Effects: As VVMF_ImportRepresentations; the coordinator saves and restores the merged state.
# Failures: Different state identity, missing data, verification failure or conflict.
# Example: two partial Dixon/REPSN results merge into one coherent generation (D3).
# See also: VVMF_ImportRepresentations; Kernel/GAPJobs.wl.
VVMF_TransferRepresentations := function(state, source, arg...)
    if not IsRecord(source) or not IsBound(source.stateID) or source.stateID <> state.stateID or
        not IsBound(source.generatorIdentity) or source.generatorIdentity <> state.generatorIdentity or
        not IsBound(source.representationData) or not IsRecord(source.representationData) then
        return VVMF_Failure("StateConflict", "Only representations of the same verified state can be transferred.");
    fi;
    if Length(arg) > 0 then return VVMF_ImportRepresentations(state, source.representationData, arg[1]); fi;
    return VVMF_ImportRepresentations(state, source.representationData);
end;
