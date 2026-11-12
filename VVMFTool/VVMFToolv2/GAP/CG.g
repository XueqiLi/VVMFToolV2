# Title: Clebsch-Gordan mirror of the accepted group state
# Summary: Carry validated CG bundle records inertly in the GAP state when a GAP route needs them; Wolfram sends
# them on demand (syncCGMirror, step4Status.md D-S4-8). GAP never computes with these records: Wolfram validated
# them before the request and is the authority for the group's CG store.
# Dependencies: Diagnostics, Scalars.
# See also: Kernel/CGStore.wl syncCGMirror (records are given to GAP on demand, D-S4-8); VVMFArch/step4Plan.md.

# Summary: Check the structure of one CG bundle record (no arithmetic).
# Parameters/defaults: data, a record with key (64 hexadecimal characters), targetID, method, normalization,
# arithmetic and channels (a list of records with copy, symmetry, embedding and dual matrices of tagged scalar
# records).
# Returns: true, or InvalidCGRecord failure.
# Effects: Pure.
# Failures: Missing fields, a malformed key, or matrices whose entries are not records.
# Example: a record produced by Kernel/CGStore.wl encodeCGBundle passes.
# See also: VVMF_IncorporateCG.
VVMF_CGRecordCheck := function(data)
    local invalid, matrixQ;
    invalid := VVMF_Failure("InvalidCGRecord", "Malformed CG bundle record.");
    matrixQ := m -> IsList(m) and Length(m) > 0 and ForAll(m, r -> IsList(r) and Length(r) = Length(m[1]) and ForAll(r, IsRecord));
    if not IsRecord(data) or not IsBound(data.key) or not IsString(data.key) or Length(data.key) <> 64 or
        not ForAll(data.key, c -> c in "0123456789abcdef") or not IsBound(data.targetID) or not IsString(data.targetID) or
        not IsBound(data.method) or not IsString(data.method) or not IsBound(data.normalization) or
        not IsBound(data.arithmetic) or not IsBound(data.channels) or not IsList(data.channels) then
        return invalid;
    fi;
    if not ForAll(data.channels, c -> IsRecord(c) and IsBound(c.copy) and IsBound(c.symmetry) and
            IsBound(c.embedding) and matrixQ(c.embedding) and IsBound(c.dual) and matrixQ(c.dual)) then
        return invalid;
    fi;
    return true;
end;

# Summary: Replace the CG mirror by the accepted key set plus newly validated bundles.
# Parameters/defaults: state; request with cgUpdate := rec(epoch (decimal string), retain (list of keys the
# accepted group stores), add (list of bundle records)).
# Returns: true, or InvalidRequest/InvalidCGRecord failure.
# Effects: state.cgMirror := rec(epoch, entries) with entries restricted to retain (entries erased by
# CleanCGCache, or carried by an older restored workspace, are dropped) and the added records stored immutably.
# Failures: A malformed update, epoch or record.
# Example: after VVMF_IncorporateCG the exported diagnostics list the retained and added keys.
# Remarks: The mirror is never exported as group data; only its key list and epoch appear in the diagnostics
# of a CG request, which the restore verification compares with the saved result.
# See also: VVMF_CGRecordCheck; VVMF_CGMirrorSummary.
VVMF_IncorporateCG := function(state, request)
    local update, epoch, entries, key, record, checked;
    if not IsBound(request.cgUpdate) or not IsRecord(request.cgUpdate) then
        return VVMF_Failure("InvalidRequest", "A CG update is required.");
    fi;
    update := request.cgUpdate;
    if not IsBound(update.epoch) or not IsBound(update.retain) or not IsBound(update.add) or
        not IsList(update.retain) or not ForAll(update.retain, IsString) or not IsList(update.add) then
        return VVMF_Failure("InvalidRequest", "Malformed CG update.");
    fi;
    epoch := VVMF_DecodeInteger(update.epoch);
    if VVMF_IsFailure(epoch) or epoch < 0 then
        return VVMF_Failure("InvalidRequest", "The CG eviction epoch must be a nonnegative decimal integer.");
    fi;
    entries := rec();
    if IsBound(state.cgMirror) then
        for key in RecNames(state.cgMirror.entries) do
            if key in update.retain then entries.(key) := state.cgMirror.entries.(key); fi;
        od;
    fi;
    for record in update.add do
        checked := VVMF_CGRecordCheck(record);
        if VVMF_IsFailure(checked) then return checked; fi;
        entries.(record.key) := Immutable(record);
    od;
    state.cgMirror := rec(epoch := epoch, entries := entries);
    return true;
end;

# Summary: The key list and epoch of the CG mirror, for the diagnostics of a CG request.
# Parameters/defaults: state.
# Returns: rec(epoch := decimal string, keys := sorted list of keys).
# Effects: Pure.
# Failures: None.
# Example: an empty mirror gives rec(epoch := "0", keys := []).
# See also: VVMF_IncorporateCG; GAP/ResultExport.g.
VVMF_CGMirrorSummary := function(state)
    if not IsBound(state.cgMirror) then return rec(epoch := "0", keys := []); fi;
    return rec(epoch := String(state.cgMirror.epoch), keys := SortedList(RecNames(state.cgMirror.entries)));
end;

# Summary: CG intertwiner spaces of P (x) Q against a target by an average over a stabilizer chain.
# Parameters/defaults: state (complete group); request.cgChain := rec(p, q, target (encoded cyclotomic generator
# matrices), multiplicity (decimal string), variant "Operator" or "Trial").
# Returns: rec(kets := list of N by dt matrices, bras := list of dt by N matrices) encoded with
# VVMF_EncodeRepScalar, or failure.
# Effects: Loads RepnDecomp; stores the result in state.cgNativeResult for the export (a query: the
# mathematical state is unchanged).
# Failures: InvalidRequest; InvalidRepresentation (matrices that fail the relators); DependencyUnavailable;
# UnprovedIdentity (the averaged operator's rank differs from the multiplicity).
# Example: A4's triplet square against the triplet gives two kets and two bras.
# Remarks: In column vectorization the action X -> R(g) X D(g^-1) has the matrix (D(g)^-1)^T (x) R(g), a group
# homomorphism, so RepnDecomp's GroupSumBSGS sums it over a stabilizer chain (products of transversal sums
# along the chain); its image is Hom_G(D, R). Bras use Y -> D(g) Y R(g)^-1, i.e. (R(g)^-1)^T (x) D(g).
# "Operator" takes independent columns of the averaged operator; "Trial" applies it to deterministic
# integer trial vectors until the rank is reached.
# See also: Kernel/CGNative.wl chainCG.
VVMF_CGChain := function(state, request)
    local spec, p, q, t, k, n, dt, m, relators, homK, homB, sumK, sumB, select, kets, bras, ok;
    if not IsBound(request.cgChain) or not IsRecord(request.cgChain) then
        return VVMF_Failure("InvalidRequest", "A CG chain request is required.");
    fi;
    spec := request.cgChain;
    if not IsBound(spec.p) or not IsBound(spec.q) or not IsBound(spec.target) or not IsBound(spec.multiplicity) or
        not IsBound(spec.variant) or not spec.variant in ["Operator", "Trial"] or Length(state.generators) = 0 or
        Length(spec.p) <> Length(state.generators) or Length(spec.q) <> Length(state.generators) or
        Length(spec.target) <> Length(state.generators) then
        return VVMF_Failure("InvalidRequest", "Malformed CG chain request.");
    fi;
    p := List(spec.p, VVMF_DecodeRequestMatrix); q := List(spec.q, VVMF_DecodeRequestMatrix);
    t := List(spec.target, VVMF_DecodeRequestMatrix);
    if ForAny(Concatenation(p, q, t), VVMF_IsFailure) then return First(Concatenation(p, q, t), VVMF_IsFailure); fi;
    m := VVMF_DecodeInteger(spec.multiplicity);
    if VVMF_IsFailure(m) then return m; fi;
    relators := VVMF_RepRelators(state);
    if relators = fail or ForAny([p, q, t], images -> ForAny(relators, letters ->
            VVMF_LetterMatrix(images, letters, Length(images[1])) <> IdentityMat(Length(images[1])))) then
        return VVMF_Failure("InvalidRepresentation", "The matrices do not satisfy the group's relators.");
    fi;
    if LoadPackage("RepnDecomp") <> true then
        return VVMF_Failure("DependencyUnavailable", "The chain average needs the RepnDecomp package.");
    fi;
    k := List([1..Length(p)], i -> KroneckerProduct(p[i], q[i]));
    n := Length(k[1]); dt := Length(t[1]);
    homK := GroupHomomorphismByImagesNC(state.group, Group(List([1..Length(k)], i -> KroneckerProduct(TransposedMat(Inverse(t[i])), k[i]))),
        state.generators, List([1..Length(k)], i -> KroneckerProduct(TransposedMat(Inverse(t[i])), k[i])));
    homB := GroupHomomorphismByImagesNC(state.group, Group(List([1..Length(k)], i -> KroneckerProduct(TransposedMat(Inverse(k[i])), t[i]))),
        state.generators, List([1..Length(k)], i -> KroneckerProduct(TransposedMat(Inverse(k[i])), t[i])));
    sumK := ValueGlobal("GroupSumBSGS")(state.group, g -> ImagesRepresentative(homK, g));
    sumB := ValueGlobal("GroupSumBSGS")(state.group, g -> ImagesRepresentative(homB, g));
    # Independent images: columns of the operator, or the operator applied to deterministic trial vectors.
    select := function(sum, rows, columns)
        local vectors, candidate, j, seed, chosen;
        chosen := [];
        j := 0;
        while Length(chosen) < m and j < 4 * m + rows * columns do
            j := j + 1;
            if spec.variant = "Operator" then
                if j > rows * columns then break; fi;
                candidate := TransposedMat(sum)[j];
            else
                seed := List([1..rows * columns], i -> ((i * 7919 + j * 104729) mod 7) - 3);
                candidate := sum * seed;
            fi;
            if candidate <> 0 * candidate and RankMat(Concatenation(chosen, [candidate])) > Length(chosen) then
                Add(chosen, candidate);
            fi;
        od;
        if Length(chosen) <> m then return fail; fi;
        # Column vectorization: entry (a, c) of an a-by-c matrix is v[(c - 1) * a_rows + a].
        return List(chosen, v -> List([1..rows], a -> List([1..columns], c -> v[(c - 1) * rows + a])));
    end;
    kets := select(sumK, n, dt);
    bras := select(sumB, dt, n);
    if kets = fail or bras = fail then
        return VVMF_Failure("UnprovedIdentity", "The chain average does not have the character multiplicity.");
    fi;
    ok := ForAll(kets, x -> ForAll([1..Length(k)], i -> k[i] * x = x * t[i])) and
        ForAll(bras, y -> ForAll([1..Length(k)], i -> y * k[i] = t[i] * y));
    if not ok then return VVMF_Failure("UnprovedIdentity", "A chain intertwiner does not verify."); fi;
    state.cgNativeResult := rec(kets := List(kets, x -> List(x, row -> List(row, ValueGlobal("VVMF_EncodeRepScalar")))),
        bras := List(bras, y -> List(y, row -> List(row, ValueGlobal("VVMF_EncodeRepScalar")))));
    return true;
end;
