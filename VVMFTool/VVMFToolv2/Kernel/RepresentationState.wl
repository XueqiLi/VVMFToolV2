(*
    :Title: Representation state: presentation order, element matrices and derived caches
    :Context: VVMFTool`Private`
    :Summary: Irrep presentation order, requested element matrices and the derived representation cache with
        its eviction epoch.
    :Responsibilities:
        - ReorderGroupIrreps and SortGroupIrreps change only IrrepOrder (D9).
        - RepresentationElementMatrices evaluates requested element words on an irrep's active variant and
          caches them by variant identity.
        - Derived cache entries (element matrices, validation results, decompositions, invariant forms)
          and CleanRepresentationCache, which advances the eviction epoch (D8).
    :Dependencies: Diagnostics.wl; GroupObject.wl (groupData, commitGroup, representation cache);
        GroupConstruction.wl (resolveOperationOptions); GroupEnrichment.wl (GroupElementWords);
        RepresentationValidation.wl (exact domains); Representation.wl (repIdentity, canonical words).
    :See Also: VVMFArch/step2Plan.md (reordering, element matrices, cache cleanup); design.md.
*)

(*
    Summary: Read one derived cache entry of a live group.
    Parameters: group — live Group; kind — cache kind; key — any expression (hashed).
    Options/defaults: None.
    Returns: The cached value, or Missing["NotCached"].
    Effects: Pure read.
    Failures: None; unknown groups give Missing["NotCached"].
    Example: representationCacheLookup[g, "ElementMatrices", key] after a store returns the stored matrix.
    See also: representationCacheStore; CleanRepresentationCache.
*)
representationCacheLookup[group_Group, kind_String, key_] := With[{data = groupData[group]},
    If[FailureQ[data], Missing["NotCached"],
        Lookup[data["RepresentationCache"]["Entries"][kind], Hash[key, "SHA256"], Missing["NotCached"]]]];
representationCacheLookup[___] := Missing["NotCached"];

(*
    Summary: Store derived cache entries of a live group at its current revision.
    Parameters: group — live Group; kind — cache kind; entries — association key -> value (keys hashed).
    Options/defaults: None.
    Returns: The group, or a Failure (the cache is recomputable, so callers may ignore it).
    Effects: One commitGroup patch of the non-receipt RepresentationCache; the revision advances.
    Failures: StateConflict when the group changed concurrently; unknown groups.
    Example: representationCacheStore[g, "Decompositions", <|key -> result|>].
    See also: representationCacheLookup.
*)
representationCacheStore[group_Group, kind_String, entries_Association] := Module[{data, cache},
    data = groupData[group]; If[FailureQ[data], Return[data]];
    cache = data["RepresentationCache"];
    cache["Entries", kind] = Join[cache["Entries"][kind], KeyMap[Hash[#, "SHA256"] &, entries]];
    commitGroup[group, data["Revision"], <|"RepresentationCache" -> cache|>]
];
representationCacheStore[___] := makeFailure["InvalidGroup", "Expected a live group, cache kind and entries."];

Options[ReorderGroupIrreps] = {};

(*
    Summary: Set the presentation order of a group's irreducible representations.
    Status: Alpha.
    Parameters: g — live Group; ids — a permutation of g's irrep IDs.
    Options/defaults: None.
    Returns: The same Group.
    Effects: Changes only IrrepOrder (no generation, receipt or identity change); character rows,
        representation matrices, bases and caches keyed by irrep ID are unchanged.
    Failures: InvalidIrrepOrder for anything other than a permutation of the irrep IDs; unknown groups.
    Example: ReorderGroupIrreps[g, Reverse[g["IrrepOrder"]]]["IrrepOrder"] is the reversed order.
    Remarks: The order is presentation metadata, saved and restored with snapshots (D9).
    See also: SortGroupIrreps; commitGroup.
*)
ReorderGroupIrreps[group_Group, order_List, options : OptionsPattern[]] := Module[{effective, data, ids},
    effective = resolveOperationOptions[ReorderGroupIrreps, "ReorderGroupIrreps", {options}];
    If[FailureQ[effective], Return[effective]];
    data = groupData[group]; If[FailureQ[data], Return[data]];
    (* an integer permutation perm gives the order old[[perm]] (uxUpdatePlan.md 1.3) *)
    ids = resolveIrrepArguments[group, order]; If[FailureQ[ids], Return[ids]];
    If[!irrepOrderQ[ids, data["CharacterData"]],
        Return[makeFailure["InvalidIrrepOrder", "Expected a permutation of the group's irrep IDs.", <|"IrrepIDs" -> ids|>]]];
    commitGroup[group, data["Revision"], <|"IrrepOrder" -> ids|>]
];
ReorderGroupIrreps[___] := makeFailure["InvalidInput", "ReorderGroupIrreps expects a live group and a list of irrep IDs."];

Options[SortGroupIrreps] = {};

(*
    Summary: Sort a group's irrep presentation order by degree, stably.
    Status: Alpha.
    Parameters: g — live Group.
    Options/defaults: None.
    Returns: The same Group.
    Effects: As ReorderGroupIrreps: only IrrepOrder changes.
    Failures: Unknown groups.
    Example: after SortGroupIrreps[g], RepDim of the irreps in g["IrrepOrder"] is nondecreasing.
    Remarks: Irreps of equal degree keep their current relative order.
    See also: ReorderGroupIrreps.
*)
SortGroupIrreps[group_Group, options : OptionsPattern[]] := Module[{effective, data, degrees, order},
    effective = resolveOperationOptions[SortGroupIrreps, "SortGroupIrreps", {options}];
    If[FailureQ[effective], Return[effective]];
    data = groupData[group]; If[FailureQ[data], Return[data]];
    degrees = AssociationThread[data["CharacterData"]["IrrepIDs"], data["CharacterData"]["Degrees"]];
    order = First /@ SortBy[Transpose[{data["IrrepOrder"], Range[Length[data["IrrepOrder"]]]}], {degrees[First[#]] &, Last}];
    commitGroup[group, data["Revision"], <|"IrrepOrder" -> order|>]
];
SortGroupIrreps[___] := makeFailure["InvalidInput", "SortGroupIrreps expects one live group."];

Options[RepresentationElementMatrices] = Append[Options[RestoreGAPState], FieldMethod -> Automatic];

(*
    Summary: Matrices of group elements in an irrep's active representation.
    Status: Alpha.
    Parameters: g — live Group; id — irrep ID; words — All (every element, from GroupElementWords) or a
        list of GroupWord values on the recorded generators.
    Options/defaults: Common GAP options, used only to obtain the element words for All.
    Returns: List of matrices in the order of words (duplicates kept), in the active variant's basis.
    Effects: For All, may run the GroupElementWords enrichment; caches each evaluated word by the active
        variant's realization identity (ElementMatrices).
    Failures: InvalidIrrepID; MissingRepresentation when the irrep has no active variant (compute it
        first); InvalidWord; element-word failures.
    Example: RepresentationElementMatrices[g, id, {GroupWord[{}]}] is {IdentityMatrix[RepDim[...]]}.
    Remarks: Exact words are evaluated in a number field of the stored matrices; a scaled variant is
        evaluated on its native matrices N and transformed once, L N(w) L^-1; a Numerical variant's words are
        numerical products at its precision. Cache entries are keyed by
        variant identity, so a new active basis never reuses another basis's matrices.
    See also: GroupElementWords; GroupRepresentation; CleanRepresentationCache.
*)
RepresentationElementMatrices[group_Group, id_String, words : Except[_Rule | _RuleDelayed | {__String}] : All, options : OptionsPattern[]] := cgFieldCatch[representationElementMatricesFieldWork[group, id, words, options]];
representationElementMatricesFieldWork[group_Group, id_String, words : Except[_Rule | _RuleDelayed | {__String}] : All, options : OptionsPattern[]] := Module[
    {effective, data, entry, variant, list, names, d, native, scales, field, matrices, cached, missing, computed, conductor},
    effective = resolveOperationOptions[RepresentationElementMatrices, "RepresentationElementMatrices", {options}];
    If[FailureQ[effective], Return[effective]];
    data = groupData[group]; If[FailureQ[data], Return[data]];
    If[!MemberQ[data["CharacterData"]["IrrepIDs"], id],
        Return[makeFailure["InvalidIrrepID", "The irrep ID is not in the group's character table.", <|"IrrepID" -> id|>]]];
    entry = Lookup[data["Representations"], id, None];
    If[!AssociationQ[entry] || !StringQ[entry["ActiveVariant"]],
        Return[makeFailure["MissingRepresentation", "The irrep has no active representation; compute it with ComputeGroupRepresentations first.",
            <|"IrrepID" -> id|>]]];
    variant = entry["Variants"][entry["ActiveVariant"]];
    list = If[words === All, GroupElementWords[group, Sequence @@ Normal[KeyTake[effective, Keys[$CommonJobDefaults]]]], words];
    If[FailureQ[list], Return[list]];
    If[!ListQ[list] || !AllTrue[list, MatchQ[#, _GroupWord] &],
        Return[makeFailure["InvalidWord", "Expected All or a list of GroupWord values."]]];
    names = Lookup[data["Generators"], "Name", {}]; d = entry["Dimension"];
    If[AnyTrue[list, FailureQ[normalizeWord[#, names]] &],
        Return[makeFailure["InvalidWord", "A word uses names other than the recorded generators."]]];
    cached = representationCacheLookup[group, "ElementMatrices", {variant["Identity"], First[normalizeWord[#, names]]}] & /@ list;
    missing = DeleteDuplicates[Pick[list, MissingQ /@ cached]];
    If[missing =!= {} && variant["Tier"] === "Numerical",
        (* Numerical variants: products at the variant's precision. *)
        computed = Association[Map[Function[word, word -> With[{m = wordMatrix[variant["Rep"], word, names]},
            If[Precision[m] === Infinity, N[m, Precision[repMatrices[variant["Rep"]]]], m]]], missing]];
        representationCacheStore[group, "ElementMatrices",
            KeyMap[{variant["Identity"], First[normalizeWord[#, names]]} &, computed]];
        cached = MapThread[If[MissingQ[#1], computed[#2], #1] &, {cached, list}];
        missing = {}];
    If[missing =!= {},
        native = If[MissingQ[variant["NativeMatrices"]], repMatrices[variant["Rep"]], variant["NativeMatrices"]];
        scales = If[MissingQ[variant["Scales"]], ConstantArray[1, d], variant["Scales"]];
        field = settingsField[native, <|"FieldMethod" -> effective[FieldMethod]|>];
        matrices = fieldEmbed[field, native];
        (* exact products in the number field, returned in readable form: radicals or e^{2 Pi i k/n}, never Root objects
           (uxUpdatePlan.md 3, U8); the cache holds the readable form, no identity depends on it *)
        conductor = If[Lookup[field, "Source", None] === "CyclotomicHint", Denominator[certifiedRootOfUnityPhase[field["Generator"]]], None];
        computed = Association[Map[Function[word, word -> If[IntegerQ[conductor],
            (* products in Q(zeta_n): their coordinates are the root-of-unity coefficients (no RootReduce, no recognition) *)
            With[{m = fieldWordMatrix[matrices, word, names, d, field]},
                Table[If[scales[[i]] === scales[[j]], 1, Sqrt[scales[[i]] / scales[[j]]]] cyclotomicFieldReadable[m[[i, j]], conductor], {i, d}, {j, d}]],
            With[{m = fieldBack[fieldWordMatrix[matrices, word, names, d, field]]},
                readableMatrix[Table[RootReduce[m[[i, j]] Sqrt[scales[[i]] / scales[[j]]]], {i, d}, {j, d}]]]]], missing]];
        representationCacheStore[group, "ElementMatrices",
            KeyMap[{variant["Identity"], First[normalizeWord[#, names]]} &, computed]];
        cached = MapThread[If[MissingQ[#1], computed[#2], #1] &, {cached, list}]];
    cached
];
RepresentationElementMatrices[group_Group, k_Integer, rest___] := withIrreps[group, {k}, RepresentationElementMatrices[group, #, rest] &];
(* plain word strings ("S", "T^2.S") where GroupWord values are expected (uxUpdatePlan.md 4) *)
RepresentationElementMatrices[group_Group, id_String, words : {__String}, rest___] := RepresentationElementMatrices[group, id, GroupWord /@ words, rest];
RepresentationElementMatrices[___] := makeFailure["InvalidInput", "RepresentationElementMatrices expects a live group, an irrep ID, optional words and options."];

Options[CleanRepresentationCache] = {CacheKinds -> All};

(*
    Summary: Remove derived representation caches and advance the eviction epoch.
    Status: Alpha.
    Parameters: g — live Group.
    Options/defaults: CacheKinds -> All, one of "ElementMatrices", "Unitarity", "Decompositions",
        "DerivedIntermediates", or a list of them.
    Returns: <|"Removed" -> kind -> number of entries, "Protected" -> the categories never removed, "Epoch"|>.
    Effects: Removes the selected derived entries and advances the epoch atomically (one commit, no GAP
        generation); later GAP requests carry the epoch, so a restored older workspace drops its derived
        native data (the stored decomposition result) before any work.
    Failures: InvalidOption for unknown kinds; unknown groups.
    Example: CleanRepresentationCache[g]["Removed"]["ElementMatrices"] counts the removed element matrices.
    Remarks: Active variants, accepted partials, derivation witnesses and characters are mathematical data
        and are never removed; GAP workspace bytes are managed by CleanGAPCache.
    See also: RepresentationElementMatrices; CleanGAPCache; emptyRepresentationCache.
*)
CleanRepresentationCache[group_Group, options : OptionsPattern[]] := Module[{effective, data, kinds, cache, removed},
    effective = resolveOperationOptions[CleanRepresentationCache, "CleanRepresentationCache", {options}];
    If[FailureQ[effective], Return[effective]];
    data = groupData[group]; If[FailureQ[data], Return[data]];
    kinds = Which[effective[CacheKinds] === All, $RepresentationCacheKinds, StringQ[effective[CacheKinds]], {effective[CacheKinds]},
        True, effective[CacheKinds]];
    cache = data["RepresentationCache"];
    removed = AssociationMap[Length[cache["Entries"][#]] &, kinds];
    Scan[(cache["Entries", #] = <||>) &, kinds];
    cache["Epoch"] = cache["Epoch"] + 1;
    With[{committed = commitGroup[group, data["Revision"], <|"RepresentationCache" -> cache|>]},
        If[FailureQ[committed], Return[committed]]];
    <|"Removed" -> removed, "Protected" -> {"ActiveVariants", "AcceptedPartials", "DerivationWitnesses", "Characters"},
        "Epoch" -> cache["Epoch"]|>
];
CleanRepresentationCache[___] := makeFailure["InvalidInput", "CleanRepresentationCache expects one live group and options."];

(* -------------------------------------------------------------------------
   Explicit mutations (natively verified)
   ------------------------------------------------------------------------- *)

(*
    Summary: Encode exact matrices as cyclotomic request scalars of a group.
    Parameters: matrices — exact matrices (any nesting of matrix lists); accepted — group snapshot.
    Options/defaults: Candidate conductors are multiples of lcm(4, group exponent).
    Returns: The encoded structure, or $Failed when an entry is not cyclotomic in those fields.
    Effects: Pure.
    Failures: $Failed.
    Example: cyclotomicMatrices[{{{1, 0}, {0, -1}}}, accepted] encodes integers.
    See also: cyclotomicEncoding; SetGroupRepresentation.
*)
cyclotomicMatrices[matrices_, accepted_Association] := Module[{orders, encoded},
    orders = LCM[LCM @@ accepted["CharacterData"]["ClassOrders"], 4] {1, 2, 3, 4, 5, 6, 8, 10, 12, 15, 20, 24, 30, 40, 60, 120};
    encoded = Map[cyclotomicEncoding[#, orders] &, matrices, {ArrayDepth[matrices]}];
    If[FreeQ[encoded, $Failed], encoded, $Failed]
];

(*
    Summary: Verify a representation of one irrep in Wolfram and encode it as an inert variant record (R1).
    Parameters: group — live Group; id — irrep ID; rep — Rep; source — <|"Method", "Model"|>; derivation —
        <|"Witness", "Conjugator"|> or Missing["None"]; basis — "Unitary" or "General" (required);
        options — validated GAP job settings (to certify the presentation once) with the call's Verification.
    Options/defaults: Exact input gives a Wolfram-tier record; numerical input a Numerical record at the
        input's precision (machine precision, or at least 16 digits). Verification "Numerical" checks on N[] and
        None runs no relator or character check (the recorded unitarity and T-diagonality are computed from the matrices,
        repBasisFacts); both record their status ("verificationStatus").
    Returns: The inert record for GAP (method Inert), or Failure.
    Effects: May certify the group's presentation in GAP (validateRepBinding).
    Failures: As validateRepBinding (WrongCharacter, InvalidRepresentation, NonUnitaryRepresentation,
        PresentationUnavailable); UnsupportedRepresentationData for numerical input below 16 digits.
    Example: inertMutationRecord[g, id, Rep[{{{2^(1/3), ...}}}], <|"Method" -> "Supplied", "Model" -> "User"|>,
        Missing["None"], "General", options]["tier"] is "Wolfram".
    Remarks: The relator and character checks are exact for exact input and within the automatic
        tolerance at the input's precision for numerical input.
    See also: encodeInertVariant; validateRepBinding; verifyInertVariants.
*)
inertMutationRecord[group_Group, id_String, rep_Rep, source_Association, derivation_, basis_String, options_Association] := Module[
    {shape, precision, declared, settings, result, data, level = Lookup[options, Verification, Automatic], record, properties},
    shape = validateRepShape[rep]; If[FailureQ[shape], Return[shape]];
    precision = shape["Precision"];
    declared = Which[precision === Infinity || precision === MachinePrecision, precision, True, Floor[precision]];
    If[IntegerQ[declared] && declared < 16,
        Return[makeFailure["UnsupportedRepresentationData", "Numerical representations need machine precision or at least 16 digits."]]];
    data = groupData[group]; If[FailureQ[data], Return[data]];
    (* Verification (methodOptionsPlan.md 2C.4): "Numerical" checks the relators and the character on N[] at
       WorkingPrecision; None runs no result check and records only the properties the input checks proved (unitarity
       of exact input under Basis -> "Unitary"); the record carries the status, so GAP keeps it inert (C7) *)
    If[level === None,
        (* unchecked as a representation (no relators, no character), but the recorded basis properties are the exact
           facts of the matrices (numerical ones within the automatic tolerance), as GAP records for its weak variants: a
           later full-level import re-checks them (verifyInertVariants) and must find them neither under- nor overstated *)
        settings = arithmeticSettings[If[precision === Infinity, "Exact", "Numerical"], If[precision === Infinity, 50, precision], Automatic, precision];
        If[FailureQ[settings], Return[settings]];
        properties = repBasisFacts[data, rep, settings];
        (* Basis -> "Unitary" is an input requirement also when nothing else is checked (review 2C-iii-a F7) *)
        If[basis === "Unitary" && !TrueQ[properties["Unitary"]],
            Return[makeFailure["NonUnitaryRepresentation", "Basis -> \"Unitary\" requires unitary matrices; use Basis -> \"General\"."]]],
        settings = arithmeticSettings[If[precision === Infinity && level =!= "Numerical", "Exact", "Numerical"],
            If[precision === Infinity, Lookup[options, WorkingPrecision, 50], precision], Automatic, precision];
        If[FailureQ[settings], Return[settings]];
        settings = Join[settings, <|"FieldMethod" -> Lookup[options, FieldMethod, Automatic]|>];
        result = validateRepBinding[group, rep, <|"Settings" -> settings, "Options" -> options, "IrrepID" -> id, "Basis" -> basis|>];
        If[FailureQ[result], Return[result]];
        properties = result["BasisProperties"]];
    record = encodeInertVariant[rep, source, properties, data["ModularAssignment"], declared, derivation];
    If[FailureQ[record], Return[record]];
    Switch[level, None, Append[record, "verificationStatus" -> "Unverified"],
        "Numerical", Append[record, "verificationStatus" -> "Numerical"], _, record]
];

Options[SetGroupRepresentation] = Join[Options[RestoreGAPState], {Basis -> "Unitary", FieldMethod -> Automatic, Verification -> Automatic, WorkingPrecision -> 50}];

(*
    Summary: Store a supplied representation of one irrep and make it the active variant.
    Status: Alpha.
    Parameters: g — live Group; id — irrep ID; r — Rep with one matrix per recorded generator.
    Options/defaults: Basis -> "Unitary" (r must be unitary) or "General"; Verification -> Automatic (GAP's VerifyRep for
        cyclotomic r, Wolfram's checks otherwise), "Exact" (exact r required), "Numerical" (Wolfram's checks on N[] at
        WorkingPrecision, default 50) or None (input checks only); a "Numerical" or None variant is stored as an inert
        record with that status (methodOptionsPlan.md C7), never as a native GAP variant; common GAP job options.
    Returns: The same Group.
    Effects: One GAP generation. Cyclotomic r is verified in GAP (relators of a complete presentation, class
        traces equal to the irrep's character) and stored as a native variant (method Supplied). Other exact r
        (tier Wolfram) and numerical r (tier Numerical, at its precision) are verified in Wolfram the same way
        (numerically within the automatic tolerance) and carried by GAP as inert records (R1). The new variant
        becomes active; the previous variants stay stored. Passing a numerical r is the explicit choice that
        makes a numerical variant active.
    Failures: InvalidIrrepID; InvalidRep/GeneratorBindingMismatch; NonUnitaryRepresentation (Basis ->
        "Unitary" with nonunitary r); WrongCharacter or InvalidRepresentation (non-cyclotomic or numerical r
        that is not the irrep); RepresentationMethodFailed with the WrongCharacter or InvalidRepresentation
        outcome (cyclotomic r); UnsupportedRepresentationData (numerical r below 16 digits); resource failures.
    Example: SetGroupRepresentation[g, id, ChangeRepBasis[GroupRepresentation[g, id], b], Basis -> "General"].
    Remarks: The controlled replacement for v1's RepSwap: a matching dimension is not enough.
    See also: ChangeGroupRepBasis; TransformGroupRepresentations; GroupRepresentation.
*)
SetGroupRepresentation[group_Group, id_String, rep_Rep, options : OptionsPattern[]] := cgFieldCatch[setGroupRepresentationFieldWork[group, id, rep, options]];
setGroupRepresentationFieldWork[group_Group, id_String, rep_Rep, options : OptionsPattern[]] := Module[
    {effective, data, shape, encoded, inert},
    effective = resolveOperationOptions[SetGroupRepresentation, "SetGroupRepresentation", {options}];
    If[FailureQ[effective], Return[effective]];
    data = groupData[group]; If[FailureQ[data], Return[data]];
    If[!MemberQ[data["CharacterData"]["IrrepIDs"], id],
        Return[makeFailure["InvalidIrrepID", "The irrep ID is not in the group's character table.", <|"IrrepID" -> id|>]]];
    shape = validateRepShape[rep]; If[FailureQ[shape], Return[shape]];
    If[shape["GeneratorCount"] =!= Length[data["Generators"]] || shape["Dimension"] =!=
            data["CharacterData"]["Degrees"][[First[FirstPosition[data["CharacterData"]["IrrepIDs"], id]]]],
        Return[makeFailure["GeneratorBindingMismatch", "The representation needs one matrix of the irrep's degree per recorded generator."]]];
    If[shape["Arithmetic"] === "Exact" && effective[Basis] === "Unitary" && !TrueQ[UnitaryRepresentationQ[rep]],
        Return[makeFailure["NonUnitaryRepresentation", "Basis -> \"Unitary\" requires unitary matrices; use Basis -> \"General\"."]]];
    If[effective[Verification] === "Exact" && shape["Arithmetic"] =!= "Exact",
        Return[makeFailure["InapplicableOption", "Verification -> \"Exact\" needs exact matrices.", <|"Options" -> {Verification}|>]]];
    (* a weak variant (Verification "Numerical" or None) is always an inert record: GAP never holds it natively (C7) *)
    encoded = If[shape["Arithmetic"] === "Exact" && !MemberQ[{"Numerical", None}, effective[Verification]], cyclotomicMatrices[repMatrices[rep], data], $Failed];
    If[encoded === $Failed,
        (* Not cyclotomic, or weak: verified here at the call's level and carried by GAP as an inert record. *)
        inert = inertMutationRecord[group, id, rep, <|"Method" -> "Supplied", "Model" -> "User"|>, Missing["None"],
            effective[Basis], effective];
        If[FailureQ[inert], Return[inert]];
        Return[runRepresentationMutation[group, <|"Method" -> "Inert", "IrrepIDs" -> {id}, "Basis" -> effective[Basis],
            "Payload" -> <|"inert" -> <|id -> inert|>|>, "ReplaceActive" -> {id}|>, effective]]];
    runRepresentationMutation[group, <|"Method" -> "Supplied", "IrrepIDs" -> {id}, "Basis" -> effective[Basis],
        "Payload" -> <|"supplied" -> <|id -> encoded|>|>, "ReplaceActive" -> {id}|>, effective]
];
SetGroupRepresentation[group_Group, k_Integer, rest___] := withIrreps[group, {k}, SetGroupRepresentation[group, #, rest] &];
SetGroupRepresentation[___] := makeFailure["InvalidInput", "SetGroupRepresentation expects a live group, an irrep ID, a Rep and options."];

Options[ChangeGroupRepBasis] = Join[Options[RestoreGAPState], {Basis -> "Unitary", FieldMethod -> Automatic, Verification -> Automatic, WorkingPrecision -> 50}];

(*
    Summary: Change the basis of an irrep's active representation in the group.
    Status: Alpha.
    Parameters: g — live Group; id — irrep ID; b — invertible matrix of the irrep's degree.
    Options/defaults: Basis -> "Unitary" (the new matrices must be unitary) or "General"; Verification as
        SetGroupRepresentation (a weak result, or a weak active variant, is an inert record); common GAP job options.
    Returns: The same Group.
    Effects: One GAP generation: the new variant b . M . Inverse[b] of the active variant's matrices M is
        stored with its derivation (witness = the active variant, conjugator b) and made active. With a native
        unscaled active variant and cyclotomic b it is recomputed and verified in GAP; otherwise (a scaled,
        Wolfram-tier or numerical active variant, or b with other exact or numerical entries) it is verified
        in Wolfram and carried by GAP as an inert Wolfram-tier or, with numerical data, Numerical record.
    Failures: InvalidIrrepID; MissingRepresentation (no active variant); SingularBasis; NonUnitaryRepresentation;
        UnsupportedRepresentationData (numerical data below 16 digits); resource failures.
    Example: ChangeGroupRepBasis[g, id, b, Basis -> "General"] makes b.M.Inverse[b] active.
    See also: ChangeRepBasis; SetGroupRepresentation; TransformGroupRepresentations.
*)
ChangeGroupRepBasis[group_Group, id_String, b_, options : OptionsPattern[]] := cgFieldCatch[changeGroupRepBasisFieldWork[group, id, b, options]];
changeGroupRepBasisFieldWork[group_Group, id_String, b_, options : OptionsPattern[]] := Module[
    {effective, data, entry, variant, changed, encoded, inert},
    effective = resolveOperationOptions[ChangeGroupRepBasis, "ChangeGroupRepBasis", {options}];
    If[FailureQ[effective], Return[effective]];
    data = groupData[group]; If[FailureQ[data], Return[data]];
    If[!MemberQ[data["CharacterData"]["IrrepIDs"], id],
        Return[makeFailure["InvalidIrrepID", "The irrep ID is not in the group's character table.", <|"IrrepID" -> id|>]]];
    entry = Lookup[data["Representations"], id, None];
    If[!AssociationQ[entry] || !StringQ[entry["ActiveVariant"]],
        Return[makeFailure["MissingRepresentation", "The irrep has no active representation; compute it with ComputeGroupRepresentations first.",
            <|"IrrepID" -> id|>]]];
    variant = entry["Variants"][entry["ActiveVariant"]];
    changed = ChangeRepBasis[variant["Rep"], b]; If[FailureQ[changed], Return[changed]];
    If[Precision[changed] === Infinity && effective[Basis] === "Unitary" && !TrueQ[UnitaryRepresentationQ[changed]],
        Return[makeFailure["NonUnitaryRepresentation", "Basis -> \"Unitary\" requires the new matrices to be unitary; use Basis -> \"General\"."]]];
    If[effective[Verification] === "Exact" && Precision[changed] =!= Infinity,
        Return[makeFailure["InapplicableOption", "Verification -> \"Exact\" needs exact matrices.", <|"Options" -> {Verification}|>]]];
    (* a weak result (Verification "Numerical" or None), or a weak active variant, is an inert record (C7, C9) *)
    encoded = If[Precision[b] === Infinity && variant["Tier"] === "Native" && gapNativeVariantQ[variant] && !MemberQ[{"Numerical", None}, effective[Verification]],
        cyclotomicMatrices[b, data], $Failed];
    If[encoded === $Failed,
        (* Verified here and carried by GAP as an inert record derived from the active variant. *)
        inert = inertMutationRecord[group, id, changed, <|"Method" -> "BasisChange", "Model" -> entry["ActiveVariant"]|>,
            <|"Witness" -> entry["ActiveVariant"], "Conjugator" -> b|>, effective[Basis], effective];
        If[FailureQ[inert], Return[inert]];
        Return[runRepresentationMutation[group, <|"Method" -> "Inert", "IrrepIDs" -> {id}, "Basis" -> effective[Basis],
            "Payload" -> <|"inert" -> <|id -> inert|>|>, "ReplaceActive" -> {id}|>, effective]]];
    runRepresentationMutation[group, <|"Method" -> "BasisChange", "IrrepIDs" -> {id}, "Basis" -> effective[Basis],
        "Payload" -> <|"basisChange" -> <|id -> <|"witness" -> entry["ActiveVariant"], "matrix" -> encoded|>|>|>,
        "ReplaceActive" -> {id}|>, effective]
];
ChangeGroupRepBasis[group_Group, k_Integer, rest___] := withIrreps[group, {k}, ChangeGroupRepBasis[group, #, rest] &];
ChangeGroupRepBasis[___] := makeFailure["InvalidInput", "ChangeGroupRepBasis expects a live group, an irrep ID, a matrix and options."];

Options[TransformGroupRepresentations] = Join[Options[RestoreGAPState], {FieldMethod -> Automatic, Route -> Automatic, WorkingPrecision -> 50, Tolerance -> Automatic,
    WitnessVariant -> Automatic, Basis -> "Unitary", UnitarizationMethod -> Automatic,
    FormFactorizationMethod -> Automatic, DiagonalizationMethod -> Automatic, TPhaseOrder -> "Ascending", PhaseConvention -> None,
    Arithmetic -> "Exact", Verification -> Automatic}];

(*
    Summary: Transform computed irreps of a group to a unitary (and optionally T-diagonal) basis, atomically.
    Status: Alpha.
    Parameters: g — live Group; ids — All (default), one irrep ID or a duplicate-free list of IDs.
    Options/defaults: Basis -> "Unitary" or "UnitaryTDiagonal" (needs a modular assignment);
        UnitarizationMethod -> Automatic (GAP BSGSAverage, then GroupAverage), "BSGSAverage", "GroupAverage"
        or "GeneratorEquations" (Wolfram, Basis -> "Unitary" only); FormFactorizationMethod Automatic,
        "Cholesky" or "LDL" (an explicit factorization unitarizes the active variant on the Wolfram route; the GAP route
        unitarizes GAP's own witness variant); TPhaseOrder -> "Ascending" | "Unchanged"; PhaseConvention ->
        None | "FirstSRow"; DiagonalizationMethod Automatic or "Exact"; Arithmetic -> "Exact"; common GAP job
        options.
    Returns: The same Group.
    Effects: One GAP generation. Every selected irrep gets a new variant derived from a stored one; the new
        variants become active together, or, if any irrep fails, none does (AtomicTransformFailed). The Wolfram route
        is also taken for an explicit FormFactorizationMethod "Cholesky"/"LDL" and for UnitaryTDiagonal with an explicit
        DiagonalizationMethod "Exact" (methodOptionsPlan.md 2A.7). GAP routes
        (default) verify in GAP (a Wolfram GeneratorEquations unitarization is sent as its conjugator and
        scales and recomputed there). The Wolfram route — Arithmetic -> "Numerical", Spectral factors,
        NumericalReconstruction or Numerical diagonalization, GeneratorEquations with UnitaryTDiagonal, or an
        irrep with no native variant — transforms each active variant with UnitarizeRepresentation and
        DiagonalizeRepresentationT, verifies the result in Wolfram and stores it as an inert Wolfram-tier
        (exact) or Numerical variant derived from the active one (R1).
    Failures: InvalidIrrepID; MissingRepresentation (compute the irreps first); MissingModularAssignment;
        InapplicableOption (UnitarizationMethod -> "BSGSAverage" where the work runs in Wolfram);
        UnsupportedRepresentationData (GeneratorEquations on an irrep without a cyclotomic native witness);
        AtomicTransformFailed (with the per-irrep failures of the Wolfram route); resource failures.
    Example: TransformGroupRepresentations[g, Basis -> "UnitaryTDiagonal", PhaseConvention -> "FirstSRow"].
    Remarks: Irreps already in the requested basis are still re-derived when a T order or phase convention is
        requested for UnitaryTDiagonal; for Basis -> "Unitary" only nonunitary actives are transformed. Unlike
        computation of missing irreps, which accepts verified irreps incrementally, this transform commits all
        selected replacements together.
    See also: UnitarizeRepresentation; DiagonalizeRepresentationT; ComputeGroupRepresentations.
*)
TransformGroupRepresentations[group_Group, selector : Except[_Rule | _RuleDelayed] : All, options : OptionsPattern[]] :=
    cgFieldCatch[transformGroupRepresentationsFieldWork[group, selector, options]];
transformGroupRepresentationsFieldWork[group_Group, selector_, options : OptionsPattern[]] := Module[
    {effective, data, ids, missing, targets, method, payload, derived, wolframOptions, bsgsRefusal},
    effective = resolveOperationOptions[TransformGroupRepresentations, "TransformGroupRepresentations", {options}];
    If[FailureQ[effective], Return[effective]];
    data = groupData[group]; If[FailureQ[data], Return[data]];
    ids = irrepSelection[selector, data]; If[FailureQ[ids], Return[ids]];
    missing = Select[ids, !AssociationQ[Lookup[data["Representations"], #, None]] || !StringQ[data["Representations"][#]["ActiveVariant"]] &];
    If[missing =!= {},
        Return[makeFailure["MissingRepresentation", "Some selected irreps have no active representation; compute them first.",
            <|"IrrepIDs" -> missing, "Suggestions" -> {"ComputeGroupRepresentations[g, " <> ToString[missing, InputForm] <> ", Basis -> \"General\"]"}|>]]];
    If[effective[Basis] === "UnitaryTDiagonal" && !AssociationQ[data["ModularAssignment"]],
        Return[makeFailure["MissingModularAssignment", "Basis -> \"UnitaryTDiagonal\" requires a modular S,T assignment."]]];
    (* Options that put the work in Wolfram; BSGSAverage is a GAP route and is never replaced by another
       unitarizer there. *)
    wolframOptions = effective[Arithmetic] =!= "Exact" || effective[FormFactorizationMethod] === "Spectral" ||
        MemberQ[{"NumericalReconstruction", "Numerical"}, effective[DiagonalizationMethod]] ||
        (* GAP's T-diagonalization picks its own eigenbasis in degenerate T eigenspaces: an explicit Wolfram method name is
           honoured on the Wolfram route (methodOptionsPlan.md 2A.7) *)
        (effective[Basis] === "UnitaryTDiagonal" && effective[DiagonalizationMethod] === "Exact") ||
        (* a weak result is an inert record made in Wolfram (methodOptionsPlan.md 2C.4, C7) *)
        MemberQ[{"Numerical", None}, effective[Verification]] ||
        (* GAP unitarizes its own witness variant (smallest conductor), not the active one: an explicit factorization of
           the active variant's form runs on the Wolfram route (review 2A finding 12) *)
        MemberQ[{"Cholesky", "LDL"}, effective[FormFactorizationMethod]] ||
        (* an explicit exact domain is chosen in Wolfram; GAP's cyclotomic arithmetic has no domain choice (review 2B
           finding 2) *)
        effective[FieldMethod] =!= Automatic ||
        (* WitnessVariant "Active" whose active variant is not native: GAP cannot start from it, Wolfram can (finding 9) *)
        (effective[WitnessVariant] === "Active" && AnyTrue[ids, Function[id, With[{entry = data["Representations"][id]},
            AssociationQ[entry] && StringQ[entry["ActiveVariant"]] &&
                !MemberQ[{"Native", "ScaledNative"}, entry["Variants"][entry["ActiveVariant"]]["Tier"]]]]]) ||
        effective[Basis] === "UnitaryTDiagonal" && effective[UnitarizationMethod] === "GeneratorEquations";
    bsgsRefusal = makeFailure["InapplicableOption", "UnitarizationMethod -> \"BSGSAverage\" runs in GAP; with these options the transform runs in Wolfram. Use Automatic, \"GroupAverage\" or \"GeneratorEquations\"."];
    (* Route (methodOptionsPlan.md 2B.4): "GAP" refuses options only the Wolfram route honours; "Wolfram" transforms
       in Wolfram also when native variants exist *)
    If[effective[Route] === "GAP" && wolframOptions, Return[makeFailure["InapplicableOption",
        "Route -> \"GAP\": these options (Verification \"Numerical\" or None, numerical arithmetic, Spectral or an explicit Cholesky/LDL factorization, numerical or explicit Exact T-diagonalization with UnitaryTDiagonal, GeneratorEquations with UnitaryTDiagonal, an explicit FieldMethod, WitnessVariant \"Active\" on a non-native active variant) are honoured only on the Wolfram route.",
        <|"Options" -> {Route}|>]]];
    If[effective[Route] === "Wolfram", wolframOptions = True];
    If[wolframOptions && effective[UnitarizationMethod] === "BSGSAverage", Return[bsgsRefusal]];
    targets = If[effective[Basis] === "UnitaryTDiagonal", ids,
        Select[ids, !TrueQ[data["Representations"][#]["Variants"][data["Representations"][#]["ActiveVariant"]]["BasisProperties"]["Unitary"]] &]];
    If[targets === {}, Return[group]];
    If[effective[Route] === "GAP" &&
            AnyTrue[targets, !AnyTrue[Values[data["Representations"][#]["Variants"]], gapNativeVariantQ] &],
        Return[makeFailure["InapplicableOption", "Route -> \"GAP\" needs a native (GAP) variant of every selected irrep.", <|"Options" -> {Route}|>]]];
    If[wolframOptions ||
        AnyTrue[targets, !AnyTrue[Values[data["Representations"][#]["Variants"]], gapNativeVariantQ] &],
        If[effective[UnitarizationMethod] === "BSGSAverage", Return[bsgsRefusal]];
        (* the Wolfram route always transforms the active variant (2B.2) *)
        If[effective[WitnessVariant] === "SmallestConductor", Return[makeFailure["InapplicableOption",
            "WitnessVariant -> \"SmallestConductor\" chooses GAP's witness; with these options the transform runs in Wolfram on the active variant.",
            <|"Options" -> {WitnessVariant}|>]]];
        Return[wolframTransform[group, targets, effective]]];
    If[effective[UnitarizationMethod] === "GeneratorEquations" && effective[WitnessVariant] === "SmallestConductor",
        Return[makeFailure["InapplicableOption", "WitnessVariant -> \"SmallestConductor\" chooses GAP's witness; the GeneratorEquations unitarization takes the active (else first) native variant; use \"Active\" or Automatic.",
            <|"Options" -> {WitnessVariant}|>]]];
    If[effective[UnitarizationMethod] === "GeneratorEquations",
        (* Wolfram unitarization of each native witness, sent as (conjugator, scales) and recomputed in GAP. *)
        derived = Association[Map[Function[id, id -> Module[{entry = data["Representations"][id], witness, operand, form, ldl, field},
            (* A native (unscaled, cyclotomic) witness, the active variant first; inert variants never qualify. *)
            witness = SelectFirst[If[effective[WitnessVariant] === "Active", {entry["ActiveVariant"]},
                    DeleteDuplicates[Prepend[Keys[entry["Variants"]], entry["ActiveVariant"]]]],
                entry["Variants"][#]["Tier"] === "Native" && gapNativeVariantQ[entry["Variants"][#]] &, None];
            If[witness === None, Return[$Failed, Module]];
            operand = <|"Matrices" -> repMatrices[entry["Variants"][witness]["Rep"]], "Shape" -> <|"Dimension" -> entry["Dimension"]|>,
                "Snapshot" -> <|"Order" -> data["Order"]|>|>;
            form = invariantForm[operand, "GeneratorEquations", <|"Arithmetic" -> "Exact"|>, AbsoluteTime[] + effective[AttemptTimeLimit]];
            If[FailureQ[form], Return[$Failed, Module]];
            field = form["Field"];
            ldl = ldlDecomposition[form["Form"], <|"Field" -> field|>]; If[FailureQ[ldl], Return[$Failed, Module]];
            <|"witness" -> witness, "conjugator" -> cyclotomicMatrices[fieldBack[fieldAdjoint[field, First[ldl]]], data],
                "scales" -> cyclotomicMatrices[{fieldBack[Last[ldl]]}, data] /. {s_List} :> s|>]], targets]];
        If[!FreeQ[derived, $Failed],
            Return[makeFailure["UnsupportedRepresentationData", "A selected irrep has no cyclotomic native witness for a Wolfram unitarization."]]];
        method = "DerivedNative"; payload = <|"derived" -> derived|>,
        method = If[effective[Basis] === "UnitaryTDiagonal", "TDiagonalize", "Unitarize"];
        payload = <|"unitarize" -> If[effective[UnitarizationMethod] === Automatic, "Automatic", effective[UnitarizationMethod]],
            If[effective[WitnessVariant] =!= Automatic, "witness" -> effective[WitnessVariant], Nothing],
            "phaseOrder" -> effective[TPhaseOrder], "phaseConvention" -> If[effective[PhaseConvention] === None, "None", effective[PhaseConvention]]|>];
    runRepresentationMutation[group, <|"Method" -> method, "IrrepIDs" -> targets, "Basis" -> effective[Basis],
        "Payload" -> Join[payload, <|"atomicCommit" -> True|>], "ReplaceActive" -> targets|>, effective]
];
TransformGroupRepresentations[___] := makeFailure["InvalidInput", "TransformGroupRepresentations expects a live group, an optional irrep selector and options."];

(*
    Summary: The Wolfram route of TransformGroupRepresentations: transform, verify, commit atomically.
    Parameters: group — live Group; targets — irrep IDs with active variants; effective — validated options.
    Options/defaults: As TransformGroupRepresentations (numerical work at WorkingPrecision 50).
    Returns: The same Group, or Failure.
    Effects: Wolfram computation per irrep (UnitarizeRepresentation unless already unitary, then
        DiagonalizeRepresentationT for UnitaryTDiagonal), verification (inertMutationRecord) and one GAP
        generation (method Inert, atomicCommit) that stores every result and activates all of them.
    Failures: AtomicTransformFailed with the per-irrep Failures before any GAP work; resource failures.
    Example: wolframTransform[g, ids, <|..., Arithmetic -> "Numerical", ...|>] stores Numerical variants.
    Remarks: Each variant's derivation is its witness (the active variant) and the combined basis change.
    See also: TransformGroupRepresentations; inertMutationRecord.
*)
wolframTransform[group_Group, targets_List, effective_Association] := Module[{data, results, failures},
    data = groupData[group]; If[FailureQ[data], Return[data]];
    results = Association[Map[Function[id, id -> Module[{entry, witness, rep, basis, step, arithmetic, label = {"Transform"}},
        entry = data["Representations"][id]; witness = entry["ActiveVariant"];
        rep = entry["Variants"][witness]["Rep"];
        arithmetic = If[effective[Arithmetic] === "Exact" && Precision[repMatrices[rep]] === Infinity, "Exact", "Numerical"];
        basis = IdentityMatrix[RepDim[rep]];
        If[!TrueQ[entry["Variants"][witness]["BasisProperties"]["Unitary"]],
            step = UnitarizeRepresentation[group, rep, UnitarizationMethod -> effective[UnitarizationMethod], FieldMethod -> effective[FieldMethod],
                FormFactorizationMethod -> effective[FormFactorizationMethod], Arithmetic -> arithmetic,
                AttemptTimeLimit -> effective[AttemptTimeLimit], Verification -> effective[Verification],
                (* the call's precision and tolerance (2B.4; before: always the default 50) *)
                Sequence @@ If[arithmetic === "Numerical", {WorkingPrecision -> effective[WorkingPrecision], Tolerance -> effective[Tolerance]}, {}]];
            If[FailureQ[step], Return[step, Module]];
            label = Join[label, {step["Validation"]["UnitarizationMethod"], step["Validation"]["FormFactorizationMethod"]}];
            rep = step["Rep"]; basis = step["BasisChange"] . basis];
        If[effective[Basis] === "UnitaryTDiagonal",
            step = DiagonalizeRepresentationT[group, rep, DiagonalizationMethod -> effective[DiagonalizationMethod], FieldMethod -> effective[FieldMethod],
                TPhaseOrder -> effective[TPhaseOrder], PhaseConvention -> effective[PhaseConvention], Arithmetic -> arithmetic,
                AttemptTimeLimit -> effective[AttemptTimeLimit], Verification -> effective[Verification],
                (* WorkingPrecision also drives the exact NumericalReconstruction (review 2B finding 3) *)
                WorkingPrecision -> effective[WorkingPrecision],
                Sequence @@ If[arithmetic === "Numerical", {Tolerance -> effective[Tolerance]}, {}]];
            If[FailureQ[step], Return[step, Module]];
            AppendTo[label, step["Validation"]["DiagonalizationMethod"]];
            rep = step["Rep"]; basis = step["BasisChange"] . basis];
        (* The provenance names the unitarizer, factorization and diagonalization actually used. *)
        inertMutationRecord[group, id, rep, <|"Method" -> StringRiffle[ToString /@ label, "+"], "Model" -> witness|>,
            <|"Witness" -> witness, "Conjugator" -> basis|>, "Unitary", effective]]], targets]];
    failures = Select[results, FailureQ];
    If[failures =!= <||>,
        Return[makeFailure["AtomicTransformFailed", "Not every selected irrep was transformed; no active variant changed.",
            <|"Failures" -> failures|>]]];
    If[effective[Basis] === "UnitaryTDiagonal" && !AllTrue[Values[results], TrueQ[#["basisProperties"]["tDiagonal"]] &],
        Return[makeFailure["AtomicTransformFailed", "A transformed irrep does not have diagonal T; no active variant changed."]]];
    runRepresentationMutation[group, <|"Method" -> "Inert", "IrrepIDs" -> targets, "Basis" -> effective[Basis],
        "Payload" -> <|"inert" -> results, "atomicCommit" -> True|>, "ReplaceActive" -> targets|>, effective]
];
wolframTransform[___] := makeFailure["InvalidInput", "Expected a live group, irrep IDs and options."];

True
