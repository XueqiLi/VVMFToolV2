(*
    :Title: Clebsch-Gordan requests, data snapshots and the group CG store
    :Context: VVMFTool`Private`
    :Summary: Resolve a CG request against a group or frozen context (variants, identities, multiplicities,
        normalization and exchange conventions), compute or reuse whole target bundles through the registered
        methods, assemble immutable CGData snapshots and serve their accessors.
    :Responsibilities:
        - makeCGRequest, resolveCGInputs, cgCacheKey, lookupCG, cgMethodDescriptors, computeCGBundle (cgRouteSpaces,
          cgFinishRoute, cgFinishSettings, cgRevalidatedBundle), cgAttemptDescriptors, cgSubgroupInformationQ,
          planCGAttempts, cgBundleByMethod, mergeCGBundle, evictCG, makeCGData, validateCGSchema.
        - CGCoefficients, CGIntertwiners, CGMatrix, ValidateCG, CacheCG, CGCacheInformation, CleanCGCache.
    :Dependencies: TensorCharacters.wl; CGLinear.wl; CGValidation.wl; CGProjection.wl; CGAdvanced.wl;
        Representation.wl (resolveRepContext, repMatrices, RepDim); RepresentationValidation.wl
        (arithmeticSettings); GroupObject.wl (groupData, commitGroup, emptyCGCache); GroupConstruction.wl
        (resolveOperationOptions).
    :See Also: VVMFArch/step4Plan.md; VVMFArch/implementation/step4Status.md (D-S4-2, D-S4-8).
*)

(* Automatic method order (step4Plan.md): an initial documented order, not a speed claim. *)
$CGMethodOrder = {"GeneratorEquations", "ProjectionLazy", "SubgroupChain", "AveragedBSGS", "SerreBSGS", "Serre",
    "CanonicalHybrid", "AveragedIntertwiners", "AveragedOrbit", "SubgroupEmbedding", "CommutantSpectral",
    "AdaptedStates", "ProjectionEager"};

(* Digits of the numerical proposals that exact reconstruction recognizes. *)
$CGReconstructionDigits = 120;

(*
    Summary: The registered CG method descriptors.
    Parameters: None.
    Options/defaults: None.
    Returns: Association method -> <|"Route" -> function of a problem, "Kind" -> "Wolfram" | "Native",
        "Exact" -> "Direct" | "Reconstruct" | "None", "Numerical" -> Boolean, "UnitaryInputs" -> Boolean,
        "Elements" -> Boolean (enumerates the image group)|>.
    Effects: Pure.
    Failures: None.
    Example: cgMethodDescriptors[]["ProjectionLazy"]["Exact"] is "Direct".
    Remarks: A route takes the resolved problem (domain matrices, dimensions, order, multiplicity, arithmetic)
        and returns <|"Kets", "Bras"|> spanning the complete Hom spaces; normalization, exchange sectors and
        validation are shared afterwards. Native GAP routes and the chain/subgroup routes register in their
        own modules (CGNative.wl).
    See also: computeCGBundle; $CGMethodOrder.
*)
cgMethodDescriptors[] := Join[<|
    "GeneratorEquations" -> <|"Route" -> (generatorCGSpaces[#P, #Q, #D, #Dims, #Multiplicity, #Arithmetic, #Prefilter] &),
        "Kind" -> "Wolfram", "Exact" -> "Direct", "Numerical" -> True, "UnitaryInputs" -> False, "Elements" -> False|>,
    "ProjectionEager" -> <|"Route" -> (projectionCG[#P, #Q, #D, #Dims, #Order, #Multiplicity, #Arithmetic, "Eager", #Unitary] &),
        "Kind" -> "Wolfram", "Exact" -> "Direct", "Numerical" -> True, "UnitaryInputs" -> False, "Elements" -> True|>,
    "ProjectionLazy" -> <|"Route" -> (projectionCG[#P, #Q, #D, #Dims, #Order, #Multiplicity, #Arithmetic, "Lazy", #Unitary] &),
        "Kind" -> "Wolfram", "Exact" -> "Direct", "Numerical" -> True, "UnitaryInputs" -> False, "Elements" -> True|>,
    "AveragedIntertwiners" -> <|"Route" -> (averagedCG[#P, #Q, #D, #Dims, #Order, #Multiplicity, #Arithmetic, "Whole"] &),
        "Kind" -> "Wolfram", "Exact" -> "Direct", "Numerical" -> True, "UnitaryInputs" -> False, "Elements" -> True|>,
    "AveragedOrbit" -> <|"Route" -> (averagedCG[#P, #Q, #D, #Dims, #Order, #Multiplicity, #Arithmetic, "Orbit"] &),
        "Kind" -> "Wolfram", "Exact" -> "Direct", "Numerical" -> False, "UnitaryInputs" -> False, "Elements" -> False|>,
    "CanonicalHybrid" -> <|"Route" -> (canonicalCG[#P, #Q, #D, #Dims, #Order, #Multiplicity, #Arithmetic] &),
        "Kind" -> "Wolfram", "Exact" -> "Direct", "Numerical" -> True, "UnitaryInputs" -> False, "Elements" -> True|>,
    "CommutantSpectral" -> <|"Route" -> (commutantCG[#NP, #NQ, #ND, #Dims, #Multiplicity, #NumericalSettings] &),
        "Kind" -> "Wolfram", "Exact" -> "Reconstruct", "Numerical" -> True, "UnitaryInputs" -> True, "Elements" -> False|>,
    "AdaptedStates" -> <|"Route" -> (adaptedStateCG[#NP, #NQ, #ND, #Dims, #Order, #Multiplicity, #NumericalSettings] &),
        "Kind" -> "Wolfram", "Exact" -> "Reconstruct", "Numerical" -> True, "UnitaryInputs" -> True, "Elements" -> True|>|>,
    If[AssociationQ[$CGNativeMethods], $CGNativeMethods, <||>]];

(*
    Summary: The variant data of one irrep in a resolved context.
    Parameters: snapshot — group data or context snapshot; id — irrep ID.
    Options/defaults: None.
    Returns: <|"IrrepID", "VariantID", "Identity", "Rep", "Matrices", "Dimension", "Tier", "Arithmetic", "Unitary",
        "VerificationStatus" (variantVerificationStatus)|>, or Missing["NotComputed"].
    Effects: Pure.
    Failures: None.
    Example: cgVariant[groupData[g], id]["Unitary"] is True for a unitary active variant.
    See also: resolveCGInputs.
*)
cgVariant[snapshot_Association, id_String] := Module[{entry = Lookup[Lookup[snapshot, "Representations", <||>], id, Missing[]], active, variant},
    If[!AssociationQ[entry], Return[Missing["NotComputed"]]];
    active = Lookup[entry, "ActiveVariant", Missing[]];
    If[!StringQ[active], Return[Missing["NotComputed"]]];
    variant = entry["Variants"][active];
    <|"IrrepID" -> id, "VariantID" -> active, "Identity" -> variant["Identity"], "Rep" -> variant["Rep"],
        "Matrices" -> repMatrices[variant["Rep"]], "Dimension" -> RepDim[variant["Rep"]], "Tier" -> variant["Tier"],
        "Arithmetic" -> variant["Arithmetic"], "Unitary" -> TrueQ[variant["BasisProperties"]["Unitary"]],
        (* the stored variant's verification status (methodOptionsPlan.md 2C.1) *)
        "VerificationStatus" -> variantVerificationStatus[variant]|>
];

(*
    Summary: Validate and resolve the conventions of a CG request.
    Parameters: context — Group or RepresentationContext; pair — {p, q}; targets — All, an ID or a list of IDs;
        effective — validated options.
    Options/defaults: Normalization Automatic -> "Unitary" when all participating matrices are unitary, otherwise "Dual"
        (an explicit "Dual" is kept, methodOptionsPlan.md 2A.1); ExchangeSymmetry
        Automatic splits sectors exactly when both factors are the same variant.
    Returns: <|"Context" -> context, "Snapshot", "Characters", "Pair", "Targets" (selected, character-table order),
        "AllTargets" (positive multiplicities), "Multiplicities", "Normalization", "Exchange" (True/False),
        "SymmetryMode", "Arithmetic", "Settings", "Missing" -> irrep IDs without matrices|>, or Failure.
    Effects: Pure.
    Failures: UnverifiedContext; CharactersUnavailable; InvalidIrrep; InvalidOption (explicit Unitary with a
        general basis, Separate with different factors, exact arithmetic for numerical matrices).
    Example: makeCGRequest[g, {t, t}, t, <|...|>]["Exchange"] is True.
    Remarks: Targets of multiplicity zero are covered by an empty bundle and need no matrices.
    See also: resolveCGInputs; CGCoefficients.
*)
makeCGRequest[context_, pair : {p_String, q_String}, targets_, effective_Association] := Module[
    {snapshot, characters, ids, selected, multiplicities, variants, missing, unitary, normalization, exchange, arithmetic,
        precision, settings},
    snapshot = If[Head[context] === Group, groupData[context], resolveRepContext[context]];
    If[FailureQ[snapshot], Return[snapshot]];
    characters = snapshot["CharacterData"];
    If[!AssociationQ[characters] || Length[characters["IrrepIDs"]] =!= Length[characters["ClassIDs"]],
        Return[makeFailure["CharactersUnavailable", "CG coefficients need the complete character table."]]];
    ids = characters["IrrepIDs"];
    If[!SubsetQ[ids, pair], Return[makeFailure["InvalidIrrep", "Unknown input irrep ID.", <|"IrrepIDs" -> Complement[pair, ids]|>]]];
    selected = Which[targets === All, ids, StringQ[targets], {targets},
        ListQ[targets] && AllTrue[targets, StringQ] && DuplicateFreeQ[targets], targets, True, $Failed];
    If[selected === $Failed || !SubsetQ[ids, selected],
        Return[makeFailure["InvalidIrrep", "Targets must be All, an irrep ID or a duplicate-free list of irrep IDs.",
            <|"Targets" -> targets|>]]];
    selected = Select[ids, MemberQ[selected, #] &];
    multiplicities = tensorMultiplicities[characters, pair];
    If[FailureQ[multiplicities], Return[multiplicities]];
    variants = AssociationMap[cgVariant[snapshot, #] &, DeleteDuplicates[Join[pair, Select[selected, multiplicities[#] > 0 &]]]];
    missing = Keys[Select[variants, MissingQ]];
    unitary = AllTrue[Values[Select[variants, AssociationQ]], #["Unitary"] &];
    normalization = Switch[effective[Normalization],
        Automatic, If[unitary, "Unitary", "Dual"],
        (* an explicit Dual stays Dual (methodOptionsPlan.md 2A.1); the call notes that Unitary is available *)
        "Dual", "Dual",
        "Unitary", If[unitary, "Unitary", Return[makeFailure["InvalidOption",
            "Normalization -> \"Unitary\" needs unitary stored matrices for the inputs and targets.", <|"Options" -> {Normalization}|>]]]];
    exchange = Which[
        effective[ExchangeSymmetry] === None, False,
        missing =!= {} && MemberQ[missing, p | q], p === q,
        True, AssociationQ[variants[p]] && AssociationQ[variants[q]] && variants[p]["Identity"] === variants[q]["Identity"]];
    If[effective[ExchangeSymmetry] === "Separate" && !(p === q),
        Return[makeFailure["InvalidOption", "ExchangeSymmetry -> \"Separate\" needs equal factors.", <|"Options" -> {ExchangeSymmetry}|>]]];
    arithmetic = effective[Arithmetic];
    If[arithmetic === "Exact" && AnyTrue[Values[Select[variants, AssociationQ]], #["Tier"] === "Numerical" &],
        Return[makeFailure["NumericalInput", "Exact CG coefficients need exact stored matrices; use Arithmetic -> \"Numerical\"."]]];
    precision = If[arithmetic === "Exact", Infinity,
        Min[Append[Precision /@ Lookup[Values[Select[variants, AssociationQ]], "Matrices"], Infinity]]];
    settings = arithmeticSettings[arithmetic, effective[WorkingPrecision], effective[Tolerance], precision];
    If[FailureQ[settings], Return[settings]];
    settings = cgCheckSettings[settings, effective];
    <|"Context" -> context, "Snapshot" -> snapshot, "Characters" -> characters, "Pair" -> pair, "Targets" -> selected,
        "AllTargets" -> Select[ids, multiplicities[#] > 0 &], "Multiplicities" -> multiplicities, "Variants" -> variants,
        "Normalization" -> normalization, "Exchange" -> exchange,
        "SymmetryMode" -> Which[exchange, "Separate", effective[ExchangeSymmetry] === None, "None", True, "Unsplit"],
        "Arithmetic" -> arithmetic, "Settings" -> settings, "Missing" -> missing, "Options" -> effective,
        "Notes" -> If[effective[Normalization] === "Dual" && unitary && missing === {},
            {"Normalization -> \"Dual\" is kept as requested; these matrices are unitary, so Normalization -> \"Unitary\" (W = K^dagger) is available"}, {}]|>
];

(*
    Summary: The cache key of one target bundle.
    Parameters: request — from makeCGRequest (with variants); target — irrep ID.
    Options/defaults: None.
    Returns: SHA256 hex string.
    Effects: Pure.
    Failures: None (requires resolved variants).
    Example: equal requests under a reordered presentation give equal keys.
    Remarks: Keys bind the group state, the ordered input realization identities, the target's realization
        identity and the output conventions (normalization, exchange mode, arithmetic and numerical precision);
        presentation order and S,T assignments are not part of them.
    See also: lookupCG; mergeCGBundle.
*)
cgCacheKey[request_Association, target_String] := cgKeyFromParts[
    request["Snapshot"][If[KeyExistsQ[request["Snapshot"], "StateID"], "StateID", "GroupIdentity"]],
    {request["Variants"][request["Pair"][[1]]]["Identity"], request["Variants"][request["Pair"][[2]]]["Identity"]},
    If[request["Multiplicities"][target] > 0, request["Variants"][target]["Identity"], "zero:" <> target],
    request["Normalization"], request["SymmetryMode"], request["Arithmetic"],
    If[request["Arithmetic"] === "Exact", Infinity, request["Settings"]["Precision"]]];

(*
    Summary: The cache key from its parts (shared by requests and snapshot import).
    Parameters: state — group state ID; inputs — the two input realization identities; target — target realization
        identity; normalization; mode — exchange-symmetry mode; arithmetic; precision — Infinity or digits.
    Options/defaults: None.
    Returns: SHA256 hex string.
    Effects: Pure.
    Failures: None.
    Example: cgKeyFromParts[s, {a, a}, b, "Unitary", "Separate", "Exact", Infinity] is a 64-character string.
    See also: cgCacheKey; importCGBundles.
*)
cgKeyFromParts[state_, inputs_List, target_, normalization_, mode_, arithmetic_, precision_] :=
    Hash[{"CG", 1, state, inputs[[1]], inputs[[2]], target, normalization, mode, arithmetic, precision}, "SHA256", "HexString"];

(*
    Summary: The stored bundle of one target, if any.
    Parameters: request; target.
    Options/defaults: None.
    Returns: The stored bundle association with "LookupMark" -> "ok" | "upgraded" | "not rechecked", or
        Missing["NotCached"], or Missing["InvalidStoredBundle"] (a check at the call's level failed; the caller recomputes
        and acceptCGBundles replaces it).
    Effects: Read; checks are memoised in $CGDeferredValidations (by key, channel hash and level).
    Failures: Throws FieldMethodUnavailable (cgArithmetic) when the call's explicit FieldMethod has no domain for a check;
        that is never recorded as an invalid entry.
    Example: after CacheCG every positive-multiplicity target of a pair is found.
    Remarks: A context request reads the store of its live group when that group still has the context's state.
        Levels (methodOptionsPlan.md 1.4, R3-1): Verification -> None serves the entry as stored ("not rechecked" for an
        entry deferred at an unverified import). An entry of a registered file is trusted at its recorded status
        (fastLoad.md). Otherwise an entry deferred at import, or one whose status is weaker than the call's
        level, is checked at the call's level: passed, it carries the stronger status ("upgraded" when that raised the
        stored status, which a group call commits; "ok" for a deferred entry that kept its status).
    See also: cgCacheKey; CGCacheInformation.
*)
lookupCG[request_Association, target_String] := Module[{store = cgStore[request["Context"]], entry, level, deferred, weak, checked},
    If[!AssociationQ[store], Return[Missing["NotCached"]]];
    entry = Lookup[store["Entries"], cgCacheKey[request, target], Missing["NotCached"]];
    If[!AssociationQ[entry], Return[entry]];
    level = Lookup[request["Settings"], "Verification", Automatic];
    deferred = entry["Validation"] === Missing["Deferred"];
    (* an entry a check of this kernel found invalid is never served, at any level (it is recomputed and replaced) *)
    If[cgStoredInvalidQ[entry], Return[Missing["InvalidStoredBundle"]]];
    (* None serves stored entries unchecked, but never one a check of this kernel found invalid (review finding 1); a
       deferred entry served unchecked is reported "Unverified" for this call (finding 2, R3-1: never shown as checked) *)
    If[level === None, Return[Which[
        deferred, Join[entry, <|"VerificationStatus" -> "Unverified", "LookupMark" -> "not rechecked"|>],
        True, Join[entry, <|"LookupMark" -> "ok"|>]]]];
    weak = cgStatusRank[cgEntryStatus[entry]] < cgStatusRank[cgRequiredStatus[level, entry["Arithmetic"]]];
    If[!deferred && !weak, Return[Join[entry, <|"LookupMark" -> "ok"|>]]];
    (* an entry deferred at import, or weaker than the call's level, is checked at that level; one that
       fails is not served (it is recomputed, and acceptCGBundles replaces it) *)
    checked = cgStoredCheck[entry, request["Variants"][request["Pair"][[1]]]["Matrices"],
        request["Variants"][request["Pair"][[2]]]["Matrices"], request["Variants"][target]["Matrices"], request["Settings"]];
    If[!checked["Passed"], Return[Missing["InvalidStoredBundle"]]];
    Join[cgCheckedEntry[entry, checked], <|"LookupMark" -> If[weak, "upgraded", "ok"]|>]
];

(*
    Summary: The CG store visible to a group or context.
    Parameters: context — Group or RepresentationContext.
    Options/defaults: None.
    Returns: The CGCache association, or None.
    Effects: Pure.
    Failures: None.
    Example: cgStore[g]["Epoch"] is 0 for a new group.
    Remarks: A context sees the store of a live group with the same state ID (entries are keyed by variant
        realization identities, so they are valid for the context's frozen variants).
    See also: lookupCG.
*)
cgStore[group_Group] := With[{data = groupData[group]}, If[FailureQ[data], None, data["CGCache"]]];
cgStore[context_RepresentationContext] := Module[{snapshot = resolveRepContext[context], live},
    If[FailureQ[snapshot], Return[None]];
    (* Several live handles can share a state ID (an import creates a fresh handle); prefer the one at the
       context's generation, then any. Entries are keyed by realization identities, so either store is valid. *)
    live = With[{candidates = Select[Values[$GroupRegistry], Lookup[#, "StateID", None] === snapshot["GroupIdentity"] &]},
        SelectFirst[candidates, #["StateGeneration"] === snapshot["StateGeneration"] &, SelectFirst[candidates, True &, None]]];
    If[AssociationQ[live], live["CGCache"], None]];
cgStore[___] := None;

(*
    Summary: The resolved numerical problem of one target for the method routes.
    Parameters: request; target; arithmetic — from cgArithmetic over the participating matrices.
    Options/defaults: None.
    Returns: Association with P, Q, D (domain values), NP, NQ, ND (numerical at $CGReconstructionDigits or the
        numerical settings), Dims, Order, Multiplicity, Arithmetic, NumericalSettings, Prefilter, Unitary,
        Original (canonical matrices).
    Effects: Pure.
    Failures: None.
    Example: cgProblem[request, t, ar]["Dims"] is {3, 3, 3} for A4 3 (x) 3 -> 3.
    See also: computeCGBundle.
*)
cgProblem[request_Association, target_String, arithmetic_Association] := Module[{p, q, d, numerical, precision},
    {p, q, d} = request["Variants"][#]["Matrices"] & /@ Append[request["Pair"], target];
    precision = If[request["Arithmetic"] === "Exact", $CGReconstructionDigits, request["Settings"]["Precision"]];
    numerical = If[request["Arithmetic"] === "Exact", arithmeticSettings["Numerical", precision, Automatic, Infinity], request["Settings"]];
    <|"P" -> arithmetic["Embed"][p], "Q" -> arithmetic["Embed"][q], "D" -> arithmetic["Embed"][d],
        "NP" -> N[p, precision], "NQ" -> N[q, precision], "ND" -> N[d, precision],
        "Dims" -> (request["Variants"][#]["Dimension"] & /@ Append[request["Pair"], target]),
        "Order" -> request["Snapshot"]["Order"], "Multiplicity" -> request["Multiplicities"][target],
        "Arithmetic" -> arithmetic, "NumericalSettings" -> numerical, "Prefilter" -> TrueQ[request["Options"][Prefilter]],
        "Unitary" -> AllTrue[request["Variants"] /@ Append[request["Pair"], target], #["Unitary"] &],
        "Original" -> <|"P" -> p, "Q" -> q, "D" -> d|>, "Request" -> request, "TargetID" -> target|>
];

(*
    Summary: Compute, normalize and validate the complete bundle of one target with one method.
    Parameters: request; target; method — a registered method name.
    Options/defaults: None.
    Returns: <|"Key", "TargetID", "Channels" -> {<|"Copy", "Symmetry", "Embedding", "Dual"|>...}, "Validation",
        "Method"|>, or Failure.
    Effects: Pure.
    Failures: MethodInapplicable (numerical-only method for exact data without reconstruction, exact-only method
        in numerical mode, a unitary-input method with general stored matrices); FieldConversionFailed
        (NumberField -> True without a common number field, for every route); the route's failures;
        UnprovedIdentity when the normalized bundle does not validate.
    Example: computeCGBundle[request, t, "GeneratorEquations"]["Channels"] has one channel per copy.
    Remarks: Exact routes return domain values; reconstruct routes return numerical proposals that reconstructCG
        accepts only after exact covariance and rank checks. A target of multiplicity zero gives an empty bundle.
        The work is cgRouteSpaces (the method's computation) followed by cgFinishRoute (exchange sectors,
        normalization, validation); a race runs the first in a subkernel and the second here (CGRace.wl).
    See also: cgMethodDescriptors; cgRouteSpaces; cgFinishRoute; normalizeCGCopies; validateCGBundle.
*)
computeCGBundle[request_Association, target_String, method_String] :=
    cgFinishRoute[request, target, method, cgRouteSpaces[request, target, method]];

(*
    Summary: The method's computation for one target, before the shared normalization and validation.
    Parameters: request — a request from makeCGRequest, or its race copy without the live context (cgRaceRequest);
        target; method.
    Options/defaults: None.
    Returns: <|"Kind" -> "Spaces", "Spaces" -> <|"Kets", "Bras"|> in the domain, "Field" -> exact domain or None,
        "Settings" -> the domain's arithmetic settings, "Dims"|>; or <|"Kind" -> "Bundle", "Bundle" -> finished bundle|>
        for an empty target, an exact witness (numerical output of an exact-only route) and a temporary unitary
        transport; or Failure.
    Effects: Pure.
    Failures: As computeCGBundle, before validation.
    Example: cgRouteSpaces[request, t, "GeneratorEquations"]["Kind"] is "Spaces".
    Remarks: The result is plain data (the domain, not its functions), so it can be returned from another kernel.
        Only the transport path reads the live context; under Method -> Automatic the race never takes it
        (cgAttemptDescriptors).
    See also: computeCGBundle; cgFinishRoute; cgArithmeticFromField.
*)
cgRouteSpaces[request_Association, target_String, method_String] := cgFieldCatch[cgRouteSpacesWork[request, target, method]];
cgRouteSpacesWork[request_Association, target_String, method_String] := Module[
    {descriptor, arithmetic, problem, spaces, dims, exact = request["Arithmetic"] === "Exact"},
    If[request["Multiplicities"][target] === 0,
        Return[<|"Kind" -> "Bundle", "Bundle" -> <|"Key" -> cgCacheKey[request, target], "TargetID" -> target, "Channels" -> {},
            "Validation" -> <|"Empty" -> True|>, "Method" -> "Characters", "VerificationStatus" -> "Exact"|>|>]];
    descriptor = Lookup[cgMethodDescriptors[], method, None];
    If[descriptor === None, Return[makeFailure["UnknownMethod", "The CG method is not registered.", <|"Method" -> method|>]]];
    Which[
        exact && descriptor["Exact"] === "None", Return[makeFailure["MethodInapplicable", "The method has no exact form.", <|"Method" -> method|>]],
        (* Exact-only routes give numerical output through an exact witness: the stored matrices are exact. *)
        !exact && !descriptor["Numerical"] && AllTrue[request["Variants"] /@ Append[request["Pair"], target], #["Tier"] =!= "Numerical" &],
            Return[With[{bundle = exactWitnessCGBundle[request, target, method]}, If[FailureQ[bundle], bundle, <|"Kind" -> "Bundle", "Bundle" -> bundle|>]]],
        !exact && !descriptor["Numerical"], Return[makeFailure["MethodInapplicable", "The method needs exact matrices or an exact witness.", <|"Method" -> method|>]]];
    arithmetic = cgArithmetic[Append[request["Variants"][#]["Matrices"] & /@ request["Pair"], request["Variants"][target]["Matrices"]], request["Settings"]];
    (* NumberField -> True binds every route, including those transported through temporary unitary forms. *)
    If[exact && request["Settings"]["NumberField"] === True && arithmetic["Field"]["Kind"] =!= "NumberField",
        Return[makeFailure["FieldConversionFailed", "No common number field of the participating matrices was found within the budget.",
            <|"Method" -> method|>]]];
    If[descriptor["UnitaryInputs"] && !AllTrue[request["Variants"] /@ Append[request["Pair"], target], #["Unitary"] &],
        Return[With[{bundle = transportedCGBundle[request, target, method, descriptor]}, If[FailureQ[bundle], bundle, <|"Kind" -> "Bundle", "Bundle" -> bundle|>]]]];
    problem = cgProblem[request, target, arithmetic];
    dims = problem["Dims"];
    spaces = descriptor["Route"][problem];
    If[FailureQ[spaces], Return[spaces]];
    If[exact && descriptor["Exact"] === "Reconstruct",
        spaces = reconstructCG[spaces, problem["Original"]["P"], problem["Original"]["Q"], problem["Original"]["D"], dims,
            problem["Multiplicity"], $CGReconstructionDigits, request["Settings"]];
        If[FailureQ[spaces], Return[spaces]];
        (* reconstructCG works in the same exact domain (exactField is memoized by the atom set). *)
        arithmetic = spaces["Arithmetic"]];
    (* Numerical proposals at the working precision: accuracy-only zeros become exact zeros before normalization. *)
    If[!exact && descriptor["Exact"] === "Reconstruct",
        spaces = <|"Kets" -> (toArithmetic[#, request["Settings"]] & /@ spaces["Kets"]),
            "Bras" -> (toArithmetic[#, request["Settings"]] & /@ spaces["Bras"])|>];
    <|"Kind" -> "Spaces", "Spaces" -> KeyTake[spaces, {"Kets", "Bras"}], "Field" -> arithmetic["Field"],
        "Settings" -> arithmetic["Settings"], "Dims" -> dims,
        (* the subgroup route names the source of its subgroup in the stored method (2A.6) *)
        "MethodLabel" -> If[AssociationQ[Lookup[spaces, "Subgroup", None]] && StringQ[Lookup[spaces["Subgroup"], "Source", None]],
            method <> " (" <> spaces["Subgroup"]["Source"] <> ")", method]|>
];

(*
    Summary: The bundle from a method's computation: exchange sectors, normalization and validation.
    Parameters: request — the full request; target; method; route — cgRouteSpaces result (possibly from another
        kernel).
    Options/defaults: None.
    Returns: Bundle association, or Failure.
    Effects: Pure.
    Failures: The route's failure; finishCGBundle's failures; UnprovedIdentity for a finished bundle that does not
        validate here; InvalidRouteResult for a malformed route result.
    Example: cgFinishRoute[request, t, m, cgRouteSpaces[request, t, m]] is computeCGBundle[request, t, m].
    Remarks: Spaces are finished in the domain rebuilt from the returned field (cgArithmeticFromField), against the
        request's own matrices. A finished bundle is returned as is when computed in this kernel (local -> True) and
        is otherwise validated again here against the request's matrices, so no result from another kernel is
        accepted without this kernel's check.
    See also: computeCGBundle; cgRouteSpaces; finishCGBundle; cgRaceBatch.
*)
cgFinishRoute[request_Association, target_String, method_String, route_, local_ : True] := With[{bundle = cgFieldCatch[cgFinishRouteBundle[request, target, method, route, local]]},
    (* only a bundle association or a Failure leaves here *)
    If[AssociationQ[bundle] || FailureQ[bundle], bundle, makeFailure["InvalidRouteResult", "The CG method gave no bundle.", <|"Method" -> method|>]]];
(*
    Summary: cgFinishRoute's work, before its check that a bundle or a Failure leaves.
    Parameters: As cgFinishRoute.
    Options/defaults: None.
    Returns: Bundle, Failure, or (for a malformed route result) InvalidRouteResult.
    Effects: Pure.
    Failures: As cgFinishRoute.
    Example: cgFinishRouteBundle[request, t, m, cgRouteSpaces[request, t, m], True] is computeCGBundle[request, t, m].
    Remarks: Spaces are finished with the settings this kernel's own computation would use (cgFinishSettings), not the
        ones returned with the spaces; only the domain (field) is taken from the route result.
    See also: cgFinishRoute; cgFinishSettings.
*)
cgFinishRouteBundle[request_Association, target_String, method_String, route_, local_] := Which[
    FailureQ[route], route,
    AssociationQ[route] && route["Kind"] === "Spaces" && AssociationQ[route["Spaces"]] && AssociationQ[route["Settings"]],
        finishCGBundle[request, target, Lookup[route, "MethodLabel", method], route["Spaces"], cgArithmeticFromField[route["Field"], cgFinishSettings[request, method]],
            <|"P" -> request["Variants"][request["Pair"][[1]]]["Matrices"], "Q" -> request["Variants"][request["Pair"][[2]]]["Matrices"],
                "D" -> request["Variants"][target]["Matrices"]|>, route["Dims"], cgCacheKey[request, target]],
    AssociationQ[route] && route["Kind"] === "Bundle" && AssociationQ[route["Bundle"]],
        If[TrueQ[local], route["Bundle"], cgRevalidatedBundle[request, target, method, route["Bundle"]]],
    True, makeFailure["InvalidRouteResult", "The CG method returned a malformed result.", <|"Method" -> method|>]
];

(*
    Summary: The arithmetic settings with which a method's spaces are finished.
    Parameters: request; method.
    Options/defaults: None.
    Returns: The request's settings, or for exact reconstruct routes the exact settings reconstructCG works in.
    Effects: Pure.
    Failures: None.
    Example: cgFinishSettings[request, "GeneratorEquations"] === request["Settings"].
    See also: cgRouteSpaces; reconstructCG.
*)
cgFinishSettings[request_Association, method_String] :=
    If[request["Arithmetic"] === "Exact" && Lookup[Lookup[cgMethodDescriptors[], method, <||>], "Exact", None] === "Reconstruct",
        cgCheckSettings[arithmeticSettings["Exact", 50, Automatic, Infinity], request["Settings"]], request["Settings"]];

(*
    Summary: A finished bundle from another kernel, validated again against the request's matrices.
    Parameters: request; target; method — the method that was run; bundle.
    Options/defaults: None.
    Returns: The bundle with this kernel's key and validation, or Failure.
    Effects: Pure.
    Failures: UnprovedIdentity (also for a channel count other than the multiplicity); InvalidRouteResult for a
        malformed bundle.
    Example: a forged channel in a subkernel's bundle gives UnprovedIdentity.
    See also: cgFinishRoute; validateCGBundle.
*)
cgRevalidatedBundle[request_Association, target_String, method_String, bundle_Association] := Module[{channels = Lookup[bundle, "Channels", None], checked},
    If[!ListQ[channels] || !AllTrue[channels, AssociationQ[#] && KeyExistsQ[#, "Embedding"] && KeyExistsQ[#, "Dual"] &],
        Return[makeFailure["InvalidRouteResult", "The returned CG bundle is malformed.", <|"TargetID" -> target|>]]];
    If[channels === {}, Return[If[request["Multiplicities"][target] === 0, Join[bundle, <|"Key" -> cgCacheKey[request, target]|>],
        makeFailure["UnprovedIdentity", "The returned CG bundle has no channels.", <|"TargetID" -> target|>]]]];
    (* one channel per copy, numbered 1..m: a short bundle with valid channels is not complete *)
    If[Length[channels] =!= request["Multiplicities"][target] || Lookup[channels, "Copy", None] =!= Range[Length[channels]],
        Return[makeFailure["UnprovedIdentity", "The returned CG bundle does not have one channel per copy.", <|"TargetID" -> target|>]]];
    (* the same acceptance as where the bundle was made: finishCGBundle, or for numerical output of an exact-only
       method exactWitnessCGBundle (no unitarity flag); decided from the request and method, not the bundle *)
    checked = cgVerifyBundle[KeyDrop[#, "Copy"] & /@ channels, request["Variants"][request["Pair"][[1]]]["Matrices"],
        request["Variants"][request["Pair"][[2]]]["Matrices"], request["Variants"][target]["Matrices"], request["Normalization"],
        request["Settings"], request["Exchange"],
        !(request["Arithmetic"] =!= "Exact" && !TrueQ[Lookup[Lookup[cgMethodDescriptors[], method, <||>], "Numerical", True]])];
    If[!checked["Passed"],
        Return[makeFailure["UnprovedIdentity", "The returned CG bundle did not validate.", <|"Validation" -> checked["Validation"], "TargetID" -> target|>]]];
    Join[bundle, <|"Key" -> cgCacheKey[request, target], "TargetID" -> target|>, KeyDrop[checked, "Passed"]]
];

(*
    Summary: Numerical output of an exact-only route through an exact witness.
    Parameters: request — a numerical request whose stored matrices are exact; target; method.
    Options/defaults: None.
    Returns: Bundle with numerical channels at the request's precision, validated numerically, or Failure.
    Effects: Pure.
    Failures: The exact computation's failures; numerical validation failures.
    Example: AveragedOrbit with Arithmetic -> "Numerical" on exact stored matrices returns numerical channels.
    Remarks: The exact bundle is computed under exact settings and converted; the numerical checks then run on the
        converted channels against the numerical matrices (step4Plan.md: numerical output may be transported from exact
        witness calculations and then numerically verified).
    See also: computeCGBundle.
*)
exactWitnessCGBundle[request_Association, target_String, method_String] := Module[{exactRequest, bundle, channels, checked},
    exactRequest = Join[request, <|"Arithmetic" -> "Exact", "Settings" -> cgCheckSettings[arithmeticSettings["Exact", 50, Automatic, Infinity],
        request["Settings"]]|>];
    bundle = computeCGBundle[exactRequest, target, method];
    If[FailureQ[bundle], Return[bundle]];
    channels = Map[Join[#, <|"Embedding" -> toArithmetic[#["Embedding"], request["Settings"]], "Dual" -> toArithmetic[#["Dual"], request["Settings"]]|>] &,
        bundle["Channels"]];
    checked = cgVerifyBundle[KeyDrop[#, "Copy"] & /@ channels, request["Variants"][request["Pair"][[1]]]["Matrices"],
        request["Variants"][request["Pair"][[2]]]["Matrices"], request["Variants"][target]["Matrices"], request["Normalization"],
        request["Settings"], request["Exchange"], False];
    If[!checked["Passed"],
        Return[makeFailure["UnprovedIdentity", "The converted witness bundle did not validate numerically.", <|"Validation" -> checked["Validation"]|>]]];
    (* the witness's status is the weaker of its exact computation and the numerical check here *)
    Join[<|"Key" -> cgCacheKey[request, target], "TargetID" -> target, "Channels" -> channels, "Method" -> Lookup[bundle, "Method", method] <> " (exact witness)",
        "Domain" -> Lookup[bundle, "Domain", Missing["NotRecorded"]]|>, KeyDrop[checked, "Passed"],
        <|"VerificationStatus" -> cgWeakestStatus[{cgEntryStatus[bundle], checked["VerificationStatus"]}]|>]
];

(*
    Summary: Shared tail of a bundle: exchange sectors, normalization, validation.
    Parameters: request; target; method; spaces — <|"Kets", "Bras"|> in arithmetic's domain; arithmetic; original —
        <|"P", "Q", "D"|> canonical matrices; dims; key.
    Options/defaults: None.
    Returns: Bundle association, or Failure.
    Effects: Pure.
    Failures: splitExchangeCopies, normalizeCGCopies and validation failures.
    Example: finishCGBundle of generator-equation spaces gives the bundle computeCGBundle returns.
    See also: computeCGBundle; transportedCGBundle.
*)
(* The field forms are used only in this kernel's own domain of the inputs: a route computed in another kernel ships its
   field, which must be the one built here from the canonical matrices (memoized), or the stored values are checked
   (cgFactoredValidationPlan.md 7, review F1). *)
cgOwnFieldQ[request_Association, target_String, arithmetic_Association] := With[{own = cgFieldCatch[cgArithmetic[
        Append[request["Variants"][#]["Matrices"] & /@ request["Pair"], request["Variants"][target]["Matrices"]], request["Settings"]]]},
    AssociationQ[own] && own["Field"] =!= None && own["Field"] === arithmetic["Field"]];
finishCGBundle[request_Association, target_String, method_String, spaces_Association, arithmetic_Association, original_Association,
    dims_List, key_String] := Module[{sectors, channels, checked, forms, exact = request["Arithmetic"] === "Exact"},
    sectors = If[request["Exchange"], splitExchangeCopies[spaces, dims[[1]], arithmetic],
        {<|"Symmetry" -> "Unspecified", "Kets" -> spaces["Kets"], "Bras" -> spaces["Bras"]|>}];
    If[FailureQ[sectors], Return[sectors]];
    channels = Map[normalizeCGCopies[#, request["Normalization"], arithmetic, dims[[3]]] &, sectors];
    (* a failing sector is returned as such (a Failure is atomic, so it is looked for in the list of sector results) *)
    If[!FreeQ[channels, _Failure], Return[FirstCase[channels, _Failure, makeFailure["UnprovedIdentity", "The CG copies could not be normalized."], {1, Infinity}]]];
    channels = Join @@ channels;
    (* the private field forms of a fresh exact unitary normalization (cgFactoredValidationPlan.md 7) *)
    forms = Lookup[channels, "FieldForm", Missing[]];
    channels = KeyDrop[#, "FieldForm"] & /@ channels;
    (* Numerical channels at the working precision; entries below the precision become exact zeros, so an
       accuracy-only zero cannot lower the precision of a whole matrix. *)
    If[!exact, channels = Map[Join[#, <|"Embedding" -> toArithmetic[#["Embedding"], request["Settings"]],
        "Dual" -> toArithmetic[#["Dual"], request["Settings"]]|>] &, channels]];
    checked = cgVerifyBundle[channels, original["P"], original["Q"], original["D"], request["Normalization"], request["Settings"], request["Exchange"],
        True, If[exact && !MemberQ[forms, _Missing] && cgOwnFieldQ[request, target, arithmetic], <|"Forms" -> forms, "Arithmetic" -> arithmetic|>, None]];
    If[!checked["Passed"],
        Return[makeFailure["UnprovedIdentity", "The normalized CG bundle did not validate.", <|"Validation" -> checked["Validation"], "Method" -> method|>]]];
    Join[<|"Key" -> key, "TargetID" -> target, "Channels" -> MapIndexed[Join[<|"Copy" -> First[#2]|>, #1] &, channels],
        "Method" -> method, "Domain" -> domainSummary[arithmetic["Field"]]|>, KeyDrop[checked, "Passed"]]
];

(*
    Summary: Run a unitary-input route on verified temporary unitary forms and transport the maps back.
    Parameters: request; target; method; descriptor.
    Options/defaults: The temporary forms use UnitarizeRepresentation with the request's arithmetic, the call's
        UnitarizationMethod and its FieldMethod (methodOptionsPlan.md 2B.5).
    Returns: Bundle in the stored (general) bases, or Failure.
    Effects: Pure (no stored representation changes).
    Failures: MethodPrerequisiteFailed when a temporary unitarization fails (a nonunitary algebra is never
        symmetrized directly); the route's and reconstruction's failures; validation failures in the original bases.
    Example: CommutantSpectral on a sheared general-basis triplet returns kets that intertwine the stored matrices.
    Remarks: With B . M . B^-1 unitary (Stage 2 convention) for each input and the target, B_pq = B_p (x) B_q,
        K = B_pq^-1 K' B_t and W = B_t^-1 W' B_pq; exact requests reconstruct K', W' exactly before transport, and
        every check is redone in the original bases.
    See also: UnitarizeRepresentation; computeCGBundle.
*)
transportedCGBundle[request_Association, target_String, method_String, descriptor_Association] := Module[
    {ids = DeleteDuplicates[Append[request["Pair"], target]], forms, temporary, arithmetic, problem, spaces, original, dims, key, exact,
        bp, bq, bt, bpqInverse, btInverse, bpq, kets, bras, reduce},
    exact = request["Arithmetic"] === "Exact";
    key = cgCacheKey[request, target];
    forms = AssociationMap[Function[id, If[request["Variants"][id]["Unitary"],
            <|"Rep" -> request["Variants"][id]["Rep"], "BasisChange" -> IdentityMatrix[request["Variants"][id]["Dimension"]],
                "InverseBasisChange" -> IdentityMatrix[request["Variants"][id]["Dimension"]]|>,
            (* the call's unitarizer and exact domain (methodOptionsPlan.md 2B.5) *)
            UnitarizeRepresentation[request["Context"], request["Variants"][id]["Rep"], Arithmetic -> request["Arithmetic"],
                Sequence @@ inheritedVerification[Lookup[request["Options"], Verification, Automatic]],
                UnitarizationMethod -> Lookup[request["Options"], UnitarizationMethod, Automatic],
                FieldMethod -> If[request["Arithmetic"] === "Exact", Lookup[request["Settings"], "FieldMethod", Automatic], Automatic],
                Sequence @@ If[exact, {}, {WorkingPrecision -> request["Settings"]["Precision"]}]]]], ids];
    (* a domain failure stays a domain failure (not a prerequisite failure) *)
    If[AnyTrue[forms, cgFieldMethodUnavailableQ], Return[FirstCase[forms, f_ /; cgFieldMethodUnavailableQ[f]]]];
    If[AnyTrue[forms, FailureQ], Return[makeFailure["MethodPrerequisiteFailed", "A temporary unitary form for the spectral route failed.",
        <|"Method" -> method, "Cause" -> FirstCase[forms, _Failure]|>]]];
    temporary = request;
    Do[temporary["Variants", id] = Join[request["Variants"][id], <|"Matrices" -> repMatrices[forms[id]["Rep"]], "Unitary" -> True|>], {id, ids}];
    arithmetic = cgArithmetic[repMatrices[forms[#]["Rep"]] & /@ ids, request["Settings"]];
    problem = cgProblem[temporary, target, arithmetic];
    dims = problem["Dims"];
    spaces = descriptor["Route"][problem];
    If[FailureQ[spaces], Return[spaces]];
    If[exact,
        spaces = reconstructCG[spaces, problem["Original"]["P"], problem["Original"]["Q"], problem["Original"]["D"], dims,
            problem["Multiplicity"], $CGReconstructionDigits, request["Settings"]];
        If[FailureQ[spaces], Return[spaces]];
        spaces = <|"Kets" -> (spaces["Arithmetic"]["Back"] /@ spaces["Kets"]), "Bras" -> (spaces["Arithmetic"]["Back"] /@ spaces["Bras"])|>];
    {bp, bq, bt} = forms[#]["BasisChange"] & /@ Append[request["Pair"], target];
    bpqInverse = KroneckerProduct[forms[request["Pair"][[1]]]["InverseBasisChange"], forms[request["Pair"][[2]]]["InverseBasisChange"]];
    btInverse = forms[target]["InverseBasisChange"];
    bpq = KroneckerProduct[bp, bq];
    reduce = If[exact, Map[RootReduce, #, {2}] &, toArithmetic[#, request["Settings"]] &];
    kets = reduce[bpqInverse . # . bt] & /@ spaces["Kets"];
    bras = reduce[btInverse . # . bpq] & /@ spaces["Bras"];
    original = <|"P" -> request["Variants"][request["Pair"][[1]]]["Matrices"], "Q" -> request["Variants"][request["Pair"][[2]]]["Matrices"],
        "D" -> request["Variants"][target]["Matrices"]|>;
    arithmetic = cgArithmetic[{original["P"], original["Q"], original["D"], kets, bras}, request["Settings"]];
    finishCGBundle[request, target, method <> " (temporary unitary transport)", <|"Kets" -> (arithmetic["Embed"] /@ kets),
        "Bras" -> (arithmetic["Embed"] /@ bras)|>, arithmetic, original, dims, key]
];

(*
    Summary: Job descriptors of the CG methods for one target, with applicability decided up front.
    Parameters: request; target; methods — ordered method names.
    Options/defaults: Method -> Automatic adds two rules (user decision 2026-10-06, cgParallelPlan.md §3.1): a
        unitary-input method (CommutantSpectral, AdaptedStates) applies only when the pair and the target are stored
        unitary (no temporary unitary transport), and SubgroupEmbedding only with subgroup information (MethodData,
        or a recorded proper subgroup with generator words; no cyclic or identity fallback). An explicit method keeps
        its own route, transport and fallbacks.
    Returns: List of job descriptors (JobScheduling.wl contract) with Operation "CG", the method, one core, a memory
        estimate, Availability "Eligible" or "Inapplicable" with a reason, and Tier 0 for Wolfram methods and 1 for
        native GAP methods (so the Wolfram methods form the first batches; packJobBatches orders by Tier).
    Effects: Pure.
    Failures: None.
    Example: in numerical arithmetic "AveragedOrbit" and the native routes are Inapplicable.
    Remarks: Memory estimates: N dt unknowns squared for equation routes (16 bytes per entry), plus |G| (dp^2 + dq^2 + dt^2)
        for routes that enumerate the image group, plus (N dt)^2 for chain operators; 32 MiB minimum.
    See also: planCGAttempts; packJobBatches; cgSubgroupInformationQ.
*)
cgAttemptDescriptors[request_Association, target_String, methods_List] := Module[{descriptors = cgMethodDescriptors[], dims, n, dt, order, exact,
        fullPair, automatic, unitary},
    exact = request["Arithmetic"] === "Exact";
    automatic = request["Options"][Method] === Automatic;
    dims = request["Variants"][#]["Dimension"] & /@ Append[request["Pair"], target];
    n = dims[[1]] dims[[2]]; dt = dims[[3]]; order = request["Snapshot"]["Order"];
    fullPair = SubsetQ[request["Targets"], request["AllTargets"]];
    unitary = AllTrue[request["Variants"] /@ Append[request["Pair"], target], #["Unitary"] &];
    Map[Function[method, Module[{d = descriptors[method], reason = None, memory},
            reason = Which[
                exact && d["Exact"] === "None", "The method has no exact form.",
                !exact && !d["Numerical"] && (d["Kind"] === "Native" || AnyTrue[request["Variants"] /@ Append[request["Pair"], target], #["Tier"] === "Numerical" &]),
                    "The method needs exact matrices or an exact witness.",
                MemberQ[{"Serre", "SerreBSGS"}, method] && !fullPair, "The native full decomposition serves complete pair requests only.",
                automatic && TrueQ[d["UnitaryInputs"]] && !unitary,
                    "Under Method -> Automatic the method needs unitary stored matrices (no temporary unitary transport).",
                automatic && method === "SubgroupEmbedding" && !cgSubgroupInformationQ[request],
                    "Under Method -> Automatic the method needs recorded subgroup information.",
                True, None];
            memory = Max[32 2^20, 16 (n dt)^2 + If[TrueQ[d["Elements"]], 16 order (dims[[1]]^2 + dims[[2]]^2 + dt^2), 0] +
                If[MemberQ[{"SubgroupChain", "AveragedBSGS"}, method], 16 (n dt)^2, 0]];
            <|"Operation" -> "CG", "Method" -> method, "Model" -> "Original", "RecoveryStrategy" -> "None",
                "WorkKey" -> "CG/" <> method <> "/" <> target, "Tier" -> If[d["Kind"] === "Native", 1, 0], "Parallel" -> False, "MinCores" -> 1,
                "MemoryEstimate" -> memory, "Availability" -> If[reason === None, "Eligible", "Inapplicable"], "Reason" -> reason|>]],
        methods]
];

(*
    Summary: Whether a CG request carries subgroup information for SubgroupEmbedding.
    Parameters: request.
    Options/defaults: None.
    Returns: True when MethodData names subgroup generators or a subgroup record, or the snapshot records a proper
        subgroup (1 < order < |G|) with generator words; otherwise False.
    Effects: Pure.
    Failures: None.
    Example: a group built with ComputeSubgroups -> True and order > 1 gives True.
    See also: cgAttemptDescriptors; cgSubgroupWords.
*)
cgSubgroupInformationQ[request_Association] := Module[{data = request["Options"][MethodData], snapshot = request["Snapshot"]},
    TrueQ[AssociationQ[data] && (KeyExistsQ[data, "SubgroupGenerators"] || KeyExistsQ[data, "SubgroupRecord"])] ||
        TrueQ[AssociationQ[Lookup[snapshot, "SubgroupData", Missing[]]] &&
            AnyTrue[Flatten[Lookup[Values[snapshot["SubgroupData"]], "Subgroups", {}]],
                AssociationQ[#] && IntegerQ[Lookup[#, "Order", None]] && 1 < #["Order"] < snapshot["Order"] && ListQ[Lookup[#, "GeneratorWords", None]] &]]
];

(*
    Summary: The attempt plan of one target under the common batch policy.
    Parameters: request; target.
    Options/defaults: Method Automatic uses $CGMethodOrder, an explicit method only itself; CoreBudget and MemoryBudget
        from the request's options.
    Returns: packJobBatches result (Batches, Skipped, CoreBudget, MemoryBudget), or Failure.
    Effects: Pure.
    Failures: InvalidMethodPlan.
    Example: with CoreBudget 8 the eligible Automatic Wolfram methods form a batch of eight; the native methods
        (Tier 1) follow in their own batch.
    Remarks: Below four cores every batch has one attempt; at four or more, batches of four (or multiples) are
        formed in the documented order, Wolfram methods (Tier 0) before native GAP methods (Tier 1).
    See also: cgAttemptDescriptors; cgBundleByMethod.
*)
planCGAttempts[request_Association, target_String] := With[{method = request["Options"][Method]},
    If[ListQ[method],
        (* an ordered list (2A.3): one attempt per batch, in the given order, in this kernel (all tier 0, one core) *)
        packJobBatches[Map[Join[#, <|"Tier" -> 0|>] &, cgAttemptDescriptors[request, target, method]],
            Join[KeyTake[request["Options"], {MemoryBudget}], <|CoreBudget -> 1|>]],
        packJobBatches[cgAttemptDescriptors[request, target, If[method === Automatic, $CGMethodOrder, {method}]],
            KeyTake[request["Options"], {CoreBudget, MemoryBudget}]]]];

(*
    Summary: Compute one target's bundle by an explicit method or the Automatic order.
    Parameters: request; target.
    Options/defaults: Method Automatic tries $CGMethodOrder (skipping inapplicable methods) within
        AttemptTimeLimit seconds per attempt; an explicit method is the only top-level route.
    Returns: Bundle (computeCGBundle) with "Attempts" -> outcomes (each with "Execution" -> "Race", "InKernel" or
        "SequentialFallback"), or Failure with the attempts.
    Effects: Pure (no publication); under Automatic may launch the session pool of race subkernels (CGRace.wl).
    Failures: MethodExhausted with every attempt's outcome; the explicit method's failure.
    Example: an explicit "AveragedOrbit" in numerical arithmetic fails with MethodInapplicable.
    Remarks: Under Automatic a batch with two or more Wolfram members races them in the pool (cgRaceBatch: the
        first bundle validated in this kernel wins, rivals are aborted); when the pool is unavailable the batch runs
        here in order and its outcomes say SequentialFallback with the reason. Native (Tier 1) batches and one-member
        batches run here in order, as do explicit methods (cgParallelPlan.md; step4Status.md D-S4-5).
    See also: computeCGBundle; cgRaceBatch; acceptCGBundles.
*)
cgBundleByMethod[request_Association, target_String] := Module[{plan, outcomes = {}, result = None, limit, explicit, kinds, ordered},
    (* a single explicit method stops at its own failure; an ordered list tries the next member (2A.3) *)
    ordered = ListQ[request["Options"][Method]];
    explicit = StringQ[request["Options"][Method]];
    plan = planCGAttempts[request, target];
    If[FailureQ[plan], Return[plan]];
    outcomes = Map[<|"Method" -> #["Descriptor"]["Method"], "Outcome" -> #["Reason"], "Details" -> Lookup[#, "Details", None]|> &, plan["Skipped"]];
    If[explicit && plan["Batches"] === {},
        Return[makeFailure["MethodInapplicable", "The requested CG method does not apply to this request.",
            <|"Method" -> request["Options"][Method], "Attempts" -> outcomes, "TargetID" -> target|>]]];
    limit = request["Options"][AttemptTimeLimit];
    kinds = Map[#["Kind"] &, cgMethodDescriptors[]];
    Do[Module[{race = None, execution = "InKernel", fallback = None},
            If[!explicit && !ordered && Count[batch["Attempts"], a_ /; kinds[a["Method"]] === "Wolfram"] >= 2 &&
                    AllTrue[batch["Attempts"], kinds[#["Method"]] === "Wolfram" &],
                race = cgRaceBatch[request, target, batch["Attempts"], limit];
                If[FailureQ[race], execution = "SequentialFallback"; fallback = Lookup[Last[race], "MessageTemplate", None]; race = None]];
            If[AssociationQ[race],
                outcomes = Join[outcomes, race["Outcomes"]];
                If[AssociationQ[race["Bundle"]], result = race["Bundle"]],
                Do[With[{method = attempt["Method"]}, With[{computed = TimeConstrained[computeCGBundle[request, target, method], limit,
                                makeFailure["Timeout", "The CG attempt exceeded AttemptTimeLimit.", <|"Method" -> method|>]]},
                        AppendTo[outcomes, Join[<|"Method" -> method, "Outcome" -> If[FailureQ[computed], First[computed], "Accepted"], "Execution" -> execution|>,
                            If[fallback === None, <||>, <|"Details" -> fallback|>]]];
                        If[!FailureQ[computed], result = computed; Break[]];
                        If[explicit, result = computed; Break[]]]],
                    {attempt, batch["Attempts"]}]]];
        If[result =!= None, Break[]],
        {batch, plan["Batches"]}];
    (* the domain can differ between methods (normalization roots, transported forms), so under Automatic every method is
       tried; when none produced a bundle and some failed for want of a domain, that is the reported failure *)
    If[result === None && MemberQ[Lookup[outcomes, "Outcome", None], "FieldMethodUnavailable"],
        result = makeFailure["FieldMethodUnavailable", "No domain of the requested FieldMethod applies to this target's values.",
            <|"FieldMethod" -> request["Settings"]["FieldMethod"], "TargetID" -> target|>]];
    (* an ordered list reports its members in the requested order (skipped members included) *)
    If[ordered, outcomes = SortBy[outcomes, FirstPosition[request["Options"][Method], #["Method"], {Infinity}] &]];
    Which[
        AssociationQ[result], Append[result, "Attempts" -> outcomes],
        FailureQ[result], Failure[First[result], Join[Last[result], <|"Attempts" -> outcomes|>]],
        True, makeFailure["MethodExhausted", If[ordered, "No method of the requested list produced a validated bundle.",
            "No CG method produced a validated bundle."], <|"Attempts" -> outcomes, "TargetID" -> target|>]]
];

(*
    Summary: Assemble an immutable CGData snapshot from resolved bundles.
    Parameters: request; bundles — target ID -> bundle; hits — target IDs served from the store.
    Options/defaults: None.
    Returns: CGData[association].
    Effects: Pure.
    Failures: None.
    Example: CGIntertwiners[makeCGData[...], t] lists t's channels.
    Remarks: Fields: SchemaVersion, Context (group identity, generator identity, state generation, context
        digest), CharacterIdentity, InputIDs, InputIdentities, InputReps, TargetIDs, TargetIdentities,
        TargetReps, Normalization, ExchangeSymmetry, Arithmetic, Multiplicities, Coverage (Selected,
        FullPair, Complete), Channels (target ID order, sectors symmetric first, copies), Provenance.
        Channel IDs are "cg:<first 16 hex of the bundle key>:<copy>". The reps are the frozen participating values,
        so ValidateCG needs no group.
    See also: CGIntertwiners; CGMatrix; ValidateCG.
*)
makeCGData[request_Association, bundles_Association, hits_List] := Module[{snapshot = request["Snapshot"], targets = request["Targets"], channels},
    (* an unstored recomputation (Recompute -> True over a stored entry) gets channel IDs of its own, so its channels are
       never confused with the stored entry's *)
    channels = Flatten[Map[Function[t, Map[Join[<|"ChannelID" -> "cg:" <> StringTake[bundles[t]["Key"], 16] <> ":" <> ToString[#["Copy"]] <>
                If[TrueQ[Lookup[bundles[t], "Unstored", False]], ":r" <> StringTake[Hash[bundles[t]["Channels"], "SHA256", "HexString"], 8], ""],
            "TargetID" -> t, "TargetBasisID" -> request["Variants"][t]["Identity"]|>, KeyTake[#, {"Copy", "Symmetry", "Embedding", "Dual"}]] &,
            bundles[t]["Channels"]]], targets], 1];
    CGData[<|"SchemaVersion" -> 1,
        "Context" -> <|"GroupIdentity" -> Lookup[snapshot, "StateID", Lookup[snapshot, "GroupIdentity", Missing[]]],
            "GeneratorIdentity" -> snapshot["GeneratorIdentity"], "StateGeneration" -> snapshot["StateGeneration"],
            "GeneratorNames" -> If[KeyExistsQ[snapshot, "GeneratorNames"], snapshot["GeneratorNames"], Lookup[snapshot["Generators"], "Name", {}]]|>,
        "CharacterIdentity" -> request["Characters"]["Identity"], "InputIDs" -> request["Pair"],
        "InputIdentities" -> (request["Variants"][#]["Identity"] & /@ request["Pair"]),
        "InputReps" -> (request["Variants"][#]["Rep"] & /@ request["Pair"]),
        "TargetIDs" -> targets,
        "TargetIdentities" -> AssociationMap[If[request["Multiplicities"][#] > 0, request["Variants"][#]["Identity"], Missing["ZeroMultiplicity"]] &, targets],
        "TargetReps" -> AssociationMap[If[request["Multiplicities"][#] > 0, request["Variants"][#]["Rep"], Missing["ZeroMultiplicity"]] &, targets],
        "Normalization" -> request["Normalization"], "ExchangeSymmetry" -> request["SymmetryMode"], "Arithmetic" -> request["Arithmetic"],
        "Multiplicities" -> KeyTake[request["Multiplicities"], targets],
        "Coverage" -> <|"Selected" -> targets, "FullPair" -> SubsetQ[targets, request["AllTargets"]],
            "Complete" -> AllTrue[targets, Length[bundles[#]["Channels"]] === request["Multiplicities"][#] &]|>,
        "Channels" -> channels,
        "Provenance" -> AssociationMap[<|"Method" -> bundles[#]["Method"], "CacheHit" -> MemberQ[hits, #],
            "Recomputed" -> TrueQ[Lookup[bundles[#], "Unstored", False]],
            "Domain" -> Lookup[bundles[#], "Domain", Missing["NotRecorded"]],
            "ValidationDomain" -> Lookup[bundles[#], "ValidationDomain", Missing["NotRecorded"]],
            (* served status: the weakest of the entry's own check, the participating variants and the group
               (methodOptionsPlan.md 2C.2); computed here, never stored, so a later upgrade of an input is seen *)
            "Verification" -> cgServedStatus[request, #, bundles[#]], "CheckStatus" -> cgEntryStatus[bundles[#]]|> &, targets],
        "VerificationStatus" -> cgWeakestStatus[cgServedStatus[request, #, bundles[#]] & /@ targets]|>]
];

(* The weaker-input rule (methodOptionsPlan.md 2C, rule for 2C-ii): a call whose level asks for more than its input
   variants and group are verified at serves its result at their status, and says so once. Returns {} or {note}. *)
cgWeakInputsNote[request_Association] := Module[{sources, inputs, required, weak},
    (* the records the result depends on: the group, the factors and the targets of positive multiplicity *)
    sources = Join[{"the group" -> groupVerificationStatus[request["Snapshot"]]},
        Map[("the representation of " <> # -> variantVerificationStatus[Lookup[request["Variants"], #, Missing[]]]) &,
            DeleteDuplicates[Join[request["Pair"], Select[request["Targets"], request["Multiplicities"][#] > 0 &]]]]];
    inputs = cgWeakestStatus[Values[sources]];
    required = cgRequiredStatus[Lookup[request["Settings"], "Verification", Automatic], request["Arithmetic"]];
    weak = Keys[Select[Association[sources], cgStatusRank[#] < cgStatusRank[required] &]];
    If[cgStatusRank[inputs] < cgStatusRank[required],
        {"the CG result of " <> StringRiffle[request["Pair"], " x "] <> " depends on " <> StringRiffle[weak, ", "] <>
            ", verified only at \"" <> inputs <> "\"; it is served at that status"}, {}]];

(* The status a CG target is served at: its own check, its input and target variants, the group. *)
cgServedStatus[request_Association, target_String, bundle_Association] := cgWeakestStatus[Join[{cgEntryStatus[bundle],
        groupVerificationStatus[request["Snapshot"]]},
    variantVerificationStatus /@ Lookup[request["Variants"], DeleteDuplicates[If[request["Multiplicities"][target] > 0, Append[request["Pair"], target], request["Pair"]]], Missing[]]]];

(* Summaries instead of the embedded matrices and frozen representations. *)
Format[CGData[data_Association], StandardForm] := Interpretation[Row[{"CGData[",
    Short[Map[irrepPlainName[Lookup[Lookup[data, "Context", <||>], "GroupIdentity", ""], #] &, Lookup[data, "InputIDs", {}]], 1], " \[Rule] ",
    Length[Lookup[data, "TargetIDs", {}]], " targets, ", Length[Lookup[data, "Channels", {}]], " channels, ", Lookup[data, "Normalization", "?"], "]"}],
    CGData[data]];

(*
    Summary: Validate the schema of a CGData snapshot before an accessor uses it.
    Parameters: data — the association inside CGData.
    Options/defaults: None.
    Returns: True, or InvalidCGData Failure.
    Effects: Pure.
    Failures: Missing fields, channel shapes that disagree with the input and target dimensions, channels of
        unselected targets, copy counts that disagree with the multiplicities.
    Example: a CGData whose Embedding was replaced by a matrix of the wrong shape fails here.
    Remarks: Shape and consistency only; mathematical validity is ValidateCG's (a stored validation label is
        never evidence).
    See also: CGIntertwiners; CGMatrix; ValidateCG.
*)
validateCGSchema[data_Association] := Module[{fields, n, dims},
    fields = {"SchemaVersion", "Context", "CharacterIdentity", "InputIDs", "InputIdentities", "InputReps", "TargetIDs",
        "TargetIdentities", "TargetReps", "Normalization", "ExchangeSymmetry", "Arithmetic", "Multiplicities", "Coverage",
        "Channels", "Provenance"};
    If[!SubsetQ[Keys[data], fields] || data["SchemaVersion"] =!= 1 || !MatchQ[data["InputReps"], {_Rep, _Rep}] ||
        !ListQ[data["Channels"]] || !AssociationQ[data["Multiplicities"]],
        Return[makeFailure["InvalidCGData", "Malformed CGData snapshot."]]];
    n = Times @@ (RepDim /@ data["InputReps"]);
    If[!AllTrue[data["Channels"], Function[c, AssociationQ[c] && SubsetQ[Keys[c], {"ChannelID", "TargetID", "Copy", "Symmetry", "Embedding", "Dual"}] &&
            MemberQ[data["TargetIDs"], c["TargetID"]] && MatchQ[data["TargetReps"][c["TargetID"]], _Rep] &&
            With[{dt = RepDim[data["TargetReps"][c["TargetID"]]]}, Dimensions[c["Embedding"]] === {n, dt} && Dimensions[c["Dual"]] === {dt, n}]]] ||
        !AllTrue[data["TargetIDs"], Count[data["Channels"], KeyValuePattern["TargetID" -> #]] === data["Multiplicities"][#] &],
        Return[makeFailure["InvalidCGData", "CGData channels disagree with the inputs, targets or multiplicities."]]];
    True
];
validateCGSchema[___] := makeFailure["InvalidCGData", "Expected a CGData snapshot."];

(*
    Summary: The channel records of one target.
    Parameters: data — CGData; target — irrep ID.
    Options/defaults: None.
    Returns: List of channel associations (ChannelID, TargetID, Copy, Symmetry, Embedding, Dual, TargetBasisID), the
        Embedding and Dual matrices in readable form (readableMatrix: radicals, roots of unity; the stored canonical
        forms stay in the CGData and are what internal code uses, cgTargetChannels); {} for a selected target of
        multiplicity zero; Missing["NotSelected"] for a target outside the selection.
    Effects: Pure.
    Failures: InvalidCGData.
    Example: Length[CGIntertwiners[cg, t]] is 2 for A4 3 (x) 3 and the triplet.
    See also: CGMatrix; CGCoefficients.
*)
CGIntertwiners[CGData[data_Association], target_String] := With[{channels = cgTargetChannels[data, target]},
    If[ListQ[channels], Map[Join[#, <|"Embedding" -> readableMatrix[#["Embedding"]], "Dual" -> readableMatrix[#["Dual"]]|>] &, channels], channels]];
cgTargetChannels[data_Association, target_String] := Module[{check = validateCGSchema[data]},
    Which[FailureQ[check], check, !MemberQ[data["TargetIDs"], target], Missing["NotSelected"],
        True, Select[data["Channels"], #["TargetID"] === target &]]];
CGIntertwiners[cg : CGData[data_Association], k_Integer] := With[{order = cgIrrepOrder[data]}, Which[
    FailureQ[order], order,
    1 <= k <= Length[order], CGIntertwiners[cg, order[[k]]],
    True, makeFailure["InvalidIrrep", "The irrep index " <> ToString[k] <> " is out of range 1.." <> ToString[Length[order]] <> "."]]];
CGIntertwiners[___] := makeFailure["InvalidInput", "CGIntertwiners expects CGData and a target irrep ID."];

(*
    Summary: The assembled embedding (side by side) or dual (stacked) matrix of a CGData snapshot.
    Parameters: data — CGData; side — "Embedding" (default) or "Dual".
    Options/defaults: side "Embedding".
    Returns: Matrix in readable form (readableMatrix); {} for an empty selection; or Failure.
    Effects: Pure.
    Failures: InvalidCGData; InvalidInput for another side.
    Example: for a full pair the embedding is square and the dual is its inverse.
    Remarks: A selected-target matrix is rectangular; it is not claimed to be invertible.
    See also: CGIntertwiners; assembleCG.
*)
CGMatrix[CGData[data_Association], side_String : "Embedding"] := Module[{check = validateCGSchema[data]},
    Which[FailureQ[check], check, !MemberQ[{"Embedding", "Dual"}, side], makeFailure["InvalidInput", "The side must be \"Embedding\" or \"Dual\"."],
        True, readableMatrix[assembleCG[{data["Channels"]}, side]]]];
CGMatrix[___] := makeFailure["InvalidInput", "CGMatrix expects CGData and \"Embedding\" or \"Dual\"."];

(*
    Summary: Recompute the validation of a CGData snapshot from its frozen matrices.
    Parameters: data — CGData.
    Options/defaults: FieldMethod (session default) — the exact domain of the checks; Verification Automatic (exact
        checks of exact data, numerical of numerical), "Exact" or "Numerical" (checks on N[] of every matrix at
        WorkingPrecision, default 50); the session's Verification does not apply (ValidateCG is the check itself).
    Returns: <|"Valid" -> Boolean, "Targets" -> target ID -> validateCGBundle checks, "FullInverse" -> Boolean or
        Missing (full-pair data: the assembled matrices are mutually inverse), "VerificationStatus" -> the level the
        checks establish|>, or Failure.
    Effects: Pure (no status is written back in Phase 1).
    Failures: InvalidCGData; InvalidOption (Verification -> None); InapplicableOption (Verification -> "Exact" on
        numerical data); FieldMethodUnavailable.
    Example: ValidateCG[cg]["Valid"] is True for coefficients returned by CGCoefficients.
    Remarks: Covariance and dual covariance on every recorded generator, pairing, rank, exchange symmetry and
        (Unitary) W = K^dagger are recomputed; nothing stored in the snapshot is trusted.
    See also: validateCGBundle; CGCoefficients.
*)
Options[ValidateCG] = {FieldMethod :> $Configuration[FieldMethod], Verification -> Automatic, WorkingPrecision -> 50};
ValidateCG[CGData[data_Association], options : OptionsPattern[]] := cgFieldCatch[Module[{check = validateCGSchema[data], effective, settings, level,
        numerical, p, q, results, checks, full},
    If[FailureQ[check], Return[check, Module]];
    effective = resolveOperationOptions[ValidateCG, "ValidateCG", {options}];
    If[FailureQ[effective], Return[effective, Module]];
    level = effective[Verification];
    If[level === None, Return[makeFailure["InvalidOption", "ValidateCG checks: Verification is Automatic, \"Exact\" or \"Numerical\".",
        <|"Options" -> {Verification}|>], Module]];
    If[level === "Exact" && data["Arithmetic"] =!= "Exact", Return[makeFailure["InapplicableOption",
        "Verification -> \"Exact\" cannot prove numerical CG coefficients; use Automatic or \"Numerical\".", <|"Options" -> {Verification}|>], Module]];
    settings = cgCheckSettings[If[data["Arithmetic"] === "Exact", arithmeticSettings["Exact", 50, Automatic, Infinity],
        (* The working precision of the stored numerical channels (exact zeros carry no precision). *)
        With[{precision = Min[Append[Precision /@ Select[Flatten[Join[Lookup[data["Channels"], "Embedding", {}], Lookup[data["Channels"], "Dual", {}]]],
                !MatchQ[#, _Integer | _Rational] &], MachinePrecision] /. MachinePrecision -> 16]},
            arithmeticSettings["Numerical", Max[16, Floor[precision]], Automatic, Max[16, Floor[precision]]]]],
        <|"FieldMethod" -> effective[FieldMethod], "Verification" -> level, "CheckPrecision" -> effective[WorkingPrecision]|>];
    numerical = level === "Numerical" && data["Arithmetic"] === "Exact";
    {p, q} = repMatrices /@ data["InputReps"];
    checks = AssociationMap[Function[t, If[data["Multiplicities"][t] === 0, <|"Validation" -> <|"Empty" -> True|>, "VerificationStatus" -> "Exact"|>,
        cgVerifyBundle[Select[data["Channels"], #["TargetID"] === t &], p, q, repMatrices[data["TargetReps"][t]],
            data["Normalization"], settings, data["ExchangeSymmetry"] === "Separate", False]]], data["TargetIDs"]];
    results = #["Validation"] & /@ checks;
    full = If[TrueQ[data["Coverage"]["FullPair"]] && data["Channels"] =!= {},
        With[{k = assembleCG[{data["Channels"]}, "Embedding"], w = assembleCG[{data["Channels"]}, "Dual"]},
            If[numerical,
                With[{digits = Max[16, effective[WorkingPrecision]]},
                    checkMatrixIdentity[N[w, digits] . N[k, digits], IdentityMatrix[Length[k]], arithmeticSettings["Numerical", digits, Automatic, Infinity]]["Holds"]],
                checkMatrixIdentity[w . k, IdentityMatrix[Length[k]], settings]["Holds"]]], Missing["Selected"]];
    <|"Valid" -> AllTrue[Values[results], AllTrue[KeyDrop[#, {"Residual", "Unitary", "Empty"}], TrueQ] &&
            (data["Normalization"] =!= "Unitary" || MissingQ[Lookup[#, "Unitary", Missing[]]] || TrueQ[#["Unitary"]]) &] && !TrueQ[full === False],
        "Targets" -> results, "FullInverse" -> full,
        (* bounded by the data's own status (its input and target variants and the group), as every Validate report is *)
        "VerificationStatus" -> cgWeakestStatus[Append[Values[#["VerificationStatus"] & /@ checks], Lookup[data, "VerificationStatus", "Exact"]]]|>
]];
ValidateCG[___] := makeFailure["InvalidInput", "ValidateCG expects CGData."];

True
