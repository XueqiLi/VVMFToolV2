(*
    :Title: Representation computation jobs
    :Context: VVMFTool`Private`
    :Summary: Register the GAP Representations operation with its request-aware coordinator rules.
    :Responsibilities: Completion of a representation request, retry rule after partial success,
        the native method vocabulary, unitary-first descriptor planning and the coordinator that
        publishes every verified partial as its own group generation.
    :Dependencies: GAPOperations.wl; RepresentationStorage.wl decoded Representations; JobScheduling.wl;
        GAPJobs.wl; GroupEnrichment.wl (source and publication).
    :See Also: GAP/Representations.g; VVMFArch/step2Plan.md (scheduling); step2Status.md.
*)

(* Native construction routes installed in GAP/Representations.g, in the plan's order within
   each phase. The descriptor planner (S2.3) orders them into unitary-first phases. *)
$RepresentationMethods = {"SL2Reps", "LinearCharacter", "DixonUnitary", "BaumClausen", "InducedUnitary",
    "Dixon", "REPSN", "CharacterSubgroup", "Induction", "Extension", "NormalExtension", "AtlasRep", "GAP"};

(*
    Summary: Decide whether a verified candidate satisfies a representation request.
    Parameters: data — decoded verified result (with its ModularAssignment and Generators); request —
        Representations request whose "representationRequest" holds "irrepIDs" (strings), "basis"
        ("General", "Unitary" or "UnitaryTDiagonal") and, for "UnitaryTDiagonal", optional "phaseOrder"
        ("Ascending" | "Unchanged") and "phaseConvention" ("None" | "FirstSRow").
    Options/defaults: A missing phaseOrder/phaseConvention imposes no order/convention.
    Returns: True only when every requested irrep has an active variant, exactly verified unless the request's "verify"
        is "Traces" (C8), that is unitary for a unitary
        basis, and unitary with diagonal T for "UnitaryTDiagonal" whose T phases are in the requested order
        and whose S matrix satisfies the requested phase convention (tConventionQ).
    Effects: Pure.
    Failures: Malformed requests or data return False.
    Example: a candidate with a general active variant does not complete a unitary request, so it
        is kept as a Partial and cannot stop a unitary rival (D1).
    See also: operationCompleteQ; runJobBatch; decodeRepresentationData.
*)
representationRequestCompleteQ[data_Association, request_Association] := Module[{spec, representations},
    spec = Lookup[request, "representationRequest", None];
    representations = Lookup[data, "Representations", None];
    If[Lookup[data, "Status", None] =!= "Complete" || !AssociationQ[spec] || !AssociationQ[representations] ||
        !ListQ[Lookup[spec, "irrepIDs", None]] || !MemberQ[{"Unitary", "General", "UnitaryTDiagonal"}, Lookup[spec, "basis", None]],
        Return[False]];
    (* The same ranks as GAP's VVMF_RepSatisfied: a numerical active variant (rank -1) meets no request. The
       requested T-phase order and convention are decided here (GAP cannot order real cyclotomics). *)
    AllTrue[spec["irrepIDs"], Function[id, Module[{entry = Lookup[representations, id, None], active},
        active = If[AssociationQ[entry], entry["ActiveVariant"], Missing["NotComputed"]];
        StringQ[active] && representationBasisRank[entry["Variants"][active], Lookup[spec, "verify", "Full"] === "Traces"] >=
            Switch[spec["basis"], "General", 0, "Unitary", 1, _, 2] &&
            (* C8 (methodOptionsPlan.md 2C): a weak active variant meets only a request at its level; a "Traces" request
               (Verification "Numerical" or None) is met by any status *)
            (Lookup[spec, "verify", "Full"] === "Traces" || variantVerificationStatus[entry["Variants"][active]] === "Exact") &&
            (spec["basis"] =!= "UnitaryTDiagonal" || tConventionQ[entry["Variants"][active], Lookup[data, "ModularAssignment", None],
                Lookup[Lookup[data, "Generators", {}], "Name", {}], Lookup[spec, "phaseOrder", "Unchanged"],
                Lookup[spec, "phaseConvention", "None"]])]]]
];

(*
    Summary: Decide whether a T-diagonal variant has its T phases in the requested order and the requested
        S phase convention.
    Parameters: variant — decoded variant; assignment — modular assignment (S and T words); names — generator
        names; order — "Ascending" or "Unchanged"; convention — "None" or "FirstSRow".
    Options/defaults: Numerical variants are compared within 10^(-Floor[p/2]) at their precision p.
    Returns: Boolean.
    Effects: Pure.
    Failures: None (False when a phase cannot be certified).
    Example: a diagonal T with phases {2/3, 0} is not "Ascending".
    Remarks: Phases k/n in [0, 1) of the diagonal of T (evaluated on the native matrices of a scaled variant,
        whose diagonal the scaling does not change) are certified exactly (Exp[2 Pi I k/n] equals the entry);
        "Ascending" means nondecreasing, as the T diagonalizations order them. "FirstSRow" means every
        off-diagonal entry of the first row of S is real and nonnegative.
    See also: representationRequestCompleteQ; firstSRowPhases; orderTPhases.
*)
tConventionQ[variant_Association, assignment_, names_List, order_String, convention_String] := Module[
    {numerical, precision, tolerance, native, t, phases, s, row},
    If[order =!= "Ascending" && convention =!= "FirstSRow", Return[True]];
    If[!AssociationQ[assignment] || names === {}, Return[names === {}]];
    numerical = Lookup[variant, "Arithmetic", "Exact"] === "Numerical";
    native = If[MissingQ[Lookup[variant, "NativeMatrices", Missing[]]], repMatrices[variant["Rep"]], variant["NativeMatrices"]];
    t = wordMatrix[Rep[native], assignment["T"], names];
    If[!MatrixQ[t], Return[False]];
    precision = If[numerical, Precision[t] /. MachinePrecision -> 16, Infinity];
    tolerance = If[numerical, 10^(-Floor[precision/2]), 0];
    phases = certifiedRootOfUnityPhase /@ Diagonal[t];
    If[MemberQ[phases, $Failed], Return[False]];
    If[order === "Ascending" && !AllTrue[Differences[phases], # >= -tolerance &], Return[False]];
    If[convention === "FirstSRow",
        s = wordMatrix[variant["Rep"], assignment["S"], names];
        If[!MatrixQ[s], Return[False]];
        row = Rest[First[s]];
        If[!AllTrue[row, Function[z, If[numerical, Abs[Im[z]] <= tolerance && Re[z] >= -tolerance,
            With[{x = RootReduce[z]}, x === 0 || (RootReduce[x - Conjugate[x]] === 0 && N[x, 30] > 0)]]]], Return[False]]];
    True
];
tConventionQ[___] := False;
representationRequestCompleteQ[___] := False;

(*
    Summary: Decide whether a representation method need not be retried after an earlier outcome.
    Parameters: result — earlier outcome Result: "Complete", "Partial" or a Failure.
    Options/defaults: None.
    Returns: True for Complete and for inapplicable/unavailable routes; False otherwise.
    Effects: Pure.
    Failures: None.
    Example: representationRecoverySkipQ["Partial"] is False: a method that verified some irreps
        reruns on the remaining IDs (D4).
    See also: operationRecoverySkipQ; reduceRecoveryBatch.
*)
representationRecoverySkipQ[result_] := result === "Complete" ||
    MatchQ[result, Failure["InapplicableMethod" | "InapplicableModel" | "DependencyUnavailable", _]];

(*
    Summary: Check that new representation data only extend accepted representation data.
    Parameters: new, old — decoded Representations of the candidate and the accepted group; replaceable —
        irrep IDs whose active variant an explicit mutation may replace by any stored variant.
    Options/defaults: replaceable {}.
    Returns: Boolean.
    Effects: Pure.
    Failures: None; malformed input returns False.
    Example: adding a variant or an irrep extends; dropping a variant or changing its matrices does not.
    Remarks: Accepted variants never disappear or change; an active variant changes only to one of
        higher basis rank (general < unitary < unitary with diagonal T: strengthening), except for the
        irreps an explicit mutation names (SetGroupRepresentation, ChangeGroupRepBasis,
        TransformGroupRepresentations). Basis properties
        may be recomputed, for example after a new modular assignment, and are not compared.
    See also: publishGroupEnrichment; subgroupDataExtendsQ; step2Status.md state rules.
*)
representationDataExtendsQ[new_Association, old_Association, replaceable_List : {}] := AllTrue[Keys[old], Function[id,
    Module[{before = old[id], after = Lookup[new, id, None]},
        AssociationQ[after] && AllTrue[Keys[before["Variants"]], Function[variant,
            KeyExistsQ[after["Variants"], variant] &&
                KeyTake[after["Variants"][variant], {"Rep", "Identity"}] ===
                    KeyTake[before["Variants"][variant], {"Rep", "Identity"}]]] &&
            (MissingQ[before["ActiveVariant"]] || after["ActiveVariant"] === before["ActiveVariant"] ||
                (MemberQ[replaceable, id] && StringQ[after["ActiveVariant"]]) ||
                (StringQ[after["ActiveVariant"]] &&
                    representationBasisRank[after["Variants"][after["ActiveVariant"]]] >
                        representationBasisRank[after["Variants"][before["ActiveVariant"]]]))]]];
representationDataExtendsQ[___] := False;

(* Representation planning uses representationDescriptors, not the generic enrichment planner, so the
   registry lists no enrichment methods for this operation. *)
(*
    Summary: Basis rank of a decoded variant: 0 general, 1 unitary, 2 unitary with diagonal T.
    Parameters: variant — decoded variant association.
    Options/defaults: None.
    Parameters (optional): weakAllowed — True ranks a weak (Wolfram-tier, recorded "Numerical" or "Unverified") variant
        by its properties, for a request at its level (default False).
    Returns: -1 (numerical tier, or a recorded status weaker than Exact: never outranks, active only when chosen
        explicitly), 0, 1 or 2.
    Effects: Pure.
    Failures: None; malformed variants have rank 0.
    Example: representationBasisRank[<|"BasisProperties" -> <|"Unitary" -> True, "TDiagonal" -> True|>|>] is 2.
    See also: representationDataExtendsQ; GAP VVMF_BasisRank.
*)
representationBasisRank[variant_Association, weakAllowed_ : False] := With[{properties = Lookup[variant, "BasisProperties", <||>]},
    Which[Lookup[variant, "Tier", None] === "Numerical", -1,
        (* a variant recorded weaker than Exact never outranks, as GAP's VVMF_RepProperties (C8) *)
        !TrueQ[weakAllowed] && variantVerificationStatus[variant] =!= "Exact", -1,
        !TrueQ[Lookup[properties, "Unitary", False]], 0, TrueQ[Lookup[properties, "TDiagonal", False]], 2, True, 1]];
representationBasisRank[___] := 0;

registerGAPOperation["Representations", <|"Source" -> "Typed", "GenerationStep" -> 1,
    "CompleteQ" -> representationRequestCompleteQ, "RecoverySkipQ" -> representationRecoverySkipQ,
    "TerminalFailures" -> {"InvalidModularGenerators", "NongeneratingModularPair", "InvalidIrrepID", "MissingModularAssignment"},
    "Methods" -> None, "ParallelExpansion" -> representationParallelExpansion|>];

(*
    Summary: Split an allocated parallel representation attempt into single-core per-irrep partitions.
    Parameters: attempt — allocated parallel descriptor; request — the batch request (its
        representationRequest irrepIDs are the remaining irreps).
    Options/defaults: k = Min[AllocatedCores, Floor[AllocatedMemory/MemoryEstimate], number of irreps]
        (at least one); irreps are dealt round-robin in request order, so degrees mix across partitions.
    Returns: k child attempts (method and model of the parent, one core and 1/k of its memory each, WorkKey
        <parent>/<i>, ParentWorkKey the sequential twin's WorkKey, RequestFields with the partition).
    Effects: Pure.
    Failures: None; malformed input gives {}.
    Example: a four-core Dixon attempt over A5's five irreps gives partitions {1, 5}, {2}, {3}, {4}.
    Remarks: Each child gets the full AttemptTimeLimit for its share of the irreps; the children's verified
        partials are merged through the sibling transfer (D3) like any batch's partials.
    See also: expandParallelBatch; representationDescriptors; runRepresentationRequest.
*)
representationParallelExpansion[attempt_Association, request_Association] := Module[{ids, k, parts, share},
    ids = Lookup[Lookup[request, "representationRequest", <||>], "irrepIDs", {}];
    If[!ListQ[ids] || ids === {} || !IntegerQ[attempt["AllocatedCores"]] || !IntegerQ[attempt["AllocatedMemory"]], Return[{}]];
    k = Max[1, Min[attempt["AllocatedCores"], Quotient[attempt["AllocatedMemory"], attempt["MemoryEstimate"]], Length[ids]]];
    parts = Table[ids[[i ;; ;; k]], {i, k}];
    share = Quotient[attempt["AllocatedMemory"], k];
    MapIndexed[Join[KeyDrop[attempt, {"AllocatedCores", "AllocatedMemory"}], <|"Parallel" -> False, "MinCores" -> 1,
        "WorkKey" -> attempt["WorkKey"] <> "/" <> ToString[First[#2]], "AllocatedCores" -> 1, "AllocatedMemory" -> share,
        "ParentWorkKey" -> representationHistoryKey[attempt],
        "RequestFields" -> <|"representationRequest" -> Join[request["representationRequest"], <|"irrepIDs" -> #1|>]|>|>] &, parts]
];
representationParallelExpansion[___] := {};

(*
    Summary: The retry-history key of a representation descriptor or child attempt.
    Parameters: descriptor — descriptor, parallel twin or child attempt.
    Options/defaults: None.
    Returns: The sequential route's WorkKey (a parallel twin and its children share it).
    Effects: Pure.
    Failures: None.
    Example: "Representations/Dixon/Original/Parallel/2" has key "Representations/Dixon/Original".
    See also: runRepresentationRequest; representationParallelExpansion.
*)
representationHistoryKey[descriptor_Association] := Lookup[descriptor, "ParentWorkKey",
    StringReplace[descriptor["WorkKey"], "/Parallel" ~~ ___ ~~ EndOfString -> ""]];

(* -------------------------------------------------------------------------
   Descriptor planning
   ------------------------------------------------------------------------- *)

(* Unitary-first phases (design.md, unitary representation output): 1 direct unitary routes;
   2 general routes unitarized in GAP (GAP/RepresentationBasis.g), preceded by unitarizing retained
   general variants ("Unitarize"); 3 general routes whose verified matrices are kept as accepted
   partials under a unitary request. A "UnitaryTDiagonal" request adds phase 4: T diagonalization in GAP
   ("TDiagonalize") of each irrep's smallest-conductor variant. *)
$RepresentationPhase = <|"SL2Reps" -> 1, "LinearCharacter" -> 1, "DixonUnitary" -> 1, "BaumClausen" -> 1,
    "InducedUnitary" -> 1, "Dixon" -> 3, "REPSN" -> 3, "CharacterSubgroup" -> 3, "Induction" -> 3,
    "Extension" -> 3, "NormalExtension" -> 3, "AtlasRep" -> 3, "GAP" -> 3|>;
(* Routes that construct each irrep separately, so a parallel descriptor can partition the missing irreps
   among workers; whole-table routes (SL2Reps, BaumClausen, AtlasRep, GAP) and the cheap LinearCharacter
   are not partitioned. *)
$RepresentationPartitionable = {"DixonUnitary", "InducedUnitary", "Dixon", "REPSN", "CharacterSubgroup", "Induction",
    "Extension", "NormalExtension", "Unitarize", "TDiagonalize"};
$RepresentationPackages = <|"SL2Reps" -> "sl2reps", "REPSN" -> "repsn", "CharacterSubgroup" -> "repsn",
    "Induction" -> "repsn", "Extension" -> "repsn", "NormalExtension" -> "repsn", "AtlasRep" -> "atlasrep"|>;

(*
    Summary: Decide solvability from a bound character table.
    Parameters: characters — decoded CharacterData (Values, Degrees, ClassSizes).
    Options/defaults: None.
    Returns: True or False; Missing["Unknown"] for incomplete data.
    Effects: Pure.
    Failures: None.
    Example: the character table of A5 gives False, that of S4 True.
    Remarks: Normal subgroups are the intersections of character kernels (sets of classes); a finite group
        is solvable exactly when every chief factor has prime-power order (a nonabelian chief factor is a
        power of a nonabelian simple group, whose order has at least three prime divisors), and chief
        factors are the covering pairs of the normal-subgroup lattice.
    See also: representationDescriptors (BaumClausen applicability).
*)
characterTableSolvableQ[characters_Association] := Module[{values, degrees, sizes, kernels, normals, order, previous},
    {values, degrees, sizes} = Lookup[characters, {"Values", "Degrees", "ClassSizes"}, Missing["Unknown"]];
    If[!MatrixQ[values] || !ListQ[degrees] || !ListQ[sizes], Return[Missing["Unknown"]]];
    kernels = Table[Flatten[Position[values[[i]], x_ /; RootReduce[x - degrees[[i]]] === 0, {1}, Heads -> False]],
        {i, Length[degrees]}];
    normals = DeleteDuplicates[Sort /@ Append[kernels, Range[Length[sizes]]]];
    previous = {};
    While[normals =!= previous, previous = normals;
        normals = DeleteDuplicates[Sort /@ Join[normals, Flatten[Outer[Intersection, normals, normals, 1], 1]]]];
    order[set_] := Total[sizes[[set]]];
    AllTrue[Flatten[Table[If[m =!= n && SubsetQ[n, m] &&
            !AnyTrue[normals, # =!= m && # =!= n && SubsetQ[n, #] && SubsetQ[#, m] &], {order[n]/order[m]}, {}],
            {n, normals}, {m, normals}]], PrimePowerQ]
];
characterTableSolvableQ[___] := Missing["Unknown"];

(*
    Summary: Build the finite, phase-ordered list of representation attempts.
    Parameters: state — Packages (probe records), HasAssignment, AtlasName (True when an Atlas name is
        known), Models (preferred model order), WorkspaceBytes, optional MaxDegree and Solvable; request —
        representationRequest with basis; options — RepresentationMethod and GroupModel.
    Options/defaults: RepresentationMethod -> Automatic uses every route of the needed phases;
        GroupModel -> Automatic uses the state's model order.
    Returns: Job descriptors whose Tier is phase - 1, or InvalidMethodPlan Failure.
    Effects: Pure.
    Failures: Unknown method, model or basis.
    Example: under a unitary request LinearCharacter has tier 0, Dixon with GAP unitarization tier 1 and
        plain Dixon tier 2, so packJobBatches never places them in one batch.
    Remarks: Batches contain one tier only, so every batch is homogeneous in its phase. Under
        Basis -> "General" planning uses the phase-3 routes. Under a unitary basis: phase 1 the direct
        unitary routes; phase 2 "Unitarize" (retained general variants) and every general route again with
        GAP unitarization (WorkKey suffix "/Unitarize"; the coordinator adds the unitarize request field);
        phase 3 the general routes. An explicit general route runs in phases 2 and 3, after "Unitarize" of retained
        general variants; an explicit direct route in phase 1. "UnitaryTDiagonal" adds phase 4, "TDiagonalize". Every per-irrep route
        ($RepresentationPartitionable) is followed by its parallel twin (WorkKey suffix "/Parallel", MinCores 2),
        which runRepresentationRequest keeps only when that route is alone in its tier. Routes that do not use the
        model (LinearCharacter, SL2Reps, AtlasRep, Unitarize, TDiagonalize) run once, on the first model;
        BaumClausen prefers the PC model. Unavailable packages, a missing assignment (SL2Reps), an unknown
        Atlas name or a nonsolvable group (BaumClausen) mark descriptors Unavailable/Inapplicable. Phase-2
        descriptors add 512 d^4 bytes (d the largest degree) to the memory estimate for the Kronecker
        sums of BSGSAverage.
    See also: packJobBatches; runRepresentationRequest; step2Plan.md scheduling.
*)
representationDescriptors[state_Association, request_Association, options_Association] := Module[
    {basis, selected, modelChoice, models, packages, memory, descriptors = {}, status, reason, routeModels,
        entries, general, direct, kronecker},
    basis = Lookup[Lookup[request, "representationRequest", <||>], "basis", None];
    selected = Lookup[options, RepresentationMethod, Automatic];
    modelChoice = Lookup[options, GroupModel, Automatic];
    packages = Lookup[state, "Packages", <||>];
    If[!MemberQ[{"Unitary", "General", "UnitaryTDiagonal"}, basis] || (selected =!= Automatic && !KeyExistsQ[$RepresentationPhase, selected]) ||
        !groupModelChoiceQ[modelChoice] || !AssociationQ[packages],
        Return[makeFailure["InvalidMethodPlan", "Invalid representation method, model or basis."]]];
    models = groupModelOrder[modelChoice, Lookup[state, "Models", {"Original", "Permutation"}]];
    direct = Select[$RepresentationMethods, $RepresentationPhase[#] === 1 &];
    general = Select[$RepresentationMethods, $RepresentationPhase[#] === 3 &];
    (* {method, phase} pairs in phase order. *)
    entries = Which[
        basis === "General", {#, 3} & /@ If[selected === Automatic, general, {selected}],
        selected =!= Automatic && MemberQ[direct, selected], {{selected, 1}},
        (* Retained general matrices are unitarized before an explicit general route runs again (reuse, not
           discovery). *)
        selected =!= Automatic, {{"Unitarize", 2}, {selected, 2}, {selected, 3}},
        True, Join[{#, 1} & /@ direct, {{"Unitarize", 2}}, {#, 2} & /@ general, {#, 3} & /@ general]];
    If[basis === "UnitaryTDiagonal", AppendTo[entries, {"TDiagonalize", 4}]];
    memory = Max[128*2^20, 3 Lookup[state, "WorkspaceBytes", 0]];
    kronecker = 512 Lookup[state, "MaxDegree", 1]^4;
    Do[
        With[{method = First[entry], phase = Last[entry]},
            {status, reason} = Which[
                KeyExistsQ[$RepresentationPackages, method] &&
                    !TrueQ[Lookup[Lookup[packages, $RepresentationPackages[method], <||>], "Available", False]],
                    {"Unavailable", "Missing package " <> $RepresentationPackages[method]},
                method === "SL2Reps" && !TrueQ[Lookup[state, "HasAssignment", False]],
                    {"Inapplicable", "Requires an explicit modular S,T assignment"},
                method === "AtlasRep" && !TrueQ[Lookup[state, "AtlasName", False]],
                    {"Inapplicable", "Requires an Atlas group name in MethodData"},
                method === "BaumClausen" && Lookup[state, "Solvable", Missing["Unknown"]] === False,
                    {"Inapplicable", "Requires a solvable group"},
                True, {"Eligible", None}];
            routeModels = Which[
                MemberQ[{"LinearCharacter", "SL2Reps", "AtlasRep", "Unitarize", "TDiagonalize"}, method], Take[models, 1],
                method === "BaumClausen" && modelChoice === Automatic, DeleteDuplicates[Prepend[models, "PC"]],
                True, models];
            Do[With[{sequential = <|"Operation" -> "Representations", "Method" -> method, "Model" -> model,
                "RecoveryStrategy" -> "Native",
                "WorkKey" -> StringRiffle[Join[{"Representations", method, model}, If[phase === 2 && method =!= "Unitarize", {"Unitarize"}, {}]], "/"],
                "Tier" -> phase - 1, "Parallel" -> False, "MinCores" -> 1,
                "MemoryEstimate" -> If[phase === 2 || phase === 4, memory + kronecker, memory],
                "Availability" -> status, "Reason" -> reason|>},
                AppendTo[descriptors, sequential];
                (* Its per-irrep parallel twin; the coordinator uses it only when this route is alone. *)
                If[MemberQ[$RepresentationPartitionable, method],
                    AppendTo[descriptors, Join[sequential, <|"WorkKey" -> sequential["WorkKey"] <> "/Parallel", "Parallel" -> True,
                        "MinCores" -> 2|>]]]], {model, routeModels}]],
        {entry, entries}];
    descriptors
];
representationDescriptors[___] := makeFailure["InvalidMethodPlan", "Expected planning state, request and options."];

(*
    Summary: The GAP request fields of the caller's unitarizer and witness choice for one tier (methodOptionsPlan.md
        2B.1, 2B.2).
    Parameters: tier — descriptor tier (phase - 1); options — validated options.
    Options/defaults: Automatic UnitarizationMethod sends "Automatic" on tier 1 only (today's request).
    Returns: Association of request fields: "unitarize" on the phases that unitarize (tier 1, and with an explicit
        unitarizer tier 3, the T-diagonalization of a general witness; never the direct or general-only phases), "witness"
        when WitnessVariant is explicit.
    Effects: Pure.
    Failures: None.
    Example: representationTierFields[2, <|UnitarizationMethod -> "GroupAverage"|>] has no "unitarize".
    See also: runRepresentationRequest.
*)
representationTierFields[tier_Integer, options_Association] := Join[
    If[tier === 1 || (tier === 3 && Lookup[options, UnitarizationMethod, Automatic] =!= Automatic),
        <|"unitarize" -> Replace[Lookup[options, UnitarizationMethod, Automatic], Automatic -> "Automatic"]|>, <||>],
    If[Lookup[options, WitnessVariant, Automatic] =!= Automatic, <|"witness" -> options[WitnessVariant]|>, <||>]];

(*
    Summary: Irrep IDs that a representation batch of one tier still has to compute.
    Parameters: representations — accepted decoded Representations; ids — requested IDs; basis;
        tier — descriptor tier (phase - 1); tier 3 asks for the whole request.
    Options/defaults: conv — <|"ModularAssignment", "Generators", "phaseOrder", "phaseConvention"|> for the
        T-phase requirements of a "UnitaryTDiagonal" request (none by default).
    Returns: Sorted list of irrep IDs.
    Effects: Pure.
    Failures: None.
    Example: under a unitary request, a phase-3 batch skips irreps that already have a verified variant
        (an accepted general partial), because more general matrices would not satisfy the request.
    Remarks: Construction phases (tiers 0-2) of a "UnitaryTDiagonal" request work toward a unitary
        basis; tier 3 (T diagonalization, and the completion checks) uses the requested basis.
    See also: runRepresentationRequest; representationRequestCompleteQ.
*)
remainingRepresentationIDs[representations_Association, ids_List, basis_String, tier_Integer, conv_Association : <||>] := Module[
    {working, unsatisfied},
    working = If[basis === "UnitaryTDiagonal" && tier < 3, "Unitary", basis];
    unsatisfied = Select[ids, !representationRequestCompleteQ[<|"Status" -> "Complete", "Representations" -> representations,
            "ModularAssignment" -> Lookup[conv, "ModularAssignment", None], "Generators" -> Lookup[conv, "Generators", {}]|>,
        <|"representationRequest" -> Join[<|"irrepIDs" -> {#}, "basis" -> working|>, KeyTake[conv, {"phaseOrder", "phaseConvention", "verify"}]]|>] &];
    Sort[If[working === "Unitary" && tier === 2,
        Select[unsatisfied, !AssociationQ[Lookup[representations, #, None]] &], unsatisfied]]
];

(* -------------------------------------------------------------------------
   Coordinator
   ------------------------------------------------------------------------- *)

(*
    Summary: Merge a verified sibling checkpoint's representations into a published checkpoint.
    Parameters: destination — published private reference; source — verified sibling reference;
        context — execution capabilities, options and call directory; replaceActive — irrep IDs whose incoming
        active variant replaces the destination's (the sibling's explicit re-derivations).
    Options/defaults: Transfer is an internal, not publicly selectable, route; replaceActive {} (admission ranks).
    Returns: Verified next-generation candidate, or Failure preserving both checkpoints.
    Effects: Runs one worker that re-verifies the source's variants in the destination state (D3).
    Failures: Different state identity, verification failure or checkpoint failure.
    Example: two partial routes of one batch are combined without merging binary workspaces.
    See also: GAP VVMF_TransferRepresentations; mergeCharacterCheckpoints.
*)
mergeRepresentationCheckpoints[destination_String, source_String, context_Association, replaceActive_List : {}] := Module[
    {target, incoming, request, descriptor},
    target = checkpointRecord[destination, context["Capabilities"]];
    incoming = checkpointRecord[source, context["Capabilities"]];
    If[FailureQ[target], Return[target]]; If[FailureQ[incoming], Return[incoming]];
    If[target["Data"]["StateID"] =!= incoming["Data"]["StateID"],
        Return[makeFailure["StateConflict", "Only representations of the same state can be transferred."]]];
    request = <|"operation" -> "Representations", "requestID" -> CreateUUID["merge-"],
        "stateID" -> target["Native"]["stateID"], "generatorIdentity" -> target["Native"]["generatorIdentity"],
        "stateGeneration" -> ToString[target["Data"]["StateGeneration"] + 1],
        "characterIdentity" -> target["Native"]["characterData"]["identity"],
        "transferredRepresentations" -> incoming["Native"]|>;
    If[replaceActive =!= {}, request["replaceActive"] = replaceActive];
    descriptor = <|"Operation" -> "Representations", "Method" -> "Transfer", "Model" -> "Original",
        "RecoveryStrategy" -> "Native", "WorkKey" -> "Representations/Transfer", "Tier" -> 0,
        "Parallel" -> False, "MinCores" -> 1, "MemoryEstimate" -> 1, "Availability" -> "Eligible",
        "Reason" -> None, "AllocatedCores" -> 1, "AllocatedMemory" -> context["Options"][MemoryBudget]|>;
    runAttempt[destination, descriptor, request, context]
];
mergeRepresentationCheckpoints[___] := makeFailure["InvalidRequest", "Expected two verified checkpoint references."];

(*
    Summary: Publish verified candidates one generation at a time.
    Parameters: group — live Group; candidates — verified candidates of one batch (winner first);
        context; source — StateSource diagnostics; outcomes — batch outcomes for diagnostics.
    Options/defaults: None.
    Returns: <|"Checkpoint" -> last published reference or None, "Failure" -> None or Failure,
        "Retention" -> retention failures of generations that were published without retained state|>.
    Effects: Publishes the first candidate directly (it advances the accepted generation once); every
        further candidate is merged into the newly published checkpoint and published in turn (D2, D3).
    Failures: A failed publication or merge stops publishing; earlier generations stay accepted.
    Example: a batch with two partial routes publishes two consecutive generations.
    Remarks: Each publication rereads the group, so revisions and generations always advance once.
    See also: publishGroupEnrichment; mergeRepresentationCheckpoints; runRepresentationRequest.
*)
publishRepresentationCandidates[group_Group, candidates_List, context_Association, source_Association,
    outcomes_List] := Module[{published = None, candidate, accepted, merged, result, retention = {}},
    Do[
        accepted = groupData[group];
        (* A sibling's explicit replacements (ReplaceActive) travel with its transfer and its publication. *)
        candidate = If[published === None, item,
            mergeRepresentationCheckpoints[published, item["Checkpoint"], context, Lookup[item, "ReplaceActive", {}]]];
        If[FailureQ[candidate], Return[<|"Checkpoint" -> published, "Failure" -> candidate|>, Module]];
        If[published =!= None && KeyExistsQ[item, "ReplaceActive"], candidate = Append[candidate, "ReplaceActive" -> item["ReplaceActive"]]];
        result = publishGroupEnrichment[group, accepted, Join[candidate, <|"Outcomes" -> outcomes|>],
            context["Capabilities"], context["Options"], source];
        If[FailureQ[result] && !MatchQ[Lookup[result[[2]], "PartialResult", None], _Group],
            Return[<|"Checkpoint" -> published, "Failure" -> result, "Retention" -> retention|>, Module]];
        (* A retention failure still publishes the generation; it is reported at the end. *)
        If[FailureQ[result], AppendTo[retention, result]];
        published = candidate["Checkpoint"],
        {item, candidates}];
    <|"Checkpoint" -> published, "Failure" -> None, "Retention" -> retention|>
];

(*
    Summary: The T-phase requirements of a representation request for remainingRepresentationIDs.
    Parameters: accepted — group data; request — <|"irrepIDs", "basis", optional "phaseOrder",
        "phaseConvention"|>.
    Options/defaults: None.
    Returns: <|"ModularAssignment", "Generators", "phaseOrder", "phaseConvention"|> (the last two only for a
        "UnitaryTDiagonal" request).
    Effects: Pure.
    Failures: None.
    Example: representationConvention[data, <|"basis" -> "Unitary"|>] has no phase requirements.
    See also: remainingRepresentationIDs; tConventionQ.
*)
representationConvention[accepted_Association, request_Association] := Join[
    <|"ModularAssignment" -> Lookup[accepted, "ModularAssignment", None], "Generators" -> Lookup[accepted, "Generators", {}]|>,
    (* a weak computation (Verification "Numerical" or None): GAP matches traces only (C7) *)
    If[Lookup[request, "verify", "Full"] === "Traces", <|"verify" -> "Traces"|>, <||>],
    If[Lookup[request, "basis", None] === "UnitaryTDiagonal", KeyTake[request, {"phaseOrder", "phaseConvention"}], <||>]];

(*
    Summary: Run the unitarization of retained variants before any route of its phase discovers matrices again.
    Parameters: descriptors — filtered descriptors; representations — accepted data; ids — requested irreps;
        basis — requested basis; conv — T-phase requirements.
    Options/defaults: None.
    Returns: Descriptors; when an eligible "Unitarize" descriptor leads the first tier with work and a remaining
        irrep of that tier has stored variants, the other eligible descriptors of that tier are withheld for this
        iteration.
    Effects: Pure.
    Failures: None.
    Example: after a General Dixon computation, a unitary request first unitarizes the stored Dixon matrices
        and does not start Dixon again unless that leaves irreps.
    Remarks: step2Plan.md: general matrices retained from earlier attempts are reused before equivalent matrices
        are discovered again. The next iteration replans; the history then skips Unitarize on the same irreps.
    See also: runRepresentationRequest; representationDescriptors.
*)
representationReuseFirst[descriptors_List, representations_, ids_List, basis_String, conv_Association : <||>] := Module[
    {eligible, tier, left},
    eligible = Select[descriptors, #["Availability"] === "Eligible" &];
    If[eligible === {}, Return[descriptors]];
    tier = Min[Lookup[eligible, "Tier"]];
    left = remainingRepresentationIDs[representations, ids, basis, tier, conv];
    If[!AnyTrue[eligible, #["Tier"] === tier && #["Method"] === "Unitarize" &] ||
        !AnyTrue[left, AssociationQ[Lookup[representations, #, None]] && Lookup[representations[#], "Variants", <||>] =!= <||> &],
        Return[descriptors]];
    Select[descriptors, !(#["Tier"] === tier && #["Availability"] === "Eligible" && #["Method"] =!= "Unitarize") &]
];

(*
    Summary: Choose between competing sequential descriptors and one route's per-irrep parallel twin.
    Parameters: descriptors — filtered descriptors with their parallel twins; representations — accepted
        data; ids — requested irreps; basis — requested basis; options — validated settings.
    Options/defaults: The twin is used when every eligible sequential descriptor of the first tier with work
        is the same method (models aside), CoreBudget is at least four and at least two irreps remain for that
        tier; it then replaces that tier's first descriptor. Otherwise every twin is dropped.
    Returns: Descriptors for packJobBatches.
    Effects: Pure.
    Failures: None.
    Example: an explicit Dixon General request for A5 with four cores runs one parallel Dixon attempt.
    Remarks: Default automatic generation keeps competing sequential descriptors (step2Plan.md); the parallel
        descriptor occupies a batch alone (packJobBatches).
    See also: representationParallelExpansion; runRepresentationRequest.
*)
representationParallelGate[descriptors_List, representations_, ids_List, basis_String, options_Association, conv_Association : <||>] := Module[
    {sequential, twins, eligible, tier, first, twin},
    twins = Select[descriptors, TrueQ[#["Parallel"]] &];
    sequential = Select[descriptors, !TrueQ[#["Parallel"]] &];
    eligible = Select[sequential, #["Availability"] === "Eligible" &];
    If[eligible === {} || !IntegerQ[options[CoreBudget]] || options[CoreBudget] < 4, Return[sequential]];
    tier = Min[Lookup[eligible, "Tier"]];
    eligible = Select[eligible, #["Tier"] === tier &];
    first = First[eligible];
    twin = SelectFirst[twins, #["WorkKey"] === first["WorkKey"] <> "/Parallel" &, None];
    If[twin === None || Length[DeleteDuplicates[Lookup[eligible, "Method"]]] =!= 1 ||
        Length[remainingRepresentationIDs[representations, ids, basis, tier, conv]] < 2, Return[sequential]];
    ReplacePart[sequential, FirstPosition[sequential, first, {}, {1}, Heads -> False] -> twin]
];

(*
    Summary: Compute requested representations by phase-ordered batches, publishing every verified partial.
    Parameters: group — live Group; request — <|"irrepIDs", "basis", optional "methodData"|>, where
        methodData is already GAP-encoded (subgroupGenerators as stable-ID words, representation as
        scalar-record matrices, atlasName, representationNumber); the public MethodData option decodes
        GroupWord and Rep values into this record;
        options — validated settings (RepresentationMethod, GroupModel, resources, StoreGAPState);
        capabilities — probe; call — owned checkpoint call; local — call-owned source or None.
    Options/defaults: AttemptTimeLimit bounds every attempt; each worker stops starting irreps at 60% of it.
    Returns: The same Group when every requested irrep is satisfied; otherwise
        Failure["UnitaryConstructionUnavailable" | "TDiagonalizationUnavailable" | "MethodExhausted" |
        other, ...] carrying
        PartialResult -> group, RemainingIDs, Outcomes and RouteOutcomes (method, model, outcome
        tag or "Verified" per attempted route). Cancellation returns Cancelled after
        publishing verified partials.
    Effects: Runs GAP workers; each accepted candidate is a new group generation (D2).
    Failures: Terminal failures (invalid assignment, unknown irrep) stop further batches; exhausted
        routes end the request; accepted generations are never lost.
    Example: catalogue A5 with Basis -> "Unitary" gets its degree-one, four and five irreps from phase 1
        and its degree-three irreps from phase 2 (Dixon unitarized in GAP); only when phases 1 and 2 fail
        does a group keep phase-3 general matrices as accepted partials and return
        UnitaryConstructionUnavailable.
    Remarks: A satisfied request returns without starting GAP. One source checkpoint serves each accepted
        state (at most one reconstruction), and its workspace size enters the admission estimate before
        packing. A request-completing winner is published alone. Each iteration replans from the group's
        current data: a descriptor is skipped after a Complete or inapplicable/unavailable outcome, or
        after any outcome on the same remaining irrep set, so partial routes rerun on the remaining
        irreps (D4) and the loop terminates. The winner rule is the operation's completion predicate
        (D1), so a general candidate never stops a unitary rival.
    See also: representationDescriptors; publishRepresentationCandidates; runJobBatch.
*)
runRepresentationRequest[group_Group, request_Association, options_Association, capabilities_Association,
    call_Association, local_ : None] := Module[
    {ids, basis, accepted, history = {}, outcomes = {}, local0 = local, published = False, descriptors,
        plan, batch, tier, remaining, source, record, methodRequest, result, candidates, publication,
        attempts, terminal, context, stateInfo, skipped = {}, partialFailure, envelope, retention = {}, routeOutcomes, conv, phaseFields},
    ids = request["irrepIDs"]; basis = request["basis"];
    context = <|"Options" -> options, "Capabilities" -> capabilities, "Directory" -> call["Directory"]|>;
    conv = representationConvention[groupData[group], request];
    partialFailure[failure_] := Failure[failure[[1]], Join[failure[[2]], <|"Outcomes" -> outcomes, "Skipped" -> skipped,
        "RemainingIDs" -> remainingRepresentationIDs[groupData[group]["Representations"], ids, basis, 3, conv]|>,
        If[published, <|"PartialResult" -> group|>, <||>],
        If[retention === {}, <||>, <|"RetentionFailure" -> Last[retention], "RemainingWork" -> {"RetainGAPState"}|>]]];
    Do[
        accepted = groupData[group];
        If[FailureQ[accepted], Return[accepted, Module]];
        If[remainingRepresentationIDs[accepted["Representations"], ids, basis, 3, conv] === {}, Break[]];
        (* One source per accepted state: a retained or call-owned checkpoint when it matches, otherwise
           one typed reconstruction; later iterations reuse it until a publication replaces it. *)
        source = groupComputationSource[group, accepted, capabilities, call, local0];
        If[FailureQ[source], Return[partialFailure[source], Module]];
        If[source["Checkpoint"] === None,
            envelope = groupEnvelope[accepted];
            If[FailureQ[envelope], Return[partialFailure[envelope], Module]];
            source["Checkpoint"] = prepareGroupCheckpoint[accepted, envelope, options, capabilities, call];
            If[FailureQ[source["Checkpoint"]], Return[partialFailure[source["Checkpoint"]], Module]]];
        local0 = source["Checkpoint"];
        record = checkpointRecord[local0, capabilities];
        If[FailureQ[record], Return[partialFailure[record], Module]];
        If[options[MemoryBudget] < Max[128*2^20, 3 record["WorkspaceArtifact"]["Bytes"]],
            Return[partialFailure[makeFailure["MemoryLimit", "The budget is below this checkpoint's admission estimate."]], Module]];
        stateInfo = <|"Packages" -> capabilities["Packages"], "HasAssignment" -> AssociationQ[accepted["ModularAssignment"]],
            "AtlasName" -> (KeyExistsQ[Lookup[request, "methodData", <||>], "atlasName"] ||
                (accepted["Construction"]["type"] === "catalogue" &&
                    MemberQ[{"AlternatingGroup", "SymmetricGroup"}, accepted["Construction"]["catalogue"]])),
            "Models" -> If[accepted["Construction"]["type"] === "presentation", {"Permutation", "Original"}, {"Original", "Permutation"}],
            "WorkspaceBytes" -> record["WorkspaceArtifact"]["Bytes"],
            "Solvable" -> characterTableSolvableQ[Lookup[accepted, "CharacterData", <||>]], "MaxDegree" -> Max[Append[Select[Lookup[Replace[Lookup[accepted, "CharacterData", <||>], Except[_Association] -> <||>],
                "Degrees", {}], IntegerQ], 1]]|>;
        descriptors = representationDescriptors[stateInfo, <|"representationRequest" -> <|"basis" -> basis|>|>, options];
        If[FailureQ[descriptors], Return[partialFailure[descriptors], Module]];
        (* A weak computation runs constructions only: GAP's unitarization and T-diagonalization derive native variants
           from proved ones (methodOptionsPlan.md C7). *)
        If[Lookup[conv, "verify", "Full"] === "Traces", descriptors = Select[descriptors, !MemberQ[{"Unitarize", "TDiagonalize"}, #["Method"]] &]];
        (* Keep only descriptors with remaining work for their tier and without a prior deciding outcome. *)
        descriptors = Select[descriptors, Function[descriptor, With[
            {left = remainingRepresentationIDs[accepted["Representations"], ids, basis, descriptor["Tier"], conv]},
            left =!= {} && !AnyTrue[history, #["WorkKey"] === representationHistoryKey[descriptor] &&
                (#["Remaining"] === left || representationRecoverySkipQ[#["Result"]]) &]]]];
        descriptors = representationReuseFirst[descriptors, accepted["Representations"], ids, basis, conv];
        descriptors = representationParallelGate[descriptors, accepted["Representations"], ids, basis, options, conv];
        plan = packJobBatches[descriptors, options];
        If[FailureQ[plan], Return[partialFailure[plan], Module]];
        skipped = DeleteDuplicates[Join[skipped, plan["Skipped"]]];
        If[plan["Batches"] === {}, Break[]];
        batch = First[plan["Batches"]]; tier = batch["Tier"];
        remaining = remainingRepresentationIDs[accepted["Representations"], ids, basis, tier, conv];
        methodRequest = Join[<|"operation" -> "Representations",
            "stateID" -> accepted["StateID"], "generatorIdentity" -> accepted["GeneratorIdentity"],
            "evictionEpoch" -> ToString[accepted["RepresentationCache"]["Epoch"]],
            "stateGeneration" -> ToString[accepted["StateGeneration"] + 1],
            "construction" -> accepted["Construction"], "characterIdentity" -> accepted["CharacterData"]["Identity"],
            "representationRequest" -> Join[<|"irrepIDs" -> remaining,
                "basis" -> If[basis === "UnitaryTDiagonal" && tier < 3, "Unitary", basis]|>, KeyTake[conv, {"phaseOrder", "phaseConvention", "verify"}]]|>,
            representationTierFields[tier, options],
            If[Lookup[conv, "verify", "Full"] === "Traces", <|"verify" -> "Traces"|>, <||>],
            (* Phase 4 re-derives every remaining irrep (also a diagonal T in another order or convention) and
               activates the result explicitly. *)
            phaseFields = If[tier === 3, <|"phaseOrder" -> Lookup[conv, "phaseOrder", "Ascending"],
                "phaseConvention" -> Lookup[conv, "phaseConvention", "None"], "force" -> True, "replaceActive" -> remaining|>, <||>],
            If[options[AttemptTimeLimit] === Infinity, <||>,
                <|"softDeadlineMilliseconds" -> ToString[Floor[600 options[AttemptTimeLimit]]]|>],
            If[AssociationQ[Lookup[request, "methodData", None]], <|"methodData" -> request["methodData"]|>, <||>]];
        result = acceptVerifiedWinner[runJobBatch[source["Checkpoint"], batch, methodRequest, context]];
        attempts = If[FailureQ[result], Lookup[result[[2]], "Outcomes", {}], result["Outcomes"]];
        outcomes = Join[outcomes, attempts];
        history = Join[history, <|"WorkKey" -> representationHistoryKey[#["Descriptor"]], "Remaining" -> remaining,
            "Result" -> #["Result"]|> & /@ Select[attempts, KeyExistsQ[#, "Descriptor"] &]];
        (* A request-completing winner is published alone; rival partials would only add redundant
           variants. Without a winner (or on cancellation) every verified partial is published. *)
        candidates = Which[FailureQ[result], Lookup[result[[2]], "Partials", {}],
            AssociationQ[result["Winner"]], {result["Winner"]}, True, result["Partials"]];
        If[candidates =!= {},
            publication = publishRepresentationCandidates[group,
                (* Each candidate replaces only the irreps it was asked for: a parallel child's partition, else all
                   remaining ones (a sibling's untouched active variants must not overwrite a merged replacement). *)
                (* a weak ("Traces") request may replace the active variants of the irreps it asked for: its GAP admission ranks
                   by properties at that level, which the default rank rule (weak = -1) would refuse (review 2C-iii-a F2) *)
                If[tier === 3 || Lookup[conv, "verify", "Full"] === "Traces", Append[#, "ReplaceActive" -> Intersection[remaining, Lookup[Lookup[Lookup[Lookup[#, "Descriptor", <||>],
                    "RequestFields", <||>], "representationRequest", <||>], "irrepIDs", remaining]]] & /@ candidates, candidates],
                context, KeyDrop[source, "Checkpoint"], attempts];
            If[publication["Checkpoint"] =!= None, published = True; local0 = publication["Checkpoint"]];
            retention = Join[retention, publication["Retention"]];
            If[FailureQ[publication["Failure"]],
                If[FailureQ[result],
                    Return[partialFailure[Failure[result[[1]], Join[result[[2]], <|"PublicationFailure" -> publication["Failure"]|>]]], Module],
                    Return[partialFailure[publication["Failure"]], Module]]]];
        If[FailureQ[result], Return[partialFailure[result], Module]];
        terminal = SelectFirst[Lookup[attempts, "Result", {}], operationTerminalFailureQ["Representations", #] &, None];
        If[FailureQ[terminal], Return[partialFailure[terminal], Module]],
        {Length[$RepresentationMethods] * 3 * (Length[ids] + 1) + 1}];
    accepted = groupData[group];
    remaining = remainingRepresentationIDs[accepted["Representations"], ids, basis, 3, conv];
    If[remaining === {}, Return[If[retention === {}, group,
        Failure[retention[[-1]][[1]], Join[retention[[-1]][[2]], <|"PartialResult" -> group, "RemainingWork" -> {"RetainGAPState"}|>]]]]];
    routeOutcomes = Map[<|"Method" -> #["Descriptor"]["Method"], "Model" -> #["Descriptor"]["Model"],
        "Outcome" -> If[FailureQ[#["Result"]], #["Result"][[1]], "Verified"]|> &,
        Select[outcomes, KeyExistsQ[#, "Descriptor"] && KeyExistsQ[#, "Result"] &]];
    (* Slow or failing irreps are named with an explicit command that computes just them. *)
    With[{nonunitary = Select[remaining, KeyExistsQ[accepted["Representations"], #] &&
            !representationRequestCompleteQ[<|"Status" -> "Complete", "Representations" -> accepted["Representations"]|>,
                <|"representationRequest" -> <|"irrepIDs" -> {#}, "basis" -> "Unitary"|>|>] &]},
    Which[
    basis =!= "General" && nonunitary =!= {},
        partialFailure[makeFailure["UnitaryConstructionUnavailable",
            "The GAP routes (direct unitary routes, and general routes unitarized in GAP) did not produce a unitary basis for some requested irreps: each route failed, was inapplicable or reached its time limit (RouteOutcomes gives each attempted route's outcome). Their verified general matrices are kept as accepted partials. A route can be retried for just these irreps with a longer time limit (see Suggestions); Wolfram unitarization and user-supplied representations are the other remedies.",
            <|"AcceptedPartialIDs" -> nonunitary,
                "RouteOutcomes" -> routeOutcomes,
                "Suggestions" -> Join[representationRetryCommand[nonunitary, #, 3 options[AttemptTimeLimit]] & /@ {"Dixon", "DixonUnitary"},
                    If[AssociationQ[accepted["ModularAssignment"]], {},
                        {"If g is a finite quotient of SL(2,Z), assign its S and T with AssignModularGenerators (or build the recorded realization with BuildModularGroup): SL2Reps then constructs unitary T-diagonal irreps directly."}]],
                "Remedies" -> {"UnitarizeRepresentation", "TransformGroupRepresentations", "SetGroupRepresentation"}|>]],
    basis === "UnitaryTDiagonal" && AllTrue[remaining, KeyExistsQ[accepted["Representations"], #] &],
        (* The cause decides the remedy: GAP diagonalizes T only from a native (cyclotomic) variant, so irreps
           whose variants are all inert need the Wolfram route; the others reached the time limit. *)
        With[{noWitness = Select[remaining, !AnyTrue[Values[accepted["Representations"][#]["Variants"]],
                MemberQ[{"Native", "ScaledNative"}, #["Tier"]] &] &]},
        partialFailure[makeFailure["TDiagonalizationUnavailable",
            "Every remaining irrep has verified unitary matrices, but GAP did not diagonalize the assigned T for them (RouteOutcomes gives each attempted route's outcome): " <>
                If[noWitness =!= {}, "irreps listed under NoNativeWitnessIDs have only Wolfram-tier or numerical variants, which GAP cannot use, so TransformGroupRepresentations diagonalizes them in Wolfram; ", ""] <>
                "the others reached the time limit. The unitary matrices are kept; DiagonalizeRepresentationT diagonalizes a representation in Wolfram.",
            <|"RouteOutcomes" -> routeOutcomes, "NoNativeWitnessIDs" -> noWitness,
                "Suggestions" -> Join[
                    If[Complement[remaining, noWitness] === {}, {}, {"ComputeGroupRepresentations[g, " <> ToString[Complement[remaining, noWitness], InputForm] <>
                        ", Basis -> \"UnitaryTDiagonal\", AttemptTimeLimit -> " <>
                        ToString[If[options[AttemptTimeLimit] === Infinity, Infinity, Ceiling[3 options[AttemptTimeLimit]]], InputForm] <> "]"}],
                    If[noWitness === {}, {}, {"TransformGroupRepresentations[g, " <> ToString[noWitness, InputForm] <>
                        ", Basis -> \"UnitaryTDiagonal\", TPhaseOrder -> " <> ToString[Lookup[conv, "phaseOrder", "Ascending"], InputForm] <>
                        ", PhaseConvention -> " <> If[Lookup[conv, "phaseConvention", "None"] === "None", "None", ToString[conv["phaseConvention"], InputForm]] <>
                        ", DiagonalizationMethod -> \"NumericalReconstruction\"]"}]],
                "Remedies" -> {"DiagonalizeRepresentationT", "TransformGroupRepresentations"}|>]]],
    True,
        partialFailure[makeFailure["MethodExhausted",
            "The representation methods did not produce every requested irrep: each route failed, was inapplicable or reached its time limit (RouteOutcomes gives each attempted route's outcome). Retry just the remaining irreps with an explicit method and a longer time limit (see Suggestions).",
            <|"RepresentationMethod" -> Lookup[options, RepresentationMethod, Automatic],
                "RouteOutcomes" -> routeOutcomes,
                "AttemptTimeLimit" -> options[AttemptTimeLimit],
                "Suggestions" -> (representationRetryCommand[remaining, #, 3 options[AttemptTimeLimit]] & /@
                    If[basis === "General", {"Dixon", "REPSN"}, {"Dixon", "DixonUnitary"}])|>]]]]
];
runRepresentationRequest[___] := makeFailure["InvalidRequest", "Expected a live group, representation request and owned call."];

(*
    Summary: Own the resources of one representation computation, or reuse the builder's call.
    Parameters: group — live Group; request — irrepIDs, basis and optional GAP-encoded methodData;
        options — validated settings.
    Options/defaults: Active builder calls on the same group are reused privately.
    Returns: The same Group, or the coordinator's Failure.
    Effects: A satisfied request returns without probing GAP. Otherwise probes GAP once, owns a checkpoint
        call and releases its workers, files and leases on every exit.
    Failures: Unknown groups, insufficient memory budget, unavailable GAP, coordinator failures.
    Example: runRepresentationEnrichment[g, <|"irrepIDs" -> ids, "basis" -> "General"|>, options] computes
        every missing irrep of g.
    See also: runRepresentationRequest; runGroupEnrichment; withCheckpointCall.
*)
runRepresentationEnrichment[group_Group, request_Association, options_Association] :=
    Block[{$GroupAcceptanceLevel = If[$GroupAcceptanceLevel === Automatic, groupAcceptanceLevel[group], $GroupAcceptanceLevel]},
        runRepresentationEnrichmentWork[group, request, options]];
runRepresentationEnrichmentWork[group_Group, request_Association, options_Association] :=
    withProgress[options, "ComputeGroupRepresentations", Function[Null, Module[{accepted, capabilities},
        accepted = groupData[group]; If[FailureQ[accepted], Return[accepted]];
        If[TrueQ[$ProgressActive], $ProgressPartialResult = group];
        If[remainingRepresentationIDs[accepted["Representations"], request["irrepIDs"], request["basis"], 3,
                representationConvention[accepted, request]] === {},
            Return[group]];
        If[options[MemoryBudget] < 128*2^20,
            Return[makeFailure["MemoryLimit", "The budget is below the initial admission estimate."]]];
        If[AssociationQ[$ActiveGroupCall] && Lookup[$ActiveGroupCall, "Group", None] === group,
            Return[runRepresentationRequest[group, request, options, $ActiveGroupCall["Capabilities"],
                $ActiveGroupCall["Call"], $ActiveGroupCall["Checkpoint"]]]];
        progressReport[<|"Event" -> "Stage", "Phase" -> "Checking GAP"|>];
        capabilities = CheckGAP[]; If[FailureQ[capabilities], Return[capabilities]];
        withCheckpointCall[Function[call, runRepresentationRequest[group, request, options, capabilities, call]]]
    ]]];
runRepresentationEnrichment[___] := makeFailure["InvalidRequest", "Expected a live group, representation request and options."];

(*
    Summary: The builders' representation stage: compute every irrep after mandatory group data.
    Parameters: group — accepted character-complete Group; options — validated builder settings
        (Basis, RepresentationMethod, MethodData and the GAP job options).
    Options/defaults: Basis -> "Unitary" by default, as for ComputeGroupRepresentations.
    Returns: The same Group, or the representation Failure (finishGroupBuild adds PartialResult and
        RemainingWork).
    Effects: Runs inside the builder's checkpoint call ($ActiveGroupCall), reusing its workers and
        verified checkpoint; each verified irrep set is its own generation.
    Failures: MissingModularAssignment for UnitaryTDiagonal without an assignment; invalid MethodData;
        the coordinator's failures.
    Example: BuildGroup[CatalogueGroup["SymmetricGroup", 3]] returns S3 with every irrep unitary.
    Remarks: Equivalent to ComputeGroupRepresentations[g, All, opts] with the builder's options (plan).
    See also: finishGroupBuild; runRepresentationEnrichment; ComputeGroupRepresentations.
*)
builderRepresentations[group_Group, options_Association] := Module[{accepted, methodData, result},
    accepted = groupData[group]; If[FailureQ[accepted], Return[accepted]];
    If[options[Basis] === "UnitaryTDiagonal" && !AssociationQ[accepted["ModularAssignment"]],
        Return[makeFailure["MissingModularAssignment",
            "Basis -> \"UnitaryTDiagonal\" requires a modular S,T assignment; build with BuildModularGroup or assign S,T first."]]];
    methodData = If[options[MethodData] === Automatic, None, encodeRepresentationMethodData[options[MethodData], accepted]];
    If[FailureQ[methodData], Return[methodData]];
    result = runRepresentationEnrichment[group, Join[<|"irrepIDs" -> accepted["CharacterData"]["IrrepIDs"], "basis" -> options[Basis]|>,
        representationPhaseFields[options], If[methodData === None, <||>, <|"methodData" -> methodData|>],
        (* a weak build computes its representations at its level (2C-iii-a: GAP matches traces only) *)
        If[MemberQ[{"Numerical", None}, Lookup[options, Verification, Automatic]], <|"verify" -> "Traces"|>, <||>]], options];
    If[FailureQ[result] || Lookup[options, Verification, Automatic] =!= "Numerical", result,
        numericalRepresentationUpgrade[group, accepted["CharacterData"]["IrrepIDs"], options]]
];
builderRepresentations[___] := makeFailure["InvalidRequest", "Expected an accepted Group and builder options."];
$BuilderEnrichments[ComputeRepresentations] = builderRepresentations;

(*
    Summary: One explicit representation mutation attempt inside an owned call, published as one generation.
    Parameters: group — live Group; spec — <|"Method" -> "Supplied" | "BasisChange" | "DerivedNative" |
        "Unitarize" | "TDiagonalize", "IrrepIDs", "Basis", "Payload" -> GAP request fields,
        "ReplaceActive" -> irrep IDs|>; options — validated settings; capabilities; call; local — call-owned
        source or None.
    Options/defaults: AttemptTimeLimit bounds the attempt.
    Returns: The same Group, or Failure (with PartialResult when a publication happened).
    Effects: Runs one GAP worker on the group's checkpoint (or a reconstruction), publishes the verified
        candidate with the replace-active IDs.
    Failures: GAP mutation failures (WrongCharacter outcomes as RepresentationMethodFailed,
        AtomicTransformFailed, InapplicableMethod), resource, storage and publication failures.
    Example: SetGroupRepresentation runs the Supplied method through this function.
    See also: runRepresentationMutation; publishRepresentationCandidates; GAP VVMF_Representations.
*)
representationMutationInCall[group_Group, spec_Association, options_Association, capabilities_Association,
    call_Association, local_ : None] := Module[{accepted, source, envelope, record, context, descriptor, plan, methodRequest,
        result, candidates, publication},
    accepted = groupData[group]; If[FailureQ[accepted], Return[accepted]];
    source = groupComputationSource[group, accepted, capabilities, call, local];
    If[FailureQ[source], Return[source]];
    If[source["Checkpoint"] === None,
        envelope = groupEnvelope[accepted]; If[FailureQ[envelope], Return[envelope]];
        source["Checkpoint"] = prepareGroupCheckpoint[accepted, envelope, options, capabilities, call];
        If[FailureQ[source["Checkpoint"]], Return[source["Checkpoint"]]]];
    record = checkpointRecord[source["Checkpoint"], capabilities]; If[FailureQ[record], Return[record]];
    context = <|"Options" -> options, "Capabilities" -> capabilities, "Directory" -> call["Directory"]|>;
    descriptor = <|"Operation" -> "Representations", "Method" -> spec["Method"], "Model" -> "Original",
        "RecoveryStrategy" -> "Native", "WorkKey" -> "Representations/" <> spec["Method"] <> "/Mutation", "Tier" -> 0,
        "Parallel" -> False, "MinCores" -> 1,
        "MemoryEstimate" -> Max[128*2^20, 3 record["WorkspaceArtifact"]["Bytes"]] +
            512 Max[Append[Select[accepted["CharacterData"]["Degrees"], IntegerQ], 1]]^4,
        "Availability" -> "Eligible", "Reason" -> None|>;
    plan = packJobBatches[{descriptor}, options]; If[FailureQ[plan], Return[plan]];
    If[plan["Batches"] === {}, Return[makeFailure["MemoryLimit", "The budget is below this mutation's admission estimate."]]];
    methodRequest = Join[<|"operation" -> "Representations", "stateID" -> accepted["StateID"],
        "generatorIdentity" -> accepted["GeneratorIdentity"], "stateGeneration" -> ToString[accepted["StateGeneration"] + 1],
        "construction" -> accepted["Construction"], "characterIdentity" -> accepted["CharacterData"]["Identity"],
        "evictionEpoch" -> ToString[accepted["RepresentationCache"]["Epoch"]],
        (* The requested T-phase order and convention are certified by the completion predicate too. *)
        "representationRequest" -> Join[<|"irrepIDs" -> spec["IrrepIDs"], "basis" -> spec["Basis"]|>,
            If[spec["Basis"] === "UnitaryTDiagonal", KeyTake[Lookup[spec, "Payload", <||>], {"phaseOrder", "phaseConvention"}], <||>]],
        "replaceActive" -> spec["ReplaceActive"], "force" -> True|>,
        If[options[AttemptTimeLimit] === Infinity, <||>, <|"softDeadlineMilliseconds" -> ToString[Floor[600 options[AttemptTimeLimit]]]|>],
        spec["Payload"]];
    result = acceptVerifiedWinner[runJobBatch[source["Checkpoint"], First[plan["Batches"]], methodRequest, context]];
    If[FailureQ[result], Return[result]];
    candidates = If[AssociationQ[result["Winner"]], {result["Winner"]}, result["Partials"]];
    If[candidates === {}, Return[makeFailure["RepresentationMethodFailed", "The mutation produced no verified result.",
        <|"Outcomes" -> result["Outcomes"]|>]]];
    publication = publishRepresentationCandidates[group, Append[#, "ReplaceActive" -> spec["ReplaceActive"]] & /@ candidates,
        context, KeyDrop[source, "Checkpoint"], result["Outcomes"]];
    Which[FailureQ[publication["Failure"]], publication["Failure"],
        publication["Retention"] =!= {}, Last[publication["Retention"]], True, group]
];
representationMutationInCall[___] := makeFailure["InvalidRequest", "Expected a live group, mutation and owned call."];

(*
    Summary: Own the resources of one explicit representation mutation, or reuse the builder's call.
    Parameters: group — live Group; spec — as representationMutationInCall; options — validated settings.
    Options/defaults: Active builder calls on the same group are reused privately.
    Returns: The same Group, or Failure.
    Effects: Probes GAP once, owns a checkpoint call and releases its workers, files and leases on every exit.
    Failures: Unknown groups, insufficient memory budget, unavailable GAP, mutation failures.
    Example: runRepresentationMutation[g, <|"Method" -> "Supplied", ...|>, options].
    See also: representationMutationInCall; runRepresentationEnrichment.
*)
runRepresentationMutation[group_Group, spec_Association, options_Association] :=
    withProgress[options, "RepresentationMutation", Function[Null, Module[{accepted, capabilities},
        accepted = groupData[group]; If[FailureQ[accepted], Return[accepted]];
        If[TrueQ[$ProgressActive], $ProgressPartialResult = group];
        If[options[MemoryBudget] < 128*2^20,
            Return[makeFailure["MemoryLimit", "The budget is below the initial admission estimate."]]];
        If[AssociationQ[$ActiveGroupCall] && Lookup[$ActiveGroupCall, "Group", None] === group,
            Return[representationMutationInCall[group, spec, options, $ActiveGroupCall["Capabilities"],
                $ActiveGroupCall["Call"], $ActiveGroupCall["Checkpoint"]]]];
        capabilities = CheckGAP[]; If[FailureQ[capabilities], Return[capabilities]];
        withCheckpointCall[Function[call, representationMutationInCall[group, spec, options, capabilities, call]]]
    ]]];
runRepresentationMutation[___] := makeFailure["InvalidRequest", "Expected a live group, mutation and options."];

(*
    Summary: Format an explicit command that computes the named irreps with one route.
    Parameters: ids — irrep IDs; method — representation route; limit — suggested AttemptTimeLimit.
    Remarks: Randomized routes (Dixon, DixonUnitary) get a RandomSeed derived from the IDs and route, so the
        retry does not replay the failed attempt's random choices, yet the command is reproducible.
    Options/defaults: None.
    Returns: The command as a string, with g standing for the group.
    Effects: Pure.
    Failures: None.
    Example: representationRetryCommand[{"c:irrep:2"}, "Dixon", 1800] mentions RepresentationMethod -> "Dixon".
    See also: runRepresentationRequest.
*)
representationRetryCommand[ids_List, method_String, limit_] := "ComputeGroupRepresentations[g, " <>
    ToString[ids, InputForm] <> ", RepresentationMethod -> " <> ToString[method, InputForm] <>
    ", AttemptTimeLimit -> " <> ToString[If[limit === Infinity, Infinity, Ceiling[limit]], InputForm] <>
    If[MemberQ[{"Dixon", "DixonUnitary"}, method],
        ", MethodData -> <|\"RandomSeed\" -> " <> ToString[1 + Mod[Hash[{ids, method}, "CRC32"], 2^28 - 1]] <> "|>", ""] <> "]";

(*
    Summary: Encode an explicit polynomial in roots of unity as a cyclotomic record without field computations.
    Parameters: value — exact expression; orders — candidate conductors in order.
    Options/defaults: None.
    Returns: Integer/rational/cyclotomic scalar record in the first listed conductor that is a multiple of the
        value's root orders (and of 4 when I occurs), or $Failed when the value is not such a polynomial.
    Effects: Pure.
    Failures: $Failed (the caller then uses the general membership test).
    Example: rootOfUnityEncoding[(Exp[2 Pi I/13] + Exp[-2 Pi I/13])/6, {52}]["rootOrder"] is 52.
    Remarks: Terms rational * Exp[2 Pi I a] (a rational), (-1)^r and Gaussian rational coefficients are read off
        as coefficients of powers of zeta_n; decodeScalar of the record is the value exactly, so no RootReduce,
        minimal polynomial or factorization is needed. A sum of 6 roots of unity of order 78 takes milliseconds
        here and minutes through the general test (VVMFUse note 3).
    See also: cyclotomicEncoding; encodeScalar.
*)
rootOfUnityEncoding[value_, orders_List] := Module[{e, phases, n, z, poly, target, coefficients},
    e = Expand[value /. Power[-1, r_Rational] :> Exp[I Pi r]];
    If[MatchQ[e, _Integer | _Rational], Return[encodeScalar[e]]];
    phases = Cases[e, Power[E, x_] :> x/(2 Pi I), {0, Infinity}];
    If[!AllTrue[phases, MatchQ[#, _Integer | _Rational] &], Return[$Failed]];
    n = LCM @@ Join[{4}, Denominator /@ phases];
    poly = Expand[e /. Power[E, x_] :> z^Mod[x/(2 Pi I) n, n] /. Complex[a_, b_] :> a + b z^(n/4)];
    If[!PolynomialQ[poly, z] || !AllTrue[Flatten[{CoefficientList[poly, z]}], MatchQ[#, _Integer | _Rational] &], Return[$Failed]];
    target = SelectFirst[orders, IntegerQ[#] && # > 0 && Divisible[#, n] &, None];
    If[target === None, Return[$Failed]];
    coefficients = ConstantArray[0, target];
    Do[With[{k = Mod[First[rule[[1]]] target/n, target]}, coefficients[[k + 1]] += rule[[2]]], {rule, CoefficientRules[poly, z]}];
    <|"type" -> "cyclotomic", "rootOrder" -> target,
        "coefficients" -> (encodeInteger /@ {Numerator[#], Denominator[#]} & /@ coefficients)|>
];

(*
    Summary: Encode an exact value in the first listed cyclotomic field that contains it.
    Parameters: value — exact number; orders — candidate conductors in order.
    Options/defaults: None.
    Returns: Integer/rational/cyclotomic scalar record, or $Failed.
    Effects: Pure.
    Failures: Non-algebraic values, values generating a non-normal field (never cyclotomic), degrees
        not dividing phi(n), or membership not established within 20 seconds per conductor.
    Example: cyclotomicEncoding[Sqrt[5], {20}]["type"] is "cyclotomic"; cyclotomicEncoding[2^(1/3), {60}] is $Failed.
    Remarks: A number lies in a cyclotomic field only if Q(x) is an abelian, in particular normal,
        extension whose degree divides phi(n); both conditions are checked exactly before ToNumberField.
    See also: encodeRepresentationMethodData; encodeScalar.
*)
cyclotomicEncoding[value_, orders_List] := Module[{reduced, variable, polynomial, degree, direct},
    If[!exactAlgebraicQ[value], Return[$Failed]];
    (* Fast path: an explicit polynomial in roots of unity is cyclotomic by construction. *)
    direct = rootOfUnityEncoding[value, orders];
    If[AssociationQ[direct], Return[direct]];
    reduced = RootReduce[value];
    If[MatchQ[reduced, _Integer | _Rational], Return[encodeScalar[reduced]]];
    polynomial = MinimalPolynomial[reduced, variable]; degree = Exponent[polynomial, variable];
    If[Length[Select[FactorList[polynomial, Extension -> reduced][[All, 1]], Exponent[#, variable] === 1 &]] =!= degree,
        Return[$Failed]];
    (* Conductors are tried in order and the first field containing the value wins; later (larger)
       conductors are never evaluated. *)
    Catch[
        Scan[If[Divisible[EulerPhi[#], degree],
            With[{encoded = TimeConstrained[encodeScalar[reduced, #], 20, $Failed]},
                If[!FailureQ[encoded] && encoded =!= $Failed, Throw[encoded, cyclotomicEncoding]]]] &, orders];
        $Failed,
        cyclotomicEncoding]
];

(*
    Summary: Encode public MethodData for the GAP adapters.
    Parameters: data — validated MethodData association; accepted — group snapshot.
    Options/defaults: None.
    Returns: GAP-encoded record (subgroupGenerators as stable-ID words, representation as exact scalar
        records, atlasName, representationNumber as a decimal string), or InvalidMethodData Failure.
    Effects: Pure.
    Failures: Words on unknown generators; a subgroup Representation whose matrix count differs from the
        subgroup generators, or whose entries are not cyclotomic numbers of a supported conductor.
    Example: <|"AtlasName" -> "A5"|> encodes to <|"atlasName" -> "A5"|>.
    Remarks: Entries are placed in the cyclotomic field of conductor k lcm(e, 4), e the group exponent,
        for the first k in {1, 2, 3, 5, 6, 10, 15, 30} that contains them (cyclotomicEncoding).
    See also: ComputeGroupRepresentations; GAP VVMF_MethodSubgroup.
*)
encodeRepresentationMethodData[data_Association, accepted_Association] := Module[
    {names, ids, result = <||>, words, exponent, matrices, encoded},
    names = Lookup[accepted["Generators"], "Name", {}]; ids = Lookup[accepted["Generators"], "ID", {}];
    If[KeyExistsQ[data, "SubgroupGenerators"],
        words = encodeWord[#, names] & /@ data["SubgroupGenerators"];
        If[AnyTrue[words, FailureQ], Return[makeFailure["InvalidMethodData", "A subgroup generator word is invalid."]]];
        result["subgroupGenerators"] = Map[{ids[[First[FirstPosition[names, First[#]]]]], Last[#]} &, words, {2}]];
    If[KeyExistsQ[data, "Representation"],
        matrices = repMatrices[data["Representation"]];
        If[FailureQ[matrices] || Length[matrices] =!= Length[data["SubgroupGenerators"]],
            Return[makeFailure["InvalidMethodData", "The subgroup representation needs one matrix per subgroup generator."]]];
        exponent = LCM @@ accepted["CharacterData"]["ClassOrders"];
        encoded = Map[cyclotomicEncoding[#, LCM[exponent, 4] {1, 2, 3, 5, 6, 10, 15, 30}] &, matrices, {3}];
        If[!FreeQ[encoded, $Failed], Return[makeFailure["InvalidMethodData", "Subgroup representation entries must be cyclotomic numbers."]]];
        result["representation"] = encoded];
    If[KeyExistsQ[data, "AtlasName"], result["atlasName"] = data["AtlasName"]];
    If[KeyExistsQ[data, "RepresentationNumber"], result["representationNumber"] = encodeInteger[data["RepresentationNumber"]]];
    If[KeyExistsQ[data, "RandomSeed"], result["randomSeed"] = encodeInteger[data["RandomSeed"]]];
    result
];
encodeRepresentationMethodData[___] := makeFailure["InvalidMethodData", "Expected MethodData and an accepted group."];

(*
    Summary: Resolve an irrep selector against the group's irrep IDs.
    Parameters: selector — All, one irrep (ID string or index in the group's irrep order) or a duplicate-free list of
        them; accepted — group snapshot.
    Options/defaults: None.
    Returns: List of irrep IDs, or InvalidIrrepID Failure.
    Effects: Pure.
    Failures: Unknown IDs, duplicates, empty lists or other values, before any computation.
    Example: irrepSelection[All, accepted] is accepted["CharacterData"]["IrrepIDs"].
    See also: ComputeGroupRepresentations.
*)
irrepSelection[selector_, accepted_Association] := Module[{all = accepted["CharacterData"]["IrrepIDs"], order, ids},
    order = Lookup[accepted, "IrrepOrder", all];
    ids = Which[selector === All, all, StringQ[selector] || IntegerQ[selector], {selector}, ListQ[selector], selector, True, $Failed];
    (* indices are positions in the irrep order (uxUpdatePlan.md 1.3) *)
    If[ListQ[ids], ids = Replace[ids, k_Integer :> If[1 <= k <= Length[order], order[[k]], k], {1}]];
    If[ids === $Failed || ids === {} || !AllTrue[ids, StringQ] || !DuplicateFreeQ[ids] || !SubsetQ[all, ids],
        makeFailure["InvalidIrrepID", "Expected All, an irrep ID of this group, or a duplicate-free list of them.",
            <|"Selector" -> selector|>], ids]
];

Options[ComputeGroupRepresentations] = Join[Options[RestoreGAPState],
    {Basis -> "Unitary", RepresentationMethod -> Automatic, MethodData -> Automatic, TPhaseOrder -> "Ascending",
        PhaseConvention -> None, UnitarizationMethod -> Automatic, WitnessVariant -> Automatic, Verification -> Automatic}];

(*
    Summary: The request fields of the T-phase options of a representation request.
    Parameters: options — validated ComputeGroupRepresentations or builder options.
    Options/defaults: None.
    Returns: <|"phaseOrder", "phaseConvention"|> for Basis -> "UnitaryTDiagonal", otherwise <||>.
    Effects: Pure.
    Failures: None.
    Example: representationPhaseFields[<|Basis -> "UnitaryTDiagonal", TPhaseOrder -> "Ascending", PhaseConvention -> None|>]
        is <|"phaseOrder" -> "Ascending", "phaseConvention" -> "None"|>.
    See also: ComputeGroupRepresentations; representationConvention.
*)
representationPhaseFields[options_Association] := If[options[Basis] === "UnitaryTDiagonal",
    <|"phaseOrder" -> options[TPhaseOrder], "phaseConvention" -> If[options[PhaseConvention] === None, "None", options[PhaseConvention]]|>,
    <||>];

(*
    Summary: Compute verified irreducible representation matrices and store them in the group.
    Status: Alpha.
    Signatures: ComputeGroupRepresentations[g]; ComputeGroupRepresentations[g, ids].
    Parameters: g — live Group; ids — All (default), one irrep ID or a duplicate-free list of IDs.
    Options/defaults: Basis -> "Unitary" ("General" accepts any verified basis; "UnitaryTDiagonal", which
        needs a modular assignment, also diagonalizes the assigned T in GAP); TPhaseOrder -> "Ascending"
        (T phases in [0, 1) nondecreasing) or "Unchanged", and PhaseConvention -> None or "FirstSRow" (first-row
        S entries real and nonnegative), both for "UnitaryTDiagonal" only: irreps whose diagonal T has another
        order or convention (for example from SL2Reps) are re-derived by the GAP T diagonalization; RepresentationMethod ->
        Automatic (unitary-first phases) or one route; MethodData -> Automatic or route data; the common
        GAP job options (StoreGAPState, GroupModel, AttemptTimeLimit, CoreBudget, MemoryBudget,
        ProgressFunction); Verification -> Automatic or "Exact" (GAP's VerifyRep: relators and traces), None (GAP
        matches the class traces only and stores each variant as an inert record with status "Unverified"; no GAP
        unitarization or T-diagonalization runs) or "Numerical" (as None, then each new variant is checked in Wolfram
        on N[] and re-stored at "Numerical", ValidateRepresentation's write-back).
    Returns: The same Group when every requested irrep has an active variant in the requested basis;
        otherwise a Failure with PartialResult (the group, which keeps every verified generation),
        RemainingIDs and Suggestions giving an explicit command for the remaining irreps.
    Effects: Runs GAP workers; each verified result is a new group generation. Already satisfied
        requests start no computation.
    Failures: Invalid selectors or options, and UnitaryTDiagonal without an assignment
        (MissingModularAssignment), fail before GAP starts; UnitaryConstructionUnavailable keeps verified
        general matrices as accepted partials; TDiagonalizationUnavailable keeps unitary matrices;
        MethodExhausted; resource, storage, cancellation.
    Example: ComputeGroupRepresentations[BuildGroup[CatalogueGroup["SymmetricGroup", 3],
        ComputeRepresentations -> False], Basis -> "General"] returns the group with three irreps.
    See also: GroupRepresentation; RepresentationData; runRepresentationRequest.
*)
ComputeGroupRepresentations[group_Group, selector : Except[_Rule | _RuleDelayed] : All, options : OptionsPattern[]] := Module[
    {effective, accepted, ids, methodData, result, upgraded},
    effective = resolveOperationOptions[ComputeGroupRepresentations, "ComputeGroupRepresentations", {options}];
    If[FailureQ[effective], Return[effective]];
    accepted = groupData[group]; If[FailureQ[accepted], Return[accepted]];
    ids = irrepSelection[selector, accepted]; If[FailureQ[ids], Return[ids]];
    If[effective[Basis] === "UnitaryTDiagonal" && !AssociationQ[accepted["ModularAssignment"]],
        Return[makeFailure["MissingModularAssignment",
            "Basis -> \"UnitaryTDiagonal\" requires a modular S,T assignment. Use AssignModularGenerators first."]]];
    methodData = If[effective[MethodData] === Automatic, None, encodeRepresentationMethodData[effective[MethodData], accepted]];
    If[FailureQ[methodData], Return[methodData]];
    result = runRepresentationEnrichment[group, Join[<|"irrepIDs" -> ids, "basis" -> effective[Basis]|>,
        representationPhaseFields[effective], If[methodData === None, <||>, <|"methodData" -> methodData|>],
        (* Verification "Numerical" or None: GAP matches traces only (methodOptionsPlan.md 2C.4, C7) *)
        If[MemberQ[{"Numerical", None}, effective[Verification]], <|"verify" -> "Traces"|>, <||>]], effective];
    If[FailureQ[result] || effective[Verification] =!= "Numerical", Return[result]];
    numericalRepresentationUpgrade[group, ids, effective]
];

(*
    Summary: Raise each unproved ("Unverified") active variant of the given irreps to "Numerical" after its numerical check
        (the second half of a Verification -> "Numerical" representation computation, methodOptionsPlan.md 2C.4).
    Parameters: group — live Group; ids — irrep IDs; options — validated options with StoreGAPState.
    Options/defaults: None.
    Returns: The group, or RepresentationVerificationFailed with PartialResult, the IrrepIDs that did not pass and their
        reports.
    Effects: One write-back generation per raised irrep (ValidateRepresentation[g, id]).
    Failures: RepresentationVerificationFailed.
    Example: after ComputeGroupRepresentations[g, Verification -> None], numericalRepresentationUpgrade[g, ids, opts] makes
        every active variant "Numerical".
    See also: ComputeGroupRepresentations; builderRepresentations; ValidateRepresentation.
*)
numericalRepresentationUpgrade[group_Group, ids_List, options_Association] := Module[{upgraded},
    upgraded = Map[Function[id, With[{entry = Lookup[groupData[group]["Representations"], id, <||>]},
            If[!StringQ[Lookup[entry, "ActiveVariant", None]] || variantVerificationStatus[entry["Variants"][entry["ActiveVariant"]]] =!= "Unverified",
                id -> True, id -> ValidateRepresentation[group, id, Verification -> "Numerical", StoreGAPState -> Lookup[options, StoreGAPState, False]]]]], ids];
    With[{failed = Select[Association[upgraded], FailureQ[#] || (AssociationQ[#] && !TrueQ[#["WrittenBack"]]) &]},
        If[failed === <||>, group, makeFailure["RepresentationVerificationFailed",
            "Some computed representations did not pass the numerical check; they stay stored as \"Unverified\".",
            <|"PartialResult" -> group, "IrrepIDs" -> Keys[failed], "Reports" -> failed|>]]]
];
ComputeGroupRepresentations[___] := makeFailure["InvalidInput", "Expected a live group, an optional irrep selector and options."];

(*
    Summary: Read the active representation of one irrep without starting a computation.
    Status: Alpha.
    Parameters: g — live Group; id — irrep ID string.
    Options/defaults: None.
    Returns: The active variant's Rep, Missing["NotComputed"] when the irrep has no active variant, or
        Failure for an unknown group or irrep ID.
    Effects: Pure read.
    Failures: InvalidIrrepID for IDs not in the character table.
    Example: GroupRepresentation[g, First[g["IrrepOrder"]]] is a Rep after ComputeGroupRepresentations[g].
    See also: RepresentationData; ComputeGroupRepresentations.
*)
GroupRepresentation[group_Group, id_String] := Module[{accepted, entry},
    accepted = groupData[group]; If[FailureQ[accepted], Return[accepted]];
    If[!MemberQ[accepted["CharacterData"]["IrrepIDs"], id],
        Return[makeFailure["InvalidIrrepID", "The irrep ID does not belong to this group.", <|"ID" -> id|>]]];
    entry = Lookup[accepted["Representations"], id, None];
    If[AssociationQ[entry] && StringQ[entry["ActiveVariant"]], entry["Variants"][entry["ActiveVariant"]]["Rep"],
        Missing["NotComputed"]]
];
GroupRepresentation[group_Group, k_Integer] := withIrreps[group, {k}, GroupRepresentation[group, #] &];
GroupRepresentation[___] := makeFailure["InvalidInput", "Expected a live group and an irrep ID."];

(*
    Summary: Read the stored representation data of one irrep.
    Status: Alpha.
    Parameters: g — live Group; id — irrep ID string.
    Options/defaults: None.
    Returns: <|"CharacterID", "Dimension", "GeneratorIdentity", "Variants", "ActiveVariant",
        "AcceptedPartial"|>; an irrep without data has empty Variants and Missing pointers.
    Effects: Pure read.
    Failures: Unknown group or irrep ID.
    Example: RepresentationData[g, id]["Variants"] lists every verified basis with its BasisProperties.
    See also: GroupRepresentation; decodeRepresentationData.
*)
RepresentationData[group_Group, id_String] := Module[{accepted, position},
    accepted = groupData[group]; If[FailureQ[accepted], Return[accepted]];
    position = FirstPosition[accepted["CharacterData"]["IrrepIDs"], id, None];
    If[position === None, Return[makeFailure["InvalidIrrepID", "The irrep ID does not belong to this group.", <|"ID" -> id|>]]];
    Lookup[accepted["Representations"], id, <|"CharacterID" -> id,
        "Dimension" -> accepted["CharacterData"]["Degrees"][[First[position]]],
        "GeneratorIdentity" -> accepted["GeneratorIdentity"], "Variants" -> <||>,
        "ActiveVariant" -> Missing["NotComputed"], "AcceptedPartial" -> Missing["NotComputed"]|>]
];
RepresentationData[group_Group, k_Integer] := withIrreps[group, {k}, RepresentationData[group, #] &];
RepresentationData[___] := makeFailure["InvalidInput", "Expected a live group and an irrep ID."];

True
