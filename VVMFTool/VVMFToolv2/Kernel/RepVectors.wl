(*
    :Title: Representation-valued vectors and their tensor products
    :Context: VVMFTool`Private`
    :Summary: Immutable RepVector values (ordered records of target irrep, components, contraction path and basis
        identity) bound to the frozen context they were made in; tensor products through CG duals with every
        copy and zero kept, left-associated paths and backward pruning to requested targets.
    :Responsibilities: makeVectorData, validateRepVector, tensorComponents, contractCG, joinVectorData,
        multiplyVectorPaths; MakeRepVector, VectorComponents, JoinRepVectors, EmptyRepVector,
        TensorProductVectors, CGPolynomialResult.
    :Dependencies: Representation.wl (freezeContext, resolveRepContext, contextDigest); CGData.wl, CGStore.wl
        (CGCoefficients); TensorCharacters.wl (characterPairProduct).
    :See Also: VVMFArch/step4Plan.md (RepVector, TensorProductVectors, CGPolynomialResult).
*)

(*
    Summary: Build a validated RepVector from a context and records.
    Parameters: context — RepresentationContext (frozen); records — list of <|"TargetID", "Components", "Path",
        "BasisID", "ChannelIDs"|> with an optional "Arithmetic"; labels — association of cosmetic labels.
    Options/defaults: None.
    Returns: RepVector[<|"SchemaVersion" -> 1, "Context" -> context, "ContextDigest", "Records", "Labels"|>]; every
        record carries "Arithmetic" -> "Exact" | "Numerical" (from the record, else "Numerical" exactly when its
        components contain approximate numbers).
    Effects: Pure.
    Failures: None (callers validate inputs).
    Example: makeVectorData[ctx, {}, <||>] is the additive zero of ctx.
    See also: validateRepVector; vectorRecordArithmetic.
*)
makeVectorData[context_RepresentationContext, records_List, labels_Association] := Module[{withArithmetic},
    withArithmetic = Map[If[KeyExistsQ[#, "Arithmetic"], #, Append[#, "Arithmetic" -> vectorRecordArithmetic[#["Components"]]]] &, records];
    RepVector[<|"SchemaVersion" -> 1,
        "Context" -> context, "ContextDigest" -> contextDigest[First[context]],
        (* every record carries its verification status (methodOptionsPlan.md 2C.2): a leaf takes its variant's and the
           group's, a product record the weakest of its factors and its CG target (multiplyVectorPaths) *)
        "Records" -> Map[If[KeyExistsQ[#, "VerificationStatus"], #, Append[#, "VerificationStatus" -> cgWeakestStatus[{
                variantVerificationStatus[cgVariant[First[context], #["TargetID"]]], groupVerificationStatus[First[context]],
                If[#["Arithmetic"] === "Numerical", "Numerical", "Exact"]}]]] &, withArithmetic],
        "Labels" -> labels|>]];

(* The verification status of a vector: the weakest of its records ("Exact" for the additive zero). *)
vectorVerificationStatus[RepVector[data_Association]] := If[data["Records"] === {}, "Exact",
    cgWeakestStatus[Lookup[#, "VerificationStatus", "Exact"] & /@ data["Records"]]];
vectorVerificationStatus[_] := "Unverified";

(*
    Summary: The arithmetic of vector components.
    Parameters: values — any expression.
    Options/defaults: None.
    Returns: "Numerical" when values contain an approximate number, else "Exact".
    Effects: Pure.
    Failures: None.
    Example: vectorRecordArithmetic[{x, 1.5 y}] is "Numerical".
    See also: makeVectorData; contractCG.
*)
vectorRecordArithmetic[values_] := If[FreeQ[values, _?InexactNumberQ], "Exact", "Numerical"];

(* A summary instead of the frozen context. *)
Format[RepVector[data_Association], StandardForm] := Interpretation[Row[{"RepVector[", Length[Lookup[data, "Records", {}]], " records: ",
    Short[Map[If[MatchQ[Lookup[data, "Context", None], _RepresentationContext], irrepPlainName[data["Context"], #], #] &, Lookup[Lookup[data, "Records", {}], "TargetID", {}]], 1], "]"}],
    RepVector[data]];

(*
    Summary: Validate a RepVector before use.
    Parameters: v — any expression.
    Options/defaults: None.
    Returns: The vector's data association, or InvalidRepVector/UnverifiedContext Failure.
    Effects: Pure.
    Failures: Wrong schema; a context that is not bound in this kernel or whose digest differs; records whose
        component count differs from the target dimension of the context's active variant, whose basis identity
        is not that variant's, or whose Arithmetic is not "Exact" or "Numerical".
    Example: a RepVector whose components were shortened by hand fails here.
    See also: makeVectorData.
*)
validateRepVector[RepVector[data_Association]] := Module[{snapshot},
    If[!SubsetQ[Keys[data], {"SchemaVersion", "Context", "ContextDigest", "Records", "Labels"}] || data["SchemaVersion"] =!= 1 ||
        Head[data["Context"]] =!= RepresentationContext || !ListQ[data["Records"]],
        Return[makeFailure["InvalidRepVector", "Malformed RepVector."]]];
    snapshot = resolveRepContext[data["Context"]];
    If[FailureQ[snapshot], Return[snapshot]];
    If[contextDigest[snapshot] =!= data["ContextDigest"], Return[makeFailure["InvalidRepVector", "The vector's context digest is inconsistent."]]];
    If[!AllTrue[data["Records"], Function[r, AssociationQ[r] && SubsetQ[Keys[r], {"TargetID", "Components", "Path", "BasisID", "ChannelIDs", "Arithmetic"}] &&
            MemberQ[{"Exact", "Numerical"}, r["Arithmetic"]] &&
            With[{variant = cgVariant[snapshot, r["TargetID"]]}, AssociationQ[variant] && ListQ[r["Components"]] &&
                Length[r["Components"]] === variant["Dimension"] && r["BasisID"] === variant["Identity"]]]],
        Return[makeFailure["InvalidRepVector", "A vector record disagrees with its context's representation."]]];
    data
];
validateRepVector[___] := makeFailure["InvalidRepVector", "Expected a RepVector."];

(*
    Summary: The frozen context of a group or context argument.
    Parameters: c — Group or RepresentationContext.
    Options/defaults: None.
    Returns: RepresentationContext, or Failure.
    Effects: Freezing a group registers its context binding.
    Failures: UnverifiedContext.
    Example: vectorContext[g] equals RepresentationContext[g] for an unchanged group.
    See also: MakeRepVector.
*)
vectorContext[group_Group] := freezeContext[group];
vectorContext[context_RepresentationContext] := With[{snapshot = resolveRepContext[context]}, If[FailureQ[snapshot], snapshot, context]];
vectorContext[___] := makeFailure["UnverifiedContext", "Expected a Group or a RepresentationContext."];

(*
    Summary: The option names a call supplies that the function does not declare.
    Parameters: f — function symbol with Options; supplied — the call's options (rules or lists of rules).
    Options/defaults: None.
    Returns: List of unsupported option names ({} when every option is declared).
    Effects: Pure.
    Failures: None.
    Example: unsupportedOptions[MakeRepVector, {Bogus -> 1}] is {Bogus}.
    See also: validateOptions.
*)
unsupportedOptions[f_Symbol, supplied_List] := Complement[Keys[Cases[Flatten[supplied], _Rule | _RuleDelayed]], Keys[Options[f]]];

Options[MakeRepVector] = {ComponentLabel -> "x"};

(*
    Summary: A representation-valued vector of one irrep.
    Parameters: c — Group or RepresentationContext; id — irrep ID; components — Automatic (inert components), a
        symbol a (components a[1], ..., a[dim], as v1's RepVec) or an explicit list of length dim(id) (numbers or symbolic
        expressions, already evaluated by the caller).
    Options/defaults: ComponentLabel "x" — cosmetic label of inert components.
    Returns: RepVector with one leaf record, or Failure.
    Effects: Automatic creates VectorComponent[vectorID, i] values with a fresh vector identity; no global symbol is
        defined or evaluated.
    Failures: UnverifiedContext; InvalidIrrep; MissingRepresentations (no accepted matrix variant); InvalidInput
        for a list of the wrong length, a System or package symbol other than Automatic, or a symbol a whose a[i] has a
        value.
    Example: VectorComponents[MakeRepVector[g, t, {x1, x2, x3}]][[1, "Components"]] is {x1, x2, x3};
        MakeRepVector[g, t, a] has the components {a[1], a[2], a[3]}.
    See also: VectorComponents; TensorProductVectors.
*)
MakeRepVector[c : (_Group | _RepresentationContext), id_String, components : Except[_Rule | _RuleDelayed] : Automatic, options : OptionsPattern[]] := Module[
    {label, context, snapshot, variant, values, vectorID},
    If[unsupportedOptions[MakeRepVector, {options}] =!= {}, Return[makeFailure["UnknownOption", "An option is not supported by this operation.",
        <|"Operation" -> "MakeRepVector", "Options" -> unsupportedOptions[MakeRepVector, {options}]|>]]];
    label = OptionValue[ComponentLabel];
    If[!StringQ[label] || StringLength[label] === 0, Return[makeFailure["InvalidOption", "ComponentLabel must be a nonempty string.", <|"Options" -> {ComponentLabel}|>]]];
    context = vectorContext[c]; If[FailureQ[context], Return[context]];
    snapshot = First[context];
    If[!MemberQ[snapshot["CharacterData"]["IrrepIDs"], id], Return[makeFailure["InvalidIrrep", "Unknown irrep ID.", <|"IrrepIDs" -> {id}|>]]];
    variant = cgVariant[snapshot, id];
    If[MissingQ[variant], Return[makeFailure["MissingRepresentations", "The irrep has no accepted matrices in this context.", <|"IrrepIDs" -> {id}|>]]];
    vectorID = "vector-" <> CreateUUID[];
    values = Which[components === Automatic, Table[VectorComponent[vectorID, i], {i, variant["Dimension"]}],
        ListQ[components] && Length[components] === variant["Dimension"], components,
        (* a user symbol a gives a[1], ..., a[dim] (v1 RepVec); System and package symbols are not names, and a symbol
           whose a[i] has a value is refused rather than mixing numbers into the components (review F1) *)
        MatchQ[components, _Symbol] && !StringStartsQ[Context[components], "System`" | "VVMFTool`"] &&
            MatchQ[Table[components[i], {i, variant["Dimension"]}], {HoldPattern[components][_Integer] ..}],
            Table[components[i], {i, variant["Dimension"]}],
        True, Return[makeFailure["InvalidInput", "Explicit components must be a symbol or a list of the irrep's dimension.",
            <|"Dimension" -> variant["Dimension"]|>]]];
    makeVectorData[context, {<|"TargetID" -> id, "Components" -> values, "Path" -> <|"Kind" -> "Leaf", "VectorID" -> vectorID|>,
        "BasisID" -> variant["Identity"], "ChannelIDs" -> {}|>}, <|vectorID -> label|>]
];
MakeRepVector[c : (_Group | _RepresentationContext), k_Integer, rest___] := withIrreps[c, {k}, MakeRepVector[c, #, rest] &];
MakeRepVector[___] := makeFailure["InvalidInput", "MakeRepVector expects a Group or RepresentationContext, an irrep ID, components and options."];

(*
    Summary: The ordered channel records of a RepVector.
    Parameters: v — RepVector.
    Options/defaults: None.
    Returns: List of <|"TargetID", "Components" (exact values in readable form), "Path", "ChannelIDs", "BasisID", "Arithmetic", "Target" (the irrep index),
        "TargetLabel" (user label, else index, as text)|>, or Failure.
    Effects: Pure.
    Failures: InvalidRepVector; UnverifiedContext.
    Example: a product of two triplets lists one record per target copy, zeros included.
    See also: MakeRepVector; TensorProductVectors.
*)
VectorComponents[v_RepVector] := With[{data = validateRepVector[v]}, If[FailureQ[data], data,
    Map[Join[#, <|"Components" -> readableExpression[#["Components"]], "Target" -> irrepIndexOf[data["Context"], #["TargetID"]],
        "TargetLabel" -> irrepPlainName[data["Context"], #["TargetID"]]|>] &, data["Records"]]]];
(* the stored records, canonical forms kept (internal callers: contractions) *)
vectorRecords[v_RepVector] := With[{data = validateRepVector[v]}, If[FailureQ[data], data, data["Records"]]];
VectorComponents[___] := makeFailure["InvalidInput", "VectorComponents expects a RepVector."];

(*
    Summary: Concatenate the records of compatible vectors.
    Parameters: vectors — nonempty list of RepVector values with the same frozen context.
    Options/defaults: None.
    Returns: RepVector, or Failure.
    Effects: Pure; equal or zero records are kept (no deduplication).
    Failures: InvalidInput for an empty list (no context is given; use EmptyRepVector); ContextMismatch.
    Example: JoinRepVectors[{v, v}] has twice v's records.
    See also: EmptyRepVector.
*)
JoinRepVectors[vectors_List] := joinVectorData[vectors];
JoinRepVectors[___] := makeFailure["InvalidInput", "JoinRepVectors expects a list of RepVector values."];

(*
    Summary: Concatenate validated vectors (JoinRepVectors' work).
    Parameters: vectors — list.
    Options/defaults: None.
    Returns: RepVector, or Failure.
    Effects: Pure.
    Failures: As JoinRepVectors.
    Example: joinVectorData[{EmptyRepVector[g], v}] has v's records.
    See also: JoinRepVectors.
*)
joinVectorData[vectors_List] := Module[{data},
    If[vectors === {}, Return[makeFailure["InvalidInput", "An empty join has no context; use EmptyRepVector[c]."]]];
    data = validateRepVector /@ vectors;
    If[AnyTrue[data, FailureQ], Return[FirstCase[data, _Failure]]];
    If[Length[DeleteDuplicates[Lookup[data, "ContextDigest"]]] > 1,
        Return[makeFailure["ContextMismatch", "The vectors belong to different frozen contexts."]]];
    makeVectorData[First[data]["Context"], Join @@ Lookup[data, "Records"], Join @@ Lookup[data, "Labels"]]
];

(*
    Summary: The additive zero vector of a context.
    Parameters: c — Group or RepresentationContext.
    Options/defaults: None.
    Returns: RepVector with no records, or Failure.
    Effects: Freezing a group registers its context.
    Failures: UnverifiedContext.
    Example: TensorProductVectors[g, {EmptyRepVector[g], v}] is the additive zero.
    See also: JoinRepVectors.
*)
EmptyRepVector[c : (_Group | _RepresentationContext)] := With[{context = vectorContext[c]},
    If[FailureQ[context], context, makeVectorData[context, {}, <||>]]];
EmptyRepVector[___] := makeFailure["InvalidInput", "EmptyRepVector expects a Group or RepresentationContext."];

(*
    Summary: Ordered component products of two component lists.
    Parameters: a, b — component lists.
    Options/defaults: None.
    Returns: Flatten[Outer[Times, a, b]] (entry (i-1) Length[b] + j is a_i b_j).
    Effects: Pure; ordinary commutative multiplication.
    Failures: None.
    Example: tensorComponents[{x, y}, {u, v}] is {x u, x v, y u, y v}.
    See also: contractCG.
*)
tensorComponents[a_List, b_List] := Flatten[Outer[Times, a, b]];

(*
    Summary: Contract a tensor-product component vector with every channel of one target.
    Parameters: channels — CG channel records of the target; left, right — vector records.
    Options/defaults: None.
    Returns: List of records <|"TargetID", "Components" -> W . (a (x) b), "Path", "BasisID", "ChannelIDs",
        "Arithmetic"|>, one per channel (zero components kept); Numerical when a factor or the CG dual is numerical.
    Effects: Pure.
    Failures: None.
    Example: equal symbolic triplets give a zero antisymmetric triplet component.
    Remarks: Components are expanded, so a zero combination of shared variables simplifies to 0.
    See also: multiplyVectorPaths.
*)
contractCG[channels_List, left_Association, right_Association, basisID_String] := Module[{product = tensorComponents[left["Components"], right["Components"]]},
    Map[<|"TargetID" -> #["TargetID"], "Components" -> Expand[#["Dual"] . product],
        "Path" -> <|"Kind" -> "Product", "Left" -> left["Path"], "Right" -> right["Path"], "ChannelID" -> #["ChannelID"]|>,
        "BasisID" -> basisID, "ChannelIDs" -> Join[left["ChannelIDs"], right["ChannelIDs"], {#["ChannelID"]}],
        "Arithmetic" -> If[MemberQ[{left["Arithmetic"], right["Arithmetic"]}, "Numerical"] || vectorRecordArithmetic[#["Dual"]] === "Numerical",
            "Numerical", "Exact"]|> &, channels]
];

(*
    Summary: StaleBasis failure when a group's active variants differ from a frozen context's on given irreps.
    Parameters: group — Group; context — the vectors' RepresentationContext; irrepIDs — irreps a product touches.
    Options/defaults: None.
    Returns: None when every listed irrep has the same variant (or none) in both, else a StaleBasis Failure
        listing the differing irreps; a freezeContext Failure is returned as is.
    Effects: Freezes the group's current state (no publication).
    Failures: StaleBasis; freezeContext failures.
    Example: after ChangeGroupRepBasis of a target triplet, staleBasisFailure[g, ctx, {two, three}] lists the triplet.
    Remarks: Identities, not context digests, are compared: CG publications advance the group's state generation
        without changing any basis. An irrep with matrices on the group but none in the context also differs.
    See also: multiplyVectorPaths; TensorProductVectors.
*)
staleBasisFailure[group_Group, context_RepresentationContext, irrepIDs_List] := Module[{live = freezeContext[group], stale},
    If[FailureQ[live], Return[live]];
    stale = Select[irrepIDs, cgVariant[First[live], #] =!= cgVariant[First[context], #] &];
    If[stale === {}, None, makeFailure["StaleBasis",
        "The group's active representations differ from the vectors' frozen context; use the vectors' RepresentationContext.",
        <|"IrrepIDs" -> stale, "Remedy" -> "TensorProductVectors[context, factors] with the context the vectors were made in."|>]]
];

(*
    Summary: Multiply vectors left-associatively, pruning channels that cannot reach the requested targets.
    Parameters: cgContext — Group or RepresentationContext used for CG coefficients; context — the vectors' frozen
        context; factors — validated vector data; targets — All or a list of final irrep IDs; options — CG options.
    Options/defaults: CG options as CGCoefficients.
    Returns: List of records, or Failure.
    Effects: CG computation (published on a group when compatible).
    Failures: CG failures; InvalidIrrep for unknown final targets; StaleBasis (cgContext is a group whose active
        variant of a factor, intermediate or target irrep differs from the vectors' context, or exists only on the group).
    Example: {t, t, t} restricted to the trivial irrep only contracts t (x) t into t at the second stage.
    Remarks: Stage k's allowed irreps are those of stage-k records with a character path to a final target; the
        CG call of each pair is restricted to the next stage's allowed targets, so no unneeded channel is computed.
        Equal (pair, targets) requests within one product are resolved once (a context call publishes nothing, so a
        repeated request would otherwise be solved again).
    See also: TensorProductVectors; planFusionPaths.
*)
multiplyVectorPaths[cgContext_, context_RepresentationContext, factors_List, targets_, options_List] := Module[
    {characters = First[context]["CharacterData"], irreps, allowed, current, n = Length[factors], wanted, failure = None, resolvedCG = <||>},
    wanted = If[targets === All, characters["IrrepIDs"], Flatten[{targets}]];
    If[!SubsetQ[characters["IrrepIDs"], wanted], Return[makeFailure["InvalidIrrep", "Unknown target irrep ID.", <|"IrrepIDs" -> Complement[wanted, characters["IrrepIDs"]]|>]]];
    irreps = DeleteDuplicates[Lookup[#["Records"], "TargetID", {}]] & /@ factors;
    (* Forward supports S_k, then backward allowed sets A_k. *)
    current = {irreps[[1]]};
    Do[AppendTo[current, DeleteDuplicates[Flatten[Outer[Keys[characterPairProduct[characters, #1, #2]] &, Last[current], irreps[[k]]]]]], {k, 2, n}];
    allowed = ConstantArray[{}, n]; allowed[[n]] = Intersection[current[[n]], wanted];
    Do[allowed[[k]] = Select[current[[k]], Function[r, AnyTrue[irreps[[k + 1]], IntersectingQ[Keys[characterPairProduct[characters, r, #]], allowed[[k + 1]]] &]]],
        {k, n - 1, 1, -1}];
    (* On a group, every irrep a planned path touches (factors, intermediate and final targets) must still have the
       variant frozen in the vectors' context; otherwise the records would carry the group's new basis. *)
    failure = If[Head[cgContext] === Group, staleBasisFailure[cgContext, context, DeleteDuplicates[Join[Flatten[irreps], Flatten[allowed]]]], None];
    If[failure =!= None, Return[failure]];
    current = Select[factors[[1]]["Records"], MemberQ[allowed[[1]], #["TargetID"]] &];
    Do[Module[{next = {}},
            Do[Module[{stageTargets = Select[allowed[[k]], KeyExistsQ[characterPairProduct[characters, left["TargetID"], right["TargetID"]], #] &], cg},
                    If[stageTargets === {}, Continue[]];
                    (* One CG resolution per distinct (pair, targets) request of the product. *)
                    With[{requestKey = {left["TargetID"], right["TargetID"], stageTargets}},
                        If[!KeyExistsQ[resolvedCG, requestKey],
                            resolvedCG[requestKey] = CGCoefficients[cgContext, {left["TargetID"], right["TargetID"]}, stageTargets, Sequence @@ options,
                                (* the caller's Verification comes first; otherwise plain Automatic, never the session's CG
                                   default (2C.4; family defaults are 2D) *)
                                Verification -> Automatic]];
                        cg = resolvedCG[requestKey]];
                    If[FailureQ[cg], failure = cg; Break[]];
                    (* a product record is served at the weakest of its factors and its CG target (2C.2) *)
                    next = Join[next, Flatten[Map[Function[target, With[{status = cgWeakestStatus[{Lookup[left, "VerificationStatus", "Exact"],
                            Lookup[right, "VerificationStatus", "Exact"], First[cg]["Provenance"][target]["Verification"]}]},
                        Append[#, "VerificationStatus" -> status] & /@ contractCG[cgTargetChannels[First[cg], target], left, right, First[cg]["TargetIdentities"][target]]]],
                        stageTargets], 1]]],
                {left, current}, {right, Select[factors[[k]]["Records"], MemberQ[irreps[[k]], #["TargetID"]] &]}];
            If[failure =!= None, Break[]];
            current = next],
        {k, 2, n}];
    If[failure =!= None, failure, current]
];

Options[TensorProductVectors] = Append[cgDerivedOptions[], TargetIrreps -> All];

(*
    Summary: Products of representation-valued vectors through CG duals.
    Parameters: c — Group or RepresentationContext; factors — list of RepVector values (same frozen context).
    Options/defaults: TargetIrreps All; CG options (Method, Normalization, ...) as CGCoefficients.
    Returns: RepVector, or Failure.
    Effects: May compute and publish CG coefficients on a compatible group.
    Failures: ContextMismatch (factors from different contexts); StaleBasis (c is a group whose active variant of
        any factor, intermediate or target irrep differs from the vectors' frozen variant — use the vectors' context);
        CG failures.
    Example: TensorProductVectors[g, {v, w}, TargetIrreps -> t] lists both copies of t for A4 triplets.
    Remarks: {} gives the tensor unit (one trivial record with component 1); an additive-zero factor gives the
        additive zero; one factor gives its records of the selected targets. Products are left-associated and
        the path records every contraction; no factor is swapped. Components multiply commutatively (no Grassmann
        semantics).
    See also: MakeRepVector; CGPolynomialResult; multiplyVectorPaths.
*)
(* one note line per distinct note for the whole product, not one per inner CG call (cgCallNotice) *)
TensorProductVectors[c : (_Group | _RepresentationContext), factors_List, options : OptionsPattern[]] :=
    If[unsupportedOptions[TensorProductVectors, {options}] =!= {},
        makeFailure["UnknownOption", "An option is not supported by this operation.",
            <|"Operation" -> "TensorProductVectors", "Options" -> unsupportedOptions[TensorProductVectors, {options}]|>],
        Block[{$cgNoticesShown = If[ListQ[$cgNoticesShown], $cgNoticesShown, {}]}, tensorProductVectorsWork[c, factors, options]]];
tensorProductVectorsWork[c : (_Group | _RepresentationContext), factors_List, options : OptionsPattern[TensorProductVectors]] := Module[
    {targets = OptionValue[TensorProductVectors, {options}, TargetIrreps], cgOptions, context, data, snapshot, trivial, records, cgContext, stale},
    If[!(targets === All || StringQ[targets] || IntegerQ[targets] || (ListQ[targets] && AllTrue[targets, StringQ[#] || IntegerQ[#] &])),
        Return[makeFailure["InvalidOption", "TargetIrreps must be All, an irrep (index or ID) or a list.", <|"Options" -> {TargetIrreps}|>]]];
    targets = resolveIrrepArguments[c, targets]; If[FailureQ[targets], Return[targets]];
    cgOptions = FilterRules[{options}, Except[TargetIrreps]];
    data = validateRepVector /@ factors;
    If[AnyTrue[data, FailureQ], Return[FirstCase[data, _Failure]]];
    If[data =!= {} && Length[DeleteDuplicates[#["ContextDigest"] & /@ data]] > 1,
        Return[makeFailure["ContextMismatch", "The factors belong to different frozen contexts."]]];
    context = If[data === {}, vectorContext[c], First[data]["Context"]];
    If[FailureQ[context], Return[context]];
    snapshot = First[context];
    (* A group argument must still carry the vectors' frozen variants; otherwise its new basis cannot be used. *)
    stale = If[Head[c] === Group && data =!= {}, staleBasisFailure[c, context, DeleteDuplicates[Flatten[Lookup[#["Records"], "TargetID", {}] & /@ data]]], None];
    If[stale =!= None, Return[stale]];
    cgContext = If[Head[c] === Group && data =!= {}, c,
        If[Head[c] === RepresentationContext && data =!= {} && contextDigest[resolveRepContext[c]] =!= First[data]["ContextDigest"],
            Return[makeFailure["ContextMismatch", "The vectors were made in another context."]], c]];
    If[data === {},
        trivial = snapshot["CharacterData"]["TrivialIrrepID"];
        If[!StringQ[trivial], Return[makeFailure["InvalidCharacters", "The character table has no trivial irrep."]]];
        If[MissingQ[cgVariant[snapshot, trivial]], Return[makeFailure["MissingRepresentations", "The trivial irrep has no stored matrices.", <|"IrrepIDs" -> {trivial}|>]]];
        Return[makeVectorData[context, If[targets === All || MemberQ[Flatten[{targets}], trivial],
            {<|"TargetID" -> trivial, "Components" -> {1}, "Path" -> <|"Kind" -> "Unit"|>, "BasisID" -> cgVariant[snapshot, trivial]["Identity"], "ChannelIDs" -> {}|>}, {}],
            <||>]]];
    If[AnyTrue[data, #["Records"] === {} &], Return[makeVectorData[context, {}, <||>]]];
    records = If[Length[data] === 1, Select[First[data]["Records"], targets === All || MemberQ[Flatten[{targets}], #["TargetID"]] &],
        multiplyVectorPaths[cgContext, context, data, targets, cgOptions]];
    If[FailureQ[records], Return[records]];
    makeVectorData[context, records, Join @@ Lookup[data, "Labels"]]
];
TensorProductVectors[___] := makeFailure["InvalidInput", "TensorProductVectors expects a Group or RepresentationContext, a list of RepVector values and options."];

Options[CGPolynomialResult] = Join[cgDerivedOptions[], {ComponentLists -> Automatic, ComponentLabel -> "x"}];

(*
    Summary: Every copy of one target in the product of two irreps, as polynomials in vector components.
    Parameters: c — Group or RepresentationContext; pair — {p, q}; target — irrep ID.
    Options/defaults: ComponentLists Automatic (distinct inert vectors) or {listA, listB} (explicit, possibly equal);
        ComponentLabel; CG options.
    Returns: RepVector whose records are all copies of the target (zero polynomials kept), or Failure.
    Effects: As TensorProductVectors.
    Failures: InvalidOption for malformed ComponentLists; MakeRepVector and TensorProductVectors failures.
    Example: CGPolynomialResult[g, {t, t}, t, ComponentLists -> {{x1, x2, x3}, {x1, x2, x3}}] has a zero antisymmetric record.
    Remarks: No copy is chosen silently; Stage 5 selects channels explicitly.
    See also: TensorProductVectors; MakeRepVector.
*)
CGPolynomialResult[c : (_Group | _RepresentationContext), pair : {_String, _String}, target_String, options : OptionsPattern[]] := Module[
    {lists, label, v, w},
    If[unsupportedOptions[CGPolynomialResult, {options}] =!= {}, Return[makeFailure["UnknownOption", "An option is not supported by this operation.",
        <|"Operation" -> "CGPolynomialResult", "Options" -> unsupportedOptions[CGPolynomialResult, {options}]|>]]];
    {lists, label} = {OptionValue[ComponentLists], OptionValue[ComponentLabel]};
    (* each entry a list of components or a symbol naming them (a -> a[1], ..., as MakeRepVector; v1 rep1Name) *)
    If[!(lists === Automatic || (ListQ[lists] && Length[lists] === 2 && AllTrue[lists, ListQ[#] || MatchQ[#, _Symbol] &])),
        Return[makeFailure["InvalidOption", "ComponentLists must be Automatic or {a, b} (component lists or symbols).", <|"Options" -> {ComponentLists}|>]]];
    v = MakeRepVector[c, pair[[1]], If[lists === Automatic, Automatic, lists[[1]]], ComponentLabel -> label];
    If[FailureQ[v], Return[v]];
    w = MakeRepVector[First[v]["Context"], pair[[2]], If[lists === Automatic, Automatic, lists[[2]]], ComponentLabel -> label];
    If[FailureQ[w], Return[w]];
    TensorProductVectors[c, {v, w}, TargetIrreps -> {target}, Sequence @@ FilterRules[{options}, Options[CGCoefficients]]]
];
CGPolynomialResult[c : (_Group | _RepresentationContext), pair : {(_Integer | _String), (_Integer | _String)}, target : (_Integer | _String), rest___] /; irrepIntegerQ[{pair, target}] :=
    withIrreps[c, {pair, target}, CGPolynomialResult[c, #1, #2, rest] &];
CGPolynomialResult[___] := makeFailure["InvalidInput", "CGPolynomialResult expects a Group or RepresentationContext, a pair of irrep IDs, a target and options."];

True
