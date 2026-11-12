(*
    :Title: Character-only tensor decomposition
    :Context: VVMFTool`Private`
    :Summary: Exact multiplicities of irreducible characters in tensor products, computed from the accepted
        character table alone (no matrices, no GAP), with backwards-pruned fusion paths for selected targets.
    :Responsibilities:
        - characterFieldData: exact coordinates of every character value in the cyclotomic field Q(zeta_n),
          n the lcm of the class orders, memoized by character identity.
        - characterPairProduct: exact pair multiplicities in Q[z]/Phi_n, memoized by unordered pair.
        - tensorMultiplicities / planFusionPaths: sparse left-associated folding and backwards pruning.
        - TensorDecomposition, TensorMultiplicity, TensorIrrepList.
    :Dependencies: Diagnostics.wl; GroupObject.wl (groupData); Representation.wl (resolveRepContext).
    :See Also: VVMFArch/step4Plan.md; VVMFArch/implementation/step4Status.md.
*)

(* Kernel-local memo tables: character identity -> field data; {identity, p, q} (p <= q) -> multiplicities.
   They hold pure functions of the accepted character table, so they are never invalidated by basis or
   order changes and are not part of any group's mutable state. *)
If[!AssociationQ[$CharacterFieldCache], $CharacterFieldCache = <||>];
If[!AssociationQ[$TensorCharacterCache], $TensorCharacterCache = <||>];

(*
    Summary: Character data and presentation order of a group or bound context.
    Parameters: context — live Group or RepresentationContext.
    Options/defaults: None.
    Returns: <|"CharacterData", "IrrepOrder", "StateID"|>, or Failure.
    Effects: Resolving a Group freezes nothing; a context must be bound in this kernel.
    Failures: UnverifiedContext; CharactersUnavailable when the table is absent or partial.
    Example: tensorCharacterSource[g]["IrrepOrder"] is g["IrrepOrder"].
    Remarks: A context has no presentation order of its own; it uses the character-table row order.
    See also: resolveRepContext; groupData.
*)
tensorCharacterSource[context : (_Group | _RepresentationContext)] := Module[{data, characters, order},
    data = If[Head[context] === Group, groupData[context], resolveRepContext[context]];
    If[FailureQ[data], Return[data]];
    characters = data["CharacterData"];
    If[!AssociationQ[characters] || Length[characters["IrrepIDs"]] =!= Length[characters["ClassIDs"]],
        Return[makeFailure["CharactersUnavailable", "Tensor decomposition needs the complete character table."]]];
    (* a context presents its live group's order (uxUpdatePlan.md 1.1) *)
    order = If[Head[context] === Group, data["IrrepOrder"], Replace[irrepOrder[context], _Failure -> characters["IrrepIDs"]]];
    <|"CharacterData" -> characters, "IrrepOrder" -> order,
        "StateID" -> If[Head[context] === Group, data["StateID"], data["GroupIdentity"]]|>
];
tensorCharacterSource[___] := makeFailure["UnverifiedContext", "Expected a Group or a RepresentationContext."];

(*
    Summary: Exact coordinates of an algebraic number in the power basis of Q(zeta_o).
    Parameters: v — exact character value; o — the order of the class element (v lies in Q(zeta_o)).
    Options/defaults: None.
    Returns: Integer list c of length EulerPhi[o] with v == Sum c[[k+1]] Exp[2 Pi I k/o]; {"Monomial", k} when
        v is the root of unity Exp[2 Pi I k/o]; or $Failed.
    Effects: Pure.
    Failures: $Failed when no small integer relation is found or the exact check fails.
    Example: cyclotomicCoordinates[1 + Exp[2 Pi I/5], 5] is {1, 1, 0, 0}; cyclotomicCoordinates[Exp[2 Pi I/3], 3]
        is {"Monomial", 1}.
    Remarks: Character values are algebraic integers with small coordinates; an integer relation among the
        numerical basis and v proposes them (LatticeReduce at 120 digits), and one exact RootReduce of the
        difference accepts them. The power basis k < EulerPhi[o] is a Q-basis, so the coordinates are unique.
        ToNumberField is avoided: it took minutes for order 25.
    See also: characterFieldData.
*)
cyclotomicCoordinates[v_, o_Integer?Positive] := Module[{phi = EulerPhi[o], basis, value, scale, lattice, row, c},
    If[MatchQ[v, _Integer | _Rational], Return[If[IntegerQ[v], Join[{v}, ConstantArray[0, phi - 1]], $Failed]]];
    (* A single root of unity (every value of a linear character) is placed by its certified phase. *)
    With[{r = If[Abs[Abs[N[v, 30]] - 1] < 10^-20, certifiedRootOfUnityPhase[v, o], $Failed]},
        If[r =!= $Failed, Return[{"Monomial", r o}]]];
    basis = N[Exp[2 Pi I Range[0, phi - 1]/o], 120];
    value = N[v, 120];
    If[Precision[value] < 60, Return[$Failed]];
    scale = 10^50;
    lattice = Join[
        MapThread[Join[UnitVector[phi + 1, #1], Round[scale {Re[#2], Im[#2]}]] &, {Range[phi], basis}],
        {Join[UnitVector[phi + 1, phi + 1], Round[-scale {Re[value], Im[value]}]]}];
    row = SelectFirst[LatticeReduce[lattice], Abs[#[[phi + 1]]] === 1 && Max[Abs[#[[phi + 2 ;;]]]] <= phi + 2 &, None];
    If[row === None, Return[$Failed]];
    c = row[[1 ;; phi]] row[[phi + 1]];
    If[Quiet[TimeConstrained[RootReduce[v - c . Exp[2 Pi I Range[0, phi - 1]/o]], 30, $Failed]] === 0, c, $Failed]
];
cyclotomicCoordinates[___] := $Failed;

(*
    Summary: The character table as polynomials in z = Exp[2 Pi I/n] reduced modulo Cyclotomic[n, z].
    Parameters: characters — accepted complete CharacterData.
    Options/defaults: None.
    Returns: <|"FieldOrder" -> n, "Values" -> rows of reduced polynomials in the private symbol fieldZ,
        "ConjugateValues" -> the complex conjugates|>, or Failure.
    Effects: Memoized by the character identity in $CharacterFieldCache.
    Failures: InvalidCharacters when a value cannot be placed in its class's cyclotomic field.
    Example: for C3, characterFieldData[ch]["Values"] contains fieldZ and fieldZ^2 (n = 3).
    See also: cyclotomicCoordinates; characterPairProduct.
*)
characterFieldData[characters_Association] := Module[{key = characters["Identity"], n, polys, failed = False},
    If[KeyExistsQ[$CharacterFieldCache, key], Return[$CharacterFieldCache[key]]];
    n = LCM @@ characters["ClassOrders"];
    polys = Table[Module[{o = characters["ClassOrders"][[c]], v = characters["Values"][[r, c]], coordinates},
            coordinates = cyclotomicCoordinates[v, o];
            Which[coordinates === $Failed, failed = True; 0,
                MatchQ[coordinates, {"Monomial", _Integer}],
                PolynomialRemainder[fieldZ^(Last[coordinates] n/o), Cyclotomic[n, fieldZ], fieldZ],
                True, PolynomialRemainder[coordinates . (fieldZ^(# n/o) & /@ Range[0, Length[coordinates] - 1]), Cyclotomic[n, fieldZ], fieldZ]]],
        {r, Length[characters["IrrepIDs"]]}, {c, Length[characters["ClassIDs"]]}];
    If[failed, Return[makeFailure["InvalidCharacters", "A character value is not an algebraic integer of its class's cyclotomic field."]]];
    $CharacterFieldCache[key] = <|"FieldOrder" -> n, "Values" -> polys,
        "ConjugateValues" -> Map[PolynomialRemainder[Expand[# /. fieldZ -> fieldZ^(n - 1)], Cyclotomic[n, fieldZ], fieldZ] &, polys, {2}]|>
];
characterFieldData[___] := makeFailure["InvalidCharacters", "Expected character data."];

(*
    Summary: Exact multiplicities of every irreducible character in chi_p chi_q.
    Parameters: characters — complete CharacterData; p, q — irrep IDs of that table.
    Options/defaults: None.
    Returns: Association irrepID -> positive Integer (sparse, character-table order), or Failure.
    Effects: Memoized by character identity and the unordered pair in $TensorCharacterCache.
    Failures: InvalidCharacters for non-integer or negative multiplicities, or a dimension mismatch
        (corrupted data); InvalidIrrep for unknown IDs.
    Example: for A4's triplet t, characterPairProduct[ch, t, t] has t -> 2.
    Remarks: m_r = (1/|G|) Sum_c |c| chi_p(c) chi_q(c) conj(chi_r(c)) evaluated in Q[z]/Phi_n, so every
        multiplicity is decided exactly.
    See also: tensorMultiplicities; characterFieldData.
*)
characterPairProduct[characters_Association, p_String, q_String] := Module[
    {ids = characters["IrrepIDs"], key, field, n, i, j, product, multiplicities, order},
    If[!MemberQ[ids, p] || !MemberQ[ids, q], Return[makeFailure["InvalidIrrep", "Unknown irrep ID.", <|"IrrepIDs" -> Complement[{p, q}, ids]|>]]];
    key = {characters["Identity"], Sort[{p, q}]};
    If[KeyExistsQ[$TensorCharacterCache, key], Return[$TensorCharacterCache[key]]];
    field = characterFieldData[characters];
    If[FailureQ[field], Return[field]];
    n = field["FieldOrder"]; order = Total[characters["ClassSizes"]];
    {i, j} = First[FirstPosition[ids, #]] & /@ {p, q};
    product = MapThread[PolynomialRemainder[Expand[#1 #2], Cyclotomic[n, fieldZ], fieldZ] &, {field["Values"][[i]], field["Values"][[j]]}];
    multiplicities = PolynomialRemainder[Expand[#], Cyclotomic[n, fieldZ], fieldZ] / order & /@
        (field["ConjugateValues"] . (characters["ClassSizes"] product));
    If[!AllTrue[multiplicities, IntegerQ[#] && # >= 0 &] ||
        multiplicities . characters["Degrees"] =!= characters["Degrees"][[i]] characters["Degrees"][[j]],
        Return[makeFailure["InvalidCharacters", "The character table gives a non-integer, negative or dimension-inconsistent tensor multiplicity.",
            <|"Pair" -> {p, q}|>]]];
    $TensorCharacterCache[key] = Select[AssociationThread[ids, multiplicities], # > 0 &]
];
characterPairProduct[___] := makeFailure["InvalidInput", "Expected character data and two irrep IDs."];

(*
    Summary: Validate tensor factor IDs against a character table.
    Parameters: characters — CharacterData; ids — the factor list.
    Options/defaults: None.
    Returns: True or Failure.
    Effects: Pure.
    Failures: InvalidInput for a non-list or non-string entries; InvalidIrrep for unknown IDs.
    Example: tensorFactorsQ[ch, {"bogus"}] is Failure["InvalidIrrep", ...].
    See also: tensorMultiplicities.
*)
tensorFactorsQ[characters_Association, ids_] := Which[
    !ListQ[ids] || !AllTrue[ids, StringQ], makeFailure["InvalidInput", "Tensor factors must be a list of irrep ID strings."],
    !SubsetQ[characters["IrrepIDs"], ids], makeFailure["InvalidIrrep", "Unknown irrep ID.", <|"IrrepIDs" -> Complement[ids, characters["IrrepIDs"]]|>],
    True, True];

(*
    Summary: Multiplicities of every irrep in the ordered tensor product of the listed factors.
    Parameters: characters — complete CharacterData; ids — list of irrep IDs (possibly empty or repeated).
    Options/defaults: None.
    Returns: Association of all irrep IDs (character-table order) -> nonnegative Integer, or Failure.
    Effects: Fills the pair memo.
    Failures: As tensorFactorsQ and characterPairProduct; a failed dimension check.
    Example: tensorMultiplicities[ch, {}] maps the trivial irrep to 1 and every other irrep to 0.
    Remarks: The empty product is one copy of the recorded TrivialIrrepID, whatever the row order. Folding is
        left-associated and sparse: only irreps already present are multiplied by the next factor.
    See also: characterPairProduct; planFusionPaths.
*)
tensorMultiplicities[characters_Association, ids_] := Module[{check, current, next, degrees},
    check = tensorFactorsQ[characters, ids];
    If[FailureQ[check], Return[check]];
    If[MissingQ[characters["TrivialIrrepID"]] || !StringQ[characters["TrivialIrrepID"]],
        Return[makeFailure["InvalidCharacters", "The character table has no trivial irrep ID."]]];
    current = <|characters["TrivialIrrepID"] -> 1|>;
    check = Catch[Do[
        next = <||>;
        Do[With[{pair = characterPairProduct[characters, r, f]},
            If[FailureQ[pair], Throw[pair, "TensorFailure"]];
            KeyValueMap[(next[#1] = Lookup[next, #1, 0] + current[r] #2) &, pair]], {r, Keys[current]}];
        current = next,
        {f, ids}], "TensorFailure"];
    If[FailureQ[check], Return[check]];
    degrees = AssociationThread[characters["IrrepIDs"], characters["Degrees"]];
    If[Total[KeyValueMap[#2 degrees[#1] &, current]] =!= Times @@ Lookup[degrees, ids],
        Return[makeFailure["InvalidCharacters", "The tensor dimension does not equal the dimension sum."]]];
    AssociationThread[characters["IrrepIDs"], Lookup[current, characters["IrrepIDs"], 0]]
];
tensorMultiplicities[___] := makeFailure["InvalidInput", "Expected character data and a factor list."];

(*
    Summary: Left-associated fusion paths of a factor list that can reach the selected final irreps.
    Parameters: characters — complete CharacterData; ids — factor list; targets — All or a list of irrep IDs.
    Options/defaults: None.
    Returns: <|"Factors" -> ids, "Targets" -> targets, "Stages" -> {<|"Index" -> k, "Allowed" -> irreps after
        k factors that lead to a target, "Transitions" -> {{r, f, s, m}...}|>...}|>, or Failure. Stage k >= 2
        lists the transitions r (x) f_k -> s with multiplicity m whose s is allowed at stage k.
    Effects: Fills the pair memo.
    Failures: As tensorMultiplicities; InvalidIrrep for unknown targets.
    Example: for A4 {t, t, t} with targets {trivial}, stage 2 allows only t (the singlets cannot reach trivial).
    Remarks: Forward supports are computed first; the backward pass keeps only irreps with a transition into
        the next allowed set, so vector products never compute channels that cannot reach a requested irrep.
    See also: tensorMultiplicities; multiplyVectorPaths.
*)
planFusionPaths[characters_Association, ids_, targets_] := Module[{check, wanted, supports = {}, current, transitions = {}, allowed, stages},
    check = tensorFactorsQ[characters, ids];
    If[FailureQ[check], Return[check]];
    wanted = If[targets === All, characters["IrrepIDs"], targets];
    If[!ListQ[wanted] || !SubsetQ[characters["IrrepIDs"], wanted],
        Return[makeFailure["InvalidIrrep", "Unknown target irrep ID.", <|"IrrepIDs" -> If[ListQ[wanted], Complement[wanted, characters["IrrepIDs"]], wanted]|>]]];
    If[ids === {}, Return[<|"Factors" -> {}, "Targets" -> wanted, "Stages" -> {}|>]];
    current = {First[ids]}; AppendTo[supports, current];
    check = Catch[Do[Module[{step = {}},
        Do[With[{pair = characterPairProduct[characters, r, ids[[k]]]},
            If[FailureQ[pair], Throw[pair, "TensorFailure"]];
            KeyValueMap[AppendTo[step, {r, ids[[k]], #1, #2}] &, pair]], {r, current}];
        AppendTo[transitions, step];
        current = DeleteDuplicates[step[[All, 3]]];
        AppendTo[supports, current]], {k, 2, Length[ids]}], "TensorFailure"];
    If[FailureQ[check], Return[check]];
    allowed = ConstantArray[{}, Length[ids]];
    allowed[[-1]] = Intersection[supports[[-1]], wanted];
    Do[allowed[[k]] = DeleteDuplicates[Select[transitions[[k]], MemberQ[allowed[[k + 1]], #[[3]]] &][[All, 1]]], {k, Length[ids] - 1, 1, -1}];
    stages = Table[<|"Index" -> k, "Allowed" -> Select[characters["IrrepIDs"], MemberQ[allowed[[k]], #] &],
        "Transitions" -> If[k === 1, {}, Select[transitions[[k - 1]], MemberQ[allowed[[k - 1]], #[[1]]] && MemberQ[allowed[[k]], #[[3]]] &]]|>,
        {k, Length[ids]}];
    <|"Factors" -> ids, "Targets" -> wanted, "Stages" -> stages|>
];
planFusionPaths[___] := makeFailure["InvalidInput", "Expected character data, a factor list and targets."];

Options[TensorDecomposition] = Options[TensorIrrepList] = {IrrepForm -> "Index", IncludeZeros -> False};

(*
    Summary: Multiplicity of the irreps in a tensor product of irreps.
    Parameters: c — Group or RepresentationContext; factors — list of irreps (indices in the irrep order, or IDs; empty:
        the tensor unit).
    Options/defaults: IrrepForm -> "Index" (keys are irrep indices; "ID": irrep IDs; "Label": the irreps' labels, user
        label > automatic label > index); IncludeZeros -> False (irreps that do not occur are dropped).
    Returns: Association irrep -> positive Integer in the presentation order (with IncludeZeros -> True every irrep,
        zeros kept), or Failure. IrrepForm -> "ID" with IncludeZeros -> True is the result before the UX update.
    Effects: No GAP, no matrices, no change to the group; fills the kernel-local character-product memo.
    Failures: UnverifiedContext; CharactersUnavailable; InvalidIrrep; InvalidCharacters; InvalidOption.
    Example: TensorDecomposition[g, {7, 7}] is <|4 -> 1, 5 -> 1, 6 -> 1, 7 -> 2|>-like for T' (3 x 3 = 1 + 1' + 1'' + 2 3).
    See also: TensorMultiplicity; TensorIrrepList; TensorDecompositionView.
*)
TensorDecomposition[context : (_Group | _RepresentationContext), factors_List, options : OptionsPattern[]] := Module[{effective, result},
    effective = resolveOperationOptions[TensorDecomposition, "TensorDecomposition", {options}]; If[FailureQ[effective], Return[effective]];
    result = tensorDecompositionIDs[context, factors]; If[FailureQ[result], Return[result]];
    If[!TrueQ[effective[IncludeZeros]], result = Select[result, # > 0 &]];
    presentIrrepKeys[context, result, effective[IrrepForm]]
];
TensorDecomposition[___] := makeFailure["InvalidInput", "TensorDecomposition expects a Group or RepresentationContext, a list of irreps and options."];

(*
    Summary: The complete ID-keyed decomposition, and the presentation of irrep keys.
    Parameters: context; factors — irreps (indices or IDs); result — association irrep ID -> value; form — "Index",
        "ID" or "Label".
    Options/defaults: None.
    Returns: tensorDecompositionIDs: <|ID -> multiplicity|> over every irrep (presentation order, zeros kept), or Failure.
        presentIrrepKeys: result with keys as requested (labels as plain text; a label shared by several irreps keeps
        the index for all but the first), or Failure.
    Effects: As TensorDecomposition.
    Failures: As TensorDecomposition.
    Example: presentIrrepKeys[g, <|First[g["IrrepOrder"]] -> 1|>, "Index"] is <|1 -> 1|>.
    See also: TensorDecomposition; irrepPresentation.
*)
tensorDecompositionIDs[context_, factors_List] := Module[{source, result, ids},
    (* factors by index or ID (uxUpdatePlan.md 1.3) *)
    ids = resolveIrrepArguments[context, factors]; If[FailureQ[ids], Return[ids]];
    source = tensorCharacterSource[context];
    If[FailureQ[source], Return[source]];
    result = tensorMultiplicities[source["CharacterData"], ids];
    If[FailureQ[result], result, KeyTake[result, source["IrrepOrder"]]]
];
presentIrrepKeys[context_, result_Association, form_] := Module[{p},
    Switch[form,
        "ID", result,
        "Index", KeyMap[irrepIndexOf[context, #] &, result],
        "Label", p = presentationData[context]; If[FailureQ[p], Return[p]];
            Module[{seen = <||>}, KeyMap[Function[id, With[{t = irrepPlainName[context, id]},
                If[KeyExistsQ[seen, t], irrepIndexOf[context, id], seen[t] = True; t]]], result]],
        _, makeFailure["InvalidOption", "IrrepForm must be \"Index\", \"ID\" or \"Label\".", <|"Options" -> {IrrepForm}|>]]];

(*
    Summary: Multiplicity of one irrep in a tensor product.
    Parameters: c — Group or RepresentationContext; factors — irreps (indices or IDs); target — irrep (index or ID).
    Options/defaults: None.
    Returns: Nonnegative Integer (0 when the target does not occur), or Failure.
    Effects: As TensorDecomposition.
    Failures: As TensorDecomposition; InvalidIrrep for an unknown target.
    Example: TensorMultiplicity[g, {t, t}, t] is 2 for the A4 triplet t.
    See also: TensorDecomposition.
*)
TensorMultiplicity[context : (_Group | _RepresentationContext), ids_List, irrep : (_String | _Integer)] := Module[{result, target},
    target = resolveIrrepArguments[context, irrep]; If[FailureQ[target], Return[target]];
    result = tensorDecompositionIDs[context, ids];
    Which[FailureQ[result], result,
        !KeyExistsQ[result, target], makeFailure["InvalidIrrep", "Unknown target irrep ID.", <|"IrrepIDs" -> {target}|>],
        True, result[target]]
];
TensorMultiplicity[___] := makeFailure["InvalidInput", "TensorMultiplicity expects a Group or RepresentationContext, a list of irreps and a target irrep."];

(*
    Summary: The irreps of a tensor product, each repeated by its multiplicity.
    Parameters: c — Group or RepresentationContext; factors — irreps (indices or IDs).
    Options/defaults: IrrepForm -> "Index" ("ID", "Label").
    Returns: List of irreps in the context's presentation order, or Failure.
    Effects: As TensorDecomposition.
    Failures: As TensorDecomposition.
    Example: TensorIrrepList[g, {}] is {1} (the trivial irrep's index).
    See also: TensorDecomposition.
*)
TensorIrrepList[context : (_Group | _RepresentationContext), ids_List, options : OptionsPattern[]] := Module[{effective, result},
    effective = resolveOperationOptions[TensorIrrepList, "TensorIrrepList", {options}]; If[FailureQ[effective], Return[effective]];
    result = tensorDecompositionIDs[context, ids]; If[FailureQ[result], Return[result]];
    result = presentIrrepKeys[context, Select[result, # > 0 &], effective[IrrepForm]]; If[FailureQ[result], Return[result]];
    Flatten[KeyValueMap[ConstantArray[#1, #2] &, result]]
];
TensorIrrepList[___] := makeFailure["InvalidInput", "TensorIrrepList expects a Group or RepresentationContext and a list of irreps."];

True
