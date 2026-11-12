(*
    :Title: Representation arithmetic checks
    :Context: VVMFTool`Private`
    :Summary: Exact and numerical matrix predicates shared by basis, unitarity and decomposition work.
    :Responsibilities:
        - Resolve the arithmetic settings (exact, or numerical with a working precision and tolerance).
        - Prove matrix identities exactly, or record numerical residuals against the tolerance.
        - Check positive Hermitian forms and unitarity of representation matrices.
        - Exact arithmetic domains (number fields found quickly, otherwise RootReduce arithmetic).
        - Group-aware validation: class values, certified relators, multiplicities, character matching,
          RepresentationCharacter and ValidateRepresentation.
    :Dependencies: Diagnostics.wl; GroupWords.wl (normalizeWord); Representation.wl (validateRepShape,
        repMatrices); GroupConstruction.wl (resolveOperationOptions); CheckpointRestore.wl (common job
        options); GroupMaps.wl (mapTargetSpecification); GroupEnrichment.wl (runGroupEnrichment); at call
        time RepresentationBasis.wl (representationOperand).
    :See Also: VVMFArch/step2Plan.md (options; unitarization, basis work and decomposition).
*)

(*
    Summary: Resolve the arithmetic settings of one representation computation.
    Parameters: arithmetic — "Exact" or "Numerical"; precision — WorkingPrecision value (integer >= 16
        or MachinePrecision); tolerance — Automatic or a positive number; inputPrecision — Precision
        of the input matrices (Infinity for exact input).
    Options/defaults: Automatic tolerance is 10^(-Floor[p/2]) with p the effective decimal precision
        (16 for machine numbers).
    Returns: <|"Arithmetic", "Precision", "Digits", "Tolerance"|>; exact settings have Precision and
        Digits Infinity and Tolerance None.
    Effects: Pure.
    Failures: NumericalInput Failure when exact arithmetic is requested for approximate input.
    Example: arithmeticSettings["Numerical", 50, Automatic, Infinity]["Tolerance"] is 10^-25.
    Remarks: Numerical input keeps its own precision when it is lower than the working precision, so the
        tolerance never claims more accuracy than the data carry.
    See also: checkMatrixIdentity; UnitarizeRepresentation.
*)
arithmeticSettings[arithmetic_String, precision_, tolerance_, inputPrecision_] := Module[{effective, digits},
    If[arithmetic === "Exact",
        Return[If[inputPrecision === Infinity,
            <|"Arithmetic" -> "Exact", "Precision" -> Infinity, "Digits" -> Infinity, "Tolerance" -> None|>,
            makeFailure["NumericalInput", "Exact arithmetic was requested for numerical matrices. Use Arithmetic -> \"Numerical\", or supply exact matrices."]]]];
    effective = Which[
        inputPrecision === Infinity, precision,
        inputPrecision === MachinePrecision || precision === MachinePrecision, MachinePrecision,
        True, Min[inputPrecision, precision]];
    digits = If[effective === MachinePrecision, 16, Floor[effective]];
    <|"Arithmetic" -> "Numerical", "Precision" -> effective, "Digits" -> digits,
        "Tolerance" -> If[tolerance === Automatic, 10^(-Floor[digits/2]), tolerance]|>
];
arithmeticSettings[___] := makeFailure["InvalidOptions", "Expected arithmetic, precision, tolerance and input precision."];

(*
    Summary: Bring matrices to the working arithmetic.
    Parameters: matrices — list of matrices (or one matrix); settings — from arithmeticSettings.
    Options/defaults: None.
    Returns: Canonical exact matrices, or numerical matrices at the settings' precision.
    Effects: Pure.
    Remarks: Numerical entries below 10^(3 - digits) in magnitude become exact zeros: a zero with no
        significant digits would otherwise lower the precision of the whole matrix.
    Failures: None.
    Example: toArithmetic[{{{1/2}}}, <|"Arithmetic" -> "Numerical", "Precision" -> 20|>] is {{{0.5`20}}}.
    See also: arithmeticSettings; canonicalMatrix.
*)
toArithmetic[data_, settings_Association] := If[settings["Arithmetic"] === "Exact",
    Map[RootReduce, data, {ArrayDepth[data]}],
    Chop[N[data, settings["Precision"]], 10^(3 - settings["Digits"])]];

(*
    Summary: Relative residual of a numerical matrix identity.
    Parameters: a, b — matrices of equal shape.
    Options/defaults: None.
    Returns: Max |a - b| divided by Max[1, max |b|], a nonnegative real.
    Effects: Pure.
    Failures: None.
    Example: matrixResidual[{{1.}}, {{1.}}] is 0.
    See also: checkMatrixIdentity.
*)
matrixResidual[a_, b_] := Max[Abs[Flatten[{a - b}]]] / Max[1, Max[Abs[Flatten[{b}]]]];

(*
    Summary: Decide a matrix identity a == b exactly or numerically.
    Parameters: a, b — matrices of equal shape; settings — from arithmeticSettings.
    Options/defaults: None.
    Returns: <|"Holds" -> Boolean|> for exact arithmetic (every entry of a - b RootReduces to 0), or
        <|"Holds" -> Boolean, "Residual" -> r|> for numerical arithmetic (r <= tolerance).
    Effects: Pure.
    Failures: None; a shape mismatch does not hold.
    Example: checkMatrixIdentity[{{Sqrt[2]^2}}, {{2}}, <|"Arithmetic" -> "Exact"|>]["Holds"] is True.
    Remarks: Exact mode never uses a tolerance.
    See also: arithmeticSettings; checkPositiveForm.
*)
checkMatrixIdentity[a_, b_, settings_Association] := Module[{residual},
    If[Dimensions[a] =!= Dimensions[b], Return[<|"Holds" -> False|>]];
    If[settings["Arithmetic"] === "Exact",
        Return[<|"Holds" -> AllTrue[Flatten[{a - b}], RootReduce[#] === 0 &]|>]];
    residual = matrixResidual[a, b];
    <|"Holds" -> TrueQ[residual <= settings["Tolerance"]], "Residual" -> residual|>
];

(*
    Summary: Decide whether a matrix is a positive definite Hermitian form.
    Parameters: h — square matrix; settings — from arithmeticSettings.
    Options/defaults: None.
    Returns: <|"Holds" -> Boolean|>, with "Residual" (Hermitian residual) and "MinEigenvalue" in
        numerical mode.
    Effects: Pure.
    Failures: None.
    Example: checkPositiveForm[{{2, I}, {-I, 2}}, <|"Arithmetic" -> "Exact"|>]["Holds"] is True.
    Remarks: Exact mode proves h == h^dagger and positivity of every leading principal minor
        (Sylvester's criterion); the minors of a Hermitian matrix are real. Numerical mode requires a
        Hermitian residual within tolerance and smallest eigenvalue above tolerance times the largest.
    See also: checkMatrixIdentity; invariantForm.
*)
checkPositiveForm[h_?SquareMatrixQ, settings_Association] := Module[{hermitian, minors, values},
    hermitian = checkMatrixIdentity[h, ConjugateTranspose[h], settings];
    If[!hermitian["Holds"], Return[Join[<|"Holds" -> False|>, KeyDrop[hermitian, "Holds"]]]];
    If[settings["Arithmetic"] === "Exact",
        minors = Table[RootReduce[Det[h[[;; k, ;; k]]]], {k, Length[h]}];
        Return[<|"Holds" -> AllTrue[minors, Element[#, Reals] && TrueQ[# > 0] &]|>]];
    values = Re[Eigenvalues[(h + ConjugateTranspose[h])/2]];
    <|"Holds" -> TrueQ[Min[values] > settings["Tolerance"] Max[Abs[values]]], "Residual" -> hermitian["Residual"],
        "MinEigenvalue" -> Min[values]|>
];
checkPositiveForm[___] := <|"Holds" -> False|>;

(*
    Summary: Decide whether every matrix of a list is unitary.
    Parameters: matrices — list of square matrices; settings — from arithmeticSettings.
    Options/defaults: None.
    Returns: <|"Holds" -> Boolean|>, with the largest "Residual" of M^dagger M - I in numerical mode.
    Effects: Pure; the hinted-field path memoizes its field (exactField).
    Failures: None.
    Example: unitaryMatricesCheck[{{{0, 1}, {1, 0}}}, <|"Arithmetic" -> "Exact"|>]["Holds"] is True.
    Remarks: Exact matrices whose entries all carry cyclotomic hints (cyclotomicHintPreferredQ) are checked in their
        number field (exact equality of field elements); others by RootReduce (checkMatrixIdentity).
    See also: UnitaryRepresentationQ; checkMatrixIdentity; exactField.
*)
unitaryMatricesCheck[matrices_List, settings_Association] := Module[{checks, field, entries},
    (* exact matrices whose entries all carry decoder hints (native cyclotomic data) are checked in their hinted
       number field, where M^dagger M of degree-60 Root entries would need minutes of RootReduce; other exact
       matrices keep the RootReduce check, which needs no field search *)
    entries = DeleteDuplicates[Select[Flatten[matrices], !MatchQ[#, _Integer | _Rational] && # =!= I &]];
    (* an explicit FieldMethod chooses the domain of the check (2B.9); otherwise the hinted field when preferred *)
    If[settings["Arithmetic"] === "Exact" && entries =!= {} && (Lookup[settings, "FieldMethod", Automatic] =!= Automatic ||
            (AllTrue[entries, KeyExistsQ[$CyclotomicHints, #] &] && cyclotomicHintPreferredQ[entries])),
        field = settingsField[matrices, settings];
        If[field["Kind"] === "NumberField",
            Return[<|"Holds" -> AllTrue[matrices, With[{m = fieldEmbed[field, #]},
                fieldZeroQ[fieldAdjoint[field, m] . m - IdentityMatrix[Length[m]]]] &]|>]]];
    checks = checkMatrixIdentity[ConjugateTranspose[#] . #, IdentityMatrix[Length[#]], settings] & /@ matrices;
    If[settings["Arithmetic"] === "Exact",
        <|"Holds" -> AllTrue[checks, #["Holds"] &]|>,
        <|"Holds" -> AllTrue[checks, #["Holds"] &], "Residual" -> Max[Append[Lookup[checks, "Residual"], 0]]|>]
];

(* -------------------------------------------------------------------------
   Exact number-field arithmetic
   ------------------------------------------------------------------------- *)

(* Bounded memo of exact domains by atom set; pure recomputable data. *)
If[!AssociationQ[$ExactFieldCache], $ExactFieldCache = <||>];
(* Bounded kernel-local hints: canonical value -> its cyclotomic coefficients (recorded by the native decoder). A hint
   is used only after exactField proves it exactly; a wrong or stale hint is ignored. *)
If[!AssociationQ[$CyclotomicHints], $CyclotomicHints = <||>];
(* Largest field degree (EulerPhi of the conductor) built from hints; Root objects are limited to $MaxRootDegree. *)
$CyclotomicHintMaxDegree = Min[1024, $MaxRootDegree];
(* Atoms of at most this degree keep the general field search first (it finds their small fields in milliseconds). *)
$CyclotomicHintMinAtomDegree = 8;

(*
    Summary: Record the cyclotomic coefficients of a canonical exact value.
    Parameters: value — canonical (RootReduced) value; order — n; coefficients — rationals c_0..c_{n-1} with
        value = Sum c_j Exp[2 Pi I j/n].
    Options/defaults: None.
    Returns: Null.
    Effects: Adds the hint to the bounded kernel-local $CyclotomicHints (at 10000 entries the oldest 5000 are dropped).
    Failures: None; malformed data is ignored.
    Example: registerCyclotomicHint[RootReduce[Exp[2 Pi I/5]], 5, {0, 1, 0, 0, 0}].
    Remarks: A hint is an unproved claim; cyclotomicHintField proves it before use.
    See also: cyclotomicHintField; decodeNativeRepScalar.
*)
registerCyclotomicHint[value_, order_Integer?Positive, coefficients_List] /;
        Length[coefficients] === order && VectorQ[coefficients, MatchQ[#, _Integer | _Rational] &] :=
    (If[Length[$CyclotomicHints] >= 10000, $CyclotomicHints = Drop[$CyclotomicHints, 5000]];
     AssociateTo[$CyclotomicHints, value -> <|"Order" -> order, "Coefficients" -> coefficients|>];);
registerCyclotomicHint[___] := Null;

(*
    Summary: Whether exactField should try the hinted cyclotomic field before its general search.
    Parameters: atoms — RootReduced nonrational values (I allowed); minimum — atom degree to exceed.
    Options/defaults: minimum Automatic is $CyclotomicHintMinAtomDegree (8: the degree-12 entries of Q(zeta_13), 78-1I, took 74 s through the general search and 2 s here); exactField's fallback uses 0.
    Returns: True when every atom other than I has a hint (cyclotomicHint), the largest atom degree exceeds the minimum, and
        EulerPhi[N] is at most four times that degree (N the least common multiple of the hinted orders and 4).
    Effects: Pure (reads $CyclotomicHints).
    Failures: None.
    Example: the degree-60 entries of a [186,1] sextet (N = 372, degree 120) are preferred; degree-2 entries hinted
        with conductor 1320 (degree 320) are not, and neither are the small-degree entries of T' or A4, whose fields
        the general search finds in milliseconds.
    See also: cyclotomicHintField; exactField.
*)
(*
    Summary: The cyclotomic hint of one canonical atom: a recorded one, or the hint of a root of unity.
    Parameters: atom — RootReduced value.
    Options/defaults: None.
    Returns: <|"Order", "Coefficients"|>, or None.
    Effects: Pure (reads $CyclotomicHints).
    Failures: None.
    Example: cyclotomicHint[RootReduce[Exp[2 Pi I 3/31]]] is <|"Order" -> 31, "Coefficients" -> UnitVector[31, 4]|>.
    Remarks: A root of unity zeta_m^k (minimal polynomial the m-th cyclotomic polynomial; m among the orders with
        EulerPhi[m] equal to its degree, k from its argument) needs no recorded hint, so values such as the
        eigenvalues RootReduce[Exp[2 Pi I/n]] added by basis code do not defeat the hinted field. Like every hint it is
        proved by cyclotomicHintField before use.
    See also: cyclotomicHintField; registerCyclotomicHint.
*)
cyclotomicHint[atom_] := Module[{recorded = Lookup[$CyclotomicHints, Key[atom], None], f, degree, x, value, fraction, m, k},
    If[recorded =!= None, Return[recorded]];
    If[Head[atom] =!= Root, Return[None]];
    f = atom[[1]]; degree = Exponent[f[x], x];
    If[!IntegerQ[degree] || degree < 1 || degree > $CyclotomicHintMaxDegree, Return[None]];
    (* a root of unity has modulus 1; its order m is the denominator of arg/(2 Pi), proved by the cyclotomic polynomial *)
    value = N[atom, 50];
    If[!NumericQ[value] || Abs[Abs[value] - 1] > 10^-30, Return[None]];
    fraction = Rationalize[Mod[Arg[value]/(2 Pi), 1], 10^-30];
    m = Denominator[fraction];
    If[m > 4 degree^2 + 4 || EulerPhi[m] =!= degree ||
        Expand[f[x] Coefficient[Cyclotomic[m, x], x, degree] - Cyclotomic[m, x] Coefficient[f[x], x, degree]] =!= 0, Return[None]];
    k = Mod[Numerator[fraction], m];
    <|"Order" -> m, "Coefficients" -> UnitVector[m, k + 1]|>
];

(*
    Summary: Candidate coordinates of an exact value on the power basis of Q(zeta_n), by an integer relation.
    Parameters: x — exact algebraic number; n — conductor.
    Options/defaults: None.
    Returns: Rationals c_0..c_{phi(n)-1} with q x = Sum c_j zeta_n^j found among high-precision values, or $Failed.
    Effects: Pure.
    Failures: $Failed when no small relation is found (LatticeReduce boxed at 20 s).
    Example: latticeCyclotomicCoordinates[1/Sqrt[2], 8] gives coordinates of (zeta_8 - zeta_8^3)/2.
    Remarks: Only a candidate: every caller certifies it exactly (RootReduce of the AlgebraicNumber equals x) before use
        (cyclotomicTerms for display, completeCyclotomicHints for exact arithmetic). About a second for phi(n) = 48.
    See also: completeCyclotomicHints; cyclotomicTerms.
*)
latticeCyclotomicCoordinates[x_, n_Integer] := Module[{phi = EulerPhi[n], precision, z, w, values, scale, lattice, reduced, q},
    precision = 80 + 8 phi;
    z = N[x, precision]; w = N[Exp[2 Pi I/n], precision];
    If[!NumericQ[z], Return[$Failed]];
    values = Prepend[w^Range[0, phi - 1], -z];
    scale = 10^(precision - 20);
    lattice = MapIndexed[Join[UnitVector[phi + 1, First[#2]], {Round[scale Re[#1]], Round[scale Im[#1]]}] &, values];
    reduced = Quiet[TimeConstrained[LatticeReduce[lattice], 20, $Failed]];
    If[!MatrixQ[reduced], Return[$Failed]];
    q = reduced[[1, 1]];
    If[q === 0 || Max[Abs[reduced[[1, -2 ;;]]]] > 10^(precision/4), Return[$Failed]];
    reduced[[1, 2 ;; phi + 1]] / q];

(*
    Summary: Complete the cyclotomic hints of an atom set whose hinted part already selects Q(zeta_N0).
    Parameters: atoms — RootReduced nonrational values (I allowed).
    Options/defaults: $CyclotomicCompletionMaxAtoms (64) unhinted atoms at most; a 120 s total box per call.
    Returns: The number of atoms newly hinted (0 when nothing applies).
    Effects: registerCyclotomicHint for each certified atom and its conjugate; records tried-and-failed atoms in the
        bounded $CyclotomicCompletionMemo (key {atom, N0, L}).
    Failures: None; atoms that cannot be completed stay unhinted (exactField then behaves as before).
    Example: hinted Q(zeta_13) entries of degree 12 with an unhinted 1/Sqrt[2]: the latter is hinted at conductor 104.
    Remarks (cgFieldVerificationPlan.md 3.1): acts only when the hinted part H passes cyclotomicHintPreferredQ, so the
        field Q(zeta_N0), N0 = lcm(orders of H, 4), would already be used if the rest were hinted. Candidate conductors
        for an atom u of degree d come from the discriminant D of its integral minimal polynomial: N0, then lcm(N0, s,
        e) for the subsets s of the admissible odd primes dividing D (p not dividing N0, phi(N0)(p - 1) <= 4 L) and e = 8
        when 2 | D, 8 does not divide N0 and 2 phi(N0) <= 4 L (L the largest atom degree), in increasing phi, each kept
        when d | phi(n) and phi(lcm(n, conductors completed so far)) <= 4 L (the non-strict rule of
        cyclotomicHintPreferredQ, so a completed set passes the gate). The running lcm makes the outcome depend on the
        order (atoms by increasing degree); this only costs completeness, never soundness. Candidate coordinates come
        from latticeCyclotomicCoordinates (box 2 + phi(n)/8 s) and are accepted only when RootReduce of the
        AlgebraicNumber on zeta_n equals the atom (SameQ of canonical forms, 10 s box); cyclotomicHintField proves every
        hint again before building the field. Mathematically the checks in Q(zeta_N) are the same exact checks.
    See also: exactField; cyclotomicHintPreferredQ; cyclotomicHintField; latticeCyclotomicCoordinates.
*)
$CyclotomicCompletionMaxAtoms = 64;
$CyclotomicExplicitMaxAtoms = 256;
$CyclotomicCompletionMemo = <||>;
completeCyclotomicHints[atoms_List, mode_String : "Gated"] := Module[{others = DeleteCases[atoms, I], hinted, unhinted, hints, n0, phi0, large, x,
        degreeOf, completedN, added = 0, explicit = mode === "Cyclotomic", deadline, thetas = <||>, theta, certify, candidates, bound},
    (* "Gated" (exactField Automatic): only when the hinted part passes cyclotomicHintPreferredQ, candidates within its
       size rule. "Cyclotomic" (FieldMethod -> "Cyclotomic", methodOptionsPlan.md 1.1): no gate, candidates bounded by
       $CyclotomicHintMaxDegree, odd primes by trial division, larger caps, its own memo key. *)
    deadline = AbsoluteTime[] + If[explicit, 300, 120];
    hinted = Select[others, cyclotomicHint[#] =!= None &];
    unhinted = Complement[others, hinted];
    If[unhinted === {} || hinted === {} || Length[unhinted] > If[explicit, $CyclotomicExplicitMaxAtoms, $CyclotomicCompletionMaxAtoms] ||
        (!explicit && !cyclotomicHintPreferredQ[hinted]), Return[0]];
    hints = cyclotomicHint /@ hinted;
    n0 = LCM @@ Append[Lookup[hints, "Order"], 4]; phi0 = EulerPhi[n0];
    degreeOf[a_] := Replace[a, {Root[f_, __] :> Exponent[f[x], x], _ -> 2}];
    large = Max[degreeOf /@ others];
    bound = If[explicit, $CyclotomicHintMaxDegree, 4 large];
    completedN = n0;
    theta[n_] := Lookup[thetas, n, thetas[n] = Quiet[RootReduce[Exp[2 Pi I/n]]]];
    certify[u_, n_, c_] := Quiet[TimeConstrained[RootReduce[AlgebraicNumber[theta[n], c]], 10, $Failed]] === u;
    candidates[u_, running_] := Module[{d = degreeOf[u], disc, oddPrimes, e, subsets, ns},
        (* MinimalPolynomial is primitive with integer coefficients: its discriminant is that of an order of Q(u), so
           every ramified prime divides it *)
        disc = Quiet[Discriminant[MinimalPolynomial[u, x], x]];
        (* trial division by the admissible primes only: D is never factored *)
        oddPrimes = Select[Prime[Range[2, PrimePi[Max[3, Floor[bound/phi0] + 1]]]],
            !Divisible[n0, #] && phi0 (# - 1) <= bound && IntegerQ[disc] && Divisible[disc, #] &];
        e = If[IntegerQ[disc] && EvenQ[disc] && !Divisible[n0, 8] && 2 phi0 <= bound, 8, 1];
        subsets = If[explicit, Subsets[oddPrimes, {0, 3}], Subsets[oddPrimes]];
        ns = DeleteDuplicates[Join[{n0}, LCM[n0, Times @@ #, e] & /@ subsets, LCM[n0, Times @@ #] & /@ subsets]];
        SortBy[Select[ns, Divisible[EulerPhi[#], d] && EulerPhi[LCM[#, running]] <= bound &], EulerPhi]];
    Scan[Function[u, Module[{key = If[explicit, {u, n0, "Cyclotomic"}, {u, n0, large}], found = None, tried, full},
            If[AbsoluteTime[] > deadline || KeyExistsQ[$CyclotomicCompletionMemo, key] || cyclotomicHint[u] =!= None, Return[Null, Module]];
            tried = candidates[u, completedN]; full = candidates[u, n0];
            Catch[Scan[Function[n, Module[{c},
                    If[AbsoluteTime[] > deadline, Throw[$Aborted, completeCyclotomicHints]];
                    c = TimeConstrained[latticeCyclotomicCoordinates[u, n], 2 + EulerPhi[n]/8, $Failed];
                    If[ListQ[c] && certify[u, n, c], found = {n, c}; Throw[found, completeCyclotomicHints]]]], tried],
                completeCyclotomicHints];
            Which[
                ListQ[found],
                    registerCyclotomicHint[u, found[[1]], PadRight[found[[2]], found[[1]]]]; added++;
                    completedN = LCM[completedN, found[[1]]];
                    (* the conjugate: c_k moved to zeta_n^(-k), certified by the same exact test *)
                    With[{n = found[[1]], cc = PadRight[found[[2]], found[[1]]], ubar = Quiet[RootReduce[Conjugate[u]]]},
                        With[{conj = Table[cc[[Mod[-k, n] + 1]], {k, 0, n - 1}]},
                            If[ubar =!= u && cyclotomicHint[ubar] === None && certify[ubar, n, conj], registerCyclotomicHint[ubar, n, conj]]]],
                AbsoluteTime[] > deadline, Null,
                (* a failure is remembered only when every candidate was tried: candidates dropped because of the
                   conductors completed earlier in this call may succeed in another call (review F1) *)
                tried =!= full, Null,
                True,
                    If[Length[$CyclotomicCompletionMemo] >= 5000, $CyclotomicCompletionMemo = <||>];
                    AssociateTo[$CyclotomicCompletionMemo, key -> True]]]],
        SortBy[unhinted, degreeOf]];
    added];

cyclotomicHintPreferredQ[atoms_List, minimum_ : Automatic] := Module[{others = DeleteCases[atoms, I], hints, x, largest},
    (* stops at the first atom without a hint *)
    hints = Catch[Map[With[{h = cyclotomicHint[#]}, If[h === None, Throw[None, "noHint"], h]] &, others], "noHint"];
    If[others === {} || hints === None, Return[False]];
    largest = Max[Replace[#, {Root[f_, __] :> Exponent[f[x], x], _ -> 2}] & /@ others];
    largest > If[minimum === Automatic, $CyclotomicHintMinAtomDegree, minimum] &&
        EulerPhi[LCM @@ Append[Lookup[hints, "Order"], 4]] <= 4 largest];

(*
    Summary: The cyclotomic number field Q(zeta_N) of hinted atoms, each hint proved exactly.
    Parameters: atoms — RootReduced nonrational values (I allowed); budget — seconds.
    Options/defaults: None.
    Returns: An exactField NumberField record with "Source" -> "CyclotomicHint" (generator zeta_N, N the least
        common multiple of the hinted orders and 4), or None when an atom has no hint, a hint fails its exact check,
        the degree exceeds $CyclotomicHintMaxDegree, or the budget is exceeded.
    Effects: Pure (reads $CyclotomicHints).
    Failures: None.
    Example: with a hint for RootReduce[Exp[2 Pi I/31] + Exp[-2 Pi I/31]], the field of that atom is Q(zeta_124).
    Remarks: Each atom's element sum c_j zeta_N^(j N/n) is accepted only when RootReduce of it is the atom itself
        (exact), so a wrong hint cannot change any value; the rules also list the atoms' conjugates (from the
        conjugate coefficients) and I. Arithmetic with field elements of degree 60 takes milliseconds where finding
        the field from Root objects of degree 60 takes many minutes (VVMFUse [186,1]).
    See also: exactField; registerCyclotomicHint.
*)
cyclotomicHintField[atoms_List, budget_] := Module[{others = DeleteCases[atoms, I], hints, n, degree, theta, element, result},
    If[others === {}, Return[None]];
    hints = cyclotomicHint /@ others;
    If[MemberQ[hints, None], Return[None]];
    n = LCM @@ Append[Lookup[hints, "Order"], 4];
    degree = EulerPhi[n];
    If[degree > $CyclotomicHintMaxDegree, Return[None]];
    result = TimeConstrained[Module[{embedded, conjugates, conjugateKeys, iElement, conjugateGenerator, x},
            theta = Quiet[RootReduce[Exp[2 Pi I/n]]];
            If[Head[theta] =!= Root, Return[None, Module]];
            (* sum_j c_j zeta_order^(sign j) as an element of Q(zeta_n) *)
            element[hint_, sign_] := AlgebraicNumber[theta, PadRight[CoefficientList[PolynomialRemainder[
                hint["Coefficients"] . x^Mod[sign (n/hint["Order"]) Range[0, hint["Order"] - 1], n], Cyclotomic[n, x], x], x], degree]];
            embedded = element[#, 1] & /@ hints;
            If[!AllTrue[Transpose[{embedded, others}], RootReduce[#[[1]]] === #[[2]] &], Return[None, Module]];
            conjugates = element[#, -1] & /@ hints;
            conjugateKeys = RootReduce /@ conjugates;
            iElement = element[<|"Order" -> 4, "Coefficients" -> {0, 1, 0, 0}|>, 1];
            conjugateGenerator = element[<|"Order" -> n, "Coefficients" -> UnitVector[n, n]|>, 1];
            <|"Kind" -> "NumberField", "Generator" -> theta, "Degree" -> degree,
                "Rules" -> Dispatch[DeleteDuplicatesBy[Join[Thread[others -> embedded], Thread[conjugateKeys -> conjugates], {I -> iElement}], First]],
                "ConjugatePowers" -> NestList[conjugateGenerator # &, 1, degree - 1], "I" -> iElement, "Source" -> "CyclotomicHint"|>],
        6 budget + Length[others], None];
    If[AssociationQ[result], result, None]
];

(*
    Summary: Exact arithmetic domain for given values: a number field when one is found quickly,
        otherwise canonical RootReduce arithmetic.
    Parameters: values — exact algebraic numbers (any nesting of lists); budget — seconds allowed for
        finding the field (default 5).
    Options/defaults: budget 5.
    Returns: <|"Kind" -> "NumberField", "Generator", "Degree", "Rules", "ConjugatePowers", "I"|> (with
        "Source" -> "CyclotomicHint" when built from cyclotomic hints), or <|"Kind" -> "RootReduce", "I" -> I|>.
    Effects: Memoizes domains by their atom set in the bounded kernel-local $ExactFieldCache (pure,
        recomputable data), so repeated checks on one representation build its field once.
    Failures: None; the RootReduce domain is always available.
    Example: exactField[{Sqrt[3]}]["Kind"] is "NumberField" (the field Q(Sqrt[3], I) of degree 4).
    Remarks: Number-field elements are AlgebraicNumber values with canonical coefficient lists, so
        arithmetic is exact and SameQ decides equality; this avoids RootReduce of growing radical
        expressions (for GAP's cyclotomic data the field is found in milliseconds). When the all-at-once
        construction exceeds the budget, a primitive element is built incrementally from I and the atoms
        outside the current field (simplest first; mixed entries after a rational basis change of an
        11-dimensional representation: about 11 s). The field is closed under conjugation, which maps the
        generator theta to conj(theta), itself a field element. Values whose field is still not found use
        RootReduce arithmetic, in which every product is reduced and zero tests are RootReduce[x] === 0;
        both domains are exact. Atoms whose cyclotomic coefficients the native decoder recorded give Q(zeta_N)
        directly (cyclotomicHintField, each hint proved exactly first); its record carries "Source" ->
        "CyclotomicHint".
        New values in the field of hinted entries (CG entries) are given certified coordinates first
        (completeCyclotomicHints, cgFieldVerificationPlan.md) when both cache keys miss.
    See also: fieldEmbed; fieldConjugate; fieldBack; fieldReduce; cyclotomicHintField.
*)
(*
    Summary: The exact arithmetic domain chosen explicitly (FieldMethod, methodOptionsPlan.md 1.1).
    Parameters: values — exact values; budget — seconds; method — "Cyclotomic" | "PrimitiveElement" | "Radical" |
        "RootReduce" or a list of them (tried in order).
    Options/defaults: Automatic (the 2-argument form) keeps today's order and gates.
    Returns: A domain record with "Method" (the strategy that produced it); for a cyclotomic field also "Conductor"
        and, when its degree exceeds 4 times the largest value degree, "Oversized" -> {degree, largest}. When no listed
        strategy applies: <|"Kind" -> "Unavailable", "Method" -> method, "Reason" -> reasons|>.
    Effects: May register certified cyclotomic hints (completeCyclotomicHints, "Cyclotomic" mode); memoizes by method.
    Failures: None (Unavailable is a record; CG code turns it into FieldMethodUnavailable, cgArithmetic).
    Example: exactField[{2^(1/3)}, 5, "Cyclotomic"]["Kind"] is "Unavailable".
    See also: exactField; completeCyclotomicHints; cgArithmetic.
*)
exactField[values_, budget_, Automatic] := exactField[values, budget];

(*
    Summary: The verification status of a stored representation variant and of a group's character table
        (methodOptionsPlan.md 2C.1).
    Parameters: variant — stored variant association (cgVariant) or Missing; data — group or context snapshot.
    Options/defaults: Records without a stored "VerificationStatus" read by their data: numerical tier or arithmetic
        "Numerical", everything else "Exact" (all such data were verified by today's checks).
    Returns: "Exact" | "Numerical" | "Unverified"; groupRecordsStatus: the weakest of the group's status, its stored
        variants and its stored CG entries.
    Effects: Pure.
    Failures: None (a missing variant, e.g. a zero-multiplicity target, is "Exact": nothing is used).
    Example: variantVerificationStatus[<|"Tier" -> "Numerical"|>] is "Numerical".
    See also: cgWeakestStatus; makeCGData; makeVectorData.
*)
variantVerificationStatus[variant_Association] := Lookup[variant, "VerificationStatus",
    If[Lookup[variant, "Tier", None] === "Numerical" || Lookup[variant, "Arithmetic", "Exact"] === "Numerical", "Numerical", "Exact"]];
variantVerificationStatus[_] := "Exact";
(* C9 (methodOptionsPlan.md 2C): the one test of a variant GAP may compute with: a native tier and an exact status *)
gapNativeVariantQ[variant_Association] := MemberQ[{"Native", "ScaledNative"}, Lookup[variant, "Tier", None]] && variantVerificationStatus[variant] === "Exact";
gapNativeVariantQ[_] := False;
groupVerificationStatus[data_Association] := Lookup[data, "VerificationStatus", "Exact"];
groupVerificationStatus[_] := "Exact";
(* the weakest record a group's data hold: its characters, every stored variant and every stored CG entry (the status of a
   saved file, methodOptionsPlan.md 2C.5) *)
groupRecordsStatus[data_Association] := cgWeakestStatus[Join[{groupVerificationStatus[data]},
    Flatten[Map[Map[variantVerificationStatus, Values[Lookup[#, "Variants", <||>]]] &, Values[Lookup[data, "Representations", <||>]]]],
    cgEntryStatus /@ Values[Lookup[Replace[Lookup[data, "CGCache", <||>], Except[_Association] -> <||>], "Entries", <||>]]]];

(*
    Summary: The exact domain of a representation computation under the call's FieldMethod (methodOptionsPlan.md 2B.9).
    Parameters: values — the values the domain must contain; settings — arithmetic settings carrying "FieldMethod".
    Options/defaults: "FieldMethod" missing or Automatic: exactField's own choice (every caller that passes no method).
    Returns: An exactField domain.
    Effects: As exactField.
    Failures: An explicit FieldMethod without an available domain throws FieldMethodUnavailable (tag
        cgFieldMethodTag), caught by cgFieldCatch at the public entry points; never a silent other domain.
    Example: settingsField[m, <|"FieldMethod" -> "RootReduce"|>]["Kind"] is "RootReduce".
    See also: exactField; cgArithmetic.
*)
settingsField[values_, settings_Association] := With[{method = Lookup[settings, "FieldMethod", Automatic]},
    If[method === Automatic, exactField[values],
        With[{field = exactField[values, 5, method]},
            If[field["Kind"] === "Unavailable",
                Throw[makeFailure["FieldMethodUnavailable", "No domain of the requested FieldMethod applies to these values.",
                    <|"FieldMethod" -> method, "Reason" -> field["Reason"]|>], cgFieldMethodTag], field]]]];
exactField[values_, budget_, method : (_String | {__String})] := Module[{atoms, key, result, reasons = {}},
    atoms = DeleteDuplicates[RootReduce /@ Select[Flatten[{values}], !MatchQ[#, _Integer | _Rational] &]];
    key = Hash[{"ExplicitField", method, Sort[atoms], budget}, "SHA256"];
    result = Lookup[$ExactFieldCache, key, None];
    If[result =!= None, Return[result]];
    result = Catch[
        Scan[Function[strategy, With[{domain = explicitFieldDomain[strategy, atoms, budget]},
            If[domain["Kind"] =!= "Unavailable", Throw[domain, explicitFieldDomain], AppendTo[reasons, strategy -> domain["Reason"]]]]],
            Flatten[{method}]];
        <|"Kind" -> "Unavailable", "Method" -> method, "Reason" -> reasons|>, explicitFieldDomain];
    (* an Unavailable outcome may depend on time boxes and on the hints known now: it is not cached *)
    If[result["Kind"] === "Unavailable", Return[result]];
    If[Length[$ExactFieldCache] >= 64, $ExactFieldCache = <||>];
    AssociateTo[$ExactFieldCache, key -> result];
    result
];
explicitFieldDomain["RootReduce", atoms_List, budget_] := <|"Kind" -> "RootReduce", "I" -> I, "Method" -> "RootReduce"|>;
explicitFieldDomain["PrimitiveElement", atoms_List, budget_] := With[{f = exactFieldFromAtoms[DeleteDuplicates[Join[atoms, RootReduce /@ Conjugate[atoms], {I}]], budget]},
    If[f["Kind"] === "NumberField", Join[f, <|"Method" -> "PrimitiveElement"|>],
        <|"Kind" -> "Unavailable", "Reason" -> "no primitive element of the values was found within the budget"|>]];
explicitFieldDomain["Radical", atoms_List, budget_] := With[{f = radicalAtomField[DeleteDuplicates[Join[atoms, RootReduce /@ Conjugate[atoms], {I}]], budget]},
    If[AssociationQ[f], Join[f, <|"Method" -> "Radical"|>], <|"Kind" -> "Unavailable", "Reason" -> "the values are not in a field of prime radicals"|>]];
explicitFieldDomain["Cyclotomic", atoms_List, budget_] := Module[{others = DeleteCases[atoms, I], hints, field, n, x, largest, missing},
    (* no irrational value: the arithmetic is rational, nothing to choose *)
    If[others === {}, Return[Join[exactField[atoms, budget], <|"Method" -> "Cyclotomic"|>]]];
    If[NoneTrue[others, cyclotomicHint[#] =!= None &],
        Return[<|"Kind" -> "Unavailable", "Reason" -> "no value has cyclotomic data (hints or roots of unity) to fix the field"|>]];
    completeCyclotomicHints[atoms, "Cyclotomic"];
    missing = Select[others, cyclotomicHint[#] === None &];
    If[missing =!= {}, Return[<|"Kind" -> "Unavailable",
        "Reason" -> ToString[Length[missing]] <> " values have no certified coordinates in a cyclotomic field within the bounds"|>]];
    field = cyclotomicHintField[atoms, budget];
    If[!AssociationQ[field], Return[<|"Kind" -> "Unavailable",
        "Reason" -> "the cyclotomic field of the hints could not be built (degree above $CyclotomicHintMaxDegree, a hint failed its proof, or the budget)"|>]];
    hints = cyclotomicHint /@ others;
    n = LCM @@ Append[Lookup[hints, "Order"], 4];
    largest = Max[Replace[#, {Root[f_, __] :> Exponent[f[x], x], _ -> 2}] & /@ others];
    Join[field, <|"Method" -> "Cyclotomic", "Conductor" -> n|>,
        If[field["Degree"] > 4 largest, <|"Oversized" -> {field["Degree"], largest}|>, <||>]]
];
explicitFieldDomain[other_, ___] := <|"Kind" -> "Unavailable", "Reason" -> "unknown FieldMethod " <> ToString[other, InputForm]|>;

(*
    Summary: A plain summary of an exact domain for records (no functions or Dispatch tables).
    Parameters: field — exactField domain record, or None (numerical arithmetic).
    Returns: <|"Kind", "Method", "Degree" (number fields), "Conductor" (cyclotomic), "Oversized" (when recorded)|>.
    Effects: Pure.
    Example: domainSummary[None] is <|"Kind" -> "Numerical"|>.
    See also: exactField.
*)
domainSummary[None] := <|"Kind" -> "Numerical"|>;
domainSummary[field_Association] := Join[<|"Kind" -> field["Kind"],
        "Method" -> Lookup[field, "Method", If[Lookup[field, "Source", None] === "CyclotomicHint", "Cyclotomic", Automatic]]|>,
    KeyTake[field, {"Degree", "Conductor", "Oversized", "Reason"}]];
domainSummary[_] := <|"Kind" -> "Unknown"|>;

exactField[values_, budget_ : 5] := Module[{atoms, field, generator, degree, conjugateGenerator, rootReduce, memberQ, theta,
        key, hintKey, result, hinted, hintAtoms},
    rootReduce = <|"Kind" -> "RootReduce", "I" -> I|>;
    atoms = DeleteDuplicates[RootReduce /@ Select[Flatten[{values}], !MatchQ[#, _Integer | _Rational] &]];
    (* Cyclotomic atoms with recorded coefficients (native decoder): Q(zeta_N) directly, each hint proved exactly,
       first when Q(zeta_N) is not much larger than the atoms' own degrees (a large conductor with small-degree
       entries, such as unitary Dixon matrices of A5, keeps the smaller field of the search below, with the hint
       field only as the fallback for a search that ends in RootReduce arithmetic). *)
    key = Hash[{"CyclotomicHint", Sort[atoms], budget}, "SHA256"];
    result = Lookup[$ExactFieldCache, key, None];
    If[result =!= None, Return[result]];
    hinted = If[cyclotomicHintPreferredQ[atoms], cyclotomicHintField[atoms, budget], None];
    If[AssociationQ[hinted],
        If[Length[$ExactFieldCache] >= 64, $ExactFieldCache = <||>];
        AssociateTo[$ExactFieldCache, key -> hinted];
        Return[hinted]];
    hintAtoms = atoms; hintKey = key;
    atoms = DeleteDuplicates[Join[atoms, RootReduce /@ Conjugate[atoms], {I}]];
    key = Hash[{Sort[atoms], budget}, "SHA256"];
    result = Lookup[$ExactFieldCache, key, None];
    If[result =!= None, Return[result]];
    (* new values (e.g. CG entries) in the field of hinted representation entries: certified coordinates complete the
       hints, and the hinted field is tried again (cgFieldVerificationPlan.md 3.1) *)
    If[completeCyclotomicHints[hintAtoms] > 0 && cyclotomicHintPreferredQ[hintAtoms],
        hinted = cyclotomicHintField[hintAtoms, budget];
        If[AssociationQ[hinted],
            If[Length[$ExactFieldCache] >= 64, $ExactFieldCache = <||>];
            AssociateTo[$ExactFieldCache, {key -> hinted, hintKey -> hinted}];
            Return[hinted]]];
    result = exactFieldFromAtoms[atoms, budget];
    (* Radical fields whose reduced atoms are large Root objects: build the field from prime radicals instead. *)
    If[result["Kind"] =!= "NumberField", With[{radical = radicalAtomField[atoms, budget]}, If[AssociationQ[radical], result = radical]]];
    (* the hinted field as the fallback, under the same size rule but for atoms of any degree *)
    If[result["Kind"] =!= "NumberField" && cyclotomicHintPreferredQ[hintAtoms, 0],
        With[{fallback = cyclotomicHintField[hintAtoms, budget]}, If[AssociationQ[fallback], result = fallback]]];
    If[Length[$ExactFieldCache] >= 64, $ExactFieldCache = <||>];
    AssociateTo[$ExactFieldCache, key -> result];
    result
];

(*
    Summary: Build the exact domain of a conjugation-closed list of canonical atoms (exactField's work).
    Parameters: atoms — RootReduced nonrational values, closed under conjugation, including I; budget.
    Options/defaults: None.
    Returns: As exactField.
    Effects: Pure.
    Failures: None.
    Example: exactFieldFromAtoms[{Sqrt[3], I}, 5]["Kind"] is "NumberField".
    See also: exactField.
*)
exactFieldFromAtoms[atoms_List, budget_] := Module[{field, generator, degree, conjugateGenerator, rootReduce, memberQ, theta},
    rootReduce = <|"Kind" -> "RootReduce", "I" -> I|>;
    (* An unevaluated ToNumberField (a nonmember) would be evaluated again, with its message, once outside Quiet: it is
       replaced by $Failed inside. *)
    field = TimeConstrained[Quiet[ToNumberField[atoms] /. _ToNumberField -> $Failed], budget, $Failed];
    If[!ListQ[field] || !AllTrue[field, MatchQ[#, _AlgebraicNumber | _Integer | _Rational] &],
        (* Incremental primitive element: start from I and adjoin only atoms outside the current field,
           simplest first; mixed entries (for example after a rational basis change) then give a small
           generator even when the all-at-once construction is slow. *)
        memberQ[a_, th_] := Quiet[MatchQ[TimeConstrained[ToNumberField[a, th], budget, $Failed], _AlgebraicNumber | _Integer | _Rational]];
        theta = TimeConstrained[Module[{th = I},
            Do[If[!memberQ[a, th], th = Quiet[First[First[ToNumberField[{th, a}]]]]], {a, SortBy[atoms, LeafCount]}]; th],
            6 budget, $Failed];
        field = If[theta === $Failed, $Failed,
            TimeConstrained[Quiet[(ToNumberField[#, theta] & /@ atoms) /. _ToNumberField -> $Failed], 6 budget, $Failed]]];
    If[!ListQ[field] || !AllTrue[field, MatchQ[#, _AlgebraicNumber | _Integer | _Rational] &] ||
        FreeQ[field, AlgebraicNumber], Return[rootReduce]];
    generator = First[FirstCase[field, _AlgebraicNumber]];
    degree = Length[Last[FirstCase[field, _AlgebraicNumber]]];
    conjugateGenerator = TimeConstrained[Quiet[ToNumberField[RootReduce[Conjugate[generator]], generator] /. _ToNumberField -> $Failed], budget, $Failed];
    If[Head[conjugateGenerator] =!= AlgebraicNumber && !MatchQ[conjugateGenerator, _Integer | _Rational],
        conjugateGenerator = recognizedConjugateGenerator[generator, degree]];
    If[Head[conjugateGenerator] =!= AlgebraicNumber && !MatchQ[conjugateGenerator, _Integer | _Rational], Return[rootReduce]];
    <|"Kind" -> "NumberField", "Generator" -> generator, "Degree" -> degree, "Rules" -> Dispatch[Thread[atoms -> field]],
        "ConjugatePowers" -> NestList[conjugateGenerator # &, 1, degree - 1],
        "I" -> Replace[I, Dispatch[Thread[atoms -> field]]]|>
];

(*
    Summary: The complex conjugate of a field generator, as an element of its field, by recognition.
    Parameters: generator — algebraic number theta; degree — [Q(theta) : Q].
    Options/defaults: None.
    Returns: AlgebraicNumber[theta, c] equal to conj(theta), or $Failed.
    Effects: Pure.
    Failures: $Failed when the integer relation is not found or the candidate does not verify.
    Example: for theta generating Q(2^(1/6), Sqrt[3], I) the result is a degree-24 coordinate vector.
    Remarks: Used when ToNumberField[conj(theta), theta] exceeds its budget (large Root generators). The candidate
        from an integer relation among the numerical power basis and conj(theta) is accepted only when it is a root
        of theta's minimal polynomial (exact field arithmetic) and lies closer to conj(theta), which is also a root,
        than half the minimal separation of that polynomial's roots. The separation comes from the isolated Root
        objects evaluated with precision tracking, so no fixed tolerance decides which root it is. $Failed when the
        separation cannot be computed within 60 s.
    See also: exactFieldFromAtoms.
*)
recognizedConjugateGenerator[generator_, degree_Integer] := Module[{precision = 60 + 25 degree, basis, value, scale, lattice, row, candidate, x, zero, separation},
    basis = N[generator^Range[0, degree - 1], precision];
    value = N[Conjugate[generator], precision];
    scale = 10^Floor[precision/3];
    lattice = Join[MapThread[Join[UnitVector[degree + 1, #1], Round[scale {Re[#2], Im[#2]}]] &, {Range[degree], basis}],
        {Join[UnitVector[degree + 1, degree + 1], Round[-scale {Re[value], Im[value]}]]}];
    row = SelectFirst[TimeConstrained[LatticeReduce[lattice], 60, {}], #[[degree + 1]] =!= 0 &, None];
    If[row === None, Return[$Failed]];
    candidate = AlgebraicNumber[generator, row[[1 ;; degree]] / row[[degree + 1]]];
    zero = Fold[#1 candidate + #2 &, 0, Reverse[CoefficientList[MinimalPolynomial[generator, x], x]]];
    If[!(zero === 0 || (Head[zero] === AlgebraicNumber && AllTrue[Last[zero], # === 0 &])), Return[$Failed]];
    (* The candidate and conj(generator) are both roots of the minimal polynomial; they are equal when they are
       closer than half the minimal separation of its roots (isolated Root objects evaluated with precision tracking). *)
    separation = Quiet[TimeConstrained[Module[{roots = N[Root[MinimalPolynomial[generator, x], #] & /@ Range[Exponent[MinimalPolynomial[generator, x], x]], 50]},
        If[Length[roots] < 2, Infinity, Min[Abs[Subtract @@@ Subsets[roots, {2}]]]]], 60, $Failed]];
    If[!NumericQ[separation] && separation =!= Infinity, Return[$Failed]];
    If[Abs[N[candidate, 50] - N[Conjugate[generator], 50]] < separation/2, candidate, $Failed]
];

(*
    Summary: A number field from the radical forms of algebraic atoms, one radical generator per prime.
    Parameters: atoms — RootReduced nonrational values (closed under conjugation); budget.
    Options/defaults: None.
    Returns: A NumberField domain (as exactFieldFromAtoms) containing every atom, or None.
    Effects: Pure.
    Failures: None (None when an atom has no radical form, no field is found, or an atom does not embed).
    Example: entries of a basis change by 2^(1/3) of a representation with Sqrt[2], Sqrt[3] entries give the field
        of 2^(1/6), 3^(1/2) and I.
    Remarks: RootReduced atoms of radical fields are Root objects whose joint primitive element ToNumberField finds
        slowly; the field generated by p^(1/n) for each prime p (n the lcm of the radical denominators of p) and I is
        found at once, and each atom is then placed in it (ToNumberField against the generator) and checked.
    See also: exactField.
*)
radicalAtomField[atoms_List, budget_] := Module[{radicals, powers, primes = <||>, generators, field, embedded},
    radicals = TimeConstrained[ToRadicals /@ atoms, budget, $Failed];
    If[radicals === $Failed || !FreeQ[radicals, Root], Return[None]];
    powers = Cases[radicals, Power[_Integer | _Rational, _Rational], {0, Infinity}];
    Scan[Function[power, With[{n = Denominator[power[[2]]]},
        Scan[(primes[First[#]] = LCM[Lookup[primes, First[#], 1], n]) &,
            Join[FactorInteger[Numerator[Abs[power[[1]]]]], FactorInteger[Denominator[Abs[power[[1]]]]]]]]], powers];
    KeyDropFrom[primes, 1];
    generators = KeyValueMap[#1^(1/#2) &, primes];
    field = exactFieldFromAtoms[Join[generators, {I}], budget];
    If[field["Kind"] =!= "NumberField", Return[None]];
    embedded = TimeConstrained[Quiet[(ToNumberField[#, field["Generator"]] & /@ atoms) /. _ToNumberField -> $Failed], 6 budget, $Failed];
    If[embedded === $Failed || !AllTrue[embedded, MatchQ[#, _AlgebraicNumber | _Integer | _Rational] &], Return[None]];
    Join[field, <|"Rules" -> Dispatch[Join[Normal[field["Rules"]], Thread[atoms -> embedded]]]|>]
];

(*
    Summary: Map exact values into an exact domain from exactField.
    Parameters: field — from exactField; data — exact values (any array).
    Options/defaults: None.
    Returns: The array with field elements (number field) or RootReduced values; rationals unchanged.
    Effects: Pure.
    Failures: None; values outside the field stay unconverted and make later field checks fail.
    Remarks: Values listed when the field was built map through its rules; other members of the field
        (for example computed forms) are placed by ToNumberField against the field generator.
    Example: fieldEmbed[exactField[{Sqrt[2]}], {{Sqrt[2], 1}}] is a matrix of field elements.
    See also: exactField; fieldBack.
*)
fieldEmbed[field_Association, data_] := Map[
    If[MatchQ[#, _Integer | _Rational | _AlgebraicNumber], #,
        If[field["Kind"] === "NumberField",
            With[{x = RootReduce[#]}, With[{mapped = Replace[x, field["Rules"]]},
                If[Head[mapped] === AlgebraicNumber || MatchQ[mapped, _Integer | _Rational], mapped,
                    Quiet[Replace[ToNumberField[x, field["Generator"]], Except[_AlgebraicNumber | _Integer | _Rational] -> x]]]]],
            RootReduce[#]]] &,
    data, {ArrayDepth[data]}];

(*
    Summary: Canonicalize computed values of an exact domain.
    Parameters: field; data — array computed from domain values.
    Options/defaults: None.
    Returns: data unchanged in a number field (arithmetic is already canonical); RootReduced otherwise.
    Effects: Pure.
    Failures: None.
    Example: fieldReduce[<|"Kind" -> "RootReduce"|>, {Sqrt[2]^2}] is {2}.
    See also: exactField.
*)
fieldReduce[field_Association, data_] := If[field["Kind"] === "NumberField", data, Map[RootReduce, data, {ArrayDepth[data]}]];

(*
    Summary: Complex conjugation in an exact domain.
    Parameters: field — from exactField; data — array of domain values.
    Options/defaults: None.
    Returns: The conjugated array, in the domain.
    Effects: Pure.
    Failures: None.
    Example: fieldConjugate[f, fieldEmbed[f, {I}]] is fieldEmbed[f, {-I}].
    Remarks: A number-field element sum_k c_k theta^k conjugates to sum_k c_k conj(theta)^k.
    See also: exactField.
*)
fieldConjugate[field_Association, data_] := If[field["Kind"] === "NumberField",
    Map[If[Head[#] === AlgebraicNumber, Take[Last[#], Length[field["ConjugatePowers"]]] . field["ConjugatePowers"], #] &,
        data, {ArrayDepth[data]}],
    Map[RootReduce[Conjugate[#]] &, data, {ArrayDepth[data]}]];

(*
    Summary: Conjugate transpose of a domain matrix.
    Parameters: field; m — domain matrix.
    Options/defaults: None.
    Returns: Transpose of the conjugated matrix.
    Effects: Pure.
    Failures: None.
    Example: fieldAdjoint[f, {{x, y}}] is {{conj x}, {conj y}}.
    See also: fieldConjugate.
*)
fieldAdjoint[field_Association, m_] := Transpose[fieldConjugate[field, m]];

(*
    Summary: Convert domain values back to canonical exact numbers.
    Parameters: data — array of domain values and rationals.
    Options/defaults: None.
    Returns: The array with RootReduced entries.
    Effects: Pure.
    Failures: None.
    Example: fieldBack[fieldEmbed[f, {Sqrt[2]}]] is {Sqrt[2]}.
    See also: fieldEmbed.
*)
fieldBack[data_] := Map[RootReduce, data, {ArrayDepth[data]}];

(*
    Summary: Decide that every entry of a domain array is zero.
    Parameters: data — array of domain values or expressions in them (default: number-field values).
    Options/defaults: None.
    Returns: True or False.
    Effects: Pure.
    Failures: None.
    Example: fieldZeroQ[{0, 0}] is True.
    Remarks: Number-field arithmetic reduces a zero element to 0; other exact values are RootReduced, so
        the test is exact in both domains.
    See also: exactField.
*)
fieldZeroQ[data_] := AllTrue[Flatten[{data}], # === 0 || (Head[#] =!= AlgebraicNumber && RootReduce[#] === 0) &];

(*
    Summary: A result identity (data == 0) decided at a Verification level (methodOptionsPlan.md 2C.4).
    Parameters: level — Automatic | "Exact" (exactly, fieldZeroQ) | "Numerical" (on N[] at precision, within the
        automatic tolerance) | None (not checked: True); data — exact domain values; precision — digits (default 50).
    Options/defaults: None.
    Returns: True or False; resultLevelStatus: the status a result checked at the level has ("Unverified" for None,
        "Numerical" for "Numerical" or numerical arithmetic, else "Exact"); resultLevelQ: InapplicableOption for
        "Exact" with numerical arithmetic, else True.
    Effects: Pure.
    Failures: None.
    Example: levelZeroQ[None, {1}] is True; levelZeroQ["Numerical", {Sqrt[2]^2 - 2}] is True.
    Remarks: Input, structural and positivity checks never go through this gate (C4).
    See also: fieldZeroQ; UnitarizeRepresentation; DiagonalizeRepresentationT.
*)
levelZeroQ[level_, data_, precision_ : 50] := Switch[level,
    None, True,
    "Numerical", With[{settings = arithmeticSettings["Numerical", precision, Automatic, Infinity]},
        TrueQ[Max[Append[Abs[N[Flatten[{data}], precision]], 0]] <= settings["Tolerance"]]],
    _, fieldZeroQ[data]];
resultLevelStatus[level_, arithmetic_] := Switch[level, None, "Unverified", "Numerical", "Numerical", _, If[arithmetic === "Numerical", "Numerical", "Exact"]];
resultLevelQ[level_, arithmetic_] := If[level === "Exact" && arithmetic === "Numerical",
    makeFailure["InapplicableOption", "Verification -> \"Exact\" cannot prove a result in numerical arithmetic; use Automatic, \"Numerical\" or None.",
        <|"Options" -> {Verification, Arithmetic}|>], True];

(*
    Summary: Null space, inverse and rank in an exact domain.
    Parameters: field; m — domain matrix.
    Options/defaults: None.
    Returns: fieldNullSpace — basis rows; fieldInverse — inverse matrix (canonical); fieldRank — integer.
    Effects: Pure.
    Failures: Inverse of a singular matrix returns the backend's unevaluated result.
    Example: fieldRank[f, IdentityMatrix[2]] is 2.
    Remarks: The RootReduce domain passes an exact zero test to the linear algebra.
    See also: exactField.
*)
fieldNullSpace[field_Association, m_] := If[field["Kind"] === "NumberField", NullSpace[m],
    fieldReduce[field, #] & /@ NullSpace[m, ZeroTest -> (RootReduce[#] === 0 &)]];
fieldInverse[field_Association, m_] := If[field["Kind"] === "NumberField", Inverse[m],
    fieldReduce[field, Inverse[m, ZeroTest -> (RootReduce[#] === 0 &)]]];
fieldRank[field_Association, m_] := If[field["Kind"] === "NumberField", MatrixRank[m],
    MatrixRank[m, ZeroTest -> (RootReduce[#] === 0 &)]];

(*
    Summary: Decide that an exact real algebraic number is positive.
    Parameters: x — field element or exact number.
    Options/defaults: None.
    Returns: True or False.
    Effects: Pure.
    Failures: None; nonreal values are not positive.
    Example: positiveExactQ[Sqrt[2] - 1] is True.
    See also: checkPositiveForm; fieldPositiveFormQ.
*)
positiveExactQ[x_] := With[{r = RootReduce[x]}, r =!= 0 && Element[r, Reals] && TrueQ[r > 0]];

(*
    Summary: Decide that a domain matrix is a positive definite Hermitian form.
    Parameters: field; h — square domain matrix.
    Options/defaults: None.
    Returns: True or False.
    Effects: Pure.
    Failures: None.
    Example: fieldPositiveFormQ[f, IdentityMatrix[2]] is True.
    Remarks: Hermitian equality is decided in the domain; the leading principal minors (Sylvester) are
        computed in the domain and then tested for positivity.
    See also: checkPositiveForm.
*)
fieldPositiveFormQ[field_Association, h_] := fieldZeroQ[h - fieldAdjoint[field, h]] &&
    AllTrue[Table[Det[h[[;; k, ;; k]]], {k, Length[h]}], positiveExactQ];

(*
    Summary: Evaluate a group word on field matrices.
    Parameters: matrices — ordered generator matrices (domain values or approximate numbers); word —
        GroupWord or text; names — ordered generator names; dimension — matrix size; field — exact domain
        from exactField, or None for plain arithmetic.
    Options/defaults: field None.
    Returns: The product matrix in the field, or Failure for an invalid word.
    Effects: Pure.
    Failures: As normalizeWord.
    Example: fieldWordMatrix[{m}, GroupWord[{{"t", 2}}], {"t"}, 2] is m . m.
    See also: wordMatrix.
*)
fieldWordMatrix[matrices_List, word_, names_List, dimension_Integer, field_ : None] := Module[{normalized, table, inverses = <||>, product, reduce, inverse},
    normalized = normalizeWord[word, names]; If[FailureQ[normalized], Return[normalized]];
    reduce = If[field === None, Identity, fieldReduce[field, #] &];
    inverse = If[field === None, Inverse, fieldInverse[field, #] &];
    table = AssociationThread[names, matrices];
    product = IdentityMatrix[dimension];
    Do[With[{base = If[Last[syllable] > 0, table[First[syllable]],
            Lookup[inverses, First[syllable], inverses[First[syllable]] = inverse[table[First[syllable]]]]]},
        Do[product = reduce[product . base], {Abs[Last[syllable]]}]],
        {syllable, First[normalized]}];
    product
];

Options[UnitaryRepresentationQ] = {Tolerance -> Automatic};

(*
    Summary: Test whether every generator matrix of a representation value is unitary.
    Status: Alpha.
    Parameters: r — Rep value.
    Options/defaults: Tolerance -> Automatic (numerical input only: 10^(-Floor[p/2]) for precision p).
    Returns: True or False; Failure for an invalid Rep or options.
    Effects: Pure; no group binding is needed because unitarity is a property of the matrices.
    Failures: InvalidRep/SingularRep; an explicit Tolerance with exact input (exact mode never
        substitutes a tolerance for proof) is InapplicableOption.
    Example: UnitaryRepresentationQ[Rep[{{{0, 1}, {1, 0}}}]] is True.
    Remarks: Every generator matrix is checked, not only S and T. Unitary generators make every
        element matrix unitary.
    See also: UnitarizeRepresentation; unitaryMatricesCheck.
*)
UnitaryRepresentationQ[rep_Rep, options : OptionsPattern[]] := Module[{effective, shape, settings},
    effective = resolveOperationOptions[UnitaryRepresentationQ, "UnitaryRepresentationQ", {options}];
    If[FailureQ[effective], Return[effective]];
    shape = validateRepShape[rep]; If[FailureQ[shape], Return[shape]];
    If[shape["Arithmetic"] === "Exact" && effective[Tolerance] =!= Automatic,
        Return[makeFailure["InapplicableOption", "Tolerance applies only to numerical matrices."]]];
    settings = arithmeticSettings[shape["Arithmetic"], shape["Precision"], effective[Tolerance], shape["Precision"]];
    unitaryMatricesCheck[repMatrices[rep], settings]["Holds"]
];
UnitaryRepresentationQ[___] := makeFailure["InvalidInput", "UnitaryRepresentationQ expects one Rep and options."];

(* -------------------------------------------------------------------------
   Group-aware validation: characters, relators, multiplicities
   ------------------------------------------------------------------------- *)

(*
    Summary: Class values (traces on the bound class representative words) of a bound representation.
    Parameters: operand — from representationOperand; settings — from arithmeticSettings.
    Options/defaults: None.
    Returns: List of values in the order of the snapshot's ClassIDs (canonical exact numbers, or
        numerical values), or Failure.
    Effects: Pure.
    Failures: Word evaluation failures.
    Example: for the standard representation of S3 the values are {2, 0, -1}.
    Remarks: Exact traces are computed in an exact domain of the entries (exactField).
    See also: RepresentationCharacter; decompositionMultiplicities.
*)
repClassValues[operand_Association, settings_Association] := Module[{words, names, d, field, matrices, traces},
    words = operand["Snapshot"]["CharacterData"]["ClassRepresentativeWords"];
    names = operand["Names"]; d = operand["Shape"]["Dimension"];
    If[settings["Arithmetic"] === "Exact",
        field = settingsField[operand["Matrices"], settings];
        matrices = fieldEmbed[field, operand["Matrices"]];
        traces = Tr[fieldWordMatrix[matrices, #, names, d, field]] & /@ words;
        Return[RootReduce /@ traces]];
    matrices = toArithmetic[operand["Matrices"], settings];
    Tr[fieldWordMatrix[matrices, #, names, d]] & /@ words
];

(*
    Summary: Relators of a complete presentation on the recorded generators.
    Parameters: context — Group or RepresentationContext; snapshot — its resolved snapshot; options —
        validated GAP job settings (used only to certify a live group).
    Options/defaults: None.
    Returns: List of GroupWord relators on the recorded generator names, or Failure.
    Effects: For a live Group without a certificate, runs the GeneratorPresentation enrichment (one new
        generation holding the certificate).
    Failures: PresentationUnavailable for a context whose presentation cannot be obtained without a live
        group; enrichment failures.
    Example: a group built from GroupPresentation[{"s","t"}, {"s^2","t^2","(s.t)^3"}] has those relators.
    Remarks: Rule (S2.5): a live Group uses its certified presentation (computed once when absent); a
        context uses a presentation-type construction, else the certificate of an accepted live group with
        the same state and generator identities in this kernel; otherwise it fails. A matrix assignment is a
        homomorphism of the actual group exactly when every relator of a complete presentation maps to the
        identity (plan: complete presentation, not displayed defining relations).
    See also: mapTargetSpecification; runGroupEnrichment; validateRepBinding.
*)
presentationRelators[context_, snapshot_Association, options_Association] := Module[
    {construction = snapshot["Construction"], decode, certificate, candidates, accepted, result},
    decode[relators_, names_] := decodeRelatorWords[relators, names, snapshot["GeneratorNames"]];
    If[Lookup[construction, "type", None] === "presentation",
        With[{words = decode[construction["relators"], construction["names"]]}, If[words =!= $Failed, Return[words]]]];
    certificate[data_] := With[{specification = mapTargetSpecification[data]},
        If[AssociationQ[specification], specification["presentation"], Missing["NotComputed"]]];
    If[MatchQ[context, _Group],
        accepted = groupData[context]; If[FailureQ[accepted], Return[accepted]];
        If[MissingQ[certificate[accepted]],
            (* The caller's Method (for example a decomposition method) is not a presentation method. *)
            result = runGroupEnrichment[context, "GeneratorPresentation", <||>, Join[options, <|Method -> Automatic|>]];
            If[FailureQ[result], Return[result]];
            accepted = groupData[context]];
        result = certificate[accepted],
        candidates = Select[groupData /@ Keys[$GroupRegistry], AssociationQ[#] &&
            #["StateID"] === snapshot["GroupIdentity"] && #["GeneratorIdentity"] === snapshot["GeneratorIdentity"] &];
        result = SelectFirst[certificate /@ candidates, AssociationQ, Missing["NotComputed"]]];
    If[!AssociationQ[result],
        Return[makeFailure["PresentationUnavailable",
            "No certified presentation of the recorded generators is available for this context; validate with the live group."]]];
    With[{words = decode[result["relators"], result["names"]]},
        If[words === $Failed, makeFailure["PresentationUnavailable", "The certified presentation uses other generator names."], words]]
];

(*
    Summary: Decode exported relator words on the recorded generator names.
    Parameters: relators — lists of {name, exponent string}; names — the certificate's generator names;
        expected — the recorded generator names.
    Options/defaults: None.
    Returns: GroupWord relators, or $Failed when the names differ.
    Effects: Pure.
    Failures: $Failed.
    Example: decodeRelatorWords[{{{"s", "2"}}}, {"s"}, {"s"}] is {GroupWord[{{"s", 2}}]}.
    See also: presentationRelators; snapshotRelators.
*)
decodeRelatorWords[relators_, names_, expected_] := If[names =!= expected, $Failed,
    GroupWord[Map[{First[#], ToExpression[Last[#]]} &, #]] & /@ relators];

(*
    Summary: Complete relators of a snapshot from its presentation construction or a given certificate.
    Parameters: snapshot — context snapshot; certificate — native generatorPresentation record or Missing.
    Options/defaults: None; no GAP work.
    Returns: GroupWord relators, or PresentationUnavailable Failure.
    Effects: Pure.
    Failures: PresentationUnavailable.
    Example: a presentation-type construction supplies its own relators.
    Remarks: For verified import candidates, whose certificate GAP checked on import (R1 inert variants).
    See also: presentationRelators; verifyInertVariants.
*)
snapshotRelators[snapshot_Association, certificate_] := Module[{construction = snapshot["Construction"], words = $Failed},
    If[Lookup[construction, "type", None] === "presentation",
        words = decodeRelatorWords[construction["relators"], construction["names"], snapshot["GeneratorNames"]]];
    If[words === $Failed && AssociationQ[certificate],
        words = decodeRelatorWords[certificate["relators"], certificate["names"], snapshot["GeneratorNames"]]];
    If[words === $Failed, makeFailure["PresentationUnavailable", "No certified presentation of the recorded generators is available."], words]
];

(*
    Summary: Decide whether generator matrices satisfy every relator.
    Parameters: operand; relators — GroupWord relators; settings.
    Options/defaults: None.
    Returns: <|"Holds" -> Boolean|> (exact), with "Residual" in numerical mode.
    Effects: Pure.
    Failures: None.
    Example: the standard S3 matrices satisfy s^2, t^2 and (s.t)^3.
    Remarks: Exact relator products are computed in an exact domain of the entries.
    See also: presentationRelators; validateRepBinding.
*)
relatorCheck[operand_Association, relators_List, settings_Association] := Module[{d, names, field, matrices, checks},
    d = operand["Shape"]["Dimension"]; names = operand["Names"];
    If[settings["Arithmetic"] === "Exact",
        field = settingsField[operand["Matrices"], settings];
        matrices = fieldEmbed[field, operand["Matrices"]];
        Return[<|"Holds" -> AllTrue[relators, fieldZeroQ[fieldWordMatrix[matrices, #, names, d, field] - IdentityMatrix[d]] &]|>]];
    matrices = toArithmetic[operand["Matrices"], settings];
    checks = checkMatrixIdentity[fieldWordMatrix[matrices, #, names, d], IdentityMatrix[d], settings] & /@ relators;
    <|"Holds" -> AllTrue[checks, #["Holds"] &], "Residual" -> Max[Append[Lookup[checks, "Residual", 0], 0]]|>
];

(*
    Summary: Irreducible-character multiplicities from class values.
    Parameters: snapshot — resolved context snapshot; values — class values (repClassValues); dimension;
        settings.
    Options/defaults: None.
    Returns: Association irrep ID -> multiplicity (nonzero only, canonical order), or Failure.
    Effects: Pure.
    Failures: InvalidRepresentation when exact multiplicities are not nonnegative integers or the degrees do
        not sum to the dimension; AmbiguousMultiplicity when a numerical multiplicity is not within the
        tolerance of an integer.
    Example: the regular representation of S3 gives <|trivial -> 1, sign -> 1, standard -> 2|>.
    Remarks: m_chi = |G|^-1 sum_C |C| conj(chi(C)) tr(rho(C)).
    See also: DecomposeRepresentation; ValidateRepresentation.
*)
decompositionMultiplicities[snapshot_Association, values_List, dimension_Integer, settings_Association] := Module[
    {characters = snapshot["CharacterData"], raw, rounded, degrees},
    raw = Table[Total[characters["ClassSizes"] Conjugate[characters["Values"][[i]]] values] / snapshot["Order"],
        {i, Length[characters["IrrepIDs"]]}];
    degrees = characters["Degrees"];
    If[settings["Arithmetic"] === "Exact",
        raw = RootReduce /@ raw;
        If[!AllTrue[raw, IntegerQ[#] && # >= 0 &] || raw . degrees =!= dimension,
            Return[makeFailure["InvalidRepresentation", "The class values are not a character of the group."]]];
        rounded = raw,
        rounded = Round[Re[raw]];
        If[Max[Abs[raw - rounded]] > settings["Tolerance"] Max[1, dimension] || Min[rounded] < 0 || rounded . degrees =!= dimension,
            Return[makeFailure["AmbiguousMultiplicity", "The numerical multiplicities are not resolved to integers at this precision.",
                <|"Multiplicities" -> raw|>]]]];
    Select[AssociationThread[characters["IrrepIDs"], rounded], # > 0 &]
];

(*
    Summary: The bound irreducible character matched by a representation's class values, if any.
    Parameters: context — Group or RepresentationContext; rep — Rep.
    Options/defaults: Exact arithmetic.
    Returns: The irrep ID whose character row equals the exact class values, None, or Failure.
    Effects: Resolving a Group registers its context binding.
    Failures: As representationOperand; NumericalInput for numerical matrices.
    Example: matchRepCharacter[g, GroupRepresentation[g, id]] is id.
    See also: validateRepBinding; decompositionMultiplicities.
*)
matchRepCharacter[context_, rep_] := Module[{operand, settings, values, rows, position},
    operand = representationOperand[context, rep]; If[FailureQ[operand], Return[operand]];
    settings = arithmeticSettings["Exact", Infinity, Automatic, operand["Shape"]["Precision"]];
    If[FailureQ[settings], Return[settings]];
    values = repClassValues[operand, settings];
    rows = operand["Snapshot"]["CharacterData"]["Values"];
    position = FirstPosition[rows, row_ /; AllTrue[RootReduce[row - values], # === 0 &], None, {1}, Heads -> False];
    If[position === None, None, operand["Snapshot"]["CharacterData"]["IrrepIDs"][[First[position]]]]
];

(*
    Summary: Validate a representation against a bound group: homomorphism, character, basis properties.
    Parameters: context — Group or RepresentationContext; rep — Rep; requirements —
        <|"Settings" -> arithmetic settings, "Options" -> GAP job settings, optional "IrrepID" -> required
        irrep, optional "Basis" -> "Unitary" | "General"|>.
    Options/defaults: Without IrrepID nothing is required of the character.
    Returns: The ValidateRepresentation association, or Failure.
    Effects: May certify a live group's presentation (presentationRelators).
    Failures: Binding, relator and multiplicity failures; WrongCharacter when a required irrep is not the
        matched one; NonUnitaryRepresentation when a unitary basis is required and the matrices are not
        unitary; InvalidRepresentation when a required irrep's matrices are not a homomorphism.
    Example: validateRepBinding[g, r, <|"Settings" -> exact, "Options" -> opts|>]["Homomorphism"] is True
        for verified matrices of g.
    Remarks: An exact irreducible claim is a single exact row of multiplicity one (hence the degree) and the
        exact homomorphism check. A numerical claim is the same match with numerically resolved multiplicities
        and relator residuals within the tolerance; its Status is "Numerical" and it is never an exact
        certificate.
    See also: ValidateRepresentation; DecomposeRepresentation (target validation).
*)
validateRepBinding[context_, rep_, requirements_Association] := Module[{operand, relators},
    operand = representationOperand[context, rep]; If[FailureQ[operand], Return[operand]];
    relators = presentationRelators[context, operand["Snapshot"], requirements["Options"]];
    If[FailureQ[relators], Return[relators]];
    validateRepOperand[operand, relators, requirements]
];

(*
    Summary: The checks of validateRepBinding on a resolved operand and its relators.
    Parameters: operand — representationOperand-shaped association; relators — GroupWord relators;
        requirements — as validateRepBinding.
    Options/defaults: As validateRepBinding.
    Returns: As validateRepBinding.
    Effects: Pure.
    Failures: As validateRepBinding (after the context and relators are resolved).
    Example: validateRepOperand[operand, relators, <|"Settings" -> exact, "IrrepID" -> id|>]["Irreducible"] is id.
    See also: validateRepBinding; verifyInertVariants.
*)
(* The basis facts of a representation's matrices (unitarity on every generator; T-diagonality under the group's
   assignment, Missing["NotAssigned"] without one) in the given arithmetic: what an unchecked (Verification -> None)
   record states, as validateRepOperand computes them. *)
repBasisFacts[data_Association, rep_Rep, settings_Association] := Module[{matrices = toArithmetic[repMatrices[rep], settings], assignment = data["ModularAssignment"]},
    <|"Unitary" -> unitaryMatricesCheck[matrices, settings]["Holds"],
        "TDiagonal" -> If[!AssociationQ[assignment], Missing["NotAssigned"],
            With[{t = fieldWordMatrix[matrices, assignment["T"], Lookup[data["Generators"], "Name", {}], RepDim[rep]]},
                checkMatrixIdentity[t, DiagonalMatrix[Diagonal[t]], settings]["Holds"]]]|>];

validateRepOperand[operand_Association, relators_List, requirements_Association] := Module[
    {settings, homomorphism, values, multiplicities, irreducible, unitary, tDiagonal, assignment, result},
    settings = requirements["Settings"];
    homomorphism = relatorCheck[operand, relators, settings];
    values = repClassValues[operand, settings];
    multiplicities = If[homomorphism["Holds"],
        decompositionMultiplicities[operand["Snapshot"], values, operand["Shape"]["Dimension"], settings],
        Missing["NotAHomomorphism"]];
    If[FailureQ[multiplicities], Return[multiplicities]];
    irreducible = If[AssociationQ[multiplicities] && Values[multiplicities] === {1}, First[Keys[multiplicities]], None];
    unitary = unitaryMatricesCheck[toArithmetic[operand["Matrices"], settings], settings];
    assignment = operand["Snapshot"]["ModularAssignment"];
    tDiagonal = If[!AssociationQ[assignment], Missing["NotAssigned"],
        With[{t = fieldWordMatrix[toArithmetic[operand["Matrices"], settings], assignment["T"], operand["Names"],
                operand["Shape"]["Dimension"]]},
            checkMatrixIdentity[t, DiagonalMatrix[Diagonal[t]], settings]["Holds"]]];
    result = Join[<|"GroupIdentity" -> operand["Snapshot"]["GroupIdentity"],
        "GeneratorIdentity" -> operand["Snapshot"]["GeneratorIdentity"], "Dimension" -> operand["Shape"]["Dimension"],
        "Arithmetic" -> settings["Arithmetic"], "Status" -> settings["Arithmetic"],
        "Homomorphism" -> homomorphism["Holds"],
        "Character" -> AssociationThread[operand["Snapshot"]["CharacterData"]["ClassIDs"], values],
        "Multiplicities" -> multiplicities, "Irreducible" -> irreducible,
        "BasisProperties" -> <|"Unitary" -> unitary["Holds"], "TDiagonal" -> tDiagonal|>|>,
        If[settings["Arithmetic"] === "Exact", <||>,
            <|"Precision" -> settings["Precision"], "Tolerance" -> settings["Tolerance"],
                "Residuals" -> <|"Relators" -> homomorphism["Residual"], "Unitary" -> unitary["Residual"]|>|>]];
    Which[
        KeyExistsQ[requirements, "IrrepID"] && !result["Homomorphism"],
            makeFailure["InvalidRepresentation", "The matrices do not satisfy the group's relators.", <|"Validation" -> result|>],
        KeyExistsQ[requirements, "IrrepID"] && result["Irreducible"] =!= requirements["IrrepID"],
            makeFailure["WrongCharacter", "The matrices do not afford the required irreducible character.",
                <|"IrrepID" -> requirements["IrrepID"], "Validation" -> result|>],
        Lookup[requirements, "Basis", "General"] === "Unitary" && !result["BasisProperties"]["Unitary"],
            makeFailure["NonUnitaryRepresentation", "A unitary basis is required.", <|"Validation" -> result|>],
        True, result]
];

(*
    Summary: Verify every inert (Wolfram-exact or numerical) variant of group data in Wolfram (R1).
    Parameters: data — decoded group data (an import candidate or accepted data); certificate — the
        verified generatorPresentation record or Missing.
    Options/defaults: Numerical variants are checked at their declared precision with the automatic tolerance.
    Returns: True, or the first Failure (with the irrep and variant IDs).
    Effects: Pure; no GAP work.
    Failures: PresentationUnavailable; InvalidRepresentation, WrongCharacter or NonUnitaryRepresentation for a
        variant that is not the irrep's representation or does not have its recorded properties
        (InvalidInertVariant, with the cause).
    Example: an imported Wolfram-tier variant with the matrices of another irrep fails with WrongCharacter.
    Remarks: The acceptance check of the mutation functions and of correspondence import; registered imports
        trust the receipt instead. Recorded T-diagonality is rechecked under the data's assignment.
    See also: validateRepOperand; decodeInertVariant; validateImportedGroupScoped.
*)
verifyInertVariants[data_Association, certificate_] := Module[{snapshot, relators, representations},
    representations = Lookup[data, "Representations", <||>];
    If[!AssociationQ[representations] || !AnyTrue[Values[representations],
            AnyTrue[Values[#["Variants"]], MemberQ[{"Wolfram", "Numerical"}, #["Tier"]] &] &],
        Return[True]];
    snapshot = contextSnapshot[data];
    relators = snapshotRelators[snapshot, certificate]; If[FailureQ[relators], Return[relators]];
    Catch[
        KeyValueMap[Function[{id, entry}, KeyValueMap[Function[{variantID, variant},
            If[MemberQ[{"Wolfram", "Numerical"}, variant["Tier"]],
                With[{result = inertVariantCheck[snapshot, relators, id, variant]},
                    If[FailureQ[result], Throw[makeFailure["InvalidInertVariant", "An inert representation variant failed verification.",
                        <|"IrrepID" -> id, "VariantID" -> variantID, "Cause" -> result|>], verifyInertVariants]]]]],
            entry["Variants"]]], representations];
        True,
        verifyInertVariants]
];
verifyInertVariants[___] := makeFailure["InvalidInertVariant", "Expected group data and a presentation certificate."];

(*
    Summary: Verify one inert variant against a snapshot: irrep, recorded unitarity and T-diagonality.
    Parameters: snapshot; relators; id — irrep ID; variant — decoded variant.
    Options/defaults: As verifyInertVariants.
    Returns: The validateRepOperand result, or Failure.
    Effects: Pure.
    Failures: As validateRepOperand; InvalidRepresentation when a recorded property does not hold.
    Example: inertVariantCheck[snapshot, relators, id, variant]["Irreducible"] is id.
    See also: verifyInertVariants; acceptInertRepresentation.
*)
inertVariantCheck[snapshot_Association, relators_List, id_String, variant_Association] := Module[
    {shape, settings, operand, result},
    shape = validateRepShape[variant["Rep"]]; If[FailureQ[shape], Return[shape]];
    settings = arithmeticSettings[If[variant["Tier"] === "Numerical", "Numerical", "Exact"], shape["Precision"] /. Infinity -> 50,
        Automatic, shape["Precision"]];
    If[FailureQ[settings], Return[settings]];
    operand = <|"Snapshot" -> snapshot, "Shape" -> shape, "Matrices" -> repMatrices[variant["Rep"]], "Names" -> snapshot["GeneratorNames"]|>;
    result = validateRepOperand[operand, relators, <|"Settings" -> settings, "IrrepID" -> id,
        "Basis" -> If[TrueQ[variant["BasisProperties"]["Unitary"]], "Unitary", "General"]|>];
    If[FailureQ[result], Return[result]];
    If[!TrueQ[variant["BasisProperties"]["Unitary"]] && TrueQ[result["BasisProperties"]["Unitary"]] ||
        TrueQ[variant["BasisProperties"]["TDiagonal"]] && !TrueQ[result["BasisProperties"]["TDiagonal"]],
        Return[makeFailure["InvalidRepresentation", "The recorded basis properties do not hold."]]];
    result
];

Options[RepresentationCharacter] = {FieldMethod -> Automatic, Arithmetic -> "Exact", WorkingPrecision -> 50, Tolerance -> Automatic};

(*
    Summary: Class values of a representation on the bound conjugacy classes.
    Status: Alpha.
    Parameters: c — Group or RepresentationContext; r — Rep with one matrix per recorded generator.
    Options/defaults: Arithmetic -> "Exact"; WorkingPrecision -> 50; Tolerance -> Automatic (numerical only).
    Returns: Association class ID -> value, in the context's class order.
    Effects: Resolving a Group registers its context binding; no GAP work.
    Failures: UnverifiedContext, InvalidRep, GeneratorBindingMismatch, NumericalInput.
    Example: RepresentationCharacter[g, GroupRepresentation[g, id]] equals row id of g's character table.
    Remarks: Works for reducible representations. It evaluates traces on the bound class representative
        words and does not by itself certify r as a representation of the group (ValidateRepresentation).
    See also: ValidateRepresentation; DecomposeRepresentation.
*)
RepresentationCharacter[context : (_Group | _RepresentationContext), rep_Rep, options : OptionsPattern[]] := cgFieldCatch[representationCharacterFieldWork[context, rep, options]];
representationCharacterFieldWork[context : (_Group | _RepresentationContext), rep_Rep, options : OptionsPattern[]] := Module[
    {effective, operand, settings},
    effective = resolveOperationOptions[RepresentationCharacter, "RepresentationCharacter", {options}];
    If[FailureQ[effective], Return[effective]];
    operand = representationOperand[context, rep]; If[FailureQ[operand], Return[operand]];
    settings = arithmeticSettings[effective[Arithmetic], effective[WorkingPrecision], effective[Tolerance],
        operand["Shape"]["Precision"]];
    If[FailureQ[settings], Return[settings]];
    settings = Join[settings, <|"FieldMethod" -> effective[FieldMethod]|>];
    AssociationThread[operand["Snapshot"]["CharacterData"]["ClassIDs"], repClassValues[operand, settings]]
];
RepresentationCharacter[___] := makeFailure["InvalidInput", "RepresentationCharacter expects a Group or RepresentationContext, a Rep and options."];

Options[ValidateRepresentation] = Join[Options[RestoreGAPState], {FieldMethod -> Automatic, Arithmetic -> "Exact", WorkingPrecision -> 50, Tolerance -> Automatic,
    Verification -> Automatic}];

(*
    Summary: Validate a representation value against a bound group.
    Status: Alpha.
    Parameters: c — Group or RepresentationContext; r — Rep with one matrix per recorded generator.
    Options/defaults: Arithmetic -> "Exact"; WorkingPrecision -> 50 and Tolerance -> Automatic for numerical
        arithmetic; Verification -> Automatic (the Arithmetic), "Exact" (InapplicableOption with numerical arithmetic)
        or "Numerical" (the checks on N[] at WorkingPrecision; None is InvalidOption); common GAP job options (used only
        to certify a live group's presentation once).
    Returns: <|"GroupIdentity", "GeneratorIdentity", "Dimension", "Arithmetic", "Status", "Homomorphism",
        "Character", "Multiplicities", "Irreducible", "BasisProperties", "VerificationStatus" (the level of the checks,
        bounded by the group's status)|> (+ "Precision", "Tolerance",
        "Residuals" when numerical); Multiplicities is Missing["NotAHomomorphism"] when the relators fail;
        Irreducible is the matched irrep ID of an irreducible representation (exact, or numerical with
        Status "Numerical"), otherwise None.
    Effects: May run one GAP enrichment that certifies a live group's presentation. On a live group the
        result is cached (CacheKinds "Unitarity"; cleared by CleanRepresentationCache and by a new modular
        assignment).
    Failures: UnverifiedContext, InvalidRep, GeneratorBindingMismatch, NumericalInput,
        PresentationUnavailable, AmbiguousMultiplicity, InvalidRepresentation (class values that are not
        a character).
    Example: ValidateRepresentation[g, GroupRepresentation[g, id]]["Irreducible"] is id.
    Remarks: The homomorphism check uses a complete presentation on the recorded generators. A proven
        invalid result (Homomorphism False) is distinct from a failure (undecided or unavailable data).
        Unitarity checks every generator.
    See also: validateRepBinding; RepresentationCharacter; DecomposeRepresentation.
*)
ValidateRepresentation[context : (_Group | _RepresentationContext), rep_Rep, options : OptionsPattern[]] := cgFieldCatch[validateRepresentationFieldWork[context, rep, options]];
validateRepresentationFieldWork[context : (_Group | _RepresentationContext), rep_Rep, options : OptionsPattern[]] := Module[
    {effective, shape, settings, key, result, allowed},
    effective = resolveOperationOptions[ValidateRepresentation, "ValidateRepresentation", {options}];
    If[FailureQ[effective], Return[effective]];
    shape = validateRepShape[rep]; If[FailureQ[shape], Return[shape]];
    allowed = checkLevelQ["ValidateRepresentation", effective[Verification], effective[Arithmetic] === "Numerical"]; If[FailureQ[allowed], Return[allowed]];
    (* Verification -> "Numerical" runs the checks in numerical arithmetic at WorkingPrecision (2C.4) *)
    settings = arithmeticSettings[If[effective[Verification] === "Numerical", "Numerical", effective[Arithmetic]], effective[WorkingPrecision],
        effective[Tolerance], shape["Precision"]];
    If[FailureQ[settings], Return[settings]];
    settings = Join[settings, <|"FieldMethod" -> effective[FieldMethod]|>];
    (* On a live group the result is a derived cache entry (Unitarity), cleared when the assignment changes. *)
    key = If[MatchQ[context, _Group], {"Validate", Hash[rep, "SHA256"], settings}, None];
    If[key =!= None, result = representationCacheLookup[context, "Unitarity", key]];
    If[key === None || MissingQ[result],
        result = validateRepBinding[context, rep, <|"Settings" -> settings, "Options" -> effective|>];
        If[key =!= None && !FailureQ[result], representationCacheStore[context, "Unitarity", <|key -> result|>]]];
    (* the level of the checks ("CheckStatus", relative to the group's recorded data: its relators and class words), and the
       report's status bounded by the group's (read now: a cached report predates later statuses) *)
    If[AssociationQ[result], With[{check = If[settings["Arithmetic"] === "Numerical", "Numerical", "Exact"]},
        Join[result, <|"CheckStatus" -> check, "VerificationStatus" -> cgWeakestStatus[{check,
            groupVerificationStatus[If[MatchQ[context, _Group], groupData[context], First[context]]]}]|>]], result]
];
(*
    Summary: Validate a stored irrep's active variant and store it again at the level the check establishes (write-back,
        methodOptionsPlan.md 2C.3).
    Status: Alpha.
    Parameters: g — live Group; id — irrep ID.
    Options/defaults: As ValidateRepresentation (Verification Automatic, "Exact" or "Numerical"; Arithmetic of the checks)
        and the common GAP job options of the re-store.
    Returns: The ValidateRepresentation report of the active variant with "WrittenBack" -> True when its stored status was
        raised (or Failure from the re-store), False when the check established nothing stronger or did not pass.
    Effects: When the check passes as the irrep at a level ("CheckStatus", not bounded by the group) above the stored
        status, the same matrices are stored again at that level and made active (SetGroupRepresentation; one GAP generation): an exactly checked cyclotomic variant is
        then admitted natively by GAP's VerifyRep (C7), others as inert records with the new status. The weak variant
        stays stored, inactive, with its status. The new variant has the same matrices, so the same realization identity:
        stored CG entries keep matching it.
    Failures: InvalidIrrepID; MissingRepresentation; as ValidateRepresentation and SetGroupRepresentation.
    Example: ValidateRepresentation[g, id] after ComputeGroupRepresentations[g, id, Verification -> None] makes an exact
        variant active.
    See also: SetGroupRepresentation; variantVerificationStatus.
*)
ValidateRepresentation[group_Group, id_String, options : OptionsPattern[]] := Module[{data, entry, variant, report, stored, level, basis, written},
    data = groupData[group]; If[FailureQ[data], Return[data]];
    If[!MemberQ[data["CharacterData"]["IrrepIDs"], id],
        Return[makeFailure["InvalidIrrepID", "The irrep ID is not in the group's character table.", <|"IrrepID" -> id|>]]];
    entry = Lookup[data["Representations"], id, None];
    If[!AssociationQ[entry] || !StringQ[entry["ActiveVariant"]],
        Return[makeFailure["MissingRepresentation", "The irrep has no active representation.", <|"IrrepID" -> id|>]]];
    variant = entry["Variants"][entry["ActiveVariant"]];
    report = ValidateRepresentation[group, variant["Rep"], options];
    If[FailureQ[report], Return[report]];
    (* the variant is stored at what the check established; readers bound it by the group's status (2C.6), so a weak
       group's variant is not held back until ValidateGroup *)
    stored = variantVerificationStatus[variant]; level = report["CheckStatus"];
    If[!TrueQ[report["Homomorphism"]] || report["Irreducible"] =!= id || cgStatusRank[level] <= cgStatusRank[stored],
        Return[Join[report, <|"WrittenBack" -> False|>]]];
    basis = If[TrueQ[report["BasisProperties"]["Unitary"]], "Unitary", "General"];
    written = SetGroupRepresentation[group, id, variant["Rep"], Basis -> basis, Verification -> If[level === "Exact", Automatic, "Numerical"],
        Sequence @@ FilterRules[{options}, Options[RestoreGAPState]]];
    If[FailureQ[written], written, Join[report, <|"WrittenBack" -> True|>]]
];
ValidateRepresentation[group_Group, k_Integer, rest___] := withIrreps[group, {k}, ValidateRepresentation[group, #, rest] &];
ValidateRepresentation[___] := makeFailure["InvalidInput", "ValidateRepresentation expects a Group or RepresentationContext, a Rep and options."];

True
