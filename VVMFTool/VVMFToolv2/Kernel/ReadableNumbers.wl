(*
    :Title: Readable exact numbers
    :Context: VVMFTool`Private`
    :Summary: Exact algebraic values as the user should see them: rationals, m Exp[2 Pi I k/n] for rational multiples of
        roots of unity, radical expressions otherwise, a Root object only when no radical form is found (uxUpdatePlan.md
        3, U8). Applied where values are returned to the user; stored values, digests and cache keys keep their
        canonical forms (P4).
    :Responsibilities: readableScalar, readableMatrix, readableExpression, cyclotomicTerms, readableConductors
        (latticeCyclotomicCoordinates, shared with exact code, lives in RepresentationValidation.wl).
    :Dependencies: DisplayNotation.wl (exactAlgebraicQ, certifiedRootOfUnityPhase, displayRadical); RepresentationJobs.wl
        (cyclotomicEncoding); GroupObject.wl ($GroupRegistry).
    :See Also: VVMFArch/uxUpdatePlan.md section 3.
*)

$ReadableScalarMemo = <||>;
$ReadableConductors = Automatic;
$ReadableConductorCache = {None, {}};

(*
    Summary: Candidate cyclotomic conductors for readable values, and a value as a sum of rational multiples of roots
        of unity.
    Parameters: x — exact number; orders — candidate conductors (ascending: the smallest field containing x wins).
    Options/defaults: $ReadableConductors (Automatic: from the exponents e of the live groups, the divisors > 2 of
        lcm(e, 4); a caller may Block it to the conductors of one group).
    Returns: readableConductors: list of integers. cyclotomicTerms: {{c, r}, ...} with rational c != 0 and r = k/n in
        [0, 1), whose sum of c Exp[2 Pi I r] equals x (certified), or $Failed.
    Effects: readableConductors caches per set of live groups.
    Failures: $Failed when x is in none of the fields or equality cannot be certified within 10 seconds.
    Example: cyclotomicTerms[RootReduce[Exp[2 Pi I/7] + Exp[-2 Pi I/7]], {7}] is {{1, 1/7}, {1, 6/7}} up to the
        power basis of Q(zeta_7).
    Remarks: The native decoder's cyclotomic hint when recorded, else ToNumberField on zeta_n for the listed conductors
        (smallest first): candidate coordinates from an integer relation (latticeCyclotomicCoordinates), accepted only when
        the AlgebraicNumber RootReduces to x, so the terms are exact. Results are memoized (failures too, except a
        search cut by the display budget, withReadableBudget).
    See also: readableScalar; scalarDisplayNode.
*)
readableConductors[] := Module[{keys, exponents},
    If[ListQ[$ReadableConductors], Return[$ReadableConductors]];
    keys = Keys[$GroupRegistry];
    If[First[$ReadableConductorCache] === keys, Return[Last[$ReadableConductorCache]]];
    exponents = DeleteDuplicates[Cases[Values[$GroupRegistry], s_Association :> With[{orders = Lookup[Lookup[s, "CharacterData", <||>], "ClassOrders", {}]},
        If[ListQ[orders] && orders =!= {} && AllTrue[orders, IntegerQ], LCM @@ orders, Nothing]]]];
    $ReadableConductorCache = {keys, groupConductors[exponents]};
    Last[$ReadableConductorCache]];
groupConductors[exponents_List] := Sort[DeleteDuplicates[Select[Flatten[Divisors[LCM[#, 4]] & /@ exponents], # > 2 &]]];
cyclotomicTerms[x_, orders_List] := Module[{reduced, hint, degree, variable, attempt, found},
    If[!exactAlgebraicQ[x], Return[$Failed]];
    reduced = Quiet[TimeConstrained[RootReduce[x], 10, $Failed]];
    If[reduced === $Failed || MatchQ[reduced, _Integer | _Rational], Return[$Failed]];
    (* exact coordinates on zeta_n, accepted only when the AlgebraicNumber equals x (RootReduce of an AlgebraicNumber is
       cheap, unlike that of a sum of exponentials) *)
    attempt[n_, coefficients_List] := With[{theta = Quiet[RootReduce[Exp[2 Pi I/n]]]},
        If[Quiet[TimeConstrained[RootReduce[AlgebraicNumber[theta, coefficients]], 10, $Failed]] === reduced,
            Select[MapIndexed[{#1, (First[#2] - 1)/n} &, coefficients], #[[1]] =!= 0 &], $Failed]];
    (* the native decoder's recorded cyclotomic coefficients (representation entries) *)
    hint = cyclotomicHint[reduced];
    If[AssociationQ[hint], found = attempt[hint["Order"], hint["Coefficients"]]; If[ListQ[found] && found =!= {}, Return[found]]];
    degree = Quiet[Exponent[MinimalPolynomial[reduced, variable], variable]];
    If[!IntegerQ[degree], Return[$Failed]];
    If[KeyExistsQ[$CyclotomicTermsMemo, {reduced, orders}], Return[$CyclotomicTermsMemo[{reduced, orders}]]];
    found = Catch[
        Scan[Function[n, If[readableBudgetExpiredQ[], Throw[$Aborted, cyclotomicTerms]];
            If[Divisible[EulerPhi[n], degree],
                With[{c = latticeCyclotomicCoordinates[reduced, n]},
                    If[ListQ[c], With[{t = attempt[n, PadRight[c, n]]}, If[ListQ[t] && t =!= {}, Throw[t, cyclotomicTerms]]]]]]],
            orders];
        $Failed, cyclotomicTerms];
    (* a search cut by the display budget is not remembered: a later call with time may still succeed *)
    If[found === $Aborted, $ReadableBudgetHit = True; Return[$Failed]];
    If[Length[$CyclotomicTermsMemo] >= 5000, $CyclotomicTermsMemo = <||>];
    AssociateTo[$CyclotomicTermsMemo, {reduced, orders} -> found];
    found];
algebraicDegree[x_] := With[{r = Quiet[TimeConstrained[RootReduce[x], 10, $Failed]]},
    Which[MatchQ[r, _Integer | _Rational], 1, Head[r] === Root, Exponent[r[[1]][\[FormalX]], \[FormalX]], True, 2]];
(* a total time budget for readable forms of one output (a matrix, an expression, a view cell): past it, values keep
   their canonical form instead of blocking the notebook (review F14) *)
$ReadableDeadline = None;
$ReadableBudgetHit = False;
$CyclotomicTermsMemo = <||>;
readableBudgetExpiredQ[] := NumericQ[$ReadableDeadline] && AbsoluteTime[] > $ReadableDeadline;
SetAttributes[withReadableBudget, HoldFirst];
withReadableBudget[expr_, seconds_ : 10] := If[NumericQ[$ReadableDeadline], expr, Block[{$ReadableDeadline = AbsoluteTime[] + seconds}, expr]];
(* field coordinates of a product computed in a hinted cyclotomic field Q(zeta_n) (exactField Source CyclotomicHint),
   read directly as a sum of rational multiples of Exp[2 Pi I k/n] *)
cyclotomicFieldReadable[value_, n_Integer] := Replace[value, {
    AlgebraicNumber[_, c_List] :> Total[MapIndexed[#1 Exp[2 Pi I (First[#2] - 1)/n] &, c]],
    other_ :> other}];

(*
    Summary: The readable form of one exact number.
    Parameters: x — any expression.
    Options/defaults: None.
    Returns: x itself for rationals, inexact numbers and non-algebraic values; m Exp[2 Pi I r] for a rational m times a
        certified root of unity (m = 1 omitted; r = 1/2 gives -m); a radical expression when one is found and certified
        equal; else a certified sum of rational multiples of Exp[2 Pi I k/n] in the smallest candidate cyclotomic field
        (readableConductors); otherwise x unchanged (a Root object).
    Effects: Memoizes per value in this kernel.
    Failures: None.
    Example: readableScalar[Root[1 + 4 #1^2 + 9 #1^4 &, 1]] is -1/(3 Sqrt[2]) - I/3 Sqrt[5/2];
        readableScalar[RootReduce[Exp[2 Pi I/3]]] is Exp[2 Pi I/3].
    Remarks: Every rewritten value is certified equal to x (RootReduce of the difference is 0) by the routines it uses.
    See also: scalarDisplayNode; displayRadical.
*)
readableScalar[x_] := Which[
    MatchQ[x, _Integer | _Rational] || !NumericQ[x] || Precision[x] =!= Infinity, x,
    MatchQ[x, Complex[_Integer | _Rational, _Integer | _Rational]], x,
    KeyExistsQ[$ReadableScalarMemo, {x, readableConductors[]}], $ReadableScalarMemo[{x, readableConductors[]}],
    readableBudgetExpiredQ[], x,
    True, Block[{$ReadableBudgetHit = False}, With[{r = readableScalarCompute[x]},
        If[!TrueQ[$ReadableBudgetHit], AssociateTo[$ReadableScalarMemo, {x, readableConductors[]} -> r]]; r]]];
readableScalarCompute[x_] := Module[{magnitude, phase, radical, terms},
    If[!exactAlgebraicQ[x], Return[x]];
    (* degree above 8: radicals are rarely readable and RootReduce of |x| is slow; the field coordinates come first
       (a single term is then a phase) *)
    If[algebraicDegree[x] > 8 && (terms = cyclotomicTerms[x, readableConductors[]]) =!= $Failed,
        Return[Total[#[[1]] Exp[2 Pi I #[[2]]] & /@ terms]]];
    magnitude = Quiet[TimeConstrained[RootReduce[Abs[x]], 10, $Failed]];
    phase = If[MatchQ[magnitude, _Integer | _Rational] && magnitude > 0,
        certifiedRootOfUnityPhase[Quiet[TimeConstrained[RootReduce[x/magnitude], 10, $Failed]]], $Failed];
    Which[
        MatchQ[phase, _Integer | _Rational], Which[
            phase === 0, magnitude,
            phase === 1/2, -magnitude,
            magnitude === 1, Exp[2 Pi I phase],
            True, magnitude Exp[2 Pi I phase]],
        (radical = displayRadical[x]) =!= $Failed, radical,
        (* a cyclotomic number without a radical form (e.g. 2 cos(2 pi/7)): its certified sum of roots of unity *)
        (terms = cyclotomicTerms[x, readableConductors[]]) =!= $Failed, Total[#[[1]] Exp[2 Pi I #[[2]]] & /@ terms],
        True, x]];

(*
    Summary: Readable forms of matrices and of nested expressions of exact numbers.
    Parameters: m — matrix; e — any expression (lists, associations, polynomials in symbols).
    Options/defaults: None.
    Returns: The same structure with every exact algebraic number replaced by readableScalar.
    Effects: As readableScalar.
    Failures: None.
    Example: readableMatrix[{{RootReduce[1/Sqrt[2]]}}] is {{1/Sqrt[2]}}.
    See also: readableScalar.
*)
readableMatrix[m_?MatrixQ] := withReadableBudget[Map[readableScalar, m, {2}]];
readableMatrix[m_] := m;
readableExpression[e_] := withReadableBudget[readableExpressionRules[e]];
readableExpressionRules[e_] := e /. x_ /; NumericQ[x] && !MatchQ[x, _Integer | _Rational] && Precision[x] === Infinity &&
    !FreeQ[x, Root | Power | Complex] :> RuleCondition[readableScalar[x]];
