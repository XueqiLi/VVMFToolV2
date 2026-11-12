(*
    :Title: Representation scalar storage
    :Context: VVMFTool`Private`
    :Summary: Encode representation entries as inert exact-algebraic or declared-precision JSON.
    :Responsibilities: Algebraic scalars by minimal polynomial and isolating rectangle; numerical
        scalars by decimal significand/exponent strings; one representation-entry decoder;
        schema-2 representationData decoding and group-level representation availability.
    :Dependencies: Diagnostics.wl; ScalarCodec.wl; at call time ResultValidation.wl (resultFieldsQ)
        and Representation.wl (repIdentity).
    :See Also: VVMFArch/step2Plan.md (scalar codec paragraph); Schemas/GroupResult.md.
*)

(* Finest dyadic grid tried when isolating an algebraic root: 2^-$AlgebraicGridBits. A value
   whose distinct conjugates are closer than about 4 * 2^-200 is reported as unsupported. *)
$AlgebraicGridBits = 200;

(*
    Summary: Test whether a value is an exact algebraic number.
    Parameters: value — any expression.
    Options/defaults: None.
    Returns: True only when Wolfram decides that the exact numeric value is algebraic.
    Effects: Pure.
    Failures: Inexact, symbolic, transcendental and undecided values return False.
    Example: exactAlgebraicQ[Sqrt[2] + Exp[2 Pi I/5]] is True; exactAlgebraicQ[Pi] is False.
    See also: encodeAlgebraic; validateRepShape.
*)
exactAlgebraicQ[value_] := NumericQ[value] && Precision[value] === Infinity &&
    TrueQ[Element[value, Algebraics]];

(*
    Summary: Count the roots of an integer polynomial in a closed rectangle and on its four edges.
    Parameters: coefficients — integers, lowest degree first; rectangle — {realMin, realMax,
        imagMin, imagMax} rationals.
    Options/defaults: None.
    Returns: {closedCount, {bottom, top, left, right}} root counts.
    Effects: Pure; exact root counting.
    Failures: Caller supplies a nonconstant integer polynomial and a nonempty rectangle.
    Example: rectangleRootCounts[{-1, 0, 1}, {1, 2, -1, 1}] is {1, {0, 0, 1, 0}}: the root 1 lies
        on the left edge.
    Remarks: CountRoots counts roots in the closed rectangle spanned by two complex corners
        (boundary and corners included) and on a degenerate rectangle, a segment, exactly; the
        unit tests pin this convention for boundary, edge and corner roots.
    See also: isolateAlgebraicRoot.
*)
rectangleRootCounts[coefficients_List, {realMin_, realMax_, imagMin_, imagMax_}] := Module[
    {variable, polynomial, count},
    polynomial = coefficients . variable^Range[0, Length[coefficients] - 1];
    count = CountRoots[polynomial, {variable, #1, #2}] &;
    {count[realMin + I imagMin, realMax + I imagMax],
        {count[realMin + I imagMin, realMax + I imagMin], count[realMin + I imagMax, realMax + I imagMax],
            count[realMin + I imagMin, realMin + I imagMax], count[realMax + I imagMin, realMax + I imagMax]}}
];

(*
    Summary: Find the unique root of a square-free integer polynomial inside an open rational rectangle.
    Parameters: coefficients — integers, lowest degree first, degree at least two; rectangle —
        {realMin, realMax, imagMin, imagMax} rationals with realMin < realMax, imagMin < imagMax.
    Options/defaults: None.
    Returns: The root as an exact RootReduced Root object or radical, or AmbiguousAlgebraicRoot Failure.
    Effects: Pure.
    Failures: No root, several roots in the rectangle, or any root on its boundary.
    Example: isolateAlgebraicRoot[{-2, 0, 1}, {1, 2, -1, 1}] is Sqrt[2].
    Remarks: Isolation is proved by exact root counting: one root in the closed rectangle and none
        on any edge. The numerical step only identifies which Root[p, k] that root is: precision is
        raised until exactly one root's approximation lies inside the rectangle by more than its
        error, which must happen because exactly one root is inside and none is on the boundary.
    See also: rectangleRootCounts; decodeAlgebraic; encodeAlgebraic.
*)
isolateAlgebraicRoot[coefficients_List, rectangle_List] := Module[
    {counts, degree, polynomial, roots, precision, inside, bounds = rectangle},
    counts = rectangleRootCounts[coefficients, rectangle];
    If[First[counts] =!= 1 || Total[Last[counts]] =!= 0,
        Return[makeFailure["AmbiguousAlgebraicRoot", "The rectangle does not isolate exactly one root in its interior."]]];
    degree = Length[coefficients] - 1;
    polynomial = Function[Evaluate[coefficients . Slot[1]^Range[0, degree]]];
    roots = Table[Root[polynomial, index], {index, degree}];
    Do[
        inside = Select[Range[degree], Function[index, With[{value = N[roots[[index]], precision]},
            With[{error = 2*10^-Accuracy[value]},
                bounds[[1]] + error < Re[value] < bounds[[2]] - error &&
                    bounds[[3]] + error < Im[value] < bounds[[4]] - error]]]];
        If[Length[inside] === 1, Return[RootReduce[roots[[First[inside]]]], Module]],
        {precision, 30*2^Range[0, 6]}];
    makeFailure["AmbiguousAlgebraicRoot", "The isolated root could not be identified numerically."]
];
isolateAlgebraicRoot[___] := makeFailure["AmbiguousAlgebraicRoot", "Expected polynomial coefficients and a rectangle."];

(*
    Summary: Encode an exact algebraic scalar by its minimal polynomial and an isolating rectangle.
    Parameters: value — exact algebraic number.
    Options/defaults: None.
    Returns: {"type" -> "algebraic", "polynomial" -> coefficient strings (low to high),
        "rootRectangle" -> realMin/realMax/imagMin/imagMax rational pairs}; rational values use
        the integer/rational codec; or UnsupportedScalar Failure.
    Effects: Pure.
    Failures: Inexact, transcendental or undecided values, or conjugates closer than the finest grid.
    Example: decodeAlgebraic[encodeAlgebraic[2^(1/3)]] is 2^(1/3).
    Remarks: The polynomial is the primitive minimal polynomial with positive leading coefficient.
        For k = 0, 1, 2, ... the rectangle spans three cells of the dyadic grid 2^-k around the
        value's k-th grid cell; the first rectangle whose exact root counts isolate one root (the
        decoder's own criterion) is the encoding, so the bytes are deterministic. The value is
        inside because its approximation error is below every grid step. Real values get
        imaginary bounds straddling zero.
    See also: decodeAlgebraic; isolateAlgebraicRoot; rectangleRootCounts; encodeScalar.
*)
encodeAlgebraic[value_] := Module[{reduced, variable, coefficients, approximation, step, bounds, counts},
    If[!exactAlgebraicQ[value],
        Return[makeFailure["UnsupportedScalar", "Expected an exact algebraic number."]]];
    reduced = RootReduce[value];
    If[MatchQ[reduced, _Integer | _Rational], Return[encodeScalar[reduced]]];
    coefficients = CoefficientList[MinimalPolynomial[reduced, variable], variable];
    coefficients = coefficients/(GCD @@ coefficients);
    If[Last[coefficients] < 0, coefficients = -coefficients];
    (* The value lies in its grid cell and the rectangle adds one cell on each side, so an
       approximation error below the step keeps the value strictly inside. *)
    approximation = N[reduced, 30 + Ceiling[$AlgebraicGridBits Log10[2.]]];
    If[Accuracy[approximation] < $AlgebraicGridBits Log10[2.] + 5,
        Return[makeFailure["UnsupportedScalar", "The algebraic value could not be approximated accurately enough."]]];
    Do[
        step = 2^-bits;
        bounds = Flatten[Function[part, {Floor[part/step] - 1, Floor[part/step] + 2} step] /@
            {Re[approximation], Im[approximation]}];
        counts = rectangleRootCounts[coefficients, bounds];
        (* One root of the minimal polynomial inside, none on the edges: it is the value itself. *)
        If[First[counts] === 1 && Total[Last[counts]] === 0,
            Return[<|"type" -> "algebraic", "polynomial" -> (encodeInteger /@ coefficients),
                "rootRectangle" -> AssociationThread[{"realMin", "realMax", "imagMin", "imagMax"},
                    (encodeInteger /@ {Numerator[#], Denominator[#]} & /@ bounds)]|>, Module]],
        {bits, 0, $AlgebraicGridBits}];
    makeFailure["UnsupportedScalar", "The algebraic value could not be isolated on the supported grid."]
];
encodeAlgebraic[___] := makeFailure["UnsupportedScalar", "Expected an exact algebraic number."];

(*
    Summary: Decode an algebraic scalar record by exact root isolation.
    Parameters: data — algebraic record as produced by encodeAlgebraic.
    Options/defaults: None.
    Returns: The RootReduced exact value, or InvalidScalar/AmbiguousAlgebraicRoot Failure.
    Effects: Pure; strings are decoded as integers, never evaluated as source.
    Failures: Extra/missing fields, malformed integers, degree below two, a polynomial that is not
        primitive, has a nonpositive leading coefficient or is not square-free, an empty rectangle,
        or a rectangle that does not isolate exactly one interior root.
    Example: decodeAlgebraic[<|"type" -> "algebraic", "polynomial" -> {"-2", "0", "1"},
        "rootRectangle" -> <|"realMin" -> {"1", "1"}, "realMax" -> {"2", "1"},
            "imagMin" -> {"-1", "1"}, "imagMax" -> {"1", "1"}|>|>] is Sqrt[2].
    See also: encodeAlgebraic; isolateAlgebraicRoot; decodeRepScalar.
*)
decodeAlgebraic[data_Association] := Module[{coefficients, rectangle, variable, polynomial},
    If[Sort[Keys[data]] =!= {"polynomial", "rootRectangle", "type"} || data["type"] =!= "algebraic" ||
        !ListQ[data["polynomial"]] || !AssociationQ[data["rootRectangle"]] ||
        Sort[Keys[data["rootRectangle"]]] =!= Sort[{"realMin", "realMax", "imagMin", "imagMax"}],
        Return[makeFailure["InvalidScalar", "Algebraic scalar fields do not match the schema."]]];
    coefficients = decodeInteger /@ data["polynomial"];
    rectangle = decodeRational /@ Lookup[data["rootRectangle"], {"realMin", "realMax", "imagMin", "imagMax"}];
    If[AnyTrue[Join[coefficients, rectangle], FailureQ] || Length[coefficients] < 3 ||
        Last[coefficients] <= 0 || (GCD @@ coefficients) =!= 1 ||
        rectangle[[1]] >= rectangle[[2]] || rectangle[[3]] >= rectangle[[4]],
        Return[makeFailure["InvalidScalar", "Invalid algebraic polynomial or rectangle."]]];
    polynomial = coefficients . variable^Range[0, Length[coefficients] - 1];
    If[!FreeQ[PolynomialGCD[polynomial, D[polynomial, variable]], variable],
        Return[makeFailure["InvalidScalar", "The algebraic polynomial must be square-free."]]];
    isolateAlgebraicRoot[coefficients, rectangle]
];
decodeAlgebraic[___] := makeFailure["InvalidScalar", "Expected an algebraic scalar record."];

(*
    Summary: Encode one real number as a canonical decimal significand/exponent pair.
    Parameters: value — finite real number; digits — number of significant decimal digits.
    Options/defaults: None.
    Returns: <|"significand" -> signed integer string, "exponent" -> integer string|> with
        value ~ significand * 10^exponent; trailing significand zeros are removed.
    Effects: Pure.
    Failures: Caller supplies a finite real and positive digit count.
    Example: decimalRecord[1.5`20, 20] is <|"significand" -> "15", "exponent" -> "-1"|>.
    Remarks: The exact binary value of the number is rounded to the nearest digits-digit
        decimal significand (RealDigits would truncate and pad beyond the precision).
    See also: encodeNumerical.
*)
decimalRecord[value_, digits_Integer] := Module[{exact, exponent, significand},
    exact = SetPrecision[value, Infinity];
    If[exact == 0, Return[<|"significand" -> "0", "exponent" -> "0"|>]];
    exponent = Floor[Log10[Abs[exact]]] + 1 - digits;
    significand = Round[Abs[exact]/10^exponent];
    If[significand >= 10^digits, significand = Round[significand/10]; exponent++];
    While[Mod[significand, 10] === 0, significand /= 10; exponent++];
    <|"significand" -> encodeInteger[Sign[exact] significand], "exponent" -> encodeInteger[exponent]|>
];

(*
    Summary: Encode a finite numerical scalar at a declared precision.
    Parameters: value — finite real or complex number (exact values are accepted and rounded);
        precision — MachinePrecision or an integer number of decimal digits, at least 16.
    Options/defaults: None.
    Returns: {"type" -> "numerical", "real", "imag" -> significand/exponent records,
        "precision" -> "MachinePrecision" or a digit string, "exact" -> False}, or Failure.
    Effects: Pure.
    Failures: Nonnumeric or nonfinite values and invalid precisions.
    Example: decodeNumerical[encodeNumerical[N[Pi, 30], 30]] has precision 30 and equals N[Pi, 30].
    Remarks: The declared precision belongs to the whole matrix or variant, not to each entry,
        so drifting per-entry precision cannot change the record. Machine numbers keep 17
        significant digits, enough to reproduce a double exactly. Real values encode an
        imaginary part of zero. The record, not the decoded approximate value, is the
        numerical identity: encoding, decoding and encoding again gives identical data.
    See also: decodeNumerical; decimalRecord; step2Plan.md scalar codec.
*)
encodeNumerical[value_, precision_] := Module[{digits, re, im},
    If[!(precision === MachinePrecision || (IntegerQ[precision] && precision >= 16)),
        Return[makeFailure["UnsupportedScalar", "The declared precision must be MachinePrecision or an integer of at least 16."]]];
    If[!NumericQ[value] || !NumberQ[N[value]] || !FreeQ[N[value], DirectedInfinity | Indeterminate | Overflow[] | Underflow[]],
        Return[makeFailure["UnsupportedScalar", "Expected a finite numerical scalar."]]];
    digits = If[precision === MachinePrecision, 17, precision];
    {re, im} = If[precision === MachinePrecision, N[{Re[value], Im[value]}],
        SetPrecision[{Re[value], Im[value]}, precision]];
    <|"type" -> "numerical", "real" -> decimalRecord[re, digits], "imag" -> decimalRecord[im, digits],
        "precision" -> If[precision === MachinePrecision, "MachinePrecision", encodeInteger[precision]],
        "exact" -> False|>
];
encodeNumerical[___] := makeFailure["UnsupportedScalar", "Expected a numerical scalar and declared precision."];

(*
    Summary: Round an exact rational number to the nearest machine real.
    Parameters: value — exact rational number within the machine range.
    Options/defaults: None.
    Returns: The machine real nearest to value.
    Effects: Pure.
    Failures: Caller supplies a finite exact rational.
    Example: nearestMachineReal[1/10] === 0.1.
    Remarks: N of an exact rational is not always correctly rounded, so the value is rounded
        exactly to a 53-bit significand and scaled by an exact power of two. Normal range only.
    See also: decodeNumerical.
*)
nearestMachineReal[value_] := Module[{exponent},
    If[value == 0, Return[0.]];
    exponent = Floor[Log[2, Abs[value]]] - 52;
    (* An integer below 2^54 and a power of two are exact machine numbers, so their product is
       the correctly rounded (half-even) machine real. *)
    N[Round[value/2^exponent]] * N[2^exponent]
];

(*
    Summary: Decode a declared-precision numerical scalar record.
    Parameters: data — numerical record as produced by encodeNumerical.
    Options/defaults: None.
    Returns: A real or complex approximate number at the declared precision, or InvalidScalar Failure.
    Effects: Pure; strings are decoded as integers, never evaluated as source.
    Failures: Missing/extra fields, exact other than False, noncanonical significands or
        exponents (trailing zeros, nonzero exponent of a zero significand), invalid precision.
    Example: decodeNumerical[encodeNumerical[1.25, MachinePrecision]] is 1.25.
    See also: encodeNumerical; decodeRepScalar.
*)
decodeNumerical[data_Association] := Module[{precision, parts},
    If[Sort[Keys[data]] =!= Sort[{"type", "real", "imag", "precision", "exact"}] ||
        data["type"] =!= "numerical" || data["exact"] =!= False,
        Return[makeFailure["InvalidScalar", "Numerical scalar fields do not match the schema."]]];
    precision = If[data["precision"] === "MachinePrecision", MachinePrecision, decodeInteger[data["precision"]]];
    If[!(precision === MachinePrecision || (IntegerQ[precision] && precision >= 16)),
        Return[makeFailure["InvalidScalar", "Invalid declared numerical precision."]]];
    parts = Function[part, If[!AssociationQ[part] || Sort[Keys[part]] =!= {"exponent", "significand"},
        $Failed, With[{significand = decodeInteger[part["significand"]], exponent = decodeInteger[part["exponent"]]},
            If[!IntegerQ[significand] || !IntegerQ[exponent] ||
                (significand === 0 && exponent =!= 0) || (significand =!= 0 && Divisible[significand, 10]),
                $Failed, significand 10^exponent]]]] /@ {data["real"], data["imag"]};
    If[MemberQ[parts, $Failed], Return[makeFailure["InvalidScalar", "Invalid numerical significand or exponent."]]];
    parts = If[precision === MachinePrecision, nearestMachineReal /@ parts, N[parts, precision]];
    If[Last[parts] == 0, First[parts], First[parts] + I Last[parts]]
];
decodeNumerical[___] := makeFailure["InvalidScalar", "Expected a numerical scalar record."];

(*
    Summary: Decode any representation-entry scalar record.
    Parameters: data — integer, rational, cyclotomic, algebraic or numerical record.
    Options/defaults: None.
    Returns: Exact RootReduced value, approximate number, or InvalidScalar Failure.
    Effects: Pure.
    Failures: Unknown types and invalid records.
    Example: decodeRepScalar[encodeRepScalar[Sqrt[3]]] is Sqrt[3].
    Remarks: Character tables keep using decodeScalar, which accepts only the exact
        rational/cyclotomic codec; representation data additionally accept these records.
    See also: decodeScalar; decodeAlgebraic; decodeNumerical.
*)
decodeRepScalar[data_Association] := Switch[Lookup[data, "type", None],
    (* GAP's encoding of a computed entry (VVMF_EncodeRepScalar) in an inert record made by a weak computation (C7) *)
    "cyclotomic" /; KeyExistsQ[data, "minimalPolynomial"], decodeNativeRepScalar[data],
    "integer" | "rational" | "cyclotomic", decodeScalar[data],
    "algebraic", decodeAlgebraic[data],
    "numerical", decodeNumerical[data],
    _, makeFailure["InvalidScalar", "Unknown representation scalar type."]];
decodeRepScalar[___] := makeFailure["InvalidScalar", "Expected a tagged representation scalar."];

(*
    Summary: Encode one representation entry as exact or declared-precision data.
    Parameters: value — exact algebraic or finite numerical scalar; precision — Infinity for
        exact data, otherwise the variant's declared numerical precision.
    Options/defaults: precision defaults to Infinity.
    Returns: Integer/rational/algebraic record for exact data, numerical record otherwise, or Failure.
    Effects: Pure.
    Failures: Inexact value with exact precision, or unsupported scalars.
    Example: encodeRepScalar[1/2]["type"] is "rational"; encodeRepScalar[0.5, 20]["type"] is "numerical".
    Remarks: Wolfram-side exact data use the algebraic codec even for cyclotomic numbers; exact
        identity is taken from RootReduced decoded values, so the codec choice does not change it.
    See also: encodeAlgebraic; encodeNumerical; decodeRepScalar.
*)
encodeRepScalar[value_, precision_ : Infinity] := Which[
    precision === Infinity && Precision[value] =!= Infinity,
        makeFailure["UnsupportedScalar", "Approximate values require a declared numerical precision."],
    precision === Infinity, encodeAlgebraic[value],
    True, encodeNumerical[value, precision]];

(*
    Summary: Decode a native representation entry: exact cyclotomic data with its minimal polynomial.
    Parameters: data — integer/rational record, or cyclotomic record with minimalPolynomial (primitive
        integer coefficients, lowest degree first, positive leading coefficient, degree at least two).
    Options/defaults: None.
    Returns: The exact canonical (RootReduced) value, or InvalidScalar/AmbiguousAlgebraicRoot Failure.
    Effects: Records the value's cyclotomic coefficients as a hint (registerCyclotomicHint); otherwise pure.
    Failures: Missing/extra fields, invalid coefficients or polynomial, a polynomial that does not
        vanish at the certified numerical value, or no isolating rectangle on the supported grid.
    Example: decodeNativeRepScalar of GAP's encoding of E(5) is Root[1 + #1 + #1^2 + #1^3 + #1^4 &, 4].
    Remarks: The cyclotomic sum is evaluated numerically with certified precision (enough for the
        finest grid step), a rectangle around it is refined until exact root counting isolates one root
        of the polynomial, and that Root object is RootReduced. This is fast even for conductors in the
        thousands, where RootReduce of the sum of roots of unity takes minutes, and gives the same
        canonical value. The polynomial is producer data from the native exporter, which recomputes
        it on every export; correspondence import re-verifies the cyclotomic values natively. The value's cyclotomic
        coefficients are recorded as a hint for exactField (registerCyclotomicHint), which proves it before use.
    See also: VVMF_EncodeRepScalar; isolateAlgebraicRoot; decodeRepVariant; registerCyclotomicHint.
*)
decodeNativeRepScalar[data_Association] := Module[
    {invalid, order, coefficients, polynomial, variable, approximation, precision, step, bounds, counts},
    invalid = makeFailure["InvalidScalar", "Invalid native representation entry."];
    If[MemberQ[{"integer", "rational"}, Lookup[data, "type", None]], Return[decodeScalar[data]]];
    If[Sort[Keys[data]] =!= Sort[{"type", "rootOrder", "coefficients", "minimalPolynomial"}] ||
        data["type"] =!= "cyclotomic" || !IntegerQ[data["rootOrder"]] || data["rootOrder"] < 1 ||
        !ListQ[data["coefficients"]] || Length[data["coefficients"]] =!= data["rootOrder"] ||
        !ListQ[data["minimalPolynomial"]], Return[invalid]];
    order = data["rootOrder"];
    coefficients = decodeRational /@ data["coefficients"];
    polynomial = decodeInteger /@ data["minimalPolynomial"];
    If[AnyTrue[Join[coefficients, polynomial], FailureQ] || Length[polynomial] < 3 ||
        Last[polynomial] <= 0 || (GCD @@ polynomial) =!= 1, Return[invalid]];
    Do[
        approximation = N[coefficients . Exp[2 Pi I Range[0, order - 1]/order], precision];
        If[Accuracy[approximation] > $AlgebraicGridBits Log10[2.] + 5, Break[]],
        {precision, {100, 200, 400}}];
    If[Accuracy[approximation] <= $AlgebraicGridBits Log10[2.] + 5, Return[invalid]];
    (* The polynomial must vanish at the value up to the certified numerical error. *)
    If[Abs[polynomial . approximation^Range[0, Length[polynomial] - 1]] >
        10^(-Accuracy[approximation] + 5) Max[1, Abs[approximation]]^Length[polynomial] Total[Abs[polynomial]],
        Return[invalid]];
    Do[
        step = 2^-bits;
        bounds = Flatten[Function[part, {Floor[part/step] - 1, Floor[part/step] + 2} step] /@
            {Re[approximation], Im[approximation]}];
        counts = rectangleRootCounts[polynomial, bounds];
        If[First[counts] === 1 && Total[Last[counts]] === 0,
            (* the coefficients are recorded as an unproved hint for exactField (cyclotomicHintField proves it) *)
            Return[With[{value = isolateAlgebraicRoot[polynomial, bounds]},
                If[!FailureQ[value], registerCyclotomicHint[value, order, coefficients]]; value], Module]],
        {bits, 0, $AlgebraicGridBits}];
    makeFailure["AmbiguousAlgebraicRoot", "The entry could not be isolated on the supported grid."]
];
decodeNativeRepScalar[___] := makeFailure["InvalidScalar", "Expected a native representation entry."];

(*
    Summary: Decode one representation variant (native, scaled native, Wolfram-exact or numerical tier).
    Parameters: data — exported variant record; dimension — the irrep's degree; names — ordered
        recorded generator names; assignment — decoded modular assignment or Missing["NotAssigned"].
    Options/defaults: None.
    Returns: <|"Rep", "Identity", "Tier", "Arithmetic", "BasisProperties", "SourceMethod", "Scales",
        "NativeMatrices", "Derivation"|>, or Failure. "Scales" is the list sigma of a scaled variant and
        "NativeMatrices" its cyclotomic matrices N (both Missing["NotScaled"] otherwise); "Derivation" is
        <|"Witness" -> variant ID, "Conjugator" -> C|> or Missing["None"].
    Effects: Exact entries are decoded with decodeNativeRepScalar (cyclotomic data with their minimal
        polynomials), which records their cyclotomic hints; otherwise pure.
    Failures: UnsupportedRepresentationData for unknown tiers; InvalidRepresentation for wrong fields, shapes, entries, singular
        matrices, basis properties inconsistent with the assignment, or scales that are not positive
        real numbers with the first equal to one.
    Example: a variant of a two-generator degree-3 irrep decodes to a Rep with two 3 by 3 matrices.
    Remarks: The producer's native checks (homomorphism, class traces, unitarity and, for a scaled
        variant, N^dagger S N = S and the derivation N = C W C^-1) are its evidence; this decoder checks
        structure, correspondence and the positivity of the scales, which GAP cannot order. A scaled
        variant's visible matrices are F = L N L^-1 with L = DiagonalMatrix[Sqrt[sigma]], entries
        N_ij Sqrt[sigma_i/sigma_j]. Identity is the exact realization digest of the visible matrices.
        Wolfram-tier (arithmetic Exact, algebraic entries) and Numerical (declared precision) variants are
        inert in GAP: decodeInertVariant; Wolfram verified them at acceptance or correspondence import (R1).
    See also: decodeRepresentationData; repIdentity; GAP VVMF_ExportRepresentations; GAP/RepresentationBasis.g.
*)
decodeRepVariant[data_Association /; MemberQ[{"Wolfram", "Numerical"}, Lookup[data, "tier", None]], dimension_Integer,
    names_List, assignment_] := decodeInertVariant[data, dimension, names, assignment];
decodeRepVariant[data_, dimension_Integer, names_List, assignment_] := Module[
    {invalid, matrices, native = Missing["NotScaled"], rep, identity, properties, source, scaled, scales = Missing["NotScaled"],
        derivation = Missing["None"], shapeQ, decodeMatrix},
    invalid = makeFailure["InvalidRepresentation", "Malformed representation variant."];
    If[!AssociationQ[data], Return[invalid]];
    If[!MemberQ[{"Native", "ScaledNative"}, Lookup[data, "tier", None]],
        Return[makeFailure["UnsupportedRepresentationData", "Unknown representation variant tier."]]];
    scaled = data["tier"] === "ScaledNative";
    If[!resultFieldsQ[KeyDrop[data, {"derivation", "verificationStatus"}],
            Join[{"tier", "arithmetic", "matrices", "sourceMethod", "basisProperties"}, If[scaled, {"scales"}, {}]]],
        Return[invalid]];
    source = data["sourceMethod"]; properties = data["basisProperties"];
    If[data["arithmetic"] =!= "Exact" || !resultFieldsQ[source, {"method", "model"}] ||
        !AllTrue[Values[source], StringQ[#] && StringLength[#] > 0 &] ||
        !resultFieldsQ[properties, {"unitary", "tDiagonal", "assignmentIdentity"}] ||
        !BooleanQ[properties["unitary"]] ||
        If[MissingQ[assignment], properties["tDiagonal"] =!= Null || properties["assignmentIdentity"] =!= Null,
            !BooleanQ[properties["tDiagonal"]] || properties["assignmentIdentity"] =!= assignment["Identity"]],
        Return[invalid]];
    shapeQ[m_] := ListQ[m] && Length[m] === dimension && AllTrue[m, ListQ[#] && Length[#] === dimension &];
    decodeMatrix[m_] := If[shapeQ[m], Map[decodeNativeRepScalar, m, {2}], $Failed];
    If[!ListQ[data["matrices"]] || Length[data["matrices"]] =!= Length[names] || !AllTrue[data["matrices"], shapeQ],
        Return[invalid]];
    matrices = decodeMatrix /@ data["matrices"];
    If[!FreeQ[matrices, _Failure], Return[invalid]];
    If[scaled,
        scales = If[ListQ[data["scales"]] && Length[data["scales"]] === dimension, decodeNativeRepScalar /@ data["scales"], $Failed];
        If[!ListQ[scales] || !FreeQ[scales, _Failure] || First[scales] =!= 1 || AllTrue[scales, # === 1 &] ||
            !AllTrue[scales, positiveExactQ], Return[invalid]];
        (* Visible matrices F = L N L^-1, L = DiagonalMatrix[Sqrt[sigma]]. *)
        native = matrices;
        matrices = Map[Function[m, Table[RootReduce[m[[i, j]] Sqrt[scales[[i]] / scales[[j]]]], {i, dimension}, {j, dimension}]], matrices]];
    If[KeyExistsQ[data, "derivation"],
        If[!resultFieldsQ[data["derivation"], {"witness", "conjugator"}] || !StringQ[data["derivation"]["witness"]],
            Return[invalid]];
        derivation = <|"Witness" -> data["derivation"]["witness"], "Conjugator" -> decodeMatrix[data["derivation"]["conjugator"]]|>;
        If[!MatrixQ[derivation["Conjugator"]] || !FreeQ[derivation["Conjugator"], _Failure], Return[invalid]]];
    rep = If[names === {}, If[dimension === 1, Rep[{}, 1], Return[invalid]], Rep[matrices]];
    identity = repIdentity[rep, names];
    If[FailureQ[identity], Return[invalid]];
    (* a recorded status that cannot be read is refused, never read as the default *)
    If[KeyExistsQ[data, "verificationStatus"] && !verificationStatusQ[data["verificationStatus"]], Return[invalid]];
    <|"Rep" -> rep, "Identity" -> identity, "Tier" -> data["tier"], "Arithmetic" -> "Exact",
        "BasisProperties" -> <|"Unitary" -> properties["unitary"],
            "TDiagonal" -> If[MissingQ[assignment], Missing["NotAssigned"], properties["tDiagonal"]],
            "AssignmentIdentity" -> If[MissingQ[assignment], Missing["NotAssigned"], properties["assignmentIdentity"]]|>,
        "SourceMethod" -> <|"Method" -> source["method"], "Model" -> source["model"]|>,
        (* an optional recorded verification status (methodOptionsPlan.md 2C.1): carried only when recorded, so the
           accepted representation data of older records are unchanged (variantVerificationStatus supplies the default) *)
        Sequence @@ If[KeyExistsQ[data, "verificationStatus"], {"VerificationStatus" -> data["verificationStatus"]}, {}],
        "Scales" -> scales, "NativeMatrices" -> native, "Derivation" -> derivation|>
];
decodeRepVariant[___] := makeFailure["InvalidRepresentation", "Expected a representation variant."];

(*
    Summary: Decode an inert (Wolfram-exact or numerical) representation variant.
    Parameters: As decodeRepVariant; data has tier "Wolfram" (arithmetic "Exact") or "Numerical"
        (arithmetic "Numerical", precision "MachinePrecision" or a decimal string of at least 16).
    Options/defaults: None.
    Returns: As decodeRepVariant, with Tier "Wolfram"/"Numerical", Arithmetic "Exact"/"Numerical", Scales
        and NativeMatrices Missing["NotScaled"], and Derivation <|"Witness", "Conjugator"|> or Missing["None"].
    Effects: Pure; entries are decoded with decodeRepScalar (algebraic or declared-precision numerical).
    Failures: InvalidRepresentation for wrong fields, shapes, entries, precisions, singular matrices or
        basis properties inconsistent with the assignment.
    Example: a Supplied Wolfram-tier variant with 2^(1/3) entries decodes to those exact matrices.
    Remarks: GAP stores these records as received and never computes with them. Numerical identity uses
        the declared precision (repIdentity).
    See also: decodeRepVariant; encodeInertVariant; GAP VVMF_InertRecordCheck.
*)
decodeInertVariant[data_Association, dimension_Integer, names_List, assignment_] := Module[
    {invalid, numerical, precision = Infinity, source, properties, shapeQ, decodeMatrix, matrices, rep, identity,
        derivation = Missing["None"]},
    invalid = makeFailure["InvalidRepresentation", "Malformed inert representation variant."];
    numerical = data["tier"] === "Numerical";
    If[!resultFieldsQ[KeyDrop[data, {"derivation", "verificationStatus"}],
            Join[{"tier", "arithmetic", "matrices", "sourceMethod", "basisProperties"}, If[numerical, {"precision"}, {}]]] ||
        data["arithmetic"] =!= If[numerical, "Numerical", "Exact"], Return[invalid]];
    If[numerical,
        precision = If[data["precision"] === "MachinePrecision", MachinePrecision, decodeInteger[data["precision"]]];
        If[!(precision === MachinePrecision || IntegerQ[precision] && precision >= 16), Return[invalid]]];
    source = data["sourceMethod"]; properties = data["basisProperties"];
    If[!resultFieldsQ[source, {"method", "model"}] || !AllTrue[Values[source], StringQ[#] && StringLength[#] > 0 &] ||
        !resultFieldsQ[properties, {"unitary", "tDiagonal", "assignmentIdentity"}] || !BooleanQ[properties["unitary"]] ||
        If[MissingQ[assignment], properties["tDiagonal"] =!= Null || properties["assignmentIdentity"] =!= Null,
            !BooleanQ[properties["tDiagonal"]] || properties["assignmentIdentity"] =!= assignment["Identity"]],
        Return[invalid]];
    shapeQ[m_] := ListQ[m] && Length[m] === dimension && AllTrue[m, ListQ[#] && Length[#] === dimension &];
    (* Numerical entries carry their own precision; each must match the declared one. *)
    decodeMatrix[m_] := If[shapeQ[m], Map[Function[entry, With[{value = decodeRepScalar[entry]},
        Which[FailureQ[value], value, numerical && (Lookup[entry, "type", None] =!= "numerical" ||
            Lookup[entry, "precision", None] =!= data["precision"]), invalid,
            !numerical && Lookup[entry, "type", None] === "numerical", invalid, True, value]]], m, {2}], $Failed];
    If[!ListQ[data["matrices"]] || Length[data["matrices"]] =!= Length[names] || !AllTrue[data["matrices"], shapeQ],
        Return[invalid]];
    matrices = decodeMatrix /@ data["matrices"];
    If[!FreeQ[matrices, _Failure | $Failed], Return[invalid]];
    If[KeyExistsQ[data, "derivation"],
        If[!resultFieldsQ[data["derivation"], {"witness", "conjugator"}] || !StringQ[data["derivation"]["witness"]],
            Return[invalid]];
        derivation = <|"Witness" -> data["derivation"]["witness"], "Conjugator" -> decodeMatrix[data["derivation"]["conjugator"]]|>;
        If[!MatrixQ[derivation["Conjugator"]] || !FreeQ[derivation["Conjugator"], _Failure], Return[invalid]]];
    rep = If[names === {}, If[dimension === 1, Rep[{}, 1], Return[invalid]], Rep[matrices]];
    identity = If[numerical, repIdentity[rep, names, precision], repIdentity[rep, names]];
    If[FailureQ[identity], Return[invalid]];
    If[KeyExistsQ[data, "verificationStatus"] && !verificationStatusQ[data["verificationStatus"]], Return[invalid]];
    <|"Rep" -> rep, "Identity" -> identity, "Tier" -> data["tier"], "Arithmetic" -> If[numerical, "Numerical", "Exact"],
        "BasisProperties" -> <|"Unitary" -> properties["unitary"],
            "TDiagonal" -> If[MissingQ[assignment], Missing["NotAssigned"], properties["tDiagonal"]],
            "AssignmentIdentity" -> If[MissingQ[assignment], Missing["NotAssigned"], properties["assignmentIdentity"]]|>,
        "SourceMethod" -> <|"Method" -> source["method"], "Model" -> source["model"]|>,
        (* an optional recorded verification status (methodOptionsPlan.md 2C.1): carried only when recorded, so the
           accepted representation data of older records are unchanged (variantVerificationStatus supplies the default) *)
        Sequence @@ If[KeyExistsQ[data, "verificationStatus"], {"VerificationStatus" -> data["verificationStatus"]}, {}],
        "Scales" -> Missing["NotScaled"], "NativeMatrices" -> Missing["NotScaled"], "Derivation" -> derivation|>
];
decodeInertVariant[___] := makeFailure["InvalidRepresentation", "Expected an inert representation variant."];

(*
    Summary: Encode a Wolfram-verified representation as an inert variant record for GAP to carry.
    Parameters: rep — Rep; source — <|"Method", "Model"|>; properties — <|"Unitary", "TDiagonal"|> as
        verified (TDiagonal Missing without an assignment); assignment — modular assignment or Missing;
        precision — Infinity (Wolfram tier) or the declared numerical precision; derivation —
        <|"Witness", "Conjugator"|> or Missing["None"].
    Options/defaults: None.
    Returns: The exported record (tier "Wolfram" or "Numerical"), or Failure.
    Effects: Pure.
    Failures: Entries that the representation codecs cannot encode.
    Example: encodeInertVariant[Rep[{{{2^(1/3)}}}], <|"Method" -> "Supplied", "Model" -> "User"|>, ...]["tier"]
        is "Wolfram".
    Remarks: The record is what decodeInertVariant reads; GAP stores and exports it unchanged except for
        the assignment-dependent properties.
    See also: decodeInertVariant; encodeRepScalar.
*)
encodeInertVariant[rep_Rep, source_Association, properties_Association, assignment_, precision_, derivation_] := Module[
    {encode, matrices, record},
    encode[m_] := Map[encodeRepScalar[#, precision] &, m, {2}];
    matrices = encode /@ repMatrices[rep];
    If[!FreeQ[matrices, _Failure], Return[FirstCase[matrices, _Failure, Null, Infinity]]];
    record = <|"tier" -> If[precision === Infinity, "Wolfram", "Numerical"],
        "arithmetic" -> If[precision === Infinity, "Exact", "Numerical"], "matrices" -> matrices,
        "sourceMethod" -> <|"method" -> source["Method"], "model" -> source["Model"]|>,
        "basisProperties" -> <|"unitary" -> TrueQ[properties["Unitary"]],
            "tDiagonal" -> If[AssociationQ[assignment], TrueQ[properties["TDiagonal"]], Null],
            "assignmentIdentity" -> If[AssociationQ[assignment], assignment["Identity"], Null]|>|>;
    If[precision =!= Infinity, record["precision"] = ToString[precision]];
    If[AssociationQ[derivation],
        record["derivation"] = <|"witness" -> derivation["Witness"], "conjugator" -> encode[derivation["Conjugator"]]|>;
        If[!FreeQ[record["derivation"], _Failure], Return[FirstCase[record["derivation"], _Failure, Null, Infinity]]]];
    record
];
encodeInertVariant[___] := makeFailure["InvalidRepresentation", "Expected a Rep, source, properties, assignment, precision and derivation."];

(*
    Summary: Check an irrep entry's active and accepted-partial pointers against its variants.
    Parameters: variants — decoded variants keyed by ID; active, partial — variant IDs or
        Missing["NotComputed"].
    Options/defaults: None.
    Returns: True when each present pointer names a variant and an accepted partial is a nonunitary
        variant that is not active and does not coexist with a unitary active variant; else False.
    Effects: Pure.
    Failures: None (False).
    Example: representationPointersQ[<|"a" -> v|>, "a", "a"] is False.
    Remarks: The decoder and context binding apply the same rule as GAP's export check.
    See also: decodeRepresentationData; bindRepContext; GAP VVMF_ExportRepresentations.
*)
representationPointersQ[variants_Association, active_, partial_] := Module[{unitaryQ},
    unitaryQ[id_] := TrueQ[variants[id]["BasisProperties"]["Unitary"]];
    (MissingQ[active] || StringQ[active] && KeyExistsQ[variants, active]) &&
        (MissingQ[partial] || StringQ[partial] && KeyExistsQ[variants, partial] &&
            partial =!= active && !unitaryQ[partial] && (MissingQ[active] || !unitaryQ[active]))
];
representationPointersQ[___] := False;

(*
    Summary: Decode schema-2 representationData into the group's Representations value.
    Parameters: data — JSON null or record keyed by irrep ID; characters — decoded complete
        CharacterData; generators — validated ID/name records; generatorIdentity — the envelope's;
        assignment — decoded modular assignment or Missing["NotAssigned"].
    Options/defaults: Null means no representation data.
    Returns: <||>, or an association keyed (sorted) by irrep ID of entries <|"CharacterID",
        "Dimension", "GeneratorIdentity", "Variants" (sorted by variant ID), "ActiveVariant",
        "AcceptedPartial"|>; absent pointers are Missing["NotComputed"]. Or Failure.
    Effects: Pure.
    Failures: Unknown irrep IDs, wrong dimensions or generator identity, empty variant sets,
        invalid variants, dangling or inconsistent active/partial pointers (an accepted partial must
        be a nonunitary variant and cannot coexist with a unitary active variant).
    Example: decodeRepresentationData[Null, characters, generators, id, Missing["NotAssigned"]] is <||>.
    Remarks: Keys are sorted so decoded data compare with SameQ regardless of JSON key order.
    See also: decodeRepVariant; representationAvailability; validateGroupResult.
*)
decodeRepresentationData[Null, ___] := <||>;
decodeRepresentationData[data_Association, characters_Association, generators_List, generatorIdentity_String,
    assignment_] := Module[{names, entries = <||>, entry, dimension, variants, active, partial, invalid},
    invalid[message_] := makeFailure["InvalidRepresentation", message];
    names = Lookup[generators, "name", {}];
    If[data === <||> || !SubsetQ[characters["IrrepIDs"], Keys[data]],
        Return[invalid["Representation data must be keyed by known irrep IDs."]]];
    Do[
        entry = data[id];
        If[!resultFieldsQ[entry, {"dimension", "generatorIdentity", "variants", "activeVariant", "acceptedPartial"}],
            Return[invalid["Malformed representation entry."], Module]];
        dimension = decodeInteger[entry["dimension"]];
        If[dimension =!= characters["Degrees"][[First[FirstPosition[characters["IrrepIDs"], id]]]] ||
            entry["generatorIdentity"] =!= generatorIdentity || !AssociationQ[entry["variants"]] ||
            entry["variants"] === <||>,
            Return[invalid["Representation entry dimension, generators or variants are invalid."], Module]];
        variants = Association[KeyValueMap[#1 -> decodeRepVariant[#2, dimension, names, assignment] &,
            KeySort[entry["variants"]]]];
        If[AnyTrue[Values[variants], FailureQ], Return[First[Select[Values[variants], FailureQ]], Module]];
        If[!AllTrue[Values[variants], MissingQ[#["Derivation"]] || KeyExistsQ[variants, #["Derivation"]["Witness"]] &],
            Return[invalid["A variant's derivation names a witness that is not a variant of the irrep."], Module]];
        active = Replace[entry["activeVariant"], Null -> Missing["NotComputed"]];
        partial = Replace[entry["acceptedPartial"], Null -> Missing["NotComputed"]];
        If[!representationPointersQ[variants, active, partial],
            Return[invalid["Inconsistent active or accepted-partial variant."], Module]];
        entries[id] = <|"CharacterID" -> id, "Dimension" -> dimension, "GeneratorIdentity" -> generatorIdentity,
            "Variants" -> variants, "ActiveVariant" -> active, "AcceptedPartial" -> partial|>,
        {id, Keys[data]}];
    KeySort[entries]
];
decodeRepresentationData[___] := makeFailure["InvalidRepresentation", "Expected representation data and accepted group data."];

(*
    Summary: Report group-level representation availability.
    Parameters: representations — decoded Representations; characters — decoded CharacterData or Missing.
    Options/defaults: None.
    Returns: "NotComputed" without data, "Complete" when every irrep has an active variant (user
        decision: an accepted active matrix set for every irrep), otherwise "Partial".
    Effects: Pure.
    Failures: None.
    Example: representationAvailability[<||>, characters] is "NotComputed".
    Remarks: Whether each active variant meets the default unitary basis is reported per irrep
        through its BasisProperties.
    See also: decodeRepresentationData; GAP VVMF_RepAvailability.
*)
representationAvailability[representations_, characters_] := Which[
    !AssociationQ[representations] || representations === <||>, "NotComputed",
    AssociationQ[characters] && AllTrue[characters["IrrepIDs"],
        StringQ[Lookup[Lookup[representations, #, <||>], "ActiveVariant", None]] &], "Complete",
    True, "Partial"];

True
