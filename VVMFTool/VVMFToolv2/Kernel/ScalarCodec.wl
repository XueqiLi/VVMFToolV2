(*
    :Title: Exact scalar interchange
    :Context: VVMFTool`Private`
    :Summary: Decode decimal, rational and cyclotomic data without evaluating strings.
    :Responsibilities: Exact scalar schema validation and rational encoding.
    :Dependencies: Diagnostics.wl.
    :See Also: VVMFArch/design.md, GAP result exchange.
*)

(*
    Summary: Encode an integer with its sign preserved in a decimal string.
    Parameters: value — any exact Integer.
    Options/defaults: None.
    Returns: Canonical signed decimal string, or Failure for a noninteger.
    Effects: Pure.
    Failures: Approximate or noninteger inputs are rejected.
    Example: encodeInteger[-17] returns "-17".
    Remarks: IntegerString formats the magnitude; the sign is added explicitly.
    See also: decodeInteger; encodeScalar.
*)
encodeInteger[value_Integer] := If[value < 0, "-", ""] <> IntegerString[Abs[value]];
encodeInteger[___] := makeFailure["InvalidInteger", "Expected an exact integer."];

(*
    Summary: Decode a canonical signed decimal integer string.
    Parameters: text — a decimal string, with optional leading minus sign.
    Options/defaults: None.
    Returns: Exact Integer, or Failure["InvalidInteger", data].
    Effects: Pure; no source evaluation.
    Failures: Rejects signs without digits, leading zeros, negative zero and nonstrings.
    Example: decodeInteger["-12345678901234567890"] returns -12345678901234567890.
    See also: decodeRational; FromDigits.
*)
decodeInteger[text_String] := If[
    StringMatchQ[text, RegularExpression["0|-?[1-9][0-9]*"]],
    If[StringStartsQ[text, "-"], -FromDigits[StringDrop[text, 1]], FromDigits[text]],
    makeFailure["InvalidInteger", "Expected a canonical decimal integer string."]
];
decodeInteger[___] := makeFailure["InvalidInteger", "Expected an integer string."];

(*
    Summary: Decode a numerator/positive-denominator pair of decimal strings.
    Parameters: pair — exactly two canonical integer strings.
    Options/defaults: None.
    Returns: Exact rational or integer, or Failure["InvalidRational", data].
    Effects: Pure; equivalent fractions are reduced by exact arithmetic.
    Failures: Rejects malformed pairs and nonpositive denominators.
    Example: decodeRational[{"-6", "4"}] returns -3/2.
    See also: decodeInteger; encodeScalar.
*)
decodeRational[pair_List] := Module[{numerator, denominator},
    If[Length[pair] =!= 2,
        Return[makeFailure["InvalidRational", "Expected a pair of integer strings."]]
    ];
    numerator = decodeInteger[pair[[1]]];
    denominator = decodeInteger[pair[[2]]];
    If[FailureQ[numerator] || FailureQ[denominator] || !TrueQ[denominator > 0],
        Return[makeFailure["InvalidRational", "The denominator must be positive."]]
    ];
    numerator/denominator
];
decodeRational[___] := makeFailure["InvalidRational", "Expected a rational pair."];

(*
    Summary: Decode an explicitly tagged exact scalar record.
    Parameters: data — integer, rational or cyclotomic schema association.
    Options/defaults: None.
    Returns: An exact Wolfram scalar, or a structured schema failure.
    Effects: Pure; strings are never passed to ToExpression.
    Failures: Rejects unknown/missing fields, malformed coefficients, and invalid order.
    Example: decodeScalar[<|"type" -> "rational", "value" -> {"1", "3"}|>] gives 1/3.
    Remarks: Cyclotomic coefficients multiply successive powers of Exp[2 Pi I/n].
        There must be exactly n coefficients, including explicit zero coefficients.
    See also: encodeScalar; decodeRational; VVMFArch/design.md.
*)
decodeScalar[data_Association] := Module[{kind, order, coefficients},
    kind = Lookup[data, "type", Missing["Type"]];
    Switch[kind,
        "integer",
        If[Sort[Keys[data]] =!= {"type", "value"},
            makeFailure["InvalidScalar", "Integer scalar fields do not match the schema."],
            decodeInteger[data["value"]]
        ],
        "rational",
        If[Sort[Keys[data]] =!= {"type", "value"},
            makeFailure["InvalidScalar", "Rational scalar fields do not match the schema."],
            decodeRational[data["value"]]
        ],
        "cyclotomic",
        If[Sort[Keys[data]] =!= {"coefficients", "rootOrder", "type"},
            Return[makeFailure["InvalidScalar", "Cyclotomic fields do not match the schema."]]
        ];
        order = data["rootOrder"];
        coefficients = data["coefficients"];
        If[!IntegerQ[order] || order < 1 || !ListQ[coefficients] ||
            Length[coefficients] =!= order,
            Return[makeFailure["InvalidScalar", "Invalid root order or coefficient count."]]
        ];
        coefficients = decodeRational /@ coefficients;
        If[AnyTrue[coefficients, FailureQ],
            Return[makeFailure["InvalidScalar", "Invalid cyclotomic coefficient."]]
        ];
        RootReduce[Total[coefficients * Table[Exp[2 Pi I power/order], {power, 0, order - 1}]]],
        _, makeFailure["InvalidScalar", "Unknown scalar type."]
    ]
];
decodeScalar[___] := makeFailure["InvalidScalar", "Expected a tagged scalar association."];

(*
    Summary: Write a validated scalar record as a polynomial in a primitive root of a common field.
    Parameters: data — integer, rational or cyclotomic record; n — a multiple of every root order
        involved; z — the polynomial variable standing for Exp[2 Pi I/n].
    Options/defaults: None.
    Returns: Polynomial in z with rational coefficients (not reduced), or Failure.
    Effects: Pure.
    Failures: Invalid records, or a root order that does not divide n.
    Example: a cyclotomic record of order 4 with coefficients {0,1,0,0} gives z^2 for n = 8.
    Remarks: Exact field arithmetic reduces modulo Cyclotomic[n, z]; complex conjugation is z -> z^(n-1).
        Character orthogonality uses this instead of RootReduce, which is slow for large root orders.
    See also: decodeScalar; decodeCharacterData.
*)
scalarCyclotomicPolynomial[data_Association, n_Integer?Positive, z_] := Module[{value = decodeScalar[data], order},
    If[FailureQ[value], Return[value]];
    If[data["type"] =!= "cyclotomic", Return[value]];
    order = data["rootOrder"];
    If[!Divisible[n, order], Return[makeFailure["InvalidScalar", "The root order does not divide the common field order."]]];
    (decodeRational /@ data["coefficients"]) . (z^(# n/order) & /@ Range[0, order - 1])
];
scalarCyclotomicPolynomial[___] := makeFailure["InvalidScalar", "Expected a scalar record and a field order."];

(*
    Summary: Encode an exact scalar with an explicit cyclotomic field when needed.
    Parameters: value — exact rational/algebraic scalar or validated scalar record;
        order — positive cyclotomic root order for a nonrational value.
    Options/defaults: order defaults to Automatic; then only rational values/records work.
    Returns: Tagged scalar association, or Failure["UnsupportedScalar", data].
    Effects: Pure; does not guess a cyclotomic field or rationalize approximate input.
    Failures: Rejects inexact values, invalid records, or values outside the declared field.
    Example: decodeScalar[encodeScalar[Exp[2 Pi I/3], 3]] equals Exp[2 Pi I/3] exactly.
    Remarks: ToNumberField supplies coefficients on the specified root, padded to order.
        The declared field is known from the producer or group exponent at the call site.
    See also: decodeScalar; ToNumberField; VVMFArch/step1Plan.md.
*)
encodeScalar[value_, order_ : Automatic] := Module[{fieldValue, coefficients, root},
    If[AssociationQ[value],
        Return[If[FailureQ[decodeScalar[value]],
            makeFailure["UnsupportedScalar", "The scalar record is invalid."], value]]
    ];
    If[IntegerQ[value],
        Return[<|"type" -> "integer", "value" -> encodeInteger[value]|>]
    ];
    If[Head[value] === Rational,
        Return[<|"type" -> "rational", "value" ->
            (encodeInteger /@ {Numerator[value], Denominator[value]})|>]
    ];
    If[!IntegerQ[order] || order < 1 || !FreeQ[value, _Real],
        Return[makeFailure["UnsupportedScalar", "An exact value and root order are required."]]
    ];
    root = Exp[2 Pi I/order];
    (* A nonmember may leave ToNumberField unevaluated (with a message: callers try several conductors);
       inspect its result explicitly. *)
    fieldValue = Quiet[ToNumberField[value, root] /. _ToNumberField -> $Failed, ToNumberField::nnfel];
    If[Head[fieldValue] =!= AlgebraicNumber ||
        !TrueQ[RootReduce[fieldValue[[1]] - root] === 0],
        Return[makeFailure["UnsupportedScalar", "The value is not in the declared root field."]]
    ];
    coefficients = PadRight[fieldValue[[2]], order];
    If[Length[coefficients] =!= order,
        Return[makeFailure["UnsupportedScalar", "The coefficient list exceeds the root order."]]
    ];
    <|"type" -> "cyclotomic", "rootOrder" -> order,
        "coefficients" -> (encodeInteger /@ {Numerator[#], Denominator[#]} & /@ coefficients)|>
];

True
