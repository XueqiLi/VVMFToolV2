(*
    :Title: Ordered group words
    :Context: VVMFTool`Private`
    :Summary: Parse and freely reduce words on a specified ordered generating set.
    :Responsibilities: Generator-name validation and noncommutative word arithmetic.
    :Dependencies: Diagnostics.wl; public GroupWord head.
    :See Also: VVMFArch/step1Plan.md, Object and input signatures.
*)

(*
    Summary: GroupWord is an inert value describing an ordered group word.
    Status: Alpha.
    Fields: One list of {generatorName_String, exponent_Integer} pairs, or word text.
    Defaults: None. The empty syllable list represents the identity.
    Identity/mutation: Value semantics; never mutates a group or a generating set.
    Validation: normalizeWord checks syntax, names and free reduction at the input boundary.
    Example: GroupWord[{{"a", 1}, {"b", -2}}] denotes a followed by b^-2.
    See also: GroupPresentation; normalizeWord.
*)

(*
    Summary: Recognize distinct generator names accepted by the typed input schema.
    Parameters: names — arbitrary expression; valid input is a list of distinct strings.
    Options/defaults: None.
    Returns: True or False. The empty generating list is valid.
    Effects: Pure.
    Failures: Invalid names return False, without changing or deduplicating input.
    Example: generatorNamesQ[{"a", "b_2"}] is True; generatorNamesQ[{"a", "a"}] is False.
    See also: normalizeWord; VVMFArch/step1Plan.md.
*)
generatorNamesQ[names_] := ListQ[names] && DuplicateFreeQ[names] &&
    AllTrue[names, StringQ[#] && StringMatchQ[#, RegularExpression["[A-Za-z][A-Za-z0-9_]*"]] &];

(*
    Summary: Recognize integer syllables on a given set of generator names.
    Parameters: syllables — candidate list; names — validated generator-name list.
    Options/defaults: None.
    Returns: True or False; zero exponents are valid and later removed by reduction.
    Effects: Pure.
    Failures: Invalid pair shapes, exponents and unknown names return False.
    Example: wordSyllablesQ[{{"a", -2}}, {"a"}] returns True.
    See also: reduceWord; normalizeWord.
*)
wordSyllablesQ[syllables_, names_List] := ListQ[syllables] &&
    AllTrue[syllables, MatchQ[#, {_String, _Integer}] && MemberQ[names, First[#]] &];

(*
    Summary: Freely reduce adjacent powers of the same generator.
    Parameters: syllables — list of string/integer pairs already checked for membership.
    Options/defaults: None.
    Returns: Reduced syllable list, or Failure for malformed pair data.
    Effects: Pure; uses a local stack and retains multiplication order.
    Failures: Rejects malformed syllables; no relations beyond free cancellation are used.
    Example: reduceWord[{{"a", 1}, {"b", 0}, {"a", -1}}] returns {}.
    See also: powerWord; normalizeWord.
*)
reduceWord[syllables_List] := Module[{stack, size = 0, exponent},
    If[!AllTrue[syllables, MatchQ[#, {_String, _Integer}] &],
        Return[makeFailure["InvalidWord", "Expected string/integer syllable pairs."]]
    ];
    stack = ConstantArray[Null, Length[syllables]];
    Do[
        If[Last[syllable] =!= 0,
            If[size > 0 && stack[[size, 1]] === First[syllable],
                exponent = stack[[size, 2]] + Last[syllable];
                If[exponent === 0, size--, stack[[size, 2]] = exponent],
                size++;
                stack[[size]] = syllable
            ]
        ],
        {syllable, syllables}
    ];
    Take[stack, size]
];
reduceWord[___] := makeFailure["InvalidWord", "Expected a syllable list."];

(*
    Summary: Raise a free word to an integer power in multiplication order.
    Parameters: syllables — valid reduced word; exponent — integer.
    Options/defaults: None.
    Returns: Reduced syllable list, or Failure for malformed inputs.
    Effects: Pure; negative powers reverse and invert the syllables.
    Failures: Invalid syllables or noninteger powers return InvalidWord.
    Example: powerWord[{{"a", 1}, {"b", 1}}, -1] gives {{"b", -1}, {"a", -1}}.
    Remarks: Binary powering avoids a list of repeated intermediate words; a single
        syllable is handled directly. Output length can still grow with the exponent.
    See also: reduceWord; readWordFactor.
*)
powerWord[syllables_List, exponent_Integer] := Module[{base, power, result = {}},
    base = reduceWord[syllables];
    If[FailureQ[base], Return[base]];
    If[base === {} || exponent === 0, Return[{}]];
    If[Length[base] === 1, Return[{{base[[1, 1]], exponent * base[[1, 2]]}}]];
    If[exponent < 0, base = {First[#], -Last[#]} & /@ Reverse[base]];
    power = Abs[exponent];
    While[power > 0,
        If[OddQ[power], result = reduceWord[Join[result, base]]];
        power = Quotient[power, 2];
        If[power > 0, base = reduceWord[Join[base, base]]]
    ];
    result
];
powerWord[___] := makeFailure["InvalidWord", "Word powers require integer exponents."];

(*
    Summary: Parse one generator/parenthesized word and its optional integer power.
    Parameters: tokens — token strings; position — starting index; names — valid names.
    Options/defaults: None.
    Returns: {syllables, nextPosition}, or Failure["InvalidWord", data].
    Effects: Pure recursive descent; never evaluates token text as program source.
    Failures: Missing atoms, unknown generators and malformed powers are rejected.
    Example: readWordFactor[{"a", "^", "-", "2"}, 1, {"a"}] gives {{{"a", -2}}, 5}.
    See also: readWordProduct; parseWord.
*)
readWordFactor[tokens_List, position_Integer, names_List] := Module[
    {next = position, value, token, nested, sign = 1, exponent, parenthesized = False},
    If[next < 1 || next > Length[tokens],
        Return[makeFailure["InvalidWord", "A word factor is missing."]]
    ];
    token = tokens[[next++]];
    Which[
        token === "(",
        nested = readWordProduct[tokens, next, names];
        If[FailureQ[nested], Return[nested]];
        {value, next} = nested;
        If[next > Length[tokens] || tokens[[next]] =!= ")",
            Return[makeFailure["InvalidWord", "A closing parenthesis is missing."]]
        ];
        next++,
        MemberQ[names, token], value = {{token, 1}},
        token === "1", value = {},
        True, Return[makeFailure["InvalidWord", "Unknown generator or invalid word factor.",
            <|"Token" -> token, "Position" -> position|>]]
    ];
    If[next <= Length[tokens] && tokens[[next]] === "^",
        next++;
        If[next <= Length[tokens] && tokens[[next]] === "(",
            parenthesized = True; next++
        ];
        If[next <= Length[tokens] && MemberQ[{"+", "-"}, tokens[[next]]],
            sign = If[tokens[[next]] === "-", -1, 1]; next++
        ];
        If[next > Length[tokens] || !StringMatchQ[tokens[[next]], DigitCharacter ..],
            Return[makeFailure["InvalidWord", "A power must be an integer literal."]]
        ];
        exponent = sign * FromDigits[tokens[[next++]]];
        If[parenthesized,
            If[next > Length[tokens] || tokens[[next]] =!= ")",
                Return[makeFailure["InvalidWord", "Malformed parenthesized exponent."]]
            ];
            next++
        ];
        value = powerWord[value, exponent]
    ];
    {value, next}
];

(*
    Summary: Parse a product up to a closing parenthesis or the end of the token list.
    Parameters: tokens — token strings; position — first factor; names — valid names.
    Options/defaults: None.
    Returns: {reducedSyllables, nextPosition}, or Failure.
    Effects: Pure; consumes explicit dot/star multiplication only.
    Failures: Adjacent atoms, missing factors and invalid operators are rejected.
    Example: readWordProduct[{"a", ".", "b"}, 1, {"a", "b"}] gives
        {{{"a", 1}, {"b", 1}}, 4}.
    See also: readWordFactor; parseWord.
*)
readWordProduct[tokens_List, position_Integer, names_List] := Module[
    {parsed, result, next},
    parsed = readWordFactor[tokens, position, names];
    If[FailureQ[parsed], Return[parsed]];
    {result, next} = parsed;
    While[next <= Length[tokens] && tokens[[next]] =!= ")",
        If[!MemberQ[{".", "*"}, tokens[[next]]],
            Return[makeFailure["InvalidWord", "Expected ordered multiplication."]]
        ];
        parsed = readWordFactor[tokens, next + 1, names];
        If[FailureQ[parsed], Return[parsed]];
        result = reduceWord[Join[result, First[parsed]]];
        next = Last[parsed]
    ];
    {result, next}
];

(*
    Summary: Parse a complete textual ordered word on the supplied generators.
    Parameters: text — word string; names — distinct valid generator names.
    Options/defaults: None.
    Returns: GroupWord[reducedSyllables], or Failure["InvalidWord", data].
    Effects: Pure; no source-text evaluation or implicit commutative multiplication.
    Failures: Invalid names, unsupported characters, malformed syntax and trailing tokens.
    Example: parseWord["(a.b)^-1", {"a", "b"}] returns
        GroupWord[{{"b", -1}, {"a", -1}}].
    Remarks: Empty/whitespace text and the atom 1 denote identity. Whitespace between
        names does not imply multiplication. Exponents may be signed or parenthesized.
    See also: normalizeWord; readWordProduct.
*)
parseWord[text_String, names_List] := Module[{tokens, compact, parsed},
    If[!generatorNamesQ[names],
        Return[makeFailure["InvalidWord", "Generator names are invalid or duplicated."]]
    ];
    compact = StringReplace[text, WhitespaceCharacter -> ""];
    If[compact === "", Return[GroupWord[{}]]];
    tokens = StringCases[text, RegularExpression["[A-Za-z][A-Za-z0-9_]*|[0-9]+|[().*^+-]"]];
    If[StringJoin[tokens] =!= compact,
        Return[makeFailure["InvalidWord", "The word contains unsupported characters."]]
    ];
    parsed = readWordProduct[tokens, 1, names];
    If[FailureQ[parsed], Return[parsed]];
    If[Last[parsed] =!= Length[tokens] + 1,
        Return[makeFailure["InvalidWord", "Unexpected closing parenthesis or trailing input."]]
    ];
    GroupWord[First[parsed]]
];
parseWord[___] := makeFailure["InvalidWord", "Expected word text and generator names."];

(*
    Summary: Validate a textual or structured group word against recorded generators.
    Parameters: word — string or GroupWord value; names — valid generator-name list.
    Options/defaults: None.
    Returns: A freely reduced GroupWord, or Failure.
    Effects: Pure; the public GroupWord data head itself is inert.
    Failures: Unknown generators, malformed word arguments and invalid names are rejected.
    Example: normalizeWord[GroupWord[{{"a", 2}, {"a", -1}}], {"a"}]
        returns GroupWord[{{"a", 1}}].
    See also: parseWord; wordSyllablesQ.
*)
normalizeWord[word_, names_List] := Which[
    !generatorNamesQ[names], makeFailure["InvalidWord", "Invalid generator names."],
    StringQ[word], parseWord[word, names],
    MatchQ[word, GroupWord[_String]], parseWord[First[word], names],
    MatchQ[word, GroupWord[_List]] && wordSyllablesQ[First[word], names],
        GroupWord[reduceWord[First[word]]],
    True, makeFailure["InvalidWord", "The word must use the recorded generators."]
];
normalizeWord[___] := makeFailure["InvalidWord", "Expected a word and generator list."];

True
