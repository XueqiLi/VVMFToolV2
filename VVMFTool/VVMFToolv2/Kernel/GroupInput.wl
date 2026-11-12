(*
    :Title: Typed finite-group construction input
    :Context: VVMFTool`Private`
    :Summary: Validate construction data and encode it as inert JSON-compatible records.
    :Responsibilities: Presentations, catalogues, permutations, matrix domains and catalogue data.
    :Dependencies: GroupWords.wl; ScalarCodec.wl; Data/ModularGroups.json.
    :See Also: VVMFArch/step1Plan.md, Typed construction schemas.
*)

(*
    Summary: GroupPresentation, CatalogueGroup, PermutationGroupSpecification and
        MatrixGroupSpecification are inert construction specifications.
    Status: Alpha.
    Fields: GroupPresentation[names_List, relators_List] uses ordered names and identity
        relators. CatalogueGroup[kind_String, key] selects a GAP catalogue entry.
        PermutationGroupSpecification[generators_List, names_List] uses Cycles values.
        MatrixGroupSpecification[generators_List, names_List, domain_Association] uses
        exact square matrices and an explicit coefficient domain.
    Defaults: None; an empty generating list specifies a trivial group. Empty matrix
        input requires a positive Dimension in the domain.
    Identity/mutation: Immutable values; order and repeated/identity generators are retained.
    Validation: validateSpecification checks shape/domains. Finiteness and actual group
        generation are checked by the construction backend, not inferred from a schema.
    Example: GroupPresentation[{"a", "b"}, {"a^2", "b^3", "(a.b)^3"}].
        CatalogueGroup["SmallGroup", {12, 3}].
        PermutationGroupSpecification[{Cycles[{{1, 2, 3}}]}, {"a"}].
        MatrixGroupSpecification[{{{0, -1}, {1, 0}}}, {"r"}, <|"Type" -> "Rationals"|>].
    See also: encodeConstruction; ModularGroupSpecification.
*)

(*
    Summary: Convert a validated word into JSON syllables with signed decimal exponents.
    Parameters: word — string/GroupWord; names — recorded generator names.
    Options/defaults: None.
    Returns: List of {name, exponentString} pairs, or Failure.
    Effects: Pure; preserves generator order.
    Failures: Propagates word validation failure before encoding.
    Example: encodeWord["a^-2", {"a"}] returns {{"a", "-2"}}.
    See also: normalizeWord; encodeInteger.
*)
encodeWord[word_, names_List] := Module[{normalized = normalizeWord[word, names]},
    If[FailureQ[normalized], normalized,
        {First[#], encodeInteger[Last[#]]} & /@ First[normalized]]
];

(*
    Summary: Validate a matrix-domain record for a known positive matrix dimension.
    Parameters: domain — domain association; dimension — positive integer dimension.
    Options/defaults: Dimension may be omitted in domain when matrices give its value.
    Returns: Canonical domain association containing Dimension, or Failure.
    Effects: Pure.
    Failures: Unknown fields/types, invalid characteristic/modulus or inconsistent dimension.
    Example: validateMatrixDomain[<|"Type" -> "PrimeField", "Characteristic" -> 3|>, 2]
        returns the same record with "Dimension" -> 2.
    See also: validateMatrixSpecification; VVMFArch/step1Plan.md.
*)
validateMatrixDomain[domain_Association, dimension_Integer] := Module[{kind, allowed, modulus},
    kind = Lookup[domain, "Type", Missing["Type"]];
    If[!MemberQ[{"Rationals", "Cyclotomics", "PrimeField", "IntegersMod"}, kind],
        Return[makeFailure["UnsupportedDomain", "The matrix domain is unsupported."]]
    ];
    allowed = Join[{"Type", "Dimension"}, Switch[kind,
        "PrimeField", {"Characteristic"}, "IntegersMod", {"Modulus"}, _, {}]];
    If[Complement[Keys[domain], allowed] =!= {} || dimension < 1 ||
        Lookup[domain, "Dimension", dimension] =!= dimension,
        Return[makeFailure["InvalidDomain", "Unknown fields or inconsistent matrix dimension."]]
    ];
    If[MemberQ[{"PrimeField", "IntegersMod"}, kind],
        modulus = Lookup[domain, If[kind === "PrimeField", "Characteristic", "Modulus"], 0];
        If[!IntegerQ[modulus] || modulus < 2 || (kind === "PrimeField" && !PrimeQ[modulus]),
            Return[makeFailure["InvalidDomain", "The field characteristic or ring modulus is invalid."]]
        ]
    ];
    Join[domain, <|"Dimension" -> dimension|>]
];
validateMatrixDomain[___] := makeFailure["InvalidDomain", "Expected a domain and dimension."];

(*
    Summary: Validate exact matrix generators and their declared coefficient domain.
    Parameters: generators — matrix list; names — names of those matrices;
        domain — supported domain record.
    Options/defaults: Domain Dimension may be inferred from a nonempty generator list.
    Returns: A JSON-compatible matrix specification, or Failure.
    Effects: Pure; matrix entries over finite rings are reduced modulo their modulus.
    Failures: Shape, exactness, membership, dimension and invertibility violations.
    Example: validateMatrixSpecification[{{{0, -1}, {1, 0}}}, {"r"},
        <|"Type" -> "Rationals"|>]["domain"]["Dimension"] returns 2.
    Remarks: A nonzero determinant over a composite ring is insufficient: it must be a unit.
        This checks generators, not finiteness of the generated group over characteristic zero.
    See also: validateMatrixDomain; encodeConstruction.
*)
validateMatrixSpecification[generators_List, names_List, domain_Association] := Module[
    {dimension, checkedDomain, kind, modulus, entries, decoded, determinants, encoded},
    If[!generatorNamesQ[names] || Length[names] =!= Length[generators],
        Return[makeFailure["InvalidSpecification", "Generator names must match the matrices."]]
    ];
    If[generators === {},
        dimension = Lookup[domain, "Dimension", 0],
        If[!AllTrue[generators, MatrixQ[#] && Length[#] > 0 &],
            Return[makeFailure["InvalidSpecification", "Expected nonempty square matrices."]]
        ];
        dimension = Length[First[generators]];
        If[!AllTrue[generators, Dimensions[#] === {dimension, dimension} &],
            Return[makeFailure["InvalidSpecification", "Matrices must share one square dimension."]]
        ]
    ];
    checkedDomain = validateMatrixDomain[domain, dimension];
    If[FailureQ[checkedDomain], Return[checkedDomain]];
    kind = checkedDomain["Type"];
    entries = Flatten[generators, 2];
    If[!AllTrue[entries, Switch[kind,
        "Rationals", IntegerQ[#] || Head[#] === Rational,
        "Cyclotomics", IntegerQ[#] || Head[#] === Rational ||
            (AssociationQ[#] && Lookup[#, "type", None] === "cyclotomic" && !FailureQ[decodeScalar[#]]),
        _, IntegerQ[#]
    ] &],
        Return[makeFailure["InvalidDomain", "Matrix entries must be exact members of the declared domain."]]
    ];
    decoded = Map[If[AssociationQ[#], decodeScalar[#], #] &, generators, {3}];
    If[MemberQ[{"PrimeField", "IntegersMod"}, kind],
        modulus = checkedDomain[If[kind === "PrimeField", "Characteristic", "Modulus"]];
        decoded = Mod[decoded, modulus];
        If[!AllTrue[Det /@ decoded, GCD[#, modulus] === 1 &],
            Return[makeFailure["NoninvertibleGenerator", "A matrix determinant is not a unit in the domain."]]
        ];
        encoded = Map[encodeScalar, decoded, {3}],
        determinants = RootReduce[Det[#]] & /@ decoded;
        If[MemberQ[determinants, 0],
            Return[makeFailure["NoninvertibleGenerator", "A generator matrix is singular."]]
        ];
        encoded = Map[encodeScalar, generators, {3}]
    ];
    <|"type" -> "matrix", "names" -> names, "domain" -> checkedDomain,
        "generators" -> encoded|>
];
validateMatrixSpecification[___] := makeFailure["InvalidSpecification", "Malformed matrix specification."];

(*
    Summary: Validate the supported typed group-construction schemas.
    Parameters: specification — one public group specification value.
    Options/defaults: None.
    Returns: Canonical JSON-compatible construction association, or Failure.
    Effects: Pure; no group construction, code execution or process launch.
    Failures: Invalid schema, generator names, words, catalogue parameters or domains.
    Example: validateSpecification[GroupPresentation[{"a"}, {"a^3"}]]["relators"]
        returns {{{"a", "3"}}}.
    Remarks: Catalogue availability/index bounds and finiteness require GAP and remain
        backend checks. Symmetric/alternating degree zero denotes the trivial group.
    See also: encodeConstruction; validateMatrixSpecification.
*)
validateSpecification[specification_] := Module[
    {names, generators, relators, catalogue, key, cycles, points},
    Which[
        MatchQ[specification, GroupPresentation[_List, _List]],
        {names, relators} = List @@ specification;
        If[!generatorNamesQ[names],
            Return[makeFailure["InvalidSpecification", "Invalid or repeated generator names."]]
        ];
        relators = encodeWord[#, names] & /@ relators;
        If[AnyTrue[relators, FailureQ], Return[First[Select[relators, FailureQ]]]];
        <|"type" -> "presentation", "names" -> names, "relators" -> relators|>,

        MatchQ[specification, CatalogueGroup[_String, _]],
        {catalogue, key} = List @@ specification;
        If[!MemberQ[{"SmallGroup", "AlternatingGroup", "SymmetricGroup", "CyclicGroup", "DihedralGroup"}, catalogue],
            Return[makeFailure["InvalidSpecification", "Unsupported catalogue."]]
        ];
        If[!Switch[catalogue,
            "SmallGroup", MatchQ[key, {_Integer, _Integer}] && Min[key] > 0,
            "AlternatingGroup" | "SymmetricGroup", IntegerQ[key] && key >= 0,
            "DihedralGroup", IntegerQ[key] && key >= 2 && EvenQ[key],
            _, IntegerQ[key] && key > 0
        ], Return[makeFailure["InvalidSpecification", "Invalid catalogue parameters."]]];
        <|"type" -> "catalogue", "catalogue" -> catalogue,
            "key" -> If[ListQ[key], encodeInteger /@ key, encodeInteger[key]]|>,

        MatchQ[specification, PermutationGroupSpecification[_List, _List]],
        {generators, names} = List @@ specification;
        If[!generatorNamesQ[names] || Length[names] =!= Length[generators] ||
            !AllTrue[generators, MatchQ[#, Cycles[_List]] &],
            Return[makeFailure["InvalidSpecification", "Invalid permutation generators or names."]]
        ];
        cycles = First /@ generators;
        If[!AllTrue[cycles, Function[permutation,
            AllTrue[permutation, ListQ[#] && Length[#] > 0 &&
                AllTrue[#, IntegerQ[#] && # > 0 &] &] &&
                DuplicateFreeQ[Flatten[permutation]]
        ]], Return[makeFailure["InvalidSpecification", "Permutation cycles must be disjoint positive points."]]];
        points = Flatten[cycles];
        <|"type" -> "permutation", "names" -> names, "degree" -> encodeInteger[Max[Prepend[points, 0]]],
            "generators" -> Map[encodeInteger, cycles, {3}]|>,

        MatchQ[specification, MatrixGroupSpecification[_List, _List, _Association]],
        validateMatrixSpecification @@ (List @@ specification),
        True, makeFailure["InvalidSpecification", "Expected a supported typed group specification."]
    ]
];

(*
    Summary: Encode construction input through the shared semantic validator.
    Parameters: specification — a supported public typed specification.
    Options/defaults: None.
    Returns: JSON-compatible association or Failure, never executable source text.
    Effects: Pure.
    Failures: Propagates the exact validation failure.
    Example: encodeConstruction[CatalogueGroup["CyclicGroup", 3]]["key"] returns "3".
    See also: validateSpecification; BuildGroup in VVMFArch/step1Plan.md.
*)
encodeConstruction[specification_] := validateSpecification[specification];

(*
    Summary: Read one modular catalogue presentation without constructing its group.
    Status: Alpha.
    Parameters: label — exact catalogue label, including any realization suffix.
    Options/defaults: None.
    Returns: GroupPresentation on the recorded generators, or Failure.
    Effects: Reads the package JSON catalogue; no GAP worker or registry mutation.
    Failures: Unknown label, missing/invalid catalogue, or malformed stored words.
    Example: ModularGroupSpecification["24-3I"] returns its presentation on S,T.
    Remarks: Abstract group IDs never merge labels or select an alternative realization.
    See also: GroupPresentation; Data/ModularGroups.json.
*)
ModularGroupSpecification[label_String] := Module[{catalogue, record, words, names, path},
    path = FileNameJoin[{$PackageRoot, "Data", "ModularGroups.json"}];
    If[!FileExistsQ[path], Return[makeFailure["CatalogueUnavailable", "The modular catalogue is missing."]]];
    catalogue = Check[Import[path, "RawJSON"], $Failed];
    If[!AssociationQ[catalogue] || Lookup[catalogue, "schemaVersion", None] =!= 1 ||
        !AssociationQ[Lookup[catalogue, "groups", None]],
        Return[makeFailure["InvalidCatalogue", "The modular catalogue schema is invalid."]]
    ];
    record = Lookup[catalogue["groups"], label, Missing["UnknownLabel"]];
    If[MissingQ[record], Return[makeFailure["UnknownModularGroup", "Unknown modular catalogue label.", <|"Label" -> label|>]]];
    If[!AssociationQ[record] || !ListQ[Lookup[record, "relators", None]] ||
        !generatorNamesQ[Lookup[record, "names", None]],
        Return[makeFailure["InvalidCatalogue", "Malformed catalogue presentation."]]
    ];
    names = record["names"];
    words = Map[Function[syllables,
        If[!ListQ[syllables] || !AllTrue[syllables, MatchQ[#, {_String, _String}] &],
            makeFailure["InvalidCatalogue", "Malformed catalogue word."],
            normalizeWord[GroupWord[{First[#], decodeInteger[Last[#]]} & /@ syllables], names]
        ]
    ], record["relators"]];
    If[AnyTrue[words, FailureQ], Return[makeFailure["InvalidCatalogue", "Invalid catalogue word data."]]];
    GroupPresentation[names, words]
];
ModularGroupSpecification[___] := makeFailure["InvalidInput", "A modular catalogue label must be a string."];

(*
    Summary: A group presentation from a relation string in the v1 / GAP form.
    Status: Alpha.
    Parameters: text — relators separated by commas at the top level, optionally in [ ]: words with * or . products,
        ^n and ^-n powers, parentheses and the identity 1; a relator a = b means a.b^-1; whitespace is ignored.
        names — optional generator names in the order that defines the group's generators.
    Options/defaults: Generator order: names when given; otherwise {S, T} when the identifiers are exactly S and T (the
        modular convention); otherwise the order of first appearance. The generator order is part of the group's identity.
    Returns: GroupPresentation[names, relators], or Failure.
    Effects: Pure.
    Failures: InvalidRelationString (with the position of the offending relator and the grammar).
    Example: RelationString["[S^4,(S*T)^3,S^-2*T^-1*S^2*T,T^3]"] is GroupPresentation[{"S", "T"}, {...}];
        RelationString["[T^7,S^3,T^-4*S*T*S^-1]"] has generators {S, T}.
    Remarks: BuildGroup and BuildModularGroup accept the string directly (uxUpdatePlan.md 4, U2).
    See also: GroupPresentation; BuildGroup; BuildModularGroup.
*)
RelationString[text_String, names : (Automatic | {__String}) : Automatic] := Catch[Module[{s = StringDelete[text, Whitespace], parts, depth = 0, current = "",
        relators, identifiers, order, fail},
    fail[reason_, extra_ : <||>] := Throw[makeFailure["InvalidRelationString", "A relation string lists relators such as [S^4,(S*T)^3,S^-2*T^-1*S^2*T,T^3]: words with * or . products, ^n powers, parentheses, separated by commas; a relator may be written a=b. " <> reason, Join[<|"Text" -> text|>, extra]], "relations"];
    If[s === "", fail["The string is empty."]];
    If[StringStartsQ[s, "["], If[!StringEndsQ[s, "]"], fail["The opening [ has no closing ]."]]; s = StringTake[s, {2, -2}]];
    (* split on top-level commas *)
    parts = {};
    Scan[Function[ch, Switch[ch,
        "(", depth++; current = current <> ch,
        ")", depth--; If[depth < 0, fail["Unbalanced parentheses."]]; current = current <> ch,
        ",", If[depth === 0, AppendTo[parts, current]; current = "", current = current <> ch],
        _, current = current <> ch]], Characters[s]];
    AppendTo[parts, current];
    If[depth =!= 0, fail["Unbalanced parentheses."]];
    If[MemberQ[parts, ""], fail["A relator is empty.", <|"Position" -> First[FirstPosition[parts, ""]]|>]];
    relators = Map[Function[r, With[{sides = StringSplit[r, "=", All]}, Switch[Length[sides],
        1, r,
        2, If[MemberQ[sides, ""], fail["An equation needs both sides.", <|"Relator" -> r|>], "(" <> sides[[1]] <> ").(" <> sides[[2]] <> ")^-1"],
        _, fail["A relator has more than one =.", <|"Relator" -> r|>]]]], parts];
    identifiers = DeleteDuplicates[Flatten[StringCases[relators, RegularExpression["[A-Za-z][A-Za-z0-9_]*"]]]];
    order = Which[ListQ[names], names, Sort[identifiers] === {"S", "T"}, {"S", "T"}, True, identifiers];
    If[!SubsetQ[order, identifiers], fail["The relators use generators that are not named.", <|"Unknown" -> Complement[identifiers, order]|>]];
    (* every relator must parse as a word on these generators *)
    MapIndexed[Function[{r, pos}, If[FailureQ[normalizeWord[r, order]], fail["A relator is not a word on the generators.", <|"Position" -> First[pos], "Relator" -> r|>]]], relators];
    GroupPresentation[order, relators]
], "relations"];
RelationString[___] := makeFailure["InvalidRelationString", "RelationString expects a relation string and optional generator names."];

True
