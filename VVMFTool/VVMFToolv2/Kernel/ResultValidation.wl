(*
    :Title: Group-result data validation
    :Context: VVMFTool`Private`
    :Summary: Validate exact JSON invariants separately from actual group provenance.
    :Responsibilities: Strict envelopes, retained construction data and exact character checks.
    :Dependencies: Diagnostics.wl; ScalarCodec.wl; GroupWords.wl; GroupInput.wl;
        GAPOperations.wl (registered operations).
    :See Also: Schemas/GroupResult.md; GAP/ResultExport.g.
*)

(*
    Summary: Require exactly the named fields of one schema record.
    Parameters: data — any expression; fields — distinct string keys.
    Options/defaults: None.
    Returns: Boolean; invalid types return False.
    Effects: Pure.
    Failures: Missing and extra fields both return False.
    Example: resultFieldsQ[<|"a" -> 1|>, {"a"}] returns True.
    See also: validateGroupResult.
*)
resultFieldsQ[data_, fields_List] := AssociationQ[data] && Sort[Keys[data]] === Sort[fields];

(*
    Summary: Test whether a collection consists of unique nonempty string identities.
    Parameters: values — any expression.
    Options/defaults: None.
    Returns: Boolean; the empty list is valid.
    Effects: Pure.
    Failures: Nonlists, nonstrings, empty or duplicate IDs return False.
    Example: resultIDsQ[{"class-1", "class-2"}] returns True.
    See also: decodeResultWord; decodeCharacterData.
*)
resultIDsQ[values_] := ListQ[values] && DuplicateFreeQ[values] &&
    AllTrue[values, StringQ[#] && StringLength[#] > 0 &];

(*
    Summary: Recognize the inert JSON types accepted by the mathematical interchange.
    Parameters: data — any expression.
    Options/defaults: None.
    Returns: Boolean.
    Effects: Pure; never evaluates text as source.
    Failures: Real numbers and other symbolic expressions are not exact JSON data.
    Example: resultJSONQ[<|"missing" -> Null, "items" -> {}|>] returns True.
    See also: validateConstructionRecord; decodeScalar.
*)
resultJSONQ[data_] := Which[
    MemberQ[{Null, True, False}, data] || StringQ[data] || IntegerQ[data], True,
    ListQ[data], AllTrue[data, resultJSONQ],
    AssociationQ[data], AllTrue[Keys[data], StringQ] && AllTrue[Values[data], resultJSONQ],
    True, False
];

(*
    Summary: Normalize JSON object-key order while preserving every array's ordered content.
    Parameters: data — inert JSON already checked by resultJSONQ at the owning boundary.
    Options/defaults: None.
    Returns: The same data with recursively sorted association keys.
    Effects: Pure; no expression or source parsing.
    Failures: Caller establishes JSON types; scalar values are returned unchanged.
    Example: differently ordered code/dependency record keys compare equally after normalization,
        while reversed generator lists remain different.
    See also: validateGroupResult; validateConstructionRecord.
*)
canonicalJSON[data_] := Which[
    AssociationQ[data], canonicalJSON /@ KeySort[data],
    ListQ[data], canonicalJSON /@ data,
    True, data
];

(*
    Summary: Decode a result word using recorded stable generator IDs.
    Parameters: syllables — ID/exponent-string pairs; generators — validated ordered
        records containing "id" and "name".
    Options/defaults: None.
    Returns: A freely reduced GroupWord on names, or InvalidResultWord Failure.
    Effects: Pure; ordered multiplication is preserved.
    Failures: Unknown IDs, malformed pairs or noncanonical exponents.
    Example: an ID corresponding to "a" with exponent "-2" gives GroupWord[{{"a",-2}}].
    See also: normalizeWord; GAP VVMF_WordIDs.
*)
decodeResultWord[syllables_, generators_List] := Module[{ids, names, exponents},
    If[!AllTrue[generators, resultFieldsQ[#, {"id", "name"}] &] ||
        !resultIDsQ[(#["id"] & /@ generators)] || !generatorNamesQ[(#["name"] & /@ generators)] ||
        !ListQ[syllables] || !AllTrue[syllables, MatchQ[#, {_String, _String}] &],
        Return[makeFailure["InvalidResultWord", "Malformed word or recorded generators."]]
    ];
    ids = #["id"] & /@ generators; names = #["name"] & /@ generators;
    If[!AllTrue[syllables, MemberQ[ids, First[#]] &],
        Return[makeFailure["InvalidResultWord", "A word contains an unknown generator ID."]]
    ];
    exponents = decodeInteger /@ (Last /@ syllables);
    If[AnyTrue[exponents, FailureQ],
        Return[makeFailure["InvalidResultWord", "Word exponents must be canonical integers."]]
    ];
    normalizeWord[GroupWord[MapThread[
        {names[[First[FirstPosition[ids, First[#1]]]]], #2} &,
        {syllables, exponents}]], names]
];
decodeResultWord[___] := makeFailure["InvalidResultWord", "Expected recorded generator data."];

(*
    Summary: Validate a retained construction record as data without executing it.
    Parameters: data — encoded typed specification or explicit gapCode record.
    Options/defaults: None. gapCode requires code, names and dependencies; dependency
        entries contain absolute path and lowercase 64-digit sha256 strings.
    Returns: The canonical record, or InvalidConstruction Failure.
    Effects: Pure; dependency files and retained source are not read or executed.
    Failures: Unknown schema, invalid exact domains, names, words or dependency records.
    Example: validateConstructionRecord[encodeConstruction[CatalogueGroup["CyclicGroup", 3]]]
        returns the same record.
    Remarks: External dependency availability is checked only at an explicit execution boundary.
    See also: validateSpecification; BuildGroupFromGAP in step1Plan.md.
*)
validateConstructionRecord[data_Association] := Module[
    {kind, specification, decoded, names, domain, cycles, degree, dependencies},
    kind = Lookup[data, "type", None];
    Switch[kind,
        "catalogue",
        If[!resultFieldsQ[data, {"type", "catalogue", "key"}],
            Return[makeFailure["InvalidConstruction", "Invalid catalogue record fields."]]];
        decoded = If[ListQ[data["key"]], decodeInteger /@ data["key"], decodeInteger[data["key"]]];
        specification = CatalogueGroup[data["catalogue"], decoded],
        "presentation",
        If[!resultFieldsQ[data, {"type", "names", "relators"}] ||
            !generatorNamesQ[data["names"]] || !ListQ[data["relators"]],
            Return[makeFailure["InvalidConstruction", "Invalid presentation record."]]];
        names = data["names"];
        decoded = decodeResultWord[#, Map[<|"id" -> #, "name" -> #|> &, names]] & /@ data["relators"];
        specification = GroupPresentation[names, decoded],
        "permutation",
        If[!resultFieldsQ[data, {"type", "names", "degree", "generators"}] ||
            !generatorNamesQ[data["names"]] || !ListQ[data["generators"]] ||
            !AllTrue[data["generators"], ListQ[#] && AllTrue[#, ListQ] &],
            Return[makeFailure["InvalidConstruction", "Invalid permutation record."]]];
        cycles = Map[decodeInteger, data["generators"], {3}];
        degree = decodeInteger[data["degree"]];
        If[!FreeQ[cycles, _Failure] || !AllTrue[cycles, Function[permutation,
            AllTrue[permutation, Length[#] > 0 && AllTrue[#, IntegerQ[#] && # > 0 &] &] &&
                DuplicateFreeQ[Flatten[permutation]]]] ||
            degree =!= Max[Prepend[Flatten[cycles], 0]],
            Return[makeFailure["InvalidConstruction", "Invalid cycles or degree."]]];
        specification = PermutationGroupSpecification[Cycles /@ cycles, data["names"]],
        "matrix",
        If[!resultFieldsQ[data, {"type", "names", "domain", "generators"}] ||
            !AssociationQ[data["domain"]] || !ListQ[data["generators"]] ||
            !AllTrue[data["generators"], ListQ[#] && AllTrue[#, ListQ] &],
            Return[makeFailure["InvalidConstruction", "Invalid matrix record."]]];
        domain = data["domain"];
        decoded = Map[If[AssociationQ[#] && Lookup[#, "type", None] === "cyclotomic",
            #, decodeScalar[#]] &, data["generators"], {3}];
        specification = MatrixGroupSpecification[decoded, data["names"], domain],
        "gapCode",
        If[!resultFieldsQ[data, {"type", "code", "names", "dependencies"}] ||
            !StringQ[data["code"]] || StringLength[data["code"]] === 0 ||
            !generatorNamesQ[data["names"]] || !ListQ[data["dependencies"]],
            Return[makeFailure["InvalidConstruction", "Invalid retained source record."]]];
        dependencies = data["dependencies"];
        If[!AllTrue[dependencies, resultFieldsQ[#, {"path", "sha256"}] &&
            absolutePathQ[#["path"]] && StringQ[#["sha256"]] &&
            StringMatchQ[#["sha256"], RegularExpression["[0-9a-f]{64}"]] &] ||
            !DuplicateFreeQ[(#["path"] & /@ dependencies)],
            Return[makeFailure["InvalidConstruction", "Invalid dependency records."]]];
        Return[data],
        _, Return[makeFailure["InvalidConstruction", "Unknown retained construction type."]]
    ];
    decoded = validateSpecification[specification];
    If[FailureQ[decoded],
        makeFailure["InvalidConstruction", "The retained construction is invalid.", <|"Cause" -> decoded|>],
        decoded]
];
validateConstructionRecord[___] := makeFailure["InvalidConstruction", "Expected a construction record."];

(*
    Summary: Exact class-weighted Gram matrix of character rows in their common cyclotomic field.
    Parameters: records — rows of validated scalar records; sizes — class sizes.
    Options/defaults: None.
    Returns: Matrix of rationals when the field reduction leaves constants, otherwise reduced
        polynomials (which then differ from the expected rational matrix), or Failure.
    Effects: Pure.
    Failures: Invalid scalar records.
    Example: for C2 {{1,1},{1,-1}} with sizes {1,1} the result is {{2,0},{0,2}}.
    Remarks: Works modulo Cyclotomic[n, z] with n the least common multiple of the root orders;
        reduced representatives are canonical, so the comparison with order*IdentityMatrix is exact.
        RootReduce of the same products took 25 s for C16 and longer for C25.
    See also: scalarCyclotomicPolynomial; decodeCharacterData.
*)
exactCharacterGram[records_List, sizes_List] := Module[{z, n, polys, conjugates, gram},
    n = LCM @@ Join[{1}, Cases[records, r_Association /; Lookup[r, "type", None] === "cyclotomic" :>
        Lookup[r, "rootOrder", 1], {2}]];
    If[!IntegerQ[n] || n < 1, Return[makeFailure["InvalidCharacters", "Invalid cyclotomic root orders."]]];
    polys = Map[scalarCyclotomicPolynomial[#, n, z] &, records, {2}];
    If[!FreeQ[polys, _Failure], Return[FirstCase[polys, _Failure, Null, Infinity]]];
    conjugates = polys /. z -> z^(n - 1);
    gram = polys . DiagonalMatrix[sizes] . Transpose[conjugates];
    Map[PolynomialRemainder[Expand[#], Cyclotomic[n, z], z] &, gram, {2}]
];

(*
    Summary: Decode and independently check exact character-table invariants.
    Parameters: data — character schema; order — positive group order; generators —
        validated ID/name records; status — Partial or Complete.
    Options/defaults: None.
    Returns: CharacterData association with public keys and exact values, or Failure.
    Effects: Pure; no group construction or provenance claim.
    Failures: Invalid IDs/shapes, classes, words, degrees, orthogonality, trivial row,
        or inconsistent completeness.
    Example: a two-row C2 table {{1,1},{1,-1}} has degrees {1,1} and two unit classes.
    Remarks: Exact weighted row orthogonality and degree sums supplement native group
        binding. They cannot detect every reassignment of values to class words.
    See also: validateGroupResult; GAP VVMF_CheckCharacters; Schemas/GroupResult.md.
*)
decodeCharacterData[data_, order_Integer, generators_List, status_String, gramLevel_ : Automatic] := Module[
    {fields, rowIDs, classIDs, sizes, orders, words, values, degrees, identity, trivial,
        expectedTrivial, rows, columns, complete, gram},
    fields = {"identity", "irrepIDs", "classIDs", "values", "classSizes", "classOrders",
        "classRepresentativeWords", "identityClassID", "trivialIrrepID", "degrees"};
    If[!resultFieldsQ[data, fields] || !resultIDsQ[{data["identity"]}] ||
        !resultIDsQ[data["irrepIDs"]] || !resultIDsQ[data["classIDs"]] ||
        !MemberQ[{"Partial", "Complete"}, status] || order < 1,
        Return[makeFailure["InvalidCharacters", "Invalid character record or identities."]]];
    rowIDs = data["irrepIDs"]; classIDs = data["classIDs"];
    rows = Length[rowIDs]; columns = Length[classIDs];
    If[columns < 1 || rows > columns || Intersection[rowIDs, classIDs] =!= {} ||
        !AllTrue[{"classSizes", "classOrders", "classRepresentativeWords"},
            ListQ[data[#]] && Length[data[#]] === columns &] ||
        !ListQ[data["degrees"]] || Length[data["degrees"]] =!= rows ||
        !ListQ[data["values"]] || Length[data["values"]] =!= rows ||
        !AllTrue[data["values"], ListQ[#] && Length[#] === columns &] ||
        !MemberQ[classIDs, data["identityClassID"]],
        Return[makeFailure["InvalidCharacters", "Character and class dimensions disagree."]]];
    sizes = decodeInteger /@ data["classSizes"];
    orders = decodeInteger /@ data["classOrders"];
    degrees = decodeInteger /@ data["degrees"];
    If[!AllTrue[Join[sizes, orders, degrees], IntegerQ[#] && # > 0 &] ||
        Total[sizes] =!= order || !AllTrue[Join[sizes, orders], Divisible[order, #] &],
        Return[makeFailure["InvalidCharacters", "Invalid class sizes, orders or degrees."]]];
    identity = First[FirstPosition[classIDs, data["identityClassID"]]];
    If[orders[[identity]] =!= 1 || sizes[[identity]] =!= 1 || Count[orders, 1] =!= 1,
        Return[makeFailure["InvalidCharacters", "Invalid identity conjugacy class."]]];
    words = decodeResultWord[#, generators] & /@ data["classRepresentativeWords"];
    If[AnyTrue[words, FailureQ] || !DuplicateFreeQ[words] ||
        AnyTrue[Delete[words, identity], # === GroupWord[{}] &],
        Return[makeFailure["InvalidCharacters", "Invalid class representative words."]]];
    values = Map[decodeScalar, data["values"], {2}];
    If[!FreeQ[values, _Failure] || (rows > 0 && values[[All, identity]] =!= degrees),
        Return[makeFailure["InvalidCharacters", "Invalid scalar values or identity-column degrees."]]];
    (* the Gram check of a weakly built table ("TransportOnly" claims) runs at the acceptance level: numerically at
       "Numerical", not at None; GAP-proved tables keep the exact re-check (methodOptionsPlan.md 2C.6) *)
    Which[
        gramLevel === None, Null,
        gramLevel === "Numerical",
            With[{numeric = If[rows === 0, {}, Table[Sum[sizes[[k]] N[values[[i, k]] Conjugate[values[[j, k]]], 40], {k, columns}], {i, rows}, {j, rows}]]},
                If[rows > 0 && Max[Abs[Flatten[numeric - order IdentityMatrix[rows]]]] > 10^-25 order || Total[degrees^2] > order,
                    Return[makeFailure["InvalidCharacters", "Numerical character orthogonality failed."]]]],
        True,
            gram = If[rows === 0, {}, exactCharacterGram[data["values"], sizes]];
            If[FailureQ[gram], Return[gram]];
            If[gram =!= If[rows === 0, {}, order IdentityMatrix[rows]] ||
                Total[degrees^2] > order,
                Return[makeFailure["InvalidCharacters", "Exact character orthogonality failed."]]]];
    trivial = Flatten[Position[values, ConstantArray[1, columns], {1}]];
    expectedTrivial = If[trivial === {}, Null, rowIDs[[First[trivial]]]];
    If[Length[trivial] > 1 || data["trivialIrrepID"] =!= expectedTrivial,
        Return[makeFailure["InvalidCharacters", "The trivial character ID is inconsistent."]]];
    complete = rows === columns && Total[degrees^2] === order && Length[trivial] === 1;
    If[(status === "Complete") =!= complete,
        Return[makeFailure["IncompleteCharacters", "Character completeness was reported incorrectly."]]];
    <|"Identity" -> data["identity"], "IrrepIDs" -> rowIDs, "ClassIDs" -> classIDs,
        "Values" -> values, "ClassSizes" -> sizes, "ClassOrders" -> orders,
        "ClassRepresentativeWords" -> words, "IdentityClassID" -> data["identityClassID"],
        "TrivialIrrepID" -> If[expectedTrivial === Null, Missing["NotComputed"], expectedTrivial],
        "Degrees" -> degrees|>
];
decodeCharacterData[___] := makeFailure["InvalidCharacters", "Malformed character validation input."];

(*
    Summary: Validate an exact group-result envelope against the owned request.
    Parameters: result — schema-1 or schema-2 JSON association; request — expected requestID,
        stateID, generatorIdentity, stateGeneration and operation, with optional
        construction and characterIdentity constraints.
    Options/defaults: None.
    Returns: Decoded association; BaseReady and Partial remain explicitly unpublished.
    Effects: Pure; does not allocate a Group or issue a provenance receipt.
    Failures: Unsupported schema/optional payload, mismatched identities, construction,
        availability, producer/binding claims or exact mathematical invariants.
    Example: a complete result has "Status" -> "Complete" and decoded "CharacterData".
    Remarks: The caller must separately establish actual producer/group correspondence.
        A binding boolean in an imported record is insufficient evidence.
    See also: decodeCharacterData; newGroup; Schemas/GroupResult.md.
*)
(* The acceptance level of weak claims (methodOptionsPlan.md 2C.6): Automatic (full claims required), "Numerical" or None
   (GAP's "TransportOnly" character claims and an "Unverified" S,T claim are accepted). Public entry points scope it with
   Block: a build its Verification, an enrichment its group's status, a correspondence import full. *)
If[!ValueQ[$GroupAcceptanceLevel], $GroupAcceptanceLevel = Automatic];
(* True only while ImportGroupData decodes a ledger-registered file (fastLoad.md): its exact character Gram re-check is
   skipped (the table was proved when the file was saved); the claims and statuses are read as for any file. *)
If[!ValueQ[$TrustedSnapshotDecode], $TrustedSnapshotDecode = False];
groupStatusLevel[status_] := Switch[status, "Unverified", None, "Numerical", "Numerical", _, Automatic];

validateGroupResult[result_Association, request_Association] := validateGroupResult[result, request, $GroupAcceptanceLevel];
validateGroupResult[result_Association, request_Association, level_] := Module[
    {weakCharacters, weakAssignment, groupStatus, fields, requestKeys, status, generation, order, construction, generators, names,
        catalogue, characters, available, binding, bindingKeys, producer, expectedAvailability, modular,
        elements, certificate, wordOrder, decodedOrderWord, subgroups, descriptions, subgroupQuery, selectedQuery,
        representations},
    fields = {"schemaVersion", "requestID", "stateID", "generatorIdentity", "stateGeneration",
        "operation", "status", "construction", "generators", "order", "catalogueID",
        "characterData", "availableData", "elements", "subgroupData", "modularAssignment",
        "producer", "binding", "diagnostics"};
    (* Schema 2 adds representationData; schema 1 envelopes carry no representation data. *)
    If[Lookup[result, "schemaVersion", None] === 2, AppendTo[fields, "representationData"]];
    requestKeys = {"requestID", "stateID", "generatorIdentity", "stateGeneration", "operation"};
    If[!resultFieldsQ[result, fields] || !MemberQ[{1, 2}, result["schemaVersion"]] || !resultJSONQ[result],
        Return[makeFailure["InvalidResultSchema", "Expected exact group-result schema 1 or 2."]]];
    If[!AllTrue[requestKeys, KeyExistsQ[request, #] && result[#] === request[#] &] ||
        !AllTrue[DeleteCases[requestKeys, "stateGeneration"],
            StringQ[result[#]] && StringLength[result[#]] > 0 &],
        Return[makeFailure["StateConflict", "The result does not match the expected request."]]];
    If[!gapOperationQ[result["operation"]],
        Return[makeFailure["UnsupportedOperation", "The result operation has no installed validator."]]];
    generation = decodeInteger[result["stateGeneration"]];
    order = decodeInteger[result["order"]]; status = result["status"];
    If[!IntegerQ[generation] || generation < 0 || !IntegerQ[order] || order < 1 ||
        !MemberQ[{"BaseReady", "Partial", "Complete"}, status],
        Return[makeFailure["InvalidResultSchema", "Invalid generation, finite order or status."]]];
    construction = validateConstructionRecord[result["construction"]];
    If[FailureQ[construction], Return[construction]];
    If[KeyExistsQ[request, "construction"] &&
        canonicalJSON[construction] =!= canonicalJSON[request["construction"]],
        Return[makeFailure["StateConflict", "The returned construction differs from the request."]]];
    generators = result["generators"];
    If[!ListQ[generators] || !AllTrue[generators, resultFieldsQ[#, {"id", "name"}] &] ||
        !resultIDsQ[(#["id"] & /@ generators)] || !generatorNamesQ[(#["name"] & /@ generators)],
        Return[makeFailure["InvalidResultSchema", "Invalid ordered generator records."]]];
    names = #["name"] & /@ generators;
    If[(construction["type"] =!= "catalogue" && names =!= construction["names"]) ||
        (construction["type"] === "catalogue" &&
            names =!= Table["g" <> ToString[i], {i, Length[names]}]) ||
        (names === {} && order =!= 1),
        Return[makeFailure["InvalidResultSchema", "Recorded generators disagree with the construction."]]];
    catalogue = If[result["catalogueID"] === Null, Missing["NotAvailable"],
        If[MatchQ[result["catalogueID"], {_String, _String}],
            decodeInteger /@ result["catalogueID"], $Failed]];
    If[!MissingQ[catalogue] && (!MatchQ[catalogue, {_Integer, _Integer}] ||
        First[catalogue] =!= order || Last[catalogue] < 1),
        Return[makeFailure["InvalidResultSchema", "Invalid finite group catalogue ID."]]];
    subgroups = decodeSubgroupData[result["subgroupData"], order, generators, result["stateID"]];
    If[FailureQ[subgroups], Return[subgroups]];
    elements = If[result["elements"] === Null, Missing["NotComputed"],
        If[ListQ[result["elements"]] && Length[result["elements"]] === order,
            decodeResultWord[#, generators] & /@ result["elements"],
            makeFailure["InvalidElements", "The element collection must have the finite group order."]]];
    If[FailureQ[elements] || (!MissingQ[elements] &&
        (AnyTrue[elements, FailureQ] || !DuplicateFreeQ[elements])),
        Return[makeFailure["InvalidElements", "Invalid or repeated element words."]]];
    If[result["operation"] === "GroupElementWords" && MissingQ[elements],
        Return[makeFailure["InvalidElements", "The requested element collection is absent."]]];
    (* weak claims are accepted only at a weak acceptance level *)
    weakCharacters = MemberQ[{"Numerical", None}, level] && Lookup[Replace[result["binding"], Except[_Association] -> <||>], "nativeCharactersVerified", None] === "TransportOnly";
    weakAssignment = MemberQ[{"Numerical", None}, level] && AssociationQ[result["modularAssignment"]] && Lookup[result["modularAssignment"], "verified", None] === "Unverified";
    modular = decodeModularAssignment[If[weakAssignment, Join[result["modularAssignment"], <|"verified" -> True|>], result["modularAssignment"]], generators];
    If[FailureQ[modular], Return[modular]];
    characters = If[status === "BaseReady",
        If[result["characterData"] === Null, Missing["NotComputed"],
            makeFailure["InvalidCharacters", "BaseReady cannot contain character data."]],
        decodeCharacterData[result["characterData"], order, generators, status, Which[weakCharacters, level, TrueQ[$TrustedSnapshotDecode], None, True, Automatic]]];
    If[FailureQ[characters], Return[characters]];
    representations = If[AssociationQ[characters] && status === "Complete",
        decodeRepresentationData[Lookup[result, "representationData", Null], characters, generators,
            result["generatorIdentity"], modular],
        If[Lookup[result, "representationData", Null] === Null, <||>,
            makeFailure["InvalidRepresentation", "Representation data require complete characters."]]];
    If[FailureQ[representations], Return[representations]];
    If[KeyExistsQ[request, "modularAssignment"] &&
        (!AssociationQ[modular] || !AssociationQ[request["modularAssignment"]] ||
            Lookup[request["modularAssignment"], "identity", None] =!= modular["Identity"] ||
            Lookup[request["modularAssignment"], "sWord", None] =!= encodeWord[modular["S"], names] ||
            Lookup[request["modularAssignment"], "tWord", None] =!= encodeWord[modular["T"], names]),
        Return[makeFailure["StateConflict", "The modular assignment differs from the requested pair."]]];
    expectedAvailability = <|"Characters" -> If[status === "BaseReady", "NotComputed", status],
        "Elements" -> If[MissingQ[elements], "NotComputed", "Complete"],
        "Subgroups" -> If[MissingQ[subgroups], {},
            (<|"QueryID" -> #["QueryID"], "Status" -> "Complete", "Descriptions" -> #["Descriptions"]|> & /@ Values[subgroups])],
        "Representations" -> representationAvailability[representations, characters],
        "Descriptions" -> "NotComputed"|>;
    descriptions = If[MissingQ[subgroups], {}, Lookup[Values[subgroups], "Descriptions", {}]];
    If[MemberQ[descriptions, "Complete"], expectedAvailability["Descriptions"] =
        If[AllTrue[descriptions, # === "Complete" &], "Complete", "Partial"]];
    available = result["availableData"];
    If[!AssociationQ[available] || canonicalJSON[available] =!= canonicalJSON[expectedAvailability],
        Return[makeFailure["InvalidResultSchema", "Availability does not match the supplied data."]]];
    If[!MissingQ[characters] && KeyExistsQ[request, "characterIdentity"] &&
        characters["Identity"] =!= request["characterIdentity"],
        Return[makeFailure["StateConflict", "The character identity differs from the request."]]];
    binding = result["binding"];
    bindingKeys = {"kind", "stateID", "generatorIdentity", "finiteGroupVerified", "generatorsVerified"};
    If[status =!= "BaseReady", bindingKeys = Join[bindingKeys, {"characterIdentity",
        "classWordsVerified", "classTransportVerified", "nativeCharactersVerified"}]];
    If[AssociationQ[binding] && KeyExistsQ[binding, "generatorPresentation"],
        certificate = validateConstructionRecord[binding["generatorPresentation"]];
        If[FailureQ[certificate] || status =!= "Complete" ||
            Lookup[certificate, "type", None] =!= "presentation" || certificate["names"] =!= names,
            Return[makeFailure["InvalidGeneratorMap", "Invalid recorded-generator presentation certificate."]]];
        AppendTo[bindingKeys, "generatorPresentation"]];
    If[!resultFieldsQ[binding, bindingKeys] || binding["stateID"] =!= result["stateID"] ||
        binding["generatorIdentity"] =!= result["generatorIdentity"] ||
        binding["finiteGroupVerified"] =!= True || binding["generatorsVerified"] =!= True ||
        binding["kind"] =!= If[status === "BaseReady", "FiniteGroup", "NativeGroupCharacters"] ||
        (status =!= "BaseReady" && (binding["characterIdentity"] =!= characters["Identity"] || binding["classWordsVerified"] =!= True ||
            !AllTrue[{"classTransportVerified", "nativeCharactersVerified"}, binding[#] === If[weakCharacters, "TransportOnly", True] &])),
        Return[makeFailure["UnboundCharacterData", "Required producer binding claims are absent or inconsistent."]]];
    producer = result["producer"];
    If[!resultFieldsQ[producer, {"gapVersion", "kernelVersion", "buildVersion",
            "architecture", "buildDateTime", "packages"}] ||
        !AllTrue[{"gapVersion", "kernelVersion", "buildVersion", "architecture", "buildDateTime"},
            StringQ[producer[#]] &] || !AssociationQ[producer["packages"]] ||
        !AllTrue[Values[producer["packages"]], StringQ] ||
        !AssociationQ[result["diagnostics"]] ||
        Lookup[result["diagnostics"], "operation", None] =!= result["operation"],
        Return[makeFailure["InvalidResultSchema", "Malformed producer or diagnostic metadata."]]];
    If[result["operation"] === "GroupWordOrder",
        wordOrder = Lookup[result["diagnostics"], "wordOrder", None];
        If[!resultFieldsQ[wordOrder, {"word", "order"}],
            Return[makeFailure["InvalidWordOrder", "The requested word order is absent."]]];
        decodedOrderWord = decodeResultWord[wordOrder["word"], generators];
        wordOrder = decodeInteger[wordOrder["order"]];
        If[FailureQ[decodedOrderWord] || !IntegerQ[wordOrder] || wordOrder < 1 ||
            !Divisible[order, wordOrder] ||
            (KeyExistsQ[request, "word"] && encodeWord[decodedOrderWord, names] =!= request["word"]),
            Return[makeFailure["InvalidWordOrder", "The exact order or requested word is inconsistent."]]]];
    If[result["operation"] === "GroupSubgroups",
        subgroupQuery = Lookup[result["diagnostics"], "subgroupQueryID", None];
        If[!AssociationQ[subgroups] || !KeyExistsQ[subgroups, subgroupQuery],
            Return[makeFailure["InvalidSubgroups", "The requested subgroup query result is absent."]]];
        If[KeyExistsQ[request, "subgroupQuery"],
            selectedQuery = SelectFirst[result["subgroupData"], #["query"]["id"] === subgroupQuery &];
            If[canonicalJSON[KeyDrop[selectedQuery["query"], "descriptions"]] =!=
                    canonicalJSON[KeyDrop[request["subgroupQuery"], "descriptions"]] ||
                (TrueQ[request["subgroupQuery"]["descriptions"]] && !TrueQ[selectedQuery["query"]["descriptions"]]),
                Return[makeFailure["StateConflict", "The subgroup result differs from the requested filters or descriptions."]]]]];
    If[result["operation"] === "CheckGeneratorMap",
        certificate = decodeGeneratorMapReport[Lookup[result["diagnostics"], "generatorMap", None],
            generators, order, request];
        If[FailureQ[certificate], Return[certificate]]];
    If[result["operation"] === "Decompose" &&
        !With[{decomposition = Lookup[result["diagnostics"], "decomposition", None]},
            resultFieldsQ[decomposition, {"method", "alignment", "solutions"}] && AssociationQ[decomposition["solutions"]] &&
                AllTrue[Values[decomposition["solutions"]], ListQ[#] && AllTrue[#, MatrixQ[#, AssociationQ] &] &]],
        Return[makeFailure["InvalidDecomposition", "The requested decomposition is absent or malformed."]]];
    If[result["operation"] === "GeneratorPresentation" && !KeyExistsQ[binding, "generatorPresentation"],
        Return[makeFailure["InvalidGeneratorMap", "The requested generator certificate is absent."]]];
    <|"StateID" -> result["stateID"], "GeneratorIdentity" -> result["generatorIdentity"],
        "StateGeneration" -> generation, "RequestID" -> result["requestID"],
        "Operation" -> result["operation"], "Status" -> status, "Construction" -> construction,
        "Generators" -> (<|"ID" -> #["id"], "Name" -> #["name"]|> & /@ generators),
        "Order" -> order, "CatalogueID" -> catalogue, "CharacterData" -> characters,
        "AvailableData" -> available, "Elements" -> elements,
        "SubgroupData" -> subgroups, "ModularAssignment" -> modular,
        "Representations" -> representations, "Producer" -> producer, "Binding" -> binding,
        "LastComputation" -> result["diagnostics"],
        (* the group's own status (2C.6): a weakly built table or a skipped S,T check; absent means "Exact" *)
        Sequence @@ With[{s = cgWeakestStatus[{If[weakCharacters, If[level === "Numerical", "Numerical", "Unverified"], "Exact"],
                If[weakAssignment, "Unverified", "Exact"]}]}, If[s === "Exact", {}, {"VerificationStatus" -> s}]]|>
];
validateGroupResult[___] := makeFailure["InvalidResultSchema", "Expected result and request records."];

(*
    Summary: Decode an explicit group-level modular assignment without inventing one.
    Parameters: data — null or native assignment record; generators — validated ordered ID/name records.
    Options/defaults: Null maps to Missing[NotAssigned].
    Returns: Identity/S/T/Verified association of GroupWords or InvalidModularAssignment Failure.
    Effects: Pure; this validates structure, not the claimed group relations or generation.
    Failures: Extra/missing fields, absent native verification claim and malformed/unknown word IDs.
    Example: a generator named a may appear in S's word; no generator position implies S or T.
    Remarks: Actual group-level proof belongs to the owned native producer or independently
        verified import correspondence. A portable Verified field never creates provenance.
    See also: GAP/GroupData.g; validateGroupResult; AssignModularGenerators.
*)
decodeModularAssignment[Null, generators_List] := Missing["NotAssigned"];
decodeModularAssignment[data_Association, generators_List] := Module[{s, t},
    If[!resultFieldsQ[data, {"identity", "sWord", "tWord", "verified"}] ||
        !StringQ[data["identity"]] || StringLength[data["identity"]] === 0 || data["verified"] =!= True,
        Return[makeFailure["InvalidModularAssignment", "Malformed or unverified modular assignment."]]];
    s = decodeResultWord[data["sWord"], generators]; t = decodeResultWord[data["tWord"], generators];
    If[FailureQ[s] || FailureQ[t],
        makeFailure["InvalidModularAssignment", "The assignment has invalid recorded-generator words."],
        <|"Identity" -> data["identity"], "S" -> s, "T" -> t, "Verified" -> True|>]
];
decodeModularAssignment[___] := makeFailure["InvalidModularAssignment", "Expected null or a modular assignment and generators."];

True
