(*
    :Title: Representation values and group contexts
    :Context: VVMFTool`Private`
    :Summary: Transparent Rep values, their shared methods and immutable group contexts.
    :Responsibilities:
        - Validate Rep shape, arithmetic and invertibility; evaluate words on matrices.
        - Matrix-realization identity for caches and variants.
        - Freeze, bind and resolve RepresentationContext snapshots of accepted groups.
        - S and T accessors through an explicit modular assignment.
    :Dependencies: Diagnostics.wl; GroupWords.wl; RepresentationStorage.wl; ResultValidation.wl;
        GroupObject.wl; GroupIdentity.wl.
    :See Also: VVMFArch/step2Plan.md (object and result signatures); VVMFArch/design.md.
*)

(* Kernel-local context bindings: snapshot digest -> evidence. Portable files never create them. *)
If[!AssociationQ[$RepContextBindings], $RepContextBindings = <||>];
(* Bounded memo of full shape validation by value hash; pure recomputable data. *)
If[!AssociationQ[$RepShapeCache], $RepShapeCache = <||>];

(* -------------------------------------------------------------------------
   Rep values
   ------------------------------------------------------------------------- *)

(*
    Summary: Check the cheap structural contract of a Rep value.
    Parameters: rep — any expression.
    Options/defaults: None.
    Returns: <|"Dimension" -> d, "GeneratorCount" -> k, "Matrices" -> list|>, or InvalidRep Failure.
    Effects: Pure.
    Failures: Other heads, Rep[{}] without dimension, nonsquare or unequal matrices, zero
        dimension, symbolic or nonfinite entries.
    Example: repStructure[Rep[{{{0, 1}, {1, 0}}}]]["Dimension"] is 2.
    Remarks: Exactness of algebraic entries and invertibility are checked by validateRepShape.
    See also: validateRepShape; RepDim.
*)
repStructure[Rep[{}, dimension_Integer]] /; dimension >= 1 :=
    <|"Dimension" -> dimension, "GeneratorCount" -> 0, "Matrices" -> {}|>;
repStructure[Rep[matrices_List]] /; matrices =!= {} := Module[{dimension},
    If[!AllTrue[matrices, SquareMatrixQ], Return[makeFailure["InvalidRep", "Every generator matrix must be square."]]];
    dimension = Length[First[matrices]];
    If[dimension < 1 || !AllTrue[matrices, Length[#] === dimension &],
        Return[makeFailure["InvalidRep", "Generator matrices must share one positive dimension."]]];
    If[!AllTrue[Flatten[matrices], NumericQ] ||
        !FreeQ[matrices, DirectedInfinity | Indeterminate | ComplexInfinity | Overflow[] | Underflow[]],
        Return[makeFailure["InvalidRep", "Matrix entries must be finite numbers or exact numeric values."]]];
    <|"Dimension" -> dimension, "GeneratorCount" -> Length[matrices], "Matrices" -> matrices|>
];
repStructure[Rep[{}]] := makeFailure["InvalidRep", "Rep[{}] requires an explicit dimension: Rep[{}, d]."];
repStructure[___] := makeFailure["InvalidRep", "Expected Rep[matrices] or Rep[{}, dimension]."];

(*
    Summary: Validate a Rep value's matrices, arithmetic and invertibility.
    Parameters: rep — any expression.
    Options/defaults: None.
    Returns: <|"Dimension", "GeneratorCount", "Arithmetic" -> "Exact" | "Numerical",
        "Precision" -> Infinity | MachinePrecision | p|>, or InvalidRep/SingularRep Failure.
    Effects: Memoizes results in the bounded kernel-local $RepShapeCache.
    Failures: Structural failures; exact entries that are not algebraic numbers (symbolic
        parameters, Pi, undecided values); singular generator matrices.
    Example: validateRepShape[Rep[{{{1, 0}, {0, -1}}}]]["Arithmetic"] is "Exact".
    Remarks: A matrix with any approximate entry is numerical. Exact invertibility is proved by the
        determinant in an exact number field of the entries (exactField), or by RootReduce of the determinant
        when no field is found. Numerical invertibility requires the smallest singular
        value to exceed 10^(-Floor[p/2]) times the largest, with p the matrix precision (16 for
        machine numbers), the plan's automatic tolerance. A valid shape does not certify that
        the matrices represent any particular group.
    See also: repStructure; exactAlgebraicQ; ValidateRepresentation in step2Plan.md.
*)
validateRepShape[rep_] := Module[{key = Hash[rep, "SHA256"], structure, matrices, exact, precision,
        arithmetic, singular, digits, result},
    result = Lookup[$RepShapeCache, key, None];
    If[result =!= None, Return[result]];
    structure = repStructure[rep];
    If[FailureQ[structure], Return[structure]];
    matrices = structure["Matrices"];
    precision = If[matrices === {}, Infinity, Precision[matrices]];
    arithmetic = If[precision === Infinity, "Exact", "Numerical"];
    exact = DeleteDuplicates[Select[Flatten[matrices], Precision[#] === Infinity &]];
    If[!AllTrue[exact, exactAlgebraicQ],
        Return[makeFailure["InvalidRep", "Exact entries must be algebraic numbers; symbolic parameters are not supported."]]];
    digits = Which[precision === Infinity, Infinity, precision === MachinePrecision, 16, True, Floor[precision]];
    singular = If[arithmetic === "Exact",
        (* A determinant far above its rounding-error bound is certainly nonzero (certifiedNonsingularQ); only an
           inconclusive case needs the exact field: determinants in an exact number field when one is found (RootReduce of a large determinant
           expression is very slow for algebraic entries). Loading the library's 120-35 took 63 s in the field
           search for this check alone. *)
        If[AllTrue[matrices, certifiedNonsingularQ], False, With[{field = exactField[matrices]},
            If[field["Kind"] === "NumberField", AnyTrue[fieldEmbed[field, matrices], Det[#] === 0 &],
                AnyTrue[matrices, RootReduce[Det[#]] === 0 &]]]],
        AnyTrue[matrices, With[{values = SingularValueList[N[#, precision], Tolerance -> 0]},
            Length[values] < Length[#] || Min[values] <= 10^(-Floor[digits/2]) Max[values]] &]];
    If[singular, Return[makeFailure["SingularRep", "Generator matrices must be invertible."]]];
    result = <|"Dimension" -> structure["Dimension"], "GeneratorCount" -> structure["GeneratorCount"],
        "Arithmetic" -> arithmetic, "Precision" -> precision|>;
    If[Length[$RepShapeCache] >= 1024, $RepShapeCache = <||>];
    AssociateTo[$RepShapeCache, key -> result];
    result
];

(* A nonzero determinant certified by an explicit rounding-error bound (review F13: Det of an arbitrary-precision matrix
   does not propagate significance, so its Precision/Accuracy prove nothing). Entries are evaluated to 60 digits; the
   computed determinant of an n x n matrix then differs from the exact one by at most about n 2^(n-1) 10^-60 times the
   Hadamard bound prod_i ||row_i|| (LU with partial pivoting, worst-case growth 2^(n-1); for n <= 60 below 10^-40 of
   the bound), so |d| > 10^-30 prod_i ||row_i|| proves det != 0. Anything smaller is decided by the exact field test. *)
certifiedNonsingularQ[m_] := Module[{a = Quiet[N[m, 60]], d, hadamard},
    (* the bound below is stated for n <= 60 (review F22) *)
    If[!MatrixQ[a, NumericQ] || Length[a] > 60, Return[False]];
    d = Quiet[Det[a]]; hadamard = Times @@ (Norm /@ a);
    NumericQ[d] && NumericQ[hadamard] && hadamard > 0 && Abs[d] > 10^-30 hadamard];

(*
    Summary: Return the ordered generator matrices of a structurally valid Rep.
    Parameters: rep — Rep value.
    Options/defaults: None.
    Returns: List of matrices ({} for Rep[{}, d]), or InvalidRep Failure.
    Effects: Pure.
    Failures: As repStructure.
    Example: repMatrices[Rep[{}, 3]] is {}.
    See also: GeneratorMatrix; repStructure.
*)
repMatrices[rep_] := With[{structure = repStructure[rep]},
    If[FailureQ[structure], structure, structure["Matrices"]]];

(*
    Summary: Bring an exact matrix to the package's canonical exact form.
    Parameters: matrix — exact algebraic matrix; approximate matrices are returned unchanged.
    Options/defaults: None.
    Returns: The matrix with RootReduced entries.
    Effects: Pure.
    Failures: None.
    Example: canonicalMatrix[{{Exp[2 Pi I/3]}}] is {{(-1 + I Sqrt[3])/2}}.
    Remarks: RootReduce is idempotent and gives equal values one form, so decoded, computed and
        imported exact matrices compare with SameQ.
    See also: wordMatrix; decodeRepScalar.
*)
canonicalMatrix[matrix_] := If[Precision[matrix] === Infinity, Map[RootReduce, matrix, {2}], matrix];

(*
    Summary: Evaluate an ordered group word on a Rep's generator matrices.
    Parameters: rep — shape-valid Rep; word — GroupWord (syllables or text) or text; names —
        ordered generator names, one per generator matrix.
    Options/defaults: None.
    Returns: The d-by-d product matrix, canonical for exact data, or InvalidWord/GeneratorBindingMismatch Failure.
    Effects: Pure.
    Failures: Invalid names, a name count different from the generator count, unknown generators
        or malformed words. Rep[{}, d] admits only the empty word.
    Example: wordMatrix[Rep[{{{0, -1}, {1, 0}}}], GroupWord[{{"s", 2}}], {"s"}] is {{-1, 0}, {0, -1}}.
    Remarks: Syllables multiply left to right; negative powers use exact or numerical inverses.
        This evaluates matrices only; it does not assert any group relation.
    See also: RepMatrix; normalizeWord; SRep.
*)
wordMatrix[rep_, word_, names_List] := Module[{structure, normalized, matrices, product, inverses = <||>, base},
    structure = repStructure[rep];
    If[FailureQ[structure], Return[structure]];
    If[!generatorNamesQ[names] || Length[names] =!= structure["GeneratorCount"],
        Return[makeFailure["GeneratorBindingMismatch",
            "The generator names must be distinct and correspond one-to-one to the generator matrices.",
            <|"GeneratorCount" -> structure["GeneratorCount"], "Names" -> names|>]]];
    normalized = normalizeWord[word, names];
    If[FailureQ[normalized], Return[normalized]];
    matrices = AssociationThread[names, structure["Matrices"]];
    product = IdentityMatrix[structure["Dimension"]];
    Do[
        base = If[Last[syllable] > 0, matrices[First[syllable]],
            Lookup[inverses, First[syllable],
                inverses[First[syllable]] = canonicalMatrix[Inverse[matrices[First[syllable]]]]]];
        product = canonicalMatrix[product . MatrixPower[base, Abs[Last[syllable]]]],
        {syllable, First[normalized]}];
    product
];
wordMatrix[___] := makeFailure["InvalidWord", "Expected a Rep, word and generator names."];

(*
    Summary: Fingerprint a matrix realization on an ordered generating set.
    Parameters: rep — valid Rep; names — ordered generator names; precision — declared numerical
        precision for numerical data (MachinePrecision or an integer of at least 16).
    Options/defaults: precision defaults to Automatic: the matrices' own precision.
    Returns: Lowercase 64-digit SHA256 string, or Failure.
    Effects: Pure.
    Failures: Invalid Rep, name/generator mismatch, numerical precision below 16 digits.
    Example: repIdentity[Rep[{{{1}}}], {"a"}] === repIdentity[Rep[{{{1}}}], {"a"}].
    Remarks: Exact identity digests the RootReduced entries, so storage codec and input form do
        not matter. Numerical identity digests the declared-precision encoded records, because
        SameQ on approximate numbers uses a tolerance. Basis properties and provenance are not part
        of this identity.
    See also: canonicalMatrix; encodeNumerical; step2Plan.md representation entries.
*)
repIdentity[rep_, names_List, precision_ : Automatic] := Module[{shape, matrices, declared, entries},
    shape = validateRepShape[rep];
    If[FailureQ[shape], Return[shape]];
    If[!generatorNamesQ[names] || Length[names] =!= shape["GeneratorCount"],
        Return[makeFailure["GeneratorBindingMismatch", "The generator names must correspond to the generator matrices."]]];
    matrices = repMatrices[rep];
    If[shape["Arithmetic"] === "Exact",
        Return[identityDigest[{"Exact", names, shape["Dimension"], canonicalMatrix /@ matrices}]]];
    declared = If[precision === Automatic,
        If[shape["Precision"] === MachinePrecision, MachinePrecision, Floor[shape["Precision"]]], precision];
    entries = Map[encodeNumerical[#, declared] &, matrices, {3}];
    If[!FreeQ[entries, _Failure],
        Return[makeFailure["InsufficientPrecision", "Numerical identity requires MachinePrecision or at least 16 digits."]]];
    identityDigest[{"Numerical", names, shape["Dimension"], entries}]
];

(*
    Summary: Shared methods of the transparent Rep value.
    Status: Alpha.
    Fields: Rep[{M1, ..., Mk}] holds the square invertible matrices of the k recorded generators in
        their recorded order; Rep[{}, d] is the d-dimensional representation of a group with no
        recorded generators.
    Defaults: None; Rep values are inert data.
    Returns: RepDim[r] — positive dimension; NumberOfGenerator[r] — k; GeneratorMatrix[r, i] — the
        i-th stored matrix; RepMatrix[r, word, names] — the word evaluated on the matrices, with names
        naming the generators in order. Invalid values or arguments give Failure.
    Identity/mutation: A Rep is a value; transformations return new values and never change inputs.
        A valid shape does not certify the matrices as a representation of a particular group.
    Example: RepMatrix[Rep[{{{0, 1}, {1, 0}}}], GroupWord["a^2"], {"a"}] is IdentityMatrix[2].
    See also: validateRepShape; wordMatrix; RepresentationContext.
*)
Unprotect[Rep];
Rep /: RepDim[rep_Rep] := With[{structure = repStructure[rep]},
    If[FailureQ[structure], structure, structure["Dimension"]]];
Rep /: NumberOfGenerator[rep_Rep] := With[{structure = repStructure[rep]},
    If[FailureQ[structure], structure, structure["GeneratorCount"]]];
Rep /: GeneratorMatrix[rep_Rep, index_Integer] := With[{structure = repStructure[rep]},
    Which[FailureQ[structure], structure,
        1 <= index <= structure["GeneratorCount"], structure["Matrices"][[index]],
        True, makeFailure["InvalidGeneratorIndex", "The generator index is outside the recorded generators.",
            <|"Index" -> index, "GeneratorCount" -> structure["GeneratorCount"]|>]]];
Rep /: RepMatrix[rep_Rep, word_GroupWord, names_List] := With[{shape = validateRepShape[rep]},
    If[FailureQ[shape], shape, wordMatrix[rep, word, names]]];
(* A Rep shows its matrices with readable entries (radicals or e^{2 Pi i k/n}, uxUpdatePlan.md 3); the value itself keeps
   its canonical entries, so identities, BasisIDs and cache keys are unchanged. *)
Format[rep : Rep[___], StandardForm] := With[{structure = Quiet[repStructure[rep]]},
    If[AssociationQ[structure],
        Interpretation[Row[{"Rep[", Row[withReadableBudget[MatrixForm[readableMatrix[#]] & /@ structure["Matrices"]], ", "], "]"}], rep],
        Interpretation[Row[{"Rep[", Length[rep], " parts]"}], rep]]];
Protect[Rep];
RepDim[___] := makeFailure["InvalidRep", "RepDim expects one Rep value."];
NumberOfGenerator[___] := makeFailure["InvalidRep", "NumberOfGenerator expects one Rep value."];
GeneratorMatrix[___] := makeFailure["InvalidRep", "GeneratorMatrix expects a Rep and an integer generator index."];
RepMatrix[___] := makeFailure["InvalidRep", "RepMatrix expects a Rep, a GroupWord and the ordered generator names."];

(* -------------------------------------------------------------------------
   Group contexts
   ------------------------------------------------------------------------- *)

$RepContextFields = {"GroupIdentity", "GeneratorIdentity", "GeneratorIDs", "GeneratorNames", "Order",
    "Construction", "StateGeneration", "CharacterData", "ModularAssignment", "Representations"};
(* Presentation keys (uxUpdatePlan.md 1.2): carried by a context for display and index resolution, never part of its
   digest or of the evidence check, so they can follow the live group without changing the context's identity. *)
$RepContextPresentationKeys = {"IrrepOrder", "IrrepLabels", "ClassLabels", "ClassOrder", "SourceInstanceID"};
(* Verification statuses (methodOptionsPlan.md 2C; user decision 2026-10-13): the group's status is an optional context
   field and every variant may carry one; neither is part of the context digest, so raising a status never invalidates
   the contexts, vectors and models built before. The group result digest (the receipt) does include them. *)
contextDigestData[data_Association] := Module[{core = KeyDrop[data, Append[$RepContextPresentationKeys, "VerificationStatus"]]},
    If[AssociationQ[Lookup[core, "Representations", None]],
        core["Representations"] = Map[If[AssociationQ[#] && AssociationQ[Lookup[#, "Variants", None]],
            Join[#, <|"Variants" -> Map[If[AssociationQ[#], KeyDrop[#, "VerificationStatus"], #] &, #["Variants"]]|>], #] &, core["Representations"]]];
    core];
contextDigestData[data_] := data;
(* The statuses a context states (the group's and each variant's, defaults included): outside the digest, they are
   protected by the binding instead (review 2C-iii-a F1): a bound context records them, and a presented context may
   state nothing stronger than what was recorded for its digest. *)
contextStatusMap[data_Association] := Join[<|"Group" -> groupVerificationStatus[data]|>,
    Association[Flatten[KeyValueMap[Function[{id, entry}, If[AssociationQ[entry] && AssociationQ[Lookup[entry, "Variants", None]],
        KeyValueMap[{id, #1} -> variantVerificationStatus[#2] &, entry["Variants"]], {}]], Lookup[data, "Representations", <||>]]]]];
contextStatusMap[_] := <||>;
(* The recorded map keeps, per key, the strongest status ever bound for the digest (each one was established). Two
   bindings with one digest share it: the digest binds the same state, variant IDs and matrices, so a status established
   for one holds for the other. *)
registerContextBinding[digest_String, binding_Association, statuses_Association] := With[{prior = Lookup[Lookup[$RepContextBindings, digest, <||>], "Statuses", <||>]},
    AssociateTo[$RepContextBindings, digest -> Join[binding, <|"Statuses" -> Merge[{prior, statuses}, Last[SortBy[#, cgStatusRank]] &]|>]]];
contextStatusesBoundQ[data_Association, recorded_Association] := AllTrue[Normal[contextStatusMap[data]],
    KeyExistsQ[recorded, First[#]] && cgStatusRank[Last[#]] <= cgStatusRank[recorded[First[#]]] &];

(*
    Summary: Digest a context snapshot independently of association key order.
    Parameters: data — context snapshot association.
    Options/defaults: None.
    Returns: Lowercase SHA256 string.
    Effects: Pure.
    Failures: None.
    Example: contextDigest[KeySort[data]] === contextDigest[data].
    Remarks: The presentation keys ($RepContextPresentationKeys) and the verification statuses (the group's and every
        variant's) are not digested (contextDigestData).
    See also: freezeContext; resolveRepContext.
*)
contextDigest[data_] := identityDigest[{"RepresentationContext", sortAssociationKeys[contextDigestData[data]]}];

(*
    Summary: Sort the keys of every association inside an expression, keeping list order.
    Parameters: expression — any expression.
    Options/defaults: None.
    Returns: The expression with recursively key-sorted associations.
    Effects: Pure.
    Failures: None.
    Example: sortAssociationKeys[<|"b" -> <|"d" -> 1, "c" -> 2|>, "a" -> {3}|>] is
        <|"a" -> {3}, "b" -> <|"c" -> 2, "d" -> 1|>|>.
    See also: contextDigest; canonicalJSON.
*)
sortAssociationKeys[association_Association] := KeySort[sortAssociationKeys /@ association];
sortAssociationKeys[list_List] := sortAssociationKeys /@ list;
sortAssociationKeys[head_[arguments___]] := head @@ (sortAssociationKeys /@ {arguments});
sortAssociationKeys[atom_] := atom;

(*
    Summary: The context snapshot fields of group data.
    Parameters: data — decoded group data (accepted, or a verified import candidate).
    Options/defaults: None.
    Returns: Association with the $RepContextFields.
    Effects: Pure; nothing is registered.
    Failures: None.
    Example: contextSnapshot[groupData[g]]["GeneratorNames"] lists g's generator names.
    See also: freezeContext; verifyInertVariants.
*)
contextSnapshot[data_Association] := <|"GroupIdentity" -> data["StateID"], "GeneratorIdentity" -> data["GeneratorIdentity"],
    "GeneratorIDs" -> Lookup[data["Generators"], "ID", {}],
    "GeneratorNames" -> Lookup[data["Generators"], "Name", {}], "Order" -> data["Order"],
    "Construction" -> data["Construction"], "StateGeneration" -> data["StateGeneration"],
    "CharacterData" -> data["CharacterData"], "ModularAssignment" -> data["ModularAssignment"],
    "Representations" -> data["Representations"],
    (* the group's own status, carried when recorded (not digested: contextDigestData) *)
    Sequence @@ If[KeyExistsQ[data, "VerificationStatus"], {"VerificationStatus" -> data["VerificationStatus"]}, {}]|>;

(*
    Summary: Freeze an accepted group's current mathematical data as an immutable context.
    Parameters: group — live Group handle.
    Options/defaults: None.
    Returns: RepresentationContext[snapshot] with the $RepContextFields, or Failure.
    Effects: Registers the snapshot digest in the kernel-local $RepContextBindings with the group's
        validation receipt as evidence. The group is not changed.
    Failures: Unknown handles or data without a matching validation receipt.
    Example: RepresentationContext[g]["Order"] equals g["Order"]; later assignments of g do not
        change an already frozen context.
    Remarks: Representations holds the group's accepted representation data at freeze time.
    See also: bindRepContext; resolveRepContext; RepresentationContext.
*)
(*
    Summary: The presentation keys of a context taken from group data.
    Parameters: data — group data (a registry state, or decoded data without presentation keys).
    Options/defaults: None.
    Returns: <|"IrrepOrder", "IrrepLabels", "ClassLabels", "ClassOrder", "SourceInstanceID"|>; missing keys default to
        the canonical orders, no labels and no source instance.
    Effects: Pure.
    Failures: None.
    Example: contextPresentation[groupData[g]]["IrrepOrder"] === g["IrrepOrder"].
    See also: freezeContext; irrepOrder.
*)
contextPresentation[data_Association] := <|"IrrepOrder" -> Lookup[data, "IrrepOrder", data["CharacterData"]["IrrepIDs"]],
    "IrrepLabels" -> Lookup[data, "IrrepLabels", <||>], "ClassLabels" -> Lookup[data, "ClassLabels", <||>],
    "ClassOrder" -> Lookup[data, "ClassOrder", data["CharacterData"]["ClassIDs"]],
    "SourceInstanceID" -> Lookup[data, "InstanceID", None]|>;

freezeContext[group_Group] := Module[{data, snapshot, digest},
    data = groupData[group];
    If[FailureQ[data], Return[data]];
    If[!groupValidationReceiptQ[data, data["ValidationReceipt"]],
        Return[makeFailure["UnverifiedContext", "The group has no valid acceptance receipt."]]];
    snapshot = Join[contextSnapshot[data], contextPresentation[data]];
    digest = contextDigest[snapshot];
    registerContextBinding[digest, <|"Evidence" -> data["ValidationReceipt"], "GroupIdentity" -> data["StateID"]|>, contextStatusMap[snapshot]];
    RepresentationContext[snapshot]
];
freezeContext[___] := makeFailure["UnverifiedContext", "Expected a live accepted Group."];

(*
    Summary: Check one representation entry of a context snapshot against its accepted group.
    Parameters: rule — irrepID -> entry; data — context snapshot; accepted — the group's data.
    Options/defaults: None.
    Returns: True or False.
    Effects: Pure; recomputes each variant's realization identity and, with an assignment, whether
        its T matrix is diagonal.
    Failures: None (False) for wrong fields, altered matrices, unbound variants or properties,
        assignment properties inconsistent with the context's assignment, or invalid pointers.
    Example: every entry of First[RepresentationContext[g]] passes against g.
    See also: bindRepContext; representationVariantBinding; representationPointersQ.
*)
contextRepresentationEntryQ[id_ -> entry_, data_Association, accepted_Association] := Module[
    {names = data["GeneratorNames"], assignment = data["ModularAssignment"], variantQ},
    variantQ[variantID_, variant_] := AssociationQ[variant] &&
        (* "VerificationStatus" is optional (recorded statuses, methodOptionsPlan.md 2C.1) *)
        Sort[Keys[KeyDrop[variant, "VerificationStatus"]]] === Sort[{"Rep", "Identity", "Tier", "Arithmetic", "BasisProperties", "SourceMethod", "Scales", "NativeMatrices", "Derivation"}] &&
        (!KeyExistsQ[variant, "VerificationStatus"] || verificationStatusQ[variant["VerificationStatus"]]) &&
        (* never stronger than the accepted group's variant of that ID (review 2C-iii-a F1) *)
        With[{held = Lookup[Lookup[Lookup[accepted["Representations"], id, <||>], "Variants", <||>], variantID, Missing[]]},
            (* a variant the group does not hold may claim nothing above "Unverified" (review 2C-iii-a round 2) *)
            If[MissingQ[held], variantVerificationStatus[variant] === "Unverified",
                cgStatusRank[variantVerificationStatus[variant]] <= cgStatusRank[variantVerificationStatus[held]]]] &&
        AssociationQ[variant["BasisProperties"]] &&
        Sort[Keys[variant["BasisProperties"]]] === Sort[{"Unitary", "TDiagonal", "AssignmentIdentity"}] &&
        repIdentity[variant["Rep"], names] === variant["Identity"] &&
        Lookup[accepted["IdentityBindings"], identityDigest[{"Representation", accepted["StateID"], id, variantID}], None] ===
            identityDigest[representationVariantBinding[accepted["GeneratorIdentity"], id, variant]] &&
        If[MissingQ[assignment],
            MissingQ[variant["BasisProperties"]["TDiagonal"]] && MissingQ[variant["BasisProperties"]["AssignmentIdentity"]],
            variant["BasisProperties"]["AssignmentIdentity"] === assignment["Identity"] &&
                (* Native properties are exact recomputations; inert variants record T-diagonality only when
                   verified under this assignment (otherwise False), numerical ones within their tolerance. *)
                With[{t = wordMatrix[variant["Rep"], assignment["T"], names], recorded = variant["BasisProperties"]["TDiagonal"]},
                    If[MemberQ[{"Wolfram", "Numerical"}, variant["Tier"]],
                        BooleanQ[recorded] && (!recorded || MatrixQ[t] && If[variant["Tier"] === "Numerical",
                            Max[Abs[t - DiagonalMatrix[Diagonal[t]]]] <= 10^(-Floor[If[Precision[t] === MachinePrecision, 16, Precision[t]]/2]),
                            DiagonalMatrixQ[RootReduce[t]]]),
                        recorded === (MatrixQ[t] && DiagonalMatrixQ[t])]]];
    StringQ[id] && AssociationQ[entry] &&
        Sort[Keys[entry]] === Sort[{"CharacterID", "Dimension", "GeneratorIdentity", "Variants", "ActiveVariant", "AcceptedPartial"}] &&
        entry["CharacterID"] === id && entry["GeneratorIdentity"] === accepted["GeneratorIdentity"] &&
        AssociationQ[entry["Variants"]] && entry["Variants"] =!= <||> &&
        AllTrue[Normal[entry["Variants"]], variantQ[First[#], Last[#]] &] &&
        AllTrue[Values[entry["Variants"]], RepDim[#["Rep"]] === entry["Dimension"] &] &&
        representationPointersQ[entry["Variants"], entry["ActiveVariant"], entry["AcceptedPartial"]]
];
contextRepresentationEntryQ[___] := False;

(*
    Summary: Bind a copied or restored context snapshot to an independently accepted group.
    Parameters: data — context snapshot association; source — live accepted Group.
    Options/defaults: None.
    Returns: RepresentationContext[data] registered in this kernel, or UnverifiedContext Failure.
    Effects: Adds one $RepContextBindings entry with source's validation receipt as evidence.
    Failures: Missing/extra fields; a different group, generator, order, construction or character
        correspondence; an assignment never accepted for the group; representation data that the
        source cannot vouch for.
    Example: bindRepContext[First[RepresentationContext[g]], g] returns an equal registered context.
    Remarks: An older valid modular assignment is checked as that assignment: it must appear in the
        source's accumulated identity bindings, never replaced by the current assignment. Every
        representation variant in the snapshot must reproduce its realization identity from its
        matrices and have its binding (identity, tier, arithmetic, unitarity) in the source's history;
        assignment properties are recomputed and pointers checked (contextRepresentationEntryQ).
    See also: freezeContext; modularAssignmentBinding; resolveRepContext.
*)
bindRepContext[data_Association, source_Group] := Module[{accepted, assignment, binding, failure},
    failure[message_] := makeFailure["UnverifiedContext", message];
    accepted = groupData[source];
    If[FailureQ[accepted], Return[accepted]];
    If[!groupValidationReceiptQ[accepted, accepted["ValidationReceipt"]],
        Return[failure["The source group has no valid acceptance receipt."]]];
    If[Sort[Keys[KeyDrop[data, Append[$RepContextPresentationKeys, "VerificationStatus"]]]] =!= Sort[$RepContextFields],
        Return[failure["The context snapshot does not have the context fields."]]];
    (* a carried group status is never stronger than the accepted group's *)
    If[KeyExistsQ[data, "VerificationStatus"] && (!verificationStatusQ[data["VerificationStatus"]] ||
            cgStatusRank[data["VerificationStatus"]] > cgStatusRank[groupVerificationStatus[accepted]]),
        Return[failure["The context claims a stronger verification status than its group's."]]];
    (* a context saved with statuses stronger than the (weaker) loaded group's is refused, never lowered silently: the
       remedy is a group at those statuses (ImportGroupData[..., Verification -> "Exact"], or ValidateGroup /
       ValidateRepresentation on it; decision recorded in methodOptionsStatus.md 2C-iii-b) *)
    If[AssociationQ[data["Representations"]] && AnyTrue[Normal[data["Representations"]], Function[rule,
            With[{held = Lookup[Lookup[accepted["Representations"], First[rule], <||>], "Variants", <||>]},
                AssociationQ[Last[rule]] && AnyTrue[Normal[Lookup[Last[rule], "Variants", <||>]], Function[v,
                    KeyExistsQ[held, First[v]] && cgStatusRank[variantVerificationStatus[Last[v]]] > cgStatusRank[variantVerificationStatus[held[First[v]]]]]]]]],
        Return[failure["The context states stronger representation statuses than the loaded group holds; load the group at those statuses (ImportGroupData with Verification -> \"Exact\", or ValidateGroup / ValidateRepresentation) and rebind."]]];
    If[data["GroupIdentity"] =!= accepted["StateID"] || data["GeneratorIdentity"] =!= accepted["GeneratorIdentity"] ||
        data["GeneratorIDs"] =!= Lookup[accepted["Generators"], "ID", {}] ||
        data["GeneratorNames"] =!= Lookup[accepted["Generators"], "Name", {}] ||
        data["Order"] =!= accepted["Order"] ||
        canonicalJSON[data["Construction"]] =!= canonicalJSON[accepted["Construction"]] ||
        data["CharacterData"] =!= accepted["CharacterData"] ||
        !IntegerQ[data["StateGeneration"]] || !(0 <= data["StateGeneration"] <= accepted["StateGeneration"]),
        Return[failure["The context does not match the accepted group's correspondence."]]];
    assignment = data["ModularAssignment"];
    If[!(assignment === Missing["NotAssigned"] || assignment === accepted["ModularAssignment"]),
        binding = If[AssociationQ[assignment] && resultFieldsQ[assignment, {"Identity", "S", "T", "Verified"}] &&
            assignment["Verified"] === True,
            modularAssignmentBinding[accepted["StateID"], accepted["GeneratorIdentity"], assignment], None];
        If[binding === None || Lookup[accepted["IdentityBindings"], First[binding], None] =!= Last[binding],
            Return[failure["The context's modular assignment was never accepted for this group."]]]];
    (* Every representation variant of the snapshot must be one the group accepted: its matrices have
       the declared realization identity, its identity binding (state, irrep, variant) -> realization,
       tier, arithmetic and unitarity is in the group's accumulated bindings, its assignment properties
       hold for the context's assignment, and the entry's pointers are consistent. *)
    If[!AssociationQ[data["Representations"]] ||
        !AllTrue[Normal[data["Representations"]], contextRepresentationEntryQ[#, data, accepted] &],
        Return[failure["The context's representation data were never accepted for this group."]]];
    registerContextBinding[contextDigest[data], <|"Evidence" -> accepted["ValidationReceipt"], "GroupIdentity" -> accepted["StateID"]|>,
        contextStatusMap[data]];
    RepresentationContext[data]
];
bindRepContext[___] := makeFailure["UnverifiedContext", "Expected a context snapshot and a live accepted Group."];

(*
    Summary: Resolve a group or context to a verified immutable snapshot.
    Parameters: context — live Group, or RepresentationContext[data].
    Options/defaults: None.
    Returns: The snapshot association, or UnverifiedContext Failure.
    Effects: Freezing a Group registers its context binding.
    Failures: Unknown groups; unregistered, altered or forged snapshots; evidence receipts that no
        longer exist in this kernel.
    Example: resolveRepContext[RepresentationContext[g]]["GroupIdentity"] is g's state ID.
    Remarks: A copied valid context resolves; any change to its content changes its digest.
    See also: freezeContext; bindRepContext; SRep.
*)
resolveRepContext[group_Group] := With[{context = freezeContext[group]},
    If[FailureQ[context], context, First[context]]];
resolveRepContext[RepresentationContext[data_Association]] := Module[{binding},
    binding = Lookup[$RepContextBindings, contextDigest[data], None];
    If[AssociationQ[binding] && KeyExistsQ[$GroupValidationReceipts, binding["Evidence"]] &&
        Lookup[data, "GroupIdentity", None] === binding["GroupIdentity"] &&
        (* the statuses are outside the digest: a context never states more than was bound *)
        contextStatusesBoundQ[data, Lookup[binding, "Statuses", <||>]], data,
        makeFailure["UnverifiedContext", "The context is not bound to an accepted group in this kernel. Obtain it with RepresentationContext[group] or rebind it after importing the group."]]
];
resolveRepContext[___] := makeFailure["UnverifiedContext", "Expected a Group or a RepresentationContext."];

(*
    Summary: Immutable snapshot of an accepted group for representation work.
    Status: Alpha.
    Fields: GroupIdentity, GeneratorIdentity, GeneratorIDs, GeneratorNames, Order, Construction,
        StateGeneration, CharacterData, ModularAssignment and Representations of the group when frozen.
    Defaults: None.
    Returns: RepresentationContext[g] freezes live group g; RepresentationContext[data] is the inert
        value; context["Field"] reads a field, Missing["UnknownProperty", key] otherwise.
    Identity/mutation: Copies are equal values. Later group changes do not change a context. Only
        a snapshot bound in this kernel (frozen here or rebound after import) is accepted by
        group-aware operations; an altered association is not.
    Example: RepresentationContext[g]["GeneratorNames"] lists g's recorded generator names.
    See also: freezeContext; resolveRepContext; SRep; TRep.
*)
Unprotect[RepresentationContext];
RepresentationContext[group_Group] := freezeContext[group];
RepresentationContext[data_Association][key_String] := Lookup[data, key, Missing["UnknownProperty", key]];
RepresentationContext[input : Except[_Association | _Group]] :=
    makeFailure["InvalidContext", "RepresentationContext expects a live Group."];
RepresentationContext[_, __] := makeFailure["InvalidContext", "RepresentationContext expects one Group."];
RepresentationContext[] := makeFailure["InvalidContext", "RepresentationContext expects one Group."];
Protect[RepresentationContext];

(* -------------------------------------------------------------------------
   Modular accessors
   ------------------------------------------------------------------------- *)

(*
    Summary: Evaluate an assigned modular generator word on a Rep's matrices.
    Parameters: context — Group or RepresentationContext; rep — Rep on the group's recorded
        generators; role — "S" or "T".
    Options/defaults: None.
    Returns: The matrix of the assigned word, or Failure.
    Effects: Resolving a Group registers its context binding.
    Failures: UnverifiedContext, MissingModularAssignment, InvalidRep/SingularRep, and
        GeneratorBindingMismatch when the matrix count differs from the recorded generators.
    Example: for BuildModularGroup["24-3I"], SRep[g, r] is the matrix of the assigned word S.
    Remarks: The assigned word, not a generator position, selects the matrix. This evaluates the
        word on the supplied matrices; certifying r as a representation of the group is the job of
        representation validation.
    See also: SRep; TRep; wordMatrix; resolveRepContext.
*)
modularGeneratorMatrix[context_, rep_, role_String] := Module[{snapshot, assignment, shape},
    snapshot = resolveRepContext[context];
    If[FailureQ[snapshot], Return[snapshot]];
    assignment = snapshot["ModularAssignment"];
    If[!AssociationQ[assignment],
        Return[makeFailure["MissingModularAssignment", "The group has no modular S,T assignment. Use AssignModularGenerators first."]]];
    shape = validateRepShape[rep];
    If[FailureQ[shape], Return[shape]];
    If[shape["GeneratorCount"] =!= Length[snapshot["GeneratorNames"]],
        Return[makeFailure["GeneratorBindingMismatch", "The representation does not have one matrix per recorded generator.",
            <|"GeneratorCount" -> shape["GeneratorCount"], "GeneratorNames" -> snapshot["GeneratorNames"]|>]]];
    wordMatrix[rep, assignment[role], snapshot["GeneratorNames"]]
];

(*
    Summary: Matrices of the assigned modular generators S and T in a representation.
    Status: Alpha.
    Signatures: SRep[c, r]; TRep[c, r] with c a Group or RepresentationContext and r a Rep.
    Parameters: c — accepted group or bound context supplying the assignment; r — Rep with one
        matrix per recorded generator, in recorded order.
    Options/defaults: None.
    Returns: The matrix of the assigned S (or T) word, or Failure.
    Effects: Resolving a Group registers its context binding; no GAP work.
    Failures: See modularGeneratorMatrix. There is no positional fallback to the first two matrices.
    Example: SRep[BuildModularGroup["24-3I"], r] evaluates the word S.
    See also: modularGeneratorMatrix; AssignModularGenerators; RepresentationContext.
*)
SRep[context : (_Group | _RepresentationContext), rep_Rep] := modularGeneratorMatrix[context, rep, "S"];
TRep[context : (_Group | _RepresentationContext), rep_Rep] := modularGeneratorMatrix[context, rep, "T"];
SRep[___] := makeFailure["InvalidInput", "SRep expects a Group or RepresentationContext and a Rep."];
TRep[___] := makeFailure["InvalidInput", "TRep expects a Group or RepresentationContext and a Rep."];

True
