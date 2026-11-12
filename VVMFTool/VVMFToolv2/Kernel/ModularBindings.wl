(*
    :Title: Binding actual modular forms to formal slots
    :Context: VVMFTool`Private`
    :Summary: Frozen snapshots of Stage 7 forms bound to formal slots of a modular model (D-S8-8): exact context,
        assignment, basis, representation and weight correspondence, resolved coefficients, Stage 7 validation evidence
        kept (never upgraded), independence of the bound copies of each space by q-coefficient rank with a Sturm bound for
        proved relations (D-S8-10), atomic merging and explicit replacement.
    :Responsibilities: snapshotFormBinding, validateFormBinding, sturmOrder, qCoefficientRows, checkBoundSpaceIndependence,
        mergeFormBindings, suppliedSpaceRecord, suppliedSpaceRecordQ; BindModularForms, ModularFormBindings, SupplyModularFormSpace.
    :Dependencies: ModularFormObjects.wl (snapshotForm); ModularOperations.wl (expandForm, expansionBinding);
        ModularEvaluation.wl (ValidateModularForm); ModularCandidates.wl (slot records).
    :See Also: VVMFArch/step8Plan.md (binding actual forms); D-S8-8, D-S8-10.
*)

(*
    Summary: The frozen binding record of a form for a slot.
    Parameters: slot — slot record; record — the form's current Stage 7 record (a snapshot); validation — Stage 7 report.
    Options/defaults: None.
    Returns: <|"SlotID", "SpaceID", "FormID", "Revision", "Record" (the whole frozen record), "Validation" (ProofStatus, the
        complete Stage 7 checks with their residuals, orders and points, and remedies), "Kind" (definition kind)|>.
    Effects: Pure.
    Failures: None.
    Example: snapshotFormBinding[slot, ModularFormData[y], report]["Revision"] is y's revision at binding time.
    Remarks: The record is a value: later updates of the source form (coefficients, expansions) never reach the binding.
    See also: BindModularForms.
*)
snapshotFormBinding[slot_Association, record_Association, validation_Association] := <|"SlotID" -> slot["ID"], "SpaceID" -> slot["SpaceID"], "FormID" -> record["ID"],
    "Revision" -> record["Revision"], "Record" -> record, "Kind" -> record["Definition"]["Kind"],
    "Validation" -> <|"ProofStatus" -> validation["ProofStatus"], "Checks" -> validation["Checks"], "Remedies" -> Lookup[validation, "Remedies", {}]|>|>;

(*
    Summary: Check that a form record can occupy a slot.
    Parameters: slot — slot record; record — the form's record; options — validated binding options.
    Options/defaults: SeriesOrder (an explicit order is required for a finite jet).
    Returns: True, or Failure.
    Effects: Extends series caches (the exact terms below q^1 are expanded for the holomorphy check).
    Failures: IncompatibleBinding (group or generator identity, assignment identity, basis identity, representation
        matrices, weight or dimension differ; an equal abstract group, dimension or spectrum is not enough);
        UnresolvedCoefficients;
        FiniteJet (a finite jet without an explicit SeriesOrder); NotHolomorphicAtCusp (a negative q exponent).
    Example: the weight-2 T' triplet from ConstructModularForms on the model's context fits the weight-2 triplet slot.
    Remarks: For another basis, use ChangeModularFormBasis first and bind the result (its Rep is then checked exactly).
    See also: BindModularForms.
*)
validateFormBinding[slot_Association, record_Association, options_Association] := Module[{mismatch},
    (* The mathematical correspondence (group, generators, assignment, basis, matrices, weight) is required exactly; the
       context's state generation is bookkeeping (CG work advances it without changing any of these), as for Stage 5
       models (modelContextForGroup). *)
    mismatch = Select[{"GroupIdentity" -> record["GroupIdentity"] === slot["GroupIdentity"], "GeneratorIdentity" -> record["GeneratorIdentity"] === slot["GeneratorIdentity"],
        "AssignmentID" -> record["AssignmentID"] === slot["AssignmentID"],
        "BasisID" -> record["BasisID"] === slot["BasisID"], "Rep" -> record["Rep"] === slot["Rep"], "Weight" -> record["Weight"] === slot["Weight"],
        "Dimension" -> record["Dimension"] === slot["Dimension"]}, !Last[#] &];
    If[mismatch =!= {}, Return[makeFailure["IncompatibleBinding", "The form does not match the slot's context, assignment, basis, representation or weight.",
        <|"SlotID" -> slot["ID"], "Mismatch" -> Keys[mismatch]|>]]];
    If[MissingQ[expansionBinding[record, True]] || expansionBinding[record, True] === "Raw",
        Return[makeFailure["UnresolvedCoefficients", "A bound form needs resolved coefficients (or none); use ModularFormGetCoeff first.", <|"SlotID" -> slot["ID"]|>]]];
    If[record["Definition"]["Kind"] === "Jet" && options[SeriesOrder] === Automatic,
        Return[makeFailure["FiniteJet", "A finite jet can be bound only with an explicit SeriesOrder (its data have no tail).", <|"SlotID" -> slot["ID"]|>]]];
    (* Slots are holomorphic form spaces: a component with a negative q exponent (a pole at the cusp) does not belong to
       M_k(rho), and the Sturm argument of the independence check presupposes holomorphy. The terms below q^1 are exact. *)
    With[{low = expandForm[record, 1, True]}, Which[
        FailureQ[low], Return[low],
        AnyTrue[qExpansionJets[First[low]], AnyTrue[Keys[#["Terms"]], Negative] &],
            Return[makeFailure["NotHolomorphicAtCusp", "The form has a negative q exponent (a pole at the cusp); slots hold holomorphic modular forms.", <|"SlotID" -> slot["ID"]|>]]]];
    True
];

(*
    Summary: A q-order beyond which a linear relation among forms of one space is proved (Sturm bound).
    Parameters: model — modular model data; weight — kY.
    Options/defaults: None.
    Returns: Integer Floor[k |G| / 12] + 1 (at least 1).
    Effects: Pure.
    Failures: None.
    Example: the T' weight-2 triplet space gives 5.
    Remarks: Each component of a form of rho is a weight-k form for ker rho, whose index in SL(2, Z) is the order |G| of
        the image (S and T generate G); a form for a finite-index subgroup with ord_q above k [SL(2, Z) : Gamma] / 12 is zero
        (measuring in q instead of the cusp parameter q^(1/h) only enlarges the bound), so vanishing coefficients below
        this order prove a relation (D-S8-10). Rational k (a cover of SL(2, Z), fractionalWeightPlan.md): let K be the
        kernel of rho composed with the map from the cover B = <S, T | S^2 central, (ST)^3 = S^4> onto G, and Gamma its
        image in SL(2, Z) (index at most |G|). On K the automorphy factor of a component with k = a/b differs from an
        honest weight-k factor at most by a multiplier phase that is a 2b-th root of unity, so the 2b-th power of a
        component is a form of integer weight 2a for Gamma; its order at the cusp is 2b times the component's, so the same
        bound k |G| / 12 holds.
    See also: checkBoundSpaceIndependence.
*)
sturmOrder[model_Association, weight_?modularWeightQ] := Max[1, Floor[Max[weight, 0] First[model["Context"]]["Order"]/12] + 1];

(*
    Summary: The q-coefficient rows of bound forms through an order.
    Parameters: records — form records; order — positive integer.
    Options/defaults: None.
    Returns: Matrix (one row per record: every component's coefficients at every exponent below the order, on a common
        exponent grid), or Failure.
    Effects: Extends series caches (temporary expansions; no record changes).
    Failures: expandForm failures (InsufficientOrder for a finite jet beyond its data).
    Example: two equal forms give two equal rows.
    See also: checkBoundSpaceIndependence.
*)
qCoefficientRows[records_List, order_Integer] := Module[{expansions, grid},
    expansions = Map[expandForm[#, order, True] &, records];
    If[AnyTrue[expansions, FailureQ], Return[FirstCase[expansions, _Failure]]];
    expansions = Map[qExpansionJets[First[#]] &, expansions];
    grid = Table[Union[Flatten[Map[Keys[#[[i]]["Terms"]] &, expansions]]], {i, Length[First[expansions]]}];
    Map[Function[jets, Flatten[Table[Lookup[jets[[i]]["Terms"], grid[[i]], 0], {i, Length[jets]}]]], expansions]
];

(*
    Summary: Independence evidence for the bound copies of one formal space.
    Parameters: model — modular model data; slots — slot records of one space; bindings — <|slotID -> binding|> for them;
        options — validated options (SeriesOrder, WorkingPrecision).
    Options/defaults: SeriesOrder Automatic (orders 4, 8, ... up to the Sturm order) or an explicit order.
    Returns: <|"SpaceID", "Bound", "SpaceDimension", "Coverage" ("Full" | "Partial"), "Status" ("Independent",
        "NumericallyIndependent"), "Method", "Order"|>, or Failure.
    Effects: Temporary expansions.
    Failures: DependentFormBindings (the same form twice, or an exact relation through the Sturm order, or a numerical rank
        clearly below the count); AmbiguousIndependence (numerical rank without a clear gap); expansion failures.
    Example: E4^3 and Delta bound to the two weight-12 trivial slots are independent at order 2.
    Remarks: Exact coefficients: a nonzero rank minor proves independence of the supplied series, conditional on their
        recorded membership evidence; exact deficiency through the Sturm order proves a relation. Numerical coefficients
        give numerical evidence only: relative singular values all 100 times above the tolerance 10^-(WorkingPrecision/2)
        mean independence; at the Sturm order, values 100 times below it with none near it mean a numerical relation;
        anything else is ambiguous. A finite jet is compared only within its explicit
        order. Full coverage means the established dimension is bound with independent members (D-S8-10).
    See also: sturmOrder; mergeFormBindings.
*)
checkBoundSpaceIndependence[model_Association, slots_List, bindings_Association, options_Association] := Module[{records, ids = Lookup[slots, "ID", {}], space, sturm, orders, rows,
        rank, result = None, exact},
    records = Lookup[Lookup[bindings, ids], "Record"];
    space = First[slots];
    If[!DuplicateFreeQ[Lookup[records, "ID"]], Return[makeFailure["DependentFormBindings", "The same form is bound to two slots of one space.", <|"SpaceID" -> space["SpaceID"]|>]]];
    sturm = sturmOrder[model, space["Weight"]];
    orders = If[IntegerQ[options[SeriesOrder]], {options[SeriesOrder]}, Union[Append[Select[2^Range[2, 10], # < sturm &], sturm]]];
    Do[rows = qCoefficientRows[records, n]; If[FailureQ[rows], Return[rows, Module]];
        exact = !inexactDataQ[rows];
        If[exact,
            rank = MatrixRank[rows];
            If[rank === Length[records], result = <|"Status" -> "Independent", "Method" -> "ExactQRank", "Order" -> n|>; Break[]],
            (* Numerical rows: relative singular values against a tolerance with a factor-100 gap on either side. *)
            With[{sv = SingularValueList[N[rows, options[WorkingPrecision]], Tolerance -> 0] / Max[10^-options[WorkingPrecision], Max[Abs[N[rows]]]],
                    tol = 10^-Floor[options[WorkingPrecision]/2]},
                rank = Count[sv, x_ /; x > tol];
                Which[
                    Length[sv] === Length[records] && Min[sv] > 100 tol, result = <|"Status" -> "NumericallyIndependent", "Method" -> "NumericalQRank", "Order" -> n|>; Break[],
                    n === Last[orders] && n >= sturm && Length[sv] === Length[records] && Min[sv] < tol/100 && Count[sv, x_ /; tol/100 <= x <= 100 tol] === 0,
                        result = makeFailure["DependentFormBindings", "The bound forms of one space satisfy a numerical linear relation through the Sturm order (numerical evidence).",
                            <|"SpaceID" -> space["SpaceID"], "Order" -> n, "SingularValues" -> N[sv, 5]|>]; Break[]]]],
        {n, orders}];
    If[FailureQ[result], Return[result]];
    If[result === None,
        Return[If[exact && Last[orders] >= sturm,
            makeFailure["DependentFormBindings", "The bound forms of one space satisfy a linear relation (exact through the Sturm order).",
                <|"SpaceID" -> space["SpaceID"], "Order" -> Last[orders], "Relation" -> NullSpace[Transpose[rows]]|>],
            makeFailure["AmbiguousIndependence", "Independence of the bound forms is not established at the available order or precision; raise SeriesOrder or WorkingPrecision.",
                <|"SpaceID" -> space["SpaceID"], "Order" -> Last[orders], "Rank" -> rank, "Count" -> Length[records]|>]]]];
    Join[<|"SpaceID" -> space["SpaceID"], "Bound" -> Length[records], "SpaceDimension" -> space["SpaceDimension"],
        "Coverage" -> If[Length[records] === space["SpaceDimension"], "Full", "Partial"]|>, result]
];

(*
    Summary: Merge new bindings into a model atomically.
    Parameters: model — modular model data; new — <|slotID -> binding|>; options — validated options (ReplaceBindings, ...).
    Options/defaults: ReplaceBindings False.
    Returns: Model data with the combined bindings and per-space independence evidence, or Failure (nothing changes).
    Effects: Temporary expansions.
    Failures: AlreadyBound (a bound slot without ReplaceBindings -> True); checkBoundSpaceIndependence failures.
    Example: binding the second weight-12 copy after the first checks both together.
    Remarks: The combined bound set of every affected space is checked again; a failure keeps the old model.
    See also: BindModularForms.
*)
mergeFormBindings[model_Association, new_Association, options_Association] := Module[{md = model["ModularData"], combined, spaces, evidence},
    If[!TrueQ[options[ReplaceBindings]] && IntersectingQ[Keys[md["Bindings"]], Keys[new]],
        Return[makeFailure["AlreadyBound", "A slot is already bound; use ReplaceBindings -> True to replace it.", <|"SlotIDs" -> Intersection[Keys[md["Bindings"]], Keys[new]]|>]]];
    combined = Join[md["Bindings"], new];
    spaces = DeleteDuplicates[Lookup[Lookup[md["Slots"], Keys[new]], "SpaceID"]];
    evidence = Map[Function[sid, With[{slots = Select[Values[md["Slots"]], #["SpaceID"] === sid && KeyExistsQ[combined, #["ID"]] &]},
        checkBoundSpaceIndependence[model, slots, KeyTake[combined, Lookup[slots, "ID"]], options]]], spaces];
    If[AnyTrue[evidence, FailureQ], Return[FirstCase[evidence, _Failure]]];
    Join[model, <|"ModularData" -> Join[md, <|"Bindings" -> combined,
        "BindingEvidence" -> Join[Lookup[md, "BindingEvidence", <||>], AssociationThread[spaces, evidence]]|>]|>]
];

Options[BindModularForms] = {ReplaceBindings -> False, RequireProof -> False, WorkingPrecision -> 40, SeriesOrder -> Automatic, TimeLimit -> 600,
    Verification -> Automatic};

(*
    Summary: Bind Stage 7 modular forms to formal slots of a modular model as frozen snapshots.
    Status: Alpha.
    Parameters: m — modular Model; bindings — association slot ID -> ModularForm.
    Options/defaults: ReplaceBindings -> False; RequireProof -> False (True: every bound form must validate Proven);
        WorkingPrecision -> 40, SeriesOrder -> Automatic (Stage 7 validation and the independence check); TimeLimit -> 600;
        Verification -> Automatic or "Numerical" (the Stage 7 validation of each form; "Exact" is InapplicableOption: the
        S/T evidence is sampled) or None (no Stage 7 validation: the binding records ProofStatus "Unchecked" and is
        "Unverified"; the exact correspondence, holomorphy and independence checks still run; RequireProof -> True with
        None is InapplicableOption).
    Returns: New Model with the bindings and their evidence, or Failure (the input model is unchanged).
    Effects: Stage 7 validation of each form, whose result ValidateModularForm records in the form's Validation "Status"
        (same revision); temporary expansions; no other form field, group or model is mutated.
    Failures: InvalidModel; NotModularModel; UnknownSlot (not a registered slot of the model) or repeated slots;
        IncompatibleBinding; UnresolvedCoefficients; FiniteJet; NotHolomorphicAtCusp; BindingValidationFailed (a form whose
        Stage 7 checks fail, or a form without a passed S/T check, finite jets included);
        ProofRequired; AlreadyBound; DependentFormBindings; AmbiguousIndependence; TimeLimit.
    Example: BindModularForms[m, <|slot -> y|>] for the weight-2 T' triplet y on the model's context.
    Remarks: The whole current record (definition, coefficients, representation, normalization frame, expansions, evidence)
        is frozen: later coefficient or expansion updates of y do not change the model; bind the new revision into a new
        model explicitly. Partial binding is allowed; unbound slots stay symbolic.
    See also: ModularFormBindings; ValidateModularModel; EvaluateModularModel.
*)
BindModularForms[m_Model, bindings_Association, options : OptionsPattern[]] := Module[{model = validateModelSchema[m], effective, md, new, merged},
    If[FailureQ[model], Return[model]];
    If[!KeyExistsQ[model, "ModularData"], Return[makeFailure["NotModularModel", "The model has no modular weights; create it with CreateModularModel."]]];
    effective = resolveOperationOptions[BindModularForms, "BindModularForms", {options}]; If[FailureQ[effective], Return[effective]];
    If[effective[Verification] === "Exact", Return[makeFailure["InapplicableOption",
        "BindModularForms has no exact validation route for forms (sampled S checks); use Automatic, \"Numerical\" or None.", <|"Options" -> {Verification}|>]]];
    If[effective[Verification] === None && TrueQ[effective[RequireProof]], Return[makeFailure["InapplicableOption",
        "RequireProof -> True needs the Stage 7 validation that Verification -> None skips.", <|"Options" -> {Verification, RequireProof}|>]]];
    md = model["ModularData"];
    If[!AllTrue[Keys[bindings], StringQ] || !SubsetQ[Keys[md["Slots"]], Keys[bindings]],
        Return[makeFailure["UnknownSlot", "Bind registered slots of the model (slots used by its terms).", <|"Unknown" -> Complement[Keys[bindings], Keys[md["Slots"]]]|>]]];
    If[!AllTrue[Values[bindings], MatchQ[#, _ModularForm] &], Return[makeFailure["InvalidInput", "Bind ModularForm objects."]]];
    new = TimeConstrained[Association[KeyValueMap[Function[{sid, form}, Module[{record = snapshotForm[form], check, report},
            If[FailureQ[record], Return[sid -> record, Module]];
            check = validateFormBinding[md["Slots"][sid], record, effective]; If[FailureQ[check], Return[sid -> check, Module]];
            (* the Stage 7 validation is the binding's result check (methodOptionsPlan.md 2C.4); None records it unchecked *)
            If[effective[Verification] === None,
                Return[sid -> snapshotFormBinding[md["Slots"][sid], record, <|"ProofStatus" -> "Unchecked", "Checks" -> <||>, "Remedies" -> {}|>], Module]];
            report = ValidateModularForm[form, WorkingPrecision -> effective[WorkingPrecision], SeriesOrder -> effective[SeriesOrder], RequireProof -> effective[RequireProof],
                Sequence @@ inheritedVerification[effective[Verification]]];
            Which[
                FailureQ[report], sid -> report,
                report["ProofStatus"] === "Failed", sid -> makeFailure["BindingValidationFailed", "The form fails an applicable Stage 7 check; it cannot be bound.",
                    <|"SlotID" -> sid, "Checks" -> Map[#["Status"] &, report["Checks"]]|>],
                (* Membership needs transformation evidence for every kind: the sampled S/T check must pass (a truncation-limited
                   or unavailable check is not evidence); a finite jet is sampled at its explicit order. *)
                !MemberQ[{"Numerical", "Proven"}, report["Checks"]["STransformation"]["Status"]],
                    sid -> makeFailure["BindingValidationFailed", "The form has no passed S/T transformation check; raise SeriesOrder or use SeriesOrder -> Automatic.",
                        <|"SlotID" -> sid, "STransformation" -> report["Checks"]["STransformation"], "Remedies" -> report["Remedies"]|>],
                snapshotForm[form]["Revision"] =!= record["Revision"], sid -> makeFailure["RevisionConflict", "The form changed during binding; bind it again.", <|"SlotID" -> sid|>],
                True, sid -> snapshotFormBinding[md["Slots"][sid], record, report]]]], bindings]],
        effective[TimeLimit], makeFailure["TimeLimit", "Binding did not finish within TimeLimit."]];
    If[FailureQ[new], Return[new]];
    If[AnyTrue[new, FailureQ], Return[FirstCase[Values[new], _Failure]]];
    merged = mergeFormBindings[model, new, effective];
    If[FailureQ[merged], merged, Model[merged]]
];
BindModularForms[___] := makeFailure["InvalidInput", "BindModularForms expects a modular Model, an association of slot IDs to ModularForm objects and options."];

(*
    Summary: The stored record of a supplied form space.
    Parameters: space — formal space record (Stage 7 status Unknown); records — the supplying form records; evidence —
        checkBoundSpaceIndependence result.
    Options/defaults: None.
    Returns: <|"IrrepID", "Weight", "Dimension", "Forms" -> {<|"FormID", "Revision"|>...}, "Independence" -> <|"Status",
        "Method", "Order"|>|>.
    Effects: Pure.
    Failures: None.
    Example: one eta form on Z_24 gives Dimension 1.
    See also: SupplyModularFormSpace; makeFormalSpace.
*)
suppliedSpaceRecord[space_Association, records_List, evidence_Association] := <|"IrrepID" -> space["IrrepID"], "Weight" -> space["Weight"],
    "Dimension" -> Length[records], "Forms" -> Map[<|"FormID" -> #["ID"], "Revision" -> #["Revision"]|> &, records],
    "Independence" -> KeyTake[evidence, {"Status", "Method", "Order"}]|>;

(*
    Summary: Whether a stored supplied-space record is well formed for its space ID in a model.
    Parameters: model — modular model data; id — the record's key; record — any expression.
    Options/defaults: None.
    Returns: True or False.
    Effects: Pure.
    Failures: None.
    Example: a record whose Dimension differs from the number of its Forms is rejected.
    Remarks: The record is the user's spanning claim with the evidence checked when it was supplied: an irrep of the
        model's context, an exact rational weight, Dimension equal to the number of distinct supplying forms (FormID,
        Revision) and an independence result; the key must recompute from the irrep and weight. Archives carry it as that
        claim (the forms themselves are not archived, so the independence is not recomputed on import).
    See also: suppliedSpaceRecord; validateModularModelData.
*)
suppliedSpaceRecordQ[model_Association, id_, r_] := AssociationQ[r] && Sort[Keys[r]] === Sort[{"IrrepID", "Weight", "Dimension", "Forms", "Independence"}] &&
    StringQ[r["IrrepID"]] && MemberQ[First[model["Context"]]["CharacterData"]["IrrepIDs"], r["IrrepID"]] && modularWeightQ[r["Weight"]] &&
    IntegerQ[r["Dimension"]] && r["Dimension"] >= 1 && ListQ[r["Forms"]] && Length[r["Forms"]] === r["Dimension"] &&
    AllTrue[r["Forms"], AssociationQ[#] && Sort[Keys[#]] === {"FormID", "Revision"} && StringQ[#["FormID"]] && IntegerQ[#["Revision"]] && #["Revision"] >= 1 &] &&
    DuplicateFreeQ[Lookup[r["Forms"], "FormID"]] && AssociationQ[r["Independence"]] && Sort[Keys[r["Independence"]]] === {"Method", "Order", "Status"} &&
    MemberQ[{"Independent", "NumericallyIndependent"}, r["Independence"]["Status"]] && StringQ[r["Independence"]["Method"]] &&
    IntegerQ[r["Independence"]["Order"]] && r["Independence"]["Order"] >= 1 && id === spaceRecordID[spaceKey[model, r["IrrepID"], r["Weight"]]];

Options[SupplyModularFormSpace] = {WorkingPrecision -> 40, SeriesOrder -> Automatic, TimeLimit -> 600};

(*
    Summary: Establish a form space that Stage 7 cannot count from forms the user supplies.
    Status: Alpha.
    Parameters: m — modular Model; forms — nonempty list of ModularForm objects of one irrep and one weight.
    Options/defaults: WorkingPrecision -> 40, SeriesOrder -> Automatic (Stage 7 validation and the independence check);
        TimeLimit -> 600.
    Returns: New Model whose space of that irrep and weight has Status "Supplied" and dimension Length[forms], so it
        gives slots (ModularFormCandidates, ModularContractions); or Failure (the input model is unchanged).
    Effects: Stage 7 validation of each form (ValidateModularForm records its result in the form's Validation "Status",
        same revision); temporary expansions.
    Failures: InvalidModel; NotModularModel; InvalidInput; IncompatibleBinding (another group, assignment, basis,
        representation or weight than the model's context); MixedFormSpace (several irreps or weights);
        EstablishedSpace (Stage 7 knows the dimension: bind forms to its slots instead); SupplyFailed (the Stage 7 count
        failed); MissingRepresentations; UnresolvedCoefficients; FiniteJet; NotHolomorphicAtCusp; BindingValidationFailed;
        DependentFormBindings; AmbiguousIndependence; SuppliedSpaceInUse (the model already has slots of a supplied space
        of this irrep and weight); TimeLimit.
    Example: SupplyModularFormSpace[m, {eta}] on the cover Z_24 (eta of weight 1/2) gives the slot of the eta irrep at
        weight 1/2.
    Remarks: For a rational weight on a cover of SL(2, Z) no dimension formula is implemented (Missing["UnknownDimension"]);
        the supplied forms are the user's statement that they span the space. The package checks what it can (exact
        compatibility, holomorphy at the cusp, a passed S/T check, independence by q-coefficient rank) but never the
        spanning claim, so a model that uses a supplied space is never Proven, and "Complete"/"Exhaustive" results that
        include a supplied space are conditional on that claim. The forms are not bound: bind them (or other forms) with
        BindModularForms. If Stage 7 later counts the space, the count wins: the supplied record is ignored, and slots of a
        different dimension make the model invalid (fail closed).
    See also: BindModularForms; ModularFormCandidates; makeFormalSpace.
*)
SupplyModularFormSpace[m_Model, forms : {__ModularForm}, options : OptionsPattern[]] := Module[{model = validateModelSchema[m], effective, md, records, space, slots,
        checked, evidence, supplied},
    If[FailureQ[model], Return[model]];
    If[!KeyExistsQ[model, "ModularData"], Return[makeFailure["NotModularModel", "The model has no modular weights; create it with CreateModularModel."]]];
    effective = resolveOperationOptions[SupplyModularFormSpace, "SupplyModularFormSpace", {options}]; If[FailureQ[effective], Return[effective]];
    md = model["ModularData"];
    records = Map[snapshotForm, forms]; If[AnyTrue[records, FailureQ], Return[FirstCase[records, _Failure]]];
    If[!DuplicateFreeQ[Lookup[records, "ID"]], Return[makeFailure["DependentFormBindings", "The same form is supplied twice."]]];
    If[Length[DeleteDuplicates[Lookup[records, {"IrrepID", "Weight"}]]] =!= 1 || !StringQ[First[records]["IrrepID"]],
        Return[makeFailure["MixedFormSpace", "Supply forms of one irrep and one weight.", <|"Spaces" -> DeleteDuplicates[Lookup[records, {"IrrepID", "Weight"}]]|>]]];
    If[!MemberQ[First[model["Context"]]["CharacterData"]["IrrepIDs"], First[records]["IrrepID"]],
        Return[makeFailure["IncompatibleBinding", "The forms belong to another group context than the model.", <|"IrrepID" -> First[records]["IrrepID"]|>]]];
    (* the Stage 7 status, ignoring an earlier supply of this space *)
    space = makeFormalSpace[model, First[records]["IrrepID"], First[records]["Weight"], True, False];
    Switch[space["Status"],
        "Known", Return[makeFailure["EstablishedSpace", "Stage 7 establishes the dimension of this space; bind forms to its slots instead.",
            <|"IrrepID" -> space["IrrepID"], "Weight" -> space["Weight"], "Dimension" -> space["Dimension"]|>]],
        "Failed", Return[makeFailure["SupplyFailed", "The Stage 7 count of this space failed.", <|"Evidence" -> space["Evidence"]|>]]];
    If[AnyTrue[Values[md["Slots"]], #["SpaceID"] === space["ID"] &],
        Return[makeFailure["SuppliedSpaceInUse", "The model already has slots of this supplied space; supply it in a new model.", <|"SpaceID" -> space["ID"]|>]]];
    space = Join[space, <|"Status" -> "Supplied", "Dimension" -> Length[records]|>];
    slots = Table[makeSlotRecord[model, space, i], {i, Length[records]}]; If[AnyTrue[slots, FailureQ], Return[FirstCase[slots, _Failure]]];
    checked = TimeConstrained[MapThread[Function[{slot, record, form}, Module[{check, report},
            check = validateFormBinding[slot, record, effective]; If[FailureQ[check], Return[check, Module]];
            report = ValidateModularForm[form, WorkingPrecision -> effective[WorkingPrecision], SeriesOrder -> effective[SeriesOrder],
                (* SupplyModularFormSpace has no level of its own: the check resolves its own (session) defaults *)
                Sequence @@ inheritedVerification[Automatic]];
            Which[
                FailureQ[report], report,
                report["ProofStatus"] === "Failed" || !MemberQ[{"Numerical", "Proven"}, report["Checks"]["STransformation"]["Status"]],
                    makeFailure["BindingValidationFailed", "A supplied form has no passed S/T transformation check.", <|"FormID" -> record["ID"],
                        "Checks" -> Map[#["Status"] &, report["Checks"]]|>],
                True, True]]], {slots, records, forms}], effective[TimeLimit], makeFailure["TimeLimit", "Supplying the space did not finish within TimeLimit."]];
    If[FailureQ[checked], Return[checked]];
    If[AnyTrue[checked, FailureQ], Return[FirstCase[checked, _Failure]]];
    evidence = checkBoundSpaceIndependence[model, slots, AssociationThread[Lookup[slots, "ID"], Map[<|"Record" -> #|> &, records]], effective];
    If[FailureQ[evidence], Return[evidence]];
    supplied = Join[Lookup[md, "SuppliedSpaces", <||>], <|space["ID"] -> suppliedSpaceRecord[space, records, evidence]|>];
    model["ModularData"] = Join[md, <|"SuppliedSpaces" -> supplied|>];
    With[{v = validateModularModelData[model]}, If[FailureQ[v], v, Model[v]]]
];
SupplyModularFormSpace[___] := makeFailure["InvalidInput", "SupplyModularFormSpace expects a modular Model, a nonempty list of ModularForm objects of one irrep and weight, and options."];

(*
    Summary: The frozen bindings of a modular model.
    Status: Alpha.
    Parameters: m — modular Model.
    Options/defaults: None.
    Returns: Association slot ID -> binding record (SlotID, SpaceID, FormID, Revision, Record, Kind, Validation), or Failure.
    Effects: Pure.
    Failures: InvalidModel; NotModularModel.
    Example: ModularFormBindings[mb] === oldBinding after the source form gets a longer expansion.
    See also: BindModularForms.
*)
ModularFormBindings[m_Model] := Module[{model = validateModelSchema[m]},
    If[FailureQ[model], Return[model]];
    If[!KeyExistsQ[model, "ModularData"], Return[makeFailure["NotModularModel", "The model has no modular weights; create it with CreateModularModel."]]];
    model["ModularData"]["Bindings"]
];
ModularFormBindings[___] := makeFailure["InvalidInput", "ModularFormBindings expects a modular Model."];

True
