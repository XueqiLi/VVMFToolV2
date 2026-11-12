(*
    :Title: Expansions, derivatives and basis changes of modular forms
    :Context: VVMFTool`Private`
    :Summary: The stored q-expansion property (atomic, binding-aware, never shortened), the modular derivative as a new
        form from a frozen source recipe, and the basis change F_new = b . F_old, rho_new = b rho b^-1 as a new form with
        the anchor's frame transported and no rescaling.
    :Responsibilities: recordContextData, expansionBinding, expandForm, derivedComponentJets, differentiateFormData,
        transformDefinition, changeFormBasisData; ModularFormQExp, ModularFormDerivative, ChangeModularFormBasis.
    :Dependencies: ModularNormalization.wl (formComponentJets); ModularScalars.wl (differentiateScalarRecipe);
        ModularConstructors.wl (modularDerivativeJet); ModularFormObjects.wl (records).
    :See Also: VVMFArch/step7Plan.md (derivative, basis change, expansions); D-S7-2, D-S7-4.
*)

(*
    Summary: The context data of an existing form record (its own Rep, not a group lookup).
    Parameters: record — form record; rep — Rep (default the record's).
    Options/defaults: None.
    Returns: formContextData-shaped association, or Failure.
    Effects: Resolves the frozen context binding.
    Failures: UnverifiedContext; GeneratorBindingMismatch.
    Example: recordContextData[record]["Dimension"] is the form's dimension.
    See also: differentiateFormData; changeFormBasisData.
*)
recordContextData[record_Association, rep_ : Automatic] := Module[{r = Replace[rep, Automatic -> record["Rep"]], snapshot, s, t},
    snapshot = resolveRepContext[record["Context"]]; If[FailureQ[snapshot], Return[snapshot]];
    s = modularGeneratorMatrix[record["Context"], r, "S"]; If[FailureQ[s], Return[s]];
    t = modularGeneratorMatrix[record["Context"], r, "T"]; If[FailureQ[t], Return[t]];
    <|"Context" -> record["Context"], "Snapshot" -> snapshot, "IrrepID" -> record["IrrepID"], "Rep" -> r, "BasisID" -> record["BasisID"], "Dimension" -> Length[s],
        "Arithmetic" -> If[inexactDataQ[repMatrices[r]], "Numerical", "Exact"], "S" -> s, "T" -> t, "Assignment" -> snapshot["ModularAssignment"]|>
];

(*
    Summary: The coefficient binding of an expansion and the expansion itself.
    Parameters: record — form record; cutoff — exact rational; apply — ApplyCoefficients.
    Options/defaults: None.
    Returns: expansionBinding: "Fixed" (no unknowns), "Raw" (unknowns kept), or "Rules-" digest of the resolved rules.
        expandForm: QExpansionData in the stored basis with that binding and the record's revision/basis/assignment as
        source, or Failure.
    Effects: Extends series caches.
    Failures: UnresolvedCoefficients (apply True, unknowns not resolved: no coefficient is set to 1); series failures.
    Example: expandForm[e4record, 4, True] is 1 + 240 q + 2160 q^2 + 6720 q^3 + O(q^4).
    See also: ModularFormQExp; formComponentJets.
*)
expansionBinding[record_Association, apply_] := Module[{ids = Lookup[record["Definition"]["Parameters"], "ID", {}], rules},
    rules = Lookup[Replace[record["Coefficients"], _Missing -> <||>], "Rules", Missing[]];
    Which[ids === {}, "Fixed", !TrueQ[apply], "Raw", ListQ[rules], "Rules-" <> Hash[rules, "SHA256", "HexString"], True, Missing["UnresolvedCoefficients", ids]]];
expandForm[record_Association, cutoff_, apply_] := Module[{binding = expansionBinding[record, apply], jets, rules},
    If[MissingQ[binding], Return[makeFailure["UnresolvedCoefficients", "The form's relative coefficients are not resolved; use ModularFormGetCoeff or ApplyCoefficients -> False.",
        <|"Parameters" -> Last[binding]|>]]];
    jets = formComponentJets[record["Definition"], cutoff]; If[FailureQ[jets], Return[jets]];
    rules = If[StringStartsQ[binding, "Rules-"], Map[FormParameter[First[#]] -> Last[#] &, record["Coefficients"]["Rules"]], {}];
    makeQExpansion[Map[makeJet[Map[Expand[# /. rules] &, #["Terms"]], #["Cutoff"]] &, jets],
        <|"Binding" -> binding, "Source" -> <|"Revision" -> record["Revision"], "BasisID" -> record["BasisID"], "AssignmentID" -> record["AssignmentID"]|>|>]
];

Options[ModularFormQExp] = {ApplyCoefficients -> True};

(*
    Summary: Compute and store the q-expansion of a form.
    Status: Alpha.
    Parameters: y — ModularForm; n — nonnegative integer order (default 5): exponents below n are kept.
    Options/defaults: ApplyCoefficients -> True (False expands the raw parameterized definition).
    Returns: y (the same object) after an atomic update of its QExpansion property, or Failure (nothing changed).
    Effects: One registry commit; aliases see it. A stored expansion with the same binding that already covers n is
        reused, and a longer one is never shortened.
    Failures: UnresolvedCoefficients; InsufficientOrder (a finite jet); series failures; RevisionConflict; option
        failures.
    Example: ModularFormQExp[y, 8]; QExpansionExpression[y["QExpansion"], q].
    Remarks: The update never changes weight, representation, definition, value, normalization or identity.
    See also: expandForm; QExpansionExpression.
*)
ModularFormQExp[y_ModularForm, n : (_Integer?NonNegative) : 5, options : OptionsPattern[]] := Module[{effective, record, binding, stored, qexp},
    effective = resolveOperationOptions[ModularFormQExp, "ModularFormQExp", {options}]; If[FailureQ[effective], Return[effective]];
    record = snapshotForm[y]; If[FailureQ[record], Return[record]];
    binding = expansionBinding[record, effective[ApplyCoefficients]];
    stored = record["QExpansion"];
    If[MatchQ[stored, _QExpansionData] && stored["Binding"] === binding && stored["Cutoff"] >= n, Return[y]];
    qexp = expandForm[record, n, effective[ApplyCoefficients]]; If[FailureQ[qexp], Return[qexp]];
    With[{committed = commitFormUpdate[record["ID"], record["Revision"], <|"QExpansion" -> qexp|>]}, If[FailureQ[committed], committed, y]]
];
ModularFormQExp[___] := makeFailure["InvalidInput", "ModularFormQExp expects a ModularForm, a nonnegative integer order and options."];

(*
    Summary: The component series of a derived (modular-derivative) definition.
    Parameters: definition — Kind "Derived" data (Recipe: Source definition, SourceWeight); cutoff.
    Options/defaults: None.
    Returns: List of jets D_k F_source (stored basis), or Failure.
    Effects: Extends series caches.
    Failures: As formComponentJets of the source (a finite source jet gives a finite derivative jet).
    Example: the derivative of the trivial form 1 is the zero vector.
    See also: differentiateFormData.
*)
derivedComponentJets[definition_Association, cutoff_] := Module[{recipe = definition["Recipe"], source},
    source = formComponentJets[recipe["Source"], cutoff]; If[FailureQ[source], Return[source]];
    Map[jetTruncate[modularDerivativeJet[#, recipe["SourceWeight"], cutoff], cutoff] &, source]];

(*
    Summary: The data of the modular derivative of a form record.
    Parameters: record — source form record.
    Options/defaults: None.
    Returns: <|"Definition", "Weight", "Coefficients"|> of the derived form, or Failure.
    Effects: Pure.
    Failures: Derivative failures of analytic trees.
    Example: an analytic form gives an analytic definition (D_k applied to the trees); an MLDE or jet form gives a
        "Derived" definition freezing the complete source definition.
    Remarks: The derived form keeps the source's unknowns and their binding: resolved rules carry over; unresolved ones
        are later solved on the frozen source recipe with its anchor (never by choosing a scale for a possibly zero
        derivative).
    See also: ModularFormDerivative.
*)
differentiateFormData[record_Association] := Module[{def = record["Definition"], k = record["Weight"], trees, definition},
    definition = If[def["Kind"] === "Analytic" && !KeyExistsQ[def, "Transform"],
        trees = Map[differentiateScalarRecipe[#, def["Coordinate"]] &, def["Components"]];
        If[AnyTrue[trees, FailureQ], Return[FirstCase[trees, _Failure]]];
        Join[def, <|"DefinitionID" -> "definition-" <> CreateUUID[],
            "Components" -> MapThread[Expand[#1 - k ModularScalarNode["E2", FormVariable[def["Coordinate"]], def["Coordinate"]] #2/12] &, {trees, def["Components"]}]|>],
        <|"SchemaVersion" -> 1, "DefinitionID" -> "definition-" <> CreateUUID[], "Kind" -> "Derived", "Coordinate" -> "q", "VariableLabel" -> def["VariableLabel"],
            "Components" -> If[ListQ[def["Components"]], Map[ModularDerivativeNode[k, #] &, def["Components"]], Missing["DerivedRecipe"]],
            "Dimension" -> def["Dimension"], "Parameters" -> def["Parameters"], "FamilyID" -> def["FamilyID"], "Jet" -> Missing["NotAJet"],
            "Recipe" -> <|"Source" -> def, "SourceWeight" -> k|>|>];
    <|"Definition" -> definition, "Weight" -> k + 2,
        "Coefficients" -> If[MissingQ[record["Coefficients"]], Missing["Unresolved"],
            (* The anchor stays stated on the root: the normalization source of the source (a derivative's own root, the
               companion F of a coupled G, or the source itself), never on the immediate source. *)
            With[{root = normalizationSource[record, record["Coefficients"]]},
                Join[record["Coefficients"], <|"DerivedSource" -> <|"Definition" -> First[root], "Weight" -> Last[root]|>|>]]]|>
];

(*
    Summary: The modular derivative of a form as a new form.
    Status: Alpha.
    Parameters: y — ModularForm.
    Options/defaults: None.
    Returns: A new ModularForm of weight k + 2 with the same representation and realization, or Failure.
    Effects: Registers the new form; y is unchanged.
    Failures: UnknownModularForm; derivative failures; record failures.
    Example: ModularFormWeight[ModularFormDerivative[y]] == ModularFormWeight[y] + 2.
    Remarks: D_k = q d/dq - k E2/12 componentwise; a provably zero derivative is a valid zero form. The source recipe and
        its coefficient binding are frozen into the new definition (no live pointer); an extendible source stays
        extendible.
    See also: differentiateFormData; ModularDerivativeExpression.
*)
ModularFormDerivative[y_ModularForm] := Module[{record = snapshotForm[y], data, ctx, new},
    If[FailureQ[record], Return[record]];
    data = differentiateFormData[record]; If[FailureQ[data], Return[data]];
    ctx = recordContextData[record]; If[FailureQ[ctx], Return[ctx]];
    new = makeFormRecord[ctx, data["Weight"], data["Definition"], <|"Method" -> "Derivative", "Coefficients" -> data["Coefficients"],
        (* D_k maps weight-k forms to weight k + 2 exactly, so the source's recipe evidence carries over with the derivation. *)
        (* a derived form is validated on its own: the source's recorded result (2C-iii) is not carried *)
        "Validation" -> Join[<|"Status" -> "Unverified", "DerivedFrom" -> record["ID"]|>,
            If[KeyExistsQ[record["Validation"], "RecipeEvidence"], <|"RecipeEvidence" -> Join[record["Validation"]["RecipeEvidence"], <|"Derivation" -> "D_" <> weightText[record["Weight"]]|>]|>, <||>]],
        "Provenance" -> <|"Source" -> "ModularFormDerivative", "SourceID" -> record["ID"], "SourceRevision" -> record["Revision"], "SourceWeight" -> record["Weight"]|>|>];
    If[FailureQ[new], Return[new]];
    new = validateFormRecord[new]; If[FailureQ[new], Return[new]];
    registerForm[new]
];
ModularFormDerivative[___] := makeFailure["InvalidInput", "ModularFormDerivative expects a ModularForm."];

(*
    Summary: The data of a form in a new basis.
    Parameters: record — form record; b — invertible matrix of the form's dimension.
    Options/defaults: None.
    Returns: <|"Rep" (b rho b^-1), "BasisID" (repIdentity of the new matrices), "Definition" (Transform b . old), "Coefficients" (anchor frame A . b^-1),
        "QExpansion" (transported when stored)|>, or Failure.
    Effects: Pure.
    Failures: InvalidBasisChange (wrong shape, singular, or nonnumeric); UnverifiedContext (the basis identity needs the
        record's context bound in this kernel).
    Example: a scaling b = 2 I doubles the components and leaves the anchor functional on F unchanged.
    Remarks: No scalar rescaling: the normalization stays established in the anchor frame, not for the new first component.
    See also: ChangeModularFormBasis; transportNormalizationAnchor.
*)
changeFormBasisData[record_Association, b_] := Module[{d = record["Dimension"], binv, rep, qexp = record["QExpansion"]},
    If[!MatrixQ[b, NumericQ] || Dimensions[b] =!= {d, d}, Return[makeFailure["InvalidBasisChange", "The basis change must be a numeric square matrix of the form's dimension."]]];
    If[TrueQ[If[inexactDataQ[b], Abs[Det[N[b]]] < 10^-10, RootReduce[Det[b]] === 0]], Return[makeFailure["InvalidBasisChange", "The basis change must be invertible."]]];
    binv = If[inexactDataQ[b], Inverse[b], RootReduce[Inverse[b]]];
    rep = Rep[Map[If[inexactDataQ[{b, #}], b . # . binv, RootReduce[b . # . binv]] &, repMatrices[record["Rep"]]]];
    (* The basis identity is the content identity of the new matrices (repIdentity, as group variants), so a form moved
       into a group's basis carries that variant's identity. *)
    <|"Rep" -> rep, "BasisID" -> With[{snapshot = resolveRepContext[record["Context"]]}, If[FailureQ[snapshot], snapshot, repIdentity[rep, snapshot["GeneratorNames"]]]],
        (* Analytic trees are transformed directly; other kinds compose a final Transform (never both). *)
        "Definition" -> transformDefinition[record["Definition"], b],
        (* The anchor functional A . b^-1 acts on the transformed normalization source, so a derived form's frozen root is
           transformed with it (A . b^-1 . b F_root = A F_root). *)
        "Coefficients" -> If[AssociationQ[record["Coefficients"]],
            With[{moved = transportNormalizationAnchor[record["Coefficients"], b]}, If[KeyExistsQ[moved, "DerivedSource"],
                Join[moved, <|"DerivedSource" -> Join[moved["DerivedSource"], <|"Definition" -> transformDefinition[moved["DerivedSource"]["Definition"], b]|>]|>], moved]],
            record["Coefficients"]],
        "QExpansion" -> If[MatchQ[qexp, _QExpansionData], makeQExpansion[transportSeries[b, qExpansionJets[First[qexp]]],
            <|"Binding" -> qexp["Binding"], "Source" -> Missing["Transported"]|>], Missing["NotComputed"]]|>
];

(*
    Summary: A definition composed with a basis change F_new = b . F_old.
    Parameters: def — definition data; b — invertible matrix of the definition's dimension.
    Options/defaults: None.
    Returns: Definition data with a new DefinitionID: analytic trees without a Transform are transformed directly, every
        other definition composes a final Transform b . (previous Transform) (never both).
    Effects: Pure.
    Failures: None (b is validated by the caller).
    Example: transformDefinition[mldeDefinition, b]["Transform"] is b.
    See also: changeFormBasisData; formComponentJets.
*)
transformDefinition[def_Association, b_] := If[def["Kind"] === "Analytic" && !KeyExistsQ[def, "Transform"],
    Join[def, <|"DefinitionID" -> "definition-" <> CreateUUID[], "Components" -> Expand /@ (b . def["Components"])|>],
    Join[def, <|"DefinitionID" -> "definition-" <> CreateUUID[], "Transform" -> b . Lookup[def, "Transform", IdentityMatrix[Length[b]]],
        "Components" -> If[ListQ[def["Components"]], Expand /@ (b . def["Components"]), def["Components"]]|>]];

(*
    Summary: A form in a new basis as a new form.
    Status: Alpha.
    Parameters: y — ModularForm; b — invertible matrix (F_new = b . F_old, rho_new = b rho_old b^-1).
    Options/defaults: None.
    Returns: A new ModularForm, or Failure.
    Effects: Registers the new form; y is unchanged.
    Failures: InvalidBasisChange; UnknownModularForm; record failures.
    Example: ChangeModularFormBasis[y, {{0, 1}, {1, 0}}] swaps the components of a doublet form.
    Remarks: Representation, definitions, expansions and the anchor frame are transformed consistently; existing proof or
        numerical limitations carry over; no new modularity evidence follows from a basis change.
    See also: changeFormBasisData.
*)
ChangeModularFormBasis[y_ModularForm, b_?MatrixQ] := Module[{record = snapshotForm[y], data, ctx, new},
    If[FailureQ[record], Return[record]];
    data = changeFormBasisData[record, b]; If[FailureQ[data], Return[data]]; If[FailureQ[data["BasisID"]], Return[data["BasisID"]]];
    ctx = recordContextData[record, data["Rep"]]; If[FailureQ[ctx], Return[ctx]];
    ctx["BasisID"] = data["BasisID"];
    new = makeFormRecord[ctx, record["Weight"], data["Definition"], <|"Method" -> record["Method"], "Coefficients" -> data["Coefficients"], "QExpansion" -> data["QExpansion"],
        "Validation" -> Join[record["Validation"], <|"Status" -> "Unverified"|>], "Provenance" -> <|"Source" -> "ChangeModularFormBasis", "SourceID" -> record["ID"], "SourceRevision" -> record["Revision"], "BasisChange" -> b|>|>];
    If[FailureQ[new], Return[new]];
    new = validateFormRecord[new]; If[FailureQ[new], Return[new]];
    registerForm[new]
];
ChangeModularFormBasis[___] := makeFailure["InvalidInput", "ChangeModularFormBasis expects a ModularForm and a square matrix."];

True
