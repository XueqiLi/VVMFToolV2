(*
    :Title: Representation-valued fields
    :Context: VVMFTool`Private`
    :Summary: Immutable Field values with inert components, bound to the frozen context and the accepted matrix variant
        of their irrep (their transformation law), and their Stage 4 vectors.
    :Responsibilities: makeFieldData, validateField, fieldToVector, resolveModelFields; Field, FieldComponent, CreateField,
        FieldComponents, FieldVector.
    :Dependencies: RepVectors.wl (vectorContext, makeVectorData); CGData.wl (cgVariant); Representation.wl
        (resolveRepContext, contextDigest).
    :See Also: VVMFArch/step5Plan.md (Field contract).
*)

(*
    Summary: Build the data of a new field.
    Parameters: context — RepresentationContext; id — irrep ID; name — display name (string).
    Options/defaults: None.
    Returns: Field[<|"SchemaVersion" -> 1, "ID", "Name", "IrrepID", "Dimension", "Rep", "BasisID", "Arithmetic",
        "Context", "ContextDigest", "Components"|>], or Failure.
    Effects: Allocates a fresh field ID; components are inert FieldComponent[fieldID, i] atoms (no symbol is defined).
    Failures: InvalidIrrep; MissingRepresentations (no accepted matrix variant); InvalidInput (empty name).
    Example: makeFieldData[ctx, t, "L"] has three components for a triplet t.
    See also: CreateField; validateField.
*)
makeFieldData[context_RepresentationContext, id_String, name_String] := Module[{snapshot = First[context], variant, fieldID},
    If[StringLength[name] === 0, Return[makeFailure["InvalidInput", "A field name must be a nonempty string."]]];
    If[!MemberQ[snapshot["CharacterData"]["IrrepIDs"], id], Return[makeFailure["InvalidIrrep", "Unknown irrep ID.", <|"IrrepIDs" -> {id}|>]]];
    variant = cgVariant[snapshot, id];
    If[MissingQ[variant], Return[makeFailure["MissingRepresentations",
        "A field needs the accepted matrices of its irrep (its transformation law); compute them and take a new context.", <|"IrrepIDs" -> {id}|>]]];
    fieldID = "field-" <> CreateUUID[];
    Field[<|"SchemaVersion" -> 1, "ID" -> fieldID, "Name" -> name, "IrrepID" -> id, "Dimension" -> variant["Dimension"],
        "Rep" -> variant["Rep"], "BasisID" -> variant["Identity"], "Arithmetic" -> variant["Arithmetic"], "Context" -> context,
        "ContextDigest" -> contextDigest[snapshot], "Components" -> Table[FieldComponent[fieldID, i], {i, variant["Dimension"]}]|>]
];
makeFieldData[___] := makeFailure["InvalidInput", "Expected a context, an irrep ID and a name."];

(*
    Summary: Validate a field before use.
    Parameters: f — any expression.
    Options/defaults: None.
    Returns: The field's data association, or InvalidField/UnverifiedContext Failure.
    Effects: Pure.
    Failures: Wrong schema or fields; a context not bound in this kernel or with another digest; components that are not
        FieldComponent[ID, 1..d]; a Rep or basis identity that is not the context's variant of the irrep.
    Example: a Field whose components were edited by hand fails here.
    See also: makeFieldData.
*)
validateField[Field[data_Association]] := Module[{snapshot, variant},
    If[!SubsetQ[Keys[data], {"SchemaVersion", "ID", "Name", "IrrepID", "Dimension", "Rep", "BasisID", "Arithmetic", "Context",
            "ContextDigest", "Components"}] || data["SchemaVersion"] =!= 1 || !StringQ[data["ID"]] || !StringQ[data["Name"]] ||
        Head[data["Context"]] =!= RepresentationContext,
        Return[makeFailure["InvalidField", "Malformed Field."]]];
    snapshot = resolveRepContext[data["Context"]];
    If[FailureQ[snapshot], Return[snapshot]];
    variant = cgVariant[snapshot, data["IrrepID"]];
    If[contextDigest[snapshot] =!= data["ContextDigest"] || MissingQ[variant] || variant["Identity"] =!= data["BasisID"] ||
            variant["Rep"] =!= data["Rep"] || data["Dimension"] =!= variant["Dimension"] ||
            data["Components"] =!= Table[FieldComponent[data["ID"], i], {i, data["Dimension"]}],
        Return[makeFailure["InvalidField", "The field disagrees with its context, representation or components."]]];
    data
];
validateField[___] := makeFailure["InvalidField", "Expected a Field."];

(*
    Summary: The Stage 4 vector of a field: its components as one leaf record.
    Parameters: data — validated field data.
    Options/defaults: None.
    Returns: RepVector with one record (target the field's irrep, components the field's atoms, path leaf with the field ID).
    Effects: Pure.
    Failures: None.
    Example: VectorComponents[fieldToVector[d]][[1, "Components"]] === d["Components"].
    See also: FieldVector; makeVectorData.
*)
fieldToVector[data_Association] := makeVectorData[data["Context"], {<|"TargetID" -> data["IrrepID"], "Components" -> data["Components"],
    "Path" -> <|"Kind" -> "Leaf", "VectorID" -> data["ID"]|>, "BasisID" -> data["BasisID"], "ChannelIDs" -> {}|>}, <|data["ID"] -> data["Name"]|>];

(*
    Summary: Resolve field selectors (Field values or field IDs) against a model's registered fields.
    Parameters: model — validated model data; selectors — list of Field values or ID strings (repetitions allowed).
    Options/defaults: None.
    Returns: List of the registered field data, in selector order, or Failure.
    Effects: Pure.
    Failures: UnknownField for a selector that is not registered in the model (a Field with the same irrep but another ID
        is a different field).
    Example: resolveModelFields[m, {l, l, r}] repeats l's data twice.
    See also: Contractions.
*)
resolveModelFields[model_Association, selectors_List] := Module[{byID = AssociationThread[Lookup[model["Fields"], "ID", {}], model["Fields"]], ids},
    ids = Map[Which[MatchQ[#, Field[_Association]], First[#]["ID"], StringQ[#], #, True, None] &, selectors];
    If[MemberQ[ids, None] || !SubsetQ[Keys[byID], ids],
        Return[makeFailure["UnknownField", "A factor is not a field registered in the model.", <|"Unknown" -> Complement[DeleteCases[ids, None], Keys[byID]]|>]]];
    byID /@ ids
];
resolveModelFields[___] := makeFailure["InvalidInput", "Expected model data and a list of field selectors."];

(* Data access by property name, e.g. f["ID"], f["IrrepID"] (Stage 8: field IDs key FieldWeights). *)
Field[data_Association][property_String] := Lookup[data, property, Missing["NotAvailable", property]];

(* A summary instead of the frozen context. *)
Format[Field[data_Association], StandardForm] := Interpretation[Row[{"Field[", Lookup[data, "Name", "?"], ", dimension ",
    Lookup[data, "Dimension", "?"], "]"}], Field[data]];

(*
    Summary: A field transforming in one irrep of a group or frozen context.
    Parameters: c — Group or RepresentationContext; id — irrep ID; name — display name.
    Options/defaults: None.
    Returns: Field, or Failure.
    Effects: Freezing a group registers its context; no symbol is defined.
    Failures: UnverifiedContext; InvalidIrrep; MissingRepresentations; InvalidInput.
    Example: FieldComponents[CreateField[g, t, "L"]] lists three inert components.
    Remarks: Distinct fields of the same irrep are independent; names are display labels only.
    See also: FieldComponents; FieldVector; CreateModel.
*)
CreateField[c : (_Group | _RepresentationContext), id_String, name_String] := With[{context = vectorContext[c]},
    If[FailureQ[context], context, makeFieldData[context, id, name]]];
CreateField[c : (_Group | _RepresentationContext), k_Integer, name_String] := withIrreps[c, {k}, CreateField[c, #, name] &];
CreateField[___] := makeFailure["InvalidInput", "CreateField expects a Group or RepresentationContext, an irrep ID and a name."];

(*
    Summary: The ordered inert components of a field.
    Parameters: f — Field.
    Options/defaults: None.
    Returns: {FieldComponent[ID, 1], ...}, or Failure.
    Effects: Pure.
    Failures: InvalidField; UnverifiedContext.
    Example: Length[FieldComponents[CreateField[g, t, "L"]]] is 3.
    See also: CreateField; FieldVector.
*)
FieldComponents[f_Field] := With[{data = validateField[f]}, If[FailureQ[data], data, data["Components"]]];
FieldComponents[___] := makeFailure["InvalidInput", "FieldComponents expects a Field."];

(*
    Summary: The Stage 4 representation-valued vector of a field.
    Parameters: f — Field.
    Options/defaults: None.
    Returns: RepVector whose components are the field's atoms, in its frozen context and basis; or Failure.
    Effects: Pure.
    Failures: InvalidField; UnverifiedContext.
    Example: TensorProductVectors[g, {FieldVector[l], FieldVector[r]}] contracts the two fields.
    See also: CreateField; TensorProductVectors.
*)
FieldVector[f_Field] := With[{data = validateField[f]}, If[FailureQ[data], data, fieldToVector[data]]];
FieldVector[___] := makeFailure["InvalidInput", "FieldVector expects a Field."];

True
