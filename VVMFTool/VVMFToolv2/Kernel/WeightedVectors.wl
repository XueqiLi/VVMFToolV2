(*
    :Title: Weighted representation vectors
    :Context: VVMFTool`Private`
    :Summary: Stage 4 vectors with one actual modular weight (an exact rational) per channel (D-S8-3): construction, joins and
        tensor products that read the weights off the single Stage 4 traversal (no second decomposition), form-slot
        records carried with the channels, and the factors of a modular model.
    :Responsibilities: weightedChannelID, makeWeightedVector, validateWeightedVector, mergeSlotRecords,
        joinWeightedVectors, productChannelWeights, weightedTensorChannels, resolveModularFactors; WeightedRepVector,
        MakeWeightedRepVector, WeightedFieldVector, JoinWeightedRepVectors, TensorProductWeightedVectors,
        WeightedVectorData.
    :Dependencies: RepVectors.wl (validateRepVector, makeVectorData, TensorProductVectors); Fields.wl; ModularModels.wl.
    :See Also: VVMFArch/step8Plan.md (weighted vectors and factors); D-S8-3.
*)

(*
    Summary: The stable identity of a vector record (channel).
    Parameters: record — vector record.
    Options/defaults: None.
    Returns: "wch:" followed by 20 hex digits of the hash of {TargetID, Path}.
    Effects: Pure.
    Failures: None.
    Example: a field leaf has the same channel ID in every vector that contains it.
    See also: makeWeightedVector.
*)
weightedChannelID[record_Association] := "wch:" <> StringTake[Hash[{record["TargetID"], record["Path"]}, "SHA256", "HexString"], 20];

(*
    Summary: Build a weighted vector from validated vector data and channel weights.
    Parameters: vector — RepVector; weights — <|channelID -> exact rational|>; slots — <|slotID -> slot record|>; reports — list of
        candidate reports; selection — selection record or Missing["NotUsed"].
    Options/defaults: None.
    Returns: WeightedRepVector, or Failure.
    Effects: Pure.
    Failures: DuplicateChannel (two records with the same path and irrep); InvalidWeights (missing, extra or not exact rational
        weights).
    Example: makeWeightedVector[FieldVector[l], <|id -> -1|>, <||>, {}, Missing["NotUsed"]].
    See also: MakeWeightedRepVector; validateWeightedVector.
*)
makeWeightedVector[vector_RepVector, weights_Association, slots_Association, reports_List, selection_] := Module[{records = First[vector]["Records"], ids},
    ids = weightedChannelID /@ records;
    If[!DuplicateFreeQ[ids], Return[makeFailure["DuplicateChannel", "Two channels have the same irrep and path, so their weights could not be told apart; join distinct vectors.",
        <|"ChannelIDs" -> Keys[Select[Counts[ids], # > 1 &]]|>]]];
    If[Sort[Keys[weights]] =!= Sort[ids] || !AllTrue[Values[weights], modularWeightQ],
        Return[makeFailure["InvalidWeights", "Give exactly one exact rational weight for every channel.", <|"Missing" -> Complement[ids, Keys[weights]], "Unknown" -> Complement[Keys[weights], ids]|>]]];
    WeightedRepVector[<|"SchemaVersion" -> 1, "Vector" -> vector, "ChannelIDs" -> ids, "Weights" -> AssociationThread[ids, Lookup[weights, ids]],
        "FormSlots" -> slots, "CandidateReports" -> reports, "Selection" -> selection|>]
];

(*
    Summary: Validate a weighted vector before use.
    Parameters: w — any expression.
    Options/defaults: None.
    Returns: The vector's data, or InvalidWeightedVector / vector Failure.
    Effects: Pure.
    Failures: InvalidWeightedVector (schema; channel IDs or weights that disagree with the records; FormComponent atoms
        without a carried slot record, or slot records whose components or irrep disagree with the channels using them).
    Example: a WeightedRepVector whose Weights were edited to an approximate number (0.5) fails here.
    See also: makeWeightedVector.
*)
validateWeightedVector[WeightedRepVector[data_Association]] := Module[{vector, ids, atoms},
    If[!SubsetQ[Keys[data], {"SchemaVersion", "Vector", "ChannelIDs", "Weights", "FormSlots", "CandidateReports", "Selection"}] || data["SchemaVersion"] =!= 1 ||
            Head[data["Vector"]] =!= RepVector || !AssociationQ[data["Weights"]] || !AssociationQ[data["FormSlots"]] || !ListQ[data["CandidateReports"]],
        Return[makeFailure["InvalidWeightedVector", "Malformed WeightedRepVector."]]];
    vector = validateRepVector[data["Vector"]]; If[FailureQ[vector], Return[vector]];
    ids = weightedChannelID /@ vector["Records"];
    If[ids =!= data["ChannelIDs"] || Keys[data["Weights"]] =!= ids || !AllTrue[Values[data["Weights"]], modularWeightQ],
        Return[makeFailure["InvalidWeightedVector", "The channel identities or weights disagree with the vector's records."]]];
    atoms = DeleteDuplicates[Cases[vector["Records"], FormComponent[s_String, _Integer] :> s, Infinity]];
    If[!SubsetQ[Keys[data["FormSlots"]], atoms] || !AllTrue[Values[data["FormSlots"]], AssociationQ[#] && SubsetQ[Keys[#], {"ID", "Components", "IrrepID", "Weight"}] &],
        Return[makeFailure["InvalidWeightedVector", "Form components must belong to the slot records the vector carries.", <|"Slots" -> Complement[atoms, Keys[data["FormSlots"]]]|>]]];
    data
];
validateWeightedVector[___] := makeFailure["InvalidWeightedVector", "Expected a WeightedRepVector."];

(* Data access by property name: "Vector", "Weights", "FormSlots", "ChannelIDs", "CandidateReport", "Selection". *)
WeightedRepVector[data_Association][property_String] := Switch[property,
    "CandidateReport", Switch[Length[Lookup[data, "CandidateReports", {}]], 0, Missing["NotUsed"], 1, First[data["CandidateReports"]], _, data["CandidateReports"]],
    _, Lookup[data, property, Missing["NotAvailable", property]]];

(*
    Summary: Merge slot records by ID.
    Parameters: lists — list of <|slotID -> record|>.
    Options/defaults: None.
    Returns: Merged association, or SlotConflict Failure.
    Effects: Pure.
    Failures: SlotConflict (one ID with two different records).
    Example: mergeSlotRecords[{a, a}] is a.
    See also: joinWeightedVectors; weightedTensorChannels.
*)
mergeSlotRecords[lists_List] := Module[{all = Flatten[Normal /@ lists], grouped},
    grouped = GroupBy[all, First -> Last];
    If[AnyTrue[grouped, Length[DeleteDuplicates[#]] > 1 &], Return[makeFailure["SlotConflict", "One form slot ID carries two different records.",
        <|"Slots" -> Keys[Select[grouped, Length[DeleteDuplicates[#]] > 1 &]]|>]]];
    Map[First, grouped]
];

(*
    Summary: Concatenate weighted vectors.
    Parameters: data — list of validated weighted data.
    Options/defaults: None.
    Returns: WeightedRepVector, or Failure.
    Effects: Pure.
    Failures: InvalidInput (empty list); ContextMismatch; DuplicateChannel; SlotConflict.
    Example: a doublet field of label 1 joined with a singlet of label 2 has weights {-1, -2}.
    See also: JoinWeightedRepVectors.
*)
joinWeightedVectors[data_List] := Module[{vector, slots},
    If[data === {}, Return[makeFailure["InvalidInput", "An empty join has no context; give at least one weighted vector."]]];
    vector = joinVectorData[Lookup[data, "Vector"]]; If[FailureQ[vector], Return[vector]];
    slots = mergeSlotRecords[Lookup[data, "FormSlots"]]; If[FailureQ[slots], Return[slots]];
    makeWeightedVector[vector, Join @@ Lookup[data, "Weights"], slots, DeleteDuplicates[Join @@ Lookup[data, "CandidateReports"]],
        If[Length[DeleteDuplicates[DeleteMissing[Lookup[data, "Selection"]]]] === 1, First[DeleteMissing[Lookup[data, "Selection"]]], Missing["NotUsed"]]]
];

(*
    Summary: The actual weights of the channels of a left-associated product, read off their paths.
    Parameters: factors — validated weighted data in product order; records — the product's records.
    Options/defaults: None.
    Returns: <|channelID -> weight|> for the records, or Failure.
    Effects: Pure.
    Failures: InconsistentPath (a path that does not decompose into the factors' channels).
    Example: for factors of weights {-1} and {-1, -2} each product channel adds its two leaves' weights.
    Remarks: A product path is Product(Left: path over the first k - 1 factors, Right: a factor-k channel path); the weight
        is the factor-1 weight plus the right weights along the spine. The product of no factors (the unit) has weight 0. No tensor decomposition
        is repeated (D-S8-3).
    See also: weightedTensorChannels.
*)
productChannelWeights[factors_List, records_List] := Module[{maps, n = Length[factors], weightOf},
    maps = Map[Function[f, AssociationThread[Lookup[First[f["Vector"]]["Records"], "Path", {}], Lookup[f["Weights"], f["ChannelIDs"]]]], factors];
    (* Every record is looked up in its factor's map (a declared unit record included); only the product of no factors
       is the unit of weight 0. *)
    weightOf[path_, k_] := Which[
        k === 0, If[path === <|"Kind" -> "Unit"|>, 0, Missing[]],
        k === 1, Lookup[maps[[1]], Key[path], Missing[]],
        MatchQ[path, KeyValuePattern[{"Kind" -> "Product"}]], With[{left = weightOf[path["Left"], k - 1], right = Lookup[maps[[k]], Key[path["Right"]], Missing[]]},
            If[MissingQ[left] || MissingQ[right], Missing[], left + right]],
        True, Missing[]];
    With[{weights = Map[weightOf[#["Path"], n] &, records]},
        If[MemberQ[weights, _Missing], makeFailure["InconsistentPath", "A product channel does not decompose into the factors' channels."],
            AssociationThread[weightedChannelID /@ records, weights]]]
];

(*
    Summary: The weighted tensor product of weighted vectors (TensorProductWeightedVectors' work).
    Parameters: c — Group or RepresentationContext; data — validated weighted data; options — TensorProductVectors options.
    Options/defaults: TargetIrreps All; CG options.
    Returns: WeightedRepVector, or Failure.
    Effects: As TensorProductVectors (CG computation and publication on a compatible group).
    Failures: TensorProductVectors failures; InconsistentPath; SlotConflict.
    Example: weightedTensorChannels[g, {wl, wr}, {TargetIrreps -> trivial}] gives the scalar channels with weight -2.
    Remarks: The Stage 4 product is computed once; zero channels, every copy and every path are kept. Empty factors give
        the tensor unit (weight 0); an empty factor gives the additive zero.
    See also: productChannelWeights.
*)
weightedTensorChannels[c_, data_List, options_List] := Module[{product, slots, weights},
    product = TensorProductVectors[c, Lookup[data, "Vector", {}], Sequence @@ options]; If[FailureQ[product], Return[product]];
    slots = mergeSlotRecords[Lookup[data, "FormSlots", {}]]; If[FailureQ[slots], Return[slots]];
    weights = productChannelWeights[data, First[product]["Records"]]; If[FailureQ[weights], Return[weights]];
    makeWeightedVector[product, weights, slots, DeleteDuplicates[Join @@ Lookup[data, "CandidateReports", {}]], Missing["NotUsed"]]
];

(*
    Summary: Resolve the factors of a modular model: fields, field IDs or weighted polynomial vectors.
    Parameters: model — validated modular model data; factors — list.
    Options/defaults: None.
    Returns: List of validated weighted data (one per factor), or Failure.
    Effects: Pure.
    Failures: UnknownField; ContextMismatch; UnsupportedFactor (a weighted vector carrying form slots, or another kind of
        value); validateWeightedPolynomial failures.
    Example: resolveModularFactors[m, {l, r}] gives two field leaves with actual weights -kf.
    Remarks: A field resolves to its weighted vector; a supplied weighted vector is checked channel by channel against its
        field content (covariance and actual weight), so a weight tag alone is never trusted.
    See also: ModularFormCandidates; ModularContractions.
*)
resolveModularFactors[model_Association, factors_List] := Module[{resolved},
    resolved = Map[Function[f, Which[
        MatchQ[f, _Field | _String], With[{fields = resolveModelFields[model, {f}]}, If[FailureQ[fields], fields,
            With[{d = First[fields]}, First[makeWeightedVector[fieldToVector[d], <|weightedChannelID[First[First[fieldToVector[d]]["Records"]]] -> model["ModularData"]["ActualFieldWeights"][d["ID"]]|>,
                <||>, {}, Missing["NotUsed"]]]]]],
        MatchQ[f, _WeightedRepVector], With[{d = validateWeightedVector[f]}, Which[
            FailureQ[d], d,
            First[d["Vector"]]["ContextDigest"] =!= model["ContextDigest"], makeFailure["ContextMismatch", "A weighted factor was made in another frozen context."],
            d["FormSlots"] =!= <||>, makeFailure["UnsupportedFactor", "Factors are field content; form slots are appended by the candidate operations."],
            True, With[{checks = MapThread[validateWeightedPolynomial[model, #1, #2] &, {First[d["Vector"]]["Records"], Lookup[d["Weights"], d["ChannelIDs"]]}]},
                If[AnyTrue[checks, FailureQ], FirstCase[checks, _Failure], d]]]],
        True, makeFailure["UnsupportedFactor", "A factor must be a Field, a field ID or a WeightedRepVector of the model's fields."]]], factors];
    If[AnyTrue[resolved, FailureQ], FirstCase[resolved, _Failure], resolved]
];

(*
    Summary: A weighted vector from a Stage 4 vector and one actual weight (an exact rational) per channel.
    Status: Alpha.
    Parameters: v — RepVector; weights — association from channel IDs (as WeightedVectorData lists them) or from record
        positions 1..n to exact rationals.
    Options/defaults: None.
    Returns: WeightedRepVector, or Failure.
    Effects: Pure.
    Failures: InvalidRepVector; InvalidWeights; DuplicateChannel; UnsupportedFactor (form components without slot records).
    Example: MakeWeightedRepVector[FieldVector[l], <|1 -> -1|>].
    Remarks: The weights are a declared grading, not a proof of the polynomials' field content; a modular model checks
        them against the fields when the vector is used as a factor.
    See also: WeightedVectorData; TensorProductWeightedVectors.
*)
MakeWeightedRepVector[v_RepVector, weights_Association] := Module[{data = validateRepVector[v], ids, keyed},
    If[FailureQ[data], Return[data]];
    If[!FreeQ[data["Records"], _FormComponent], Return[makeFailure["UnsupportedFactor", "Form components enter weighted vectors only through the candidate operations (with their slot records)."]]];
    ids = weightedChannelID /@ data["Records"];
    keyed = Which[
        AllTrue[Keys[weights], IntegerQ], If[Sort[Keys[weights]] =!= Range[Length[ids]], Return[makeFailure["InvalidWeights", "Record positions must be 1 .. n, each once.",
            <|"Records" -> Length[ids]|>]], KeyMap[ids[[#]] &, weights]],
        True, weights];
    makeWeightedVector[v, keyed, <||>, {}, Missing["NotUsed"]]
];
MakeWeightedRepVector[___] := makeFailure["InvalidInput", "MakeWeightedRepVector expects a RepVector and an association of channel weights."];

(*
    Summary: The weighted vector of model fields (a direct-sum family in caller order).
    Status: Alpha.
    Parameters: m — modular Model; selectors — list of Field values or field IDs.
    Options/defaults: None.
    Returns: WeightedRepVector whose channels are the fields' leaves with actual weights -kf, or Failure.
    Effects: Pure.
    Failures: InvalidModel; NotModularModel; UnknownField; DuplicateChannel (a field listed twice: repeat it as a product
        factor instead).
    Example: WeightedFieldVector[m, {d, s}] joins a doublet and a singlet, possibly of different weights.
    See also: MakeWeightedRepVector; JoinWeightedRepVectors.
*)
WeightedFieldVector[m_Model, selectors_List] := Module[{model = validateModelSchema[m], fields},
    If[FailureQ[model], Return[model]];
    If[!KeyExistsQ[model, "ModularData"], Return[makeFailure["NotModularModel", "The model has no modular weights; create it with CreateModularModel."]]];
    If[selectors === {}, Return[makeFailure["InvalidInput", "Select at least one field."]]];
    fields = resolveModelFields[model, selectors]; If[FailureQ[fields], Return[fields]];
    joinWeightedVectors[Map[With[{v = fieldToVector[#]}, First[makeWeightedVector[v, <|weightedChannelID[First[First[v]["Records"]]] -> model["ModularData"]["ActualFieldWeights"][#["ID"]]|>,
        <||>, {}, Missing["NotUsed"]]]] &, fields]]
];
WeightedFieldVector[___] := makeFailure["InvalidInput", "WeightedFieldVector expects a modular Model and a list of fields."];

(*
    Summary: Concatenate weighted vectors.
    Status: Alpha.
    Parameters: vectors — nonempty list of WeightedRepVector values of one frozen context.
    Options/defaults: None.
    Returns: WeightedRepVector, or Failure.
    Effects: Pure.
    Failures: InvalidInput; InvalidWeightedVector; ContextMismatch; DuplicateChannel; SlotConflict.
    Example: JoinWeightedRepVectors[{WeightedFieldVector[m, {d}], WeightedFieldVector[m, {s}]}].
    See also: JoinRepVectors; WeightedFieldVector.
*)
JoinWeightedRepVectors[vectors_List] := Module[{data = validateWeightedVector /@ vectors},
    If[AnyTrue[data, FailureQ], Return[FirstCase[data, _Failure]]];
    joinWeightedVectors[data]
];
JoinWeightedRepVectors[___] := makeFailure["InvalidInput", "JoinWeightedRepVectors expects a list of WeightedRepVector values."];

Options[TensorProductWeightedVectors] = Options[TensorProductVectors];

(*
    Summary: Tensor products of weighted vectors; the weights of a channel are the sum of its factors' weights.
    Status: Alpha.
    Parameters: c — Group or RepresentationContext; vectors — list of WeightedRepVector values.
    Options/defaults: TargetIrreps All; CG options (Method, Normalization, ...) as TensorProductVectors.
    Returns: WeightedRepVector, or Failure.
    Effects: As TensorProductVectors.
    Failures: InvalidWeightedVector; TensorProductVectors failures; InconsistentPath; SlotConflict.
    Example: TensorProductWeightedVectors[c, {wl, wr}, TargetIrreps -> trivial].
    Remarks: One Stage 4 traversal gives the data and the weights; zero channels, multiplicities and paths are kept; {}
        gives the tensor unit of weight 0.
    See also: TensorProductVectors; WeightedVectorData.
*)
TensorProductWeightedVectors[c : (_Group | _RepresentationContext), vectors_List, options : OptionsPattern[]] := Module[{data = validateWeightedVector /@ vectors},
    If[AnyTrue[data, FailureQ], Return[FirstCase[data, _Failure]]];
    weightedTensorChannels[c, data, {options}]
];
TensorProductWeightedVectors[___] := makeFailure["InvalidInput", "TensorProductWeightedVectors expects a Group or RepresentationContext, a list of WeightedRepVector values and options."];

(*
    Summary: The immutable data of a weighted vector.
    Status: Alpha.
    Parameters: v — WeightedRepVector.
    Options/defaults: None.
    Returns: <|"Vector" (RepVector), "ChannelIDs", "Weights" (channel ID -> actual weight), "FormSlots" (slot ID -> record),
        "CandidateReport" (Missing["NotUsed"] for vectors without form candidates), "Selection"|>, or Failure.
    Effects: Pure.
    Failures: InvalidWeightedVector.
    Example: VectorComponents[WeightedVectorData[v]["Vector"]] lists the channels.
    See also: MakeWeightedRepVector.
*)
WeightedVectorData[v_WeightedRepVector] := With[{data = validateWeightedVector[v]}, If[FailureQ[data], data,
    <|"Vector" -> data["Vector"], "ChannelIDs" -> data["ChannelIDs"], "Weights" -> data["Weights"], "FormSlots" -> data["FormSlots"],
        "CandidateReport" -> v["CandidateReport"], "Selection" -> data["Selection"]|>]];
WeightedVectorData[___] := makeFailure["InvalidInput", "WeightedVectorData expects a WeightedRepVector."];

Format[WeightedRepVector[data_Association], StandardForm] := Interpretation[Row[{"WeightedRepVector[", Length[Lookup[data, "ChannelIDs", {}]], " channels, weights ",
    Short[DeleteDuplicates[Values[Lookup[data, "Weights", <||>]]], 1], "]"}], WeightedRepVector[data]];

True
