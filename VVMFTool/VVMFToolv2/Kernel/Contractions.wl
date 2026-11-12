(*
    :Title: Field contractions and independent channels
    :Context: VVMFTool`Private`
    :Summary: All CG contraction paths of model fields into the model's degree-one target (zeros and repeated copies
        kept), their exact linear independence over the CG constants, a complete relation map, and explicit selection.
    :Responsibilities: buildContractionSet, validateContractionSet, polynomialCoefficientData, independentChannelBasis,
        selectChannelData; ContractionSet, Contractions, IndependentContractions, SelectContractions.
    :Dependencies: Fields.wl; Models.wl; RepVectors.wl (TensorProductVectors); CGLinear.wl (cgArithmetic).
    :See Also: VVMFArch/step5Plan.md (Contractions, IndependentContractions).
*)

(*
    Summary: Sparse exact coefficient data of polynomials in given variables.
    Parameters: expressions — polynomials; variables — component atoms; arithmetic — cgArithmetic settings.
    Options/defaults: None.
    Returns: <|"Monomials" -> exponent vectors (stable order of first appearance), "Matrix" -> rows of coefficients|>, or Failure.
    Effects: Pure.
    Failures: UnsupportedCoefficient (a coefficient that is not a number: independence is over scalar constants only).
    Example: polynomialCoefficientData[{x y, 2 x y}, {x, y}, ar]["Matrix"] is {{1}, {2}}.
    See also: independentChannelBasis.
*)
polynomialCoefficientData[expressions_List, variables_List, arithmetic_Association] := Module[{rules, monomials, matrix},
    rules = If[variables === {}, ({{} -> #} &) /@ expressions, CoefficientRules[Expand[#], variables] & /@ expressions];
    rules = Map[If[# === {}, {}, #] &, rules];
    If[!AllTrue[Flatten[Values /@ rules], NumericQ],
        Return[makeFailure["UnsupportedCoefficient", "Contraction coefficients must be numbers (CG constants) for an independence test."]]];
    monomials = DeleteDuplicates[Flatten[Keys /@ rules, 1]];
    matrix = Map[Function[r, Lookup[Association[r], monomials, 0]], rules];
    <|"Monomials" -> monomials, "Matrix" -> matrix|>
];
polynomialCoefficientData[___] := makeFailure["InvalidInput", "Expected expressions, variables and arithmetic."];

(*
    Summary: A basis of rows in stable order and every row's coordinates in it.
    Parameters: matrix — coefficient rows; settings — arithmetic settings.
    Options/defaults: None.
    Returns: <|"Basis" -> row positions, "Relations" -> list of coordinate vectors (one per row, in the basis order),
        "Rank"|>, or Failure.
    Effects: Pure.
    Failures: PrecisionFailure (numerical rank without a clear gap); UnprovedIdentity (a reconstruction that does not hold).
    Example: rows {{1, 0}, {2, 0}, {0, 1}} give basis {1, 3} and relations {{1, 0}, {2, 0}, {0, 1}}.
    Remarks: Exact rows are placed in one exact domain (number field or Root arithmetic) and each row joins the basis
        exactly when it raises the exact rank; coordinates solve the exact linear system and are checked. A tiny exact
        nonzero coefficient is never dropped. Numerical rows are taken at the working precision; the rank counts singular
        values above tolerance x max(largest singular value, 1) and needs a gap of a factor ten there (the cgNullSpace
        convention), and every relation is checked against the same threshold.
    See also: IndependentContractions; independentMatrices.
*)
independentChannelBasis[matrix_List, settings_Association] := Module[{ar, rows, basis = {}, rank = 0, r, basisRows, relations, check, numeric, sigma,
        threshold, scale},
    If[matrix === {} || AllTrue[Flatten[matrix], # === 0 &], Return[<|"Basis" -> {}, "Relations" -> ConstantArray[{}, Length[matrix]], "Rank" -> 0|>]];
    ar = cgArithmetic[{matrix}, settings];
    rows = ar["Embed"][matrix];
    If[ar["Field"] === None,
        (* One convention (review M8), as cgNullSpace: on the rows at the working precision, a singular value counts when
           it exceeds threshold = tolerance x max(largest singular value, 1); a value in (threshold, 10 threshold] is an
           ambiguous rank; the basis is chosen greedily with the same threshold and relations are checked against it. *)
        numeric = N[matrix, Replace[settings["Precision"], {Infinity -> 50, MachinePrecision -> MachinePrecision}]];
        sigma = SingularValueList[numeric, Tolerance -> 0];
        scale = Max[Append[Abs[sigma], 1]];
        threshold = settings["Tolerance"] scale;
        If[AnyTrue[sigma, threshold < # <= 10 threshold &],
            Return[makeFailure["PrecisionFailure", "The numerical rank of the contraction polynomials is ambiguous at this tolerance."]]];
        Do[r = Count[SingularValueList[Append[numeric[[basis]], numeric[[k]]], Tolerance -> 0], x_ /; x > threshold];
            If[r > rank, AppendTo[basis, k]; rank = r], {k, Length[numeric]}];
        basisRows = numeric[[basis]];
        relations = Map[LeastSquares[Transpose[basisRows], #] &, numeric];
        check = AllTrue[Range[Length[numeric]], Max[Append[Abs[relations[[#]] . basisRows - numeric[[#]]], 0]] <= 10 threshold &],
        Do[r = fieldRank[ar["Field"], Append[rows[[basis]], rows[[k]]]];
            If[r > rank, AppendTo[basis, k]; rank = r], {k, Length[rows]}];
        basisRows = rows[[basis]];
        relations = Map[Function[row, ar["Back"][{LinearSolve[Transpose[basisRows], row]}][[1]]], rows];
        check = AllTrue[Range[Length[rows]], fieldZeroQ[ar["Reduce"][ar["Embed"][{relations[[#]]}][[1]] . basisRows - rows[[#]]]] &]];
    If[!check, Return[makeFailure["UnprovedIdentity", "A contraction polynomial is not reconstructed from the basis."]]];
    <|"Basis" -> basis, "Relations" -> relations, "Rank" -> rank|>
];
independentChannelBasis[___] := makeFailure["InvalidInput", "Expected a coefficient matrix and settings."];

(*
    Summary: Build a ContractionSet from the model, its resolved factors and Stage 4 vector records.
    Parameters: model — validated model data; fields — resolved factor field data; options — CG option rules.
    Options/defaults: CG options as CGCoefficients (Method, Arithmetic, Normalization, ExchangeSymmetry, ...); the model's
        arithmetic by default.
    Returns: ContractionSet data, or Failure.
    Effects: Context CG calls (nothing is published).
    Failures: TensorProductVectors and CG failures; InvalidTarget (empty factors with a nontrivial target).
    Example: buildContractionSet[m, {l, r}, {}]["Channels"] has one channel for A4 3 (x) 3 -> trivial.
    Remarks: Each Stage 4 record of the degree-one target gives a channel: its path, CG channel IDs, scalar polynomial
        (the record's single component) and zero status. Repeated factors with the same field ID use the same components.
    See also: Contractions; TensorProductVectors.
*)
buildContractionSet[model_Association, fields_List, options_List] := Module[{vectors, records, settings, channels, arithmetic, supplied = Association[options], forwarded,
        precision},
    arithmetic = Lookup[supplied, Arithmetic, model["Arithmetic"]];
    (* The representation data of the factors, the target and every irrep that can occur as an intermediate of the
       left-associated product bound the set's precision (reviews M25, M29); exact arithmetic over numerical variants
       fails NumericalInput. Intermediates come from the characters, so ordinary rounding of the CG data never lowers the
       declared precision. *)
    precision = dataPrecision[{Map[repMatrices, Lookup[fields, "Rep", {}]], repMatrices[model["TargetRep"]],
        Map[repMatrices, Lookup[DeleteMissing[cgVariant[First[model["Context"]], #] & /@ intermediateIrreps[First[model["Context"]], Lookup[fields, "IrrepID", {}]]], "Rep", {}]]}];
    settings = If[arithmetic === "Exact", arithmeticSettings["Exact", 50, Automatic, precision],
        arithmeticSettings["Numerical", Lookup[supplied, WorkingPrecision, If[model["Precision"] === MachinePrecision || NumericQ[model["Precision"]], model["Precision"], 50]],
            Lookup[supplied, Tolerance, model["Tolerance"]], precision]];
    If[FailureQ[settings], Return[settings]];
    settings = checkedTolerance[settings, precision =!= Infinity]; If[FailureQ[settings], Return[settings]];
    (* the call's domain choice (methodOptionsPlan.md 1.3); the session default when not supplied *)
    settings = cgCheckSettings[settings, <|NumberField -> Lookup[supplied, NumberField, Automatic],
        FieldMethod -> Lookup[supplied, FieldMethod, OptionValue[Contractions, FieldMethod]]|>];
    If[fields === {} && model["TargetIrrepID"] =!= First[model["Context"]]["CharacterData"]["TrivialIrrepID"],
        Return[<|"Channels" -> {}, "Settings" -> settings, "Arithmetic" -> arithmetic|>]];
    vectors = fieldToVector /@ fields;
    (* The CG data use the set's arithmetic, precision and tolerance (review M7): a numerical model's own settings are
       forwarded when the caller gives none. *)
    forwarded = Join[FilterRules[options, Options[CGCoefficients]], If[KeyExistsQ[supplied, Arithmetic], {}, {Arithmetic -> arithmetic}],
        If[arithmetic === "Numerical" && !KeyExistsQ[supplied, WorkingPrecision], {WorkingPrecision -> settings["Precision"]}, {}],
        If[arithmetic === "Numerical" && !KeyExistsQ[supplied, Tolerance] && model["Tolerance"] =!= Automatic, {Tolerance -> model["Tolerance"]}, {}]];
    records = TensorProductVectors[model["Context"], vectors, TargetIrreps -> model["TargetIrrepID"], Sequence @@ forwarded];
    If[FailureQ[records], Return[records]];
    channels = Map[Function[record, With[{p = Expand[First[record["Components"]]]},
            <|"ChannelID" -> "path:" <> StringTake[Hash[{Lookup[fields, "ID"], record["Path"]}, "SHA256", "HexString"], 16],
                "Path" -> record["Path"], "ChannelIDs" -> record["ChannelIDs"], "Polynomial" -> p,
                "Zero" -> If[arithmetic === "Exact", p === 0 || TrueQ[cgZeroTest[p, cgArithmetic[{}, settings]]],
                    AllTrue[Flatten[{CoefficientList[p, Flatten[Lookup[fields, "Components"]]]}], Abs[#] <= settings["Tolerance"] &]],
                (* the channel's verification status: its vector record's (methodOptionsPlan.md 2C.2) *)
                "VerificationStatus" -> Lookup[record, "VerificationStatus", "Exact"]|>]],
        vectorRecords[records]];
    <|"Channels" -> channels, "Settings" -> settings, "Arithmetic" -> arithmetic|>
];

(*
    Summary: The irreps that can occur as intermediates of the left-associated product of the listed irreps.
    Parameters: snapshot — frozen context data; ids — factor irrep IDs in product order.
    Options/defaults: None.
    Returns: Duplicate-free list of irrep IDs with positive multiplicity in some partial product f1 x ... x fk,
        2 <= k < Length[ids] (empty for one or two factors), or {} when the characters cannot decide.
    Effects: Pure (fills the character pair memo).
    Failures: None (a character failure gives {}; the CG computation reports it).
    Example: for four T' triplets the intermediates include the singlets 1' and 1''.
    Remarks: A superset of the intermediates a target-pruned path plan uses, so the precision bound is conservative.
    See also: buildContractionSet; tensorMultiplicities.
*)
intermediateIrreps[snapshot_Association, ids_List] := DeleteDuplicates[Flatten[Table[
    With[{m = tensorMultiplicities[snapshot["CharacterData"], Take[ids, k]]}, If[AssociationQ[m], Keys[Select[m, # > 0 &]], {}]],
    {k, 2, Length[ids] - 1}]]];

(*
    Summary: Validate a ContractionSet before use.
    Parameters: set — any expression.
    Options/defaults: None.
    Returns: The set's data, or InvalidContractionSet Failure.
    Effects: Pure.
    Failures: Missing fields, malformed channels, duplicate channel IDs.
    Example: a set whose Channels were replaced by a string fails here.
    See also: Contractions.
*)
validateContractionSet[ContractionSet[data_Association]] := If[
    SubsetQ[Keys[data], {"SchemaVersion", "ID", "ModelID", "ContextDigest", "TargetIrrepID", "Factors", "FieldIDs", "Variables", "Channels",
        "RawChannels", "Independence", "Arithmetic", "Precision", "Tolerance"}] && data["SchemaVersion"] === 1 && ListQ[data["Channels"]] &&
        AllTrue[Join[data["Channels"], data["RawChannels"]], AssociationQ[#] && SubsetQ[Keys[#], {"ChannelID", "Path", "Polynomial", "Zero"}] &] &&
        DuplicateFreeQ[Lookup[data["Channels"], "ChannelID", {}]] && SubsetQ[Lookup[data["RawChannels"], "ChannelID", {}], Lookup[data["Channels"], "ChannelID", {}]] &&
        AssociationQ[Lookup[data, "FieldNames", <||>]] && MatchQ[Lookup[data, "Context", Missing[]], _Missing | _RepresentationContext] &&
        TrueQ[optionValueQ[FieldMethod, Lookup[data, "FieldMethod", Automatic], "Contractions"]],
    data, makeFailure["InvalidContractionSet", "Malformed ContractionSet."]];
validateContractionSet[___] := makeFailure["InvalidContractionSet", "Expected a ContractionSet."];

(* Data access by property name, e.g. set["Channels"], set["Relations"]. *)
ContractionSet[data_Association][property_String] := Lookup[data, property, Lookup[Lookup[data, "Independence", <||>] /. _Missing -> <||>, property,
    Missing["NotAvailable", property]]];

(*
    Summary: A new set with exactly the given channels in caller order and recomputed independence metadata.
    Parameters: data — validated set data; ids — duplicate-free list of known channel IDs.
    Options/defaults: None.
    Returns: Set data, or Failure.
    Effects: Pure.
    Failures: InvalidSelection (duplicates or unknown IDs).
    Example: selectChannelData[d, {id2, id1}]["Channels"] lists id2 first.
    See also: SelectContractions.
*)
selectChannelData[data_Association, ids_List] := Module[{byID = AssociationThread[Lookup[data["RawChannels"], "ChannelID", {}], data["RawChannels"]], selected},
    If[!DuplicateFreeQ[ids] || !SubsetQ[Keys[byID], ids],
        Return[makeFailure["InvalidSelection", "Select known channel IDs once each.", <|"Unknown" -> Complement[ids, Keys[byID]]|>]]];
    selected = Join[data, <|"ID" -> "contractions-" <> CreateUUID[], "Channels" -> Lookup[byID, ids], "Independence" -> Missing["NotComputed"]|>];
    If[MissingQ[data["Independence"]], selected, independenceData[selected]]
];

(*
    Summary: Compute the independence metadata of a set's current channels.
    Parameters: data — set data.
    Options/defaults: None.
    Returns: Set data whose Independence is <|"Basis" -> channel IDs, "Relations" -> channel ID -> <|basis ID -> coefficient|>,
        "Rank", "Arithmetic"|>, or Failure.
    Effects: Pure.
    Failures: polynomialCoefficientData and independentChannelBasis failures.
    Example: a set with one zero and one nonzero channel has rank one.
    See also: IndependentContractions.
*)
independenceData[data_Association] := Module[{settings = setSettings[data], coefficients, basis, ids = Lookup[data["Channels"], "ChannelID", {}]},
    coefficients = polynomialCoefficientData[Lookup[data["Channels"], "Polynomial", {}], data["Variables"], settings];
    If[FailureQ[coefficients], Return[coefficients]];
    basis = independentChannelBasis[coefficients["Matrix"], settings];
    If[FailureQ[basis], Return[basis]];
    Join[data, <|"Independence" -> <|"Basis" -> ids[[basis["Basis"]]], "Rank" -> basis["Rank"], "Arithmetic" -> data["Arithmetic"],
        "Relations" -> AssociationThread[ids, Map[AssociationThread[ids[[basis["Basis"]]], #] &, basis["Relations"]]]|>|>]
];

(* The status of a set of contraction channels: the weakest channel ("Exact" for none; channels made before statuses
   existed read "Exact"). *)
contractionChannelsStatus[channels_List] := If[channels === {}, "Exact", cgWeakestStatus[Lookup[#, "VerificationStatus", "Exact"] & /@ channels]];

(*
    Summary: The arithmetic settings of a set.
    Parameters: data — set data.
    Options/defaults: None.
    Returns: arithmeticSettings association with the set's FieldMethod (cgCheckSettings).
    Effects: Pure.
    Failures: None.
    Example: setSettings[d]["Arithmetic"] is "Exact" by default.
    See also: independenceData.
*)
setSettings[data_Association] := cgCheckSettings[If[data["Arithmetic"] === "Exact", arithmeticSettings["Exact", 50, Automatic, Infinity],
    arithmeticSettings["Numerical", data["Precision"], data["Tolerance"], data["Precision"]]],
    (* the FieldMethod of the call that built the set (Automatic for sets made before it was recorded) *)
    <|"FieldMethod" -> Lookup[data, "FieldMethod", Automatic]|>];

Options[Contractions] = cgDerivedOptions[];
(* D-S5-8: a set records its field names and frozen context (display and archive of Stage 6); both keys are optional for
   validation, so sets made before this addition stay valid. *)

(*
    Summary: Every CG contraction path of model fields into the model's target, as scalar polynomials.
    Parameters: m — Model; factors — ordered list of Field values or field IDs of the model (repetitions allowed).
    Options/defaults: CG options (Method, Arithmetic, Normalization, ExchangeSymmetry, ...); the model's arithmetic by default.
    Returns: ContractionSet with all channels (zeros and every copy kept), the factor field names and the frozen context,
        or Failure.
    Effects: CG computation in the model's frozen context (nothing published to the group). The context reads the live
        group's CG store when its state matches, so CacheCG[g] beforehand makes repeated contractions cache hits.
    Failures: InvalidModel; UnknownField; UnknownOption; InvalidOption; CG failures (a failure leaves accepted CG data as
        Stage 4 promises).
    Example: Length[Contractions[m, {l, r}]["Channels"]] is 1 for two A4 triplets and a trivial target.
    Remarks: Empty factors give the scalar unit only for the trivial target (no channel otherwise).
    See also: IndependentContractions; SelectContractions; CoupleContractions.
*)
Contractions[m_Model, factors_List, options : OptionsPattern[]] := Module[{model = validateModelSchema[m], fields, built, effective},
    If[FailureQ[model], Return[model]];
    (* Unknown or invalid options fail (review M6); only the supplied rules are forwarded, so the model's own arithmetic
       applies to options the caller did not give. *)
    effective = resolveOperationOptions[Contractions, "Contractions", {options}];
    If[FailureQ[effective], Return[effective]];
    fields = resolveModelFields[model, factors];
    If[FailureQ[fields], Return[fields]];
    built = cgFieldCatch[buildContractionSet[model, fields, {options}]];
    If[FailureQ[built], Return[built]];
    ContractionSet[<|"SchemaVersion" -> 1, "ID" -> "contractions-" <> CreateUUID[], "ModelID" -> model["ID"], "ContextDigest" -> model["ContextDigest"],
        "TargetIrrepID" -> model["TargetIrrepID"], "Factors" -> Lookup[fields, "ID", {}], "FieldIDs" -> DeleteDuplicates[Lookup[fields, "ID", {}]],
        "Variables" -> DeleteDuplicates[Flatten[Lookup[fields, "Components", {}]]], "Channels" -> built["Channels"], "RawChannels" -> built["Channels"],
        "Independence" -> Missing["NotComputed"], "Arithmetic" -> built["Arithmetic"], "Precision" -> built["Settings"]["Precision"],
        "Tolerance" -> built["Settings"]["Tolerance"], "FieldMethod" -> built["Settings"]["FieldMethod"],
        "VerificationStatus" -> contractionChannelsStatus[built["Channels"]],
        "FieldNames" -> AssociationThread[Lookup[fields, "ID", {}], Lookup[fields, "Name", {}]],
        "Context" -> model["Context"]|>]
];
Contractions[___] := makeFailure["InvalidInput", "Contractions expects a Model, a list of fields and options."];

(*
    Summary: A linearly independent basis of the set's channel polynomials and every channel's relation to it.
    Parameters: set — ContractionSet.
    Options/defaults: The set's arithmetic.
    Returns: ContractionSet whose Channels are the basis (a subset of the original nonzero channels, stable order),
        with Relations (every original channel, zeros included, as basis coefficients) and Rank; RawChannels keep all paths.
    Effects: Pure.
    Failures: InvalidContractionSet; UnsupportedCoefficient; PrecisionFailure (ambiguous numerical rank).
    Example: the A4 repeated-field quartic has seven raw paths of rank two.
    Remarks: Linear independence over scalar constants with distinct field components as independent commuting variables;
        no equations of motion or polynomial-ideal relations are used.
    See also: Contractions; CoupleContractions.
*)
IndependentContractions[set_ContractionSet] := Module[{data = validateContractionSet[set], computed},
    If[FailureQ[data], Return[data]];
    computed = cgFieldCatch[independenceData[data]];
    If[FailureQ[computed], Return[computed]];
    ContractionSet[Join[computed, <|"ID" -> "contractions-" <> CreateUUID[],
        "Channels" -> Select[computed["Channels"], MemberQ[computed["Independence"]["Basis"], #["ChannelID"]] &]|>]]
];
IndependentContractions[___] := makeFailure["InvalidInput", "IndependentContractions expects a ContractionSet."];

(*
    Summary: A new set with exactly the given channels, in caller order.
    Parameters: set — ContractionSet; ids — duplicate-free list of known channel IDs (from the set's raw channels).
    Options/defaults: None.
    Returns: ContractionSet, or Failure.
    Effects: Pure; the input set is unchanged.
    Failures: InvalidContractionSet; InvalidSelection.
    Example: SelectContractions[s, {}] has no channels.
    See also: Contractions; CoupleContractions.
*)
SelectContractions[set_ContractionSet, ids_List] := Module[{data = validateContractionSet[set], selected},
    If[FailureQ[data], Return[data]];
    selected = cgFieldCatch[selectChannelData[data, ids]];
    If[FailureQ[selected], selected, ContractionSet[selected]]
];
SelectContractions[___] := makeFailure["InvalidInput", "SelectContractions expects a ContractionSet and a list of channel IDs."];

Format[ContractionSet[data_Association], StandardForm] := Interpretation[Row[{"ContractionSet[", Length[Lookup[data, "Channels", {}]], " channels of ",
    Length[Lookup[data, "RawChannels", {}]], "]"}], ContractionSet[data]];

True
