(*
    :Title: Structured diagnostics
    :Context: VVMFTool`Private`
    :Summary: Construct consistent failure values without printing or mutating state.
    :Responsibilities: Failure tags, messages and contextual diagnostic data.
    :Dependencies: Wolfram Failure.
    :See Also: VVMFArch/step1Plan.md
*)

(*
    Summary: Create a package failure with a readable message and contextual data.
    Parameters: tag, message — strings; data — an association of diagnostic details.
    Options/defaults: data defaults to an empty association.
    Returns: Failure[tag, association].
    Effects: Pure; does not emit Message or Print output.
    Failures: Callers supply the documented argument types; details cannot override message.
    Example: FailureQ[makeFailure["InvalidInput", "Expected a word."]] returns True.
    See also: Failure; FailureQ.
*)
makeFailure[tag_String, message_String, data_Association : <||>] :=
    Failure[tag, Join[data, <|"MessageTemplate" -> message|>]];

(*
    Summary: Explicit property access for the package's value heads (final review FP-6).
    Parameters: None (definitions only).
    Options/defaults: None.
    Returns: head[data_Association][key_String] gives the value or Missing["UnknownProperty", key] for the heads without
        their own accessor; any other head[...][key] (malformed contents or a non-string key) gives Failure
        InvalidProperty. Heads with their own accessor (Field, ContractionSet, ModelOutput, DisplayDocument, ModularForm,
        QExpansionData, CoefficientResult, WeightedRepVector, ModularFormOutput, ModularFormCandidateData) keep it; the
        more specific definitions are tried first. Group has its own explicit failure (GroupObject.wl).
    Effects: Defines subvalues at load time.
    Failures: InvalidProperty.
    Example: Model[5]["ID"] is Failure["InvalidProperty", ...]; Model[<|"ID" -> "m"|>]["ID"] is "m".
    See also: makeFailure.
*)
$ValueHeads = {Field, Model, CGData, RepVector, ContractionSet, CoupledExpression, MassMatrix, ModelOutput, PythonArtifact,
    DisplayDocument, ModularForm, QExpansionData, CoefficientResult, WeightedRepVector, ModularFormOutput, ModularFormCandidateData};
Scan[Function[head,
    If[MemberQ[{Model, CGData, RepVector, CoupledExpression, MassMatrix, PythonArtifact}, head],
        head[data_Association][key_String] := Lookup[data, key, Missing["UnknownProperty", key]]];
    head[___][_] := makeFailure["InvalidProperty", "A property needs a well-formed value of this head and a string key.",
        <|"Head" -> SymbolName[head]|>]], $ValueHeads];

True
