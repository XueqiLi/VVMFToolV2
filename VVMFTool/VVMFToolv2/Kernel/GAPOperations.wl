(*
    :Title: Registered GAP group operations
    :Context: VVMFTool`Private`
    :Summary: One registry of GAP group-result operations and their coordinator rules.
    :Responsibilities: Source/generation rules, completion and recovery predicates, terminal
        failures and enrichment method lists shared by validation, workers and batches.
    :Dependencies: Diagnostics.wl.
    :See Also: ResultValidation.wl; GAPWorkers.wl; GAPJobs.wl; GroupJobs.wl; GAP/Driver.g.
*)

(* Owning modules register their operations here together with their payload validator and
   GAP dispatcher; unknown operations are rejected by validation and never launched. GAP/Driver.g
   keeps its own native dispatch list, which must name the same operations. *)
If[!AssociationQ[$GAPOperations], $GAPOperations = <||>];

$GAPOperationFields = {"Source", "GenerationStep", "CompleteQ", "RecoverySkipQ",
    "TerminalFailures", "Methods"};

(*
    Summary: Decide whether a verified candidate satisfies the whole request by envelope status.
    Parameters: data — decoded verified result; request — the operation request.
    Options/defaults: None.
    Returns: Boolean.
    Effects: Pure.
    Failures: Malformed data returns False.
    Example: statusCompleteQ[<|"Status" -> "Partial"|>, <||>] is False.
    Remarks: Default completion rule. Operations whose completeness depends on the request
        (for example requested irreps in a requested basis) register their own predicate.
    See also: operationCompleteQ; runJobBatch.
*)
statusCompleteQ[data_Association, request_Association] := Lookup[data, "Status", None] === "Complete";
statusCompleteQ[___] := False;

(*
    Summary: Decide whether a batch member need not run again after an earlier outcome.
    Parameters: result — an earlier outcome's Result: "Complete", "Partial" or a Failure.
    Options/defaults: None.
    Returns: Boolean.
    Effects: Pure.
    Failures: Other values return False, permitting a retry.
    Example: repeatSkipQ["Partial"] is True: a character algorithm cannot add rows by rerunning.
    Remarks: Default recovery rule. Timeouts, native errors and word failures remain retryable.
    See also: operationRecoverySkipQ; reduceRecoveryBatch.
*)
repeatSkipQ[result_] := MemberQ[{"Complete", "Partial"}, result] ||
    MatchQ[result, Failure["InapplicableMethod" | "InapplicableModel" | "DependencyUnavailable", _]];

(*
    Summary: Recognize a registry rule: a pure function or a package-defined function symbol.
    Parameters: rule — any value.
    Options/defaults: None.
    Returns: Boolean.
    Effects: Pure.
    Failures: System symbols such as True and None are not rules.
    Example: operationRuleQ[statusCompleteQ] is True; operationRuleQ[True] is False.
    See also: registerGAPOperation.
*)
operationRuleQ[rule_] := Head[rule] === Function ||
    (Head[rule] === Symbol && Context[rule] =!= "System`");

(*
    Summary: Validate and install one GAP operation's coordinator rules.
    Parameters: name — nonempty operation string; entry — association with exactly the fields
        Source ("New" | "Checkpoint" | "Typed" | "Import"), GenerationStep (0 or 1), CompleteQ and
        RecoverySkipQ (functions or symbols), TerminalFailures (failure tags) and Methods
        (None or a function of the request returning method names), and optionally ParallelExpansion
        (a function of an allocated parallel descriptor and the batch request returning its single-core
        child attempts; see expandParallelBatch).
    Options/defaults: Re-registering a name replaces its entry.
    Returns: The name, or InvalidOperationRegistration Failure.
    Effects: Updates $GAPOperations.
    Failures: Missing/extra fields or invalid field values leave the registry unchanged.
    Example: registerGAPOperation["Characters", entry] installs the character operation.
    Remarks: Source "New" starts from no checkpoint at generation zero; "Checkpoint" requires a
        verified source; "Typed" also accepts certified typed reconstruction data; "Import" runs
        against its accepted validation source at the imported generation.
    See also: gapOperation; operationCompleteQ; startGAPAttempt.
*)
registerGAPOperation[name_String, entry_Association] := If[
    StringLength[name] > 0 && Sort[KeyDrop[entry, "ParallelExpansion"] // Keys] === Sort[$GAPOperationFields] &&
        (!KeyExistsQ[entry, "ParallelExpansion"] || operationRuleQ[entry["ParallelExpansion"]]) &&
        MemberQ[{"New", "Checkpoint", "Typed", "Import"}, entry["Source"]] &&
        MemberQ[{0, 1}, entry["GenerationStep"]] &&
        AllTrue[{entry["CompleteQ"], entry["RecoverySkipQ"]}, operationRuleQ] &&
        ListQ[entry["TerminalFailures"]] && AllTrue[entry["TerminalFailures"], StringQ] &&
        (entry["Methods"] === None || operationRuleQ[entry["Methods"]]),
    AssociateTo[$GAPOperations, name -> entry]; name,
    makeFailure["InvalidOperationRegistration", "Invalid GAP operation registry entry.", <|"Operation" -> name|>]];
registerGAPOperation[___] := makeFailure["InvalidOperationRegistration", "Expected an operation name and registry entry."];

(*
    Summary: Read one registered GAP operation.
    Parameters: operation — any value.
    Options/defaults: None.
    Returns: Registry entry, or UnsupportedOperation Failure.
    Effects: Pure.
    Failures: Unregistered names and nonstrings.
    Example: gapOperation["Characters"]["Source"] is "Checkpoint".
    See also: registerGAPOperation; gapOperationQ.
*)
gapOperation[operation_String] := Lookup[$GAPOperations, operation,
    makeFailure["UnsupportedOperation", "The operation has no installed coordinator rules.",
        <|"Operation" -> operation|>]];
gapOperation[___] := makeFailure["UnsupportedOperation", "Expected an operation name."];

(*
    Summary: Test whether an operation is registered.
    Parameters: operation — any value.
    Options/defaults: None.
    Returns: Boolean.
    Effects: Pure.
    Failures: None.
    Example: gapOperationQ["Unregistered"] is False.
    See also: gapOperation; validateGroupResult.
*)
gapOperationQ[operation_] := StringQ[operation] && KeyExistsQ[$GAPOperations, operation];

(*
    Summary: Decide whether a verified candidate completes its request under its operation's rule.
    Parameters: data — decoded verified result; request — operation request with "operation".
    Options/defaults: None.
    Returns: Boolean; unregistered operations return False.
    Effects: Pure.
    Failures: None; a non-Boolean predicate result counts as incomplete.
    Example: a character-Partial candidate is not a winner and cannot stop its rivals.
    See also: runJobBatch; statusCompleteQ.
*)
operationCompleteQ[data_Association, request_Association] := With[
    {entry = gapOperation[Lookup[request, "operation", None]]},
    !FailureQ[entry] && TrueQ[entry["CompleteQ"][data, request]]];
operationCompleteQ[___] := False;

(*
    Summary: Decide whether an earlier outcome makes rerunning the same descriptor unnecessary.
    Parameters: operation — registered name; result — earlier outcome Result.
    Options/defaults: None.
    Returns: Boolean; unregistered operations use repeatSkipQ.
    Effects: Pure.
    Failures: None.
    Example: operationRecoverySkipQ["Characters", "Partial"] is True.
    See also: reduceRecoveryBatch; repeatSkipQ.
*)
operationRecoverySkipQ[operation_, result_] := With[{entry = gapOperation[operation]},
    TrueQ[If[FailureQ[entry], repeatSkipQ[result], entry["RecoverySkipQ"][result]]]];

(*
    Summary: Recognize a mathematical negative that makes further attempts of an operation pointless.
    Parameters: operation — registered name; result — an outcome Result.
    Options/defaults: None.
    Returns: Boolean.
    Effects: Pure.
    Failures: Unregistered operations have no terminal failures.
    Example: an invalid modular pair ends AssignModularGenerators without trying other models.
    See also: runGroupRequest.
*)
operationTerminalFailureQ[operation_, result_] := With[{entry = gapOperation[operation]},
    !FailureQ[entry] && MatchQ[result, Failure[tag_String, _] /; MemberQ[entry["TerminalFailures"], tag]]];

(*
    Summary: List the permitted native methods of an enrichment operation.
    Parameters: request — operation request, with its optional payload.
    Options/defaults: None.
    Returns: Ordered method names; {} for unregistered operations or operations without a list.
    Effects: Pure.
    Failures: None.
    Example: operationMethods[<|"operation" -> "GroupWordOrder"|>] is {"GAP"}.
    See also: groupDescriptors.
*)
operationMethods[request_Association] := With[{entry = gapOperation[Lookup[request, "operation", None]]},
    If[FailureQ[entry] || entry["Methods"] === None, {},
        Replace[entry["Methods"][request], Except[{___String}] -> {}]]];
operationMethods[___] := {};

(* Stage 1 operations. Invalid or nongenerating modular pairs are native proofs, so every
   enrichment that rechecks an assignment stops instead of retrying equivalent models. *)
With[{modular = {"InvalidModularGenerators", "NongeneratingModularPair"}, gap = Function[request, {"GAP"}]},
    Scan[registerGAPOperation[#, <|"Source" -> "New", "GenerationStep" -> 0,
        "CompleteQ" -> statusCompleteQ, "RecoverySkipQ" -> repeatSkipQ,
        "TerminalFailures" -> {}, "Methods" -> None|>] &, {"Construct", "ConstructGAP"}];
    registerGAPOperation["Characters", <|"Source" -> "Checkpoint", "GenerationStep" -> 1,
        "CompleteQ" -> statusCompleteQ, "RecoverySkipQ" -> repeatSkipQ,
        "TerminalFailures" -> {}, "Methods" -> None|>];
    registerGAPOperation["Import", <|"Source" -> "Import", "GenerationStep" -> 0,
        "CompleteQ" -> statusCompleteQ, "RecoverySkipQ" -> repeatSkipQ,
        "TerminalFailures" -> {}, "Methods" -> None|>];
    registerGAPOperation["Reconstruct", <|"Source" -> "Typed", "GenerationStep" -> 0,
        "CompleteQ" -> statusCompleteQ, "RecoverySkipQ" -> repeatSkipQ,
        "TerminalFailures" -> {}, "Methods" -> None|>];
    Scan[registerGAPOperation[#, <|"Source" -> "Typed", "GenerationStep" -> 1,
        "CompleteQ" -> statusCompleteQ, "RecoverySkipQ" -> repeatSkipQ,
        "TerminalFailures" -> modular, "Methods" -> gap|>] &,
        {"GroupElementWords", "GroupWordOrder", "AssignModularGenerators", "GeneratorPresentation",
            "CheckGeneratorMap", "Decompose"}];
    (* a table a fresh native computation does not reproduce is a proof's verdict, reported as GAP's cause *)
    registerGAPOperation["ValidateGroup", <|"Source" -> "Typed", "GenerationStep" -> 1,
        "CompleteQ" -> statusCompleteQ, "RecoverySkipQ" -> repeatSkipQ,
        "TerminalFailures" -> Join[modular, {"InvalidCharacters", "InvalidGeneratorMap"}], "Methods" -> gap|>];
    registerGAPOperation["GroupSubgroups", <|"Source" -> "Typed", "GenerationStep" -> 1,
        "CompleteQ" -> statusCompleteQ, "RecoverySkipQ" -> repeatSkipQ,
        "TerminalFailures" -> modular, "Methods" -> Function[request,
            Switch[Lookup[Lookup[request, "subgroupQuery", <||>], "kind", None],
                "ConjugacyClasses", {"GAP"}, "All", {"GAP", "ClassExpansion"},
                "Normal", {"GAP", "ClassFilter"}, _, {}]]|>]
];

True
