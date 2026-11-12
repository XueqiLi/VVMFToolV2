(*
    :Title: Explicit native GAP checkpoint restoration
    :Context: VVMFTool`Private`
    :Summary: Verify a retained group state in a fresh GAP worker without recomputation.
    :Responsibilities: Restore protocol, group correspondence and public restoration diagnostics.
    :Dependencies: CheckpointCalls.wl; GroupConstruction.wl; GAPProtocol.wl.
    :See Also: RestoreGAPState; VVMF_VerifyCheckpoint; VVMFArch/step1Plan.md.
*)

(*
    Summary: Restore one admitted checkpoint and compare an independent native reexport.
    Parameters: reference — registered verified checkpoint; capabilities — fresh GAP probe;
        options — validated common job settings; call — active ID/Directory call record.
    Options/defaults: AttemptTimeLimit includes hash checks, startup, restore and comparison;
        MemoryBudget limits the single worker. No new group algorithm or generation is run.
    Returns: Restored=True, StateID and StateGeneration report, or Failure.
    Effects: Launches/tracks/stops one owned worker, writes/removes one verification file,
        marks successful source use for the call's eventual lease release.
    Failures: Admission, native mismatch, incompatible producer, timeout/cancellation and cleanup.
        Failure never creates a claim that reconstruction was a restore.
    Example: restoreCheckpoint[reference, caps, settings, call] reuses an already computed table.
    See also: admitCheckpoint; checkpointRecord; RestoreGAPState.
*)
restoreCheckpoint[reference_String, capabilities_Association, options_Association, call_Association] := Module[
    {deadline, record, worker = None, launch, nonce = CreateUUID["restore-"], path, result,
        packet, expected, command, native, checked, cleanup = True, removed, exitTag},
    If[!ContainsAll[Keys[options], {AttemptTimeLimit, MemoryBudget}] ||
        !optionValueQ[AttemptTimeLimit, options[AttemptTimeLimit]] ||
        !IntegerQ[options[MemoryBudget]] || options[MemoryBudget] < 1 ||
        !resultFieldsQ[call, {"ID", "Directory"}] || !KeyExistsQ[$CheckpointCalls, call["ID"]] ||
        $CheckpointCalls[call["ID"]]["Directory"] =!= call["Directory"],
        Return[makeFailure["InvalidRequest", "Expected allocated restore settings and an owned call."]]];
    deadline = SessionTime[] + options[AttemptTimeLimit];
    path = FileNameJoin[{call["Directory"], nonce <> ".json"}];
    result = CheckAbort[TimeConstrained[Catch[
        progressReport[<|"Event" -> "Stage", "Phase" -> "Restoring saved GAP state"|>];
        record = checkpointRecord[reference, capabilities];
        If[FailureQ[record], Throw[record, exitTag]];
        If[SessionTime[] >= deadline, Throw[makeFailure["Timeout", "The restore deadline expired."], exitTag]];
        AbortProtect[
            launch = launchGAPWorker[capabilities,
                <|"TimeLimit" -> deadline - SessionTime[], "MemoryBytes" -> options[MemoryBudget]|>, reference];
            If[!FailureQ[launch], worker = launch["Worker"]; trackCheckpointWorker[call["Directory"], worker]]
        ];
        If[FailureQ[launch], Throw[launch, exitTag]];
        packet = awaitGAPPacket[worker, <|"type" -> "workerReady", "requestID" -> launch["Nonce"]|>];
        If[FailureQ[packet], Throw[packet, exitTag]];
        If[!compatibleGAPProducerQ[Lookup[packet, "producer", <||>], capabilities],
            Throw[makeFailure["IncompatibleCheckpoint", "The restored runtime differs from the probe."], exitTag]];
        command = "VVMF_VerifyCheckpoint(" <> gapStringLiteral[nonce] <> "," <> gapStringLiteral[path] <> ");;\n";
        checked = writeOwnedProcess[worker, command]; If[FailureQ[checked], Throw[checked, exitTag]];
        expected = Join[KeyTake[record["Native"], {"stateID", "generatorIdentity", "stateGeneration", "status"}],
            <|"requestID" -> nonce, "checkpointRequestID" -> record["Native"]["requestID"]|>];
        packet = awaitGAPPacket[worker, Join[expected, <|"type" -> "checkpointRestored"|>]];
        If[FailureQ[packet], Throw[packet, exitTag]];
        packet = awaitGAPPacket[worker, Join[expected,
            <|"type" -> "checkpointVerified", "verifiedResultPath" -> path|>]];
        If[FailureQ[packet], Throw[packet, exitTag]];
        native = readResult[path]; If[FailureQ[native], Throw[native, exitTag]];
        progressReport[<|"Event" -> "Stage", "Phase" -> "Verifying restored group"|>];
        If[canonicalJSON[native] =!= canonicalJSON[record["Native"]],
            Throw[makeFailure["InvalidCheckpoint", "The restored native group differs from its saved result."], exitTag]];
        checked = pollOwnedProcess[worker]; If[FailureQ[checked], Throw[checked, exitTag]];
        If[SessionTime[] >= deadline, Throw[makeFailure["Timeout", "The restore deadline expired before acceptance."], exitTag]];
        noteCheckpointRestored[reference];
        <|"Restored" -> True, "StateID" -> record["Data"]["StateID"],
            "StateGeneration" -> record["Data"]["StateGeneration"], "StateSource" -> "Restored"|>,
        exitTag], options[AttemptTimeLimit], makeFailure["Timeout", "Checkpoint restoration timed out."]],
        makeFailure["Cancelled", "Checkpoint restoration was cancelled."]];
    If[StringQ[worker], cleanup = closeGAPProtocol[worker, "RestoreFinished"]];
    removed = removeWriteTemporary[path];
    If[FailureQ[cleanup] || FailureQ[removed],
        makeFailure["CleanupFailed", "Restore resources were not fully released.",
            <|"Result" -> result, "WorkerCleanup" -> cleanup, "FileCleanup" -> removed|>], result]
];
restoreCheckpoint[___] := makeFailure["InvalidRequest", "Expected checkpoint, capabilities, settings and call."];

Options[RestoreGAPState] = Select[Options[BuildGroup], MemberQ[Keys[$CommonJobDefaults], First[#]] &];

(*
    Summary: Verify the group's retained GAP state in a fresh worker without reconstructing it.
    Status: Alpha.
    Parameters: group — accepted live finite-group handle.
    Options/defaults: Common job settings from configuration; no new mathematical data is requested.
        StoreGAPState=False does not delete or rewrite an already retained source checkpoint.
    Returns: Restored/StateID/StateGeneration/StateSource association, or Failure.
    Effects: Acquires/releases a cache lease, validates native correspondence and updates
        LastComputation plus last successful cache use. The mathematical group is unchanged.
    Failures: Unknown group, missing/evicted/foreign/incompatible/corrupt cache, budgets and backend
        failures are explicit. A missing workspace is not silently rebuilt by this operation.
    Example: RestoreGAPState[g]["Restored"] is True only after actual fresh GAP restoration.
    See also: CleanGAPCache; BuildGroup; BuildModularGroup; GroupElementWords.
*)
RestoreGAPState[group_Group, options : OptionsPattern[]] :=
    Block[{$GroupAcceptanceLevel = If[$GroupAcceptanceLevel === Automatic, groupAcceptanceLevel[group], $GroupAcceptanceLevel]},
        restoreGAPStateWork[group, options]];
restoreGAPStateWork[group_Group, options : OptionsPattern[]] := Module[
    {effective, accepted, capabilities, result, committed, diagnostics, patch},
    effective = resolveOperationOptions[RestoreGAPState, "RestoreGAPState", {options}];
    If[FailureQ[effective], Return[effective]];
    accepted = groupData[group]; If[FailureQ[accepted], Return[accepted]];
    If[!AssociationQ[accepted["GAPCacheMetadata"]],
        Return[makeFailure["MissingCheckpoint", "This group has no retained GAP checkpoint."]]];
    If[FileType[accepted["GAPCachePath"]] =!= File,
        Return[makeFailure["MissingCheckpoint", "The group's retained GAP workspace is no longer available."]]];
    result = withProgress[effective, "RestoreGAPState", Function[Null,
        $ProgressPartialResult = group;
        progressReport[<|"Event" -> "Stage", "Phase" -> "Checking GAP"|>];
        capabilities = CheckGAP[]; If[FailureQ[capabilities], Return[capabilities]];
        withCheckpointCall[Function[call, Module[{reference, tracked, record},
            AbortProtect[
                reference = admitCheckpoint[accepted["GAPCacheMetadata"], capabilities];
                If[!FailureQ[reference], tracked = trackCheckpointSource[call["ID"], reference]]
            ];
            If[FailureQ[reference], Return[reference]];
            If[FailureQ[tracked], Return[tracked]];
            record = checkpointRecord[reference, capabilities]; If[FailureQ[record], Return[record]];
            If[!sameGroupStateQ[record["Data"], accepted],
                Return[makeFailure["StateConflict", "The retained checkpoint does not match this group's mathematical data."]]];
            restoreCheckpoint[reference, capabilities, effective, call]
        ]]]
    ]];
    diagnostics = <|"Operation" -> "RestoreGAPState", "Status" -> If[FailureQ[result], "Failed", "Complete"],
        "StateSource" -> If[FailureQ[result], "Unavailable", "Restored"]|>;
    If[FailureQ[result], diagnostics["Failure"] = result];
    patch = <|"LastComputation" -> diagnostics|>;
    If[!FailureQ[result], patch["GAPCacheMetadata"] = Join[accepted["GAPCacheMetadata"],
        <|"LastUsed" -> Round[1000 AbsoluteTime[]]|>]];
    committed = commitGroup[group, accepted["Revision"], patch];
    If[FailureQ[committed], committed, result]
];
RestoreGAPState[___] := makeFailure["InvalidInput", "Expected a live group and restoration options."];

True
