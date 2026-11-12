(*
    :Title: Owned computational process groups
    :Context: VVMFTool`Private`
    :Summary: Track only package-launched process groups, resource usage and cleanup.
    :Responsibilities: Verified process ownership, nonblocking I/O, deadlines and RSS limits.
    :Dependencies: ProcessIO.wl; exact integer decoder; POSIX ps and kill.
    :See Also: GAPJobs.wl; VVMFArch/step1Plan.md worker ownership.
*)

(* Kernel-local ownership is not recoverable from a mathematical import or a PID alone. *)
If[!AssociationQ[$OwnedProcesses], $OwnedProcesses = <||>];
If[!AssociationQ[$OwnedProcessOutcomes], $OwnedProcessOutcomes = <||>];
If[!ValueQ[$OwnedProcessMonitor], $OwnedProcessMonitor = None];
$OwnedProcessMonitorInterval = 0.1;
(* One observation shared by the coordinator's polls and the monitor within its maximum age. *)
$ProcessSnapshotCache = None;

(*
    Summary: Enforce owned worker budgets during ordinary Wolfram evaluations.
    Parameters: None; observes the private ownership registry.
    Options/defaults: The session monitor runs every 0.1 seconds while workers exist.
    Returns: Null; terminal failures are retained for pollOwnedProcess.
    Effects: Samples one shared process snapshot and stops only over-budget owned trees.
    Failures: Inspection/ownership errors are retained without signaling an uncertain PID.
    Example: a sleeping GAP rival is timed out while the main evaluator runs RootReduce.
    Remarks: SessionSubmit is preemptive. It does not run inside PreemptProtect, and this
        is sampled enforcement, not a hard real-time memory bound. No stdout is consumed.
    See also: https://reference.wolfram.com/language/ref/SessionSubmit.html;
        https://reference.wolfram.com/language/ref/PreemptProtect.html.
*)
monitorOwnedProcesses[] := PreemptProtect[Module[
    {tokens, snapshot, owner, members, bytes, tag, cleanup, failure},
    tokens = Complement[Keys[$OwnedProcesses], Keys[$OwnedProcessOutcomes]];
    If[tokens === {}, Return[Null]];
    snapshot = sharedProcessSnapshot[];
    Do[
        owner = $OwnedProcesses[token];
        members = If[FailureQ[snapshot], snapshot, ownedProcessMembers[owner, snapshot]];
        If[FailureQ[members],
            AssociateTo[$OwnedProcessOutcomes, token -> members],
            bytes = Total[(#["ResidentBytes"] & /@ members)];
            owner["ObservedDescendants"] = KeyTake[#, {"PID", "Started"}] & /@ members;
            AssociateTo[$OwnedProcesses, token -> owner];
            tag = Which[SessionTime[] >= owner["Deadline"], "Timeout",
                bytes > owner["MemoryBytes"], "MemoryLimit", True, None];
            If[tag =!= None,
                cleanup = stopOwnedProcess[token, tag];
                failure = makeFailure[tag, "The worker exceeded its allocated resources.",
                    <|"ResidentBytes" -> bytes, "Cleanup" -> cleanup,
                        "StandardOutput" -> owner["StandardOutput"],
                        "StandardError" -> owner["StandardError"]|>];
                AssociateTo[$OwnedProcessOutcomes, token -> failure]
            ]
        ],
        {token, tokens}
    ];
    Null
]];

(*
    Summary: Install the single package-owned preemptive resource monitor if needed.
    Parameters: None.
    Options/defaults: Uses $OwnedProcessMonitorInterval seconds in the current kernel.
    Returns: True or ResourceMonitorUnavailable Failure.
    Effects: Creates one session TaskObject; does not create another Wolfram kernel.
    Failures: Failed task creation is reported so a worker is never launched unmonitored.
    Example: repeated calls reuse the same task until the last worker is released.
    See also: monitorOwnedProcesses; stopOwnedProcess.
*)
ensureOwnedProcessMonitor[] := PreemptProtect[Module[{task},
    If[Head[$OwnedProcessMonitor] === TaskObject, Return[True]];
    task = Check[SessionSubmit[ScheduledTask[monitorOwnedProcesses[],
        Quantity[$OwnedProcessMonitorInterval, "Seconds"]]], $Failed];
    If[Head[task] =!= TaskObject,
        Return[makeFailure["ResourceMonitorUnavailable", "Cannot monitor worker resources."]]];
    $OwnedProcessMonitor = task;
    True
]];

(*
    Summary: Read process IDs, ancestry, groups, resident memory and start identities.
    Parameters: None.
    Options/defaults: Requires POSIX /bin/ps; RSS is reported in bytes.
    Returns: List of associations, or ProcessInspectionFailed Failure.
    Effects: Runs one read-only ps query without a shell; reads no process arguments.
    Failures: Missing tool, nonzero status or malformed output.
    Example: select a known owned PID and check that its PGID equals that PID.
    See also: startOwnedProcess; ownedProcessMembers.
*)
processSnapshot[] := Module[{result, rows, fields, numbers},
    If[!FileExistsQ["/bin/ps"] || !FileExistsQ["/bin/kill"],
        Return[makeFailure["CapabilityUnavailable", "Owned worker groups require POSIX process tools."]]];
    result = RunProcess[{"/bin/ps", "-axo", "pid=,ppid=,pgid=,rss=,lstart="}];
    If[!AssociationQ[result] || result["ExitCode"] =!= 0,
        Return[makeFailure["ProcessInspectionFailed", "Cannot inspect owned worker resources."]]];
    rows = StringSplit[StringTrim[result["StandardOutput"]], "\n"];
    fields = StringSplit /@ rows;
    If[!AllTrue[fields, Length[#] >= 9 &&
        AllTrue[Take[#, 4], StringMatchQ[#, DigitCharacter ..] &] &],
        Return[makeFailure["ProcessInspectionFailed", "Malformed process resource data."]]];
    Map[Function[row,
        numbers = FromDigits /@ Take[row, 4];
        <|"PID" -> numbers[[1]], "PPID" -> numbers[[2]], "PGID" -> numbers[[3]],
            "ResidentBytes" -> 1024 numbers[[4]], "Started" -> StringRiffle[Drop[row, 4]]|>
    ], fields]
];

(*
    Summary: Reuse one recent process observation across polls in the same sampling interval.
    Parameters: maxAge — seconds, default $OwnedProcessMonitorInterval.
    Options/defaults: A snapshot older than maxAge, or none, is refreshed with processSnapshot.
    Returns: processSnapshot list, or its Failure (failures are not cached).
    Effects: Updates $ProcessSnapshotCache; starting or stopping an owned process invalidates it.
    Failures: As processSnapshot.
    Example: polling four active workers in one coordinator cycle runs /bin/ps once.
    Remarks: Budget enforcement is sampled at the same interval as the monitor; ownership checks
        at launch and cleanup still take fresh observations.
    See also: processSnapshot; pollOwnedProcess; monitorOwnedProcesses.
*)
sharedProcessSnapshot[maxAge_ : $OwnedProcessMonitorInterval] := Module[{now = SessionTime[], snapshot},
    If[AssociationQ[$ProcessSnapshotCache] && now - $ProcessSnapshotCache["Time"] < maxAge,
        Return[$ProcessSnapshotCache["Snapshot"]]];
    snapshot = processSnapshot[];
    If[!FailureQ[snapshot], $ProcessSnapshotCache = <|"Time" -> now, "Snapshot" -> snapshot|>];
    snapshot
];

(*
    Summary: Find an owned worker's process-group members and observed descendants.
    Parameters: owner — verified PID/PGID/Started record; snapshot — processSnapshot result.
    Options/defaults: None.
    Returns: Member records, or OwnershipConflict when the original PID identifies a new process.
    Effects: Pure; follows ancestry to a fixed point.
    Failures: Caller supplies validated ownership/snapshot records; a reused leader PID is rejected.
    Example: a child in the worker's process group is included even after its parent exits.
    Remarks: Backend adapters must not detach children into unrelated sessions. Descendants
        observed while attached are included even if a child creates another process group.
    See also: processSnapshot; stopOwnedProcess.
*)
ownedProcessMembers[owner_Association, snapshot_List] := Module[
    {leader, ids, previous = {}, members, retained},
    leader = SelectFirst[snapshot, #["PID"] === owner["PID"] &, Missing["Exited"]];
    If[!MissingQ[leader] && (leader["Started"] =!= owner["Started"] ||
        leader["PGID"] =!= owner["PGID"] || leader["PPID"] =!= owner["PPID"]),
        Return[makeFailure["OwnershipConflict", "The original PID no longer identifies this worker."]]];
    members = Select[snapshot, #["PGID"] === owner["PGID"] &];
    retained = Lookup[owner, "ObservedDescendants", {}];
    members = Union[members, Select[snapshot, Function[row,
        AnyTrue[retained, #["PID"] === row["PID"] && #["Started"] === row["Started"] &]]]];
    ids = Union[Append[(#["PID"] & /@ members), owner["PID"]]];
    While[ids =!= previous,
        previous = ids;
        ids = Union[ids, #["PID"] & /@ Select[snapshot, MemberQ[ids, #["PPID"]] &]]
    ];
    Select[snapshot, MemberQ[ids, #["PID"]] &]
];

(*
    Summary: Start a worker and verify that Wolfram assigned it an isolated process group.
    Parameters: arguments — nonempty command/argument strings; budget — TimeLimit in seconds
        (positive or Infinity) and positive integral MemoryBytes.
    Options/defaults: None. Arguments are passed directly without a shell.
    Returns: Opaque owned-process token, or Failure.
    Effects: Starts one process, opens streams and records its observed group/start identity.
    Failures: Bad budgets, unsupported ownership, launch/inspection failure; failed launch
        registration terminates the original process before sending any mathematical commands.
    Example: startOwnedProcess[{"/bin/cat"}, <|"TimeLimit" -> 10, "MemoryBytes" -> 10^8|>].
    Remarks: StartProcess's PID is read from its returned metadata, then verified with ps.
        No user-provided PID becomes an owned worker. GAP is launched with startup files
        disabled and receives computational commands only after this function succeeds.
    See also: writeOwnedProcess; pollOwnedProcess; stopOwnedProcess.
*)
startOwnedProcess[arguments_List, budget_Association] := PreemptProtect[Module[
    {process, metadata, snapshot, leader, token, started, limit, memory, monitor},
    limit = Lookup[budget, "TimeLimit", None]; memory = Lookup[budget, "MemoryBytes", None];
    If[arguments === {} || !AllTrue[arguments, StringQ] ||
        !(limit === Infinity || (NumberQ[limit] && TrueQ[Im[limit] == 0] && TrueQ[limit > 0])) ||
        !IntegerQ[memory] || memory < 1,
        Return[makeFailure["InvalidProcessRequest", "Expected arguments and positive worker budgets."]]];
    started = SessionTime[];
    process = Check[StartProcess[arguments], $Failed];
    If[Head[process] =!= ProcessObject,
        Return[makeFailure["ProcessStartFailed", "Cannot start the owned worker."]]];
    ProcessConnection[process, "StandardInput"];
    metadata = First[process];
    snapshot = processSnapshot[]; $ProcessSnapshotCache = None;
    If[FailureQ[snapshot] || !AssociationQ[metadata] || !IntegerQ[Lookup[metadata, "PID", None]],
        KillProcess[process];
        Return[makeFailure["ProcessInspectionFailed", "Cannot establish worker ownership."]]];
    leader = SelectFirst[snapshot, #["PID"] === metadata["PID"] &, Missing["Exited"]];
    If[MissingQ[leader] || leader["PID"] <= 1 || leader["PGID"] =!= leader["PID"] ||
        leader["PPID"] =!= $ProcessID,
        KillProcess[process];
        Return[makeFailure["ProcessOwnershipFailed", "The worker did not enter its own process group."]]];
    token = CreateUUID["worker-"];
    AssociateTo[$OwnedProcesses, token -> Join[leader, <|"Process" -> process,
        "Deadline" -> started + limit, "MemoryBytes" -> memory,
        "StandardOutput" -> "", "StandardError" -> "", "Arguments" -> arguments,
        "ObservedDescendants" -> {}|>]];
    monitor = ensureOwnedProcessMonitor[];
    If[FailureQ[monitor], stopOwnedProcess[token, "MonitorUnavailable"]; Return[monitor]];
    token
]];
startOwnedProcess[___] := makeFailure["InvalidProcessRequest", "Expected worker arguments and budget."];

(*
    Summary: Send bounded coordinator commands to a registered worker.
    Parameters: token — owned-process token; text — literal main-input commands.
    Options/defaults: None; at most 1 MiB per send, with source/data normally in owned files.
    Returns: True, or Failure for an unknown/stopped worker or failed write.
    Effects: Writes only that worker's standard input.
    Failures: No commands are sent for invalid ownership/type/size.
    Example: writeOwnedProcess[token, "QUIT_GAP(0);\n"].
    See also: startOwnedProcess; GAP/Driver.g.
*)
writeOwnedProcess[token_String, text_String] := PreemptProtect[Module[{owner, result},
    If[KeyExistsQ[$OwnedProcessOutcomes, token], Return[$OwnedProcessOutcomes[token]]];
    owner = Lookup[$OwnedProcesses, token, Missing["UnknownWorker"]];
    If[MissingQ[owner] || StringLength[text] > 2^20 ||
        ProcessStatus[owner["Process"]] =!= "Running",
        Return[makeFailure["InvalidWorker", "The worker is unavailable or the command is too large."]]];
    result = Check[WriteString[owner["Process"], text], $Failed];
    If[result === $Failed, makeFailure["ProcessWriteFailed", "Cannot write to the worker."], True]
]];
writeOwnedProcess[___] := makeFailure["InvalidWorker", "Expected an owned worker and command text."];

(*
    Summary: Stop all currently owned group members and observed descendants.
    Parameters: token — owned-process token; reason — diagnostic reason string.
    Options/defaults: None; cleanup uses immediate termination after accepted checkpoints are safe.
    Returns: Cleanup report or Failure; unknown/already released tokens return an empty report.
    Effects: Verifies identity, signals the owned group and individually observed detached
        descendants, releases Wolfram streams and removes the private ownership record.
    Failures: Inspection or ownership conflict leaves the record intact for explicit recovery.
    Example: stopOwnedProcess[token, "Cancelled"] never selects workers by executable name.
    Remarks: No mathematical state is saved during forced cleanup. The coordinator retains
        the last verified generation and calls this only after winner publication when racing.
    See also: ownedProcessMembers; pollOwnedProcess.
*)
stopOwnedProcess[token_String, reason_String] := PreemptProtect[Module[
    {owner, snapshot, members, groups, direct, commands, results, errors, deadline},
    owner = Lookup[$OwnedProcesses, token, Missing["UnknownWorker"]];
    KeyDropFrom[$OwnedProcessOutcomes, token];
    If[MissingQ[owner], Return[<|"Stopped" -> {}, "Reason" -> reason|>]];
    snapshot = processSnapshot[];
    If[FailureQ[snapshot], Return[snapshot]];
    members = ownedProcessMembers[owner, snapshot];
    If[FailureQ[members], Return[members]];
    groups = If[AnyTrue[members, #["PGID"] === owner["PGID"] &], {owner["PGID"]}, {}];
    direct = #["PID"] & /@ Select[members, #["PGID"] =!= owner["PGID"] &];
    commands = Join[({"/bin/kill", "-KILL", "-" <> ToString[#]} & /@ groups),
        ({"/bin/kill", "-KILL", ToString[#]} & /@ Reverse[direct])];
    results = RunProcess /@ commands;
    (* A worker may exit between inspection and the signal. Verify surviving members
       rather than treating every 'no such process' response as a cleanup failure. *)
    deadline = SessionTime[] + 1;
    errors = members;
    While[errors =!= {} && SessionTime[] < deadline,
        snapshot = processSnapshot[];
        If[FailureQ[snapshot], Break[]];
        errors = Select[snapshot, Function[row, row["ResidentBytes"] > 0 &&
            AnyTrue[members, #["PID"] === row["PID"] && #["Started"] === row["Started"] &]]];
        If[errors =!= {}, Pause[0.01]]
    ];
    If[FailureQ[snapshot], Return[snapshot]];
    If[errors =!= {},
        Return[makeFailure["ProcessCleanupFailed", "Owned workers remain after termination.",
            <|"Processes" -> errors, "Diagnostics" -> results|>]]];
    KillProcess[owner["Process"]];
    KeyDropFrom[$OwnedProcesses, token]; $ProcessSnapshotCache = None;
    If[Length[$OwnedProcesses] === 0 && Head[$OwnedProcessMonitor] === TaskObject,
        TaskRemove[$OwnedProcessMonitor]; $OwnedProcessMonitor = None];
    <|"Stopped" -> (#["PID"] & /@ members), "Reason" -> reason|>
]];
stopOwnedProcess[___] := makeFailure["InvalidWorker", "Expected worker token and cleanup reason."];

(*
    Summary: Read available output and enforce one worker allocation's time and resident-memory cap.
    Parameters: token — owned token; snapshot — optional shared processSnapshot list.
    Options/defaults: snapshot defaults to Automatic, using sharedProcessSnapshot (at most one
        /bin/ps observation per monitor interval across all polls).
    Returns: Running/Finished report with new output, RSS and exit code, or resource/process Failure.
    Effects: Drains stdout/stderr, retains only the last 1 MiB of each diagnostic stream;
        stops the owned tree on timeout or memory overrun.
    Failures: Unknown worker, failed resource observation, stale ownership or exceeded budget.
    Example: a timed-out sleeping worker yields Failure["Timeout", ...] after tree cleanup.
    Remarks: RSS is sampled both here and by the preemptive session monitor. Detection is
        delayed by the sampling interval and nonpreemptible kernel operations. GAP's -K
        limit separately bounds its workspace. Explicit cleanup releases retained failures.
    See also: processSnapshot; readProcessOutput; stopOwnedProcess.
*)
pollOwnedProcess[token_String, snapshot_ : Automatic] := PreemptProtect[Module[
    {owner, observed, members, bytes, chunk, report, tag, cleanup, finished, combined},
    If[KeyExistsQ[$OwnedProcessOutcomes, token], Return[$OwnedProcessOutcomes[token]]];
    owner = Lookup[$OwnedProcesses, token, Missing["UnknownWorker"]];
    If[MissingQ[owner], Return[makeFailure["InvalidWorker", "Unknown owned worker."]]];
    observed = If[snapshot === Automatic, sharedProcessSnapshot[], snapshot];
    If[FailureQ[observed], Return[observed]];
    If[!ListQ[observed], Return[makeFailure["ProcessInspectionFailed", "Invalid process snapshot."]]];
    members = ownedProcessMembers[owner, observed];
    If[FailureQ[members], Return[members]];
    bytes = Total[(#["ResidentBytes"] & /@ members)];
    owner["ObservedDescendants"] = KeyTake[#, {"PID", "Started"}] & /@ members;
    chunk = readProcessOutput[owner["Process"]];
    combined = owner["StandardOutput"] <> chunk[[1]];
    owner["StandardOutput"] = StringTake[combined, -Min[StringLength[combined], 2^20]];
    combined = owner["StandardError"] <> chunk[[2]];
    owner["StandardError"] = StringTake[combined, -Min[StringLength[combined], 2^20]];
    AssociateTo[$OwnedProcesses, token -> owner];
    tag = Which[SessionTime[] >= owner["Deadline"], "Timeout",
        bytes > owner["MemoryBytes"], "MemoryLimit", True, None];
    If[tag =!= None,
        cleanup = stopOwnedProcess[token, tag];
        Return[makeFailure[tag, "The worker exceeded its allocated resources.",
            <|"ResidentBytes" -> bytes, "StandardOutput" -> owner["StandardOutput"],
                "StandardError" -> owner["StandardError"], "Cleanup" -> cleanup|>]]];
    finished = ProcessStatus[owner["Process"]] =!= "Running";
    report = <|"Status" -> If[finished, "Finished", "Running"], "ResidentBytes" -> bytes,
        "StandardOutput" -> chunk[[1]], "StandardError" -> chunk[[2]],
        "ExitCode" -> If[finished, ProcessInformation[owner["Process"], "ExitCode"], None]|>;
    report
]];
pollOwnedProcess[___] := makeFailure["InvalidWorker", "Expected an owned worker token."];

True
