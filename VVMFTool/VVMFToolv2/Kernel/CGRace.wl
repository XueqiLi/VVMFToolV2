(*
    :Title: Concurrent Method -> Automatic CG methods (race of the Wolfram routes in a session pool of subkernels)
    :Context: VVMFTool`Private`
    :Summary: Run the Wolfram members of one CG batch at the same time in Wolfram subkernels; the main kernel
        finishes and validates each returned result, the first validated bundle wins and the rivals are aborted.
    :Responsibilities: cgRaceRequest (values only), cgRaceJob (subkernel side), the session pool (cgNoRelaunch,
        cgProcessStart, cgKillPoolProcess, cgPoolKernelsAlive, cgPoolRecord, cgPoolEnsure, CloseCGPool, cgPoolAbort,
        cgPoolHealth), cgRaceBatch (coordinator).
    :Dependencies: CGData.wl (cgRouteSpaces, cgFinishRoute, cgAttemptDescriptors); CGLinear.wl
        (cgArithmeticFromField); Parallel` (LaunchKernels, ParallelSubmit, AbortKernels, CloseKernels).
    :See Also: VVMFArch/implementation/cgParallelPlan.md; step4Status.md (D-S4-5).
*)

(* The pool lives for the session (cgParallelPlan.md §3.3): VVMFUse calls CacheCG once per pair. *)
If[!AssociationQ[$CGPool], $CGPool = <|"Kernels" -> {}, "PIDs" -> <||>, "Directory" -> None, "Baseline" -> 0, "Check" -> False|>];

(* Seconds a finished-or-not member may overrun its limit before the coordinator records a timeout, and the grace
   after an abort before an unresponsive kernel is closed. *)
$CGRaceGrace = 30;
$CGRaceAbortGrace = 10;
(* Poll interval of the coordinator (seconds). *)
$CGRacePoll = 0.2;

(*
    Summary: The request a race subkernel receives: values only, without the live context or the stores.
    Parameters: request — from makeCGRequest.
    Options/defaults: None.
    Returns: The request without "Context", with "Snapshot" reduced to the fields the routes read, and
        "CyclotomicHints" -> this kernel's hints for the entries of the participating variants.
    Effects: Pure.
    Failures: None.
    Example: KeyExistsQ[cgRaceRequest[request], "Context"] is False.
    Remarks: The routes read Order, generator names, subgroup data and representations of the snapshot (subgroupCG
        reads every irrep's variant); the CG store, native envelope and representation cache stay in the main kernel
        (cgParallelPlan.md N2).
    See also: cgRaceJob; cgRouteSpaces.
*)
cgRaceRequest[request_Association] := Join[KeyDrop[request, "Context"],
    <|"Snapshot" -> KeyTake[request["Snapshot"], {"Order", "GeneratorNames", "Generators", "SubgroupData", "Representations",
        "StateID", "GroupIdentity", "CharacterData"}],
        (* the main kernel's cyclotomic hints for the participating entries (a subkernel has no decoder history) *)
        "CyclotomicHints" -> KeyTake[$CyclotomicHints, DeleteDuplicates[Flatten[Lookup[Values[Select[request["Variants"], AssociationQ]],
            "Matrices", {}]]]]|>];

(*
    Summary: One race member, evaluated in a pool subkernel.
    Parameters: request — cgRaceRequest; target; method; limit — seconds; memory — bytes.
    Options/defaults: None.
    Returns: cgRouteSpaces result, or Failure Timeout/MemoryLimit.
    Effects: Registers the request's cyclotomic hints in the subkernel (each is proved before use); otherwise
        computation only (the pool kernel never publishes or writes the ledger).
    Failures: Timeout; MemoryLimit; the route's failures.
    Example: cgRaceJob[cgRaceRequest[r], t, "GeneratorEquations", 600, 2^30]["Kind"] is "Spaces".
    See also: cgRaceBatch; cgRouteSpaces.
*)
cgRaceJob[request_Association, target_String, method_String, limit_, memory_Integer] := (
    KeyValueMap[registerCyclotomicHint[#1, #2["Order"], #2["Coefficients"]] &, Lookup[request, "CyclotomicHints", <||>]];
    MemoryConstrained[
        TimeConstrained[cgRouteSpaces[request, target, method], limit,
            makeFailure["Timeout", "The CG attempt exceeded AttemptTimeLimit.", <|"Method" -> method|>]],
        memory, makeFailure["MemoryLimit", "The CG attempt exceeded its memory share.", <|"Method" -> method|>]]);

(*
    Summary: Evaluate with the Parallel framework's relaunch of failed kernels switched off.
    Parameters: expr — held expression.
    Options/defaults: None.
    Returns: expr's value.
    Effects: Blocks Parallel`Settings`$RelaunchFailedKernels to False.
    Failures: None.
    Example: cgNoRelaunch[AbortKernels[]] never starts a bare replacement kernel.
    Remarks: Otherwise a pool kernel that dies, or that does not acknowledge an abort within the framework's 3 s, is
        "resurrected" as a bare kernel without the package; that foreign kernel would disable the race for the rest of
        the session and survive CloseCGPool (implementation review F1). The pool replaces lost kernels itself
        (cgPoolEnsure).
    See also: cgPoolAbort; cgPoolHealth; cgRaceBatch.
*)
SetAttributes[cgNoRelaunch, HoldAll];
cgNoRelaunch[expr_] := Block[{Parallel`Settings`$RelaunchFailedKernels = False}, expr];

(*
    Summary: The start time of a process as ps reports it, or None.
    Parameters: pid — process ID.
    Options/defaults: None.
    Returns: String (ps lstart) or None when no such process runs.
    Effects: Runs ps.
    Failures: None.
    Example: StringQ[cgProcessStart[$ProcessID]] is True.
    See also: cgKillPoolProcess; cgPoolEnsure.
*)
cgProcessStart[pid_Integer] := Module[{out = Quiet[RunProcess[{"ps", "-o", "lstart=", "-p", ToString[pid]}]]},
    If[AssociationQ[out] && out["ExitCode"] === 0 && StringTrim[out["StandardOutput"]] =!= "", StringTrim[out["StandardOutput"]], None]];
cgProcessStart[_] := None;

(*
    Summary: Kill the process of a pool kernel that left the pool, if it still runs.
    Parameters: record — the pool's <|"PID", "Started", ...|> record of that kernel.
    Options/defaults: None.
    Returns: True when a process was killed, otherwise False.
    Effects: kill -9, only when the PID still runs a WolframKernel whose start time equals the recorded one (a reused
        PID is never killed).
    Failures: None.
    Example: after a pool kernel was closed for not answering, its surviving process is killed.
    See also: cgPoolKernelsAlive; cgProcessStart.
*)
cgKillPoolProcess[record_Association] := Module[{pid = Lookup[record, "PID", None], command},
    If[!IntegerQ[pid] || !StringQ[Lookup[record, "Started", None]] || cgProcessStart[pid] =!= record["Started"], Return[False]];
    command = Quiet[RunProcess[{"ps", "-o", "comm=", "-p", ToString[pid]}]];
    If[!AssociationQ[command] || !StringContainsQ[command["StandardOutput"], "WolframKernel"], Return[False]];
    Quiet[RunProcess[{"kill", "-9", ToString[pid]}]];
    True];
cgKillPoolProcess[_] := False;

(*
    Summary: The live kernels of the pool.
    Parameters: None.
    Options/defaults: None.
    Returns: List of kernel objects that are still running.
    Effects: Drops closed kernels from the pool record, kills a dropped kernel's process if it survived
        (cgKillPoolProcess), and rewrites the session file when the pool changed.
    Failures: None.
    Example: cgPoolKernelsAlive[] is {} before the first race.
    See also: cgPoolEnsure.
*)
cgPoolKernelsAlive[] := Module[{alive = Intersection[$CGPool["Kernels"], Kernels[]], gone},
    gone = Complement[Keys[$CGPool["PIDs"]], ToString /@ alive];
    Scan[cgKillPoolProcess[$CGPool["PIDs"][#]] &, gone];
    $CGPool["Kernels"] = Select[$CGPool["Kernels"], MemberQ[alive, #] &];
    $CGPool["PIDs"] = KeyTake[$CGPool["PIDs"], ToString /@ $CGPool["Kernels"]];
    If[gone =!= {}, cgPoolRecord[]];
    $CGPool["Kernels"]];

(*
    Summary: Write the session file listing the pool's kernel processes, for a sweep after the main kernel is killed.
    Parameters: None.
    Options/defaults: None.
    Returns: The file path, or None when the pool is empty (the file is removed).
    Effects: Writes or removes $TemporaryDirectory/vvmf-session-<main PID>.json (PID and ps start time per kernel).
    Failures: None (a write failure leaves no file; the race does not depend on it).
    Example: after a race the file lists one PID per pool kernel.
    Remarks: Tools/sweep-sessions.py kills a listed PID only while it is still a WolframKernel with the recorded start
        time whose parent is gone. A kernel that exits without CloseCGPool leaves its file behind (its subkernels end
        with it); the sweep removes such files.
    See also: cgPoolEnsure; CloseCGPool.
*)
cgPoolRecord[] := Module[{file = FileNameJoin[{$TemporaryDirectory, "vvmf-session-" <> ToString[$ProcessID] <> ".json"}]},
    If[$CGPool["PIDs"] === <||>, Quiet[DeleteFile[file]]; Return[None]];
    (* an unknown start time is JSON null (None would make the export fail and leave no file); the sweep never kills
       an entry without a start time *)
    Quiet[Export[file, <|"MainPID" -> $ProcessID, "MainStarted" -> cgProcessStart[$ProcessID], "Kernels" -> Values[$CGPool["PIDs"]]|> /. None -> Null, "RawJSON"]];
    file];

(*
    Summary: A pool of at least n initialized subkernels.
    Parameters: n — kernels wanted (positive integer).
    Options/defaults: None.
    Returns: List of pool kernels (at least n), or Failure.
    Effects: Runs the deferred health check after an abort (cgPoolHealth). Launches subkernels; each loads the
        package from this kernel's package root, uses one library thread, and points its export ledger and cache
        directory at the pool's temporary directory (never the user's ApplicationData). Records the kernels' PIDs and
        start times (cgPoolRecord). Launch, package load and registration are one unit: an abort in between (the
        caller's TimeConstrained) closes the kernels launched so far, so none is left outside the pool.
    Failures: PoolUnavailable when other (foreign) parallel kernels are running, a launch fails, or the package does
        not load in a new kernel; the kernels launched by this call are closed again.
    Example: Length[cgPoolEnsure[2]] >= 2.
    Remarks: ParallelSubmit schedules on any running kernel, so a race requires that every running kernel is a pool
        kernel; otherwise the caller runs the batch sequentially.
    See also: cgRaceBatch; CloseCGPool.
*)
cgPoolEnsure[n_Integer?Positive] := cgNoRelaunch[Module[{alive = cgPoolKernelsAlive[], launched = {}, init, dir, registered = False},
    If[!SubsetQ[alive, Kernels[]],
        Return[makeFailure["PoolUnavailable", "Other parallel kernels are running; the CG race needs its own pool."], Module]];
    (* after an abort every kernel must answer before it is used again *)
    If[TrueQ[$CGPool["Check"]], cgPoolHealth[]; alive = cgPoolKernelsAlive[]];
    If[Length[alive] >= n, Return[alive, Module]];
    dir = $CGPool["Directory"];
    If[!StringQ[dir] || !DirectoryQ[dir], dir = CreateDirectory[]; $CGPool["Directory"] = dir];
    WithCleanup[
        launched = Quiet[LaunchKernels[n - Length[alive]]];
        If[!ListQ[launched] || launched === {} || Length[launched] < n - Length[alive],
            Return[makeFailure["PoolUnavailable", "The CG race could not launch its subkernels."], Module]];
        With[{init0 = FileNameJoin[{$PackageRoot, "Kernel", "init.m"}], ledger = FileNameJoin[{dir, "ExportLedger"}],
                cache = FileNameJoin[{dir, "GAPCache"}]},
            init = Quiet[ParallelEvaluate[
                Module[{loaded = Get[init0]},
                    Quiet[SetSystemOptions["ParallelOptions" -> {"ParallelThreadNumber" -> 1}]];
                    VVMFTool`Private`$ExportLedgerDirectory = ledger;
                    VVMFTool`Private`$Configuration[CacheDirectory] = cache;
                    {TrueQ[loaded], $ProcessID, MemoryInUse[]}],
                launched]]];
        If[!ListQ[init] || Length[init] =!= Length[launched] || !AllTrue[init, MatchQ[#, {True, _Integer, _Integer}] &],
            Return[makeFailure["PoolUnavailable", "The package did not load in a CG race subkernel.", <|"Results" -> Short[init]|>], Module]];
        $CGPool["Kernels"] = Join[alive, launched];
        MapThread[($CGPool["PIDs"][ToString[#1]] = <|"PID" -> #2[[2]], "Started" -> cgProcessStart[#2[[2]]],
            "Launched" -> DateString["ISODateTime"]|>) &, {launched, init}];
        registered = True,
        (* a launch that did not end in registration (failure or abort) leaves no kernel behind *)
        If[!registered && ListQ[launched] && launched =!= {}, Quiet[CloseKernels[launched]]]];
    $CGPool["Baseline"] = Max[$CGPool["Baseline"], Max[init[[All, 3]]]];
    cgPoolRecord[];
    $CGPool["Kernels"]
]];

(*
    Summary: Close the session pool of CG race subkernels.
    Parameters: None.
    Options/defaults: None.
    Returns: <|"Closed" -> number of kernels closed|>.
    Effects: Closes the pool's subkernels (killing a process that survives), removes the pool's temporary directory and
        the session file. Kernels the pool did not launch are not touched.
    Failures: None.
    Example: CloseCGPool[] after a CacheCG call with Method -> Automatic closes the race kernels.
    See also: CacheCG; CGCoefficients.
*)
CloseCGPool[] := cgNoRelaunch[Module[{alive = cgPoolKernelsAlive[], records = $CGPool["PIDs"]},
    If[alive =!= {}, Quiet[CloseKernels[alive]]];
    Scan[cgKillPoolProcess, Values[records]];
    If[StringQ[$CGPool["Directory"]] && DirectoryQ[$CGPool["Directory"]], Quiet[DeleteDirectory[$CGPool["Directory"], DeleteContents -> True]]];
    $CGPool = <|"Kernels" -> {}, "PIDs" -> <||>, "Directory" -> None, "Baseline" -> 0, "Check" -> False|>;
    cgPoolRecord[];
    <|"Closed" -> Length[alive]|>
]];
CloseCGPool[___] := makeFailure["InvalidInput", "CloseCGPool takes no arguments."];

(*
    Summary: Abort every running pool job.
    Parameters: None.
    Options/defaults: None.
    Returns: Null.
    Effects: AbortKernels on the pool, without the framework's relaunch of failed kernels (cgNoRelaunch); a kernel that
        does not acknowledge within the framework's 3 s is closed by the framework, dropped from the pool and its
        process killed (cgPoolKernelsAlive). Marks the pool for a health check before its next use (cgPoolHealth).
    Failures: None.
    Example: after a won race the rivals' jobs are aborted and the next race first checks every kernel.
    Remarks: This runs in the cleanup of an aborted evaluation (outer TimeConstrained, user abort), where a kernel
        cannot be asked to answer; the check is therefore deferred to cgPoolEnsure. Each unresponsive kernel adds up to
        3 s to the cleanup.
    See also: cgPoolHealth; cgRaceBatch.
*)
cgPoolAbort[] := cgNoRelaunch[If[cgPoolKernelsAlive[] =!= {}, Quiet[AbortKernels[]]; $CGPool["Check"] = True; cgPoolKernelsAlive[]];];

(*
    Summary: Make sure each pool kernel answers; drop the ones that do not.
    Parameters: None.
    Options/defaults: $CGRaceAbortGrace seconds per kernel.
    Returns: List of kernels that were closed because they did not answer.
    Effects: A kernel that does not answer within the grace period is closed, dropped from the pool and its process
        killed if it survives (cgPoolKernelsAlive), so cgPoolEnsure launches a fresh one. Clears the pool's check mark.
    Failures: None.
    Example: after a won race every rival's kernel answers 1 again and none is closed.
    See also: cgPoolAbort; cgPoolEnsure.
*)
cgPoolHealth[] := cgNoRelaunch[Module[{dead = {}},
    Do[If[TimeConstrained[Quiet[ParallelEvaluate[1, k]], $CGRaceAbortGrace, $Failed] =!= 1,
            AppendTo[dead, k]; Quiet[CloseKernels[{k}]]],
        {k, cgPoolKernelsAlive[]}];
    $CGPool["Check"] = False;
    cgPoolKernelsAlive[];
    dead
]];

(*
    Summary: Race the Wolfram members of one batch for one target.
    Parameters: request — full request; target; attempts — the batch's allocated descriptors (Wolfram methods);
        limit — AttemptTimeLimit seconds.
    Options/defaults: None.
    Returns: <|"Bundle" -> validated bundle or None, "Outcomes" -> per-method outcomes|>, or Failure PoolUnavailable
        (the caller then runs the batch sequentially).
    Effects: Submits one job per member to the pool and polls them; each returned result is finished and validated
        in this kernel (cgFinishRoute with local False, within the member's remaining time plus $CGRaceGrace), so a
        wrong, malformed or late result never wins; a failure or a rejected result never stops a rival. On every exit
        (winner, all failed, outer TimeConstrained, user abort) the running jobs are aborted (cgPoolAbort); a kernel
        that then does not answer is replaced before the next race (cgPoolHealth).
    Failures: PoolUnavailable.
    Example: with a slow and a fast route the fast one's bundle is returned and the slow one is recorded
        StoppedAfterValidatedWinner.
    Remarks: Each member runs under TimeConstrained (limit) and MemoryConstrained (its share of MemoryBudget after
        the pool kernels' measured baseline) in its subkernel; the coordinator also records a Timeout for a member
        that has not returned $CGRaceGrace seconds after its limit. A kernel that dies has its job requeued on another
        pool kernel by the Parallel framework (no replacement kernel is started; cgNoRelaunch). Members that finished
        but were not examined before the winner was accepted are recorded FinishedAfterValidatedWinner. Aborting the
        pool also cancels any other ParallelSubmit job queued on the pool kernels.
    See also: cgBundleByMethod; cgRaceJob; cgPoolEnsure.
*)
cgRaceBatch[request_Association, target_String, attempts_List, limit_] := cgNoRelaunch[Module[
    {kernels, race, jobs = <||>, outcomes = <||>, winner = None, start, memory, budget, pending},
    kernels = cgPoolEnsure[Length[attempts]];
    If[FailureQ[kernels], Return[kernels, Module]];
    budget = Total[Lookup[attempts, "AllocatedMemory"]] - Length[kernels] $CGPool["Baseline"];
    memory = Quotient[budget, Length[attempts]];
    If[memory < 32 2^20, Return[makeFailure["PoolUnavailable", "The memory budget leaves no share for the race members after the pool baseline."], Module]];
    race = cgRaceRequest[request];
    start = AbsoluteTime[];
    WithCleanup[
        Block[{$DistributedContexts = None},
            Do[With[{method = attempt["Method"], r = race, t = target, l = limit, m = memory},
                    jobs[method] = ParallelSubmit[VVMFTool`Private`cgRaceJob[r, t, method, l, m]]],
                {attempt, attempts}]];
        Parallel`Developer`QueueRun[];
        pending = Keys[jobs];
        While[pending =!= {} && winner === None,
            Parallel`Developer`QueueRun[];
            Do[Which[
                    Parallel`Developer`DoneQ[jobs[method]],
                    pending = DeleteCases[pending, method];
                    (* the finish is bounded like the in-kernel attempt: the member's remaining time plus the grace *)
                    With[{bundle = TimeConstrained[cgFinishRoute[request, target, method, WaitAll[jobs[method]], False],
                            Max[1, limit - (AbsoluteTime[] - start)] + $CGRaceGrace,
                            makeFailure["Timeout", "The CG attempt exceeded AttemptTimeLimit.", <|"Method" -> method|>]]},
                        outcomes[method] = <|"Method" -> method, "Outcome" -> If[AssociationQ[bundle], "Accepted", First[bundle]],
                            "Execution" -> "Race", "Seconds" -> Round[AbsoluteTime[] - start, 0.1]|>;
                        If[AssociationQ[bundle], winner = bundle; Break[]]],
                    AbsoluteTime[] - start > limit + $CGRaceGrace,
                    pending = DeleteCases[pending, method];
                    outcomes[method] = <|"Method" -> method, "Outcome" -> "Timeout", "Execution" -> "Race",
                        "Seconds" -> Round[AbsoluteTime[] - start, 0.1]|>],
                {method, pending}];
            If[pending =!= {} && winner === None, Pause[$CGRacePoll]]],
        (* every exit: abort what still runs (rivals of a winner, overdue members, an outer abort) *)
        If[AnyTrue[Values[jobs], !Parallel`Developer`DoneQ[#] &], cgPoolAbort[]]];
    Do[If[!KeyExistsQ[outcomes, attempt["Method"]],
            outcomes[attempt["Method"]] = <|"Method" -> attempt["Method"], "Outcome" ->
                If[KeyExistsQ[jobs, attempt["Method"]] && Parallel`Developer`DoneQ[jobs[attempt["Method"]]] && WaitAll[jobs[attempt["Method"]]] =!= $Failed,
                    "FinishedAfterValidatedWinner", "StoppedAfterValidatedWinner"], "Execution" -> "Race"|>],
        {attempt, attempts}];
    (* outcomes in plan order, whatever order the members finished in *)
    <|"Bundle" -> winner, "Outcomes" -> Lookup[outcomes, Lookup[attempts, "Method"]]|>
]];
