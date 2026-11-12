# Title: Optional package access and guarded native calls
# Summary: Load optional method packages on demand, never allowing silent downloads, and run
# optional native algorithms so that their errors are data instead of ending the worker.
# Dependencies: Diagnostics.g.
# See also: GAP/Probe.g; Kernel/GAPDiscovery.wl MethodDependencies; VVMFArch/step2Plan.md.

# Summary: Make the AtlasRep package usable for local data only.
# Parameters/defaults: None.
# Returns: true, or a DependencyUnavailable failure when the package cannot be loaded.
# Effects: Loads atlasrep when needed and sets its AtlasRepAccessRemoteFiles user preference to
# false on every call, so a missing table file is reported as unavailable instead of downloaded.
# Failures: Missing package. A later local-only lookup returning fail is an unavailable
# dependency, never a mathematical negative.
# Example: VVMF_UseAtlasRep() = true; then UserPreference("AtlasRep","AtlasRepAccessRemoteFiles") = false.
# Remarks: Workers start with -r, which ignores the user's gap.ini, so the package default
# (remote access enabled) would otherwise apply. Preferences are process state; call this
# before every Atlas access, including in workers restored from a saved workspace.
# See also: VVMF_Failure; AtlasGenerators.
VVMF_UseAtlasRep := function()
    if LoadPackage("atlasrep") <> true then
        return VVMF_Failure("DependencyUnavailable","The AtlasRep package is unavailable.");
    fi;
    SetUserPreference("AtlasRep","AtlasRepAccessRemoteFiles",false);
    return true;
end;

# Summary: Run a function, turning GAP errors into structured failures instead of break loops.
# Parameters/defaults: func is a function of no arguments.
# Returns: rec(ok := true, value := result) or rec(ok := false, tag := "AdapterError", message := text).
# Effects: Temporarily sets BreakOnError to false and captures the error text; restores both and
# clears the options stack after an error (an interrupted call with options leaves them pushed).
# Failures: Errors inside func become AdapterError; func returning nothing gives value fail.
# Example: VVMF_Guarded(function() return 1/0; end).tag = "AdapterError".
# Remarks: Workers run with --quitonbreak; without this guard one failing irrep would end the
# worker and discard every other irrep verified by the same attempt. A computation that hits the
# worker's -K memory cap inside the guard also returns AdapterError, and the worker continues near
# its limit; the coordinator's resource monitor and the attempt deadline still bound it.
# See also: VVMF_Representations.
VVMF_Guarded := function(func)
    local oldBreak, oldOutput, readOnly, text, stream, result;
    oldBreak := BreakOnError;
    oldOutput := ERROR_OUTPUT;
    readOnly := IsReadOnlyGlobal("ERROR_OUTPUT");
    text := "";
    stream := OutputTextString(text, true);
    if readOnly then MakeReadWriteGlobal("ERROR_OUTPUT"); fi;
    ERROR_OUTPUT := stream;
    BreakOnError := false;
    result := CALL_WITH_CATCH(func, []);
    BreakOnError := oldBreak;
    ERROR_OUTPUT := oldOutput;
    if readOnly then MakeReadOnlyGlobal("ERROR_OUTPUT"); fi;
    CloseStream(stream);
    if not result[1] then
        if not IsEmpty(OptionsStack) then ResetOptionsStack(); fi;
        return rec(ok := false, tag := "AdapterError", message := text);
    fi;
    if Length(result) < 2 then return rec(ok := true, value := fail); fi;
    return rec(ok := true, value := result[2]);
end;

# Summary: Run a guarded computation with a wall-clock limit in a forked child process.
# Parameters/defaults: seconds is a positive integer or infinity; func is a function of no arguments
# whose result can be transferred by the IO package (matrices of cyclotomics, lists, records).
# Returns: As VVMF_Guarded, or rec(ok := false, tag := "IrrepTimeout", message := ...) when the limit
# expires or the child ends without a result.
# Effects: With a finite limit, forks the worker through the IO package; the child's changes to GAP
# state are discarded and only the returned value comes back. The child's standard output and error
# go to /dev/null, because it inherits the worker's protocol pipe and a copy of its output buffer. On
# expiry the child is killed with SIGKILL and reaped. Without a limit, runs in process.
# Failures: Errors inside func are captured as AdapterError by VVMF_Guarded in the child.
# Example: VVMF_TimedGuarded(1, function() while true do od; end).tag = "IrrepTimeout".
# Remarks: GAP has no in-process timeout; this bounds one irrep's construction so that a route that
# loops (unitary Dixon can retry indefinitely) cannot consume the whole attempt and lose the irreps it
# already verified. IO_CallWithTimeout is not used: it stops children with SIGTERM, which workers
# launched by the coordinator inherit as ignored, so the call would wait until the attempt deadline.
# See also: VVMF_Guarded; VVMF_Representations; BackgroundJobByFork.
VVMF_TimedGuarded := function(seconds, func)
    local job, deadline, state, result;
    if seconds = infinity or LoadPackage("io") <> true then return VVMF_Guarded(func); fi;
    job := ValueGlobal("BackgroundJobByFork")(function()
            local sink;
            # The child shares the worker's protocol pipe and a copy of its output buffers; send
            # everything it prints or flushes to /dev/null so no protocol line can be corrupted.
            sink := ValueGlobal("IO_open")("/dev/null", ValueGlobal("IO").O_WRONLY, 0);
            if sink <> fail then
                ValueGlobal("IO_dup2")(sink, 1); ValueGlobal("IO_dup2")(sink, 2); ValueGlobal("IO_close")(sink);
            fi;
            return VVMF_Guarded(func);
        end, [], rec(TerminateImmediately := true));
    if job = fail then return VVMF_Guarded(func); fi;
    deadline := NanosecondsSinceEpoch() + Maximum(1, seconds) * 10^9;
    repeat
        state := ValueGlobal("IsIdle")(job);
        if state = true then
            result := job!.result;
            ValueGlobal("IO_Close")(job!.childtoparent);
            ValueGlobal("IO_WaitPid")(job!.pid, true);
            if IsRecord(result) and IsBound(result.ok) then return result; fi;
            return rec(ok := false, tag := "AdapterError", message := "The construction returned no result.");
        elif state = fail then
            return rec(ok := false, tag := "AdapterError", message := "The construction ended without a result.");
        fi;
        MicroSleep(20000);
    until NanosecondsSinceEpoch() > deadline;
    ValueGlobal("IO_kill")(job!.pid, 9);
    ValueGlobal("IO_Close")(job!.childtoparent);
    ValueGlobal("IO_WaitPid")(job!.pid, true);
    return rec(ok := false, tag := "IrrepTimeout", message := "The construction did not finish within its time share.");
end;
