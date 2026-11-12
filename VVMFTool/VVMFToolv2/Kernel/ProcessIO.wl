(*
    :Title: Bounded subprocess diagnostics
    :Context: VVMFTool`Private`
    :Summary: Capture owned short-lived probe processes without shell interpolation.
    :Responsibilities: Nonblocking output reads; time bounds; cancellation cleanup.
    :Dependencies: Wolfram StartProcess, ProcessConnection and ProcessStatus.
    :See Also: Configuration.wl; https://reference.wolfram.com/language/ref/ReadString.html
*)

(*
    Summary: Read currently buffered standard output and error from an owned process.
    Parameters: process — a ProcessObject created by StartProcess.
    Options/defaults: None.
    Returns: A pair of strings; exhausted streams contribute empty strings.
    Effects: Consumes available stream contents without waiting for new output.
    Failures: The caller must supply a process whose streams remain readable.
    Example: readProcessOutput[process] returns {"ready\n", ""} after that output arrives.
    See also: runProbeProcess; ProcessConnection.
*)
readProcessOutput[process_ProcessObject] := Map[
    Function[name, Replace[
        ReadString[ProcessConnection[process, name], EndOfBuffer],
        EndOfFile -> ""
    ]],
    {"StandardOutput", "StandardError"}
];

(*
    Summary: Run a short diagnostic program with a bounded lifetime and capture output.
    Parameters: arguments — nonempty executable/argument string list; seconds — positive limit;
        input — optional short text delivered to standard input.
    Options/defaults: input defaults to ""; no shell.
    Returns: ExitCode/StandardOutput/StandardError association, or a typed Failure.
    Effects: Starts and owns one process; terminates it on timeout or user abort.
    Failures: Invalid input, failed launch, timeout or cancellation. Nonzero exits remain
        reported in the result, so the caller can attach operation-specific diagnostics.
    Example: runProbeProcess[{"/bin/echo", "ready"}, 5]["StandardOutput"] is "ready\n".
    Remarks: This helper is for trusted short probes that do not launch child workers.
        Computational worker trees are owned by the GAP job coordinator.
    See also: CheckGAP; readProcessOutput; StartProcess.
*)
runProbeProcess[arguments_List, seconds_?NumericQ, input_String : ""] := Module[
    {process, deadline, output = {"", ""}, chunk, aborted = False, timedOut = False, result},
    If[arguments === {} || !AllTrue[arguments, StringQ] ||
        !TrueQ[Im[seconds] == 0] || !TrueQ[seconds > 0],
        Return[makeFailure["InvalidProcessRequest", "Expected a command and positive time limit."]]
    ];
    process = Check[StartProcess[arguments], $Failed];
    If[Head[process] =!= ProcessObject,
        Return[makeFailure["ProcessStartFailed", "The diagnostic process could not start.",
            <|"Command" -> arguments|>]]
    ];
    (* Open all owned connections before cleanup. Wolfram 15's ProcessLink otherwise
       attempts to unset a missing input-stream cache entry when releasing a process. *)
    ProcessConnection[process, "StandardInput"];
    deadline = AbsoluteTime[] + seconds;
    CheckAbort[
        If[input =!= "", WriteString[process, input]];
        While[ProcessStatus[process] === "Running" && AbsoluteTime[] < deadline,
            chunk = readProcessOutput[process];
            output = MapThread[StringJoin, {output, chunk}];
            Pause[0.01]
        ];
        timedOut = ProcessStatus[process] === "Running";
        If[timedOut, KillProcess[process]],
        aborted = True;
        If[ProcessStatus[process] === "Running", KillProcess[process]]
    ];
    If[aborted || timedOut,
        Return[makeFailure[If[aborted, "Cancelled", "Timeout"],
            "The diagnostic process ended before completion.",
            <|"Command" -> arguments, "StandardOutput" -> First[output],
                "StandardError" -> Last[output]|>]]
    ];
    output = MapThread[StringJoin, {output, readProcessOutput[process]}];
    result = <|"ExitCode" -> ProcessInformation[process, "ExitCode"],
        "StandardOutput" -> First[output], "StandardError" -> Last[output]|>;
    KillProcess[process];
    result
];
runProbeProcess[___] := makeFailure["InvalidProcessRequest", "Malformed diagnostic process request."];
