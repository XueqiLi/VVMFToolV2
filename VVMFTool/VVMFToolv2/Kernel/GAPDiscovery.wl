(*
    :Title: GAP executable and capability discovery
    :Context: VVMFTool`Private`
    :Summary: Inspect GAP without starting mathematical jobs or retaining a cache.
    :Responsibilities: Executable resolution; version/package/flag reporting; save/restore probe.
    :Dependencies: Configuration.wl; ProcessIO.wl; GAP/Probe.g.
    :See Also: https://gap-system.github.io/gap/doc/ref/chap3_mj.html
*)

(*
    Summary: Encode a string as a literal GAP string without evaluating its contents.
    Parameters: text — a string not containing a NUL character.
    Options/defaults: None.
    Returns: Quoted GAP source literal or Failure.
    Effects: Pure.
    Failures: NUL and nonstring input are rejected.
    Example: gapStringLiteral["a b"] returns the source text "\"a b\"".
    See also: probeGAP; typed construction codecs in GroupInput.wl.
*)
gapStringLiteral[text_String] := If[StringContainsQ[text, FromCharacterCode[0]],
    makeFailure["InvalidPath", "GAP paths cannot contain a NUL character."],
    "\"" <> StringReplace[text, {"\\" -> "\\\\", "\"" -> "\\\"",
        "\n" -> "\\n", "\r" -> "\\r", "\t" -> "\\t"}] <> "\""
];
gapStringLiteral[___] := makeFailure["InvalidInput", "Expected a string to encode."];

(*
    Summary: Locate the configured executable or the first existing GAP installation.
    Parameters: configuration — validated configuration association.
    Options/defaults: Automatic searches PATH, then common Homebrew/local/system locations.
    Returns: An association with an absolute Executable path, or Failure.
    Effects: Reads environment/path existence; starts no process.
    Failures: Missing executable, relative/invalid explicit path, or malformed configuration.
    Example: resolveGAP[<|GAPExecutable -> "/opt/homebrew/bin/gap"|>]["Executable"]
        returns that path when it exists.
    Remarks: Executability and actual GAP identity are checked by the bounded probe.
    See also: CheckGAP; probeGAP.
*)
resolveGAP[configuration_Association] := Module[{selected, pathEntries, candidates},
    selected = Lookup[configuration, GAPExecutable, Automatic];
    If[selected =!= Automatic,
        If[!absolutePathQ[selected] || FileType[selected] =!= File,
            Return[makeFailure["GAPNotFound", "The configured GAP executable does not exist.",
                <|"Path" -> selected|>]]
        ];
        Return[<|"Executable" -> selected|>]
    ];
    pathEntries = StringSplit[Replace[Environment["PATH"], Except[_String] -> ""],
        If[$OperatingSystem === "Windows", ";", ":"]];
    candidates = DeleteDuplicates[Join[
        FileNameJoin[{#, If[$OperatingSystem === "Windows", "gap.exe", "gap"]}] & /@
            Select[pathEntries, absolutePathQ],
        {"/opt/homebrew/bin/gap", "/usr/local/bin/gap", "/usr/bin/gap"}
    ]];
    selected = SelectFirst[candidates, FileType[#] === File &, Missing["NotFound"]];
    If[MissingQ[selected], makeFailure["GAPNotFound", "No GAP executable was found."],
        <|"Executable" -> selected|>]
];
resolveGAP[___] := makeFailure["InvalidConfiguration", "Expected a configuration association."];

(*
    Summary: Decode the probe's bounded, nonexecutable line protocol.
    Parameters: text — captured GAP standard output.
    Options/defaults: Nonprotocol informational lines are ignored.
    Returns: Version/build/workspace/package association or Failure.
    Effects: Pure; never interprets a GAP or Wolfram expression.
    Failures: Missing/duplicate fields, malformed records, invalid workspace status.
    Example: parseGAPProbe[output]["Packages"]["json"]["Available"] reports the probe result.
    See also: GAP/Probe.g; probeGAP.
*)
parseGAPProbe[text_String] := Module[{lines, fields, records, packages, required, installed, entries},
    lines = Select[StringSplit[StringReplace[text, "\r" -> ""], "\n"],
        StringStartsQ[#, "VVMF_PROBE\t"] &];
    fields = StringSplit[#, "\t", All] & /@ lines;
    If[!AllTrue[fields, Length[#] === 3 &] ||
        !DuplicateFreeQ[If[fields === {}, {}, fields[[All, 2]]]],
        Return[makeFailure["InvalidProbe", "The GAP capability protocol is malformed."]]
    ];
    records = Association[Rule @@@ (Rest /@ fields)];
    required = {"Version", "KernelVersion", "Architecture", "BuildVersion", "BuildDateTime", "Workspace"};
    If[!AllTrue[required, KeyExistsQ[records, #] &] ||
        !MemberQ[{"true", "false"}, records["Workspace"]],
        Return[makeFailure["InvalidProbe", "Required GAP capability fields are missing or invalid."]]
    ];
    packages = Association @ KeyValueMap[Function[{key, value},
        StringDrop[key, StringLength["Package:"]] -> <|
            "Available" -> (value =!= "unavailable"),
            "Version" -> If[value === "unavailable", Missing["NotInstalled"], value]|>
    ], KeySelect[records, StringStartsQ[#, "Package:"] &]];
    entries = KeySelect[records, StringStartsQ[#, "InstalledPackage:"] &];
    If[!AllTrue[Keys[entries], StringMatchQ[StringDrop[#, StringLength["InstalledPackage:"]],
        RegularExpression["[^:]+:[1-9][0-9]*"]] &],
        Return[makeFailure["InvalidProbe", "Malformed installed-package metadata."]]];
    installed = GroupBy[KeyValueMap[
        {First[StringSplit[StringDrop[#1, StringLength["InstalledPackage:"]], ":"]], #2} &, entries],
        First -> Last];
    Join[KeyTake[records, Most[required]], <|"Packages" -> packages,
        "InstalledPackages" -> installed, "Workspace" -> (records["Workspace"] === "true")|>]
];
parseGAPProbe[___] := makeFailure["InvalidProbe", "Expected probe output text."];

(*
    Summary: Probe a concrete executable, including a real save and fresh-process restore.
    Parameters: executable — existing absolute executable path; directory — owned temporary
        directory; seconds — positive bound applied to each short probe subprocess.
    Options/defaults: Quiet batch GAP, break errors terminate, no user startup files.
    Returns: Capability association or Failure, including captured diagnostics on failure.
    Effects: Writes a temporary workspace inside directory; launches bounded probe workers.
    Failures: Non-GAP executable, unsupported flags, protocol/save/restore failures or timeout.
    Example: probeGAP[path, temporaryDirectory, 30]["WorkspaceRestored"] is True on success.
    Remarks: SaveWorkspace is a literal main-input command after Read[Probe.g] returns,
        not inside any function. The owner deletes directory after this function returns.
    See also: CheckGAP; runProbeProcess; parseGAPProbe.
*)
probeGAP[executable_String, directory_String, seconds_?NumericQ] := Module[
    {help, flags, workspace, commands, result, capabilities, restored, probeFile},
    help = runProbeProcess[{executable, "-h"}, seconds];
    If[FailureQ[help], Return[help]];
    flags = AssociationMap[StringContainsQ[help["StandardOutput"], #] &,
        {"-K", "-L", "--quitonbreak", "-r", "-A"}];
    If[help["ExitCode"] =!= 0 || !TrueQ[And @@ Values[flags]],
        Return[makeFailure["UnsupportedGAP", "Required GAP command flags are unavailable.",
            <|"Flags" -> flags, "Diagnostics" -> help|>]]
    ];
    workspace = FileNameJoin[{directory, "probe.wsp"}];
    probeFile = FileNameJoin[{$PackageRoot, "GAP", "Probe.g"}];
    If[!FileExistsQ[probeFile], Return[makeFailure["ProbeUnavailable", "The packaged GAP probe is missing."]]];
    commands = "Read(" <> gapStringLiteral[probeFile] <> ");;\n" <>
        "VVMF_PROBE_SAVED := SaveWorkspace(" <> gapStringLiteral[workspace] <> ");;\n" <>
        "Print(\"VVMF_PROBE\\tWorkspace\\t\",VVMF_PROBE_SAVED,\"\\n\");\nQUIT_GAP(0);\n";
    result = runProbeProcess[{executable, "-q", "-b", "-r", "-A", "--quitonbreak"}, seconds, commands];
    If[FailureQ[result], Return[result]];
    If[result["ExitCode"] =!= 0,
        Return[makeFailure["GAPProbeFailed", "GAP could not complete its capability probe.",
            <|"Diagnostics" -> result|>]]
    ];
    capabilities = parseGAPProbe[result["StandardOutput"]];
    If[FailureQ[capabilities], Return[capabilities]];
    If[!TrueQ[capabilities["Workspace"]] || !FileExistsQ[workspace] || FileByteCount[workspace] === 0,
        Return[makeFailure["WorkspaceUnavailable", "GAP did not save a nonempty probe workspace."]]
    ];
    restored = runProbeProcess[{executable, "-q", "-b", "-r", "-A", "--quitonbreak",
        "-L", workspace}, seconds,
        "if IsBound(VVMF_PROBE_TOKEN) and VVMF_PROBE_TOKEN = [17,23,42] then\n" <>
        "Print(\"VVMF_RESTORED\\n\"); QUIT_GAP(0);\nelse QUIT_GAP(1); fi;\n"];
    If[FailureQ[restored], Return[restored]];
    If[restored["ExitCode"] =!= 0 || !StringContainsQ[restored["StandardOutput"], "VVMF_RESTORED"],
        Return[makeFailure["WorkspaceRestoreFailed", "A fresh GAP worker did not recover probe state.",
            <|"Diagnostics" -> restored|>]]
    ];
    Join[capabilities, <|"Executable" -> executable, "Flags" -> flags,
        "WorkspaceRestored" -> True, "WorkspaceBytes" -> FileByteCount[workspace],
        "MethodDependencies" -> <|"Unger" -> {"inducereduce"}, "REPSN" -> {"repsn"},
            "IrreducibleRepresentationsDixon" -> {}, "NormalSubgroupsByIndex" -> {"lins"},
            "SL2Reps" -> {"sl2reps"}, "AtlasRep" -> {"atlasrep"}, "JSONTransport" -> {"json"},
            "CheckpointTransport" -> {"json", "io"}|>|>]
];
probeGAP[___] := makeFailure["InvalidProbe", "Malformed GAP capability probe request."];

(*
    Summary: Discover GAP capabilities and verify resumable workspaces.
    Status: Alpha.
    Parameters: None; executable and attempt bound come from package configuration.
    Options/defaults: Each probe subprocess is capped at min(30, AttemptTimeLimit) seconds.
    Returns: Capability association or Failure; missing optional packages appear unavailable.
    Effects: Runs GAP in an owned temporary directory, then removes its probe workspace.
        Does not download packages, create retained caches or mutate group objects.
    Failures: Missing executable, unsupported flags, launch/timeout/save/restore/protocol errors.
    Example: CheckGAP[]["WorkspaceRestored"] is True after successful real save and restore.
    See also: ConfigureVVMFTool; VVMFToolConfiguration; probeGAP.
*)
CheckGAP[] := Module[{resolved, directory, result, seconds},
    resolved = resolveGAP[$Configuration];
    If[FailureQ[resolved], Return[resolved]];
    directory = CreateDirectory[];
    If[!StringQ[directory], Return[makeFailure["ProbeStorageFailed", "Cannot create probe storage."]]];
    seconds = Min[30, $Configuration[AttemptTimeLimit]];
    result = CheckAbort[probeGAP[resolved["Executable"], directory, seconds],
        makeFailure["Cancelled", "The GAP capability check was cancelled."]];
    DeleteDirectory[directory, DeleteContents -> True];
    result
];
CheckGAP[___] := makeFailure["InvalidInput", "CheckGAP takes no arguments."];

True
