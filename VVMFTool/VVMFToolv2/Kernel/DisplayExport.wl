(*
    :Title: Display export
    :Context: VVMFTool`Private`
    :Summary: ExportDisplay writes complete LaTeX or static notebook files atomically.
    :Responsibilities:
        - writeDisplayArtifact: temporary sibling, serialization, rename; Overwrite -> False refuses an existing
          target; failures keep the old file; nothing is compiled.
    :Dependencies: ArtifactIO.wl (absolutePathQ, removeWriteTemporary); LaTeXDisplay.wl; NotebookDisplay.wl.
    :See Also: VVMFArch/step3Plan.md (export contracts).
*)

(*
    Summary: Write a rendered display artifact atomically.
    Parameters: file — absolute target path; payload — LaTeX string or Notebook expression; format — "LaTeX" or
        "Notebook"; overwrite — Boolean.
    Options/defaults: None.
    Returns: The absolute path, or Failure.
    Effects: Writes a temporary sibling, then renames it over the target; the temporary file is removed on every
        exit.
    Failures: ExportFailed (invalid path or parent, existing target without Overwrite, serialization or rename
        errors, cancellation); the old target is preserved.
    Example: writeDisplayArtifact["/tmp/t.tex", "x", "LaTeX", False].
    See also: ExportDisplay; writeResult.
*)
writeDisplayArtifact[file_String, payload_, format_String, overwrite_] := Module[{parent, temporary, result, cleanup},
    If[!absolutePathQ[file], Return[makeFailure["ExportFailed", "Expected an absolute file path.", <|"File" -> file|>]]];
    parent = DirectoryName[file];
    If[!DirectoryQ[parent], Return[makeFailure["ExportFailed", "The target directory does not exist.", <|"File" -> file|>]]];
    If[FileType[file] === Directory, Return[makeFailure["ExportFailed", "The target is a directory.", <|"File" -> file|>]]];
    If[FileType[file] === File && !TrueQ[overwrite],
        Return[makeFailure["ExportFailed", "The target exists; use Overwrite -> True to replace it.", <|"File" -> file|>]]];
    temporary = FileNameJoin[{parent, ".vvmf-" <> CreateUUID[] <> ".partial"}];
    result = CheckAbort[
        If[Check[Switch[format,
                "LaTeX" | "Text", Export[temporary, payload, "Text", CharacterEncoding -> "UTF-8"],
                "Notebook", Export[temporary, payload, "NB"]], $Failed] === $Failed || FileType[temporary] =!= File,
            makeFailure["ExportFailed", "Cannot write the display artifact.", <|"File" -> file|>],
            If[Check[RenameFile[temporary, file, OverwriteTarget -> TrueQ[overwrite]], $Failed] === $Failed,
                makeFailure["ExportFailed", "Cannot publish the display artifact.", <|"File" -> file|>],
                file]],
        makeFailure["Cancelled", "The export was cancelled.", <|"File" -> file|>]];
    cleanup = removeWriteTemporary[temporary];
    If[FailureQ[cleanup] && !FailureQ[result],
        makeFailure["CleanupFailed", "The artifact was written but its temporary file remains.", <|"File" -> file, "Cleanup" -> cleanup|>],
        result]
];

Options[ExportDisplay] = {ScalarNotation -> Automatic, NotationStyle -> Automatic, OneByOneMatrix -> Automatic, DefineOmega -> Automatic,
    Digits -> Automatic, Caption -> Automatic, Label -> Automatic, PageSize -> Automatic, Standalone -> False, Overwrite -> False};

(*
    Summary: Export a display document to a LaTeX or notebook file.
    Status: Alpha.
    Parameters: file — absolute path; v — DisplayDocument; format — "LaTeX" (default) or "Notebook".
    Options/defaults: The renderer options of ToLaTeX (LaTeX) or ToNotebook (Notebook), Automatic taking the
        document's saved defaults; Standalone -> False (LaTeX fragment) or True (complete document); Overwrite ->
        False (refuse an existing file) or True (replace it atomically).
    Returns: The absolute path, or Failure.
    Effects: Writes one file atomically; nothing is compiled; no GAP work. A notebook is a static, self-contained
        Notebook of explicit boxes with every row (PageSize only organizes sections).
    Failures: InvalidDisplayDocument; InvalidOption; UnsupportedFormat; ExportFailed (existing target without
        Overwrite, unwritable directory, serialization or rename failure — the old file is kept).
    Example: ExportDisplay[FileNameJoin[{$TemporaryDirectory, "A4.tex"}], CharacterTableView[g], "LaTeX", Standalone -> True, Overwrite -> True].
    See also: ToLaTeX; ToNotebook.
*)
ExportDisplay[file_String, document_DisplayDocument, format_String : "LaTeX", options : OptionsPattern[]] := Module[
    {data, settings, payload},
    If[!MemberQ[{"LaTeX", "Notebook"}, format],
        Return[makeFailure["UnsupportedFormat", "ExportDisplay writes \"LaTeX\" or \"Notebook\".", <|"Format" -> format|>]]];
    data = validateDisplayDocument[document]; If[FailureQ[data], Return[data]];
    settings = displayRenderSettings[ExportDisplay, "ExportDisplay", data, {options}]; If[FailureQ[settings], Return[settings]];
    payload = If[format === "LaTeX",
        ToLaTeX[document, Sequence @@ Normal[KeyDrop[Select[settings, # =!= Automatic &], {PageSize, Overwrite}]]],
        renderStaticNotebook[If[settings[Caption] =!= Automatic,
            Join[data, <|"Caption" -> If[StringQ[settings[Caption]], textNode[settings[Caption]], labelNode[settings[Caption]]]|>], data], settings]];
    If[FailureQ[payload], Return[payload]];
    writeDisplayArtifact[ExpandFileName[file], payload, format, settings[Overwrite]]
];
ExportDisplay[___] := makeFailure["InvalidInput", "ExportDisplay expects an absolute file path, a DisplayDocument, a format and options."];

True
