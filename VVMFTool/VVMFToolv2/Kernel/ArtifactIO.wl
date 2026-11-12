(*
    :Title: Exact JSON artifact I/O
    :Context: VVMFTool`Private`
    :Summary: Read inert interchange data and write checked atomic file replacements.
    :Responsibilities: File digests, owned temporary output, cancellation cleanup and JSON decoding.
    :Dependencies: ResultValidation.wl; Configuration.wl; Wolfram filesystem functions.
    :See Also: GroupStorage.wl; Schemas/GroupResult.md.
*)

(*
    Summary: Compute exact byte length and SHA256 for an existing regular file.
    Parameters: file — absolute file path.
    Options/defaults: None.
    Returns: File/SHA256/Bytes association, or FileUnavailable/ReadFailed Failure.
    Effects: Reads file bytes; no execution or mutation.
    Failures: Nonabsolute/missing/nonfile paths and failed reads.
    Example: fileDigest[path]["SHA256"] is a lowercase 64-digit string.
    Remarks: A digest identifies bytes; it does not establish mathematical or executable trust.
    See also: writeResult; readResult.
*)
fileDigest[file_String] := Module[{digest, bytes},
    If[!absolutePathQ[file] || FileType[file] =!= File,
        Return[makeFailure["FileUnavailable", "Expected an existing absolute file path.",
            <|"File" -> file|>]]];
    digest = Check[FileHash[file, "SHA256"], $Failed];
    bytes = Check[FileByteCount[file], $Failed];
    If[!IntegerQ[digest] || !IntegerQ[bytes] || bytes < 0,
        Return[makeFailure["ReadFailed", "Could not read the artifact bytes.", <|"File" -> file|>]]];
    <|"File" -> file, "SHA256" -> IntegerString[digest,16,64], "Bytes" -> bytes|>
];
fileDigest[___] := makeFailure["FileUnavailable", "Expected an absolute artifact path."];

(*
    Summary: Remove one temporary file owned by the active write operation.
    Parameters: path — generated temporary path, never an arbitrary imported reference.
    Options/defaults: None.
    Returns: True if absent/removed, or CleanupFailed Failure.
    Effects: Deletes only that file; no recursive directory deletion.
    Failures: Failed removal is reported and cannot replace the main mathematical result.
    Example: removeWriteTemporary[path] is True after a failed rename leaves an owned file.
    See also: writeResult.
*)
removeWriteTemporary[path_String] := If[!FileExistsQ[path], True,
    If[Check[DeleteFile[path], $Failed] === $Failed,
        makeFailure["CleanupFailed", "Could not remove owned temporary output.", <|"File" -> path|>],
        True]
];
removeWriteTemporary[___] := makeFailure["CleanupFailed", "Expected the owned temporary path."];

(*
    Summary: Write exact inert JSON via a unique sibling temporary file and rename.
    Parameters: file — absolute output path with an existing parent directory;
        data — values accepted by resultJSONQ.
    Options/defaults: None; an existing regular target file is atomically replaced.
    Returns: File/SHA256/Bytes record for the produced bytes, or Failure.
    Effects: Writes and hashes an owned sibling file, renames it and removes unfinished output.
    Failures: Invalid data/path, export/hash/rename errors and cancellation preserve the
        existing target until the final rename. Cleanup failures are attached separately.
    Example: writeResult[path, <|"schemaVersion" -> 1, "missing" -> Null|>].
    Remarks: The hash is taken from the completed temporary artifact, not from a possibly
        later modified destination. Publication/import trust checks remain separate.
    See also: readResult; fileDigest; SaveGroupData in step1Plan.md.
*)
writeResult[file_String, data_] := Module[{temporary, result, metadata, cleanup, parent},
    If[!absolutePathQ[file] || !resultJSONQ[data],
        Return[makeFailure["SaveFailed", "Expected an absolute path and exact JSON data."]]];
    parent = DirectoryName[file];
    If[!DirectoryQ[parent] || !MemberQ[{File,None},FileType[file]],
        Return[makeFailure["SaveFailed", "The output parent or target type is invalid.",
            <|"File" -> file|>]]];
    temporary = FileNameJoin[{parent, ".vvmf-" <> CreateUUID[] <> ".partial"}];
    result = CheckAbort[
        If[Check[Export[temporary,data,"RawJSON"],$Failed] === $Failed,
            makeFailure["SaveFailed","Cannot write the JSON artifact.",<|"File" -> file|>],
            metadata = fileDigest[temporary];
            If[FailureQ[metadata], metadata,
                If[Check[RenameFile[temporary,file,OverwriteTarget -> True],$Failed] === $Failed,
                    makeFailure["SaveFailed","Cannot publish the JSON artifact.",<|"File" -> file|>],
                    Join[metadata,<|"File" -> file|>]
                ]
            ]
        ],
        makeFailure["Cancelled", "The JSON save was cancelled.", <|"File" -> file|>]
    ];
    cleanup = removeWriteTemporary[temporary];
    If[FailureQ[cleanup],
        If[FailureQ[result],
            Failure[result[[1]], Join[result[[2]], <|"Cleanup" -> cleanup|>]],
            makeFailure["CleanupFailed", "The artifact was saved but temporary cleanup failed.",
                <|"SavedArtifact" -> result, "Cleanup" -> cleanup|>]
        ],
        result
    ]
];
writeResult[___] := makeFailure["SaveFailed", "Expected an artifact path and JSON data."];

(*
    Summary: Read an inert JSON artifact without evaluating any saved source or path.
    Parameters: file — absolute existing file path.
    Options/defaults: None; mathematical/schema validation belongs to the owning decoder.
    Returns: Exact JSON data, or FileUnavailable/InvalidJSON Failure.
    Effects: Reads bytes through RawJSON; no ToExpression, Get, GAP execution or workspace load.
    Failures: Missing files, JSON syntax errors and values outside the exact interchange.
    Example: a retained code string remains a string after readResult[path].
    Remarks: Parsing alone never issues a group validation receipt.
    See also: validateGroupResult; validateConstructionRecord; ImportGroupData in step1Plan.md.
*)
readResult[file_String] := Module[{data},
    If[!absolutePathQ[file] || FileType[file] =!= File,
        Return[makeFailure["FileUnavailable", "The JSON artifact is unavailable.", <|"File" -> file|>]]];
    data = Check[Import[file,"RawJSON"],$Failed];
    If[data === $Failed || !resultJSONQ[data],
        makeFailure["InvalidJSON","The artifact does not contain exact JSON data.",<|"File" -> file|>],
        data]
];
readResult[___] := makeFailure["FileUnavailable", "Expected an absolute JSON file path."];

True

