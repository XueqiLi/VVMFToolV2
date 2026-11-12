(*
    :Title: Managed storage paths and transactions
    :Context: VVMFTool`Private`
    :Summary: Keep cache/ledger operations inside canonical owned directories.
    :Responsibilities: Safe relative paths, exclusive directory locks and guaranteed release.
    :Dependencies: ArtifactIO.wl; POSIX test; Wolfram AbsoluteFileName and WithCleanup.
    :See Also: GroupCache.wl; GroupStorage.wl.
*)

(*
    Summary: Resolve an existing storage root, optionally creating the requested directory.
    Parameters: directory — absolute path; create — Boolean, default False.
    Options/defaults: Creation includes missing parents only when explicitly requested.
    Returns: Canonical existing directory path or InvalidStorageRoot/StorageUnavailable Failure.
    Effects: Reads the filesystem; optional directory creation. Never removes existing content.
    Failures: Relative/non-directory paths, unavailable creation or canonical resolution.
    Example: a caller's /var temporary path resolves to its /private/var path on macOS.
    See also: managedPath; https://reference.wolfram.com/language/ref/AbsoluteFileName.html.
*)
managedRoot[directory_String, create_ : False] := Module[{root, created},
    If[!absolutePathQ[directory] || !MemberQ[{True, False}, create],
        Return[makeFailure["InvalidStorageRoot", "Expected an absolute directory and creation flag."]]];
    If[!DirectoryQ[directory] && TrueQ[create] && FileType[directory] === None,
        created = Check[CreateDirectory[directory, CreateIntermediateDirectories -> True], $Failed];
        If[created === $Failed, Return[makeFailure["StorageUnavailable", "Cannot create managed storage."]]]];
    If[!DirectoryQ[directory], Return[makeFailure["StorageUnavailable", "The storage directory is unavailable."]]];
    root = Check[AbsoluteFileName[directory], $Failed];
    If[!StringQ[root], makeFailure["StorageUnavailable", "Cannot resolve managed storage."], root]
];
managedRoot[___] := makeFailure["InvalidStorageRoot", "Expected an absolute storage path."];

(*
    Summary: Resolve relative path components without following links inside managed storage.
    Parameters: root — canonical existing managed root; components — nonempty simple names.
    Options/defaults: Names cannot be dot/dot-dot, separators, NULs or absolute paths.
    Returns: Absolute contained path (possibly absent) or InvalidManagedPath Failure.
    Effects: Inspects every existing component. POSIX test detects dangling symbolic links.
    Failures: Noncanonical roots, escaping names, symlink components, non-directory ancestors,
        missing platform inspection support or failed inspection.
    Example: managedPath[root, {"entry-id", "result.json"}] never resolves a symlink outside root.
    Remarks: Callers serialize managed mutations with withStoreLock and recheck before deletion.
        This is ownership protection for package operations, not a sandbox against a user who
        deliberately replaces directories concurrently outside the package.
    See also: managedRoot; withStoreLock.
*)
managedPath[root_String, components_List] := Module[{path = root, resolved, index, linkTest, failure = None},
    If[!DirectoryQ[root] || Check[AbsoluteFileName[root], $Failed] =!= root || components === {} ||
        !AllTrue[components, StringQ[#] && StringLength[#] > 0 && !MemberQ[{".", ".."}, #] &&
            !StringContainsQ[#, {"/", "\\", FromCharacterCode[0]}] &],
        Return[makeFailure["InvalidManagedPath", "Expected a canonical root and contained simple path components."]]];
    Do[
        path = FileNameJoin[{path, components[[index]]}];
        If[FileExistsQ[path],
            resolved = Check[AbsoluteFileName[path], $Failed];
            If[resolved =!= path || (index < Length[components] && !DirectoryQ[path]),
                failure = makeFailure["InvalidManagedPath", "A managed path contains a link or invalid ancestor."];
                Break[]],
            If[!FileExistsQ["/bin/test"],
                failure = makeFailure["CapabilityUnavailable", "Managed storage requires POSIX link inspection."];
                Break[]];
            linkTest = RunProcess[{"/bin/test", "-L", path}];
            If[!AssociationQ[linkTest] || linkTest["ExitCode"] =!= 1,
                failure = makeFailure["InvalidManagedPath", "A managed path is a dangling link or cannot be inspected."];
                Break[]]
        ], {index, Length[components]}
    ];
    If[FailureQ[failure], failure, path]
];
managedPath[___] := makeFailure["InvalidManagedPath", "Expected managed root and relative components."];

(*
    Summary: Acquire an exclusive short storage transaction using atomic directory creation.
    Parameters: root — canonical managed root; seconds — positive maximum wait, default 10.
    Options/defaults: Lock directory .vvmf-lock contains a nonce and owning kernel PID/host.
    Returns: Lock record or CacheBusy/StorageUnavailable Failure.
    Effects: Creates only the lock and its owner metadata; waits briefly for an existing owner.
    Failures: Unsafe path, creation/write errors or wait timeout. A stale/unknown lock is reported;
        it is not removed by guessing whether another kernel or computer is still using it.
    Example: another kernel cannot concurrently rewrite the same managed index.
    See also: releaseStoreLock; withStoreLock.
*)
acquireStoreLock[root_String, seconds_ : 10] := Module[
    {path, deadline, created, owner, written, lock, acquired = False, failure = None},
    If[!NumberQ[seconds] || !TrueQ[Im[seconds] == 0] || !TrueQ[seconds > 0],
        Return[makeFailure["InvalidStorageLock", "Expected a positive storage-lock wait."]]];
    path = managedPath[root, {".vvmf-lock"}];
    If[FailureQ[path], Return[path]];
    deadline = SessionTime[] + seconds;
    owner = <|"nonce" -> CreateUUID["lock-"], "pid" -> $ProcessID, "host" -> $MachineName|>;
    lock = <|"Root" -> root, "Path" -> path, "Owner" -> owner|>;
    While[!acquired && !FailureQ[failure] && SessionTime[] < deadline,
        If[!FileExistsQ[path],
            (* Existing-directory errors are the expected atomic acquisition race;
               other creation diagnostics remain visible. *)
            AbortProtect[
                created = Quiet[Check[CreateDirectory[path], $Failed], CreateDirectory::filex];
                If[StringQ[created],
                    written = writeResult[FileNameJoin[{path, "owner.json"}], owner];
                    If[FailureQ[written],
                        If[FileNames["*", path] === {}, DeleteDirectory[path]];
                        failure = written,
                        acquired = True
                    ];
                ]
            ]
        ];
        If[!acquired, Pause[0.01]]
    ];
    If[FailureQ[failure], Return[failure]];
    If[acquired, lock,
        makeFailure["CacheBusy", "Managed storage is locked by another or interrupted operation.",
            <|"LockDirectory" -> path|>]]
];
acquireStoreLock[___] := makeFailure["InvalidStorageLock", "Expected managed root and wait bound."];

(*
    Summary: Release exactly the transaction lock whose nonce this caller acquired.
    Parameters: lock — record returned by acquireStoreLock.
    Options/defaults: No recursive deletion; unexpected contents or changed ownership are preserved.
    Returns: True or StorageLockConflict/CleanupFailed Failure.
    Effects: Deletes the matching owner file and then the empty lock directory.
    Failures: Link replacement, changed owner, unexpected files or filesystem errors.
    Example: a copied path with a different nonce cannot release a live transaction lock.
    See also: acquireStoreLock; withStoreLock.
*)
releaseStoreLock[lock_Association] := Module[{path, ownerPath, owner, files},
    If[!resultFieldsQ[lock, {"Root", "Path", "Owner"}],
        Return[makeFailure["StorageLockConflict", "Malformed owned lock record."]]];
    path = managedPath[lock["Root"], {".vvmf-lock"}];
    If[FailureQ[path] || path =!= lock["Path"] || !DirectoryQ[path],
        Return[makeFailure["StorageLockConflict", "The owned lock directory changed."]]];
    ownerPath = managedPath[path, {"owner.json"}];
    If[FailureQ[ownerPath], Return[ownerPath]];
    owner = readResult[ownerPath];
    files = FileNames[All, path];
    If[canonicalJSON[owner] =!= canonicalJSON[lock["Owner"]] || files =!= {ownerPath},
        Return[makeFailure["StorageLockConflict", "Lock ownership or contents changed."]]];
    If[Check[DeleteFile[ownerPath]; DeleteDirectory[path], $Failed] === $Failed,
        makeFailure["CleanupFailed", "Cannot release the owned storage lock."], True]
];
releaseStoreLock[___] := makeFailure["StorageLockConflict", "Expected the acquired lock record."];

(*
    Summary: Evaluate a short managed-storage transaction with guaranteed owned lock release.
    Parameters: root — canonical managed root; expression — held transaction body.
    Options/defaults: HoldRest; lock wait is 10 seconds. No progress callbacks belong inside a lock.
    Returns: Body result or lock/cleanup Failure. Throws propagate after cleanup; aborts become Cancelled.
    Effects: Acquires and releases one lock using WithCleanup, including nonlocal exits.
    Failures: Cleanup failure is returned alongside the saved body result on ordinary completion.
    Example: withStoreLock[root, writeResult[indexPath, updatedIndex]].
    See also: https://reference.wolfram.com/language/ref/WithCleanup.html; releaseStoreLock.
*)
SetAttributes[withStoreLock, HoldRest];
withStoreLock[root_String, expression_] := Module[{lock = None, cleanup = True, result},
    result = CheckAbort[WithCleanup[
        lock = acquireStoreLock[root],
        (* Consume a body abort before cleanup calls Import. Wolfram's importer can
           observe a pending abort even inside WithCleanup's protected cleanup. *)
        CheckAbort[If[FailureQ[lock], lock, expression],
            makeFailure["Cancelled", "The storage transaction was cancelled."]],
        If[AssociationQ[lock], cleanup = releaseStoreLock[lock]]
    ],
        If[AssociationQ[lock] && FailureQ[cleanup], cleanup = releaseStoreLock[lock]];
        makeFailure["Cancelled", "The storage transaction was cancelled."]
    ];
    If[FailureQ[cleanup], makeFailure["CleanupFailed", "Storage transaction lock cleanup failed.",
        <|"Result" -> result, "Cleanup" -> cleanup|>], result]
];
withStoreLock[___] := makeFailure["InvalidStorageLock", "Expected root and held transaction."];

True
