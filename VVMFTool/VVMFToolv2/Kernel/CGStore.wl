(*
    :Title: Clebsch-Gordan publication, caching and public entry points
    :Context: VVMFTool`Private`
    :Summary: Publish validated CG bundles into the group's Wolfram CG store (GAP receives CG records only on
        demand), and serve CGCoefficients, CacheCG, CGCacheInformation and CleanCGCache.
    :Responsibilities: encodeCGBundle, decodeCGBundle, acceptCGBundles, syncCGMirror, prepareCGRequest, resolveCGTargets,
        CGCoefficients, CacheCG, CGCacheInformation, CleanCGCache.
    :Dependencies: CGData.wl; GroupEnrichment.wl (runGroupEnrichment); RepresentationJobs.wl
        (ComputeGroupRepresentations); RepresentationStorage.wl (encodeRepScalar, decodeRepScalar);
        GAPOperations.wl (registerGAPOperation); GAP/CG.g.
    :See Also: VVMFArch/step4Plan.md; VVMFArch/implementation/step4Status.md (D-S4-2, D-S4-8).
*)

registerGAPOperation["CG", <|"Source" -> "Typed", "GenerationStep" -> 1, "CompleteQ" -> statusCompleteQ,
    "RecoverySkipQ" -> repeatSkipQ, "TerminalFailures" -> {"InvalidCGRecord"}, "Methods" -> Function[request, {"GAP"}]|>];

(*
    Summary: Encode a validated bundle as an inert JSON record for the GAP mirror and for snapshots.
    Parameters: bundle — stored bundle association; precision — Infinity (exact) or the numerical precision.
    Options/defaults: None.
    Returns: <|"key", "targetID", "pair", "inputIdentities", "targetIdentity", "method", "normalization",
        "symmetryMode", "arithmetic", "precision", "channels" -> {<|"copy", "symmetry", "embedding", "dual"|>},
        "verificationStatus" -> "Exact" | "Numerical" | "Unverified", "domain" -> <|"kind", "method", ...|> (when recorded)|>,
        or Failure.
    Effects: Pure.
    Failures: UnsupportedScalar from the Stage 2 scalar codec.
    Example: encodeCGBundle[b, Infinity]["channels"][[1]]["embedding"][[1, 1]]["type"] is a scalar type tag.
    Remarks: Entries use encodeRepScalar (algebraic numbers by minimal polynomial and isolating rectangle,
        numerical values by decimal strings), so GAP stores them without arithmetic.
    See also: decodeCGBundle; VVMF_CGRecordCheck.
*)
encodeCGBundle[bundle_Association, precision_] := Module[{encode, channels},
    encode[m_] := Map[encodeRepScalar[#, precision] &, m, {2}];
    channels = Map[<|"copy" -> ToString[#["Copy"]], "symmetry" -> #["Symmetry"], "embedding" -> encode[#["Embedding"]],
        "dual" -> encode[#["Dual"]]|> &, bundle["Channels"]];
    If[!FreeQ[channels, _Failure], Return[FirstCase[channels, _Failure, Null, Infinity]]];
    Join[<|"key" -> bundle["Key"], "targetID" -> bundle["TargetID"], "pair" -> bundle["Pair"],
        "inputIdentities" -> bundle["InputIdentities"], "targetIdentity" -> bundle["TargetIdentity"], "method" -> bundle["Method"],
        "normalization" -> bundle["Normalization"], "symmetryMode" -> bundle["SymmetryMode"], "arithmetic" -> bundle["Arithmetic"],
        "precision" -> If[precision === Infinity, "Infinity", ToString[precision]], "channels" -> channels,
        (* optional fields (methodOptionsPlan.md 1.4): older readers and GAP's record check ignore them, so the snapshot
           schema version is unchanged *)
        "verificationStatus" -> cgEntryStatus[bundle]|>,
        With[{d = Lookup[bundle, "Domain", None]}, If[AssociationQ[d], <|"domain" -> cgDomainRecord[d]|>, <||>]]]
];

(* A domain summary as an inert record of strings and integers (and back). *)
cgDomainRecord[d_Association] := Association[KeyValueMap[ToLowerCase[StringTake[#1, 1]] <> StringDrop[#1, 1] -> Replace[#2, Automatic -> "Automatic"] &,
    KeyTake[d, {"Kind", "Method", "Degree", "Conductor", "Oversized"}]]];
cgDomainFromRecord[r_Association] := Association[KeyValueMap[ToUpperCase[StringTake[#1, 1]] <> StringDrop[#1, 1] -> Replace[#2, "Automatic" -> Automatic] &,
    KeyTake[r, {"kind", "method", "degree", "conductor", "oversized"}]]];
cgDomainFromRecord[_] := Missing["NotRecorded"];

(*
    Summary: Decode an inert bundle record.
    Parameters: record — from encodeCGBundle.
    Options/defaults: None.
    Returns: Stored bundle association (matrices decoded), or Failure. "VerificationStatus" is the record's
        "verificationStatus", or for a record written before statuses existed "Exact" (exact arithmetic) or "Numerical".
    Effects: Pure.
    Failures: InvalidCGRecord for missing fields, malformed scalars or an unknown verification status.
    Example: decodeCGBundle[encodeCGBundle[b, Infinity]] has the same channels as b.
    Remarks: Decoding does not validate the mathematics; an importer revalidates the bundle (validateCGBundle)
        against the group's variants before accepting it, except a registered file's (importCGBundles "Trusted").
    See also: encodeCGBundle; importCGBundles.
*)
decodeCGBundle[record_Association] := Module[{fields, decode, channels},
    fields = {"key", "targetID", "pair", "inputIdentities", "targetIdentity", "method", "normalization", "symmetryMode",
        "arithmetic", "precision", "channels"};
    If[!SubsetQ[Keys[record], fields] || !ListQ[record["channels"]],
        Return[makeFailure["InvalidCGRecord", "Malformed CG bundle record."]]];
    decode[m_] := If[MatrixQ[m, AssociationQ], Map[decodeRepScalar, m, {2}], $Failed];
    channels = Map[<|"Copy" -> ToExpression[#["copy"]], "Symmetry" -> #["symmetry"], "Embedding" -> decode[#["embedding"]],
        "Dual" -> decode[#["dual"]]|> &, record["channels"]];
    If[!FreeQ[channels, $Failed | _Failure] || !AllTrue[Lookup[channels, "Copy"], IntegerQ],
        Return[makeFailure["InvalidCGRecord", "Malformed CG bundle channels."]]];
    If[!MemberQ[{"Exact", "Numerical", "Unverified"}, Lookup[record, "verificationStatus", "Exact"]],
        Return[makeFailure["InvalidCGRecord", "Unknown CG verification status."]]];
    <|"Key" -> record["key"], "TargetID" -> record["targetID"], "Pair" -> record["pair"], "InputIdentities" -> record["inputIdentities"],
        "TargetIdentity" -> record["targetIdentity"], "Method" -> record["method"], "Normalization" -> record["normalization"],
        "SymmetryMode" -> record["symmetryMode"], "Arithmetic" -> record["arithmetic"], "Channels" -> channels,
        "Validation" -> Missing["Revalidate"],
        (* a status never exceeds what its arithmetic can establish (review finding 3: numerical data labelled "Exact") *)
        "VerificationStatus" -> First[SortBy[{Lookup[record, "verificationStatus", "Exact"], If[record["arithmetic"] === "Numerical", "Numerical", "Exact"]},
            cgStatusRank]],
        "Domain" -> cgDomainFromRecord[Lookup[record, "domain", None]]|>
];

(*
    Summary: Validate saved CG bundles against an imported group's own data before they enter its store.
    Parameters: data — decoded group data of the snapshot; records — saved bundle records; epoch — saved store epoch.
    Options/defaults: None.
    Returns: A CGCache association (emptyCGCache[epoch] with the validated entries), or InvalidCGData Failure.
    Effects: Pure.
    Failures: A record whose input or target identity is not a stored variant of the group, whose key differs
        from the key recomputed from its identities and conventions, whose copy count differs from the character
        multiplicity, or whose channels fail covariance, dual covariance, pairing, rank, exchange symmetry or
        (Unitary) W = K^dagger.
    Example: a snapshot whose embedding entry was edited fails import with InvalidCGData.
    Remarks: With mode "Trusted" (a ledger-registered snapshot, ImportGroupData; user decision 2026-10-22, fastLoad.md)
        only the identities and the recomputed key are checked: the entries keep their recorded statuses and are served
        without a check (an Unverified one is checked on its first use at a verifying level). Otherwise a stored
        validation label is never trusted; every check is recomputed. With mode "Deferred" the structural checks still run (identities,
        recomputed key, copy count), but the exact channel validation is deferred: the entry carries
        Validation -> Missing["Deferred"] and is validated exactly when it is first served (lookupCG) or mirrored to GAP.
        Final review of the VVMFUse runs (user decision 2026-10-04): exact revalidation of a large store took longer than
        the computation it protects.
    See also: SaveGroupData; ImportGroupData; validateCGBundle; deferredCGValidation.
*)
importCGBundles[data_Association, records_List, epoch_Integer, mode_String : "Full"] := Module[{find, entries = <||>, failure = None},
    find[identity_, id_] := SelectFirst[Values[Lookup[Lookup[Lookup[data, "Representations", <||>], id, <||>], "Variants", <||>]],
        #["Identity"] === identity &, Missing[]];
    Do[Module[{bundle = decodeCGBundle[record], p, q, t, settings, validation, multiplicity, key},
            If[FailureQ[bundle], failure = bundle; Break[]];
            {p, q, t} = MapThread[find, {Append[bundle["InputIdentities"], bundle["TargetIdentity"]], Append[bundle["Pair"], bundle["TargetID"]]}];
            If[AnyTrue[{p, q, t}, MissingQ], failure = makeFailure["InvalidCGData", "A saved CG bundle names a representation the group does not store.",
                <|"Key" -> bundle["Key"]|>]; Break[]];
            key = cgKeyFromParts[data["StateID"], bundle["InputIdentities"], bundle["TargetIdentity"], bundle["Normalization"],
                bundle["SymmetryMode"], bundle["Arithmetic"], If[record["precision"] === "Infinity", Infinity, ToExpression[record["precision"]]]];
            (* a registered file's entries (mode "Trusted", fastLoad.md) keep their recorded statuses: no copy-count or
               channel check; an Unverified one is still checked on its first use at a verifying level (lookupCG) *)
            If[mode === "Trusted",
                If[key =!= bundle["Key"], failure = makeFailure["InvalidCGData", "A saved CG bundle's key does not match its identities.", <|"Key" -> bundle["Key"]|>]; Break[]];
                entries[bundle["Key"]] = Join[bundle, <|"Validation" -> If[bundle["VerificationStatus"] === "Unverified", <|"Skipped" -> True|>, <|"Trusted" -> "RegisteredExport"|>],
                    "Precision" -> If[record["precision"] === "Infinity", Infinity, ToExpression[record["precision"]]]|>];
                Continue[]];
            multiplicity = Lookup[tensorMultiplicities[data["CharacterData"], bundle["Pair"]], bundle["TargetID"], -1];
            If[key =!= bundle["Key"] || Length[bundle["Channels"]] =!= multiplicity,
                failure = makeFailure["InvalidCGData", "A saved CG bundle's key or copy count does not match its identities.", <|"Key" -> bundle["Key"]|>]; Break[]];
            If[mode === "Deferred",
                entries[bundle["Key"]] = Join[bundle, <|"Validation" -> Missing["Deferred"],
                    "Precision" -> If[record["precision"] === "Infinity", Infinity, ToExpression[record["precision"]]]|>];
                Continue[]];
            (* each entry is checked at its own recorded level (an exact entry labelled Numerical numerically); an Unverified
               entry is kept unchecked and is checked on its first use at a verifying level (lookupCG) *)
            If[bundle["VerificationStatus"] === "Unverified",
                entries[bundle["Key"]] = Join[bundle, <|"Validation" -> <|"Skipped" -> True|>,
                    "Precision" -> If[record["precision"] === "Infinity", Infinity, ToExpression[record["precision"]]]|>];
                Continue[]];
            settings = cgCheckSettings[If[bundle["Arithmetic"] === "Exact", arithmeticSettings["Exact", 50, Automatic, Infinity],
                With[{precision = ToExpression[record["precision"]]}, arithmeticSettings["Numerical", precision, Automatic, precision]]],
                <|"Verification" -> If[bundle["Arithmetic"] === "Exact" && bundle["VerificationStatus"] === "Numerical", "Numerical", Automatic]|>];
            validation = cgVerifyBundle[bundle["Channels"], repMatrices[p["Rep"]], repMatrices[q["Rep"]], repMatrices[t["Rep"]],
                bundle["Normalization"], settings, bundle["SymmetryMode"] === "Separate"];
            If[!validation["Passed"],
                failure = makeFailure["InvalidCGData", "A saved CG bundle does not validate against the group's representations.",
                    <|"Key" -> bundle["Key"], "Validation" -> validation["Validation"]|>]; Break[]];
            entries[bundle["Key"]] = Join[bundle, <|"Validation" -> validation["Validation"], "ValidationDomain" -> validation["ValidationDomain"],
                "Precision" -> If[record["precision"] === "Infinity", Infinity, ToExpression[record["precision"]]]|>]],
        {record, records}];
    If[failure =!= None, failure, Join[emptyCGCache[epoch], <|"Entries" -> entries|>]]
];

(*
    Summary: Whether a validateCGBundle result accepts a bundle.
    Parameters: validation — validateCGBundle result; normalization — the bundle's normalization.
    Options/defaults: None.
    Returns: True or False.
    Effects: Pure.
    Failures: None.
    Example: cgValidationPassedQ[<|"Covariance" -> True, "Unitary" -> False|>, "Dual"] is True.
    See also: importCGBundles; deferredCGValidation.
*)
cgValidationPassedQ[validation_Association, normalization_] :=
    AllTrue[KeyDrop[validation, {"Residual", "Unitary"}], TrueQ] && (normalization =!= "Unitary" || TrueQ[validation["Unitary"]]);
cgValidationPassedQ[___] := False;

(* Checks of stored entries (deferred at import, or weaker than a call's level) done in this kernel, by {bundle key, hash
   of its channels, status the check establishes}: the key fixes the state, the variant identities and the conventions,
   and the hash the channel data, so two live copies of a group with different stored channels under one key (e.g. one
   from an edited file) never share a result. Values are cgVerifyBundle results. A FieldMethodUnavailable outcome is
   thrown before the memo is written (a domain failure is not a check result). *)
$CGDeferredValidations = <||>;
deferredCGMemoKey[entry_Association, level_ : Automatic] := {entry["Key"], Hash[entry["Channels"], "SHA256"],
    cgRequiredStatus[level, entry["Arithmetic"]]};

(*
    Summary: Check a stored entry at a call's verification level (memoised).
    Parameters: entry — stored bundle; p, q, t — the matrices of its input and target variants; carrier — the call's
        settings (cgCheckSettings: FieldMethod, Verification, CheckPrecision); Automatic level when omitted.
    Options/defaults: carrier <||>.
    Returns: cgVerifyBundle result.
    Effects: Records the result in $CGDeferredValidations.
    Failures: Throws FieldMethodUnavailable (cgArithmetic) for an explicit FieldMethod without a domain.
    Example: cgStoredCheck[entry, p, q, t, <|"Verification" -> "Numerical"|>]["VerificationStatus"] is "Numerical".
    See also: deferredCGValidation; lookupCG.
*)
cgStoredCheck[entry_Association, p_List, q_List, t_List, carrier_Association : <||>] := Module[{level = Lookup[carrier, "Verification", Automatic], key, result, settings},
    key = deferredCGMemoKey[entry, level];
    result = Lookup[$CGDeferredValidations, Key[key], None];
    If[AssociationQ[result] && KeyExistsQ[result, "Passed"],
        If[result["Passed"] =!= True, $CGDeferredValidations[Append[Most[key], "Invalid"]] = True];
        Return[result]];
    settings = cgCheckSettings[If[entry["Arithmetic"] === "Exact", arithmeticSettings["Exact", 50, Automatic, Infinity],
        arithmeticSettings["Numerical", entry["Precision"], Automatic, entry["Precision"]]], Join[carrier, <|"Verification" -> level|>]];
    result = cgVerifyBundle[KeyDrop[#, "Copy"] & /@ entry["Channels"], p, q, t, entry["Normalization"], settings, entry["SymmetryMode"] === "Separate"];
    $CGDeferredValidations[key] = result;
    (* the entry's invalid mark, {key, channel hash, "Invalid"} in the same memo (one lookup for cgStoredInvalidQ); a
       failed check at any level is final for these channels: a later passed check at a weaker level never clears it
       (review R2-1) *)
    If[result["Passed"] =!= True, $CGDeferredValidations[Append[Most[key], "Invalid"]] = True];
    result
];

(* Whether some check of this kernel found the stored entry invalid (it is then replaced by a recomputed bundle). *)
cgStoredInvalidQ[entry_Association] := TrueQ[Lookup[$CGDeferredValidations, Key[Append[Most[deferredCGMemoKey[entry]], "Invalid"]], False]];

(*
    Summary: The validation of a stored entry whose validation was deferred at import (memoised by key).
    Parameters: entry — stored bundle; p, q, t — the matrices of its input and target variants; carrier — the call's
        settings (level and domain; Automatic when omitted).
    Options/defaults: carrier <||> (the full level of the entry's arithmetic).
    Returns: The entry with its validation and the stronger of its stored status and the check's, or Failure
        InvalidCGData when the channels do not validate. An entry that is not deferred is returned unchanged.
    Effects: Records the result in $CGDeferredValidations (by key, channel hash and level).
    Failures: InvalidCGData.
    Example: deferredCGValidation[entry, p, q, t]["Validation"]["Covariance"] is True for a valid deferred T' bundle.
    See also: importCGBundles; lookupCG; syncCGMirror.
*)
deferredCGValidation[entry_Association, p_List, q_List, t_List, carrier_Association : <||>] := Module[{checked},
    If[entry["Validation"] =!= Missing["Deferred"], Return[entry]];
    checked = cgStoredCheck[entry, p, q, t, carrier];
    If[checked["Passed"], cgCheckedEntry[entry, checked],
        makeFailure["InvalidCGData", "A stored CG bundle does not validate against the group's representations.",
            <|"Key" -> entry["Key"], "Validation" -> checked["Validation"]|>]]
];
(* the entry after a passed check: its validation, and the stronger of its stored status and the check's *)
cgCheckedEntry[entry_Association, checked_Association] := Join[entry, <|"Validation" -> checked["Validation"],
    "VerificationStatus" -> Last[SortBy[{cgEntryStatus[entry], checked["VerificationStatus"]}, cgStatusRank]],
    "ValidationDomain" -> checked["ValidationDomain"]|>];

(*
    Summary: A stored entry as SaveGroupData writes it.
    Parameters: entry — stored bundle.
    Options/defaults: None.
    Returns: The entry, marked "Unverified" when a check of this kernel found it invalid (methodOptionsPlan.md 1.4), so a
        later trusted import never serves it as checked.
    Effects: Pure (reads $CGDeferredValidations).
    Failures: None.
    Example: a deferred entry whose first-use check failed is saved with "verificationStatus" "Unverified".
    See also: groupSnapshot; cgStoredInvalidQ.
*)
cgSnapshotEntry[entry_Association] := If[cgStoredInvalidQ[entry], Join[entry, <|"VerificationStatus" -> "Unverified"|>], entry];

(*
    Summary: Complete a computed bundle with the identities a stored entry needs.
    Parameters: request; bundle — from computeCGBundle.
    Options/defaults: None.
    Returns: The bundle with Pair, InputIdentities, TargetIdentity, Normalization, SymmetryMode and Arithmetic.
    Effects: Pure.
    Failures: None.
    Example: storedCGBundle[request, b]["Pair"] is request["Pair"].
    See also: acceptCGBundles; CGCacheInformation.
*)
storedCGBundle[request_Association, bundle_Association] := Join[bundle, <|"Pair" -> request["Pair"],
    "InputIdentities" -> (request["Variants"][#]["Identity"] & /@ request["Pair"]),
    "TargetIdentity" -> request["Variants"][bundle["TargetID"]]["Identity"], "Normalization" -> request["Normalization"],
    "SymmetryMode" -> request["SymmetryMode"], "Arithmetic" -> request["Arithmetic"],
    "Precision" -> If[request["Arithmetic"] === "Exact", Infinity, request["Settings"]["Precision"]]|>];

(*
    Summary: Publish newly validated bundles, and status upgrades of stored entries, into the group's Wolfram CG store.
    Parameters: group — live Group; bundles — stored bundles (storedCGBundle), each checked by cgVerifyBundle at the
        call's level; options — validated settings (unused: publication starts no worker); upgrades — stored entries
        whose check at the call's level raised their status (lookupCG mark "upgraded").
    Options/defaults: upgrades {}.
    Returns: <|"Published" -> number of bundles newly stored|> (with "Upgraded" -> n when statuses were raised), or
        Failure. A commit holding only upgrades that fails returns <|"Published" -> 0, "Upgraded" -> 0, "UpgradeFailure"|>
        (the call still returns the data it verified; methodOptionsPlan.md 1.4).
    Effects: One commitGroup of CGCache against the revision read here; no GAP worker, checkpoint or retained state.
    Failures: The record encoding (every bundle must be serializable, so a later SaveGroupData cannot fail on it);
        StateConflict / commit failures when the group changed since it was read.
    Example: acceptCGBundles[g, {bundle}, options] makes lookupCG find the bundle.
    Remarks: D-S4-8 (user decision 2026-10-01): CG coefficients are computed in Wolfram, so they are accepted in the
        Wolfram store directly; GAP receives CG records only on demand (syncCGMirror), when a GAP route needs them.
        The commit is atomic against the group revision, so no acceptance lease is needed. A key the store already
        holds keeps its accepted bundle (its copy convention), unless a check of this kernel found it invalid
        (cgStoredInvalidQ: a failed deferred or upgrade check), and a key repeated in the input is stored once. An
        upgrade changes only the status and validation of an entry whose channels are unchanged.
    See also: encodeCGBundle; syncCGMirror; CGCoefficients.
*)
acceptCGBundles[group_Group, bundles_List, options_Association, upgrades_List : {}] := Module[{data, fresh, raised, records, committed},
    If[bundles === {} && upgrades === {}, Return[<|"Published" -> 0|>]];
    data = groupData[group]; If[FailureQ[data], Return[data]];
    (* a stored entry that a check of this kernel found invalid is replaced by the newly validated bundle *)
    fresh = Select[DeleteDuplicatesBy[bundles, #["Key"] &], !KeyExistsQ[data["CGCache"]["Entries"], #["Key"]] ||
        cgStoredInvalidQ[data["CGCache"]["Entries"][#["Key"]]] &];
    (* upgrades apply only to the entry that was checked (same channels) and only when they raise its status *)
    raised = Select[DeleteDuplicatesBy[KeyDrop[#, "LookupMark"] & /@ upgrades, #["Key"] &], With[{stored = Lookup[data["CGCache"]["Entries"], #["Key"], None]},
        AssociationQ[stored] && !MemberQ[Lookup[fresh, "Key", {}], #["Key"]] && stored["Channels"] === #["Channels"] &&
            cgStatusRank[cgEntryStatus[#]] > cgStatusRank[cgEntryStatus[stored]]] &];
    If[fresh === {} && raised === {}, Return[<|"Published" -> 0|>]];
    records = encodeCGBundle[#, #["Precision"]] & /@ fresh;
    If[!FreeQ[records, _Failure], Return[FirstCase[records, _Failure, Null, Infinity]]];
    committed = commitGroup[group, data["Revision"], <|"CGCache" -> Join[data["CGCache"],
        <|"Entries" -> Join[data["CGCache"]["Entries"], AssociationThread[Lookup[raised, "Key", {}], raised],
            AssociationThread[Lookup[fresh, "Key", {}], fresh]]|>]|>];
    (* a bundle this call verified clears an invalid mark on the same channels (a check that once failed on correct data,
       e.g. by rounding, must not condemn the recomputed identical bundle for the rest of the session; review R3-1) *)
    If[!FailureQ[committed], Scan[If[cgEntryStatus[#] =!= "Unverified",
        KeyDropFrom[$CGDeferredValidations, Key[Append[Most[deferredCGMemoKey[#]], "Invalid"]]]] &, fresh]];
    Which[
        !FailureQ[committed], Join[<|"Published" -> Length[fresh]|>, If[raised === {}, <||>, <|"Upgraded" -> Length[raised]|>]],
        fresh === {}, <|"Published" -> 0, "Upgraded" -> 0, "UpgradeFailure" -> committed|>,
        True, committed]
];

(*
    Summary: Give a GAP worker the stored CG records it needs (on demand).
    Parameters: group — live Group; keys — stored CG keys (a repeated key is sent once); options — job settings
        (StoreGAPState, AttemptTimeLimit, budgets).
    Options/defaults: As any group enrichment.
    Returns: <|"Mirrored" -> number of records, "Epoch", "GAPState" -> "Retained" | "NotRetained"|>, with "Reason"
        when not retained (the retention failure, or "StoreGAPState -> False"); or Failure.
    Effects: One runGroupEnrichment["CG"]: a new generation whose GAP state holds exactly these records (and the
        store's epoch); the Wolfram store is unchanged.
    Failures: InvalidInput for keys that are not stored; the enrichment's own failure (Timeout, SaveFailed, ...)
        unless the generation was verifiably produced and only its retention failed; StateConflict when the
        operation did not produce the next generation with the expected epoch and key set.
    Example: syncCGMirror[g, Keys[CGCacheInformation-entries], opts]["Mirrored"] is the number of keys.
    Remarks: D-S4-8. No current GAP route reads CG records; this is the path a future one uses. Acceptance needs
        positive evidence (generation + 1, operation CG, mirror epoch and keys), because every enrichment failure
        carries the group as PartialResult. When retention failed, the generation was verified but no GAP state holds
        the records after the call, which GAPState -> "NotRetained" reports.
    See also: acceptCGBundles; VVMF_IncorporateCG.
*)
syncCGMirror[group_Group, keys_List, options_Association] := Module[{data, cache, unique = DeleteDuplicates[keys], records, run, after, mirror, verified, retained,
    find, checked},
    data = groupData[group]; If[FailureQ[data], Return[data]];
    cache = data["CGCache"];
    If[!SubsetQ[Keys[cache["Entries"]], unique], Return[makeFailure["InvalidInput", "Only stored CG keys can be given to GAP.",
        <|"Keys" -> Complement[unique, Keys[cache["Entries"]]]|>]]];
    (* GAP receives only fully validated records: entries deferred at import, and entries weaker than their
       arithmetic's full level (Numerical-checked exact data, Unverified), are checked at that level first, and a failure
       ends the call before anything is mirrored *)
    find[identity_, id_] := SelectFirst[Values[Lookup[Lookup[Lookup[data, "Representations", <||>], id, <||>], "Variants", <||>]],
        #["Identity"] === identity &, Missing[]];
    checked = Map[Function[entry, If[entry["Validation"] =!= Missing["Deferred"] &&
            cgStatusRank[cgEntryStatus[entry]] >= cgStatusRank[cgRequiredStatus[Automatic, entry["Arithmetic"]]], entry,
        With[{v = MapThread[find, {Append[entry["InputIdentities"], entry["TargetIdentity"]], Append[entry["Pair"], entry["TargetID"]]}]},
            If[AnyTrue[v, MissingQ], makeFailure["InvalidCGData", "A stored CG bundle names a representation the group does not store.", <|"Key" -> entry["Key"]|>],
                With[{c = cgStoredCheck[entry, Sequence @@ (repMatrices[#["Rep"]] & /@ v)]},
                    If[c["Passed"], cgCheckedEntry[entry, c], makeFailure["InvalidCGData", "A stored CG bundle does not validate against the group's representations.",
                        <|"Key" -> entry["Key"], "Validation" -> c["Validation"]|>]]]]]]], Lookup[cache["Entries"], unique]];
    If[!FreeQ[checked, _Failure, {1}], Return[FirstCase[checked, _Failure, Null, {1}]]];
    records = encodeCGBundle[#, Lookup[#, "Precision", Infinity]] & /@ checked;
    If[!FreeQ[records, _Failure], Return[FirstCase[records, _Failure, Null, Infinity]]];
    run = runGroupEnrichment[group, "CG", <|"cgUpdate" -> <|"epoch" -> ToString[cache["Epoch"]], "retain" -> {}, "add" -> records|>|>,
        Join[options, <|Method -> Automatic, GroupModel -> Automatic|>]];
    after = groupData[group]; If[FailureQ[after], Return[If[FailureQ[run], run, after]]];
    mirror = Lookup[after["LastComputation"], "cgMirror", None];
    verified = after["StateGeneration"] === data["StateGeneration"] + 1 && Lookup[after["LastComputation"], "Operation", None] === "CG" &&
        AssociationQ[mirror] && Lookup[mirror, "epoch", None] === ToString[cache["Epoch"]] && Sort[Lookup[mirror, "keys", {}]] === Sort[unique];
    If[FailureQ[run] && !(verified && Lookup[after["LastComputation"], "Status", None] === "SaveFailed"), Return[run]];
    If[!verified, Return[makeFailure["StateConflict", "The GAP CG operation did not produce the expected generation, epoch or key set."]]];
    retained = !FailureQ[run] && StringQ[after["GAPCachePath"]];
    Join[<|"Mirrored" -> Length[unique], "Epoch" -> cache["Epoch"], "GAPState" -> If[retained, "Retained", "NotRetained"]|>,
        If[retained, <||>, <|"Reason" -> If[FailureQ[run], run, "StoreGAPState -> False"]|>]]
];

(*
    Summary: Resolve a CG request, computing missing input and target representations for a group.
    Parameters: context — Group or RepresentationContext; pair; targets; effective — validated options.
    Options/defaults: ComputeMissingRepresentations True computes only the missing input and positive-multiplicity
        target irreps (ComputeGroupRepresentations with the call's job options); False reports them.
    Returns: Request (makeCGRequest), or Failure.
    Effects: May publish representation generations on the group (Stage 2).
    Failures: MissingRepresentations (context, or ComputeMissingRepresentations False); representation failures;
        StateConflict when a starting variant changed while the prerequisites were computed.
    Example: a character-only group gets exactly the representations the requested pair needs.
    Remarks: The starting variants of the irreps already present are frozen and must still be active afterwards,
        so a concurrent basis change cannot mix revisions.
    See also: makeCGRequest; CGCoefficients.
*)
prepareCGRequest[context_, pair_List, targets_, effective_Association] := Module[{request, starting, computed, again},
    request = makeCGRequest[context, pair, targets, effective];
    If[FailureQ[request] || request["Missing"] === {}, Return[request]];
    If[Head[context] =!= Group || !TrueQ[effective[ComputeMissingRepresentations]],
        Return[makeFailure["MissingRepresentations", "The CG request needs matrices that are not stored.",
            <|"IrrepIDs" -> request["Missing"], "Remedy" -> If[Head[context] === Group,
                "Use ComputeMissingRepresentations -> True or ComputeGroupRepresentations.",
                "Compute the representations on the group and take a new RepresentationContext."]|>]]];
    starting = #["Identity"] & /@ DeleteCases[request["Variants"], _Missing];
    (* an internal step inherits the call's level (inheritedVerification); the CG result is bounded by its inputs' statuses *)
    computed = ComputeGroupRepresentations[context, request["Missing"], Sequence @@ inheritedVerification[effective[Verification]],
        Sequence @@ Normal[KeyTake[effective, {StoreGAPState, AttemptTimeLimit, CoreBudget, MemoryBudget, ProgressFunction}]]];
    again = makeCGRequest[context, pair, targets, effective];
    (* A failure after the representations were accepted (for example a retention failure) does not stop the CG
       call: the stored matrices are the positive evidence; any other failure is returned unchanged. *)
    If[FailureQ[computed] && (FailureQ[again] || again["Missing"] =!= {}), Return[computed]];
    If[FailureQ[again], Return[again]];
    If[again["Missing"] =!= {}, Return[makeFailure["MissingRepresentations", "Representations are still missing after computation.",
        <|"IrrepIDs" -> again["Missing"]|>]]];
    If[KeyValueMap[#2 === again["Variants"][#1]["Identity"] &, starting] =!= ConstantArray[True, Length[starting]],
        Return[makeFailure["StateConflict", "A stored representation changed while the CG prerequisites were computed; retry the call."]]];
    again
];

(*
    Summary: Serve every selected target of a request from the store or by computation.
    Parameters: request; effective.
    Options/defaults: Cache lookup precedes the method's applicability: a compatible stored bundle is returned even
        when the requested method is unavailable.
    Returns: <|"Bundles" -> target -> bundle, "Hits" -> target IDs, "New" -> stored bundles to publish (replacements
        of invalid stored entries included), "Upgrades" -> stored entries whose status a check raised, "Attempts" ->
        target -> outcomes, "Failure" -> the first target failure or None, "FailedTargets" -> IDs|>.
    Effects: Pure (publication is the caller's).
    Failures: None at this level: a failing target (FieldMethodUnavailable included) is recorded and the remaining
        targets are still served, so the caller can publish every validated bundle before reporting the failure.
    Example: a second call for the same pair reports every target in "Hits".
    See also: cgBundleByMethod; acceptCGBundles; cgCoverageFailure.
*)
resolveCGTargets[request_Association] := Module[{bundles = <||>, hits = {}, new = {}, upgrades = {}, attempts = <||>, failure = None, failed = {},
        method = request["Options"][Method], recompute = TrueQ[Lookup[request["Options"], Recompute, False]], other = {}},
    Do[Module[{stored, computed},
            stored = cgFieldCatch[lookupCG[request, t]];
            If[FailureQ[stored], If[failure === None, failure = stored]; AppendTo[failed, t]; Continue[]];
            Which[
                (* an explicit Method is served from the store with a note naming the stored method (user decision U1,
                   methodOptionsPlan.md 2A.4); Recompute -> True computes with the requested method instead *)
                AssociationQ[stored] && !(recompute && request["Multiplicities"][t] > 0),
                If[stored["LookupMark"] === "upgraded", AppendTo[upgrades, KeyDrop[stored, "LookupMark"]]];
                If[method =!= Automatic && request["Multiplicities"][t] > 0 && !cgStoredMethodMatchQ[stored["Method"], method],
                    AppendTo[other, stored["Method"]]];
                bundles[t] = KeyDrop[stored, "LookupMark"]; AppendTo[hits, t],
                request["Multiplicities"][t] === 0, bundles[t] = computeCGBundle[request, t, "GeneratorEquations"],
                True,
                computed = cgBundleByMethod[request, t];
                If[FailureQ[computed], If[failure === None, failure = computed]; AppendTo[failed, t]; Continue[]];
                attempts[t] = computed["Attempts"];
                bundles[t] = storedCGBundle[request, KeyDrop[computed, "Attempts"]];
                (* a recomputation never replaces a stored entry (vectors made earlier refer to its channels): it is
                   returned unstored, with channel IDs of its own (makeCGData) *)
                If[AssociationQ[stored], bundles[t] = Join[bundles[t], <|"Unstored" -> True|>], AppendTo[new, bundles[t]]]]],
        {t, request["Targets"]}];
    <|"Bundles" -> bundles, "Hits" -> hits, "New" -> new, "Upgrades" -> upgrades, "Attempts" -> attempts, "Failure" -> failure, "FailedTargets" -> failed,
        "Notes" -> Join[Lookup[request, "Notes", {}],
            (* an explicit UnitarizationMethod acts only on transported spectral routes (review 2B finding 11) *)
            If[Lookup[request["Options"], UnitarizationMethod, Automatic] =!= Automatic && new =!= {} &&
                    NoneTrue[new, StringContainsQ[#["Method"], "temporary unitary transport"] &],
                {"UnitarizationMethod had no effect: no computed target used a temporary unitary transport"}, {}]],
        "OtherMethods" -> other|>
];

(* The note for targets served from the store under an explicit Method (one line per call; CacheCG has no Recompute). *)
cgOtherMethodsNote[other_List, recompute_] := If[other === {}, {},
    {ToString[Length[other]] <> If[Length[other] === 1, " target was", " targets were"] <> " served from the store, made by " <>
        StringRiffle[DeleteDuplicates[other], ", "] <> " (not by the requested Method)" <>
        If[TrueQ[recompute], "; CGCoefficients[..., Recompute -> True] computes with the requested method", "; stored coefficients are never replaced (CleanCGCache, then compute, changes them)"]}];

(* Whether a stored bundle's method label names one of the requested methods ("Flip:" and " (...)" qualifiers dropped). *)
cgStoredMethodMatchQ[label_String, method_] := MemberQ[Flatten[{method}],
    StringReplace[label, {StartOfString ~~ "Flip:" -> "", " (" ~~ ___ ~~ EndOfString -> ""}]];
cgStoredMethodMatchQ[_, _] := False;

(*
    Summary: The failure of a partially served CG request, with its true coverage.
    Parameters: resolved — resolveCGTargets result with a Failure; request; published — True when the call's new
        bundles were accepted into the store (or there were none, or the call was a context call).
    Options/defaults: None.
    Returns: The first target failure, extended with "Coverage" -> <|"AcceptedTargets" -> targets now served by the
        store or the cache hit (zero-multiplicity targets included), "ComputedTargets" -> validated targets of this
        call (published only when the call could publish), "FailedTargets", "PendingTargets"|>.
    Effects: Pure.
    Failures: None.
    Example: with the last target failing, AcceptedTargets lists the others and a repeated call computes only it.
    See also: CGCoefficients; resolveCGTargets.
*)
cgCoverageFailure[resolved_Association, request_Association, published_] := Module[{failure = resolved["Failure"], served},
    served = If[TrueQ[published], Keys[resolved["Bundles"]], Join[resolved["Hits"], Select[Keys[resolved["Bundles"]], request["Multiplicities"][#] === 0 &]]];
    Failure[First[failure], Join[Last[failure], <|"Coverage" -> <|"AcceptedTargets" -> served, "ComputedTargets" -> Keys[resolved["Bundles"]],
        "FailedTargets" -> resolved["FailedTargets"], "PendingTargets" -> Complement[request["Targets"], served]|>|>]]
];

(*
    Summary: The one notice line of a CG call about its new bundles (methodOptionsPlan.md 1.5).
    Parameters: bundles — the call's newly computed bundles.
    Options/defaults: None.
    Returns: Null.
    Effects: At most one notice (Print, silenced by ConfigureVVMFTool[Notices -> False]); main kernel only.
    Failures: None.
    Example: a FieldMethod -> "Cyclotomic" call whose field is much larger than its values notes the degrees.
    Remarks: The conditions come from the bundles' records (exactField never prints; subkernels never print).
    See also: CGCoefficients; CacheCG.
*)
cgCallNotice[bundles_List, notes_List : {}] := Module[{over, unverified, numerical, parts = DeleteDuplicates[notes]},
    over = Select[Lookup[#, "Domain", Missing[]] & /@ bundles, AssociationQ[#] && KeyExistsQ[#, "Oversized"] &];
    If[over =!= {}, AppendTo[parts, "FieldMethod -> \"Cyclotomic\" used a cyclotomic field of degree " <> ToString[Max[over[[All, "Oversized", 1]]]] <>
        " for values of degree at most " <> ToString[Max[over[[All, "Oversized", 2]]]] <> " (" <> ToString[Length[over]] <>
        If[Length[over] === 1, " target", " targets"] <> "); the arithmetic may be slow"]];
    unverified = Count[cgEntryStatus /@ bundles, "Unverified"];
    If[unverified > 0, AppendTo[parts, ToString[unverified] <> If[unverified === 1, " new CG bundle is", " new CG bundles are"] <>
        " unverified (Verification -> None) and marked \"Unverified\""]];
    numerical = Count[bundles, b_ /; Lookup[b, "Arithmetic", "Exact"] === "Exact" && cgEntryStatus[b] === "Numerical"];
    If[numerical > 0, AppendTo[parts, ToString[numerical] <> If[numerical === 1, " new exact CG bundle was", " new exact CG bundles were"] <>
        " checked numerically only (Verification -> \"Numerical\")"]];
    (* inside a derived call ($cgNoticesShown is a list) a note already shown is not repeated *)
    If[ListQ[$cgNoticesShown], parts = Complement[parts, $cgNoticesShown]; $cgNoticesShown = Join[$cgNoticesShown, parts]];
    If[parts =!= {}, notice["Note: " <> StringRiffle[parts, "; "] <> "."]];
];
$cgNoticesShown = None;

(* Job options, FieldMethod and Verification read the session (ConfigureVVMFTool) through delayed defaults
   (methodOptionsPlan.md 1.2; before, the hard-coded job defaults hid the session settings from the CG family). *)
Options[CGCoefficients] = {Method -> Automatic, Normalization -> Automatic, ExchangeSymmetry -> Automatic, Arithmetic -> "Exact",
    WorkingPrecision -> 50, Tolerance -> Automatic, Prefilter -> True, NumberField -> Automatic, MethodData -> Automatic,
    ComputeMissingRepresentations -> True, StoreGAPState :> $Configuration[StoreGAPState],
    AttemptTimeLimit :> $Configuration[AttemptTimeLimit], CoreBudget :> $Configuration[CoreBudget],
    MemoryBudget :> $Configuration[MemoryBudget], ProgressFunction :> $Configuration[ProgressFunction],
    FieldMethod :> $Configuration[FieldMethod], Verification :> $Configuration[Verification], Recompute -> False,
    UnitarizationMethod -> Automatic};
(* the derived functions take FieldMethod and Verification (their records carry the status, methodOptionsPlan.md 2C.4);
   Verification defaults to plain Automatic, never the session's CG value (Phase 1's R2-1, kept by 2D: a session "Exact"
   would otherwise refuse every numerical-model contraction); FieldMethod follows the session *)
cgDerivedOptions[] := Append[DeleteCases[Options[CGCoefficients], (Rule | RuleDelayed)[Verification | Recompute, _]], Verification -> Automatic];

(*
    Summary: Clebsch-Gordan coefficients of an ordered pair of irreps for selected targets.
    Parameters: c — Group or RepresentationContext; pair — {p, q} irrep IDs; targets — All (default), an ID or a
        duplicate-free list.
    Options/defaults: Method Automatic ($CGMethodOrder) or one registered method; Normalization Automatic;
        ExchangeSymmetry Automatic; Arithmetic "Exact" (WorkingPrecision, Tolerance for "Numerical"); Prefilter True;
        NumberField Automatic; MethodData Automatic; ComputeMissingRepresentations True; FieldMethod (the exact domain)
        and Verification (Automatic | "Exact" | "Numerical" | None) and the job options default to the session
        (ConfigureVVMFTool).
    Returns: CGData with every copy of every selected target (empty for multiplicity zero), with "VerificationStatus"
        (weakest of its targets) and per target Provenance "Domain", "ValidationDomain", "CheckStatus" (the stored entry's
        own check) and "Verification" (the served status: the weakest of that check, the group and the pair's and the
        target's variants, methodOptionsPlan.md 2C.2); or Failure.
        A group call's CGData also has "Publication" -> <|"Published" -> number of new bundles stored|> (with
        "Upgraded" when stored statuses were raised, "UpgradeFailure" when only that commit failed).
    Effects: Group calls may compute missing representations (GAP) and store new bundles in the group's Wolfram CG
        store (one atomic commit per call, no GAP work: D-S4-8). Context calls never publish CG bundles; they read the
        live group's store when its state matches. The native GAP routes (SubgroupChain, AveragedBSGS, Serre,
        SerreBSGS) run their worker query on the live group even for a context call, which advances its state
        generation (and retains a workspace with StoreGAPState -> True) without changing its mathematical data.
    Failures: Option failures; UnverifiedContext; InvalidIrrep; MissingRepresentations; FieldMethodUnavailable; MethodExhausted or the
        explicit method's failure with "Coverage" (AcceptedTargets, ComputedTargets, FailedTargets, PendingTargets):
        the other targets are still computed and, on a group, published first; storage failures.
    Example: Length[CGIntertwiners[CGCoefficients[g, {t, t}, t], t]] is 2 for the A4 triplet.
    Remarks: Cache hits keep the accepted copy convention; different uncached methods may choose different valid
        phases or multiplicity bases.
    See also: CGIntertwiners; CGMatrix; ValidateCG; CacheCG.
*)
CGCoefficients[context : (_Group | _RepresentationContext), pair : {_String, _String}, targets : Except[_Rule | _RuleDelayed] : All,
    options : OptionsPattern[]] := Module[{effective, request, resolved, accepted},
    effective = resolveOperationOptions[CGCoefficients, "CGCoefficients", {options}];
    If[FailureQ[effective], Return[effective]];
    request = prepareCGRequest[context, pair, targets, effective];
    If[FailureQ[request], Return[request]];
    resolved = resolveCGTargets[request];
    cgCallNotice[resolved["New"], Join[resolved["Notes"], cgOtherMethodsNote[resolved["OtherMethods"], True], cgWeakInputsNote[request]]];
    (* Every validated bundle is published, even when another target failed, so a repeated call resumes only the
       missing targets. *)
    accepted = None;
    If[Head[context] === Group && (resolved["New"] =!= {} || resolved["Upgrades"] =!= {}),
        accepted = acceptCGBundles[context, resolved["New"], effective, resolved["Upgrades"]];
        If[FailureQ[accepted], Return[If[resolved["Failure"] === None, accepted,
            (* both happened: the target failure, its coverage without publication, and the publication failure *)
            With[{coverage = cgCoverageFailure[resolved, request, False]},
                Failure[First[coverage], Join[Last[coverage], <|"PublicationFailure" -> accepted|>]]]]]]];
    If[resolved["Failure"] =!= None, Return[cgCoverageFailure[resolved, request, Head[context] === Group]]];
    (* A group call states how many new bundles it stored. *)
    With[{cg = makeCGData[request, resolved["Bundles"], resolved["Hits"]]},
        If[Head[context] =!= Group, cg, CGData[Join[First[cg], <|"Publication" ->
            If[accepted === None, <|"Published" -> 0|>, accepted]|>]]]]
];
CGCoefficients[context : (_Group | _RepresentationContext), pair : {(_Integer | _String), (_Integer | _String)}, targets : Except[_Rule | _RuleDelayed] : All, options : OptionsPattern[]] /;
    irrepIntegerQ[{pair, targets}] := withIrreps[context, {pair, targets}, CGCoefficients[context, #1, #2, options] &];
CGCoefficients[___] := makeFailure["InvalidInput", "CGCoefficients expects a Group or RepresentationContext, a pair of irrep IDs, targets and options."];

Options[CacheCG] = Join[DeleteCases[Options[CGCoefficients], (Rule | RuleDelayed)[Recompute, _]], {TargetIrreps -> All, ReversePairs -> "Flip"}];

(*
    Summary: Compute and store CG bundles for every ordered pair (or the listed pairs) of a group.
    Parameters: g — live Group; pairs — All (default) or a duplicate-free list of {p, q}.
    Options/defaults: As CGCoefficients, plus TargetIrreps (All, an ID or a list).
    Returns: <|"Complete" -> Boolean, "AcceptedPairs", "AcceptedTargets" -> {p, q} -> IDs, "PendingTargets",
        "AttemptOutcomes", "Publication" -> <|"Published" -> n|> (when bundles were stored)|>, or Failure carrying that
        report.
    Effects: One publication for every new bundle of the call; reverse pairs are obtained by a verified tensor flip
        of the computed orientation (copy order and symmetry tags preserved). A flipped bundle's Method is
        "Flip:" <> the source method, which encodeCGBundle persists, so the orientation survives save and import.
    Failures: As CGCoefficients; the report lists what was accepted before the failure, including the validated
        targets of the failing pair (published with the rest). When the publication itself fails, only targets the
        store already held count as accepted, and an earlier target failure keeps its tag with "PublicationFailure".
    Remarks: A pair with a failing target stays pending while the other pairs continue; the first such failure is
        returned with the report, and a repeated call resumes from the store. A prerequisite failure stops the run.
        A requested subset never computes unrelated pairs.
    Example: CacheCG[g]["Complete"] is True, and later CGCoefficients calls are cache hits.
    See also: CGCoefficients; CGCacheInformation; flipCG.
*)
CacheCG[group_Group, pairs : (All | {{_String, _String} ...}) : All, options : OptionsPattern[]] := Module[
    {effective, ids, list, report, new = {}, upgrades = {}, done = <||>, partial = <||>, stored = <||>, failure = None, outcomes = <||>, notes = {}, other = {}},
    effective = resolveOperationOptions[CacheCG, "CacheCG", {options}];
    If[!FailureQ[effective], effective = resolveIrrepOptions[group, effective]];
    If[FailureQ[effective], Return[effective]];
    ids = With[{d = groupData[group]}, If[FailureQ[d], Return[d], d["IrrepOrder"]]];
    list = If[pairs === All, Tuples[ids, 2], pairs];
    If[!DuplicateFreeQ[list], Return[makeFailure["InvalidInput", "Pairs must be duplicate-free."]]];
    Do[Module[{pair = list[[k]], reverse, request, resolved, flipped, hits = {}},
            reverse = Reverse[pair];
            (* The reverse orientation of a pair computed in this call is obtained by a verified flip (checked at the
               call's level; a stored entry is served as lookupCG serves it, upgrades included). *)
            If[KeyExistsQ[done, reverse] && pair =!= reverse && effective[ReversePairs] === "Flip",
                request = prepareCGRequest[group, pair, effective[TargetIrreps], effective];
                If[!FailureQ[request], notes = Join[notes, Lookup[request, "Notes", {}]]];
                If[FailureQ[request], failure = request; Break[]];
                flipped = AssociationMap[Function[t, Module[{source = done[reverse]["Bundles"][t], channels, checked, hit},
                        If[request["Multiplicities"][t] === 0, Return[source, Module]];
                        hit = cgFieldCatch[lookupCG[request, t]];
                        If[FailureQ[hit], Return[hit, Module]];
                        If[AssociationQ[hit],
                            If[hit["LookupMark"] === "upgraded", AppendTo[upgrades, KeyDrop[hit, "LookupMark"]]];
                            If[effective[Method] =!= Automatic && !cgStoredMethodMatchQ[hit["Method"], effective[Method]], AppendTo[other, hit["Method"]]];
                            AppendTo[hits, t]; Return[KeyDrop[hit, "LookupMark"], Module]];
                        (* flipCG takes the source orientation's dimensions: the source pair is reverse = {q, p}. *)
                        channels = flipCG[source["Channels"], request["Variants"][#]["Dimension"] & /@ reverse];
                        checked = cgFieldCatch[cgVerifyBundle[channels, request["Variants"][pair[[1]]]["Matrices"], request["Variants"][pair[[2]]]["Matrices"],
                            request["Variants"][t]["Matrices"], request["Normalization"], request["Settings"], request["Exchange"], False]];
                        If[FailureQ[checked], Return[checked, Module]];
                        If[!checked["Passed"], Return[$Failed, Module]];
                        storedCGBundle[request, Join[<|"Key" -> cgCacheKey[request, t], "TargetID" -> t, "Channels" -> channels,
                            "Method" -> "Flip:" <> source["Method"], "Domain" -> Lookup[source, "Domain", Missing["NotRecorded"]]|>, KeyDrop[checked, "Passed"]]]]],
                    request["Targets"]];
                If[!FreeQ[flipped, _Failure, {1}], failure = FirstCase[Values[flipped], _Failure]; Break[]];
                If[!FreeQ[flipped, $Failed], failure = makeFailure["UnprovedIdentity", "A flipped reverse-pair bundle did not validate.", <|"Pair" -> pair|>]; Break[]];
                new = Join[new, Select[Values[flipped], AssociationQ[#] && Length[#["Channels"]] > 0 && !MemberQ[hits, #["TargetID"]] &]];
                stored[pair] = Select[request["Targets"], request["Multiplicities"][#] === 0 || MemberQ[hits, #] &];
                done[pair] = <|"Bundles" -> flipped|>; Continue[]];
            request = prepareCGRequest[group, pair, effective[TargetIrreps], effective];
            If[FailureQ[request], failure = request; Break[]];
            resolved = resolveCGTargets[request];
            notes = Join[notes, resolved["Notes"], cgWeakInputsNote[request]]; other = Join[other, resolved["OtherMethods"]];
            outcomes[pair] = resolved["Attempts"];
            new = Join[new, resolved["New"]];
            upgrades = Join[upgrades, resolved["Upgrades"]];
            stored[pair] = Join[resolved["Hits"], Select[Keys[resolved["Bundles"]], request["Multiplicities"][#] === 0 &]];
            (* A failing target leaves its pair pending; the pair's validated targets and every later pair are still
               computed, published and reported (the first failure is returned). *)
            If[resolved["Failure"] =!= None,
                If[failure === None, failure = cgCoverageFailure[resolved, request, True]];
                partial[pair] = Keys[resolved["Bundles"]]; Continue[]];
            done[pair] = resolved],
        {k, Length[list]}];
    cgCallNotice[DeleteDuplicatesBy[new, #["Key"] &], Join[notes, cgOtherMethodsNote[other, False]]];
    report = <|"AcceptedPairs" -> Keys[done], "AcceptedTargets" -> Join[Keys[#["Bundles"]] & /@ done, partial],
        "PendingTargets" -> Complement[list, Keys[done]], "AttemptOutcomes" -> outcomes|>;
    If[new =!= {} || upgrades =!= {},
        With[{accepted = acceptCGBundles[group, DeleteDuplicatesBy[new, #["Key"] &], effective, upgrades]},
            If[FailureQ[accepted],
                (* Nothing new was published: only what the store already held (cache hits, zero multiplicities)
                   is accepted; an earlier target failure is kept with the publication failure beside it. *)
                report["AcceptedTargets"] = stored;
                report["AcceptedPairs"] = Select[Keys[done], SubsetQ[stored[#], Keys[done[#]["Bundles"]]] &];
                report["PendingTargets"] = Complement[list, report["AcceptedPairs"]];
                failure = If[failure === None, accepted, Failure[First[failure], Join[Last[failure], <|"PublicationFailure" -> accepted|>]]],
                report["Publication"] = accepted]]];
    If[failure =!= None, Failure[First[failure], Join[Last[failure], <|"Report" -> Prepend[report, "Complete" -> False]|>]],
        Prepend[report, "Complete" -> True]]
];
(* a flat pair of irreps is one pair *)
CacheCG[group_Group, pair : {(_Integer | _String), (_Integer | _String)}, options : OptionsPattern[]] := CacheCG[group, {pair}, options];
CacheCG[group_Group, pairs : {{(_Integer | _String), (_Integer | _String)} ...}, options : OptionsPattern[]] /; irrepIntegerQ[pairs] :=
    withIrreps[group, {pairs}, CacheCG[group, #, options] &];
CacheCG[___] := makeFailure["InvalidInput", "CacheCG expects a live Group, All or a list of pairs, and options."];

(*
    Summary: Coverage of the CG store visible to a group or context, without changing anything.
    Parameters: c — Group or RepresentationContext.
    Options/defaults: IrrepForm -> "ID" (pairs and targets as irrep IDs: a program-facing report that VVMFUse uses to
        decide CG coverage, uxUpdatePlan.md review N4); "Index" or "Label" present them by index or label.
    Returns: <|"Epoch", "Entries" -> count, "Pairs" -> <|{p, q} -> <|"Targets" -> IDs, "Conventions" -> list,
        "VerificationStatus" -> <|status -> count|>, "CurrentBasis" -> Boolean|>|>|>, or Failure.
    Effects: Pure read; no worker, no use-time update.
    Failures: UnverifiedContext.
    Example: after CacheCG[g] every ordered pair of irreps appears under "Pairs".
    Remarks: CurrentBasis says whether the entry's input and target identities are the active variants; entries of
        an older basis remain in their own namespace for held vectors.
    See also: CacheCG; CleanCGCache.
*)
Options[CGCacheInformation] = {IrrepForm -> "ID"};
CGCacheInformation[context : (_Group | _RepresentationContext), options : OptionsPattern[]] := Module[{store = cgStore[context], snapshot, active, grouped, effective, info, key},
    effective = resolveOperationOptions[CGCacheInformation, "CGCacheInformation", {options}]; If[FailureQ[effective], Return[effective]];
    snapshot = If[Head[context] === Group, groupData[context], resolveRepContext[context]];
    If[FailureQ[snapshot], Return[snapshot]];
    If[!AssociationQ[store], store = emptyCGCache[]];
    active = #["Identity"] & /@ DeleteCases[AssociationMap[cgVariant[snapshot, #] &, snapshot["CharacterData"]["IrrepIDs"]], _Missing];
    grouped = GroupBy[Values[store["Entries"]], #["Pair"] &];
    info = <|"Epoch" -> store["Epoch"], "Entries" -> Length[store["Entries"]],
        "Pairs" -> Map[Function[entries, <|"Targets" -> Union[Lookup[entries, "TargetID"]],
            "Conventions" -> Union[Map[KeyTake[#, {"Normalization", "SymmetryMode", "Arithmetic"}] &, entries]],
            "VerificationStatus" -> Counts[cgEntryStatus /@ entries],
            "CurrentBasis" -> AllTrue[entries, Function[e, e["InputIdentities"] === Lookup[active, e["Pair"], None] &&
                e["TargetIdentity"] === Lookup[active, e["TargetID"], None]]]|>], grouped]|>;
    If[effective[IrrepForm] === "ID", Return[info]];
    key[id_] := First[Keys[presentIrrepKeys[context, <|id -> 1|>, effective[IrrepForm]]]];
    Join[info, <|"Pairs" -> KeyMap[Map[key], Map[Join[#, <|"Targets" -> key /@ #["Targets"]|>] &, info["Pairs"]]]|>]
];
CGCacheInformation[___] := makeFailure["InvalidInput", "CGCacheInformation expects a Group or RepresentationContext."];

(*
    Summary: Remove stored CG bundles of the listed pairs (all pairs by default).
    Parameters: g — live Group; pairs — All or a list of {p, q}.
    Options/defaults: None.
    Returns: <|"Removed" -> number, "Epoch" -> new epoch|>, or Failure.
    Effects: One commit of CGCache: entries of the pairs in every basis namespace are removed and the eviction epoch
        advances, so a later on-demand GAP sync (syncCGMirror) prunes them from the mirror of any restored workspace. Characters,
        representations, GAP workspaces and already returned CGData/RepVector values are untouched.
    Failures: Unknown groups; StateConflict when the group changed concurrently.
    Example: CleanCGCache[g]["Removed"] is the number of stored bundles.
    Remarks: Later computation may choose new valid copy conventions. CleanGAPCache is separate (it evicts
        binary workspaces only).
    See also: CacheCG; CGCacheInformation.
*)
CleanCGCache[group_Group, pairs : (All | {{_String, _String} ...}) : All] := Module[{data, cache, removed, committed},
    data = groupData[group]; If[FailureQ[data], Return[data]];
    cache = data["CGCache"];
    removed = Keys[Select[cache["Entries"], pairs === All || MemberQ[pairs, #["Pair"]] &]];
    committed = commitGroup[group, data["Revision"], <|"CGCache" -> Join[cache,
        <|"Entries" -> KeyDrop[cache["Entries"], removed], "Epoch" -> cache["Epoch"] + 1|>]|>];
    If[FailureQ[committed], Return[committed]];
    <|"Removed" -> Length[removed], "Epoch" -> cache["Epoch"] + 1|>
];
CleanCGCache[group_Group, pair : {(_Integer | _String), (_Integer | _String)}] := CleanCGCache[group, {pair}];
CleanCGCache[group_Group, pairs : {{(_Integer | _String), (_Integer | _String)} ...}] /; irrepIntegerQ[pairs] := withIrreps[group, {pairs}, CleanCGCache[group, #] &];
CleanCGCache[___] := makeFailure["InvalidInput", "CleanCGCache expects a live Group and All or a list of pairs."];

True
