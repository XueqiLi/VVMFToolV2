(*
    :Title: Incremental owned GAP protocol
    :Context: VVMFTool`Private`
    :Summary: Decode bounded inert messages and match the coordinator's expected handshake.
    :Responsibilities: Split stream chunks, preserve packet order, reject mismatched replies.
    :Dependencies: OwnedProcesses.wl; ResultValidation.wl; Diagnostics.wl.
    :See Also: GAP/Driver.g; GAPWorkers.wl.
*)

$GAPProtocolPrefix = "VVMF_PROTOCOL\t";
$GAPProtocolLimit = 2^20;
If[!AssociationQ[$GAPProtocolBuffers], $GAPProtocolBuffers = <||>];

(*
    Summary: Decode complete protocol lines without interpreting GAP or Wolfram source.
    Parameters: pending — previous unterminated line; chunk — newly received stdout.
    Options/defaults: Each line is bounded to 1 MiB; nonprotocol diagnostics are ignored.
    Returns: Pending/Packets association, or InvalidProtocol Failure.
    Effects: Pure. JSON parsing may report its specific syntax error.
    Failures: Oversized lines, malformed JSON or nonrecord/inexact protocol values.
    Example: a prefix split across two reads remains pending until its terminating newline.
    See also: pollGAPPacket; GAP VVMF_Emit.
*)
parseGAPOutput[pending_String, chunk_String] := Module[
    {text, parts, tail, packets = {}, packet, failure = None},
    text = pending <> chunk;
    parts = StringSplit[text, "\n", All];
    tail = Last[parts];
    If[AnyTrue[parts, StringLength[#] > $GAPProtocolLimit &],
        Return[makeFailure["InvalidProtocol", "A GAP output line exceeds the protocol bound."]]];
    Do[
        If[StringStartsQ[line, $GAPProtocolPrefix],
            packet = Check[ImportString[StringDrop[line, StringLength[$GAPProtocolPrefix]],
                "RawJSON"], $Failed];
            If[!AssociationQ[packet] || !resultJSONQ[packet],
                failure = makeFailure["InvalidProtocol", "GAP emitted malformed protocol JSON."];
                Break[]];
            AppendTo[packets, packet]
        ],
        {line, Most[parts]}
    ];
    If[FailureQ[failure], failure, <|"Pending" -> tail, "Packets" -> packets|>]
];
parseGAPOutput[___] := makeFailure["InvalidProtocol", "Expected GAP output strings."];

(*
    Summary: Check one reply against the exact expected phase and coordinator-owned fields.
    Parameters: packet — decoded record; expected — type and requestID, with phase-specific
        state IDs, generation, status and exact output paths when applicable.
    Options/defaults: Extra native diagnostic fields are permitted; expected fields all match.
    Returns: The packet, or protocol/native Failure.
    Effects: Pure; a matching packet alone does not authorize workspace loading/publication.
    Failures: Missing/mismatched identities, unexpected phase, malformed native failure.
    Example: a checkpointReady reply for another generation fails even if its paths match.
    See also: pollGAPPacket; VVMF_ProtocolFailure.
*)
checkGAPPacket[packet_Association, expected_Association] := Module[{native},
    If[!AllTrue[{"type", "requestID"}, KeyExistsQ[expected, #] &],
        Return[makeFailure["InvalidProtocol", "Expected phase and request identity are required."]]];
    If[Lookup[packet, "type", None] === "failure",
        If[Lookup[packet, "requestID", None] =!= expected["requestID"],
            Return[makeFailure["InvalidProtocol", "The failure belongs to another request."]]];
        native = Lookup[packet, "failure", None];
        If[!AssociationQ[native] || !StringQ[Lookup[native, "tag", None]] ||
            !StringQ[Lookup[native, "message", None]],
            Return[makeFailure["InvalidProtocol", "The native failure is malformed."]]];
        Return[makeFailure[native["tag"], native["message"], <|"Native" -> native|>]]
    ];
    If[!AllTrue[Keys[expected], KeyExistsQ[packet, #] && packet[#] === expected[#] &],
        Return[makeFailure["InvalidProtocol", "The GAP reply does not match the pending handshake.",
            <|"Expected" -> expected, "Received" -> packet|>]]];
    packet
];
checkGAPPacket[___] := makeFailure["InvalidProtocol", "Expected reply and handshake records."];

(*
    Summary: Register an empty protocol buffer for an already owned process.
    Parameters: token — a token returned by startOwnedProcess, before protocol reads begin.
    Options/defaults: None.
    Returns: True or InvalidWorker Failure.
    Effects: Adds one buffer. Repeated initialization fails rather than discarding unread replies.
    Failures: Unknown token or existing buffer.
    Example: initializeGAPProtocol[token] immediately after launching a GAP worker.
    See also: pollGAPPacket; closeGAPProtocol.
*)
initializeGAPProtocol[token_String] := If[
    KeyExistsQ[$OwnedProcesses, token] && !KeyExistsQ[$GAPProtocolBuffers, token],
    AssociateTo[$GAPProtocolBuffers, token -> <|"Pending" -> "", "Packets" -> {}|>]; True,
    makeFailure["InvalidWorker", "The worker is unknown or already has a protocol buffer."]
];
initializeGAPProtocol[___] := makeFailure["InvalidWorker", "Expected an owned worker token."];

(*
    Summary: Read available output and consume at most one expected protocol packet.
    Parameters: token — registered owned worker; expected — checkGAPPacket's handshake record.
    Options/defaults: No waiting; the shared coordinator calls this on each active worker.
    Returns: Matching packet, Missing["Pending"], or Failure.
    Effects: Advances only this worker's ordered buffer and samples its resource allocation.
    Failures: Resource/ownership errors, malformed/out-of-order reply, or exit before reply.
    Example: two replies arriving in one read are delivered by two successive calls.
    Remarks: Budget enforcement precedes consuming queued replies, so expired work cannot win.
    See also: monitorOwnedProcesses; awaitGAPPacket; GAP/Driver.g.
*)
pollGAPPacket[token_String, expected_Association] := Module[{buffer, report, parsed, packet},
    buffer = Lookup[$GAPProtocolBuffers, token, Missing["UnknownWorker"]];
    If[MissingQ[buffer], Return[makeFailure["InvalidWorker", "No owned protocol buffer exists."]]];
    report = pollOwnedProcess[token];
    If[FailureQ[report], Return[report]];
    parsed = parseGAPOutput[buffer["Pending"], report["StandardOutput"]];
    If[FailureQ[parsed], Return[parsed]];
    buffer = <|"Pending" -> parsed["Pending"],
        "Packets" -> Join[buffer["Packets"], parsed["Packets"]]|>;
    If[Length[buffer["Packets"]] > 16,
        Return[makeFailure["InvalidProtocol", "Too many unsolicited GAP replies."]]];
    If[buffer["Packets"] =!= {},
        packet = First[buffer["Packets"]];
        buffer["Packets"] = Rest[buffer["Packets"]];
        AssociateTo[$GAPProtocolBuffers, token -> buffer];
        Return[checkGAPPacket[packet, expected]]
    ];
    AssociateTo[$GAPProtocolBuffers, token -> buffer];
    If[report["Status"] === "Finished",
        makeFailure["IncompleteOutput", "GAP exited before the required reply.",
            <|"ExitCode" -> report["ExitCode"], "Pending" -> buffer["Pending"],
                "StandardError" -> report["StandardError"]|>], Missing["Pending"]]
];
pollGAPPacket[___] := makeFailure["InvalidProtocol", "Expected owned worker and handshake."];

(*
    Summary: Await one handshake for a sequential worker operation.
    Parameters: token and expected — pollGAPPacket arguments.
    Options/defaults: Poll interval 0.01 seconds; the owned worker deadline is authoritative.
    Returns: Packet or Failure, including Cancelled when the caller aborts.
    Effects: Reads this worker only. Batch scheduling uses pollGAPPacket directly.
    Failures: Propagates protocol/worker failures; abort closes this worker and its buffer.
    Example: awaitGAPPacket[token, <|"type" -> "workerReady", "requestID" -> nonce|>].
    See also: pollGAPPacket; closeGAPProtocol.
*)
awaitGAPPacket[token_String, expected_Association] := CheckAbort[Module[{packet},
    packet = pollGAPPacket[token, expected];
    While[MissingQ[packet], Pause[0.01]; packet = pollGAPPacket[token, expected]];
    packet
],
    makeFailure["Cancelled", "The GAP handshake was cancelled.",
        <|"Cleanup" -> closeGAPProtocol[token, "Cancelled"]|>]
];
awaitGAPPacket[___] := makeFailure["InvalidProtocol", "Expected owned worker and handshake."];

(*
    Summary: Release protocol data and terminate the corresponding owned process tree.
    Parameters: token — owned token; reason — diagnostic string.
    Options/defaults: None; repeated cleanup is allowed.
    Returns: stopOwnedProcess's cleanup report or Failure.
    Effects: Drops only this worker's buffer; never selects processes by program name.
    Failures: Retains a buffer when process cleanup fails, permitting explicit recovery.
    Example: closeGAPProtocol[token, "CandidateSaved"] after saving an immutable generation.
    See also: stopOwnedProcess; initializeGAPProtocol.
*)
closeGAPProtocol[token_String, reason_String] := Module[{cleanup},
    cleanup = stopOwnedProcess[token, reason];
    If[!FailureQ[cleanup], KeyDropFrom[$GAPProtocolBuffers, token]];
    cleanup
];
closeGAPProtocol[___] := makeFailure["InvalidWorker", "Expected worker token and reason."];

True
