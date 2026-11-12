# Title: Owned GAP worker and checkpoint protocol
# Summary: Run one operation and prepare paired exact data/workspace saves.
# Dependencies: Diagnostics, JSON, Scalars, Groups, Serialization, Characters, ResultExport.
# Contracts: The coordinator owns every path and worker. Main input alone calls SaveWorkspace.
# See also: Schemas/GroupResult.md; VVMFArch/step1Plan.md checkpoint transactions.

# Load transport dependencies explicitly; optional mathematical packages stay on demand.
VVMF_DRIVER_DEPENDENCIES := rec(json := LoadPackage("json") <> fail, io := LoadPackage("io") <> fail);
# Persistent roots use fail for absent state; rereading the module preserves actual roots.
if not IsBound(VVMF_STATE) then VVMF_STATE := fail; fi;
if not IsBound(VVMF_SAVED_RESULT) then VVMF_SAVED_RESULT := fail; fi;
if not IsBound(VVMF_READY_RECORD) then VVMF_READY_RECORD := fail; fi;

# Summary: Emit one unwrapped line of inert JSON with the protocol prefix.
# Parameters/defaults: message is a JSON-compatible record; no options.
# Returns: true, or the serialization failure without a misleading success packet.
# Effects: Writes stdout, temporarily disables line wrapping and restores its prior setting.
# Failures: Unsupported native payloads cannot be emitted.
# Example: VVMF_Emit(rec(type := "checkpointReady",requestID := "id")) writes one line.
# See also: VVMF_JSONString; VVMF_PrepareCheckpoint.
VVMF_Emit := function(message)
    local encoded, formatting;
    encoded := VVMF_JSONString(message);
    if VVMF_IsFailure(encoded) then return encoded; fi;
    formatting := PrintFormattingStatus("*stdout*");
    SetPrintFormattingStatus("*stdout*",false);
    Print("VVMF_PROTOCOL\t",encoded,"\n");
    SetPrintFormattingStatus("*stdout*",formatting);
    return true;
end;

# Summary: Report a structured worker failure while retaining its request identity.
# Parameters/defaults: failure is VVMF_Failure output; request is the current request
# or an empty record if decoding failed; no options.
# Returns: The original failure.
# Effects: Emits a failure packet only; never emits readiness or success.
# Failures: Missing request metadata is represented as null.
# Example: a failed write is reported with type="failure", not checkpointReady.
# See also: VVMF_Emit; VVMF_PrepareCheckpoint.
VVMF_ProtocolFailure := function(failure,request)
    local message, key;
    message := rec(type := "failure",failure := failure,requestID := fail,stateGeneration := fail);
    if IsRecord(request) then
        for key in ["requestID","stateGeneration"] do
            if IsBound(request.(key)) then message.(key) := request.(key); fi;
        od;
    fi;
    VVMF_Emit(message);
    return failure;
end;

# Summary: Write new exact JSON through an exclusive sibling temporary file and atomic rename.
# Parameters/defaults: path is a new file inside the caller-owned directory; data is inert JSON.
# Returns: true, or SaveFailed/DependencyUnavailable/serialization failure.
# Effects: Creates path.partial with owner-only permissions, handles short writes,
# closes it, and renames to path. Existing paths are never intentional targets.
# Failures: Invalid/existing paths, open/write/close/rename errors preserve existing files;
# an owned temporary file is removed after an ordinary I/O failure.
# Example: VVMF_WriteJSON("/owned/job/result.json",rec(missing := fail)).
# Remarks: The coordinator chooses a unique attempt directory, verifies artifact hashes
# and restoration, then publishes a manifest. Rename alone is not that acceptance step.
# See also: IO_open; IO_write; IO_rename; VVMF_PrepareCheckpoint.
VVMF_WriteJSON := function(path,data)
    local encoded, temporary, descriptor, offset, written, closed, renamed, constants;
    if not IsString(path) or Length(path) = 0 or '\000' in path then
        return VVMF_Failure("SaveFailed","Expected an owned nonempty file path.");
    fi;
    if not VVMF_DRIVER_DEPENDENCIES.io then
        return VVMF_Failure("DependencyUnavailable","Atomic GAP output requires the io package.");
    fi;
    encoded := VVMF_JSONString(data);
    if VVMF_IsFailure(encoded) then return encoded; fi;
    temporary := Concatenation(path,".partial");
    if ValueGlobal("IO_lstat")(path) <> fail or ValueGlobal("IO_lstat")(temporary) <> fail then
        return VVMF_Failure("SaveFailed","The result or temporary path already exists.");
    fi;
    constants := ValueGlobal("IO");
    descriptor := ValueGlobal("IO_open")(temporary,
        constants.O_WRONLY + constants.O_CREAT + constants.O_EXCL,384);
    if descriptor = fail then return VVMF_Failure("SaveFailed","Cannot create the JSON temporary file."); fi;
    offset := 0;
    while offset < Length(encoded) do
        written := ValueGlobal("IO_write")(descriptor,encoded,offset,Length(encoded)-offset);
        if written = fail or written <= 0 then
            ValueGlobal("IO_close")(descriptor);
            RemoveFile(temporary);
            return VVMF_Failure("SaveFailed","Could not finish writing the JSON result.");
        fi;
        offset := offset + written;
    od;
    closed := ValueGlobal("IO_close")(descriptor);
    if closed <> true then
        RemoveFile(temporary);
        return VVMF_Failure("SaveFailed","Could not close the JSON result.");
    fi;
    renamed := ValueGlobal("IO_rename")(temporary,path);
    if renamed <> true then
        RemoveFile(temporary);
        return VVMF_Failure("SaveFailed","Could not publish the JSON result.");
    fi;
    return true;
end;

# Operations that enrich an accepted complete group from its checkpoint or certified typed data.
# Kernel/GAPOperations.wl registers the same names with Source "Typed" and GenerationStep 1.
VVMF_ENRICHMENT_OPERATIONS := ["GroupElementWords","GroupWordOrder","AssignModularGenerators",
    "GroupSubgroups","GeneratorPresentation","CheckGeneratorMap","Representations","Decompose","CG","CGNative","ValidateGroup"];

# Summary: Drop derived native caches older than the request's representation-cache eviction epoch.
# Parameters/defaults: state; request with optional evictionEpoch (nonnegative decimal string).
# Returns: true, or InvalidRequest failure.
# Effects: When the request's epoch is newer than state.cacheEpoch (or none is recorded), unbinds the
# derived native data (the stored decomposition result) and records the epoch; proven data such as
# relators and accepted variants are not derived caches (D8).
# Failures: A malformed epoch.
# Example: a workspace restored after CleanRepresentationCache forgets its stored decomposition result.
# See also: VVMF_Run; Kernel/RepresentationState.wl CleanRepresentationCache.
VVMF_ApplyEvictionEpoch := function(state,request)
    local epoch;
    if not IsBound(request.evictionEpoch) then return true; fi;
    epoch := VVMF_DecodeInteger(request.evictionEpoch);
    if VVMF_IsFailure(epoch) or epoch < 0 then
        return VVMF_Failure("InvalidRequest","The eviction epoch must be a nonnegative decimal integer.");
    fi;
    if not IsBound(state.cacheEpoch) or state.cacheEpoch < epoch then
        if IsBound(state.decompositionResult) then Unbind(state.decompositionResult); fi;
        state.cacheEpoch := epoch;
    fi;
    return true;
end;

# Summary: Run one construction or character operation in the owned worker.
# Parameters/defaults: request supplies protocol identities, operation and its typed
# construction or explicit character method/model. ConstructGAP additionally supplies
# codePath containing exactly the retained, deliberately executable gapCode text.
# Optional modularAssignment explicitly supplies its identity and ordered named S/T words;
# VVMF_AssignST validates the actual pair before it becomes part of the candidate.
# Returns: Candidate state, or structured failure. It does not publish a Group.
# Effects: Constructs the base or resumes VVMF_STATE, runs one algorithm, updates the
# candidate request/generation. Raw code is read only for the explicit ConstructGAP operation.
# Failures: Unsupported operation, absent checkpoint, malformed request, invalid construction,
# method error, nonfinite group or state conflict. Native GAP errors terminate the worker.
# Example: Construct establishes generation zero; Characters resumes it at generation one.
# Remarks: Later mathematical operations extend this dispatcher through their owning modules.
# There is no SaveWorkspace invocation here or anywhere inside a GAP function.
# See also: VVMF_SetIdentity; VVMF_PrepareCheckpoint; GAPJobs.wl.
VVMF_Run := function(request)
    local state, result, code, names, epoch;
    if not VVMF_DRIVER_DEPENDENCIES.json or not VVMF_DRIVER_DEPENDENCIES.io then
        return VVMF_Failure("DependencyUnavailable","Worker transport requires json and io.");
    fi;
    if not IsRecord(request) or not IsBound(request.operation) then
        return VVMF_Failure("InvalidRequest","The operation is missing.");
    fi;
    if request.operation = "Import" then
        if not IsRecord(VVMF_STATE) or not IsBound(request.importedGroup) or
            not IsBound(request.validationSource) or not IsRecord(request.validationSource) or
            request.validationSource <> rec(stateID := VVMF_STATE.stateID,
                generatorIdentity := VVMF_STATE.generatorIdentity,
                stateGeneration := String(VVMF_STATE.generation)) then
            return VVMF_Failure("StateConflict","Import requires the independently accepted validation source.");
        fi;
        state := ValueGlobal("VVMF_ValidateImported")(VVMF_STATE,request.importedGroup);
        if VVMF_IsFailure(state) then return state; fi;
        if IsBound(request.knownSubgroupClasses) then
            result := ValueGlobal("VVMF_CheckImportedSubgroupClasses")(state,request.knownSubgroupClasses);
            if VVMF_IsFailure(result) then return result; fi;
        fi;
    elif request.operation = "Reconstruct" then
        if not IsBound(request.acceptedGroup) or not IsRecord(request.acceptedGroup) or
            not IsBound(request.acceptedGroup.construction) then
            return VVMF_Failure("InvalidRequest","Reconstruction requires independently accepted typed data.");
        fi;
        state := VVMF_Construct(request.acceptedGroup.construction);
        if VVMF_IsFailure(state) then return state; fi;
        result := VVMF_RebindGroup(state,request.acceptedGroup);
        if VVMF_IsFailure(result) then return result; fi;
    elif request.operation = "Construct" then
        if not IsBound(request.construction) then
            return VVMF_Failure("InvalidRequest","Typed construction data are missing.");
        fi;
        state := VVMF_Construct(request.construction);
    elif request.operation = "ConstructGAP" then
        if not IsBound(request.construction) or not IsRecord(request.construction) or
            not IsBound(request.construction.type) or request.construction.type <> "gapCode" or
            not IsBound(request.construction.code) or not IsString(request.construction.code) or
            not IsBound(request.construction.names) or not VVMF_NamesQ(request.construction.names) or
            not IsBound(request.codePath) or not IsString(request.codePath) then
            return VVMF_Failure("InvalidRequest","An explicit code recipe and owned source path are required.");
        fi;
        code := StringFile(request.codePath);
        if code = fail or code <> request.construction.code then
            return VVMF_Failure("InvalidRequest","The owned code file does not match the explicit recipe.");
        fi;
        if IsBoundGlobal("VVMFInputGroup") then UnbindGlobal("VVMFInputGroup"); fi;
        if IsBoundGlobal("VVMFInputGenerators") then UnbindGlobal("VVMFInputGenerators"); fi;
        Read(request.codePath);
        if not IsBound(VVMFInputGroup) or not IsBound(VVMFInputGenerators) then
            return VVMF_Failure("InvalidConstruction","Code must set VVMFInputGroup and VVMFInputGenerators.");
        fi;
        state := VVMF_ConstructRaw(ValueGlobal("VVMFInputGroup"),ValueGlobal("VVMFInputGenerators"),
            request.construction.names,request.construction);
    elif request.operation in VVMF_ENRICHMENT_OPERATIONS then
        if IsRecord(VVMF_STATE) then
            state := ShallowCopy(ValueGlobal("VVMF_STATE"));
        elif IsBound(request.acceptedGroup) and IsRecord(request.acceptedGroup) and
            IsBound(request.acceptedGroup.construction) then
            state := VVMF_Construct(request.acceptedGroup.construction);
            if VVMF_IsFailure(state) then return state; fi;
            result := VVMF_RebindGroup(state,request.acceptedGroup);
            if VVMF_IsFailure(result) then return result; fi;
        else
            return VVMF_Failure("MissingCheckpoint","Enrichment requires a checkpoint or certified typed data.");
        fi;
    elif request.operation = "Characters" then
        if not IsRecord(VVMF_STATE) then
            return VVMF_Failure("MissingCheckpoint","Character work requires a constructed base checkpoint.");
        fi;
        if not IsBound(request.method) or not IsBound(request.model) then
            return VVMF_Failure("InvalidRequest","An explicit character method and model are required.");
        fi;
        state := ShallowCopy(ValueGlobal("VVMF_STATE"));
    else
        return VVMF_Failure("UnsupportedOperation","No adapter is installed for this operation.");
    fi;
    if VVMF_IsFailure(state) then return state; fi;
    if request.operation in ["Reconstruct","Import"] then
        # Reconstruction reproduces accepted mathematics at its existing generation.
        # Subsequent isolated algorithms each advance this shared base by one.
        if not IsBound(request.stateID) or request.stateID <> state.stateID or
            not IsBound(request.generatorIdentity) or request.generatorIdentity <> state.generatorIdentity or
            not IsBound(request.stateGeneration) or request.stateGeneration <> String(state.generation) or
            not IsBound(request.requestID) or not IsString(request.requestID) or Length(request.requestID) = 0 then
            return VVMF_Failure("StateConflict","Reconstruction changed an accepted state identity or generation.");
        fi;
        state.requestID := request.requestID;
        state.operation := request.operation;
    else
        result := VVMF_SetIdentity(state,request);
        if VVMF_IsFailure(result) then return result; fi;
    fi;
    if request.operation in VVMF_ENRICHMENT_OPERATIONS then
        if not IsBound(request.model) then
            return VVMF_Failure("InvalidRequest","A computational model is required.");
        fi;
        result := VVMF_Model(state,request.model);
        if VVMF_IsFailure(result) then return result; fi;
        state.dataModel := result;
    fi;
    # a weak build's character table (methodOptionsPlan.md 2C.6): set before any character computation of this request
    if IsBound(request.characterCheck) then
        if not request.characterCheck in ["Full", "TransportOnly"] then return VVMF_Failure("InvalidRequest","Unknown character check mode."); fi;
        if request.characterCheck = "TransportOnly" and not IsBound(state.characterData) then state.characterCheck := "TransportOnly"; fi;
    fi;
    if IsBound(request.stCheck) then
        if not request.stCheck in ["Full", "Skip"] then return VVMF_Failure("InvalidRequest","Unknown S,T check mode."); fi;
        # "Skip" only for a new assignment; "Full" re-proves (and raises) a skipped one
        if request.stCheck = "Full" or IsBound(request.modularAssignment) then state.stCheck := request.stCheck; fi;
        if request.stCheck = "Full" and IsBound(state.modularAssignment) and not IsBound(request.modularAssignment) then
            result := VVMF_CheckST(state,state.modularAssignment.sWord,state.modularAssignment.tWord);
            if VVMF_IsFailure(result) then state.stCheck := "Skip"; return result; fi;
        fi;
    fi;
    if IsBound(request.modularAssignment) then
        result := VVMF_AssignST(state,request.modularAssignment);
        if VVMF_IsFailure(result) then return result; fi;
    fi;
    state.lastRequest := ShallowCopy(request);
    if IsBound(request.wordRecoveryStrategy) then
        if not request.wordRecoveryStrategy in ["Native","FP","Cayley"] then
            return VVMF_Failure("InvalidWordStrategy","Unknown word recovery strategy.");
        fi;
        state.wordRecoveryStrategy := request.wordRecoveryStrategy;
    fi;
    if IsBound(request.wordRecoveryBudget) then
        state.wordRecoveryBudget := request.wordRecoveryBudget;
    fi;
    epoch := VVMF_ApplyEvictionEpoch(state,request);
    if VVMF_IsFailure(epoch) then return epoch; fi;
    if request.operation = "Characters" then
        if request.method = "Transfer" then
            if not IsBound(request.transferredCharacters) then
                return VVMF_Failure("InvalidRequest","A certified character transfer payload is required.");
            fi;
            result := VVMF_TransferCharacters(state,request.transferredCharacters);
        else
            result := VVMF_Characters(state,request.method,request);
        fi;
        if VVMF_IsFailure(result) then return result; fi;
    fi;
    if request.operation = "Representations" then
        if IsBound(request.method) and request.method = "Transfer" then
            if not IsBound(request.transferredRepresentations) then
                return VVMF_Failure("InvalidRequest","A certified representation transfer payload is required.");
            fi;
            # The owning representation module loads before the driver in every worker.
            # replaceActive names the irreps whose incoming active variant replaces this state's (an explicit
            # re-derivation of a sibling partition); absent, the admission ranks decide.
            if IsBound(request.replaceActive) then
                result := ValueGlobal("VVMF_TransferRepresentations")(state,request.transferredRepresentations,
                    request.replaceActive);
            else
                result := ValueGlobal("VVMF_TransferRepresentations")(state,request.transferredRepresentations);
            fi;
        else
            result := ValueGlobal("VVMF_Representations")(state,request);
        fi;
        if VVMF_IsFailure(result) then return result; fi;
    elif request.operation = "GeneratorPresentation" then
        result := VVMF_GeneratorPresentation(state);
        if VVMF_IsFailure(result) then return result; fi;
    elif request.operation = "Decompose" then
        # A query: the verified decomposition is exported in the diagnostics; the mathematical state is unchanged.
        result := ValueGlobal("VVMF_Decompose")(state,request);
        if VVMF_IsFailure(result) then return result; fi;
        state.decompositionResult := result;
    elif request.operation = "CheckGeneratorMap" then
        result := VVMF_MapRequest(state,request);
        if VVMF_IsFailure(result) then return result; fi;
    elif request.operation = "GroupElementWords" then
        result := VVMF_Elements(state);
        if VVMF_IsFailure(result) then return result; fi;
    elif request.operation = "GroupSubgroups" then
        if not IsBound(request.subgroupQuery) then return VVMF_Failure("InvalidRequest","A subgroup query is required."); fi;
        result := VVMF_Subgroups(state,request.subgroupQuery,request.method,request.model);
        if VVMF_IsFailure(result) then return result; fi;
    elif request.operation = "GroupWordOrder" then
        if not IsBound(request.word) then return VVMF_Failure("InvalidRequest","An order word is required."); fi;
        result := VVMF_WordOrder(state,request.word);
        if VVMF_IsFailure(result) then return result; fi;
    elif request.operation = "CGNative" then
        # A query: the verified chain intertwiners are exported in the diagnostics; the state is unchanged.
        result := ValueGlobal("VVMF_CGChain")(state,request);
        if VVMF_IsFailure(result) then return result; fi;
    elif request.operation = "CG" then
        # The CG mirror module (GAP/CG.g) loads before the driver in every worker.
        result := ValueGlobal("VVMF_IncorporateCG")(state,request);
        if VVMF_IsFailure(result) then return result; fi;
    elif request.operation = "AssignModularGenerators" and not IsBound(request.modularAssignment) then
        return VVMF_Failure("InvalidRequest","Explicit modular generators are required.");
    elif request.operation = "ValidateGroup" then
        # methodOptionsPlan.md 2C.6: prove a weakly built table (and a skipped S,T check, through stCheck "Full" above);
        # level "Export" only re-exports (Wolfram's numerical reading of the new generation); at every level the recorded
        # generator presentation is proved first (an unverified import's certificate, final review H-1)
        result := ValueGlobal("VVMF_ProveGeneratorPresentation")(state);
        if VVMF_IsFailure(result) then return result; fi;
        if not IsBound(request.level) or request.level <> "Export" then
            result := VVMF_Characters(state,"GAP",rec(model := "Original",characterCheck := "Full"));
            if VVMF_IsFailure(result) then return result; fi;
        fi;
    fi;
    return state;
end;

# Summary: Root a candidate and emit save readiness only after atomic JSON output succeeds.
# Parameters/defaults: state is VVMF_Run output; resultPath is a new caller-owned JSON path.
# Returns: checkpointReady record, or a reported structured failure.
# Effects: On success stores VVMF_STATE, VVMF_SAVED_RESULT and VVMF_READY_RECORD globally
# for the subsequent main-input SaveWorkspace. The paired workspace path is resultPath+".wsp".
# Failures: Clears stale readiness first. Export/write failures emit no success marker and
# do not replace the preceding accepted global state.
# Example: VVMF_PrepareCheckpoint(candidate,path); then main input calls
# SaveWorkspace(VVMF_READY_RECORD.workspacePath) only after receiving matching readiness.
# See also: VVMF_ReportCheckpoint; VVMF_ReportRestored.
VVMF_PrepareCheckpoint := function(state,resultPath)
    local request, result, written, ready;
    VVMF_READY_RECORD := fail;
    if VVMF_IsFailure(state) then return VVMF_ProtocolFailure(state,rec()); fi;
    if not IsRecord(state) or not IsBound(state.lastRequest) then
        return VVMF_ProtocolFailure(VVMF_Failure("InvalidState","Candidate request metadata are missing."),rec());
    fi;
    request := state.lastRequest;
    result := VVMF_Export(state,request);
    if VVMF_IsFailure(result) then return VVMF_ProtocolFailure(result,request); fi;
    written := VVMF_WriteJSON(resultPath,result);
    if VVMF_IsFailure(written) then return VVMF_ProtocolFailure(written,request); fi;
    ready := rec(type := "checkpointReady",requestID := state.requestID,
        stateID := state.stateID,generatorIdentity := state.generatorIdentity,
        stateGeneration := String(state.generation),status := result.status,resultPath := resultPath,
        workspacePath := Concatenation(resultPath,".wsp"));
    VVMF_STATE := state;
    VVMF_SAVED_RESULT := result;
    VVMF_READY_RECORD := ready;
    VVMF_Emit(ready);
    return ready;
end;

# Summary: Report the outcome of a literal main-input SaveWorkspace call.
# Parameters/defaults: saveStatus is its Boolean return; requestID identifies pending readiness.
# Returns: checkpointSaved record or reported failure.
# Effects: Emits one packet after checking the pending request and nonempty artifacts.
# Failures: No readiness, wrong request, false save return, absent/empty result or workspace.
# Example: VVMF_ReportCheckpoint(VVMF_SAVE_OK,"request-1") after main input saves.
# Remarks: The coordinator additionally checks digests and real restoration before acceptance.
# The helper cannot prove that an arbitrary supplied true came from SaveWorkspace.
# See also: VVMF_PrepareCheckpoint; VVMF_ReportRestored.
VVMF_ReportCheckpoint := function(saveStatus,requestID)
    local ready, resultInfo, workspaceInfo, message;
    if not IsRecord(VVMF_READY_RECORD) then
        return VVMF_ProtocolFailure(VVMF_Failure("SaveFailed","There is no pending checkpoint."),rec());
    fi;
    ready := ValueGlobal("VVMF_READY_RECORD");
    if saveStatus <> true or requestID <> ready.requestID then
        return VVMF_ProtocolFailure(VVMF_Failure("SaveFailed","Workspace save failed or request mismatched."),ready);
    fi;
    resultInfo := ValueGlobal("IO_lstat")(ready.resultPath);
    workspaceInfo := ValueGlobal("IO_lstat")(ready.workspacePath);
    if resultInfo = fail or workspaceInfo = fail or resultInfo.size <= 0 or workspaceInfo.size <= 0 or
        QuoInt(resultInfo.mode,4096) mod 16 <> 8 or QuoInt(workspaceInfo.mode,4096) mod 16 <> 8 then
        return VVMF_ProtocolFailure(VVMF_Failure("SaveFailed","The checkpoint artifacts are not nonempty regular files."),ready);
    fi;
    message := ShallowCopy(ready);
    message.type := "checkpointSaved";
    VVMF_Emit(message);
    return message;
end;

# Summary: Recheck restored native state against its saved mathematical envelope.
# Parameters/defaults: restoreRequestID is a fresh coordinator nonce for this restore; no options.
# Returns: checkpointRestored packet or a reported failure.
# Effects: Revalidates native characters/class words; emits the restored state identity/generation.
# Failures: Missing roots, mismatched saved identities, changed native data or invalid nonce.
# Example: a fresh worker loaded with -L emits matching identity and generation after this check.
# Remarks: Import never invokes this helper on an untrusted workspace path. Compatibility and
# checksum checks precede launching the worker; time/memory limits include this native recheck.
# See also: VVMF_Export; VVMF_ReportCheckpoint.
VVMF_ReportRestored := function(restoreRequestID)
    local state, result, message, ready;
    if not IsString(restoreRequestID) or Length(restoreRequestID) = 0 or
        not IsRecord(VVMF_STATE) or not IsRecord(VVMF_SAVED_RESULT) or not IsRecord(VVMF_READY_RECORD) then
        return VVMF_ProtocolFailure(VVMF_Failure("InvalidCheckpoint","Required checkpoint roots are absent."),rec());
    fi;
    state := ValueGlobal("VVMF_STATE");
    ready := ValueGlobal("VVMF_READY_RECORD");
    result := VVMF_Export(state,state.lastRequest);
    if VVMF_IsFailure(result) or result <> ValueGlobal("VVMF_SAVED_RESULT") or
        result.requestID <> ready.requestID or result.stateGeneration <> ready.stateGeneration then
        return VVMF_ProtocolFailure(VVMF_Failure("InvalidCheckpoint","Restored native data differ from their saved envelope."),ready);
    fi;
    message := rec(type := "checkpointRestored",requestID := restoreRequestID,
        checkpointRequestID := result.requestID,stateID := result.stateID,
        generatorIdentity := result.generatorIdentity,stateGeneration := result.stateGeneration,
        status := result.status);
    VVMF_Emit(message);
    return message;
end;

# Summary: Export revalidated restored state for independent comparison with the saved JSON.
# Parameters/defaults: restoreRequestID is the coordinator's fresh nonce; resultPath is a new
# owned verification file. No options.
# Returns: checkpointVerified packet, or a reported native/output failure.
# Effects: First performs VVMF_ReportRestored, then writes its native envelope atomically
# to a separate file and emits checkpointVerified. Does not overwrite the saved result.
# Failures: Invalid restored state, existing/unwritable verification path or JSON failure.
# Example: the coordinator compares this verified file to the candidate result before
# publishing its manifest or issuing an in-memory validation receipt.
# Remarks: A matching workspace identity alone cannot detect a tampered, still-orthogonal
# JSON character table. The separately exported native envelope closes that correspondence.
# See also: VVMF_ReportRestored; VVMF_WriteJSON; ResultValidation.wl.
VVMF_VerifyCheckpoint := function(restoreRequestID,resultPath)
    local restored, written, verified;
    restored := VVMF_ReportRestored(restoreRequestID);
    if VVMF_IsFailure(restored) then return restored; fi;
    written := VVMF_WriteJSON(resultPath,ValueGlobal("VVMF_SAVED_RESULT"));
    if VVMF_IsFailure(written) then return VVMF_ProtocolFailure(written,restored); fi;
    verified := ShallowCopy(restored);
    verified.type := "checkpointVerified";
    verified.verifiedResultPath := resultPath;
    VVMF_Emit(verified);
    return verified;
end;
