# Title: Structured backend failures
# Summary: Ordinary validation failures are data, distinct from GAP break-loop errors.
# Dependencies: None. The job driver also handles process-level errors and timeouts.

# Summary: Construct an ordinary backend failure record.
# Parameters: tag, message are strings established by the caller.
# Returns: rec(ok := false, tag := tag, message := message).
# Effects: Pure; prints nothing and does not enter a break loop.
# Failures: Caller supplies the documented strings.
# Example: VVMF_Failure("InvalidInput", "Expected a word.").ok = false.
# See also: VVMF_IsFailure; the job protocol in VVMFArch/step1Plan.md.
VVMF_Failure := function(tag, message)
    return rec(ok := false, tag := tag, message := message);
end;

# Summary: Recognize a structured backend failure.
# Parameters: value is any GAP object.
# Returns: true for a record with ok=false; false otherwise.
# Effects: Pure; no failure for other objects.
# Example: VVMF_IsFailure(fail) = false; VVMF_IsFailure(VVMF_Failure("x","y")) = true.
# See also: VVMF_Failure.
VVMF_IsFailure := function(value)
    return IsRecord(value) and IsBound(value.ok) and value.ok = false;
end;
