# Title: Strict JSON output for typed interchange
# Summary: Encode JSON data, including null, without changing methods in the json package.
# Dependencies: Diagnostics.g; json package for scalar escaping and input parsing.
# See also: Schemas/GroupResult.md; ResultExport.g.

# Summary: Encode an inert JSON value with explicit support for GAP fail as JSON null.
# Parameters/defaults: value is fail, a boolean, integer, string, list or string-keyed record;
# no options. Strings use GAP's string representation, including the empty string.
# Returns: JSON text, or a structured InvalidJSON/DependencyUnavailable failure.
# Effects: Loads json if necessary; does not evaluate source or mutate value.
# Failures: Other native GAP objects and nested unsupported values are rejected.
# Example: VVMF_JSONString(rec(items := [], missing := fail)) decodes to that record.
# Remarks: json 2.2.3 parses null as fail but its boolean encoder rejects fail.
# This package-local traversal handles null and delegates scalar escaping to json.
# See also: GapToJsonString; JsonStringToGap; VVMF_Export.
VVMF_JSONString := function(value)
    local parts, keys, encode;
    if value = fail then return "null"; fi;
    if not IsBound(GapToJsonString) and LoadPackage("json") = fail then
        return VVMF_Failure("DependencyUnavailable", "JSON interchange requires the json package.");
    fi;
    encode := ValueGlobal("GapToJsonString");
    if IsInt(value) or value = true or value = false or
        (IsString(value) and (Length(value) > 0 or IsStringRep(value))) then
        return encode(value);
    elif IsRecord(value) then
        keys := SortedList(RecNames(value));
        parts := List(keys, key -> VVMF_JSONString(value.(key)));
        if ForAny(parts,VVMF_IsFailure) then
            return First(parts,VVMF_IsFailure);
        fi;
        parts := List([1..Length(keys)], i ->
            Concatenation(encode(keys[i]),":",parts[i]));
        return Concatenation("{",JoinStringsWithSeparator(parts,","),"}");
    elif IsList(value) then
        parts := List(value,VVMF_JSONString);
        if ForAny(parts,VVMF_IsFailure) then return First(parts,VVMF_IsFailure); fi;
        return Concatenation("[",JoinStringsWithSeparator(parts,","),"]");
    fi;
    return VVMF_Failure("InvalidJSON", "Unsupported native object in JSON data.");
end;
