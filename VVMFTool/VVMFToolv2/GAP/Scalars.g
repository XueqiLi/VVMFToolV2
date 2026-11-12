# Title: Exact scalar JSON codecs
# Summary: Convert exact integers, rationals and cyclotomics without source evaluation.
# Dependencies: Diagnostics.g.
# See also: Kernel/ScalarCodec.wl; GAP reference chapter 18.

# Summary: Decode a canonical signed decimal integer.
# Parameters: text is any object; valid input is a canonical decimal string.
# Returns: Integer or structured failure.
# Effects: Pure; Int parses an integer and does not evaluate GAP source.
# Failures: Leading signs/zeroes, nonintegers and nonstrings are rejected.
# Example: VVMF_DecodeInteger("-123") = -123.
# See also: VVMF_DecodeRational.
VVMF_DecodeInteger := function(text)
    local value;
    if not IsString(text) or Length(text) = 0 then
        return VVMF_Failure("InvalidInteger", "Expected a canonical decimal string.");
    fi;
    value := Int(text);
    if value = fail or String(value) <> text then
        return VVMF_Failure("InvalidInteger", "Noncanonical decimal integer.");
    fi;
    return value;
end;

# Summary: Decode an exact rational pair of signed numerator and positive denominator.
# Parameters: pair is a two-element list of canonical decimal strings.
# Returns: Rational or structured failure.
# Effects: Pure; rational reduction is exact.
# Failures: Malformed pairs and nonpositive denominators are rejected.
# Example: VVMF_DecodeRational(["-6","4"]) = -3/2.
# See also: VVMF_DecodeScalar; VVMF_DecodeInteger.
VVMF_DecodeRational := function(pair)
    local numerator, denominator;
    if not IsList(pair) or Length(pair) <> 2 then
        return VVMF_Failure("InvalidRational", "Expected numerator/denominator strings.");
    fi;
    numerator := VVMF_DecodeInteger(pair[1]);
    denominator := VVMF_DecodeInteger(pair[2]);
    if VVMF_IsFailure(numerator) or VVMF_IsFailure(denominator) or denominator <= 0 then
        return VVMF_Failure("InvalidRational", "Invalid rational numerator or denominator.");
    fi;
    return numerator / denominator;
end;

# Summary: Decode a structured integer, rational or cyclotomic scalar.
# Parameters: data is a scalar-schema record.
# Returns: Exact GAP cyclotomic, or structured failure.
# Effects: Pure. The positive root is E(rootOrder); coefficient k belongs to E(n)^(k-1).
# Failures: Extra/missing fields, unknown type, invalid root order, length or coefficients.
# Example: VVMF_DecodeScalar(rec(type:="integer",value:="-4")) = -4.
# See also: VVMF_EncodeScalar; Kernel/ScalarCodec.wl.
VVMF_DecodeScalar := function(data)
    local coefficients, i, value;
    if not IsRecord(data) or not IsBound(data.type) then
        return VVMF_Failure("InvalidScalar", "Expected a typed scalar record.");
    fi;
    if data.type in ["integer", "rational"] then
        if Set(RecNames(data)) <> ["type", "value"] then
            return VVMF_Failure("InvalidScalar", "Invalid scalar fields.");
        fi;
        if data.type = "integer" then return VVMF_DecodeInteger(data.value); fi;
        return VVMF_DecodeRational(data.value);
    fi;
    if data.type <> "cyclotomic" or
        Set(RecNames(data)) <> ["coefficients", "rootOrder", "type"] or
        not IsInt(data.rootOrder) or data.rootOrder < 1 or
        not IsList(data.coefficients) or Length(data.coefficients) <> data.rootOrder then
        return VVMF_Failure("InvalidScalar", "Invalid cyclotomic schema.");
    fi;
    coefficients := List(data.coefficients, VVMF_DecodeRational);
    if ForAny(coefficients, VVMF_IsFailure) then
        return VVMF_Failure("InvalidScalar", "Invalid cyclotomic coefficients.");
    fi;
    value := 0;
    for i in [1..data.rootOrder] do
        value := value + coefficients[i] * E(data.rootOrder)^(i-1);
    od;
    return value;
end;

# Summary: Encode an exact scalar as data using its actual cyclotomic conductor.
# Parameters: value is an integer, rational or GAP cyclotomic.
# Returns: Scalar-schema record, or structured failure.
# Effects: Pure; no printed algebraic expression is parsed.
# Failures: Floats, finite-field elements and other noncyclotomics are rejected.
# Example: VVMF_EncodeScalar(-1/2) = rec(type:="rational",value:=["-1","2"]).
# Remarks: CoeffsCyc has exactly conductor entries in ascending powers of E(conductor).
# See also: VVMF_DecodeScalar; https://gap-system.github.io/gap/doc/ref/chap18.html
VVMF_EncodeScalar := function(value)
    local conductor, coefficients;
    if IsInt(value) then return rec(type := "integer", value := String(value)); fi;
    if IsRat(value) then
        return rec(type := "rational",
            value := [String(NumeratorRat(value)), String(DenominatorRat(value))]);
    fi;
    if not IsCyc(value) then
        return VVMF_Failure("UnsupportedScalar", "Expected an exact complex cyclotomic.");
    fi;
    conductor := Conductor(value);
    coefficients := CoeffsCyc(value, conductor);
    return rec(type := "cyclotomic", rootOrder := conductor,
        coefficients := List(coefficients,
            x -> [String(NumeratorRat(x)), String(DenominatorRat(x))]));
end;
