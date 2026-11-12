(*
    :Title: Dimensions, weight profiles and existence of vector-valued modular forms
    :Context: VVMFTool`Private`
    :Summary: Certified exact T exponents and central sign of a representation, the low-rank weight profiles (ranks 1-5,
        with the cyclic/noncyclic and five rank-5 types), dimensions from the Hilbert series of a profile and from the
        k >= 2 trace formula with a cross-check, explicit unknowns, and a derived cache keyed by the actual modular
        representation.
    :Responsibilities: modularSpectralData, profileCandidates, dimensionFromProfile, dimensionFromTraces,
        resolveModularDimension, dimensionCacheKey, cleanDimensionEntries; ModularDimension, ModularDimensionData,
        ModularDimensionTable, ModularWeightProfile, MinimumModularWeight, ModularFormExistQ, CleanModularDimensionCache.
    :Dependencies: ModularFormObjects.wl (formContextData); RepresentationBasis.wl (RepresentationTSpectrum).
    :See Also: VVMFArch/step7Plan.md (dimensions and profiles); local MLDE.tex (profile table, Hilbert series, trace
        formula with its k >= 2 qualification).
*)

If[!AssociationQ[$ModularDimensionCache], $ModularDimensionCache = <||>];

(*
    Summary: Exact spectral and trace data of a representation under the assigned S, T.
    Parameters: c — Group or RepresentationContext; irrep — irrep ID or Rep.
    Options/defaults: None.
    Returns: <|"Dimension", "Exponents" (ascending, with multiplicity, each in [0, 1)), "TraceL" (their sum, exact),
        "CentralSign" (+1 or -1 with rho(S^2) = sign I, or Missing["NotCentral"] for a reducible representation or a
        cover-group irrep), "CentralPhase" (the exact lambda with rho(S^2) = lambda I, or Missing["NotCentral"]),
        "Traces" -> <|"S3", "S3T", "STST"|>, "Trivial", "IrrepID", "RepKey", "GroupIdentity", "AssignmentID"|>, or Failure.
    Effects: Freezes a group context.
    Failures: Context failures; MissingExactSpectrum (numerical matrices: exponents are never defined by rounding).
    Example: modularSpectralData[c, triplet]["Exponents"] is {0, 1/3, 2/3} for the T' triplet.
    Remarks: The exponents come from RepresentationTSpectrum (exact eigenspaces of T in a number field); Tr L is basis
        invariant; no entrywise matrix Log or Arg is used.
    See also: profileCandidates; dimensionFromTraces.
*)
modularSpectralData[c_, irrep_] := Module[{ctx = formContextData[c, irrep], spectrum, s, t, d, s2, sign, phase, trace},
    If[FailureQ[ctx], Return[ctx]];
    If[inexactDataQ[{ctx["S"], ctx["T"]}], Return[makeFailure["MissingExactSpectrum", "Exact T exponents need exact matrices; numerical matrices never define exponents by rounding.",
        <|"IrrepID" -> ctx["IrrepID"]|>]]];
    spectrum = RepresentationTSpectrum[ctx["Context"], ctx["Rep"]]; If[FailureQ[spectrum], Return[spectrum]];
    {s, t, d} = {ctx["S"], ctx["T"], ctx["Dimension"]};
    s2 = s . s;
    sign = Which[AllTrue[Flatten[s2 - IdentityMatrix[d]], TrueQ[RootReduce[#] === 0] &], 1,
        AllTrue[Flatten[s2 + IdentityMatrix[d]], TrueQ[RootReduce[#] === 0] &], -1, True, Missing["NotCentral"]];
    (* the exact central phase lambda with rho(S^2) = lambda I (+-1 for SL(2,Z) quotients; any root of unity for a cover) *)
    phase = If[IntegerQ[sign], sign, With[{l = RootReduce[s2[[1, 1]]]},
        If[AllTrue[Flatten[s2 - l IdentityMatrix[d]], TrueQ[RootReduce[#] === 0] &], l, Missing["NotCentral"]]]];
    trace[m_] := RootReduce[Tr[m]];
    <|"Dimension" -> d, "Exponents" -> Flatten[MapThread[ConstantArray, {spectrum["Phases"], spectrum["Multiplicities"]}]],
        "TraceL" -> Total[spectrum["Phases"] spectrum["Multiplicities"]], "CentralSign" -> sign, "CentralPhase" -> phase,
        "Traces" -> <|"S3" -> trace[s . s . s], "S3T" -> trace[s . s . s . t], "STST" -> trace[s . t . s . t]|>,
        "Trivial" -> (d === 1 && ctx["IrrepID"] === ctx["Snapshot"]["CharacterData"]["TrivialIrrepID"]),
        "IrrepID" -> ctx["IrrepID"], "RepKey" -> Hash[{s, t}, "SHA256", "HexString"], "GroupIdentity" -> ctx["Snapshot"]["GroupIdentity"],
        "AssignmentID" -> ctx["Assignment"]["Identity"]|>
];

(*
    Summary: The weight-profile candidates of a representation and the justified one.
    Parameters: data — modularSpectralData.
    Options/defaults: None.
    Returns: <|"Candidates" -> {<|"Type", "Offsets", "MinimumWeight"|>...}, "Profile" -> list of weights, or
        Missing["UnknownProfile", reason]|>, or Failure.
    Effects: Pure.
    Failures: InconsistentProfile (no or several candidates satisfy integrality and parity; a low-rank minimum weight
        that is not an integer of the allowed parity).
    Example: the T' triplet {0, 1/3, 2/3} has Tr L = 1, k0 = 4 Tr L - 2 = 2 and profile {2, 4, 6}.
    Remarks: Ranks 1-3: k0 = 12 Tr L, 6 Tr L - 1, 4 Tr L - 2 with offsets {0}, {0, 2}, {0, 2, 4}. Rank 4: cyclic
        k0 = 3 Tr L - 3, offsets {0, 2, 4, 6}; noncyclic k0 = 3 Tr L - 2, offsets {0, 2, 2, 4}. Rank 5: offsets {0,2,4,6,8},
        {0,2,4,4,6}, {0,2,2,4,4}, {0,0,2,2,4}, {0,2,2,4,6} with k0 = (12 Tr L - offset sum)/5. A candidate needs an integer
        k0 with (-1)^k0 equal to the central sign; exactly one must remain. Ranks above 5 have no profile here.
    See also: dimensionFromProfile.
*)
profileCandidates[data_Association] := Module[{d = data["Dimension"], l = data["TraceL"], sign = data["CentralSign"], candidates, valid},
    If[MissingQ[sign], Return[<|"Candidates" -> {}, "Profile" -> If[MissingQ[data["CentralPhase"]],
        Missing["UnknownProfile", "The representation has no central S^2 (reducible)."],
        Missing["UnknownProfile", "rho(S^2) is not +-1 (an irrep of a cover of SL(2,Z), rational weights): weight profiles are implemented for SL(2,Z) quotients only."]]|>]];
    candidates = Switch[d,
        1, {<|"Type" -> "Rank1", "Offsets" -> {0}, "MinimumWeight" -> 12 l|>},
        2, {<|"Type" -> "Rank2", "Offsets" -> {0, 2}, "MinimumWeight" -> 6 l - 1|>},
        3, {<|"Type" -> "Rank3", "Offsets" -> {0, 2, 4}, "MinimumWeight" -> 4 l - 2|>},
        4, {<|"Type" -> "Cyclic4D", "Offsets" -> {0, 2, 4, 6}, "MinimumWeight" -> 3 l - 3|>, <|"Type" -> "NonCyclic4D", "Offsets" -> {0, 2, 2, 4}, "MinimumWeight" -> 3 l - 2|>},
        5, Map[<|"Type" -> "Rank5" <> StringJoin[ToString /@ #], "Offsets" -> #, "MinimumWeight" -> (12 l - Total[#])/5|> &,
            {{0, 2, 4, 6, 8}, {0, 2, 4, 4, 6}, {0, 2, 2, 4, 4}, {0, 0, 2, 2, 4}, {0, 2, 2, 4, 6}}],
        _, Return[<|"Candidates" -> {}, "Profile" -> Missing["UnknownProfile", "Weight profiles are implemented for ranks 1 to 5."]|>]];
    valid = Select[candidates, IntegerQ[#["MinimumWeight"]] && (-1)^#["MinimumWeight"] === sign &];
    If[Length[valid] =!= 1, Return[makeFailure["InconsistentProfile", "The exponents and central sign do not select exactly one weight profile.",
        <|"Candidates" -> candidates, "Valid" -> valid, "TraceL" -> l, "CentralSign" -> sign|>]]];
    <|"Candidates" -> candidates, "Type" -> First[valid]["Type"], "Profile" -> First[valid]["MinimumWeight"] + First[valid]["Offsets"]|>
];

(*
    Summary: Dimensions from a weight profile and from the trace formula.
    Parameters: profile — list of integer weights; data — modularSpectralData; k — integer weight.
    Options/defaults: None.
    Returns: dimensionFromProfile: the coefficient of t^k in Sum t^w/((1 - t^4)(1 - t^6)) (a nonnegative integer).
        dimensionFromTraces: the exact value of (5 + k) d/12 + i^k Tr S^3/4 + (-w^2)^k Tr S^3 T/(3 (1 - w))
        + w^k Tr (ST)^2/(3 (1 - w^2)) - Tr L with w = Exp[2 Pi I/3], or Failure.
    Effects: Pure.
    Failures: DimensionFormulaFailure (the trace formula is not a nonnegative integer: a diagnostic, never silently 0);
        InvalidWeight (k < 2 for the trace formula, whose stated domain is k >= 2).
    Example: dimensionFromProfile[{2, 4, 6}, 6] is 2 (t^6 from w = 2 via 4 a + 6 b = 4 and from w = 6).
    See also: resolveModularDimension.
*)
dimensionFromProfile[profile_List, k_Integer] := Total[Map[Function[w, If[k - w < 0, 0,
    Count[Flatten[Table[4 a + 6 b, {a, 0, Floor[(k - w)/4]}, {b, 0, Floor[(k - w)/6]}]], k - w]]], profile]];
dimensionFromTraces[data_Association, k_Integer] := Module[{value},
    If[k < 2, Return[makeFailure["InvalidWeight", "The trace formula is stated for weights k >= 2.", <|"Weight" -> k|>]]];
    value = traceFormulaValue[data, k];
    If[IntegerQ[value] && value >= 0, value, makeFailure["DimensionFormulaFailure", "The trace formula did not give a nonnegative integer in its stated domain.",
        <|"Weight" -> k, "Value" -> value|>]]
];

(*
    Summary: The raw value of the trace formula at any integer weight (no domain or integrality check).
    Parameters: data — modularSpectralData; k — integer weight.
    Options/defaults: None.
    Returns: The exact value (5 + k) d/12 + i^k Tr S^3/4 + (-w^2)^k Tr S^3 T/(3 (1 - w)) + w^k Tr (ST)^2/(3 (1 - w^2)) - Tr L.
    Effects: Pure.
    Failures: None.
    Example: traceFormulaValue[data, 1] for the T' doublet with exponents {0, 1/3} is 1.
    Remarks: At k = 1 the formula is shown in the dimension table with a note that it may be incorrect (user decision,
        uxUpdatePlan.md 2.5); dimensionFromTraces applies it in its stated domain k >= 2.
    See also: dimensionFromTraces; resolveModularDimension.
*)
traceFormulaValue[data_Association, k_Integer] := With[{w = Exp[2 Pi I/3]}, RootReduce[(5 + k) data["Dimension"]/12 + I^k data["Traces"]["S3"]/4 +
    (-w^2)^k data["Traces"]["S3T"]/(3 (1 - w)) + w^k data["Traces"]["STST"]/(3 (1 - w^2)) - data["TraceL"]]];

(*
    Summary: The dimension of M_k(rho) with its method and evidence.
    Parameters: data — modularSpectralData; k — integer; method — Automatic, "Profile" or "TraceFormula".
    Options/defaults: None.
    Returns: <|"Dimension" -> nonnegative integer or Missing["UnknownDimension", reason], "Method", "Weight", "Profile",
        "Hypotheses", "Evidence"|>, or Failure.
    Effects: Pure.
    Failures: InconsistentProfile; DimensionFormulaFailure; InconsistentDimensionData (profile and trace formula
        disagree at k >= 2); MethodUnavailable (an explicit method that does not apply).
    Example: weight 0 of the trivial irrep is 1, of any other irrep 0; a weight of the wrong parity is 0.
    Remarks: Negative weights are 0 (holomorphic, finite image); parity: rho(S^2) = (-1)^k; a profile (ranks 1-5) gives
        the count at every k, cross-checked with the trace formula for k >= 2; beyond profile coverage k >= 2 uses the trace
        formula and k = 1 is Missing["UnknownDimension"] (unknown is neither zero nor existence).
    See also: ModularDimension; ModularDimensionData.
*)
resolveModularDimension[data_Association, k_?modularWeightQ, method_] := Module[{profile, fromProfile, fromTraces, base},
    base = <|"Weight" -> k, "Hypotheses" -> {"Holomorphic", If[IntegerQ[k], "IntegerWeight", "RationalWeight"], "FiniteImage"}, "Exponents" -> data["Exponents"],
        "TraceL" -> data["TraceL"], "CentralSign" -> data["CentralSign"]|>;
    (* rational weight (fractionalWeightPlan.md): F(-1/tau) = (-tau)^k rho(S) F(tau) on the principal branch forces
       rho(S^2) = e^{i Pi k}; for an SL(2,Z) quotient rho(S^2) = +-1, so every non-integer k gives 0 *)
    If[!IntegerQ[k], Return[Which[
        k < 0, Join[base, <|"Dimension" -> 0, "Method" -> "NegativeWeight", "Evidence" -> "Holomorphic forms of negative weight vanish."|>],
        !MissingQ[Lookup[data, "CentralPhase", Missing[]]] && !TrueQ[RootReduce[data["CentralPhase"] - Exp[I Pi k]] === 0],
            Join[base, <|"Dimension" -> 0, "Method" -> "CentralPhase",
                "Evidence" -> "rho(S^2) = e^{i Pi k} fails (rho(S^2) = " <> ToString[data["CentralPhase"], InputForm] <> "), so no nonzero form of this weight exists."|>],
        True, Join[base, <|"Dimension" -> Missing["UnknownDimension", "No dimension formula is implemented for this rational weight; supply the forms."],
            "Method" -> "Unknown", "Evidence" -> "None."|>]]]];
    Which[
        k < 0, Return[Join[base, <|"Dimension" -> 0, "Method" -> "NegativeWeight", "Evidence" -> "Holomorphic forms of negative weight vanish."|>]],
        k === 0, Return[Join[base, <|"Dimension" -> If[TrueQ[data["Trivial"]], 1, 0], "Method" -> "WeightZero",
            "Evidence" -> "Weight-zero forms are constants: one for the trivial irrep, none otherwise."|>]],
        IntegerQ[data["CentralSign"]] && (-1)^k =!= data["CentralSign"], Return[Join[base, <|"Dimension" -> 0, "Method" -> "Parity",
            "Evidence" -> "rho(S^2) = (-1)^k fails, so no nonzero form exists."|>]],
        (* a cover irrep: rho(S^2) = lambda I with lambda != +-1 never equals (-1)^k *)
        !IntegerQ[data["CentralSign"]] && !MissingQ[Lookup[data, "CentralPhase", Missing[]]], Return[Join[base, <|"Dimension" -> 0, "Method" -> "CentralPhase",
            "Evidence" -> "rho(S^2) = (-1)^k fails (rho(S^2) = " <> ToString[data["CentralPhase"], InputForm] <> "), so no nonzero form of integer weight exists."|>]]];
    profile = profileCandidates[data];
    (* the formula decides: a profile that cannot be formed (e.g. InconsistentProfile) blocks only Method -> "Profile" *)
    If[FailureQ[profile], If[method === "Profile", Return[profile]];
        profile = <|"Profile" -> Missing["ProfileUnavailable", First[profile]]|>];
    fromProfile = If[ListQ[profile["Profile"]], dimensionFromProfile[profile["Profile"], k], Missing["UnknownProfile"]];
    fromTraces = If[k >= 2, dimensionFromTraces[data, k], Missing["OutsideTraceFormulaDomain"]];
    If[FailureQ[fromTraces], Return[fromTraces]];
    Switch[method,
        "Profile", If[MissingQ[fromProfile], makeFailure["MethodUnavailable", "No weight profile is available for this representation.", <|"Profile" -> profile["Profile"]|>],
            Join[base, <|"Dimension" -> fromProfile, "Method" -> "Profile", "Profile" -> profile["Profile"], "Evidence" -> "Hilbert series of the weight profile."|>]],
        "TraceFormula", If[MissingQ[fromTraces], makeFailure["MethodUnavailable", "The trace formula is stated for k >= 2."],
            Join[base, <|"Dimension" -> fromTraces, "Method" -> "TraceFormula", "Profile" -> profile["Profile"], "Evidence" -> "Trace formula (k >= 2)."|>]],
        (* the dimension formula decides (user decision, uxUpdatePlan.md 2.5); the profile is derived data: a
           disagreement is a diagnostic, never a failure *)
        _, Which[
            IntegerQ[fromTraces], Join[base, <|"Dimension" -> fromTraces, "Method" -> "TraceFormula", "Profile" -> profile["Profile"],
                "Evidence" -> If[IntegerQ[fromProfile] && fromProfile === fromTraces, "Trace formula (k >= 2), equal to the weight profile.", "Trace formula (k >= 2)."]|>,
                If[IntegerQ[fromProfile] && fromProfile =!= fromTraces, <|"Diagnostics" -> "The weight profile gives " <> ToString[fromProfile] <> "."|>, <||>]],
            (* k = 1: consumers keep today's value (the profile, or unknown); the table shows the formula with a note *)
            k === 1, Join[base, <|"Dimension" -> If[IntegerQ[fromProfile], fromProfile, Missing["UnknownDimension", "Weight one beyond profile coverage has no implemented dimension formula."]],
                "Method" -> If[IntegerQ[fromProfile], "Profile", "Unknown"], "Profile" -> profile["Profile"],
                "Evidence" -> If[IntegerQ[fromProfile], "Hilbert series of the weight profile.", "None."],
                "FormulaValue" -> traceFormulaValue[data, 1], "Caveat" -> "weight 1"|>],
            True, Join[base, <|"Dimension" -> Missing["UnknownDimension", "No dimension formula applies."], "Method" -> "Unknown",
                "Profile" -> profile["Profile"], "Evidence" -> "None."|>]]]
];

(*
    Summary: The dimension cache key and its cleaning.
    Parameters: data — modularSpectralData; k — weight; method — Method value; selector — All or a group identity.
    Options/defaults: None.
    Returns: dimensionCacheKey: {RepKey (S, T matrices), AssignmentID, k, method}. cleanDimensionEntries: number of
        removed entries.
    Effects: cleanDimensionEntries removes derived entries only (no form data, no GAP state).
    Failures: None.
    Example: two irrep orders of one group give the same key for the same matrices.
    Remarks: The key is the actual modular representation (S and T matrices) and assignment, not a display position.
    See also: CleanModularDimensionCache.
*)
dimensionCacheKey[data_Association, k_?modularWeightQ, method_] := {data["RepKey"], data["AssignmentID"], k, method};
cleanDimensionEntries[selector_] := With[{remove = Select[Keys[$ModularDimensionCache], selector === All || $ModularDimensionCache[#]["GroupIdentity"] === selector &]},
    KeyDropFrom[$ModularDimensionCache, remove]; Length[remove]];

(*
    Summary: Resolve a cached dimension record.
    Parameters: c — Group or RepresentationContext; irrep — irrep ID or Rep; k — weight; effective — validated options.
    Options/defaults: Method, DimensionCache.
    Returns: Dimension record (resolveModularDimension), or Failure.
    Effects: Reads and writes $ModularDimensionCache when DimensionCache -> True.
    Failures: As modularSpectralData and resolveModularDimension.
    Example: dimensionRecord[c, t, 6, opts]["Dimension"] is 2 for the T' triplet.
    See also: ModularDimension.
*)
dimensionRecord[c_, irrep_, k_?modularWeightQ, effective_Association] := Module[{data = modularSpectralData[c, irrep], key, result},
    If[FailureQ[data], Return[data]];
    key = dimensionCacheKey[data, k, effective[Method]];
    If[TrueQ[effective[DimensionCache]] && KeyExistsQ[$ModularDimensionCache, key], Return[$ModularDimensionCache[key]["Record"]]];
    result = resolveModularDimension[data, k, effective[Method]];
    If[!FailureQ[result] && TrueQ[effective[DimensionCache]], AssociateTo[$ModularDimensionCache, key -> <|"Record" -> result, "GroupIdentity" -> data["GroupIdentity"]|>]];
    result
];

Options[ModularDimension] = Options[ModularDimensionData] = Options[ModularFormExistQ] = {Method -> Automatic, DimensionCache -> True};
Options[ModularDimensionTable] = {Method -> Automatic, DimensionCache -> True, Weights -> Range[0, 20], IrrepForm -> "Index", IrrepLabels -> <||>};
Options[ModularWeightProfile] = {};
Options[MinimumModularWeight] = {WeightSearchLimit -> 20, DimensionCache -> True, DimensionMethod -> Automatic};

(*
    Summary: Dimensions, profiles, existence and minimum weights of vector-valued modular forms.
    Status: Alpha.
    Signatures: ModularDimension[c, irrep, k]; ModularDimensionData[c, irrep, k]; ModularDimensionTable[c, irreps,
        Weights -> weights] (or ModularDimensionTable[c, irreps, weights]);
        ModularWeightProfile[c, irrep]; MinimumModularWeight[c, irrep]; ModularFormExistQ[c, irrep, k];
        CleanModularDimensionCache[c].
    Parameters: c — Group or RepresentationContext with an S,T assignment; irrep — irrep (index in the irrep order, or
        ID); k — weight, an exact rational; irreps — All (the irrep order) or a list of irreps; weights — list of exact
        rationals (option Weights, default Range[0, 20]).
    Options/defaults: Method -> Automatic ("Profile", "TraceFormula"); DimensionCache -> True; WeightSearchLimit -> 20.
    Returns: A nonnegative integer or Missing["UnknownDimension", reason]; the full record; an ordered association
        irrep -> weight -> value (Failure and Missing cells kept); the profile or Missing["UnknownProfile", reason];
        the minimum weight, or Missing["SearchLimitReached"] / Missing["UnknownMinimumWeight", weights]; True/False or
        Missing; the removal report <|"Removed" -> n|>.
    Effects: Freezes the context; derived cache only (CleanModularDimensionCache never touches forms or GAP state).
    Failures: Context failures; MissingExactSpectrum; InconsistentProfile; DimensionFormulaFailure;
        InconsistentDimensionData; option failures.
    Example: ModularDimension[c, triplet, 6] is 2 for the T' triplet (profile {2, 4, 6}).
    Remarks: Unknown is neither zero nor existence. A rational weight k needs rho(S^2) = e^{i Pi k}: for an SL(2,Z)
        quotient (rho(S^2) = +-1) every non-integer k gives 0 exactly; on a cover group an admissible non-integer k is
        Missing["UnknownDimension"] (the user supplies the forms). MinimumModularWeight searches integer weights; for a
        cover irrep it is Missing["UnknownMinimumWeight", <|"CentralPhase", "Reason"|>].
    See also: resolveModularDimension; profileCandidates.
*)
ModularDimensionData[c : (_Group | _RepresentationContext), irrep_String, k_?modularWeightQ, options : OptionsPattern[]] := Module[{effective},
    effective = resolveOperationOptions[ModularDimensionData, "ModularDimension", {options}]; If[FailureQ[effective], Return[effective]];
    dimensionRecord[c, irrep, k, effective]];
ModularDimension[c : (_Group | _RepresentationContext), irrep_String, k_?modularWeightQ, options : OptionsPattern[]] := Module[{effective, record},
    effective = resolveOperationOptions[ModularDimension, "ModularDimension", {options}]; If[FailureQ[effective], Return[effective]];
    record = dimensionRecord[c, irrep, k, effective];
    If[FailureQ[record], record, record["Dimension"]]];
ModularFormExistQ[c : (_Group | _RepresentationContext), irrep_String, k_?modularWeightQ, options : OptionsPattern[]] := Module[{effective, record},
    effective = resolveOperationOptions[ModularFormExistQ, "ModularDimension", {options}]; If[FailureQ[effective], Return[effective]];
    record = dimensionRecord[c, irrep, k, effective];
    Which[FailureQ[record], record, MissingQ[record["Dimension"]], record["Dimension"], True, record["Dimension"] > 0]];
(* the positional weight list needs the irreps argument explicitly: a lone list is the irreps (D3) *)
ModularDimensionTable[c : (_Group | _RepresentationContext), irreps : Except[_Rule | _RuleDelayed], weights_List, options : OptionsPattern[]] :=
    If[AllTrue[weights, modularWeightQ], ModularDimensionTable[c, irreps, Weights -> weights, options],
        makeFailure["InvalidInput", "Weights must be exact rationals (integers included)."]];
ModularDimensionTable[c : (_Group | _RepresentationContext), irreps : Except[_Rule | _RuleDelayed] : All, options : OptionsPattern[]] := Module[{effective, context, ids, weights},
    effective = resolveOperationOptions[ModularDimensionTable, "ModularDimensionTable", {options}]; If[FailureQ[effective], Return[effective]];
    weights = effective[Weights];
    context = vectorContext[c]; If[FailureQ[context], Return[context]];
    (* irreps: All (the irrep order), an index or ID, or a list of them (uxUpdatePlan.md 1.3, D3) *)
    ids = Which[irreps === All, irrepOrder[c], StringQ[irreps] || IntegerQ[irreps], {irreps}, True, irreps];
    If[FailureQ[ids], Return[ids]];
    ids = resolveIrrepArguments[c, ids]; If[FailureQ[ids], Return[ids]];
    If[!ListQ[ids] || !AllTrue[ids, StringQ], Return[makeFailure["InvalidInput", "Irreps must be All, an irrep (index or ID) or a list of them."]]];
    effective = resolveIrrepOptions[c, effective]; If[FailureQ[effective], Return[effective]];
    (* the table is a self-rendering document (U9, review F3); DisplayData[table]["Table"] holds the values *)
    dimensionTableDocument[c, AssociationMap[Function[id, AssociationMap[Function[k,
        dimensionRecord[context, id, k, KeyTake[effective, {Method, DimensionCache}]]], weights]], ids], effective]];
ModularWeightProfile[c : (_Group | _RepresentationContext), irrep_String, options : OptionsPattern[]] := Module[{effective, data, profile},
    effective = resolveOperationOptions[ModularWeightProfile, "ModularWeightProfile", {options}]; If[FailureQ[effective], Return[effective]];
    data = modularSpectralData[c, irrep]; If[FailureQ[data], Return[data]];
    profile = profileCandidates[data]; If[FailureQ[profile], profile, profile["Profile"]]];
MinimumModularWeight[c : (_Group | _RepresentationContext), irrep_String, options : OptionsPattern[]] := Module[{effective, data, profile, unknown = {}, found = None},
    effective = resolveOperationOptions[MinimumModularWeight, "MinimumModularWeight", {options}]; If[FailureQ[effective], Return[effective]];
    data = modularSpectralData[c, irrep]; If[FailureQ[data], Return[data]];
    (* a cover irrep has no admissible integer weight (rho(S^2) = lambda I, lambda != +-1) and no rational dimension formula *)
    If[MissingQ[data["CentralSign"]] && !MissingQ[data["CentralPhase"]], Return[Missing["UnknownMinimumWeight",
        <|"CentralPhase" -> data["CentralPhase"], "Reason" -> "rho(S^2) is not +-1: the admissible weights are k0 + 2 Z with e^{i Pi k0} = CentralPhase; supply the forms."|>]]];
    (* DimensionMethod (methodOptionsPlan.md 2B.7): Automatic takes the weight profile when it decides, else searches;
       "Profile" uses the profile only; "TraceFormula" searches with trace-formula dimensions (no profile shortcut) *)
    If[effective[DimensionMethod] =!= "TraceFormula",
        profile = profileCandidates[data];
        If[FailureQ[profile], Return[profile]];
        If[ListQ[profile["Profile"]], Return[Min[profile["Profile"]]]];
        If[effective[DimensionMethod] === "Profile", Return[Missing["UnknownMinimumWeight", <|"Reason" -> "The weight profile does not decide the minimum weight; DimensionMethod -> Automatic or \"TraceFormula\" searches."|>]]]];
    Do[With[{r = dimensionRecord[c, irrep, k, <|Method -> effective[DimensionMethod], DimensionCache -> effective[DimensionCache]|>]},
            Which[
                (* an explicit "TraceFormula" has no formula at some weights (k = 1): that weight is unknown, not a failure (review 2B R1) *)
                FailureQ[r] && effective[DimensionMethod] === "TraceFormula" && First[r] === "MethodUnavailable", AppendTo[unknown, k],
                FailureQ[r], Return[r, Module], MissingQ[r["Dimension"]], AppendTo[unknown, k], r["Dimension"] > 0, found = k; Break[]]],
        {k, 0, effective[WeightSearchLimit]}];
    Which[found =!= None && unknown === {}, found, unknown =!= {}, Missing["UnknownMinimumWeight", <|"UnknownWeights" -> unknown, "FirstKnownPositive" -> found|>],
        True, Missing["SearchLimitReached", effective[WeightSearchLimit]]]];
CleanModularDimensionCache[c_ : All] := Module[{selector},
    selector = If[c === All, All, With[{context = vectorContext[c]}, If[FailureQ[context], Return[context, Module], First[context]["GroupIdentity"]]]];
    <|"Removed" -> cleanDimensionEntries[selector]|>];
ModularDimensionData[c : (_Group | _RepresentationContext), i_Integer, rest___] := withIrreps[c, {i}, ModularDimensionData[c, #, rest] &];
ModularDimension[c : (_Group | _RepresentationContext), i_Integer, rest___] := withIrreps[c, {i}, ModularDimension[c, #, rest] &];
ModularFormExistQ[c : (_Group | _RepresentationContext), i_Integer, rest___] := withIrreps[c, {i}, ModularFormExistQ[c, #, rest] &];
ModularWeightProfile[c : (_Group | _RepresentationContext), i_Integer, rest___] := withIrreps[c, {i}, ModularWeightProfile[c, #, rest] &];
MinimumModularWeight[c : (_Group | _RepresentationContext), i_Integer, rest___] := withIrreps[c, {i}, MinimumModularWeight[c, #, rest] &];
ModularDimension[___] := makeFailure["InvalidInput", "ModularDimension expects a context, an irrep ID, an exact rational weight and options."];
ModularDimensionData[___] := makeFailure["InvalidInput", "ModularDimensionData expects a context, an irrep ID, an exact rational weight and options."];
ModularFormExistQ[___] := makeFailure["InvalidInput", "ModularFormExistQ expects a context, an irrep ID, an exact rational weight and options."];
ModularDimensionTable[___] := makeFailure["InvalidInput", "ModularDimensionTable expects a context, irreps, a weight list and options."];
ModularWeightProfile[___] := makeFailure["InvalidInput", "ModularWeightProfile expects a context and an irrep ID."];
MinimumModularWeight[___] := makeFailure["InvalidInput", "MinimumModularWeight expects a context, an irrep ID and options."];

True
