(*
    :Title: Automatic construction of vector-valued modular forms
    :Context: VVMFTool`Private`
    :Summary: The construction frame (an exact temporary T-diagonal basis B, rho_temp = B rho B^-1), the rank 1-3
        analytic recipes of v1 in certified exponents (eta powers and generalized hypergeometric functions of K), their
        leading-exponent and scalar-MLDE residual checks, transport to the stored basis (F_stored = B^-1 F_temp) and the
        automatic normalization anchor; the recipe dispatcher.
    :Responsibilities: constructionFrame, modularDerivativeJet, iteratedModularDerivative, scalarMLDECoefficients,
        scalarMLDEResidual, etaSeed, hypergeometricSeed, selectFormRecipe, recipeRecord; ConstructModularForms.
    :Dependencies: ModularDimensions.wl (modularSpectralData, profileCandidates); ModularScalars.wl (treeSeries,
        scalarSeries); ModularFormObjects.wl (makeFormRecord, registerForm); RepresentationBasis.wl
        (DiagonalizeRepresentationT).
    :See Also: VVMFArch/step7Plan.md (automatic construction); v1 VVMFTool-ModularForm.wl Y1D/Y2D/Y3D; local MLDE.tex.
*)

(*
    Summary: The exact construction frame of a representation.
    Parameters: ctx — formContextData; phases — certified T phases (modularSpectralData exponents).
    Options/defaults: None.
    Returns: <|"B" (rho_temp = B rho B^-1), "BInverse", "FrameRep", "Exponents" (the certified phase of each diagonal
        entry of the frame T, in frame order), "FrameID"|>, or Failure.
    Effects: Pure (no group change).
    Failures: DiagonalizeRepresentationT failures; MissingExactSpectrum (numerical matrices).
    Example: a T-diagonal stored basis with ascending phases gives B = IdentityMatrix.
    Remarks: The frame is exact; the group's representation is never mutated or replaced by another with the same T
        spectrum.
    See also: ConstructModularForms; transportSeries.
*)
constructionFrame[ctx_Association, phases_List, method_ : Automatic, level_ : Automatic] := Module[{result, t, exponents},
    If[inexactDataQ[{ctx["S"], ctx["T"]}], Return[makeFailure["MissingExactSpectrum", "Automatic construction needs exact matrices."]]];
    (* the caller's diagonalization method of the frame (methodOptionsPlan.md 2B.8) *)
    result = DiagonalizeRepresentationT[ctx["Context"], ctx["Rep"], Basis -> "General", DiagonalizationMethod -> method,
        (* the caller's level (inheritedVerification); constructed forms start "Unverified" *)
        Sequence @@ inheritedVerification[level]]; If[FailureQ[result], Return[result]];
    t = modularGeneratorMatrix[ctx["Context"], result["Rep"], "T"]; If[FailureQ[t], Return[t]];
    (* Each diagonal entry is matched to a certified phase p with an exact proof Exp[2 Pi I p] - entry == 0. *)
    exponents = Map[Function[z, SelectFirst[DeleteDuplicates[phases], TrueQ[RootReduce[z - Exp[2 Pi I #]] === 0] &, Missing["UnmatchedPhase"]]], Diagonal[t]];
    If[AnyTrue[exponents, MissingQ] || !DiagonalMatrixQ[t], Return[makeFailure["MissingExactSpectrum", "The construction frame's T entries could not be matched to certified phases."]]];
    <|"B" -> result["BasisChange"], "BInverse" -> result["InverseBasisChange"], "FrameRep" -> result["Rep"],
        "Exponents" -> exponents,
        "FrameID" -> "frame-" <> Hash[{result["BasisChange"], ctx["BasisID"]}, "SHA256", "HexString"]|>
];

(*
    Summary: Modular derivatives of series.
    Parameters: jet — series; k — weight; n — number of iterations; cutoff — requested cutoff.
    Options/defaults: None.
    Returns: Jet of D_k jet = q d/dq jet - k E2 jet/12, or of D_(k + 2 (n - 1)) ... D_(k + 2) D_k jet.
    Effects: Extends the scalar series cache.
    Failures: None for valid jets.
    Example: modularDerivativeJet[E4 jet, 4, 6] is -E6/3 + O(q^6).
    See also: scalarMLDEResidual; mldeSystem.
*)
modularDerivativeJet[jet_Association, k_, cutoff_] := jetAdd[jetThetaDerivative[jet], jetScale[jetMultiply[scalarSeries["E2", Min[cutoff, jet["Cutoff"]] - jetValuationBound[jet]], jet, cutoff], -k/12]];
iteratedModularDerivative[jet_Association, k_, n_Integer, cutoff_] := Fold[modularDerivativeJet[#1, k + 2 #2, cutoff] &, jet, Range[0, n - 1]];

(*
    Summary: The scalar MLDE of the rank 2 and 3 recipes from the indicial equation.
    Parameters: exponents — ordered frame exponents (2 or 3); k — weight.
    Options/defaults: None.
    Returns: <|"Order" -> 2, "a"|> for (D^2 + a E4) f = 0, or <|"Order" -> 3, "a", "b"|> for (D^3 + a E4 D + b E6) f = 0,
        or Failure.
    Effects: Pure.
    Failures: IndicialInconsistency (the exponents do not share one equation: the recipe does not apply).
    Example: the T' triplet {0, 1/3, 2/3} at weight 2 has a unique (a, b).
    Remarks: At the leading power q^r, D_(k + 2j) acts as r - (k + 2j)/12; E4, E6 start with 1.
    See also: scalarMLDEResidual.
*)
scalarMLDECoefficients[exponents_List, k_] := Module[{lead, a, b, solutions},
    lead[r_, n_] := Product[r - (k + 2 j)/12, {j, 0, n - 1}];
    Switch[Length[exponents],
        2, solutions = Solve[Map[lead[#, 2] + a == 0 &, exponents], {a}],
        3, solutions = Solve[Map[lead[#, 3] + a lead[#, 1] + b == 0 &, exponents], {a, b}],
        _, Return[makeFailure["IndicialInconsistency", "Scalar MLDE coefficients are defined for ranks 2 and 3 here."]]];
    If[Length[solutions] =!= 1, Return[makeFailure["IndicialInconsistency", "The exponents do not determine one scalar MLDE.", <|"Exponents" -> exponents, "Weight" -> k|>]]];
    If[Length[exponents] === 2, <|"Order" -> 2, "a" -> (a /. First[solutions])|>, <|"Order" -> 3, "a" -> (a /. First[solutions]), "b" -> (b /. First[solutions])|>]
];

(*
    Summary: The residual of the scalar MLDE on a series, to its known order.
    Parameters: jet — series of one component; k — weight; mlde — scalarMLDECoefficients.
    Options/defaults: None.
    Returns: <|"Residual" -> jet, "ZeroThrough" -> cutoff when every coefficient vanishes exactly, else Missing|>.
    Effects: Extends the scalar series cache.
    Failures: None.
    Example: each component of the rank 2 hypergeometric seed has ZeroThrough equal to its cutoff.
    See also: hypergeometricSeed.
*)
scalarMLDEResidual[jet_Association, k_, mlde_Association] := Module[{cutoff = jet["Cutoff"], d1, residual},
    residual = Switch[mlde["Order"],
        2, jetAdd[iteratedModularDerivative[jet, k, 2, cutoff], jetScale[jetMultiply[scalarSeries["E4", cutoff], jet, cutoff], mlde["a"]]],
        3, d1 = modularDerivativeJet[jet, k, cutoff];
            jetAdd[{iteratedModularDerivative[jet, k, 3, cutoff], jetScale[jetMultiply[scalarSeries["E4", cutoff], iteratedModularDerivative[jet, k, 1, cutoff], cutoff], mlde["a"]],
                jetScale[jetMultiply[scalarSeries["E6", cutoff], jet, cutoff], mlde["b"]]}]];
    <|"Residual" -> residual, "ZeroThrough" -> If[residual["Terms"] === <||>, residual["Cutoff"], Missing["NonzeroResidual", First[Keys[residual["Terms"]]]]]|>
];

(*
    Summary: The analytic seeds of ranks 1, 2 and 3 in the construction frame.
    Parameters: exponents — ordered frame exponents; k — minimum weight; family — family ID.
    Options/defaults: None.
    Returns: <|"Components" -> frame trees (FormParameter relative coefficients on components 2 and 3), "Parameters" ->
        {<|"ID", "Label"|>...}, "Method"|>, or Failure.
    Effects: Pure.
    Failures: UnsupportedConstruction (repeated exponents: the recipe's components coincide); SingularHypergeometric.
    Example: rank 1 with exponent 1/3 gives {Eta^8} of weight 4.
    Remarks: v1 Y1D/Y2D/Y3D: rank 1 eta^(2 k0); rank 2 eta^(12 (r1 + r2) - 2) (K/1728)^((6 (r1 - r2) + 1)/12)
        2F1((6 (r1 - r2) + 1)/12, (6 (r1 - r2) + 5)/12; r1 - r2 + 1; K) and the same with r1, r2 exchanged; rank 3
        eta^(8 (r1 + r2 + r3) - 4) (K/1728)^((a1 + 1)/6) 3F2((a1 + 1)/6, (a1 + 3)/6, (a1 + 5)/6; r1 - r2 + 1, r1 - r3 + 1; K)
        with a1 = 4 r1 - 2 r2 - 2 r3 and cyclic versions. Component i leads with q^(r_i).
    See also: ConstructModularForms.
*)
etaSeed[exponents_List, k_, family_String] := <|"Components" -> {ModularScalarNode["Eta", FormVariable["q"], "q"]^(2 k)}, "Parameters" -> {}, "Method" -> "Eta1D"|>;
hypergeometricSeed[exponents_List, k_, family_String] := Module[{eta = ModularScalarNode["Eta", FormVariable["q"], "q"], kk = ModularScalarNode["K", FormVariable["q"], "q"]/1728,
        node, d = Length[exponents], parameters, terms},
    If[!DuplicateFreeQ[exponents], Return[makeFailure["UnsupportedConstruction", "Repeated T exponents make the hypergeometric recipe degenerate.", <|"Exponents" -> exponents|>]]];
    node[a_, b_] := HypergeometricKNode[a, b, FormVariable["q"], "q"];
    terms = Switch[d,
        2, With[{r = exponents}, Table[With[{s = 6 (r[[i]] - r[[3 - i]]) + 1},
            eta^(12 Total[r] - 2) kk^(s/12) node[{s/12, (s + 4)/12}, {r[[i]] - r[[3 - i]] + 1}]], {i, 2}]],
        3, With[{r = exponents}, Table[With[{a = 4 r[[i]] - 2 Total[Delete[r, i]], others = Delete[r, i]},
            eta^(8 Total[r] - 4) kk^((a + 1)/6) node[{(a + 1)/6, (a + 3)/6, (a + 5)/6}, {r[[i]] - others[[1]] + 1, r[[i]] - others[[2]] + 1}]], {i, 3}]]];
    If[AnyTrue[terms, !FreeQ[#, HypergeometricKNode[a_, b_, __] /; hypergeometricSingularity[a, b] =!= None] &],
        Return[makeFailure["SingularHypergeometric", "A hypergeometric factor of the recipe is singular.", <|"Exponents" -> exponents|>]]];
    parameters = Table[<|"ID" -> family <> ":c" <> ToString[i], "Label" -> "c" <> ToString[i]|>, {i, d - 1}];
    <|"Components" -> Prepend[MapThread[FormParameter[#1["ID"]] #2 &, {parameters, Rest[terms]}], First[terms]], "Parameters" -> parameters,
        "Method" -> If[d === 2, "Hypergeometric2D", "Hypergeometric3D"]|>
];

$ModularConstructionMethods = {"Eta1D", "Hypergeometric2D", "Hypergeometric3D", "Cyclic4D", "NonCyclic4D", "Coupled5D"};

(*
    Summary: Select the construction recipe for a representation.
    Parameters: data — modularSpectralData; profile — profileCandidates; method — Method option.
    Options/defaults: None.
    Returns: Method name, or Failure.
    Effects: Pure.
    Failures: UnsupportedConstruction (beyond the implemented recipes, with dimension and profile data); InapplicableMethod
        (an explicit method that does not fit the rank or profile).
    Example: a triplet gives "Hypergeometric3D"; a noncyclic rank-4 profile gives "NonCyclic4D".
    See also: ConstructModularForms.
*)
selectFormRecipe[data_Association, profile_Association, method_] := Module[{automatic},
    automatic = Switch[data["Dimension"], 1, "Eta1D", 2, "Hypergeometric2D", 3, "Hypergeometric3D",
        4, Lookup[profile, "Type", None], 5, If[Lookup[profile, "Type", None] === "Rank502246", "Coupled5D", None], _, None];
    Which[
        method === Automatic && automatic === None, makeFailure["UnsupportedConstruction", "No automatic recipe is implemented for this representation; use CreateModularForm for a manual definition.",
            <|"Dimension" -> data["Dimension"], "Profile" -> profile["Profile"], "Exponents" -> data["Exponents"]|>],
        method === Automatic, automatic,
        !MemberQ[$ModularConstructionMethods, method], makeFailure["InvalidOption", "Unknown construction method.", <|"Options" -> {Method}|>],
        method =!= automatic, makeFailure["InapplicableMethod", "The construction method does not fit this representation's rank and weight profile.",
            <|"Method" -> method, "Applicable" -> automatic, "Profile" -> profile["Profile"]|>],
        True, method]
];

Options[ConstructModularForms] = {Method -> Automatic, SeriesOrder -> Automatic, DiagonalizationMethod -> Automatic, Verification -> Automatic};

(*
    Summary: Construct the generating vector-valued modular forms of an irrep.
    Status: Alpha.
    Parameters: c — Group or RepresentationContext with an S,T assignment; irrep — irrep ID.
    Options/defaults: Method -> Automatic (or "Eta1D", "Hypergeometric2D", "Hypergeometric3D", "Cyclic4D", "NonCyclic4D",
        "Coupled5D"); SeriesOrder -> Automatic (checks through order 6) or a positive integer; Verification -> Automatic or
        "Numerical" (the recipe evidence: leading exponents and MLDE residuals; "Exact" is InapplicableOption) or None (no
        recipe evidence is computed or recorded; the forms are "Unverified" as every new form).
    Returns: Ordered list of new ModularForm objects (a singleton for one seed), each with its weight, recipe,
        construction frame, unresolved relative normalization (resolved for rank 1), and recipe evidence; or Failure.
    Effects: Freezes the context; registers the forms; no group mutation.
    Failures: UnsupportedConstruction (also for an irrep with rho(S)^4 != I); InapplicableMethod; InconsistentProfile; MissingExactSpectrum; IndicialInconsistency;
        RecipeCheckFailed (a leading exponent or the MLDE residual does not match); option failures.
    Example: ConstructModularForms[c, triplet] gives the weight-2 triplet of the T' module.
    Remarks: The forms are generators supplied by the recipe, not every form of every weight. The normalization anchor
        is the first component of F in the construction frame at its leading exponent, value 1; ModularFormGetCoeff
        resolves the relative coefficients.
    See also: selectFormRecipe; etaSeed; hypergeometricSeed; ModularFormGetCoeff.
*)
ConstructModularForms[c : (_Group | _RepresentationContext), irrep_String, options : OptionsPattern[]] := Module[
    {effective, ctx, data, profile, method, frame, k0, family, seeds},
    effective = resolveOperationOptions[ConstructModularForms, "ConstructModularForms", {options}]; If[FailureQ[effective], Return[effective]];
    If[effective[Verification] === "Exact", Return[makeFailure["InapplicableOption",
        "The recipe evidence is a check through a finite order, not an exact proof; Verification is Automatic, \"Numerical\" or None.", <|"Options" -> {Verification}|>]]];
    ctx = formContextData[c, irrep]; If[FailureQ[ctx], Return[ctx]];
    data = modularSpectralData[ctx["Context"], irrep]; If[FailureQ[data], Return[data]];
    (* constructions are for SL(2,Z) quotients (rho(S)^4 = I); forms of a cover irrep (rational weight) are user supplied *)
    If[!MatchQ[data["CentralSign"], 1 | -1], Return[makeFailure["UnsupportedConstruction",
        If[MissingQ[data["CentralPhase"]], "ConstructModularForms needs rho(S^2) = +-1 times the identity; this representation's rho(S^2) is not a scalar +-1.",
            "ConstructModularForms builds forms for SL(2,Z) quotients (rho(S)^4 = I); this irrep has rho(S^2) = lambda I with lambda != +-1 (a cover group, rational weight): supply the forms with CreateModularForm."],
        <|"IrrepID" -> irrep, "CentralPhase" -> data["CentralPhase"]|>]]];
    profile = profileCandidates[data]; If[FailureQ[profile], Return[profile]];
    method = selectFormRecipe[data, profile, effective[Method]]; If[FailureQ[method], Return[method]];
    frame = constructionFrame[ctx, data["Exponents"], effective[DiagonalizationMethod], effective[Verification]]; If[FailureQ[frame], Return[frame]];
    k0 = Min[profile["Profile"]]; family = "family-" <> CreateUUID[];
    seeds = Switch[method,
        "Eta1D", {Join[etaSeed[frame["Exponents"], k0, family], <|"Weight" -> k0, "SeedID" -> "F"|>]},
        "Hypergeometric2D" | "Hypergeometric3D", With[{s = hypergeometricSeed[frame["Exponents"], k0, family]}, If[FailureQ[s], Return[s, Module], {Join[s, <|"Weight" -> k0, "SeedID" -> "F"|>]}]],
        _, If[DownValues[mldeSeeds] === {}, Return[makeFailure["UnsupportedConstruction", "The rank 4 and 5 MLDE recipes are not loaded.", <|"Method" -> method|>], Module],
            With[{s = mldeSeeds[method, frame["Exponents"], k0, family, effective]}, If[FailureQ[s], Return[s, Module], s]]]];
    Map[Function[seed, Module[{evidence = If[effective[Verification] === None, None, recipeEvidence[seed, frame, If[effective[SeriesOrder] === Automatic, 6, effective[SeriesOrder]]]],
            definition, record},
            If[FailureQ[evidence], Return[evidence, Module]];
            definition = Join[<|"SchemaVersion" -> 1, "DefinitionID" -> "definition-" <> CreateUUID[], "Kind" -> If[KeyExistsQ[seed, "Recipe"], "MLDE", "Analytic"],
                "Coordinate" -> "q", "VariableLabel" -> "q", "Components" -> Expand /@ (frame["BInverse"] . seed["Components"]), "Dimension" -> Length[seed["Components"]],
                "Parameters" -> seed["Parameters"], "FamilyID" -> family, "Jet" -> Missing["NotAJet"]|>,
                If[KeyExistsQ[seed, "Recipe"], <|"Recipe" -> Join[seed["Recipe"], <|"FrameBInverse" -> frame["BInverse"]|>]|>, <||>]];
            record = makeFormRecord[ctx, seed["Weight"], definition, <|"Method" -> seed["Method"],
                "Coefficients" -> <|"Kind" -> "Anchor", "Rules" -> If[seed["Parameters"] === {}, {}, Missing["Unresolved"]], "ProofStatus" -> If[seed["Parameters"] === {}, "NotApplicable", "None"],
                    "AnchorFrameID" -> frame["FrameID"], "FrameRep" -> frame["FrameRep"], "FrameFromStored" -> frame["B"], "FamilyID" -> family, "SeedID" -> "F", "AnchorSeed" -> "F",
                    "Component" -> 1, "Exponent" -> First[frame["Exponents"]], "Value" -> 1|>,
                "Validation" -> If[evidence === None, <|"Status" -> "Unverified"|>, <|"Status" -> "Unverified", "RecipeEvidence" -> evidence|>],
                "Provenance" -> <|"Source" -> "ConstructModularForms", "Recipe" -> seed["Method"], "SeedID" -> seed["SeedID"], "FamilyID" -> family,
                    "FrameComponents" -> seed["Components"], "Exponents" -> frame["Exponents"], "Weight" -> seed["Weight"], "ProfileType" -> Lookup[profile, "Type", None]|>|>];
            If[FailureQ[record], Return[record, Module]];
            record = validateFormRecord[record]; If[FailureQ[record], Return[record, Module]];
            registerForm[record]]], seeds]
];
ConstructModularForms[c : (_Group | _RepresentationContext), i_Integer, rest___] := withIrreps[c, {i}, ConstructModularForms[c, #, rest] &];
ConstructModularForms[___] := makeFailure["InvalidInput", "ConstructModularForms expects a Group or RepresentationContext, an irrep ID and options."];

(*
    Summary: Leading-exponent and MLDE evidence of a seed in its construction frame.
    Parameters: seed — seed association; frame — constructionFrame; order — check order (positive integer).
    Options/defaults: None.
    Returns: <|"LeadingExponents" -> {...}, "MLDE" -> coefficients or Missing, "ResidualZeroThrough" -> {...}, "Order"|>,
        or RecipeCheckFailed Failure.
    Effects: Extends the scalar series cache.
    Failures: RecipeCheckFailed; IndicialInconsistency.
    Example: the triplet seed's leading exponents equal the frame exponents and its residuals vanish through order 6.
    Remarks: Relative FormParameter coefficients are set to 1 for the check (each component is checked separately).
    See also: scalarMLDEResidual.
*)
recipeEvidence[seed_Association, frame_Association, order_Integer] := Module[{jets, leading, mlde, residuals},
    If[Lookup[seed, "Evidence", None] =!= None, Return[seed["Evidence"]]];
    jets = Map[treeSeries[# /. FormParameter[_] -> 1, frame["Exponents"][[1]] + order + 1] &, seed["Components"]];
    If[AnyTrue[jets, FailureQ], Return[FirstCase[jets, _Failure]]];
    leading = Map[If[MissingQ[jetLeadingTerm[#]], Missing["UnknownLeadingTerm"], jetLeadingTerm[#]["Exponent"]] &, jets];
    If[Mod[leading, 1] =!= frame["Exponents"] && leading =!= frame["Exponents"],
        Return[makeFailure["RecipeCheckFailed", "A component's leading q exponent differs from its frame T exponent.", <|"Leading" -> leading, "Exponents" -> frame["Exponents"]|>]]];
    If[Length[seed["Components"]] < 2, Return[<|"LeadingExponents" -> leading, "MLDE" -> Missing["NotApplicable"], "Order" -> order|>]];
    mlde = scalarMLDECoefficients[leading, seed["Weight"]]; If[FailureQ[mlde], Return[mlde]];
    residuals = Map[scalarMLDEResidual[#, seed["Weight"], mlde]["ZeroThrough"] &, jets];
    If[AnyTrue[residuals, MissingQ], Return[makeFailure["RecipeCheckFailed", "A component does not satisfy the recipe's scalar MLDE.", <|"Residuals" -> residuals|>]]];
    <|"LeadingExponents" -> leading, "MLDE" -> mlde, "ResidualZeroThrough" -> residuals, "Order" -> order|>
];

(* -------------------------------------------------------------------------
   Rank 4 and 5: modular linear differential equations (source systems of v1)
   ------------------------------------------------------------------------- *)

(*
    Summary: The source MLDE systems as residual functions of the F and G series.
    Parameters: kind — "Cyclic4D", "NonCyclic4D" or "Coupled5D".
    Options/defaults: None.
    Returns: <|"Kind", "Unknowns" (coefficient names), "HasG", "Residuals" -> Function[{f, g, c, k, cutoff}, list of
        residual jets]|>, or Failure.
    Effects: Pure.
    Failures: UnsupportedConstruction.
    Example: mldeSystem["NonCyclic4D"]["Unknowns"] is {"a1", "a2", "a3"}.
    Remarks: Cyclic4D: -D^4 F + a1 E4^2 F + a2 E6 D F + a3 E4 D^2 F = 0. NonCyclic4D: -D^3 F + a1 E6 F + a2 E4 D F
        + a3 E4 G = 0 and -D G + E4 F = 0. Coupled5D: -D G + E4 F = 0 and -D^4 F + b1 E4^2 F + b2 E6 D F + b3 E6 G
        + b4 E4 D^2 F = 0. D^j applies D_k, D_(k + 2), ... with the successive weights; G has weight k + 2.
    See also: solveIndicialSystem; extendMLDESeries.
*)
mldeSystem[kind_String] := Module[{e4, e6, d, dn},
    e4[cut_] := scalarSeries["E4", cut]; e6[cut_] := scalarSeries["E6", cut];
    d[f_, w_, cut_] := modularDerivativeJet[f, w, cut]; dn[f_, w_, n_, cut_] := iteratedModularDerivative[f, w, n, cut];
    Switch[kind,
        "Cyclic4D", <|"Kind" -> kind, "Unknowns" -> {"a1", "a2", "a3"}, "HasG" -> False,
            "Residuals" -> Function[{f, g, c, k, cut}, {jetAdd[{jetScale[dn[f, k, 4, cut], -1], jetScale[jetMultiply[jetMultiply[e4[cut], e4[cut], cut], f, cut], c["a1"]],
                jetScale[jetMultiply[e6[cut], d[f, k, cut], cut], c["a2"]], jetScale[jetMultiply[e4[cut], dn[f, k, 2, cut], cut], c["a3"]]}]}]|>,
        "NonCyclic4D", <|"Kind" -> kind, "Unknowns" -> {"a1", "a2", "a3"}, "HasG" -> True,
            "Residuals" -> Function[{f, g, c, k, cut}, {jetAdd[{jetScale[dn[f, k, 3, cut], -1], jetScale[jetMultiply[e6[cut], f, cut], c["a1"]],
                jetScale[jetMultiply[e4[cut], d[f, k, cut], cut], c["a2"]], jetScale[jetMultiply[e4[cut], g, cut], c["a3"]]}],
                jetAdd[jetScale[d[g, k + 2, cut], -1], jetMultiply[e4[cut], f, cut]]}]|>,
        "Coupled5D", <|"Kind" -> kind, "Unknowns" -> {"b1", "b2", "b3", "b4"}, "HasG" -> True,
            "Residuals" -> Function[{f, g, c, k, cut}, {jetAdd[jetScale[d[g, k + 2, cut], -1], jetMultiply[e4[cut], f, cut]],
                jetAdd[{jetScale[dn[f, k, 4, cut], -1], jetScale[jetMultiply[jetMultiply[e4[cut], e4[cut], cut], f, cut], c["b1"]],
                    jetScale[jetMultiply[e6[cut], d[f, k, cut], cut], c["b2"]], jetScale[jetMultiply[e6[cut], g, cut], c["b3"]],
                    jetScale[jetMultiply[e4[cut], dn[f, k, 2, cut], cut], c["b4"]]}]}]|>,
        _, makeFailure["UnsupportedConstruction", "Unknown MLDE system.", <|"Kind" -> kind|>]]
];

(*
    Summary: Solve the indicial equations of a system jointly across all exponents.
    Parameters: system — mldeSystem; exponents — frame exponents; k — weight of F.
    Options/defaults: None.
    Returns: <|"Coefficients" -> <|name -> value|>, "GLeading" -> list (G's leading coefficient per component, F's being
        1) or Missing["NoG"]|>, or Failure.
    Effects: Pure.
    Failures: IndicialInconsistency (no solution, several, or a free coefficient); Resonance (G's leading coefficient is
        not determined: r = (k + 2)/12).
    Example: the noncyclic [48,29] exponents {1/8, 3/8, 5/8, 7/8} at k = 4 give unique a1, a2, a3.
    Remarks: The residuals are evaluated on F = q^r and G = g0 q^r with inert unknowns; their q^r coefficients are
        linear in the unknowns, and every exponent must satisfy the same coefficients.
    See also: extendMLDESeries.
*)
solveIndicialSystem[system_Association, exponents_List, k_] := Module[{c, equations, g0, solutions},
    c = AssociationMap[mldeUnknown, system["Unknowns"]];
    g0 = Table[mldeUnknown["g0", i], {i, Length[exponents]}];
    equations = Flatten[MapIndexed[Function[{r, i}, Module[{f = makeJet[<|r -> 1|>, r + 1], g = makeJet[<|r -> g0[[First[i]]]|>, r + 1]},
        Map[Lookup[#["Terms"], r, 0] == 0 &, system["Residuals"][f, If[system["HasG"], g, makeJet[<||>, Infinity]], c, k, r + 1]]]], exponents]];
    solutions = Quiet[Solve[equations, Join[Values[c], If[system["HasG"], g0, {}]]]];
    If[Length[solutions] =!= 1 || !FreeQ[Values[c] /. First[solutions], _mldeUnknown] || (system["HasG"] && !FreeQ[g0 /. First[solutions], _mldeUnknown]),
        Return[makeFailure[If[system["HasG"] && AnyTrue[exponents, # == (k + 2)/12 &], "Resonance", "IndicialInconsistency"],
            "The indicial equations do not determine the system's coefficients uniquely for these exponents.", <|"Exponents" -> exponents, "Weight" -> k, "Kind" -> system["Kind"]|>]]];
    <|"Coefficients" -> AssociationMap[(mldeUnknown[#] /. First[solutions]) &, system["Unknowns"]],
        "GLeading" -> If[system["HasG"], g0 /. First[solutions], Missing["NoG"]]|>
];

(*
    Summary: Extend the solution of an MLDE order by order.
    Parameters: system — mldeSystem; indicial — solveIndicialSystem; exponents — frame exponents; k — weight; order —
        number of orders after the leading one (positive integer).
    Options/defaults: None.
    Returns: <|"F" -> list of component jets (leading coefficient 1), "G" -> list of component jets or Missing["NoG"],
        "Order"|>, each component known below r + order + 1, or Failure.
    Effects: Extends the scalar series cache.
    Failures: Resonance (the order-n coefficients are not determined); IndicialInconsistency (inconsistent equations).
    Example: the A5 quintet (Coupled5D, k = 2) gives F with coefficients {1, 6, 18, ...} for exponent 0.
    Remarks: At each order the new coefficients f_n (and g_n) are inert unknowns; the residuals' coefficients at q^(r + n)
        are linear in them and must have a unique solution. Nothing is padded with zeros and no solution is chosen.
    See also: validateMLDEResidual.
*)
extendMLDESeries[system_Association, indicial_Association, exponents_List, k_, order_Integer?Positive] := Catch[Module[{fs = {}, gs = {}},
    Do[Module[{r = exponents[[l]], f, g},
            f = makeJet[<|r -> 1|>, r + 1];
            g = If[system["HasG"], makeJet[<|r -> indicial["GLeading"][[l]]|>, r + 1], makeJet[<||>, Infinity]];
            Do[Module[{cut = r + n + 1, trialF, trialG, residuals, solution, unknowns},
                    trialF = makeJet[Append[f["Terms"], r + n -> mldeUnknown["f", n]], cut];
                    trialG = If[system["HasG"], makeJet[Append[g["Terms"], r + n -> mldeUnknown["g", n]], cut], g];
                    unknowns = If[system["HasG"], {mldeUnknown["f", n], mldeUnknown["g", n]}, {mldeUnknown["f", n]}];
                    residuals = system["Residuals"][trialF, trialG, indicial["Coefficients"], k, cut];
                    solution = Quiet[Solve[Map[Lookup[#["Terms"], r + n, 0] == 0 &, residuals], unknowns]];
                    If[Length[solution] =!= 1 || !FreeQ[unknowns /. First[solution], _mldeUnknown],
                        Throw[makeFailure[If[solution === {}, "IndicialInconsistency", "Resonance"], "The MLDE does not determine the series coefficients at this order.",
                            <|"Exponent" -> r, "Order" -> n, "Kind" -> system["Kind"]|>], "mlde"]];
                    f = makeJet[Append[f["Terms"], r + n -> (mldeUnknown["f", n] /. First[solution])], cut];
                    If[system["HasG"], g = makeJet[Append[g["Terms"], r + n -> (mldeUnknown["g", n] /. First[solution])], cut]]],
                {n, 1, order}];
            AppendTo[fs, f]; If[system["HasG"], AppendTo[gs, g]]],
        {l, Length[exponents]}];
    <|"F" -> fs, "G" -> If[system["HasG"], gs, Missing["NoG"]], "Order" -> order|>], "mlde"];

(*
    Summary: Check that a solution satisfies every MLDE equation through its known order.
    Parameters: system; coefficients — <|name -> value|>; solution — extendMLDESeries; k — weight.
    Options/defaults: None.
    Returns: <|"ZeroThrough" -> per component the cutoff through which every residual coefficient vanishes exactly|>, or
        RecipeCheckFailed Failure.
    Effects: Extends the scalar series cache.
    Failures: RecipeCheckFailed.
    Example: the [48,29] noncyclic solution has zero residuals through its order.
    Remarks: Independent of the solver: the residual functions are re-evaluated on the final series.
    See also: extendMLDESeries.
*)
validateMLDEResidual[system_Association, coefficients_Association, solution_Association, k_] := Module[{zero},
    zero = Table[With[{f = solution["F"][[l]], g = If[system["HasG"], solution["G"][[l]], makeJet[<||>, Infinity]]},
            With[{residuals = system["Residuals"][f, g, coefficients, k, f["Cutoff"]]},
                If[AllTrue[residuals, #["Terms"] === <||> &], Min[Lookup[residuals, "Cutoff"]], Missing["NonzeroResidual"]]]],
        {l, Length[solution["F"]]}];
    If[AnyTrue[zero, MissingQ], makeFailure["RecipeCheckFailed", "An MLDE residual does not vanish.", <|"ZeroThrough" -> zero|>], <|"ZeroThrough" -> zero|>]
];

(*
    Summary: The seeds (F, and G for coupled systems) of the rank 4 and 5 recipes.
    Parameters: method — "Cyclic4D", "NonCyclic4D" or "Coupled5D"; exponents — frame exponents; k — weight of F; family;
        effective — ConstructModularForms options.
    Options/defaults: SeriesOrder Automatic means 6 orders.
    Returns: List of seed associations: frame components c_i MLDEComponentNode[family, seed, i] (c_1 = 1, the anchor;
        c_i FormParameter atoms shared by F and G), "Recipe" (system, coefficients, exponents, weight, solution jets),
        "Evidence"; weights k and k + 2; or Failure.
    Effects: Extends the scalar series cache.
    Failures: As solveIndicialSystem, extendMLDESeries and validateMLDEResidual; UnsupportedConstruction (repeated
        exponents).
    Example: mldeSeeds["NonCyclic4D", {1/8, 3/8, 5/8, 7/8}, 4, "f", opts] gives F (weight 4) and G (weight 6).
    Remarks: One joint recipe and one overall scale fixed by F's first component; G's component l is the companion of
        F's with its determined leading coefficient.
    See also: ConstructModularForms; extendMLDESeries.
*)
mldeSeeds[method_String, exponents_List, k_, family_String, effective_Association] := Module[{system, indicial, order, solution, check, parameters, seed},
    system = mldeSystem[method]; If[FailureQ[system], Return[system]];
    If[!DuplicateFreeQ[exponents], Return[makeFailure["UnsupportedConstruction", "Repeated T exponents are not supported by the MLDE recipes.", <|"Exponents" -> exponents|>]]];
    indicial = solveIndicialSystem[system, exponents, k]; If[FailureQ[indicial], Return[indicial]];
    order = If[effective[SeriesOrder] === Automatic, 6, effective[SeriesOrder]];
    solution = extendMLDESeries[system, indicial, exponents, k, order]; If[FailureQ[solution], Return[solution]];
    check = validateMLDEResidual[system, indicial["Coefficients"], solution, k]; If[FailureQ[check], Return[check]];
    parameters = Table[<|"ID" -> family <> ":c" <> ToString[i], "Label" -> "c" <> ToString[i]|>, {i, Length[exponents] - 1}];
    seed[id_String, weight_] := <|"Components" -> Table[If[i === 1, 1, FormParameter[parameters[[i - 1]]["ID"]]] MLDEComponentNode[family, id, i], {i, Length[exponents]}],
        "Parameters" -> parameters, "Method" -> method, "Weight" -> weight, "SeedID" -> id,
        "Recipe" -> <|"System" -> method, "Coefficients" -> indicial["Coefficients"], "GLeading" -> indicial["GLeading"], "Exponents" -> exponents, "Weight" -> k,
            "FamilyID" -> family, "SeedID" -> id, "Solution" -> solution|>,
        "Evidence" -> <|"LeadingExponents" -> exponents, "MLDE" -> <|"System" -> method, "Coefficients" -> indicial["Coefficients"]|>,
            "ResidualZeroThrough" -> check["ZeroThrough"], "Order" -> order|>|>;
    If[system["HasG"], {seed["F", k], seed["G", k + 2]}, {seed["F", k]}]
];

True
