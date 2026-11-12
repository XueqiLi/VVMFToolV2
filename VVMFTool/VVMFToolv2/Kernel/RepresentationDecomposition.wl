(*
    :Title: Representation decomposition
    :Context: VVMFTool`Private`
    :Summary: Decompose a bound representation into certified irreducible targets with a complete,
        verified embedding.
    :Responsibilities:
        - Select and validate targets (stored active variants, computed when missing on a live group, or
          supplied TargetRepresentations).
        - Wolfram GeneratorEquations route: intertwiner null spaces per constituent, multiplicity-space
          normalization in unitary coordinates, exact proofs in a number field or numerical residuals.
        - The public DecomposeRepresentation result: blocks, multiplicities, embedding U and its inverse.
    :Dependencies: Diagnostics.wl; Configuration.wl; GroupConstruction.wl (resolveOperationOptions);
        Representation.wl; RepresentationValidation.wl (arithmetic, exact domains, validation);
        RepresentationBasis.wl (representationOperand, invariantForm, ldlDecomposition); RepresentationJobs.wl
        (runRepresentationEnrichment).
    :See Also: VVMFArch/step2Plan.md (decomposition); design.md.
*)

(*
    Summary: Targets for the nonzero constituents of a decomposition.
    Parameters: context — Group or RepresentationContext; snapshot — resolved snapshot; multiplicities —
        irrep ID -> multiplicity; effective — validated DecomposeRepresentation options; settings.
    Options/defaults: TargetRepresentations -> Automatic uses each irrep's active variant (unitary when
        Basis -> "Unitary"); on a live Group missing targets are computed with ComputeGroupRepresentations
        semantics under the same options.
    Returns: Association irrep ID -> <|"Rep" -> visible target, "Native" -> matrices to solve against,
        "Scales" -> list, "Source" -> variant ID or "Supplied"|>, or Failure.
    Effects: May run representation computation on a live group (new generations).
    Failures: MissingTargets (a frozen context without stored targets, or a supplied association that does
        not cover a constituent; Suggestions give the command); validation failures of supplied targets
        (WrongCharacter, InvalidRepresentation, NonUnitaryRepresentation).
    Example: for S3's regular representation the targets are the three stored irreps.
    Remarks: A scaled stored target F = L N L^-1 is solved against its native matrices N; the embedding is
        transported by L^-1 afterwards. Supplied targets are validated against the same group and their
        stated irrep ID; a general target with Basis -> "Unitary" fails rather than being changed.
    See also: generatorDecomposition; validateRepBinding.
*)
decompositionTargets[context_, snapshot_Association, multiplicities_Association, effective_Association,
    settings_Association] := Module[{supplied = effective[TargetRepresentations], basis = effective[Basis], current = snapshot,
        targets = <||>, missing, target, check, computed},
    If[AssociationQ[supplied],
        missing = Complement[Keys[multiplicities], Keys[supplied]];
        If[missing =!= {}, Return[makeFailure["MissingTargets", "TargetRepresentations must cover every nonzero constituent.",
            <|"IrrepIDs" -> missing|>]]];
        Do[
            check = validateRepBinding[context, supplied[id], <|"Settings" -> settings, "Options" -> effective,
                "IrrepID" -> id, "Basis" -> basis|>];
            If[FailureQ[check], Return[check, Module]];
            targets[id] = <|"Rep" -> supplied[id], "Native" -> repMatrices[supplied[id]],
                "Scales" -> ConstantArray[1, RepDim[supplied[id]]], "Source" -> "Supplied"|>,
            {id, Keys[multiplicities]}];
        Return[targets]];
    target[id_] := Module[{entry = Lookup[current["Representations"], id, None], active, variant},
        If[!AssociationQ[entry] || !StringQ[entry["ActiveVariant"]], Return[None]];
        variant = entry["Variants"][entry["ActiveVariant"]];
        If[basis === "Unitary" && !TrueQ[variant["BasisProperties"]["Unitary"]], Return[None]];
        <|"Rep" -> variant["Rep"], "Native" -> If[MissingQ[variant["NativeMatrices"]], repMatrices[variant["Rep"]], variant["NativeMatrices"]],
            "Scales" -> If[MissingQ[variant["Scales"]], ConstantArray[1, entry["Dimension"]], variant["Scales"]],
            "Source" -> entry["ActiveVariant"]|>];
    missing = Select[Keys[multiplicities], target[#] === None &];
    If[missing =!= {},
        If[!MatchQ[context, _Group],
            Return[makeFailure["MissingTargets", "The context has no stored target for some constituents.",
                <|"IrrepIDs" -> missing, "Suggestions" -> {"ComputeGroupRepresentations[g, " <> ToString[missing, InputForm] <>
                    ", Basis -> " <> ToString[basis, InputForm] <> "] on the live group, then decompose again."}|>]]];
        computed = runRepresentationEnrichment[context, <|"irrepIDs" -> missing, "basis" -> basis|>, effective];
        If[FailureQ[computed], Return[computed]];
        current = resolveRepContext[context]; If[FailureQ[current], Return[current]];
        missing = Select[Keys[multiplicities], target[#] === None &];
        If[missing =!= {}, Return[makeFailure["MissingTargets", "Some constituents have no target in the requested basis.",
            <|"IrrepIDs" -> missing|>]]]];
    AssociationMap[target, Keys[multiplicities]]
];

(*
    Summary: Direct sum of square matrices.
    Parameters: blocks — list of square matrices.
    Options/defaults: None.
    Returns: Block-diagonal matrix.
    Effects: Pure.
    Failures: None.
    Example: directSum[{{{1}}, {{2}}}] is {{1, 0}, {0, 2}}.
    See also: generatorDecomposition.
*)
directSum[blocks_List] := ArrayFlatten[Table[If[i === j, blocks[[i]], 0], {i, Length[blocks]}, {j, Length[blocks]}]];

(*
    Summary: Complete decomposition by the generator equations M_i X = X D_i.
    Parameters: operand; targets — from decompositionTargets; multiplicities; basis — "Unitary" or "General";
        settings; deadline; solutions — None, or irrep ID -> list of intertwiner bases X (d by target degree,
        exact) with M_i X = X N_i from a native decomposition, used instead of the null-space computation;
        knownForm — None, or an invariant form of the input computed earlier (a derived cache entry).
    Options/defaults: solutions None; knownForm None.
    Returns: <|"Embedding" -> U, "InverseEmbedding" -> Inverse[U], "BlockMatrices", "Blocks", "Validation",
        "InvariantForm"|> (the form used for unitary coordinates, Missing["General"] otherwise), or Failure.
    Effects: Pure.
    Failures: UnprovedIdentity (a null-space dimension different from the multiplicity, singular U, or an
        identity that does not hold); PrecisionFailure (numerical rank not separated); invariant-form
        failures.
    Example: the regular representation of S3 decomposes with U satisfying old . U == U . block.
    Remarks: Row-major vec(M X - X D) = (M kron I - I kron D^T) vec(X). For a target F = L N L^-1 the
        equations are solved against N (X_F = X L^-1). In unitary coordinates the m solutions X_k of one
        constituent have Gram matrices X_k^dagger H X_l = g_kl S (Schur; H the input's invariant form, the
        identity for unitary input, S = L^2); an LDL of the m-by-m positive g orthonormalizes the copies, so
        U^dagger H U = I and U maps the stored target blocks to the input coordinates. Exact covariance,
        rank and Gram identities are proved in one exact domain; square roots enter only the returned U.
    See also: decompositionTargets; DecomposeRepresentation.
*)
generatorDecomposition[operand_Association, targets_Association, multiplicities_Association, basis_String,
    settings_Association, deadline_, solutions_ : None, knownForm_ : None] := Module[{d = operand["Shape"]["Dimension"], exact = settings["Arithmetic"] === "Exact",
        field = None, matrices, ids = Keys[multiplicities], h, columns = {}, scales = {}, blocks = {}, nativeBlocks = {},
        records = {}, index = 1, xall, u, uinverse, checks, reduce, adjoint, rank, failure,
        level = Lookup[settings, "Verification", Automatic], precision = Lookup[settings, "CheckPrecision", 50]},
    If[operand["Matrices"] === {},
        (* No generators: the trivial irrep with multiplicity d; any basis decomposes it. *)
        Return[<|"Embedding" -> IdentityMatrix[d], "InverseEmbedding" -> IdentityMatrix[d], "BlockMatrices" -> {},
            "Blocks" -> Table[<|"CharacterID" -> First[ids], "Copy" -> k, "Indices" -> {k, k},
                "Target" -> targets[First[ids]]["Source"]|>, {k, d}], "Validation" -> <|"Covariance" -> True, "FullRank" -> True|>|>]];
    If[exact,
        field = settingsField[Join[{operand["Matrices"]}, Lookup[Values[targets], "Native"], Lookup[Values[targets], "Scales"]], settings];
        matrices = fieldEmbed[field, operand["Matrices"]];
        reduce = fieldReduce[field, #] &; adjoint = fieldAdjoint[field, #] &,
        matrices = toArithmetic[operand["Matrices"], settings];
        reduce = Identity; adjoint = ConjugateTranspose];
    (* The input's invariant form: the identity for unitary input; an explicit UnitarizationMethod (settings
       "FormMethod", methodOptionsPlan.md 2B.3) computes the form with that method only, also for unitary input. *)
    h = Which[basis === "General", None,
        knownForm =!= None, If[exact, fieldEmbed[field, knownForm], toArithmetic[knownForm, settings]],
        Lookup[settings, "FormMethod", Automatic] =!= Automatic,
            With[{form = invariantForm[operand, settings["FormMethod"], settings, deadline]},
                If[FailureQ[form], form, If[exact, fieldEmbed[field, fieldBack[form["Form"]]], form["Form"]]]],
        unitaryMatricesCheck[toArithmetic[operand["Matrices"], settings], settings]["Holds"], IdentityMatrix[d],
        True, With[{form = invariantForm[operand, "GroupAverage", settings, deadline]},
            Which[!FailureQ[form], If[exact, fieldEmbed[field, fieldBack[form["Form"]]], form["Form"]],
                True, With[{again = invariantForm[operand, "GeneratorEquations", settings, deadline]},
                    If[FailureQ[again], again, If[exact, fieldEmbed[field, fieldBack[again["Form"]]], again["Form"]]]]]]];
    If[FailureQ[h], Return[h]];
    failure = Catch[Do[
        Module[{target = targets[id], m = multiplicities[id], native, dt, sigma, system, null, xs, g, ldl, mixing, factors},
            dt = Length[First[target["Native"], {{1}}]];
            native = If[exact, fieldEmbed[field, target["Native"]], toArithmetic[target["Native"], settings]];
            sigma = If[exact, fieldEmbed[field, {target["Scales"]}][[1]], toArithmetic[{target["Scales"]}, settings][[1]]];
            system = Join @@ MapThread[KroneckerProduct[#1, IdentityMatrix[dt]] - KroneckerProduct[IdentityMatrix[d], Transpose[#2]] &,
                {matrices, native}];
            null = Which[
                AssociationQ[solutions], Flatten[fieldEmbed[field, #]] & /@ solutions[id],
                exact, fieldNullSpace[field, reduce[system]],
                True,
                Module[{u0, w0, v0, sv, threshold, keep},
                    {u0, w0, v0} = SingularValueDecomposition[system];
                    sv = Join[Diagonal[w0], ConstantArray[0, Max[0, d dt - Length[Diagonal[w0]]]]];
                    threshold = settings["Tolerance"] Max[Append[Abs[sv], 1]];
                    keep = Flatten[Position[Abs[sv], x_ /; x <= threshold, {1}, Heads -> False]];
                    If[Complement[Range[d dt], keep] =!= {} && Min[Abs[sv[[Complement[Range[d dt], keep]]]]] <= 10 threshold,
                        Return[makeFailure["PrecisionFailure", "The numerical rank of the intertwiner equations is not separated at this precision."], Module]];
                    Transpose[v0][[keep]]]];
            If[FailureQ[null], Throw[null]];
            If[Length[null] =!= m,
                Throw[makeFailure["UnprovedIdentity", "The intertwiner space does not have the character multiplicity.",
                    <|"IrrepID" -> id, "Dimension" -> Length[null], "Multiplicity" -> m|>]]];
            xs = Partition[#, dt] & /@ null;
            factors = ConstantArray[1, m];
            If[h =!= None,
                (* Schur: X_k^dagger H X_l = g_kl S. *)
                g = Table[reduce[adjoint[xs[[k]]] . h . xs[[l]]][[1, 1]] / sigma[[1]], {k, m}, {l, m}];
                If[exact && !AllTrue[Flatten[Table[reduce[adjoint[xs[[k]]] . h . xs[[l]] - g[[k, l]] DiagonalMatrix[sigma]], {k, m}, {l, m}], 1],
                        fieldZeroQ],
                    Throw[makeFailure["UnprovedIdentity", "The multiplicity-space Gram matrix is not a scalar multiple of the target form."]]];
                ldl = ldlDecomposition[reduce[g], If[exact, <|"Field" -> field|>, settings]];
                If[FailureQ[ldl], Throw[ldl]];
                mixing = If[exact, fieldInverse[field, adjoint[First[ldl]]], Inverse[ConjugateTranspose[First[ldl]]]];
                xs = Table[reduce[Sum[mixing[[l, k]] xs[[l]], {l, m}]], {k, m}];
                factors = If[exact, Sqrt /@ fieldBack[Last[ldl]], Sqrt[Last[ldl]]]];
            Do[
                AppendTo[columns, Transpose[xs[[k]]]];
                scales = Join[scales, (factors[[k]] Sqrt[If[exact, fieldBack[#], #]]) & /@ sigma];
                AppendTo[blocks, repMatrices[target["Rep"]]];
                AppendTo[nativeBlocks, native];
                AppendTo[records, <|"CharacterID" -> id, "Copy" -> k, "Indices" -> {index, index + dt - 1},
                    "Target" -> target["Source"]|>];
                index += dt,
                {k, m}]],
        {id, ids}]; None];
    If[FailureQ[failure], Return[failure]];
    xall = Transpose[Join @@ columns];
    (* Exact proofs on the unscaled columns: covariance with the native block sum, full rank, Gram form. The covariance
       and the Gram form are result checks at the call's Verification level (methodOptionsPlan.md 2C.4: "Numerical" on
       N[], None not checked); the rank, which the inverse needs, always runs. *)
    checks = If[exact,
        rank = fieldRank[field, xall];
        <|"FullRank" -> rank === d,
            "Covariance" -> If[level === None, "NotChecked",
                AllTrue[Range[Length[matrices]], levelZeroQ[level, reduce[matrices[[#]] . xall - xall . directSum[nativeBlocks[[All, #]]]], precision] &]],
            "UnitaryCoordinates" -> Which[h === None, Missing["General"], level === None, "NotChecked",
                True, levelZeroQ[level, reduce[adjoint[xall] . h . xall] - DiagonalMatrix[fieldEmbed[field, scales^2]], precision]]|>,
        <||>];
    u = If[exact, Map[RootReduce, fieldBack[xall] . DiagonalMatrix[1/scales], {2}], xall . DiagonalMatrix[1/scales]];
    uinverse = If[exact, Map[RootReduce, DiagonalMatrix[scales] . fieldBack[fieldInverse[field, xall]], {2}], Inverse[u]];
    If[!exact && level === None,
        checks = <|"FullRank" -> MatrixRank[u, Tolerance -> settings["Tolerance"]] === d, "Covariance" -> "NotChecked",
            "UnitaryCoordinates" -> If[h === None, Missing["General"], "NotChecked"]|>];
    If[!exact && level =!= None,
        checks = <|"FullRank" -> MatrixRank[u, Tolerance -> settings["Tolerance"]] === d,
            "CovarianceResidual" -> Max[Table[matrixResidual[matrices[[i]] . u, u . directSum[toArithmetic[blocks[[All, i]], settings]]],
                {i, Length[matrices]}]],
            "UnitaryResidual" -> If[h === None, Missing["General"], matrixResidual[ConjugateTranspose[u] . h . u, IdentityMatrix[d]]]|>;
        checks["Covariance"] = checks["CovarianceResidual"] <= settings["Tolerance"];
        If[h =!= None, checks["UnitaryCoordinates"] = checks["UnitaryResidual"] <= settings["Tolerance"]]];
    If[checks["FullRank"] =!= True || checks["Covariance"] === False || (h =!= None && checks["UnitaryCoordinates"] === False),
        Return[makeFailure["UnprovedIdentity", "The decomposition embedding did not verify.", <|"Checks" -> checks|>]]];
    <|"Embedding" -> u, "InverseEmbedding" -> uinverse, "Domain" -> If[field === None, Missing["Numerical"], domainSummary[field]],
        "BlockMatrices" -> Table[directSum[blocks[[All, i]]], {i, Length[matrices]}], "Blocks" -> records, "Validation" -> checks,
        "InvariantForm" -> Which[h === None, Missing["General"], exact, fieldBack[h], True, h]|>
];

(* Native decomposition methods (GAP/RepresentationBasis.g VVMF_Decompose), in Automatic order. *)
$NativeDecompositionMethods = {"Serre", "Alternative", "Canonical", "REPSNConstituents", "REPSNBlocks"};

(*
    Summary: Intertwiner bases from a native GAP decomposition.
    Parameters: context — Group or RepresentationContext; operand; targets — from decompositionTargets;
        multiplicities; method — a native method; effective — validated DecomposeRepresentation options.
    Options/defaults: IsomorphismMethod is passed to GAP as the alignment ("Automatic" tries BSGS,
        GroupAverage and OrbitSum where they apply, then GeneratorEquations).
    Returns: Association irrep ID -> list of exact intertwiner bases X (d by target degree) with
        M_i X = X N_i, or Failure.
    Effects: Runs one GAP enrichment on the supporting live group (a query generation; the group's
        mathematical data are unchanged).
    Failures: NativeUnavailable (a context without an accepted live group of the same state); InapplicableMethod
        (input or supplied targets that are not cyclotomic); GAP decomposition failures.
    Example: the natural permutation representation of S4 by "Serre" gives one basis per constituent.
    Remarks: Native methods need GAP-representable (cyclotomic) exact input; stored targets are named by
        variant ID, so GAP uses its own verified matrices (native matrices N for scaled variants).
    See also: DecomposeRepresentation; generatorDecomposition; GAP VVMF_Decompose.
*)
nativeDecompositionSolutions[context_, operand_Association, targets_Association, multiplicities_Association,
    method_String, effective_Association] := Module[{snapshot = operand["Snapshot"], group, orders, encode, matrices,
        targetData, result, solutions},
    group = If[MatchQ[context, _Group], context,
        SelectFirst[Keys[$GroupRegistry], With[{data = groupData[#]}, AssociationQ[data] &&
            data["StateID"] === snapshot["GroupIdentity"] && data["GeneratorIdentity"] === snapshot["GeneratorIdentity"]] &, None]];
    If[group === None, Return[makeFailure["NativeUnavailable", "Native decomposition needs an accepted live group of this state."]]];
    orders = LCM[LCM @@ snapshot["CharacterData"]["ClassOrders"], 4] {1, 2, 3, 5, 6, 10, 15, 30};
    encode[m_] := Map[cyclotomicEncoding[#, orders] &, m, {2}];
    matrices = encode /@ operand["Matrices"];
    If[!FreeQ[matrices, $Failed], Return[makeFailure["InapplicableMethod", "Native decomposition needs cyclotomic input."]]];
    targetData = Association[KeyValueMap[Function[{id, target}, id -> If[target["Source"] =!= "Supplied",
        <|"variant" -> target["Source"]|>, <|"matrices" -> (encode /@ repMatrices[target["Rep"]])|>]], targets]];
    If[!FreeQ[targetData, $Failed], Return[makeFailure["InapplicableMethod", "Native decomposition needs cyclotomic targets."]]];
    result = runGroupEnrichment[group, "Decompose", <|"decomposition" -> <|"matrices" -> matrices, "targets" -> targetData,
        "multiplicities" -> (ToString /@ multiplicities), "method" -> method,
        "alignment" -> If[effective[IsomorphismMethod] === Automatic, "Automatic", effective[IsomorphismMethod]]|>|>,
        (* The decomposition method travels in the payload; the group-job planner has its own Method. *)
        Join[effective, <|Method -> Automatic|>]];
    If[FailureQ[result], Return[result]];
    solutions = Lookup[Lookup[group["LastComputation"], "decomposition", <||>], "solutions", None];
    If[!AssociationQ[solutions] || Sort[Keys[solutions]] =!= Sort[Keys[multiplicities]],
        Return[makeFailure["InvalidDecomposition", "The native decomposition result does not cover the constituents."]]];
    solutions = Map[Map[decodeNativeRepScalar, #, {3}] &, solutions];
    If[!FreeQ[solutions, _Failure], Return[makeFailure["InvalidDecomposition", "The native decomposition result has invalid entries."]]];
    solutions
];

Options[DecomposeRepresentation] = Join[Options[RestoreGAPState], {FieldMethod -> Automatic, UnitarizationMethod -> Automatic, Method -> Automatic, IsomorphismMethod -> Automatic,
    TargetRepresentations -> Automatic, Basis -> "Unitary", Arithmetic -> "Exact", WorkingPrecision -> 50, Tolerance -> Automatic, Verification -> Automatic}];

(*
    Summary: Decompose a representation into irreducible target blocks with a verified embedding.
    Status: Alpha.
    Parameters: c — Group or RepresentationContext; r — Rep with one matrix per recorded generator.
    Options/defaults: Method -> Automatic (for exact cyclotomic input on a live group the native "Serre",
        "Alternative", "Canonical", "REPSNConstituents", "REPSNBlocks" in turn, then the Wolfram
        "GeneratorEquations"); IsomorphismMethod -> Automatic (native alignment BSGS, GroupAverage, OrbitSum where
        applicable, then GeneratorEquations);
        TargetRepresentations -> Automatic (stored active irreps, computed on a live group when missing)
        or an association irrep ID -> Rep covering every constituent; Basis -> "Unitary" (unitary targets and
        unitary multiplicity coordinates) or "General"; Arithmetic -> "Exact"; WorkingPrecision -> 50;
        Tolerance -> Automatic; Verification -> Automatic (the re-proof in the arithmetic), "Exact" (InapplicableOption
        with numerical arithmetic), "Numerical" (the covariance and Gram identities on N[] at WorkingPrecision) or None
        (re-proof skipped, those checks read "NotChecked"; the input validation and the rank still run); common GAP
        job options.
    Returns: <|"Rep" -> block representation, "Blocks" (CharacterID, Copy, Indices, Target), "Multiplicities",
        "Embedding" -> U, "BasisChange" -> Inverse[U], "InverseBasisChange" -> U, "Arithmetic", "Validation" (with
        "VerificationStatus": the weakest of the re-proof level, the group and the target variants)|>
        with r's matrices M_i . U == U . block_i for every generator.
    Effects: May certify a live group's presentation or compute missing targets on it (new generations). On a
        live group the result and the input's invariant form are cached (CacheKinds "Decompositions" and
        "DerivedIntermediates"; the key includes every irrep's active variant).
    Failures: UnverifiedContext, InvalidRep, GeneratorBindingMismatch, NumericalInput, PresentationUnavailable,
        InvalidRepresentation (not a homomorphism, or not a character), AmbiguousMultiplicity, MissingTargets,
        WrongCharacter, NonUnitaryRepresentation, UnprovedIdentity, PrecisionFailure, NativeUnavailable and
        InapplicableMethod (an explicit native method without a live group or cyclotomic data),
        InapplicableOption (a native IsomorphismMethod with Method -> "GeneratorEquations" or numerical
        arithmetic), TimeLimit.
    Example: DecomposeRepresentation[g, r]["Multiplicities"] lists the constituents of r.
    Remarks: The input is first validated (relators of a complete presentation; multiplicities by character
        inner products, exact nonnegative integers or numerically resolved). With Basis -> "Unitary" U satisfies
        U^dagger H U = I for the input's invariant form H (U itself is unitary when r is), so a general input
        is decomposed into unitary blocks in the unitarized coordinates, and U maps back to r's coordinates.
        The block matrices are the stored or supplied target matrices, unchanged. A native method only
        supplies intertwiner bases (verified in GAP); normalization and the exact proofs are the same as
        for GeneratorEquations. Native methods skip immediately when the input has no GAP mapping
        (non-cyclotomic or numerical data, or a context without a live group). Numerical results record
        residuals and are never exact.
    See also: generatorDecomposition; decompositionTargets; ValidateRepresentation.
*)
DecomposeRepresentation[context : (_Group | _RepresentationContext), rep_Rep, options : OptionsPattern[]] := cgFieldCatch[decomposeRepresentationFieldWork[context, rep, options]];
decomposeRepresentationFieldWork[context : (_Group | _RepresentationContext), rep_Rep, options : OptionsPattern[]] := Module[
    {effective, operand, settings, validation, targets, result, deadline, cacheKey, formKey, knownForm, allowed},
    effective = resolveOperationOptions[DecomposeRepresentation, "DecomposeRepresentation", {options}];
    If[FailureQ[effective], Return[effective]];
    allowed = resultLevelQ[effective[Verification], effective[Arithmetic]]; If[FailureQ[allowed], Return[allowed]];
    effective = resolveIrrepOptions[context, effective]; If[FailureQ[effective], Return[effective]];
    If[(effective[Method] === "GeneratorEquations" || effective[Arithmetic] === "Numerical") &&
        !MemberQ[{Automatic, "GeneratorEquations"}, effective[IsomorphismMethod]],
        Return[makeFailure["InapplicableOption", "Native alignment methods apply only to native decomposition methods.",
            <|"Method" -> effective[Method], "IsomorphismMethod" -> effective[IsomorphismMethod]|>]]];
    If[MemberQ[$NativeDecompositionMethods, effective[Method]] && effective[Arithmetic] === "Numerical",
        Return[makeFailure["InapplicableOption", "Native decomposition methods need exact arithmetic."]]];
    operand = representationOperand[context, rep]; If[FailureQ[operand], Return[operand]];
    settings = arithmeticSettings[effective[Arithmetic], effective[WorkingPrecision], effective[Tolerance],
        operand["Shape"]["Precision"]];
    If[FailureQ[settings], Return[settings]];
    (* the invariant-form method travels in the settings, so the derived cache keys below include it *)
    settings = Join[settings, <|"FormMethod" -> effective[UnitarizationMethod], "FieldMethod" -> effective[FieldMethod],
        (* the re-proof level (2C.4) is part of the settings, so cached decompositions are kept per level *)
        "Verification" -> effective[Verification], "CheckPrecision" -> effective[WorkingPrecision]|>];
    deadline = AbsoluteTime[] + effective[AttemptTimeLimit];
    (* On a live group decompositions and the input's invariant form are derived cache entries; the key
       includes the active variant of every irrep, so a changed target is never reused. *)
    cacheKey = If[MatchQ[context, _Group], {"Decompose", Hash[rep, "SHA256"], settings,
        KeyTake[effective, {Basis, Method, IsomorphismMethod, TargetRepresentations}],
        Map[Lookup[#, "ActiveVariant", None] &, operand["Snapshot"]["Representations"]]}, None];
    formKey = {"InvariantForm", Hash[rep, "SHA256"], settings};
    If[cacheKey =!= None, result = representationCacheLookup[context, "Decompositions", cacheKey];
        If[!MissingQ[result], Return[result]]];
    knownForm = If[cacheKey === None, None, Replace[representationCacheLookup[context, "DerivedIntermediates", formKey], _Missing -> None]];
    result = TimeConstrained[Catch[
        validation = validateRepBinding[context, rep, <|"Settings" -> settings, "Options" -> effective|>];
        If[FailureQ[validation], Throw[validation]];
        If[!validation["Homomorphism"],
            Throw[makeFailure["InvalidRepresentation", "The matrices do not satisfy the group's relators.", <|"Validation" -> validation|>]]];
        targets = decompositionTargets[context, operand["Snapshot"], validation["Multiplicities"], effective, settings];
        If[FailureQ[targets], Throw[targets]];
        With[{decomposition = Module[{methods, attempt, attempts = {}},
                methods = Which[effective[Method] =!= Automatic, {effective[Method]},
                    settings["Arithmetic"] === "Exact", Append[$NativeDecompositionMethods, "GeneratorEquations"],
                    True, {"GeneratorEquations"}];
                Catch[
                    Do[
                        If[MemberQ[Lookup[attempts, "Method", {}], method], Continue[]];
                        attempt = If[method === "GeneratorEquations",
                            generatorDecomposition[operand, targets, validation["Multiplicities"], effective[Basis], settings, deadline, None, knownForm],
                            With[{solutions = nativeDecompositionSolutions[context, operand, targets, validation["Multiplicities"], method, effective]},
                                If[FailureQ[solutions], solutions,
                                    generatorDecomposition[operand, targets, validation["Multiplicities"], effective[Basis], settings, deadline, solutions, knownForm]]]];
                        AppendTo[attempts, <|"Method" -> method, "Outcome" -> If[FailureQ[attempt], attempt[[1]], "Verified"]|>];
                        If[!FailureQ[attempt], Throw[Join[attempt, <|"Method" -> method, "Attempts" -> attempts|>]]];
                        (* Without a GAP mapping, every native method is skipped at once. *)
                        If[effective[Method] === Automatic && MemberQ[{"NativeUnavailable", "InapplicableMethod"}, attempt[[1]]],
                            attempts = Join[attempts, <|"Method" -> #, "Outcome" -> "Skipped"|> & /@
                                Complement[$NativeDecompositionMethods, Lookup[attempts, "Method"]]]];
                        If[effective[Method] =!= Automatic, Throw[attempt]],
                        {method, methods}];
                    makeFailure["DecompositionFailed", "No selected decomposition method produced a verified embedding.",
                        <|"Attempts" -> attempts|>]]]},
            If[FailureQ[decomposition], Throw[decomposition]];
            Join[<|"Rep" -> If[decomposition["BlockMatrices"] === {}, Rep[{}, operand["Shape"]["Dimension"]], Rep[decomposition["BlockMatrices"]]],
                "InvariantForm" -> Lookup[decomposition, "InvariantForm", Missing["General"]],
                "Blocks" -> decomposition["Blocks"], "Multiplicities" -> validation["Multiplicities"],
                "Embedding" -> decomposition["Embedding"], "BasisChange" -> decomposition["InverseEmbedding"],
                "InverseBasisChange" -> decomposition["Embedding"], "Arithmetic" -> settings["Arithmetic"],
                "Validation" -> Join[<|"Status" -> settings["Arithmetic"], "Method" -> decomposition["Method"],
                    "UnitarizationMethod" -> If[effective[Basis] === "General", Missing["General"], effective[UnitarizationMethod]],
                    "Domain" -> Lookup[decomposition, "Domain", Missing["NotRecorded"]],
                    "Attempts" -> decomposition["Attempts"], "Homomorphism" -> True,
                    (* weakest of the re-proof level, the group and the target variants (methodOptionsPlan.md 2C.2) *)
                    "VerificationStatus" -> cgWeakestStatus[Join[{resultLevelStatus[effective[Verification], settings["Arithmetic"]],
                        groupVerificationStatus[operand["Snapshot"]]}, variantVerificationStatus[cgVariant[operand["Snapshot"], #]] & /@
                            Select[Keys[Select[validation["Multiplicities"], TrueQ[# > 0] &]], StringQ]]]|>,
                    decomposition["Validation"],
                    If[settings["Arithmetic"] === "Exact", <||>, <|"Precision" -> settings["Precision"], "Tolerance" -> settings["Tolerance"]|>]]|>,
                If[settings["Arithmetic"] =!= "Exact" && operand["Shape"]["Arithmetic"] === "Exact",
                    <|"ExactReference" -> repIdentity[rep, operand["Names"]]|>, <||>]]]],
        effective[AttemptTimeLimit],
        makeFailure["TimeLimit", "The decomposition did not finish within AttemptTimeLimit."]];
    If[cacheKey =!= None && !FailureQ[result],
        representationCacheStore[context, "Decompositions", <|cacheKey -> KeyDrop[result, "InvariantForm"]|>];
        If[!MissingQ[result["InvariantForm"]], representationCacheStore[context, "DerivedIntermediates", <|formKey -> result["InvariantForm"]|>]]];
    If[FailureQ[result], result, KeyDrop[result, "InvariantForm"]]
];
DecomposeRepresentation[___] := makeFailure["InvalidInput", "DecomposeRepresentation expects a Group or RepresentationContext, a Rep and options."];

True
