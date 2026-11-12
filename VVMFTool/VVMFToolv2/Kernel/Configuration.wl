(*
    :Title: Package configuration and operation options
    :Context: VVMFTool`Private`
    :Summary: Validate configuration and resolve effective operation settings.
    :Responsibilities: Atomic defaults; explicit option precedence; executable discovery.
    :Dependencies: Diagnostics.wl; GroupWords.wl; ProcessIO.wl; at call time RepresentationJobs.wl
        ($RepresentationMethods) for representation option domains.
    :See Also: VVMFArch/step1Plan.md; GAP/Probe.g.
*)

(* Configuration is session-owned and survives package reload. Paths are not created
   here. Automatic resources are resolved per request, leaving stored defaults readable. *)
If[!AssociationQ[$Configuration],
    $Configuration = <|
        GAPExecutable -> Automatic,
        CacheDirectory -> FileNameJoin[{$UserBaseDirectory, "ApplicationData", "VVMFTool", "GAPCache"}],
        StoreGAPState -> True, AttemptTimeLimit -> 600,
        CoreBudget -> Automatic, MemoryBudget -> Automatic, ProgressFunction -> Automatic, Notices -> True,
        FieldMethod -> Automatic, Verification -> Automatic, Defaults -> <||>
    |>
];
(* Notices: one-line notes such as "a group with this GAP ID already exists" (uxUpdatePlan.md 2.3, P6). *)
If[!KeyExistsQ[$Configuration, Notices], $Configuration[Notices] = True];
(* FieldMethod and Verification: session defaults of the CG family (methodOptionsPlan.md 1.2); reload-safe *)
If[!KeyExistsQ[$Configuration, FieldMethod], $Configuration[FieldMethod] = Automatic];
If[!KeyExistsQ[$Configuration, Verification], $Configuration[Verification] = Automatic];
(* Defaults: family and operation session defaults (methodOptionsPlan.md 2D); reload-safe *)
If[!KeyExistsQ[$Configuration, Defaults], $Configuration[Defaults] = <||>];

(* The option families of 2D. An operation belongs to at most one family; the Validate functions are the checks
   themselves and belong to none (as ValidateCG in Phase 1). The CG family's FieldMethod and Verification are the flat
   Phase 1 keys (ConfigureVVMFTool[FieldMethod -> ...]) with their Phase 1 reach: FieldMethod the whole CG family,
   Verification CGCoefficients and CacheCG only (R2-1: the functions built on CG coefficients default to plain
   Automatic). *)
$OptionFamilies = <|
    "CG" -> {"CGCoefficients", "CacheCG", "Contractions", "ModularTensorProductVectors", "ModularContractions"},
    "Representations" -> {"ComputeGroupRepresentations", "SetGroupRepresentation", "ChangeGroupRepBasis", "TransformGroupRepresentations",
        "UnitarizeRepresentation", "DiagonalizeRepresentationT", "DecomposeRepresentation", "RepresentationTSpectrum",
        "RepresentationCharacter", "RepresentationElementMatrices"},
    "Models" -> {"CreateModel", "AddModelTerm", "CoupleContractions", "CoupleExpressions", "ExtractBilinearMatrix",
        "ExtractQuadraticMatrix", "ImportModelData", "SaveModelData"},
    "Modular" -> {"CreateModularModel", "ConstructModularForms", "SolveModularCoefficients", "BindModularForms",
        "AddModularFormCouplings", "SupplyModularFormSpace", "ModularFormCandidates", "ImportModularFormData",
        "EvaluateModularModel", "EvaluateModularMassMatrix", "ModularFormEvaluate"}|>;
(* Options with a per-operation meaning, and options that carry a call's data (names, targets, values, files, couplings):
   never a family default (settable per call or as an operation key). *)
$FamilyExcludedOptions = {Method, Normalization, Basis, MethodData, Arithmetic, WorkingPrecision, TargetIrreps, SeriesOrder,
    Name, Overwrite, ReplaceBindings, Recompute, Couplings, CouplingPrefix, FieldValues, FieldWeights, FormCouplings,
    FormSelection, MassMatrices, ParameterSymbols, ParameterValues, TargetIrrep, TargetRepresentations, ValidationGroup,
    NormalizationRules, SuperpotentialWeight, ExchangeSymmetry, ReversePairs, ApplyCoefficients};
(* Values an operation refuses inside the function although its domain admits them (a family value must suit every member;
   an operation key must suit its operation): the checks' None (checkLevelQ; ValidateModularForm also "Exact"), the
   operations that are their own proof (proofComputationLevelQ). *)
$FamilyRefusedValues = <|{"ConstructModularForms", Verification} -> {"Exact"}, {"SolveModularCoefficients", Verification} -> {"Exact"},
    {"BindModularForms", Verification} -> {"Exact"},
    {"ValidateRepresentation", Verification} -> {None}, {"ValidateModel", Verification} -> {None},
    {"ValidateMassMatrix", Verification} -> {None}, {"ValidateModularForm", Verification} -> {None, "Exact"},
    {"ValidateCG", Verification} -> {None}, {"ValidateGroup", Verification} -> {None},
    {"GroupSubgroups", Verification} -> {"Numerical"}, {"NormalSubgroupsByIndex", Verification} -> {"Numerical"},
    {"GroupElementWords", Verification} -> {"Numerical"}, {"CheckGeneratorMap", Verification} -> {None, "Numerical"},
    {"AssignModularGenerators", Verification} -> {"Numerical"}, {"ValidateModularModel", Verification} -> {None}|>;

(* Per-operation option domains. Configuration supplies only matching shared keys;
   stored defaults are never copied into another long-lived mutable defaults table. *)
$CommonJobDefaults = <|StoreGAPState -> True, GroupModel -> Automatic,
    AttemptTimeLimit -> 600, CoreBudget -> Automatic, MemoryBudget -> Automatic,
    ProgressFunction -> Automatic|>;
$BuilderDefaults = Join[$CommonJobDefaults, <|WordRecovery -> Automatic, UnitarizationMethod -> Automatic, WitnessVariant -> Automatic,
    (* the level of the build's checks (methodOptionsPlan.md 2C.4, 2C.6; user decision U2) *)
    Verification -> Automatic,
    ComputeRepresentations -> True,
    ComputeElements -> False, ComputeSubgroups -> False, SubgroupDescriptions -> False,
    CharacterMethod -> Automatic, Name -> Automatic, SubgroupKind -> "ConjugacyClasses",
    Basis -> "Unitary", RepresentationMethod -> Automatic, MethodData -> Automatic,
    TPhaseOrder -> "Ascending", PhaseConvention -> None|>];
$DisplayPresentationDefaults = <|ScalarNotation -> "Standard", NotationStyle -> "Standard", OneByOneMatrix -> "Scalar",
    DefineOmega -> True, Digits -> Automatic, Caption -> Automatic, Label -> None, PageSize -> 20|>;
$CGDefaults = <|Method -> Automatic, Normalization -> Automatic, ExchangeSymmetry -> Automatic, Arithmetic -> "Exact",
    WorkingPrecision -> 50, Tolerance -> Automatic, Prefilter -> True, NumberField -> Automatic, MethodData -> Automatic,
    ComputeMissingRepresentations -> True, FieldMethod -> Automatic, UnitarizationMethod -> Automatic|>;
$OperationDefaults = <|
    "Configuration" -> $Configuration,
    "BuildGroup" -> $BuilderDefaults,
    "BuildModularGroup" -> $BuilderDefaults,
    "BuildGroupFromGAP" -> Join[$BuilderDefaults,
        <|GeneratorNames -> Automatic, ConstructionDependencies -> {}|>],
    (* WordRecovery only where a planner has recovery tiers (characters and group enrichments; 2B.6) *)
    "GroupElementWords" -> Join[$CommonJobDefaults, <|WordRecovery -> Automatic, Verification -> Automatic|>],
    "ValidateGroup" -> Join[$CommonJobDefaults, <|Verification -> Automatic|>],
    "GroupWordOrder" -> Join[$CommonJobDefaults, <|WordRecovery -> Automatic|>],
    "AssignModularGenerators" -> Join[$CommonJobDefaults, <|WordRecovery -> Automatic, Verification -> Automatic|>],
    "CheckGeneratorMap" -> Join[$CommonJobDefaults, <|WordRecovery -> Automatic, Verification -> Automatic|>],
    "RestoreGAPState" -> $CommonJobDefaults,
    "ImportGroupData" -> Join[$CommonJobDefaults, <|ValidationGroup -> Automatic, Verification -> Automatic|>],
    "GroupSubgroups" -> Join[$CommonJobDefaults, <|WordRecovery -> Automatic, Method -> Automatic,
        SubgroupKind -> "ConjugacyClasses", SubgroupOrder -> All, SubgroupIndex -> All,
        SubgroupDescriptions -> False, Verification -> Automatic|>],
    "NormalSubgroupsByIndex" -> Join[KeyDrop[$CommonJobDefaults, {StoreGAPState, GroupModel}],
        <|IndexMode -> "Exact", MaxResults -> All, SmallGenerators -> True, Verification -> Automatic|>],
    "CleanGAPCache" -> <|MaxBytes -> 10^9|>,
    "ComputeGroupRepresentations" -> Join[$CommonJobDefaults, <|UnitarizationMethod -> Automatic, WitnessVariant -> Automatic, Basis -> "Unitary",
        RepresentationMethod -> Automatic, MethodData -> Automatic, TPhaseOrder -> "Ascending", PhaseConvention -> None,
        Verification -> Automatic|>],
    "UnitaryRepresentationQ" -> <|Tolerance -> Automatic|>,
    "ChangeRepBasis" -> <||>,
    "UnitarizeRepresentation" -> <|FieldMethod -> Automatic, UnitarizationMethod -> Automatic, FormFactorizationMethod -> Automatic,
        Arithmetic -> "Exact", WorkingPrecision -> 50, Tolerance -> Automatic, AttemptTimeLimit -> 600, Verification -> Automatic|>,
    "DiagonalizeRepresentationT" -> <|FieldMethod -> Automatic, DiagonalizationMethod -> Automatic, Basis -> "Unitary",
        TPhaseOrder -> "Ascending", PhaseConvention -> None, Arithmetic -> "Exact", WorkingPrecision -> 50,
        Tolerance -> Automatic, AttemptTimeLimit -> 600, Verification -> Automatic|>,
    "RepresentationTSpectrum" -> <|FieldMethod -> Automatic, Arithmetic -> "Exact", WorkingPrecision -> 50, Tolerance -> Automatic|>,
    "RepresentationCharacter" -> <|FieldMethod -> Automatic, Arithmetic -> "Exact", WorkingPrecision -> 50, Tolerance -> Automatic|>,
    "ValidateRepresentation" -> Join[$CommonJobDefaults, <|FieldMethod -> Automatic, Arithmetic -> "Exact", WorkingPrecision -> 50, Tolerance -> Automatic,
        Verification -> Automatic|>],
    "DecomposeRepresentation" -> Join[$CommonJobDefaults, <|FieldMethod -> Automatic, UnitarizationMethod -> Automatic, Method -> Automatic, IsomorphismMethod -> Automatic,
        TargetRepresentations -> Automatic, Basis -> "Unitary", Arithmetic -> "Exact", WorkingPrecision -> 50, Tolerance -> Automatic,
        Verification -> Automatic|>],
    "ReorderGroupIrreps" -> <||>, "SortGroupIrreps" -> <||>,
    "RepresentationElementMatrices" -> Join[$CommonJobDefaults, <|FieldMethod -> Automatic|>],
    "CleanRepresentationCache" -> <|CacheKinds -> All|>,
    "SetGroupRepresentation" -> Join[$CommonJobDefaults, <|Basis -> "Unitary", FieldMethod -> Automatic, Verification -> Automatic, WorkingPrecision -> 50|>],
    "ChangeGroupRepBasis" -> Join[$CommonJobDefaults, <|Basis -> "Unitary", FieldMethod -> Automatic, Verification -> Automatic, WorkingPrecision -> 50|>],
    "TransformGroupRepresentations" -> Join[$CommonJobDefaults, <|FieldMethod -> Automatic, Route -> Automatic, WorkingPrecision -> 50, Tolerance -> Automatic,
        WitnessVariant -> Automatic, Basis -> "Unitary", UnitarizationMethod -> Automatic,
        FormFactorizationMethod -> Automatic, DiagonalizationMethod -> Automatic, TPhaseOrder -> "Ascending",
        PhaseConvention -> None, Arithmetic -> "Exact", Verification -> Automatic|>],
    (* Stage 3 displays: view producers save presentation defaults; renderers take Automatic as "the view's". *)
    "GroupSummary" -> Join[<|Basis -> Automatic, ShowIDs -> False, ShowStatus -> Automatic|>, $DisplayPresentationDefaults],
    "CharacterTableView" -> Join[<|RowOrder -> Automatic, ClassOrder -> Automatic, LabelStyle -> Automatic, IrrepLabels -> <||>,
        DisplayTimeLimit -> 5, ShowIDs -> False, ShowAutomaticLabels -> True|>, $DisplayPresentationDefaults],
    "RepresentationTable" -> Join[<|MatrixSet -> Automatic, LabelStyle -> Automatic, IrrepLabels -> <||>, Basis -> Automatic,
        DisplayTimeLimit -> 5, ShowIDs -> False, ShowStatus -> Automatic, ShowAutomaticLabels -> True|>, $DisplayPresentationDefaults],
    "RepresentationView" -> Join[<|MatrixSet -> Automatic, LabelStyle -> Automatic, DisplayTimeLimit -> 5, ShowStatus -> Automatic|>, $DisplayPresentationDefaults],
    "RepresentationLabelData" -> <|LabelStyle -> Automatic, DisplayTimeLimit -> 5|>,
    "ScalarLaTeX" -> <|ScalarNotation -> "Standard", NotationStyle -> "Standard", Digits -> Automatic|>,
    "MatrixLaTeX" -> <|ScalarNotation -> "Standard", NotationStyle -> "Standard", Digits -> Automatic, OneByOneMatrix -> "Scalar"|>,
    "LaTeXPreamble" -> <|NotationStyle -> "Standard"|>,
    "ToLaTeX" -> <|ScalarNotation -> Automatic, NotationStyle -> Automatic, OneByOneMatrix -> Automatic, DefineOmega -> Automatic,
        Digits -> Automatic, Caption -> Automatic, Label -> Automatic, Standalone -> False|>,
    "ToNotebook" -> <|ScalarNotation -> Automatic, NotationStyle -> Automatic, OneByOneMatrix -> Automatic, DefineOmega -> Automatic,
        Digits -> Automatic, Caption -> Automatic, PageSize -> Automatic|>,
    "ExportDisplay" -> <|ScalarNotation -> Automatic, NotationStyle -> Automatic, OneByOneMatrix -> Automatic, DefineOmega -> Automatic,
        Digits -> Automatic, Caption -> Automatic, Label -> Automatic, PageSize -> Automatic, Standalone -> False, Overwrite -> False|>,
    (* Stage 4 tensor products and CG coefficients. *)
    "TensorDecompositionView" -> Join[<|LabelStyle -> Automatic, IrrepLabels -> <||>, DisplayTimeLimit -> 5|>, $DisplayPresentationDefaults],
    (* Stage 5 models. *)
    "CreateModel" -> <|Name -> "Model", TargetIrrep -> Automatic, Arithmetic -> "Exact", WorkingPrecision -> 50, Tolerance -> Automatic|>,
    (* Stage 5 operations with options (review M6): unknown options and invalid values fail. *)
    "Contractions" -> Join[KeyDrop[$CommonJobDefaults, GroupModel], $CGDefaults, <|Verification -> Automatic|>],
    "CoupleContractions" -> <|ChannelPolicy -> "Independent", Couplings -> Automatic, CouplingPrefix -> "c", ParameterSymbols -> {}|>,
    "CoupleExpressions" -> <|Couplings -> Automatic, CouplingPrefix -> "c", ParameterSymbols -> {}, Arithmetic -> "Exact", WorkingPrecision -> 50,
        Tolerance -> Automatic|>,
    "ExtractBilinearMatrix" -> <|RequirePure -> False, Arithmetic -> "Exact", WorkingPrecision -> 50, Tolerance -> Automatic|>,
    "ExtractQuadraticMatrix" -> <|QuadraticConvention -> "Polynomial", RequirePure -> False, Arithmetic -> "Exact", WorkingPrecision -> 50,
        Tolerance -> Automatic|>,
    "CGCoefficients" -> Join[KeyDrop[$CommonJobDefaults, GroupModel], $CGDefaults, <|Verification -> Automatic, Recompute -> False|>],
    "CacheCG" -> Join[KeyDrop[$CommonJobDefaults, GroupModel], $CGDefaults, <|TargetIrreps -> All, Verification -> Automatic,
        ReversePairs -> "Flip"|>],
    (* CGCoefficients, CacheCG and ValidateCG take Verification (Phase 1); the derived CG functions too (2C.4) *)
    "ValidateCG" -> <|FieldMethod -> Automatic, Verification -> Automatic, WorkingPrecision -> 50|>,
    (* Stage 6 model output: prepared outputs, Python modules. *)
    "PrepareModelOutput" -> <|ParameterValues -> <||>|>,
    "ToPython" -> <|PythonBackend -> "NumPy", WorkingPrecision -> Automatic, FunctionNames -> <||>, ParameterNames -> <||>, CommonSubexpressions -> True,
        FormEvaluation -> "Embedded", ExportEvaluationMethod -> Automatic, SeriesOrder -> Automatic, AccuracyGoal -> Automatic, PrecisionGoal -> Automatic,
        MaxSeriesOrder -> 2000, TimeLimit -> 600, RequireProof -> False|>,
    "ExportPython" -> <|Overwrite -> False|>,
    "SaveModelData" -> <|MassMatrices -> <||>, Overwrite -> False|>,
    "ImportModelData" -> Join[$CommonJobDefaults, <|ValidationGroup -> Automatic, Verification -> Automatic|>],
    "ModelView" -> Join[<|FieldLabels -> <||>, CouplingLabels -> <||>, IrrepLabels -> <||>, FormSlotLabels -> <||>, DisplayTimeLimit -> 5|>, $DisplayPresentationDefaults],
    "FieldTable" -> Join[<|FieldLabels -> <||>, CouplingLabels -> <||>, IrrepLabels -> <||>, FormSlotLabels -> <||>, DisplayTimeLimit -> 5|>, $DisplayPresentationDefaults],
    "ContractionTable" -> Join[<|FieldLabels -> <||>, CouplingLabels -> <||>, IrrepLabels -> <||>, FormSlotLabels -> <||>, DisplayTimeLimit -> 5|>, $DisplayPresentationDefaults],
    "CouplingTable" -> Join[<|FieldLabels -> <||>, CouplingLabels -> <||>, IrrepLabels -> <||>, FormSlotLabels -> <||>, DisplayTimeLimit -> 5|>, $DisplayPresentationDefaults],
    "MassMatrixView" -> Join[<|FieldLabels -> <||>, CouplingLabels -> <||>, IrrepLabels -> <||>, FormSlotLabels -> <||>, DisplayTimeLimit -> 5|>, $DisplayPresentationDefaults],
    "ModelOutputView" -> Join[<|FieldLabels -> <||>, CouplingLabels -> <||>, IrrepLabels -> <||>, FormSlotLabels -> <||>, DisplayTimeLimit -> 5|>, $DisplayPresentationDefaults],
    (* Stage 9 modular outputs and displays. *)
    "PrepareModularFormOutput" -> <||>,
    "SaveModularFormData" -> <|Overwrite -> False|>,
    "ImportModularFormData" -> Join[$CommonJobDefaults, <|ValidationGroup -> Automatic|>],
    "ModularFormView" -> Join[<|FormLabels -> <||>, IrrepLabels -> <||>, ExpressionMode -> "Normalized", MaxQTerms -> 6, FactorQSeries -> True, DisplayTimeLimit -> 5|>,
        $DisplayPresentationDefaults],
    "ModularFormTable" -> Join[<|FormLabels -> <||>, IrrepLabels -> <||>, ExpressionMode -> "Normalized", MaxQTerms -> 6, FactorQSeries -> True, DisplayTimeLimit -> 5,
        IncludeWeight -> True|>, $DisplayPresentationDefaults],
    "QExpansionView" -> Join[<|MaxQTerms -> 6, FactorQSeries -> True|>, $DisplayPresentationDefaults],
    "ModularDimensionView" -> Join[<|IrrepLabels -> <||>|>, $DisplayPresentationDefaults],
    "FormSlotTable" -> Join[<|FormSlotLabels -> <||>, IrrepLabels -> <||>, DisplayTimeLimit -> 5|>, $DisplayPresentationDefaults],
    (* Stage 7 modular forms. *)
    "CreateModularForm" -> <|Normalization -> Automatic|>,
    "ModularFormExpression" -> <|ApplyCoefficients -> True|>,
    "ModularFormValue" -> <|ApplyCoefficients -> True|>,
    "ScalarModularExpression" -> <|Coordinate -> "q"|>,
    "HypergeometricK" -> <|Coordinate -> "q"|>,
    "ScalarQSeries" -> <|Coordinate -> "q"|>,
    "ModularDerivativeExpression" -> <|Coordinate -> "q"|>,
    "ModularDimension" -> <|Method -> Automatic, DimensionCache -> True|>,
    "ModularDimensionTable" -> <|Method -> Automatic, DimensionCache -> True, Weights -> Range[0, 20], IrrepForm -> "Index", IrrepLabels -> <||>|>,
    "ModularWeightProfile" -> <||>,
    "MinimumModularWeight" -> <|WeightSearchLimit -> 20, DimensionCache -> True, DimensionMethod -> Automatic|>,
    "ConstructModularForms" -> <|Method -> Automatic, SeriesOrder -> Automatic, DiagonalizationMethod -> Automatic, Verification -> Automatic|>,
    "SolveModularCoefficients" -> <|Method -> Automatic, WorkingPrecision -> 80, AccuracyGoal -> Automatic, SeriesOrder -> Automatic,
        NormalizationRules -> Automatic, RequireProof -> False, Normalization -> Automatic, TimeLimit -> 600, Verification -> Automatic|>,
    "ModularFormQExp" -> <|ApplyCoefficients -> True|>,
    "ModularFormEvaluate" -> <|Method -> Automatic, WorkingPrecision -> 80, AccuracyGoal -> Automatic, PrecisionGoal -> Automatic, SeriesOrder -> Automatic,
        MaxSeriesOrder -> 2000, TimeLimit -> 600, ApplyCoefficients -> True|>,
    "EvaluateScalarModular" -> <|Method -> Automatic, WorkingPrecision -> 80, AccuracyGoal -> Automatic, PrecisionGoal -> Automatic, SeriesOrder -> Automatic,
        MaxSeriesOrder -> 2000, TimeLimit -> 600, ApplyCoefficients -> True, Coordinate -> "q"|>,
    "ValidateModularForm" -> <|RequireProof -> False, WorkingPrecision -> 40, SeriesOrder -> Automatic, Verification -> Automatic|>,
    (* Stage 8 modular models. *)
    "CreateModularModel" -> <|FieldWeights -> Automatic, SuperpotentialWeight -> 0, Name -> "Model", TargetIrrep -> Automatic, Arithmetic -> "Exact",
        WorkingPrecision -> 50, Tolerance -> Automatic|>,
    "ModularFormCandidates" -> <|TargetIrreps -> Automatic, DimensionCache -> True, DimensionMethod -> Automatic|>,
    "ModularTensorProductVectors" -> Join[KeyDrop[$CommonJobDefaults, GroupModel], $CGDefaults, <|Verification -> Automatic, TargetIrreps -> Automatic, FormSelection -> All, DimensionCache -> True, DimensionMethod -> Automatic|>],
    "ModularContractions" -> Join[KeyDrop[$CommonJobDefaults, GroupModel], $CGDefaults, <|Verification -> Automatic, FormSelection -> All, DimensionCache -> True, DimensionMethod -> Automatic|>],
    "AddModularFormCouplings" -> <|FormCouplings -> Automatic, CouplingPrefix -> "a", ParameterSymbols -> {}, Verification -> Automatic|>,
    "AddModelTerm" -> <|Verification -> Automatic|>,
    "BindModularForms" -> <|ReplaceBindings -> False, RequireProof -> False, WorkingPrecision -> 40, SeriesOrder -> Automatic, TimeLimit -> 600,
        Verification -> Automatic|>,
    "SupplyModularFormSpace" -> <|WorkingPrecision -> 40, SeriesOrder -> Automatic, TimeLimit -> 600|>,
    "SetIrrepLabels" -> <|AllowDuplicates -> False|>,
    "LoadGroup" -> <|Fresh -> False, Verification -> Automatic|>,
    "TensorDecomposition" -> <|IrrepForm -> "Index", IncludeZeros -> False|>,
    "TensorIrrepList" -> <|IrrepForm -> "Index"|>,
    "CGCacheInformation" -> <|IrrepForm -> "ID"|>,
    "ValidateModularModel" -> <|RequireBindings -> False, RequireProof -> False, Verification -> Automatic|>,
    (* the checks themselves take the level of their checks (methodOptionsPlan.md 2C.4) *)
    "ValidateModel" -> <|Verification -> Automatic|>,
    "ValidateMassMatrix" -> <|Verification -> Automatic|>,
    "EvaluateModularModel" -> <|ParameterValues -> <||>, FieldValues -> <||>, WorkingPrecision -> 50, AccuracyGoal -> Automatic, PrecisionGoal -> Automatic,
        SeriesOrder -> Automatic, MaxSeriesOrder -> 2000, TimeLimit -> 600|>,
    "EvaluateModularMassMatrix" -> <|ParameterValues -> <||>, FieldValues -> <||>, WorkingPrecision -> 50, AccuracyGoal -> Automatic, PrecisionGoal -> Automatic,
        SeriesOrder -> Automatic, MaxSeriesOrder -> 2000, TimeLimit -> 600|>
|>;

(*
    Summary: Check a path's absolute, nonempty form without creating or reading its target.
    Parameters: path — arbitrary value.
    Options/defaults: None.
    Returns: True for an absolute path on the current platform, otherwise False.
    Effects: Pure.
    Failures: Relative, empty and nonstring input return False.
    Example: absolutePathQ[FileNameJoin[{$TemporaryDirectory, "cache"}]] returns True.
    See also: optionValueQ; ExpandFileName.
*)
absolutePathQ[path_] := StringQ[path] && StringLength[path] > 0 &&
    ExpandFileName[path] === path;

(* Operation-specific value domains take precedence over the shared domains below, so one
   option symbol (for example Method) can mean different method families per operation. *)
$OperationOptionDomains = <|
    "CreateModularForm" -> <|Normalization -> Function[value, value === Automatic || AssociationQ[value]]|>,
    "ModularDimension" -> <|Method -> Function[value, MemberQ[{Automatic, "Profile", "TraceFormula"}, value]]|>,
    "ModularDimensionTable" -> <|Method -> Function[value, MemberQ[{Automatic, "Profile", "TraceFormula"}, value]],
        Weights -> Function[value, ListQ[value] && value =!= {} && AllTrue[value, modularWeightQ] && DuplicateFreeQ[value]]|>,
    "ConstructModularForms" -> <|Method -> Function[value, value === Automatic || StringQ[value]],
        (* the frame must be exact (2B.8) *)
        DiagonalizationMethod -> Function[value, MemberQ[{Automatic, "Exact", "NumericalReconstruction"}, value]]|>,
    "ModularFormEvaluate" -> <|Method -> Function[value, MemberQ[{Automatic, "QSeries", "Analytic"}, value]], WorkingPrecision -> Function[value, IntegerQ[value] && value >= 16]|>,
    "EvaluateScalarModular" -> <|Method -> Function[value, MemberQ[{Automatic, "QSeries", "Analytic"}, value]], WorkingPrecision -> Function[value, IntegerQ[value] && value >= 16]|>,
    "ValidateModularForm" -> <|WorkingPrecision -> Function[value, IntegerQ[value] && value >= 16]|>,
    "BindModularForms" -> <|WorkingPrecision -> Function[value, IntegerQ[value] && value >= 16]|>,
    "SupplyModularFormSpace" -> <|WorkingPrecision -> Function[value, IntegerQ[value] && value >= 16]|>,
    "EvaluateModularModel" -> <|WorkingPrecision -> Function[value, IntegerQ[value] && value >= 16]|>,
    "EvaluateModularMassMatrix" -> <|WorkingPrecision -> Function[value, IntegerQ[value] && value >= 16]|>,
    "ModularFormCandidates" -> <|TargetIrreps -> Function[value, value === Automatic || value === All || StringQ[value] || (ListQ[value] && AllTrue[value, StringQ] && DuplicateFreeQ[value])]|>,
    "SolveModularCoefficients" -> <|Method -> Function[value, MemberQ[{Automatic, "Exact", "NumericalFit", "Reconstruct"}, value]],
        Normalization -> Function[value, value === Automatic || AssociationQ[value]], WorkingPrecision -> Function[value, IntegerQ[value] && value >= 16]|>,
    "GroupSubgroups" -> <|Method -> Function[value,
        MemberQ[{Automatic, "GAP", "ClassExpansion", "ClassFilter"}, value]]|>,
    "ComputeGroupRepresentations" -> <|
        Basis -> Function[value, MemberQ[{"Unitary", "General", "UnitaryTDiagonal"}, value]],
        RepresentationMethod -> Function[value, value === Automatic || MemberQ[$RepresentationMethods, value]],
        MethodData -> methodDataValueQ|>,
    "DiagonalizeRepresentationT" -> <|Basis -> Function[value, MemberQ[{"Unitary", "General"}, value]]|>,
    "SetGroupRepresentation" -> <|Basis -> Function[value, MemberQ[{"Unitary", "General"}, value]]|>,
    "ChangeGroupRepBasis" -> <|Basis -> Function[value, MemberQ[{"Unitary", "General"}, value]]|>,
    "TransformGroupRepresentations" -> <|Basis -> Function[value, MemberQ[{"Unitary", "UnitaryTDiagonal"}, value]]|>,
    "DecomposeRepresentation" -> <|Basis -> Function[value, MemberQ[{"Unitary", "General"}, value]],
        Method -> Function[value, MemberQ[{Automatic, "GeneratorEquations", "Serre", "Alternative", "Canonical",
            "REPSNConstituents", "REPSNBlocks"}, value]]|>
|>;
(* Stage 4: Method names a CG route; MethodData carries subgroup data for SubgroupEmbedding. *)
(* Phase 2 (2A.3): Method may be an ordered duplicate-free list of routes, tried one at a time in that order;
   (2A.6) MethodData may add "SubgroupSource" -> "Recorded" | "Any" (Any allows the cyclic/identity fallbacks). *)
cgMethodValueQ[value_] := value === Automatic || MemberQ[$CGMethodOrder, value] ||
    (ListQ[value] && value =!= {} && DuplicateFreeQ[value] && AllTrue[value, MemberQ[$CGMethodOrder, #] &]);
cgMethodDataValueQ[value_] := value === Automatic || (AssociationQ[value] &&
    SubsetQ[{"SubgroupGenerators", "SubgroupRecord", "SubgroupSource"}, Keys[value]] && value =!= <||> &&
    Count[Keys[value], "SubgroupGenerators" | "SubgroupRecord"] <= 1 &&
    (!KeyExistsQ[value, "SubgroupGenerators"] || (ListQ[value["SubgroupGenerators"]] && value["SubgroupGenerators"] =!= {} &&
        AllTrue[value["SubgroupGenerators"], MatchQ[#, _GroupWord] &])) &&
    (!KeyExistsQ[value, "SubgroupRecord"] || AssociationQ[value["SubgroupRecord"]]) &&
    (!KeyExistsQ[value, "SubgroupSource"] || MemberQ[{"Recorded", "Any"}, value["SubgroupSource"]]));
Do[$OperationOptionDomains[operation] = <|
        Method -> cgMethodValueQ,
        MethodData -> cgMethodDataValueQ,
        (* the temporary unitarization of transported spectral routes (methodOptionsPlan.md 2B.5): Wolfram form methods *)
        UnitarizationMethod -> Function[value, MemberQ[{Automatic, "GroupAverage", "GeneratorEquations"}, value]]|>,
    {operation, {"CGCoefficients", "CacheCG", "Contractions", "ModularTensorProductVectors", "ModularContractions"}}];
$OperationOptionDomains["ModularTensorProductVectors"] = Append[$OperationOptionDomains["ModularTensorProductVectors"],
    TargetIrreps -> $OperationOptionDomains["ModularFormCandidates"][TargetIrreps]];
(* Stage 6: WorkingPrecision of ToPython is Automatic, MachinePrecision (NumPy) or digits (mpmath); ToPython checks the backend. *)
$OperationOptionDomains["ToPython"] = <|WorkingPrecision -> Function[value, value === Automatic || value === MachinePrecision || (IntegerQ[value] && value >= 16)]|>;
(* Display: Basis Automatic reports actual properties; renderers accept Automatic ("the view's saved default"). *)
Do[$OperationOptionDomains[operation] = <|Basis -> Function[value, MemberQ[{Automatic, "General", "Unitary", "UnitaryTDiagonal"}, value]]|>,
    {operation, {"GroupSummary", "RepresentationTable"}}];
Do[$OperationOptionDomains[renderer] = Association[Map[Function[option, option -> With[{o = option},
        Function[value, value === Automatic || optionValueQ[o, value]]]],
    {ScalarNotation, NotationStyle, OneByOneMatrix, DefineOmega, Digits, Caption, Label, PageSize}]],
    {renderer, {"ToLaTeX", "ToNotebook", "ExportDisplay"}}];
(* GAP unitarizers only for computed representations (methodOptionsPlan.md 2B.1); GeneratorEquations is a Wolfram
   unitarizer (UnitarizeRepresentation, TransformGroupRepresentations). *)
$OperationOptionDomains["ComputeGroupRepresentations"] = Join[Lookup[$OperationOptionDomains, "ComputeGroupRepresentations", <||>],
    <|UnitarizationMethod -> Function[value, MemberQ[{Automatic, "BSGSAverage", "GroupAverage"}, value]]|>];
(* DecomposeRepresentation's invariant form for unitary coordinates (2B.3): the Wolfram form methods *)
$OperationOptionDomains["DecomposeRepresentation"] = Join[Lookup[$OperationOptionDomains, "DecomposeRepresentation", <||>],
    <|UnitarizationMethod -> Function[value, MemberQ[{Automatic, "GroupAverage", "GeneratorEquations"}, value]]|>];
(* Builders accept the representation options of ComputeGroupRepresentations (their representation stage). *)
Do[$OperationOptionDomains[builder] = $OperationOptionDomains["ComputeGroupRepresentations"],
    {builder, {"BuildGroup", "BuildModularGroup", "BuildGroupFromGAP"}}];

(* Cross-option applicability rules, each a function of the effective options returning True
   or a Failure. They run after every value is individually valid. *)
$OperationOptionRules = <|
    "ComputeGroupRepresentations" -> {methodDataApplicableQ, tPhaseOptionsApplicableQ, unitarizeOptionsApplicableQ,
        (* GAP's proof is the only exact route; a weak computation has no GAP unitarizer (C7) *)
        Function[effective, If[MemberQ[{"Numerical", None}, effective[Verification]] && effective[UnitarizationMethod] =!= Automatic,
            makeFailure["InapplicableOption", "UnitarizationMethod is GAP's unitarizer of proved variants; with Verification \"Numerical\" or None no GAP unitarization runs.",
                <|"Options" -> {Verification, UnitarizationMethod}|>], True]]},
    "BuildGroup" -> {builderRepresentationOptionsQ, methodDataApplicableQ, tPhaseOptionsApplicableQ, unitarizeOptionsApplicableQ},
    "BuildModularGroup" -> {builderRepresentationOptionsQ, methodDataApplicableQ, tPhaseOptionsApplicableQ, unitarizeOptionsApplicableQ},
    "BuildGroupFromGAP" -> {builderRepresentationOptionsQ, methodDataApplicableQ, tPhaseOptionsApplicableQ, unitarizeOptionsApplicableQ},
    "UnitarizeRepresentation" -> {arithmeticOptionsApplicableQ, fieldMethodApplicableQ, representationChoicesApplicableQ},
    "DiagonalizeRepresentationT" -> {arithmeticOptionsApplicableQ, fieldMethodApplicableQ, representationChoicesApplicableQ},
    "TransformGroupRepresentations" -> {tPhaseOptionsApplicableQ, arithmeticOptionsApplicableQ, fieldMethodApplicableQ, representationNumericalFieldQ,
        Function[effective, resultLevelQ[effective[Verification], effective[Arithmetic]]]},
    "RepresentationTSpectrum" -> {arithmeticOptionsApplicableQ, fieldMethodApplicableQ, representationChoicesApplicableQ},
    "RepresentationCharacter" -> {arithmeticOptionsApplicableQ, fieldMethodApplicableQ, representationChoicesApplicableQ},
    "ValidateRepresentation" -> {arithmeticOptionsApplicableQ, fieldMethodApplicableQ, representationChoicesApplicableQ},
    "DecomposeRepresentation" -> {arithmeticOptionsApplicableQ, fieldMethodApplicableQ, representationChoicesApplicableQ},
    "CGCoefficients" -> {arithmeticOptionsApplicableQ, cgMethodDataApplicableQ, fieldMethodApplicableQ, verificationApplicableQ},
    "CreateModel" -> {arithmeticOptionsApplicableQ},
    "CreateModularModel" -> {arithmeticOptionsApplicableQ},
    "Contractions" -> {cgMethodDataApplicableQ, fieldMethodApplicableQ, verificationApplicableQ},
    "ModularTensorProductVectors" -> {cgMethodDataApplicableQ, fieldMethodApplicableQ, verificationApplicableQ},
    "ModularContractions" -> {cgMethodDataApplicableQ, fieldMethodApplicableQ, verificationApplicableQ},
    "CoupleExpressions" -> {arithmeticOptionsApplicableQ},
    "ExtractBilinearMatrix" -> {arithmeticOptionsApplicableQ},
    "ExtractQuadraticMatrix" -> {arithmeticOptionsApplicableQ},
    "CacheCG" -> {arithmeticOptionsApplicableQ, cgMethodDataApplicableQ, fieldMethodApplicableQ, verificationApplicableQ},
    "GroupSubgroups" -> {Function[effective, With[{allowed = Switch[effective[SubgroupKind],
        "All", {Automatic, "GAP", "ClassExpansion"}, "Normal", {Automatic, "GAP", "ClassFilter"},
        _, {Automatic, "GAP"}]},
        If[MemberQ[allowed, effective[Method]], True,
            makeFailure["InapplicableMethod", "The method does not compute the requested subgroup kind."]]]]}
|>;
(* the session defaults (methodOptionsPlan.md 2D) *)
$OperationOptionRules["Configuration"] = {sessionDefaultsApplicableQ};

(*
    Summary: Check the shape of a representation MethodData value.
    Parameters: value — any expression.
    Options/defaults: None.
    Returns: True for Automatic or an association using only SubgroupGenerators (nonempty list of
        GroupWord), Representation (Rep), AtlasName (string), RepresentationNumber (positive integer) and
        RandomSeed (integer from 1 to 2^28 - 1, reseeding randomized constructions).
    Effects: Pure.
    Failures: Other keys, empty associations and wrongly typed values return False.
    Example: methodDataValueQ[<|"AtlasName" -> "A5"|>] is True.
    See also: methodDataApplicableQ; ComputeGroupRepresentations.
*)
methodDataValueQ[value_] := value === Automatic || (AssociationQ[value] && value =!= <||> &&
    SubsetQ[{"SubgroupGenerators", "Representation", "AtlasName", "RepresentationNumber", "RandomSeed"}, Keys[value]] &&
    (!KeyExistsQ[value, "SubgroupGenerators"] || (ListQ[value["SubgroupGenerators"]] &&
        value["SubgroupGenerators"] =!= {} && AllTrue[value["SubgroupGenerators"], MatchQ[#, _GroupWord] &])) &&
    (!KeyExistsQ[value, "Representation"] || MatchQ[value["Representation"], _Rep]) &&
    (!KeyExistsQ[value, "AtlasName"] || (StringQ[value["AtlasName"]] && StringLength[value["AtlasName"]] > 0)) &&
    (!KeyExistsQ[value, "RepresentationNumber"] || (IntegerQ[value["RepresentationNumber"]] && value["RepresentationNumber"] > 0)) &&
    (!KeyExistsQ[value, "RandomSeed"] || (IntegerQ[value["RandomSeed"]] && 1 <= value["RandomSeed"] < 2^28)));

(*
    Summary: Require MethodData keys to belong to the explicitly selected representation route.
    Parameters: effective — validated ComputeGroupRepresentations options.
    Options/defaults: None.
    Returns: True, or InapplicableOption Failure.
    Effects: Pure.
    Failures: MethodData without an explicit RepresentationMethod; subgroup keys for a route other than
        CharacterSubgroup/Induction/InducedUnitary/Extension/NormalExtension; a subgroup Representation
        without SubgroupGenerators or with CharacterSubgroup; Atlas keys for a route other than AtlasRep.
        RandomSeed may accompany any explicit route.
    Example: MethodData -> <|"AtlasName" -> "A5"|> with RepresentationMethod -> "Dixon" fails.
    See also: methodDataValueQ; step2Plan.md MethodData.
*)
methodDataApplicableQ[effective_Association] := Module[{data = effective[MethodData], method = effective[RepresentationMethod],
        subgroupKeys, atlasKeys, failure},
    failure[message_] := makeFailure["InapplicableOption", message, <|"RepresentationMethod" -> method|>];
    If[data === Automatic, Return[True]];
    If[method === Automatic, Return[failure["MethodData requires an explicit RepresentationMethod."]]];
    subgroupKeys = Intersection[Keys[data], {"SubgroupGenerators", "Representation"}];
    atlasKeys = Intersection[Keys[data], {"AtlasName", "RepresentationNumber"}];
    Which[
        subgroupKeys =!= {} && atlasKeys =!= {}, failure["MethodData mixes subgroup and Atlas data."],
        subgroupKeys =!= {} && !MemberQ[{"CharacterSubgroup", "Induction", "InducedUnitary", "Extension", "NormalExtension"}, method],
            failure["Subgroup MethodData applies only to subgroup routes."],
        KeyExistsQ[data, "Representation"] && (!KeyExistsQ[data, "SubgroupGenerators"] || method === "CharacterSubgroup"),
            failure["A subgroup Representation needs SubgroupGenerators and an induction or extension route."],
        atlasKeys =!= {} && method =!= "AtlasRep", failure["Atlas MethodData applies only to AtlasRep."],
        True, True]
];

(*
    Summary: Refuse representation options for a builder that computes no representations.
    Parameters: effective — validated builder options.
    Options/defaults: None.
    Returns: True, or InapplicableOption Failure.
    Effects: Pure.
    Failures: A non-default Basis, RepresentationMethod, MethodData, TPhaseOrder or PhaseConvention with
        ComputeRepresentations -> False.
    Example: builderRepresentationOptionsQ[<|ComputeRepresentations -> False, Basis -> "General",
        RepresentationMethod -> Automatic, MethodData -> Automatic|>] fails.
    See also: BuildGroup; methodDataApplicableQ.
*)
builderRepresentationOptionsQ[effective_Association] := If[TrueQ[effective[ComputeRepresentations]] ||
    (effective[Basis] === "Unitary" && effective[RepresentationMethod] === Automatic && effective[MethodData] === Automatic &&
        effective[TPhaseOrder] === "Ascending" && effective[PhaseConvention] === None &&
        Lookup[effective, UnitarizationMethod, Automatic] === Automatic && Lookup[effective, WitnessVariant, Automatic] === Automatic),
    True, makeFailure["InapplicableOption", "Representation options require ComputeRepresentations -> True."]];

(*
    Summary: Refuse choices the representation functions would not use (review 2B findings 7, 8, 10).
    Parameters: effective — validated options.
    Options/defaults: None.
    Returns: True, or InapplicableOption Failure.
    Effects: Pure.
    Failures: an explicit FieldMethod with Arithmetic -> "Numerical" (no exact domain); DecomposeRepresentation with
        Basis -> "General" and an explicit UnitarizationMethod (no unitary coordinates); an explicit GroupModel other than
        "Original" where the GAP work runs on the original model only (Decompose, ValidateRepresentation).
    Example: representationChoicesApplicableQ[<|Arithmetic -> "Numerical", FieldMethod -> "Cyclotomic"|>] fails.
    See also: settingsField.
*)
representationChoicesApplicableQ[effective_Association] := Which[
    Lookup[effective, Arithmetic, "Exact"] === "Numerical" && Lookup[effective, FieldMethod, Automatic] =!= Automatic,
        makeFailure["InapplicableOption", "FieldMethod chooses an exact domain; Arithmetic -> \"Numerical\" uses none.", <|"Options" -> {FieldMethod, Arithmetic}|>],
    KeyExistsQ[effective, IsomorphismMethod] && Lookup[effective, Basis, None] === "General" && Lookup[effective, UnitarizationMethod, Automatic] =!= Automatic,
        makeFailure["InapplicableOption", "Basis -> \"General\" has no unitary coordinates, so UnitarizationMethod does not apply.", <|"Options" -> {UnitarizationMethod, Basis}|>],
    MemberQ[{"Permutation", "PC"}, Lookup[effective, GroupModel, Automatic]] || (ListQ[Lookup[effective, GroupModel, Automatic]] && effective[GroupModel] =!= {"Original"}),
        makeFailure["InapplicableOption", "This operation's GAP work runs on the original model; use GroupModel -> Automatic or \"Original\".", <|"Options" -> {GroupModel}|>],
    True, True];

(*
    Summary: Refuse GAP unitarization choices for a request that unitarizes nothing (methodOptionsPlan.md 2B.1, 2B.2).
    Parameters: effective — validated options of ComputeGroupRepresentations or a builder.
    Options/defaults: None.
    Returns: True, or InapplicableOption Failure.
    Effects: Pure.
    Failures: an explicit UnitarizationMethod or WitnessVariant with Basis -> "General" (no unitarization runs).
    Example: unitarizeOptionsApplicableQ[<|Basis -> "General", UnitarizationMethod -> "GroupAverage"|>] fails.
    See also: ComputeGroupRepresentations.
*)
(* Transform: only the FieldMethod/numerical rule (its GroupModel serves GAP routes on every model) *)
representationNumericalFieldQ[effective_Association] := representationChoicesApplicableQ[KeyDrop[effective, {GroupModel, IsomorphismMethod}]];
unitarizeOptionsApplicableQ[effective_Association] := If[effective[Basis] === "General" &&
        (Lookup[effective, UnitarizationMethod, Automatic] =!= Automatic || Lookup[effective, WitnessVariant, Automatic] =!= Automatic),
    makeFailure["InapplicableOption", "UnitarizationMethod and WitnessVariant choose how GAP unitarizes; Basis -> \"General\" unitarizes nothing.",
        <|"Options" -> {UnitarizationMethod, WitnessVariant}|>], True];

(*
    Summary: Refuse T-phase options for a representation request whose basis does not diagonalize T.
    Parameters: effective — validated options of ComputeGroupRepresentations or a builder.
    Options/defaults: None.
    Returns: True, or InapplicableOption Failure.
    Effects: Pure.
    Failures: TPhaseOrder -> "Unchanged", PhaseConvention -> "FirstSRow" or (TransformGroupRepresentations) an explicit
        DiagonalizationMethod without Basis -> "UnitaryTDiagonal".
    Example: tPhaseOptionsApplicableQ[<|Basis -> "Unitary", TPhaseOrder -> "Ascending", PhaseConvention -> "FirstSRow"|>]
        fails.
    See also: representationRequestCompleteQ; builderRepresentationOptionsQ.
*)
tPhaseOptionsApplicableQ[effective_Association] := If[effective[Basis] === "UnitaryTDiagonal" ||
    (effective[TPhaseOrder] === "Ascending" && effective[PhaseConvention] === None &&
        Lookup[effective, DiagonalizationMethod, Automatic] === Automatic), True,
    makeFailure["InapplicableOption", "TPhaseOrder, PhaseConvention and DiagonalizationMethod apply to Basis -> \"UnitaryTDiagonal\"."]];

(* The exact arithmetic domains a caller can name (methodOptionsPlan.md 1.1). *)
$FieldMethods = {"Cyclotomic", "PrimitiveElement", "Radical", "RootReduce"};

(*
    Summary: Refuse contradictory FieldMethod / NumberField and Verification / Arithmetic combinations (D1: an
        explicit choice is never silently overridden).
    Parameters: effective — validated CG options.
    Options/defaults: None.
    Returns: True, or InapplicableOption Failure.
    Effects: Pure.
    Failures: NumberField -> False with a FieldMethod other than Automatic or "RootReduce"; NumberField -> True with
        only "RootReduce"; Verification -> "Exact" with Arithmetic -> "Numerical". The messages name the session default
        as a possible source (delayed defaults look like per-call options).
    Example: fieldMethodApplicableQ[<|NumberField -> False, FieldMethod -> "Cyclotomic"|>] fails.
    See also: cgArithmetic; exactField.
*)
fieldMethodApplicableQ[effective_Association] := With[{method = Lookup[effective, FieldMethod, Automatic], nf = Lookup[effective, NumberField, Automatic]},
    Which[
        nf === False && !MemberQ[{Automatic, "RootReduce", {"RootReduce"}}, method],
            makeFailure["InapplicableOption", "NumberField -> False always uses RootReduce arithmetic, so FieldMethod (possibly the session default) cannot apply.",
                <|"Options" -> {NumberField, FieldMethod}|>],
        nf === True && MemberQ[{"RootReduce", {"RootReduce"}}, method],
            makeFailure["InapplicableOption", "NumberField -> True requires a number field, so FieldMethod -> \"RootReduce\" (possibly the session default) cannot apply.",
                <|"Options" -> {NumberField, FieldMethod}|>],
        True, True]];
(* The Validate functions are the checks themselves: their Verification is Automatic, "Exact" or "Numerical" (None is
   not a check, methodOptionsPlan.md 2C.4); "Exact" on numerical data cannot be honoured. Returns True or a Failure. *)
checkLevelQ[operation_String, level_, numericalData_] := Which[
    level === None, makeFailure["InvalidOption", operation <> " checks: Verification is Automatic, \"Exact\" or \"Numerical\".", <|"Options" -> {Verification}|>],
    level === "Exact" && TrueQ[numericalData], makeFailure["InapplicableOption",
        "Verification -> \"Exact\" cannot prove numerical data; use Automatic or \"Numerical\".", <|"Options" -> {Verification}|>],
    True, True];

(* Operations whose computation is their own proof (methodOptionsPlan.md 2C.4: GroupSubgroups, NormalSubgroupsByIndex,
   GroupElementWords; CheckGeneratorMap, whose map proof is the check): "Numerical" has no analogue (InapplicableOption);
   None runs the computation in full with a notice (refused for CheckGeneratorMap, a check: InvalidOption). Returns True or
   a Failure. *)
proofComputationLevelQ[operation_String, level_, check_ : False] := Which[
    level === "Numerical", makeFailure["InapplicableOption", operation <> " is exact by construction; Verification \"Numerical\" has no meaning here.", <|"Options" -> {Verification}|>],
    level === None && TrueQ[check], makeFailure["InvalidOption", operation <> " checks: Verification is Automatic or \"Exact\".", <|"Options" -> {Verification}|>],
    level === None, (notice[operation <> ": the computation is its own proof; it runs in full (Verification -> None skips nothing here)."]; True),
    True, True];

(*
    Summary: The session default of one option for one operation (methodOptionsPlan.md 2D), and the check of Defaults.
    Parameters: operation — option schema name; option — option symbol; effective — Configuration options.
    Options/defaults: None.
    Returns: sessionOptionDefault: the operation key's value, else the family key's (an excluded option never has one),
        else Missing["NoSessionDefault"]. sessionDefaultsApplicableQ: True, or InvalidOption naming the operations that
        refuse a family value (with the remedy of an operation key), an excluded option, or an unknown family/operation.
    Effects: Pure.
    Failures: InvalidOption.
    Example: with Defaults -> <|"Representations" -> <|FieldMethod -> "Cyclotomic"|>|>, sessionOptionDefault[
        "UnitarizeRepresentation", FieldMethod] is "Cyclotomic".
    Remarks: A family value is accepted only when every member that has the option admits it (its domain and the values
        it refuses in the function), so a session default never makes a member fail on every call.
    See also: ConfigureVVMFTool; resolveOperationOptions.
*)
optionFamily[operation_String] := SelectFirst[Keys[$OptionFamilies], MemberQ[$OptionFamilies[#], operation] &, None];
sessionOptionDefault[operation_String, option_] := Module[{defaults = Lookup[$Configuration, Defaults, <||>], family},
    If[!AssociationQ[defaults], Return[Missing["NoSessionDefault"]]];
    With[{own = Lookup[Lookup[defaults, operation, <||>], option, Missing["NoSessionDefault"]]}, If[!MissingQ[own], Return[own]]];
    family = optionFamily[operation];
    If[family === None || MemberQ[$FamilyExcludedOptions, option], Return[Missing["NoSessionDefault"]]];
    Lookup[Lookup[defaults, family, <||>], option, Missing["NoSessionDefault"]]];
familyValueRefusedQ[operation_String, option_, value_] := !TrueQ[optionValueQ[option, value, operation]] ||
    MemberQ[Lookup[$FamilyRefusedValues, Key[{operation, option}], {}], value];
sessionDefaultsApplicableQ[effective_Association] := Catch[Module[{defaults = Lookup[effective, Defaults, <||>], invalid},
    invalid[message_, data_] := Throw[makeFailure["InvalidOption", message, Join[<|"Options" -> {Defaults}|>, data]], sessionDefaultsApplicableQ];
    If[!AssociationQ[defaults], invalid["Defaults must be an association of families or operations to option rules.", <||>]];
    KeyValueMap[Function[{key, rules},
        If[!AssociationQ[rules], invalid["Each Defaults entry must be an association of options to values.", <|"Key" -> key|>]];
        Which[
            KeyExistsQ[$OptionFamilies, key],
                KeyValueMap[Function[{option, value}, Module[{members = Select[$OptionFamilies[key], KeyExistsQ[$OperationDefaults[#], option] &]},
                    If[MemberQ[$FamilyExcludedOptions, option], invalid["This option has a per-operation meaning; set it as an operation key.",
                        <|"Family" -> key, "Option" -> option|>]];
                    If[members === {}, invalid["No operation of the family takes this option.", <|"Family" -> key, "Option" -> option|>]];
                    With[{refusing = Select[members, familyValueRefusedQ[#, option, value] &]},
                        If[refusing =!= {}, invalid["Some operations of the family refuse this value; set it as their operation keys instead.",
                            <|"Family" -> key, "Option" -> option, "Operations" -> refusing|>]]]]], rules],
            StringQ[key] && KeyExistsQ[$OperationDefaults, key] && key =!= "Configuration",
                KeyValueMap[Function[{option, value},
                    If[!KeyExistsQ[$OperationDefaults[key], option] || familyValueRefusedQ[key, option, value],
                        invalid["The operation does not take this option or refuses this value.", <|"Operation" -> key, "Option" -> option|>]]], rules],
            True, invalid["Unknown family or operation.", <|"Key" -> key|>]]], defaults];
    True], sessionDefaultsApplicableQ];

(* The whole session configuration (methodOptionsPlan.md 2D): every family member, ValidateCG (the flat CG keys) and every
   operation key must still resolve for a call without its own options. A combination the per-value check admits can
   still refuse every such call (NumberField -> False with FieldMethod -> "Cyclotomic"; Verification -> "Exact" with
   Arithmetic -> "Numerical", which the functions refuse in their bodies); those settings are refused, naming the
   operations. An operation that does not resolve
   without session defaults either is not counted. True or InvalidOption. *)
sessionDefaultsCallableQ[config_Association] := Module[{operations, callable, base, broken},
    operations = Select[DeleteDuplicates[Join[Flatten[Values[$OptionFamilies]], {"ValidateCG"},
            Select[Keys[Replace[Lookup[config, Defaults, <||>], Except[_Association] -> <||>]], StringQ]]],
        KeyExistsQ[$OperationDefaults, #] && NameQ["VVMFTool`" <> #] &];
    (* resolved, and not "Exact" on numerical arithmetic, which the functions refuse in their bodies (resultLevelQ) *)
    callable[c_, operation_] := With[{resolved = Block[{$Configuration = c}, Quiet[resolveOperationOptions[Symbol["VVMFTool`" <> operation], operation, {}]]]},
        AssociationQ[resolved] && !(Lookup[resolved, Verification, Automatic] === "Exact" && Lookup[resolved, Arithmetic, "Exact"] === "Numerical")];
    base = Join[config, <|Defaults -> <||>, FieldMethod -> Automatic, Verification -> Automatic|>];
    broken = Select[operations, callable[base, #] && !callable[config, #] &];
    If[broken === {}, True, makeFailure["InvalidOption",
        "These settings would make every call of these operations without their own options fail; choose compatible values, or give the options such a call needs in the same operation key.",
        <|"Options" -> {Defaults, FieldMethod, Verification}, "Operations" -> broken|>]]
];
(* Stored Defaults survive a package reload; ones the reloaded schemas refuse are dropped with a notice, so the rest of the
   configuration stays usable (called once after loading). *)
reconcileStoredDefaults[] := If[AssociationQ[$Configuration] && Lookup[$Configuration, Defaults, <||>] =!= <||> &&
        (FailureQ[sessionDefaultsApplicableQ[$Configuration]] || FailureQ[sessionDefaultsCallableQ[$Configuration]]),
    $Configuration[Defaults] = <||>;
    notice["ConfigureVVMFTool: the stored Defaults no longer fit the loaded package and were cleared."]];

(* A step an operation runs internally inherits the caller's level (methodOptionsPlan.md 2D, user decision 2026-10-13):
   an explicit or session level of the caller is passed on; with the caller at Automatic the step resolves its own
   (session) defaults. The caller's result is marked with the weakest status of what it used. *)
inheritedVerification[level_] := If[level === Automatic, {}, {Verification -> level}];

verificationApplicableQ[effective_Association] :=
    If[Lookup[effective, Verification, Automatic] === "Exact" && Lookup[effective, Arithmetic, "Exact"] === "Numerical",
        makeFailure["InapplicableOption", "Verification -> \"Exact\" (possibly the session default) cannot prove numerical CG coefficients; use Automatic or \"Numerical\".",
            <|"Options" -> {Verification, Arithmetic}|>], True];

(*
    Summary: Require numerical-only settings to accompany numerical arithmetic.
    Parameters: effective — validated options of a representation arithmetic operation.
    Options/defaults: None.
    Returns: True, or InapplicableOption Failure.
    Effects: Pure.
    Failures: An explicit Tolerance with exact arithmetic (exact mode never substitutes a tolerance
        for proof); DiagonalizationMethod "Numerical" without numerical arithmetic, or "Exact" /
        "NumericalReconstruction" with numerical arithmetic.
    Example: arithmeticOptionsApplicableQ[<|Arithmetic -> "Exact", Tolerance -> 10^-5|>] fails.
    See also: UnitarizeRepresentation; DiagonalizeRepresentationT; arithmeticSettings.
*)
arithmeticOptionsApplicableQ[effective_Association] := Module[{numerical = effective[Arithmetic] === "Numerical",
        method = Lookup[effective, DiagonalizationMethod, Automatic]},
    Which[
        !numerical && Lookup[effective, Tolerance, Automatic] =!= Automatic,
            makeFailure["InapplicableOption", "Tolerance applies only with Arithmetic -> \"Numerical\"."],
        method === "Numerical" && !numerical,
            makeFailure["InapplicableOption", "DiagonalizationMethod -> \"Numerical\" requires Arithmetic -> \"Numerical\"."],
        MemberQ[{"Exact", "NumericalReconstruction"}, method] && numerical,
            makeFailure["InapplicableOption", "Exact diagonalization methods require Arithmetic -> \"Exact\"."],
        True, True]
];

(*
    Summary: Validate the value domain of a known option, optionally for one operation.
    Parameters: option — an option symbol; value — its evaluated value; operation — registered
        option-schema name, or None for the shared domain.
    Options/defaults: operation defaults to None.
    Returns: Boolean; cross-option applicability is checked by validateOptions.
    Effects: Reads hardware counts or dependency file existence where necessary.
    Failures: Unknown options, options without a domain for the operation and values outside
        their specified domains return False.
    Example: optionValueQ[AttemptTimeLimit, 20] is True; zero is False.
        optionValueQ[Method, "ClassFilter", "GroupSubgroups"] is True; without the operation
        Method has no shared domain.
    See also: validateOptions; ConfigureVVMFTool; $OperationOptionDomains.
*)
optionValueQ[option_, value_, operation_String] := With[
    {domain = Lookup[Lookup[$OperationOptionDomains, operation, <||>], option, None]},
    If[domain === None, optionValueQ[option, value], TrueQ[domain[value]]]];
optionValueQ[option_, value_, None] := optionValueQ[option, value];
optionValueQ[option_, value_] := Switch[option,
    (* checked in full by sessionDefaultsApplicableQ (the Configuration rule) *)
    Defaults, AssociationQ[value],
    GAPExecutable, value === Automatic || absolutePathQ[value],
    CacheDirectory, absolutePathQ[value] && (!FileExistsQ[value] || DirectoryQ[value]),
    StoreGAPState | ComputeRepresentations | ComputeElements | ComputeSubgroups |
        SubgroupDescriptions | SmallGenerators, MemberQ[{True, False}, value],
    AttemptTimeLimit, value === Infinity ||
        (NumberQ[value] && TrueQ[Im[value] == 0] && TrueQ[value > 0]),
    CoreBudget, value === Automatic || (IntegerQ[value] && 1 <= value <= $ProcessorCount),
    MemoryBudget, value === Automatic || (IntegerQ[value] && value > 0),
    ProgressFunction, MemberQ[{Automatic, None}, value] ||
        Head[value] === Function || (Head[value] === Symbol && Context[value] =!= "System`"),
    CharacterMethod, MemberQ[{Automatic, "DixonSchneider", "Unger", "Conlon",
        "BaumClausen", "KnownTable", "GAP"}, value],
    GroupModel, groupModelChoiceQ[value],
    WordRecovery, wordRecoveryChoiceQ[value],
    Name, value === Automatic || StringQ[value],
    GeneratorNames, generatorNamesQ[value],
    ConstructionDependencies, ListQ[value] &&
        AllTrue[value, absolutePathQ[#] && FileType[#] === File &],
    ValidationGroup, value === Automatic || MatchQ[value, VVMFTool`Group[_String]],
    SubgroupKind, MemberQ[{"ConjugacyClasses", "All", "Normal"}, value],
    SubgroupOrder | SubgroupIndex | MaxResults,
        value === All || (IntegerQ[value] && value > 0),
    IndexMode, MemberQ[{"Exact", "UpTo"}, value],
    MaxBytes, IntegerQ[value] && value >= 0,
    Arithmetic, MemberQ[{"Exact", "Numerical"}, value],
    WorkingPrecision, value === MachinePrecision || (IntegerQ[value] && value >= 16),
    Tolerance, value === Automatic || (NumericQ[value] && Element[value, Reals] && TrueQ[value > 0]),
    UnitarizationMethod, MemberQ[{Automatic, "BSGSAverage", "GroupAverage", "GeneratorEquations"}, value],
    WitnessVariant, MemberQ[{Automatic, "Active", "SmallestConductor"}, value],
    DimensionMethod, MemberQ[{Automatic, "Profile", "TraceFormula"}, value],
    Route, MemberQ[{Automatic, "GAP", "Wolfram"}, value],
    FormFactorizationMethod, MemberQ[{Automatic, "Cholesky", "LDL", "Spectral"}, value],
    DiagonalizationMethod, MemberQ[{Automatic, "Exact", "NumericalReconstruction", "Numerical"}, value],
    TPhaseOrder, MemberQ[{"Ascending", "Unchanged"}, value],
    PhaseConvention, MemberQ[{None, "FirstSRow"}, value],
    IsomorphismMethod, MemberQ[{Automatic, "GroupAverage", "BSGS", "OrbitSum", "GeneratorEquations"}, value],
    CacheKinds, value === All || MemberQ[$RepresentationCacheKinds, value] || (ListQ[value] && value =!= {} &&
        DuplicateFreeQ[value] && SubsetQ[$RepresentationCacheKinds, value]),
    TargetRepresentations, value === Automatic || (AssociationQ[value] && value =!= <||> &&
        AllTrue[Keys[value], StringQ[#] || (IntegerQ[#] && # > 0) &] && AllTrue[Values[value], MatchQ[#, _Rep] &]),
    MatrixSet, MemberQ[{Automatic, "Generators", "Modular"}, value] || (ListQ[value] && value =!= {} && DuplicateFreeQ[value] &&
        (AllTrue[value, StringQ] || AllTrue[value, IntegerQ[#] && # > 0 &])),
    LabelStyle, MemberQ[{Automatic, "ID", "Dimension", "TPhases"}, value],
    IrrepLabels, AssociationQ[value] && AllTrue[Keys[value], StringQ[#] || (IntegerQ[#] && # > 0) &] &&
        AllTrue[Values[value], StringQ[#] || MatchQ[#, TeXFragment[_String]] &],
    ClassOrder, value === Automatic || (ListQ[value] && value =!= {} && AllTrue[value, StringQ] && DuplicateFreeQ[value]),
    RowOrder, value === Automatic || (ListQ[value] && value =!= {} && AllTrue[value, StringQ[#] || (IntegerQ[#] && # > 0) &] && DuplicateFreeQ[value]),
    ScalarNotation, MemberQ[{"Standard", "Exponential", "Omega"}, value],
    OneByOneMatrix, MemberQ[{"Scalar", "Matrix"}, value],
    NotationStyle, MemberQ[{"Standard", "Paper"}, value],
    DefineOmega | Standalone | Overwrite | AllowDuplicates | ShowIDs | ShowAutomaticLabels | Notices | IncludeZeros | Fresh, BooleanQ[value],
    ShowStatus, MemberQ[{Automatic, True, False}, value],
    IrrepForm, MemberQ[{"Index", "ID", "Label"}, value],
    Digits, value === Automatic || (IntegerQ[value] && value > 0),
    Caption, value === Automatic || StringQ[value] || MatchQ[value, TeXFragment[_String]],
    Label, value === None || (StringQ[value] && StringMatchQ[value, RegularExpression["[A-Za-z0-9:_-]+"]]),
    PageSize, value === All || (IntegerQ[value] && value > 0),
    DisplayTimeLimit, value === Infinity || (NumberQ[value] && TrueQ[Im[value] == 0] && TrueQ[value > 0]),
    Normalization, MemberQ[{Automatic, "Unitary", "Dual"}, value],
    ExchangeSymmetry, MemberQ[{Automatic, "Separate", None}, value],
    Prefilter | ComputeMissingRepresentations, BooleanQ[value],
    NumberField, MemberQ[{Automatic, True, False}, value],
    FieldMethod, value === Automatic || MemberQ[$FieldMethods, value] ||
        (ListQ[value] && value =!= {} && DuplicateFreeQ[value] && AllTrue[value, MemberQ[$FieldMethods, #] &]),
    Verification, MemberQ[{Automatic, "Exact", "Numerical", None}, value],
    Recompute, BooleanQ[value],
    ReversePairs, MemberQ[{"Flip", "Compute"}, value],
    TargetIrreps, value === All || StringQ[value] || (IntegerQ[value] && value > 0) ||
        (ListQ[value] && AllTrue[value, StringQ[#] || (IntegerQ[#] && # > 0) &] && DuplicateFreeQ[value]),
    ComponentLabel, StringQ[value] && StringLength[value] > 0,
    TargetIrrep, value === Automatic || StringQ[value] || (IntegerQ[value] && value > 0),
    ComponentLists, value === Automatic || (ListQ[value] && Length[value] === 2 && AllTrue[value, (ListQ[#] && # =!= {}) || MatchQ[#, _Symbol] &]),
    ChannelPolicy, MemberQ[{"Independent", "AllChannels"}, value],
    ApplyCoefficients, BooleanQ[value],
    Coordinate, MemberQ[{"q", "tau"}, value],
    DimensionCache, BooleanQ[value],
    WeightSearchLimit, IntegerQ[value] && value >= 0,
    SeriesOrder, value === Automatic || (IntegerQ[value] && value > 0),
    AccuracyGoal, value === Automatic || (NumberQ[value] && value > 0),
    PrecisionGoal, value === Automatic || (NumberQ[value] && value > 0),
    MaxSeriesOrder, IntegerQ[value] && value > 0,
    NormalizationRules, value === Automatic || AssociationQ[value] || (ListQ[value] && AllTrue[value, MatchQ[#, _String -> _] &]),
    RequireProof, BooleanQ[value],
    TimeLimit, value === Infinity || (NumberQ[value] && value > 0),
    Couplings, value === Automatic || ListQ[value],
    CouplingPrefix, StringQ[value] && StringLength[value] > 0,
    ParameterSymbols, ListQ[value],
    QuadraticConvention, MemberQ[{"Polynomial", "Half"}, value],
    RequirePure, BooleanQ[value],
    ParameterValues, AssociationQ[value],
    FieldWeights, value === Automatic || AssociationQ[value],
    SuperpotentialWeight, MatchQ[value, _Integer | _Rational],
    FormCouplings, value === Automatic || AssociationQ[value],
    ReplaceBindings | RequireBindings, BooleanQ[value],
    FieldValues, AssociationQ[value],
    FormSelection, value === All || (ListQ[value] && AllTrue[value, StringQ] && DuplicateFreeQ[value]),
    PythonBackend, MemberQ[{"NumPy", "mpmath"}, value],
    FunctionNames | ParameterNames, AssociationQ[value] && AllTrue[Keys[value], StringQ] && AllTrue[Values[value], StringQ],
    CommonSubexpressions, BooleanQ[value],
    MassMatrices, AssociationQ[value] && AllTrue[Keys[value], StringQ[#] && StringLength[#] > 0 &],
    ExpressionMode, MemberQ[{"Normalized", "Raw"}, value],
    FormEvaluation, MemberQ[{"Embedded", "External"}, value],
    ExportEvaluationMethod, MemberQ[{Automatic, "QSeries", "FiniteSeries", "Analytic"}, value],
    MaxQTerms, value === All || (IntegerQ[value] && value > 0),
    FactorQSeries | IncludeWeight, BooleanQ[value],
    FieldLabels | CouplingLabels | FormLabels | FormSlotLabels, AssociationQ[value] && AllTrue[Keys[value], StringQ] &&
        AllTrue[Values[value], StringQ[#] || MatchQ[#, TeXFragment[_String]] &],
    _, False
];

(*
    Summary: Require CG MethodData only with the method that uses it.
    Parameters: effective — validated CG options.
    Options/defaults: None.
    Returns: True, or InapplicableOption Failure.
    Effects: Pure.
    Failures: MethodData with a method other than SubgroupEmbedding (or Automatic).
    Example: MethodData -> <|"SubgroupGenerators" -> {GroupWord["a"]}|> with Method -> "ProjectionLazy" fails.
    See also: CGCoefficients; CacheCG.
*)
cgMethodDataApplicableQ[effective_Association] := If[effective[MethodData] === Automatic ||
        MemberQ[{Automatic, "SubgroupEmbedding"}, effective[Method]] || (ListQ[effective[Method]] && MemberQ[effective[Method], "SubgroupEmbedding"]), True,
    makeFailure["InapplicableOption", "MethodData applies only to the SubgroupEmbedding CG method.", <|"Method" -> effective[Method]|>]];

(*
    Summary: Merge configuration and explicit options and reject invalid combinations.
    Parameters: operation — registered operation name; supplied — symbol-keyed association.
    Options/defaults: Operation defaults < matching configuration < supplied options.
    Returns: Effective options association or Failure; Automatic resources become integers
        for operations, while Configuration preserves their Automatic settings.
    Effects: Pure except hardware-memory queries; no worker or cache creation.
    Failures: Unknown operation/option, invalid values (per-operation domains), or a failed
        cross-option rule of $OperationOptionRules such as an inapplicable method/kind pairing.
    Example: validateOptions["BuildGroup", <|ComputeRepresentations -> False|>]
        returns effective builder settings with ComputeRepresentations -> False.
    Remarks: Automatic memory is half physical memory minus this kernel's current allocation,
        bounded below by one byte. It is a conservative budget, not a free-RAM measurement.
    See also: optionValueQ; ConfigureVVMFTool.
*)
validateOptions[operation_String, supplied_Association] := Module[
    {defaults, effective, unknown, invalid, applicable},
    If[!KeyExistsQ[$OperationDefaults, operation],
        Return[makeFailure["UnknownOperation", "No option schema exists for this operation."]]
    ];
    defaults = $OperationDefaults[operation];
    unknown = Complement[Keys[supplied], Keys[defaults]];
    If[unknown =!= {},
        Return[makeFailure["UnknownOption", "An option is not supported by this operation.",
            <|"Operation" -> operation, "Options" -> unknown|>]]
    ];
    effective = Join[defaults, KeyTake[$Configuration, Keys[defaults]], supplied];
    invalid = Select[Keys[effective], !TrueQ[optionValueQ[#, effective[#], operation]] &];
    If[invalid =!= {},
        Return[makeFailure["InvalidOption", "An option value is invalid.",
            <|"Operation" -> operation, "Options" -> invalid|>]]
    ];
    applicable = Select[Through[Lookup[$OperationOptionRules, operation, {}][effective]], FailureQ, 1];
    If[applicable =!= {}, Return[First[applicable]]];
    If[TrueQ[Lookup[effective, SubgroupDescriptions, False]] &&
        KeyExistsQ[effective, ComputeSubgroups], effective[ComputeSubgroups] = True];
    If[operation =!= "Configuration",
        If[Lookup[effective, CoreBudget, None] === Automatic,
            effective[CoreBudget] = Max[1, $ProcessorCount]];
        If[Lookup[effective, MemoryBudget, None] === Automatic,
            effective[MemoryBudget] = Max[1, Floor[$SystemMemory/2] - MemoryInUse[]]]
    ];
    effective
];
validateOptions[___] := makeFailure["InvalidOptions", "Expected an operation name and option association."];

(*
    Summary: Return the current configuration without changing it.
    Status: Alpha.
    Parameters: None.
    Options/defaults: None.
    Returns: A value association keyed by the public option symbols.
    Effects: Read-only; no GAP discovery, processes or directory creation.
    Failures: Arguments produce InvalidInput.
    Example: VVMFToolConfiguration[][StoreGAPState] is initially True.
    See also: ConfigureVVMFTool; CheckGAP.
*)
VVMFToolConfiguration[] := $Configuration;
VVMFToolConfiguration[___] := makeFailure["InvalidInput", "VVMFToolConfiguration takes no arguments."];

Options[ConfigureVVMFTool] = {
    Defaults :> $Configuration[Defaults],
    GAPExecutable :> $Configuration[GAPExecutable],
    CacheDirectory :> $Configuration[CacheDirectory],
    StoreGAPState :> $Configuration[StoreGAPState],
    AttemptTimeLimit :> $Configuration[AttemptTimeLimit],
    CoreBudget :> $Configuration[CoreBudget],
    MemoryBudget :> $Configuration[MemoryBudget],
    ProgressFunction :> $Configuration[ProgressFunction],
    Notices :> $Configuration[Notices],
    FieldMethod :> $Configuration[FieldMethod],
    Verification :> $Configuration[Verification]
};

(*
    Summary: Atomically update validated package configuration.
    Status: Alpha.
    Parameters: options — rules using public option symbols.
    Options/defaults: Omitted settings retain their current values; duplicate rules follow
        Wolfram OptionValue's first-occurrence precedence.
    Returns: Updated configuration association or Failure.
    Effects: Changes session defaults only; leaves objects and existing cache files intact.
    Failures: Any invalid/unknown option leaves the entire old configuration unchanged.
    Example: ConfigureVVMFTool[StoreGAPState -> False][StoreGAPState] returns False.
    See also: VVMFToolConfiguration; validateOptions.
*)
ConfigureVVMFTool[options : OptionsPattern[]] := Module[{supplied, checked, effective, cg},
    supplied = Association[Reverse[Flatten[{options}]]];
    If[Complement[Keys[supplied], Keys[$Configuration]] =!= {},
        Return[makeFailure["UnknownOption", "An unsupported configuration option was supplied."]]
    ];
    (* Reading through OptionValue also supports delayed public defaults and option lists. *)
    effective = Association @@ Map[
        Function[key, key -> OptionValue[ConfigureVVMFTool, {options}, key]],
        Keys[$Configuration]
    ];
    (* The CG family's FieldMethod and Verification are the flat Phase 1 keys (one value, two spellings, 2D) *)
    If[AssociationQ[effective[Defaults]] && AssociationQ[Lookup[effective[Defaults], "CG", None]],
        cg = effective[Defaults]["CG"];
        Do[If[KeyExistsQ[cg, key],
            If[KeyExistsQ[supplied, key] && supplied[key] =!= cg[key],
                Return[makeFailure["InvalidOption", "The CG family's value and the flat key disagree.", <|"Options" -> {key, Defaults}|>], Module]];
            effective[key] = cg[key]], {key, {FieldMethod, Verification}}];
        effective[Defaults] = Join[effective[Defaults], <|"CG" -> KeyDrop[cg, {FieldMethod, Verification}]|>];
        If[effective[Defaults]["CG"] === <||>, effective[Defaults] = KeyDrop[effective[Defaults], "CG"]]];
    checked = validateOptions["Configuration", effective];
    If[FailureQ[checked], Return[checked]];
    With[{callable = sessionDefaultsCallableQ[checked]}, If[FailureQ[callable], Return[callable]]];
    $Configuration = checked;
    $Configuration
];
ConfigureVVMFTool[___] := makeFailure["InvalidOptions", "Expected configuration option rules."];

True
