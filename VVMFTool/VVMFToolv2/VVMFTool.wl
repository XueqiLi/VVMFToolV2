(*
    :Title: VVMFTool public context and module loader
    :Context: VVMFTool`
    :Summary: Declare the public input vocabulary and load implemented modules once.
    :Responsibilities: Package-relative loading; preserve existing state on reload.
    :Dependencies: Kernel modules listed in loadModules.
    :See Also: Kernel/init.m; VVMFArch/step1Plan.md
*)
BeginPackage["VVMFTool`"];

Group::usage =
    "Group[id] is a handle to a finite-group object. group[\"property\"] reads a stored property without starting a computation.";
NumberOfRep::usage =
    "NumberOfRep[group] returns the number of irreducible characters, including when representation matrices have not been computed.";
GroupWord::usage =
    "GroupWord[syllables] denotes an ordered generator word. GroupWord[text] denotes a word parsed in the receiving group's generators.";
GroupPresentation::usage =
    "GroupPresentation[names, relators] specifies a group by ordered generator names and words equal to the identity.";
CatalogueGroup::usage =
    "CatalogueGroup[catalogue, key] specifies a finite group from a supported GAP catalogue.";
PermutationGroupSpecification::usage =
    "PermutationGroupSpecification[generators, names] specifies a group with an ordered list of Cycles generators.";
MatrixGroupSpecification::usage =
    "MatrixGroupSpecification[generators, names, domain] specifies a group of exact matrices over the declared domain.";
ModularGroupSpecification::usage =
    "ModularGroupSpecification[label] returns the recorded presentation of a named modular realization.";
VVMFToolConfiguration::usage =
    "VVMFToolConfiguration[] returns the current package configuration as an association keyed by option symbols.";
ConfigureVVMFTool::usage =
    "ConfigureVVMFTool[options] atomically changes package defaults and returns the configuration, or Failure.";
CheckGAP::usage =
    "CheckGAP[] probes the configured GAP executable and reports versions, packages, command flags and workspace support.";
CleanGAPCache::usage =
    "CleanGAPCache[opts] removes least-recently-used managed GAP checkpoints until the byte cap is met.\nCleanGAPCache[\"All\"] removes all eligible entries; active entries are deferred until their leases end.";
BuildGroup::usage =
    "BuildGroup[spec, opts] constructs a finite group with a complete irreducible character table and the requested optional data.";
BuildGroupFromGAP::usage =
    "BuildGroupFromGAP[code, opts] executes explicit GAP construction code defining VVMFInputGroup and VVMFInputGenerators, and builds the resulting finite group.";
BuildModularGroup::usage =
    "BuildModularGroup[label, opts] builds the recorded finite modular realization and validates its S,T generators.\nBuildModularGroup[presentation, opts] uses the presentation's explicitly named S and T.";
RestoreGAPState::usage =
    "RestoreGAPState[group, opts] verifies the group's retained GAP state in a fresh worker and returns a restoration report, or Failure when it cannot restore.";
VVMFTool`GroupElementWords::usage =
    "GroupElementWords[group, opts] returns all elements as recorded-generator words, computing and storing them in the group when needed.";
GroupWordOrder::usage =
    "GroupWordOrder[group, word, opts] returns the exact positive order of a GroupWord in the finite group.";
AssignModularGenerators::usage =
    "AssignModularGenerators[group, sWord, tWord, opts] validates the explicit modular generator pair and updates the same group, or returns Failure while preserving its previous assignment.";
GroupSubgroups::usage =
    "GroupSubgroups[group, opts] returns a complete collection of embedded subgroup classes, all subgroups or normal subgroups, with optional order/index filters and descriptions.";
CheckGeneratorMap::usage =
    "CheckGeneratorMap[source, target, images, opts] checks the prescribed target word for each source generator, returning map flags and inverse words when isomorphic. It may enrich the groups' backend state.";

Rep::usage =
    "Rep[{m1, m2, ...}] is a representation value holding one invertible square matrix per recorded group generator, in recorded order.\nRep[{}, d] is the d-dimensional representation of a group with no recorded generators.";
RepDim::usage = "RepDim[r] returns the dimension of the representation value r.";
NumberOfGenerator::usage = "NumberOfGenerator[r] returns the number of generator matrices of the representation value r.";
GeneratorMatrix::usage = "GeneratorMatrix[r, i] returns the matrix of the i-th recorded generator in the representation value r.";
RepMatrix::usage =
    "RepMatrix[r, word, names] evaluates the GroupWord word on the matrices of r, where names are the ordered generator names of those matrices.";
SRep::usage =
    "SRep[g, r] returns the matrix of the modular generator S assigned to group or context g, evaluated as its assigned word on the matrices of r.";
TRep::usage =
    "TRep[g, r] returns the matrix of the modular generator T assigned to group or context g, evaluated as its assigned word on the matrices of r.";
RepresentationContext::usage =
    "RepresentationContext[g] returns an immutable snapshot of the accepted group g's generators, characters, modular assignment and representation data. context[\"field\"] reads a field.";

ComputeGroupRepresentations::usage =
    "ComputeGroupRepresentations[g] computes verified matrices of every irreducible representation of the group g and stores them in g.\nComputeGroupRepresentations[g, ids] computes the irreps with the given IDs.";
GroupRepresentation::usage =
    "GroupRepresentation[g, id] returns the active Rep of the irrep with ID id, or Missing[\"NotComputed\"]; it never starts a computation.";
RepresentationData::usage =
    "RepresentationData[g, id] returns the stored data of the irrep with ID id: its variants, active variant and accepted partial matrices.";

UnitaryRepresentationQ::usage =
    "UnitaryRepresentationQ[r] tests whether every generator matrix of the representation value r is unitary.";
ChangeRepBasis::usage =
    "ChangeRepBasis[r, b] returns the representation with matrices b.M.Inverse[b] for every generator matrix M of r.";
UnitarizeRepresentation::usage =
    "UnitarizeRepresentation[g, r] transforms the representation r of the group or context g to a unitary basis through a verified invariant form, returning the new Rep, the basis change and validation data.";
DiagonalizeRepresentationT::usage =
    "DiagonalizeRepresentationT[g, r] transforms the representation r so that the assigned modular generator T of g is diagonal, returning the new Rep, the basis change, the T spectrum and validation data.";
RepresentationTSpectrum::usage =
    "RepresentationTSpectrum[g, r] returns the eigenvalues, phases and multiplicities of the assigned modular generator T of g in the representation r.";

RepresentationCharacter::usage =
    "RepresentationCharacter[g, r] returns the values of the character of the representation r on the conjugacy classes of the group or context g, keyed by class ID.";
ValidateGroup::usage =
    "ValidateGroup[g] proves a weakly built group's character table (and a skipped S,T check) in GAP and raises the group's verification status; ValidateGroup[g, Verification -> \"Numerical\"] re-reads it with Wolfram's numerical checks only.";
ValidateRepresentation::usage =
    "ValidateRepresentation[g, r] checks the representation r against the group or context g: the relators of a complete presentation, the character and its irreducible multiplicities, and the basis properties.";
DecomposeRepresentation::usage =
    "DecomposeRepresentation[g, r] decomposes the representation r of the group or context g into irreducible blocks, returning the block Rep, the multiplicities and a verified embedding U with M.U == U.block for every generator matrix M.";

ReorderGroupIrreps::usage =
    "ReorderGroupIrreps[g, ids] sets the presentation order of the irreducible representations of g to the permutation ids of its irrep IDs.";
SortGroupIrreps::usage =
    "SortGroupIrreps[g] sorts the presentation order of the irreducible representations of g by degree, keeping the order of equal degrees.";
RepresentationElementMatrices::usage =
    "RepresentationElementMatrices[g, id] returns the matrices of every group element in the active representation of irrep id.\nRepresentationElementMatrices[g, id, words] returns the matrices of the given element words, in order.";
CleanRepresentationCache::usage =
    "CleanRepresentationCache[g] removes derived representation caches of g and advances their eviction epoch; representations and characters are kept.";

SetGroupRepresentation::usage =
    "SetGroupRepresentation[g, id, r] verifies the representation r against irrep id of the group g, stores it and makes it the active representation.";
ChangeGroupRepBasis::usage =
    "ChangeGroupRepBasis[g, id, b] stores the active representation of irrep id in the basis given by b, with matrices b.M.Inverse[b], and makes it active.";
TransformGroupRepresentations::usage =
    "TransformGroupRepresentations[g] transforms the computed irreps of g to a unitary (or unitary T-diagonal) basis, committing all selected irreps together.\nTransformGroupRepresentations[g, ids] transforms the irreps with the given IDs.";

ImportGroupData::usage =
    "ImportGroupData[file, opts] reads a mathematical snapshot into a fresh Group after independent registered-export or actual native correspondence validation.";
SaveGroupData::usage =
    "SaveGroupData[group, file] atomically saves a mathematical JSON snapshot and registers its validated bytes in the independent local export ledger.";
NormalSubgroupsByIndex::usage =
    "NormalSubgroupsByIndex[presentation, bound, opts] searches normal subgroups at an exact or bounded index, returning subgroup words, finite quotient presentations and explicit completeness.";

GAPExecutable::usage = "GAPExecutable specifies an absolute GAP executable path, or Automatic for discovery.";
CacheDirectory::usage = "CacheDirectory specifies the absolute directory for managed retained GAP state.";
StoreGAPState::usage = "StoreGAPState specifies whether GAP checkpoints survive the current call; the default is True.";
ComputeRepresentations::usage = "ComputeRepresentations specifies whether a builder computes irreducible matrices; the default is True.";
ComputeElements::usage = "ComputeElements specifies whether a builder computes element words; the default is False.";
ComputeSubgroups::usage = "ComputeSubgroups specifies whether a builder computes subgroups; the default is False.";
SubgroupDescriptions::usage = "SubgroupDescriptions requests structure descriptions and implies subgroup computation.";
CharacterMethod::usage = "CharacterMethod selects the character algorithm, or Automatic for permitted applicable attempts.";
GroupModel::usage = "GroupModel selects Original, Permutation or PC computational models, or Automatic.";
AttemptTimeLimit::usage = "AttemptTimeLimit limits each algorithm attempt including validation and saving, in seconds; the default is 600.";
CoreBudget::usage = "CoreBudget specifies the total available worker cores, or Automatic.";
MemoryBudget::usage = "MemoryBudget specifies the total worker memory budget in bytes, or Automatic.";
ProgressFunction::usage = "ProgressFunction specifies Automatic, None, or a callback receiving progress associations.";
Name::usage = "Name specifies a group's display name, or Automatic.";
GeneratorNames::usage = "GeneratorNames specifies the ordered generator names for explicit GAP-code construction.";
ConstructionDependencies::usage = "ConstructionDependencies lists existing absolute input file paths for a GAP-code construction.";
ValidationGroup::usage = "ValidationGroup specifies a group supplying correspondence checks for imported data, or Automatic.";
SubgroupKind::usage = "SubgroupKind selects ConjugacyClasses, All or Normal subgroup results.";
SubgroupOrder::usage = "SubgroupOrder filters subgroups by a positive order, or All.";
SubgroupIndex::usage = "SubgroupIndex filters subgroups by a positive index, or All.";
IndexMode::usage = "IndexMode selects Exact or UpTo for bounded normal-subgroup searches.";
MaxResults::usage = "MaxResults caps a bounded search at a positive number of results, or All.";
SmallGenerators::usage = "SmallGenerators requests smaller subgroup generating sets.";
MaxBytes::usage = "MaxBytes sets the retained GAP cache byte cap; the default is 10^9.";
Basis::usage = "Basis specifies the requested representation basis: \"Unitary\" (default), \"General\" or \"UnitaryTDiagonal\" (unitary with diagonal assigned T), as each function allows.";
RepresentationMethod::usage = "RepresentationMethod selects one representation construction route, or Automatic for the unitary-first phases.";
MethodData::usage = "MethodData supplies route-specific data: subgroup generator words and an optional subgroup representation, or an Atlas group name and representation number.";
UnitarizationMethod::usage = "UnitarizationMethod selects the invariant-form method: Automatic, \"BSGSAverage\", \"GroupAverage\" or \"GeneratorEquations\".";
FormFactorizationMethod::usage = "FormFactorizationMethod selects the factorization H = B^\[Dagger] B of an invariant form: Automatic, \"Cholesky\", \"LDL\" or \"Spectral\".";
DiagonalizationMethod::usage = "DiagonalizationMethod selects T diagonalization: Automatic, \"Exact\", \"NumericalReconstruction\" or \"Numerical\".";
Arithmetic::usage = "Arithmetic selects \"Exact\" (default) or explicitly \"Numerical\" representation arithmetic.";
TPhaseOrder::usage = "TPhaseOrder orders a diagonal T by \"Ascending\" phase (default) or keeps the \"Unchanged\" basis order.";
IsomorphismMethod::usage = "IsomorphismMethod selects how decomposition blocks are aligned to target irreps: Automatic, \"GroupAverage\", \"BSGS\", \"OrbitSum\" or \"GeneratorEquations\".";
CacheKinds::usage = "CacheKinds selects the derived representation caches to clean: All, \"ElementMatrices\", \"Unitarity\", \"Decompositions\", \"DerivedIntermediates\" or a list of them.";
TargetRepresentations::usage = "TargetRepresentations gives the irreducible target matrices of a decomposition: Automatic (the group's stored irreps) or an association irrep ID -> Rep.";
PhaseConvention::usage = "PhaseConvention selects None (default) or \"FirstSRow\", a diagonal rephasing making the first row of S real and nonnegative.";
DisplayDocument::usage = "DisplayDocument[kind, data] is an immutable display snapshot of accepted group data; v[\"field\"] reads a field. Later group changes do not alter it.";
TeXFragment::usage = "TeXFragment[\"tex\"] marks explicitly supplied raw TeX for display labels and captions; ordinary strings are escaped text. It is shown literally in notebooks and never evaluated.";
GroupSummary::usage = "GroupSummary[g] snapshots the group's identity, generators, modular assignment, data availability and retained GAP state for display.";
CharacterTableView::usage = "CharacterTableView[g] snapshots the character table of g (exact values, class sizes, orders and words) for display; no matrices are needed.";
RepresentationTable::usage = "RepresentationTable[g] snapshots the stored irreducible representations of g for display.\nRepresentationTable[g, ids] shows the irreps with the given IDs, in that order.";
RepresentationView::usage = "RepresentationView[r] snapshots a representation value for display.\nRepresentationView[c, r] shows it with the generator names, assignment and known validation of the group or context c.";
RepresentationLabelData::usage = "RepresentationLabelData[c, r] returns the dimension, irrep ID, certified T phases, arithmetic and unique ID of a representation for labelling, without new computation on the group.";
DisplayData::usage = "DisplayData[v] returns the data association of the display document v.";
ToNotebook::usage = "ToNotebook[v] renders the display document v for a notebook.";
ToLaTeX::usage = "ToLaTeX[v] renders the display document v as LaTeX.";
ScalarLaTeX::usage = "ScalarLaTeX[x] returns the LaTeX of an exact algebraic or numerical scalar without changing its value.";
MatrixLaTeX::usage = "MatrixLaTeX[m] returns the LaTeX of a matrix as a pmatrix, keeping the parentheses of its entries.";
LaTeXPreamble::usage = "LaTeXPreamble[] returns the package and macro lines that LaTeX fragments from ToLaTeX need.";
ExportDisplay::usage = "ExportDisplay[file, v] writes the display document v to a LaTeX file.\nExportDisplay[file, v, \"Notebook\"] writes a static notebook.";
MatrixSet::usage = "MatrixSet selects the matrices a representation view shows: Automatic, \"Generators\", \"Modular\", or a list of generator names (indices for a bare representation).";
IrrepLabels::usage = "IrrepLabels gives custom display labels: an association irrep ID -> string or TeXFragment.";
ClassOrder::usage = "ClassOrder gives the column order of a character table view: Automatic or a permutation of the class IDs.";
RowOrder::usage = "RowOrder gives the row order of a character table view: Automatic (the group's IrrepOrder) or a permutation of the irrep IDs.";
ScalarNotation::usage = "ScalarNotation selects how certified roots of unity are written: \"Standard\", \"Exponential\" or \"Omega\".";
OneByOneMatrix::usage = "OneByOneMatrix selects whether a 1x1 matrix is written as its \"Scalar\" entry or as a \"Matrix\".";
NotationStyle::usage = "NotationStyle selects \"Standard\" LaTeX commands or the \"Paper\" macros \\ii, \\ee and \\rep.";
DefineOmega::usage = "DefineOmega specifies whether the definition of omega_a^b is included once when used.";
Digits::usage = "Digits limits the displayed digits of numerical values: Automatic or a positive integer. Exact values are never rounded.";
Caption::usage = "Caption overrides the automatic caption of a display: Automatic, a string or a TeXFragment.";
Standalone::usage = "Standalone specifies whether LaTeX output is a complete document (True) or a fragment (False).";
PageSize::usage = "PageSize gives the rows per page of notebook views: a positive integer or All. Exports are always complete.";
DisplayTimeLimit::usage = "DisplayTimeLimit bounds optional label work such as certifying T phases, in seconds.";
Overwrite::usage = "Overwrite specifies whether ExportDisplay replaces an existing file.";
TensorDecomposition::usage =
    "TensorDecomposition[g, {id1, id2, ...}] gives the exact multiplicity of every irrep in the tensor product of the listed irreps of the group or context g, from the character table alone (no matrices, no GAP). The empty product is one copy of the trivial irrep.";
TensorMultiplicity::usage = "TensorMultiplicity[g, ids, target] gives the multiplicity of the irrep target in the tensor product of the irreps ids.";
TensorIrrepList::usage = "TensorIrrepList[g, ids] lists the irreps of the tensor product of ids, each repeated by its multiplicity, in the presentation order.";
TensorDecompositionView::usage = "TensorDecompositionView[g, products] is a read-only display document of tensor-product decompositions (All: every unordered pair; or one list of irrep IDs; or a list of lists), from the character table alone. Render it with ToNotebook, ToLaTeX or ExportDisplay.";
CGData::usage = "CGData[data] is an immutable snapshot of Clebsch-Gordan coefficients: input and target bases, conventions, coverage and one channel (embedding K and dual W) per copy of each selected target.";
CGCoefficients::usage =
    "CGCoefficients[g, {p, q}, targets] gives CGData with every copy of every selected target irrep in the tensor product of the irreps p and q of the group or context g: embeddings K with R.K == K.D and duals W with W.R == D.W on every recorded generator, normalized and validated. targets is All (default), an irrep ID or a list.";
CGIntertwiners::usage = "CGIntertwiners[cg, target] lists the channel records (ChannelID, Copy, Symmetry, Embedding, Dual) of one target of CGData cg; Missing[\"NotSelected\"] for a target outside the selection.";
CGMatrix::usage = "CGMatrix[cg] assembles the embedding matrices of CGData side by side; CGMatrix[cg, \"Dual\"] stacks the duals.";
ValidateCG::usage = "ValidateCG[cg] recomputes covariance, dual covariance, pairing, rank, exchange symmetry and normalization of CGData cg from its frozen matrices.";
CacheCG::usage = "CacheCG[g] computes and stores CG coefficients for every ordered pair of irreps of the group g (CacheCG[g, pairs] for selected pairs) and reports the coverage and, when it stored new coefficients, the Publication (how many were stored).";
CGCacheInformation::usage = "CGCacheInformation[g] reports the coverage of the group's CG store without changing it.";
CleanCGCache::usage = "CleanCGCache[g] removes stored CG coefficients (CleanCGCache[g, pairs] for selected pairs) and advances the store's eviction epoch.";
CloseCGPool::usage = "CloseCGPool[] closes the subkernels that CacheCG and CGCoefficients launched to race CG methods under Method -> Automatic (they are kept for the session) and reports how many were closed.";
Normalization::usage = "Normalization selects the CG convention: Automatic (\"Unitary\" when all participating matrices are unitary, else \"Dual\"), \"Unitary\" or \"Dual\".";
ExchangeSymmetry::usage = "ExchangeSymmetry controls equal-factor CG copies: Automatic (split into symmetric and antisymmetric sectors when both factors are the same stored variant), \"Separate\" (require the split) or None.";
Prefilter::usage = "Prefilter specifies whether exactly certified distinct eigenvalues of diagonal generators eliminate CG unknowns before the full equations are solved.";
NumberField::usage = "NumberField controls the common algebraic number field of CG arithmetic: Automatic, True or False.";
FieldMethod::usage = "FieldMethod selects the exact arithmetic domain of the CG family: Automatic (the package's choice), \"Cyclotomic\" (Q(zeta_N) from the cyclotomic hints, with no size gate), \"PrimitiveElement\", \"Radical\", \"RootReduce\" or an ordered list of these tried in turn. An explicit choice is used as given; FieldMethodUnavailable if none applies.";
Verification::usage = "Verification sets how a calculation checks its result: Automatic (the usual checks), \"Exact\", \"Numerical\" (checks at WorkingPrecision) or None (no checks; the result is marked \"Unverified\"). Its session default (ConfigureVVMFTool) is the CG family's.";
Defaults::usage = "Defaults is a ConfigureVVMFTool setting: <|family -> <|option -> value|>, operation -> <|option -> value|>|> with the families \"CG\", \"Representations\", \"Models\" and \"Modular\" and operation names such as \"UnitarizeRepresentation\". A call uses an explicit option first, then its operation's key, then its family's, then the built-in default.";
DimensionMethod::usage = "DimensionMethod is an option of MinimumModularWeight, ModularFormCandidates, ModularTensorProductVectors and ModularContractions: the Method of the modular dimensions they use (Automatic, \"Profile\" or \"TraceFormula\").";
Route::usage = "Route is an option of TransformGroupRepresentations: Automatic (GAP for native variants unless an option needs Wolfram), \"GAP\" or \"Wolfram\".";
WitnessVariant::usage = "WitnessVariant is an option of ComputeGroupRepresentations, the group builders and TransformGroupRepresentations: which stored variant GAP unitarizes or T-diagonalizes: Automatic or \"SmallestConductor\" (the variant with the smallest cyclotomic conductor) or \"Active\" (the active variant).";
WordRecovery::usage = "WordRecovery is an option of the group builders and the GAP group operations (GroupElementWords, GroupWordOrder, GroupSubgroups, AssignModularGenerators, CheckGeneratorMap): Automatic (Native, then FP, then Cayley word recovery) or an ordered list of \"Native\", \"FP\", \"Cayley\".";
Recompute::usage = "Recompute is an option of CGCoefficients: True computes the coefficients with the requested Method even when the store already holds them (the result is stored only where nothing is stored yet).";
ReversePairs::usage = "ReversePairs is an option of CacheCG: \"Flip\" (default) obtains a reverse pair by a verified tensor flip of the computed orientation, \"Compute\" computes it like any pair.";
ComputeMissingRepresentations::usage = "ComputeMissingRepresentations specifies whether a group CG call computes the missing input and target representations it needs.";
RepVector::usage = "RepVector[data] is an immutable representation-valued vector: ordered records (target irrep, components, contraction path, basis identity, arithmetic) bound to the frozen RepresentationContext it was made in.";
VectorComponent::usage = "VectorComponent[vectorID, i] is the inert i-th component of a vector made by MakeRepVector with automatic components.";
MakeRepVector::usage = "MakeRepVector[g, id] makes a vector of the irrep id with inert components; MakeRepVector[g, id, {c1, ..., cd}] uses explicit components (numbers or expressions).";
VectorComponents::usage = "VectorComponents[v] lists the records of the RepVector v: TargetID, Components, Path, ChannelIDs, BasisID and Arithmetic (\"Exact\" or \"Numerical\").";
JoinRepVectors::usage = "JoinRepVectors[{v1, v2, ...}] concatenates the records of vectors of one frozen context, keeping equal and zero records.";
EmptyRepVector::usage = "EmptyRepVector[g] is the additive zero vector of the group or context g.";
TensorProductVectors::usage = "TensorProductVectors[g, {v1, v2, ...}] multiplies representation-valued vectors left-associatively through CG duals, keeping every copy and every zero; TargetIrreps prunes the paths to the requested final irreps. {} gives the tensor unit.";
CGPolynomialResult::usage = "CGPolynomialResult[g, {p, q}, target] gives every copy of target in the product of a p-vector and a q-vector as polynomials of their components (ComponentLists -> {listA, listB} for explicit components).";
ComponentLabel::usage = "ComponentLabel gives the display label of the inert components of MakeRepVector (default \"x\"); it is cosmetic only.";
ComponentLists::usage = "ComponentLists gives the component lists of CGPolynomialResult: Automatic (distinct inert vectors) or {listA, listB}.";
TargetIrreps::usage = "TargetIrreps selects the target irreps of CacheCG and vector products: All, an irrep ID or a list of IDs.";
Field::usage = "Field[data] is an immutable field transforming in one irrep: ID, name, irrep, accepted matrices (its transformation law), frozen context and inert components.";
FieldComponent::usage = "FieldComponent[fieldID, i] is the inert i-th component of a Field.";
CreateField::usage = "CreateField[g, id, name] creates a field in the irrep id of the group or context g, with inert components; distinct fields of one irrep are independent.";
FieldComponents::usage = "FieldComponents[f] lists the inert components of the Field f.";
FieldVector::usage = "FieldVector[f] is the representation-valued vector (RepVector) of the Field f.";
Model::usage = "Model[data] is an immutable finite-group model: fields, a degree-one target irrep, coupled terms and parameters in one frozen context.";
CreateModel::usage = "CreateModel[g, {f1, f2, ...}] creates an empty model of the fields over the group or context g (TargetIrrep: the trivial irrep or another degree-one irrep).";
ContractionSet::usage = "ContractionSet[data] holds every contraction path of model fields into the model's target: path, CG channel IDs and scalar polynomial, zeros included, with independence data when computed.";
Contractions::usage = "Contractions[m, {f1, f2, ...}] gives every CG contraction of the listed model fields (repetitions allowed) into the model's target as a ContractionSet.";
IndependentContractions::usage = "IndependentContractions[set] keeps a linearly independent basis of the set's channel polynomials and expresses every original channel in it (Relations).";
SelectContractions::usage = "SelectContractions[set, ids] keeps exactly the listed channel IDs, in the given order.";
CoupledExpression::usage = "CoupledExpression[data] is an immutable coupled term: expressions, their coefficients, the parameter records and a TermID.";
Coupling::usage = "Coupling[id] is an inert model parameter (an independent complex scalar).";
CoupleContractions::usage = "CoupleContractions[set] attaches one fresh coupling to each independent channel of a ContractionSet (ChannelPolicy -> \"AllChannels\" for every nonzero channel).";
CoupleExpressions::usage = "CoupleExpressions[{e1, e2, ...}] attaches one coefficient to each nonzero scalar expression; the term's symmetry is unverified until it is added to a model.";
CouplingParameters::usage = "CouplingParameters[e] lists the parameter records (Atom, ID, Label, Domain, SourceAtom) of a CoupledExpression.";
CoupledExpressionValue::usage = "CoupledExpressionValue[e] is the scalar value of a CoupledExpression.";
AddModelTerm::usage = "AddModelTerm[m, e] returns a new model with the coupled term e, after checking fields, target, context and covariance on every generator.";
ModelExpression::usage = "ModelExpression[m] is the exact sum of the model's terms.";
ModelParameters::usage = "ModelParameters[m] lists the model's parameter records in first-appearance order.";
ValidateModel::usage = "ValidateModel[m] recomputes the covariance of the model and of each term on every recorded generator.";
MassMatrix::usage = "MassMatrix[data] holds a bilinear or quadratic coefficient matrix: input, selected sector, remainder, variables, convention and field identities.";
ExtractBilinearMatrix::usage = "ExtractBilinearMatrix[expr, rows, cols] gives M with selected == rows . M . cols (fields for rows and cols use their components); the remainder is kept. Numerical input needs Arithmetic -> \"Numerical\".";
ExtractQuadraticMatrix::usage = "ExtractQuadraticMatrix[expr, x] gives the symmetric M with selected == x . M . x (QuadraticConvention -> \"Half\": selected == (x . M . x)/2). Numerical input needs Arithmetic -> \"Numerical\".";
MatrixValues::usage = "MatrixValues[mass] is the matrix of a MassMatrix.";
ValidateMassMatrix::usage = "ValidateMassMatrix[m, mass] certifies that mass was extracted from the model's expression, selects whole field multiplets and transforms covariantly.";
TargetIrrep::usage = "TargetIrrep sets the target irrep of CreateModel: Automatic (trivial) or a degree-one irrep ID.";
ChannelPolicy::usage = "ChannelPolicy selects the channels CoupleContractions couples: \"Independent\" (default) or \"AllChannels\".";
Couplings::usage = "Couplings gives explicit coefficient expressions for CoupleContractions and CoupleExpressions (Automatic: fresh couplings).";
CouplingPrefix::usage = "CouplingPrefix gives the label prefix of generated couplings (default \"c\").";
ParameterSymbols::usage = "ParameterSymbols declares the user symbols or indexed atoms that are parameters in Couplings or in the supplied expressions; each declaration becomes a new parameter (share one between terms through its Coupling atom).";
QuadraticConvention::usage = "QuadraticConvention chooses the quadratic matrix convention: \"Polynomial\" (selected == x . M . x) or \"Half\" (selected == (x . M . x)/2).";
RequirePure::usage = "RequirePure specifies whether matrix extraction fails unless the selected sector is the whole expression.";
ModelOutput::usage = "ModelOutput[data] is an immutable prepared output of a model: named scalar and matrix outputs as typed expression trees, explicit parameter substitutions, the ordered runtime parameter IDs and the required field inputs. out[\"field\"] reads a field.";
PrepareModelOutput::usage = "PrepareModelOutput[m] prepares the model expression of the Model m for numerical export.\nPrepareModelOutput[m, <|name -> output, ...|>] prepares named scalar expressions, matrices or validated MassMatrix values (ParameterValues -> <|id -> value|> fixes parameters explicitly).";
PythonArtifact::usage = "PythonArtifact[data] is an immutable generated Python module: source, embedded manifest, backend, precision and the identity of its ModelOutput.";
ToPython::usage = "ToPython[out] generates a standalone NumPy (default) or mpmath Python module that evaluates the outputs of the ModelOutput out, with validated inputs and finite checked results.";
PythonSource::usage = "PythonSource[a] is the Python source of the PythonArtifact a.";
PythonManifest::usage = "PythonManifest[a] is the manifest of the PythonArtifact a: model and group identities, outputs, parameter IDs and names, substitutions, fields and numerical status.";
ExportPython::usage = "ExportPython[file, a] writes the module of the PythonArtifact a to file atomically and returns the absolute path; nothing is imported or executed.";
ModelView::usage = "ModelView[m] is a read-only display document of the Model m: target and covariance status as recorded, fields, expression, terms and parameters. Render it with ToNotebook, ToLaTeX or ExportDisplay.";
FieldTable::usage = "FieldTable[m] is a display document of the fields of the Model m: name, ID, irrep, dimension, basis and ordered components.";
ContractionTable::usage = "ContractionTable[s] is a display document of the ContractionSet s: every channel with its path, polynomial, zero status and independence role (never computed by the display).";
CouplingTable::usage = "CouplingTable[x] is a display document of the parameters of a Model or CoupledExpression: ID, label, domain and source spelling.";
MassMatrixView::usage = "MassMatrixView[mass] is a display document of a MassMatrix: shape, row and column variables, entries, convention, selected sector, remainder and extraction status.";
ModelOutputView::usage = "ModelOutputView[out] is a display document of a ModelOutput: outputs, explicit substitutions, runtime parameters and required fields.";
FieldLabels::usage = "FieldLabels gives display labels of fields in model views: an association from field IDs to strings or TeXFragment.";
CouplingLabels::usage = "CouplingLabels gives display labels of parameters in model views: an association from parameter IDs to strings or TeXFragment.";
SaveModelData::usage = "SaveModelData[m, file] atomically saves the Model m (fields, parameters, terms, frozen context and its group's mathematical snapshot) as a JSON archive and registers its bytes in the export ledger; MassMatrices -> <|name -> mass|> adds certified coefficient matrices.";
ImportModelData::usage = "ImportModelData[file] imports a model archive: it admits the embedded group as ImportGroupData does, rebinds the frozen context, revalidates the model and every matrix, and returns <|\"Model\", \"MassMatrices\", \"Group\"|>.";
MassMatrices::usage = "MassMatrices gives the named coefficient matrices SaveModelData stores with a model: an association from names to MassMatrix values, each certified against the model.";
ParameterValues::usage = "ParameterValues gives explicit parameter substitutions for PrepareModelOutput: an association from parameter IDs to finite numeric constants.";
PythonBackend::usage = "PythonBackend selects the numerical backend of ToPython: \"NumPy\" (machine precision, default) or \"mpmath\" (arbitrary precision).";
FunctionNames::usage = "FunctionNames gives Python function names for selected outputs in ToPython: an association from output names to identifiers.";
ParameterNames::usage = "ParameterNames gives cosmetic Python names for selected parameters in ToPython: an association from parameter IDs to identifiers.";
CommonSubexpressions::usage = "CommonSubexpressions specifies whether ToPython evaluates subexpressions shared between outputs once (True, default).";
(* Inert scalar atoms: N must never convert a component index or parameter ID into a number. *)

(* Stage 7: modular-form objects and computation. *)
FormVariable::usage = "FormVariable[\"q\"] or FormVariable[\"tau\"] is the inert independent variable of a parsed modular-form definition.";
FormParameter::usage = "FormParameter[id] is an inert relative-normalization unknown of a modular-form definition; its ID is scoped by the definition's family.";
ModularFormDefinition::usage = "ModularFormDefinition[{f1, ...}, var, opts] parses a modular-form definition held, replacing var and the declared NormalizationParameters by inert atoms.\nModularFormDefinition[qexp] defines a form by the explicitly finite QExpansionData qexp.";
QExpansionData::usage = "QExpansionData[data] is an immutable vector q-series: per component an exponent -> coefficient map with exact rational exponents, its cutoff (remainder O(q^cutoff)), arithmetic and binding.";
QExpansionExpression::usage = "QExpansionExpression[qexp, z] gives the components of QExpansionData qexp as finite sums in z with their O[z]^cutoff remainders.";
QExpansionCoefficients::usage = "QExpansionCoefficients[qexp] gives the ordered exponent -> coefficient maps and cutoffs of QExpansionData qexp.";
ModularForm::usage = "ModularForm[id] is a handle to a registered modular form; aliases of one ID observe its validated updates.";
CreateModularForm::usage = "CreateModularForm[c, irrep, k, definition] creates a modular form of exact rational weight k for the irrep of the frozen context c from a ModularFormDefinition, checking shape and rho(S^2) = e^{i Pi k} but not modularity.";
ModularFormData::usage = "ModularFormData[y] gives the immutable record snapshot of the modular form y.";
ModularFormRep::usage = "ModularFormRep[y] gives the actual frozen representation of the modular form y.";
ModularFormWeight::usage = "ModularFormWeight[y] gives the weight of the modular form y, an exact rational.";
ModularFormExpression::usage = "ModularFormExpression[y] gives the component expressions of the modular form y with its resolved coefficients (ApplyCoefficients -> False keeps the raw parameterized definition).";
ModularFormValue::usage = "ModularFormValue[y] gives the computational recipe of the modular form y with its resolved coefficients.";
ModularFormCoefficients::usage = "ModularFormCoefficients[y] gives the coefficient and normalization record of the modular form y, or Missing[\"Unresolved\"].";
ScalarModularExpression::usage = "ScalarModularExpression[name, z] gives the inert scalar modular ingredient name (\"Eta\", \"E2\", \"E4\", \"E6\", \"Delta\", \"j\", \"K\") in the variable z.";
HypergeometricK::usage = "HypergeometricK[a, b, z] gives the inert generalized hypergeometric function with parameters a, b at K(z) = 1728/j.";
Coordinate::usage = "Coordinate is an option of ModularFormDefinition and the scalar recipe functions: \"q\" (default) or \"tau\".";
NormalizationParameters::usage = "NormalizationParameters is an option of ModularFormDefinition: the coefficient symbols of the definition, captured held as FormParameter atoms.";
FamilyID::usage = "FamilyID is an option of ModularFormDefinition: the family whose relative-normalization unknowns the definition shares (Automatic for a new family).";
ScalarQSeries::usage = "ScalarQSeries[expr, var, n] gives the q-series of a scalar expression in var and scalar modular ingredients, keeping exponents below n, as QExpansionData.";
ModularDerivativeExpression::usage = "ModularDerivativeExpression[k, expr, var] gives the modular derivative q d/dq expr - k E2 expr/12 of a scalar expression of weight k.";
ModularDimension::usage = "ModularDimension[c, irrep, k] gives the dimension of the space of weight-k vector-valued modular forms of the irrep, or Missing[\"UnknownDimension\", reason].";
ModularDimensionData::usage = "ModularDimensionData[c, irrep, k] gives the dimension with its method, hypotheses, profile, spectrum and evidence.";
ModularDimensionTable::usage = "ModularDimensionTable[c, irreps, weights] gives an ordered association irrep -> weight -> dimension, keeping zero, Missing and Failure cells.";
ModularWeightProfile::usage = "ModularWeightProfile[c, irrep] gives the weights of a free basis of the module of vector-valued modular forms (ranks 1 to 5), or Missing[\"UnknownProfile\", reason].";
MinimumModularWeight::usage = "MinimumModularWeight[c, irrep] gives the smallest weight with a nonzero form, from the profile or a bounded search.";
ModularFormExistQ::usage = "ModularFormExistQ[c, irrep, k] gives True or False for an established dimension and Missing for an unknown one.";
CleanModularDimensionCache::usage = "CleanModularDimensionCache[c] removes the derived dimension cache entries of the group of c (All: every entry) and reports the count.";
DimensionCache::usage = "DimensionCache is an option of the modular dimension functions: True (default) caches derived dimensions by the actual modular representation.";
WeightSearchLimit::usage = "WeightSearchLimit is an option of MinimumModularWeight: the largest weight searched when no profile is available (default 20).";
ConstructModularForms::usage = "ConstructModularForms[c, irrep] gives the list of generating modular forms the recipe for the irrep supplies (eta, hypergeometric or MLDE), with unresolved relative normalization.";
SeriesOrder::usage = "SeriesOrder is an option of the modular-form constructors, coefficient solvers and evaluators: Automatic or a positive integer order of the q-series used.";
CoefficientResult::usage = "CoefficientResult[data] is an immutable report of a normalization solve: Rules, the numeric fit, exact candidates, the anchor, evidence and ProofStatus.";
SolveModularCoefficients::usage = "SolveModularCoefficients[c, r, k, definition] fits the relative-normalization unknowns of a raw definition of weight k for the representation r of c, without changing anything.";
ModularFormGetCoeff::usage = "ModularFormGetCoeff[y] resolves the relative-normalization coefficients of the modular form y and commits them atomically; it returns y.";
NormalizationRules::usage = "NormalizationRules is an option of the coefficient solvers: Automatic or explicit rules parameter ID -> value, checked through the same evidence path.";
RequireProof::usage = "RequireProof is an option of the coefficient solvers and ValidateModularForm: True refuses results that are not Proven. No implemented route produces Proven at present (no exact identity certificate; the S check is sampled), so RequireProof -> True currently refuses every result.";
TimeLimit::usage = "TimeLimit is an option of the expensive modular-form computations: a positive number of seconds (default 600) or Infinity.";
ModularFormQExp::usage = "ModularFormQExp[y, n] computes the q-expansion of the modular form y below order n and stores it in y atomically; it returns y.";
ModularFormDerivative::usage = "ModularFormDerivative[y] gives the modular derivative D_k y = q dy/dq - k E2 y/12 as a new modular form of weight k + 2.";
ChangeModularFormBasis::usage = "ChangeModularFormBasis[y, b] gives the modular form b . y with representation b rho b^-1 as a new object, without rescaling.";
ModularFormEvaluate::usage = "ModularFormEvaluate[y, point] evaluates the modular form y at TauPoint[tau] or QPoint[q, sheet] by an adaptive q-series and reports the value with its evidence.";
EvaluateScalarModular::usage = "EvaluateScalarModular[expr, var, point] evaluates a scalar modular expression at TauPoint[tau] or QPoint[q, sheet].";
ValidateModularForm::usage = "ValidateModularForm[y] gives a read-only report of the record, parity, exact T expansion, recipe, normalization and numerical S checks of the modular form y.";
TauPoint::usage = "TauPoint[tau] is a point of the upper half plane (Im tau > 0).";
QPoint::usage = "QPoint[q, sheet] is the point with q = Exp[2 Pi I tau] and log q = Log[q] + 2 Pi I sheet (0 < |q| < 1); QPoint[0] is the cusp.";
MaxSeriesOrder::usage = "MaxSeriesOrder is an option of the modular-form evaluators: the largest series order an adaptive evaluation may use (default 2000).";
ApplyCoefficients::usage = "ApplyCoefficients is an option of ModularFormExpression, ModularFormValue and ModularFormQExp: True (default) applies the resolved coefficients, False keeps the parameterized definition.";

FormComponent::usage = "FormComponent[slotID, i] is the inert i-th component of a formal modular-form slot of a modular model (a symbolic Y copy).";
CreateModularModel::usage = "CreateModularModel[c, fields, FieldWeights -> <|id -> kf, ...|>] gives an empty model whose fields carry exact rational weight labels kf (actual weight -kf) and whose target has actual weight SuperpotentialWeight.";
FieldModularWeight::usage = "FieldModularWeight[m, f] gives the weight label kf of the field f of the modular model m.";
WeightedRepVector::usage = "WeightedRepVector[data] is a representation-valued vector with one actual modular weight (an exact rational) per channel (and the form-slot records its channels use).";
MakeWeightedRepVector::usage = "MakeWeightedRepVector[v, weights] attaches one actual weight (an exact rational) to every channel of the RepVector v (weights keyed by channel ID or record position).";
WeightedFieldVector::usage = "WeightedFieldVector[m, {f1, ...}] gives the weighted vector of the listed fields of the modular model m, each channel with actual weight -kf.";
JoinWeightedRepVectors::usage = "JoinWeightedRepVectors[{w1, ...}] concatenates weighted vectors of one context.";
TensorProductWeightedVectors::usage = "TensorProductWeightedVectors[c, {w1, ...}] multiplies weighted vectors through CG duals; each channel's weight is the sum of its factors' weights.";
WeightedVectorData::usage = "WeightedVectorData[w] gives the vector, channel IDs, weights, form slots, candidate report and selection of the weighted vector w.";
ModularFormCandidates::usage = "ModularFormCandidates[m, factors] gives the formal modular-form spaces and copies (slots) a product of fields of the modular model m needs to reach its target at the model's weight, with their counts and completeness.";
ModularFormCandidateData::usage = "ModularFormCandidateData[data] is the immutable candidate report of ModularFormCandidates: Complete, Slots, Spaces, Unknown, Combinations, TargetIrreps and Factors.";
ModularTensorProductVectors::usage = "ModularTensorProductVectors[m, factors] gives every representation-valued channel of the model's fields times formal modular-form copies (all copies, paths and zeros) for TargetIrreps, with total actual weight kW.";
ModularContractions::usage = "ModularContractions[m, factors] gives every contraction of the model's fields with formal modular-form copies into the model's degree-one target as a ContractionSet.";
FormSelection::usage = "FormSelection is an option of ModularContractions and ModularTensorProductVectors: All (exhaustive, needs every relevant count) or a list of slot IDs of the candidate report.";
AddModularFormCouplings::usage = "AddModularFormCouplings[m] multiplies every used formal form slot of the modular model m by its own physical coupling in every term (recorded, so repeating it adds nothing); AddModularFormCouplings[m, slotIDs] selects slots.";
FormCouplings::usage = "FormCouplings is an option of AddModularFormCouplings: Automatic (a fresh coupling per selected slot) or an association from the selected slot IDs to coefficients.";
BindModularForms::usage = "BindModularForms[m, <|slotID -> y, ...|>] binds Stage 7 modular forms to formal slots of the modular model m as frozen snapshots, after exact compatibility, validation and independence checks.";
ModularFormBindings::usage = "ModularFormBindings[m] gives the frozen form bindings of the modular model m by slot ID.";
ValidateModularModel::usage = "ValidateModularModel[m] gives the layered report of the modular model m: schema, formal covariance and total weight, and binding completeness, membership and independence evidence.";
EvaluateModularModel::usage = "EvaluateModularModel[m, point] evaluates the expression of the modular model m at TauPoint[tau] or QPoint[q, sheet] with its bound forms, ParameterValues and FieldValues; EstimatedError is the output's own estimate, and amplification refines the form series or fails with OutputAccuracy.";
EvaluateModularMassMatrix::usage = "EvaluateModularMassMatrix[m, mass, point] validates the matrix against the modular model m and evaluates its entries at the point with the bound forms and the given inputs; EstimatedError is the matrix's own estimate (largest entry), as for EvaluateModularModel.";
SetIrrepLabels::usage = "SetIrrepLabels[g, {l1, l2, ...}] sets the user labels of the irreps of g in irrep order (None for no label); SetIrrepLabels[g, <|irrep -> label, ...|>] adds or replaces labels of irreps given by index or ID. Labels such as 1, 1', 2^{iv}, \\hat{3} or \\rep{2}' are stored with the group and shown by every view.";
SetIrrepLabel::usage = "SetIrrepLabel[g, irrep, label] sets the user label of one irrep (index or ID).";
RemoveIrrepLabel::usage = "RemoveIrrepLabel[g, irrep] removes the user label of one irrep.";
RemoveIrrepLabels::usage = "RemoveIrrepLabels[g] removes every user label of the irreps of g.";
IrrepLabel::usage = "IrrepLabel[g, irrep] gives the user label of an irrep (index or ID) as plain text, or Missing[\"NoLabel\"]. IrrepLabel[g, irrep, \"Display\"] gives it typeset as in the views (super- and subscripts, accents); IrrepLabel[g, irrep, \"TeX\"] gives its LaTeX.";
IrrepIndex::usage = "IrrepIndex[g, label] gives the index of the irrep that carries the user label (or has the irrep ID) label.";
SetClassLabels::usage = "SetClassLabels[g, names] sets the names of the conjugacy classes of g (a list in class order, entries name or {name, representative word}, or an association class -> name).";
ReorderGroupClasses::usage = "ReorderGroupClasses[g, order] sets the presentation order of the classes of g (class IDs or a permutation of 1..n).";
SetGroupName::usage = "SetGroupName[g, name] sets the display name of g.";
SetGroupTitle::usage = "SetGroupTitle[g, tex] sets the TeX title of g used by ToLaTeX captions.";
SetCatalogueLabel::usage = "SetCatalogueLabel[g, label] records the modular catalogue label of g (for example \"24-3I\"), which names the group in its display.";
ShowIDs::usage = "ShowIDs is an option of CharacterTableView, RepresentationTable and GroupSummary: True adds the irrep ID column (default False; irreps are shown by index and labels).";
ShowStatus::usage = "ShowStatus is an option of RepresentationTable, RepresentationView and GroupSummary: True shows the status, basis and validation columns with a legend; Automatic (default) shows them only when a row needs attention (not computed, partial, numerical).";
ShowAutomaticLabels::usage = "ShowAutomaticLabels is an option of CharacterTableView and RepresentationTable: False hides the automatic (T-phase) label column.";
IrrepForm::usage = "IrrepForm is an option of TensorDecomposition, TensorIrrepList and CGCacheInformation: \"Index\" (irrep indices), \"ID\" (irrep IDs) or \"Label\" (the irreps' labels).";
IncludeZeros::usage = "IncludeZeros is an option of TensorDecomposition: True keeps the irreps of multiplicity 0.";
RelationString::usage = "RelationString[\"[S^4,(S*T)^3,...]\"] gives the GroupPresentation of a relation string in the v1 / GAP form; BuildGroup and BuildModularGroup accept such a string directly.";
Notices::usage = "Notices is an option of ConfigureVVMFTool: True (default) prints one-line notes such as \"a group 24-3I already exists\".";
LoadGroup::usage = "LoadGroup[label] loads a group computed in the VVMFUse project from the package's library (irreps, S and T, CG coefficients, labels), without GAP; LoadGroup[label, \"Information\"] gives its library entry.";
LibraryGroups::usage = "LibraryGroups[] lists the groups of the package's library with their status.";
Fresh::usage = "Fresh is an option of LoadGroup: True loads a new copy even when the group is already loaded.";
AllowDuplicates::usage = "AllowDuplicates is an option of SetIrrepLabels: True allows two irreps with the same label.";
SupplyModularFormSpace::usage = "SupplyModularFormSpace[m, {y1, ...}] establishes, for the modular model m, the space of the forms' irrep and weight from the supplied independent forms when Stage 7 has no count (for example a rational weight on a cover of SL(2,Z)); the space gets status Supplied and slots, and a model using it is never Proven.";
ReplaceBindings::usage = "ReplaceBindings is an option of BindModularForms: True replaces existing bindings of the given slots (the combined set is checked again).";
RequireBindings::usage = "RequireBindings is an option of ValidateModularModel: True requires every used slot bound with full independent coverage of its space.";
FieldValues::usage = "FieldValues is an option of the modular model evaluators: an association from field IDs to full ordered vectors of finite values.";
(* Weights, the option of ModularDimensionTable, is the System symbol (its usage is left untouched). *)
FieldWeights::usage = "FieldWeights is an option of CreateModularModel: an association from every field ID to its weight label kf, an exact rational such as 1/2 (actual weight -kf).";
SuperpotentialWeight::usage = "SuperpotentialWeight is an option of CreateModularModel: the actual modular weight kW (an exact rational) of the model's target expression (default 0).";

PrepareModularFormOutput::usage = "PrepareModularFormOutput[<|name -> y, ...|>] gives a ModularFormOutput: an immutable export snapshot of named modular forms with frozen records, shared dependencies and a digest.";
ModularFormOutput::usage = "ModularFormOutput[data] is the immutable export snapshot of named modular forms made by PrepareModularFormOutput.";
ModularFormView::usage = "ModularFormView[y] gives a DisplayDocument of the modular form y: representation, weight, definition, expression, stored q-expansion, normalization and evidence.";
ModularFormTable::usage = "ModularFormTable[{y1, y2, ...}] gives a DisplayDocument tabulating modular forms in the given order, with per-row group and assignment metadata.";
QExpansionView::usage = "QExpansionView[y] or QExpansionView[qexp] gives a DisplayDocument of a stored q-expansion with its cutoff; a missing expansion is shown as not computed.";
ModularDimensionView::usage = "ModularDimensionView[table] gives a DisplayDocument of a ModularDimensionTable result, keeping zero, unknown and failed cells distinct.";
FormSlotTable::usage = "FormSlotTable[m] gives a DisplayDocument of the form slots of the modular model m: labels, weights, copies, use and frozen bindings.";
SaveModularFormData::usage = "SaveModularFormData[<|name -> y, ...|>, file] or SaveModularFormData[y, file] saves modular forms (records, definitions, coefficients, stored expansions, evidence) and their group as a validated JSON archive.";
ImportModularFormData::usage = "ImportModularFormData[file] imports a modular form archive as fresh independent ModularForm handles, after validating every record against the admitted group.";
FormEvaluation::usage = "FormEvaluation is an option of ToPython for modular outputs: \"Embedded\" (the module evaluates the bound forms) or \"External\" (the caller supplies form_values).";
ExportEvaluationMethod::usage = "ExportEvaluationMethod is an option of ToPython for modular outputs: Automatic (\"QSeries\"), \"QSeries\", \"FiniteSeries\" (with SeriesOrder) or \"Analytic\" (unavailable).";
FormLabels::usage = "FormLabels is an option of ModularFormView and ModularFormTable: an association from form IDs to label strings or TeXFragment values.";
FormSlotLabels::usage = "FormSlotLabels is an option of FormSlotTable and the model views: an association from form-slot IDs to label strings or TeXFragment values.";
ExpressionMode::usage = "ExpressionMode is an option of ModularFormView and ModularFormTable: \"Normalized\" (stored resolved coefficients substituted) or \"Raw\" (normalization parameters shown).";
MaxQTerms::usage = "MaxQTerms is an option of the modular views: the number of known nonzero q-series terms shown per component (default 6), or All.";
FactorQSeries::usage = "FactorQSeries is an option of the modular views: True factors out the leading q power (and coefficient) when the leading term is established nonzero.";
IncludeWeight::usage = "IncludeWeight is an option of ModularFormTable: True (default) shows a column of the actual weight k.";

SetAttributes[{FieldComponent, Coupling, FormComponent}, NHoldAll];
Protect[Defaults];
Protect[GAPExecutable, CacheDirectory, StoreGAPState, ComputeRepresentations,
    ComputeElements, ComputeSubgroups, SubgroupDescriptions, CharacterMethod, GroupModel,
    AttemptTimeLimit, CoreBudget, MemoryBudget, ProgressFunction, Name, GeneratorNames,
    ConstructionDependencies, ValidationGroup, SubgroupKind, SubgroupOrder, SubgroupIndex,
    IndexMode, MaxResults, SmallGenerators, MaxBytes, Basis, RepresentationMethod, MethodData,
    UnitarizationMethod, FormFactorizationMethod, DiagonalizationMethod, Arithmetic, TPhaseOrder, PhaseConvention,
    IsomorphismMethod, TargetRepresentations, CacheKinds, MatrixSet, IrrepLabels, ClassOrder, RowOrder, ScalarNotation,
    OneByOneMatrix, NotationStyle, DefineOmega, Digits, Caption, Standalone, PageSize, DisplayTimeLimit, Overwrite,
    Normalization, ExchangeSymmetry, Prefilter, NumberField, FieldMethod, Verification, Recompute, ReversePairs, WordRecovery, WitnessVariant, Route, DimensionMethod, ComputeMissingRepresentations, TargetIrreps, ComponentLabel, ComponentLists,
    TargetIrrep, ChannelPolicy, Couplings, CouplingPrefix, ParameterSymbols, QuadraticConvention, RequirePure,
    ParameterValues, PythonBackend, FunctionNames, ParameterNames, CommonSubexpressions, FieldLabels, CouplingLabels, MassMatrices,
    Coordinate, NormalizationParameters, FamilyID, ApplyCoefficients, DimensionCache, WeightSearchLimit, SeriesOrder, NormalizationRules, RequireProof, TimeLimit, MaxSeriesOrder,
    FieldWeights, SuperpotentialWeight, FormSelection, FormCouplings, ReplaceBindings, RequireBindings, FieldValues,
    FormLabels, FormSlotLabels, ExpressionMode, MaxQTerms, FactorQSeries, IncludeWeight, FormEvaluation, ExportEvaluationMethod];

Begin["`Private`"];

(*
    Summary: Load all implemented modules in their dependency order.
    Parameters: root — existing absolute package directory.
    Options/defaults: None.
    Returns: True, or Failure["PackageLoadFailed", data].
    Effects: Installs definitions once; performs no GAP or front-end work.
    Failures: Missing/failed modules do not set the completed-load flag; retry is allowed.
    Example: loadModules[$PackageRoot] returns True after successful initialization.
    Remarks: All required paths are checked before any module is evaluated.
        Modules preserve already initialized state when retried after a partial load.
    See also: Kernel/init.m; Get.
*)
loadModules[root_String] := Module[{paths, result, failedPath = None},
    If[TrueQ[$ModulesLoaded], Return[True]];
    paths = FileNameJoin[{root, "Kernel", #}] & /@ {
        "Diagnostics.wl", "ScalarCodec.wl", "RepresentationStorage.wl", "GroupWords.wl", "GroupInput.wl",
        "ProcessIO.wl", "Configuration.wl", "Progress.wl", "GAPDiscovery.wl",
        "GAPOperations.wl", "ResultValidation.wl", "GroupMapValidation.wl", "SubgroupValidation.wl",
        "GroupObject.wl", "OwnedProcesses.wl", "JobScheduling.wl", "ArtifactIO.wl",
        "ManagedFiles.wl", "GroupCache.wl", "GAPProtocol.wl", "GAPWorkers.wl",
        "CheckpointStorage.wl", "CheckpointCalls.wl", "GAPJobs.wl", "GroupConstruction.wl",
        "CheckpointRestore.wl", "GroupJobs.wl", "RepresentationJobs.wl", "GroupEnrichment.wl", "GroupSubgroups.wl",
        "GroupMaps.wl", "NormalSearchValidation.wl", "NormalSearch.wl", "GroupIdentity.wl", "Representation.wl",
        "RepresentationValidation.wl", "RepresentationBasis.wl", "RepresentationDecomposition.wl", "RepresentationState.wl",
        "ExportLedger.wl", "GroupSnapshots.wl", "GroupStorage.wl", "IrrepIndex.wl", "GroupLabels.wl", "Library.wl",
        "DisplayLabels.wl", "DisplayData.wl", "DisplayNotation.wl", "ReadableNumbers.wl", "LaTeXDisplay.wl", "NotebookDisplay.wl", "DisplayExport.wl",
        "TensorCharacters.wl", "CGLinear.wl", "CGValidation.wl", "CGProjection.wl", "CGAdvanced.wl", "CGData.wl", "CGStore.wl", "CGNative.wl", "CGRace.wl", "RepVectors.wl", "TensorDisplay.wl", "Fields.wl", "Contractions.wl", "Couplings.wl", "Models.wl", "MassMatrices.wl",
        "PythonIR.wl", "ModelOutput.wl", "PythonExport.wl", "ModelDisplay.wl", "ModelSerialization.wl",
        "ModularSeries.wl", "ModularFormObjects.wl", "ModularScalars.wl", "ModularDimensions.wl", "ModularConstructors.wl", "ModularNormalization.wl", "ModularOperations.wl", "ModularEvaluation.wl",
        "ModularModels.wl", "WeightedVectors.wl", "ModularCandidates.wl", "ModularContractions.wl", "ModularCouplings.wl", "ModularBindings.wl", "ModularModelEvaluation.wl", "ModularPythonIR.wl",
        "ModularDisplayNodes.wl", "ModularDisplay.wl", "ModularOutput.wl", "ModularSerialization.wl"
    };
    If[!AllTrue[paths, FileExistsQ],
        Return[Failure["PackageLoadFailed", <|
            "MessageTemplate" -> "A required package module is missing.",
            "Files" -> Select[paths, !FileExistsQ[#] &]
        |>]]
    ];
    Do[
        result = Block[{$Context = "VVMFTool`Private`",
            $ContextPath = {"VVMFTool`", "System`"}}, Check[Get[path], $Failed]];
        If[result === $Failed || FailureQ[result],
            failedPath = path;
            Break[]
        ],
        {path, paths}
    ];
    If[failedPath =!= None,
        Return[Failure["PackageLoadFailed", <|
            "MessageTemplate" -> "A package module could not be initialized.",
            "File" -> failedPath, "Cause" -> result
        |>]]
    ];
    $ModulesLoaded = True
];
loadModules[___] := Failure["PackageLoadFailed", <|
    "MessageTemplate" -> "The package root must be a directory path string."
|>];

(* Package-owned path and load status; no user directory or notebook state is read. *)
If[!StringQ[$PackageRoot], $PackageRoot = DirectoryName[$InputFileName]];
$LoadResult = loadModules[$PackageRoot];
If[$LoadResult === True, reconcileStoredDefaults[]];

End[];
EndPackage[];
VVMFTool`Private`$LoadResult
