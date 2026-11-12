# Group result schemas 1 and 2

This document describes the executable-free GAP/Wolfram interchange record. It does not authorize imported source text or workspace paths to execute. The coordinator establishes producer trust separately from schema and arithmetic validation.

| Field | Value |
| --- | --- |
| schemaVersion | Integer 2 for current producers; schema-1 envelopes (without representationData) remain valid input |
| requestID, stateID, generatorIdentity | Nonempty strings; request ownership, mathematical group identity and ordered-generator identity |
| stateGeneration | Canonical nonnegative decimal integer string |
| operation | Operation registered in `Kernel/GAPOperations.wl` (native dispatch in `GAP/Driver.g`) |
| status | BaseReady, Partial or Complete |
| construction | Retained typed construction record, or an explicit gapCode record with source/dependency data |
| generators | Ordered records with unique id and name strings |
| order | Positive canonical decimal integer string |
| catalogueID | null or the actual order/index pair as decimal strings |
| characterData | null before characters exist; otherwise the record below |
| availableData | Characters, Elements, Subgroups, Representations and Descriptions availability |
| elements, subgroupData, modularAssignment | null when absent; owning stage schemas govern present data |
| representationData | Schema 2 only. null without representation data (availability NotComputed); otherwise the record below. Availability is Complete when every irrep has an active variant, else Partial |
| producer | GAP, kernel/build/architecture and loaded-package versions |
| binding | Finite-group/generation checks; character/class binding checks when characters are present |
| diagnostics | Operation/method/model and diagnostic references, separate from mathematical values |

Scalar values follow the integer/rational/cyclotomic records in the design. Class sizes, element orders, dimensions and degrees are decimal strings. Word syllables in result data use **generator IDs**, followed by signed decimal exponent strings. Typed construction relators use their input generator names. Wolfram decodes result words to public GroupWord expressions on the stored names.

The character record contains identity, irrepIDs, classIDs, values, classSizes, classOrders, classRepresentativeWords, identityClassID, trivialIrrepID and degrees. IDs are unique within each ordered collection. The character identity owns those row/class IDs. A partial table may lack a trivial character, represented by null; a complete table has exactly one.

A retained executable recipe has exactly type="gapCode", code, names and dependencies. Each declared dependency has an absolute path and a lowercase SHA256 digest under sha256. Validation treats these as inert data; it does not execute code or read dependency files. The producer record separately retains GAP/package versions.

GAP output uses the package-local VVMF_JSONString encoder. The installed json 2.2.3 package decodes null to fail but rejects fail in its output boolean method. The local encoder handles null recursively and delegates scalar escaping to the package without altering its global methods.

BaseReady means that a finite generated group can be checkpointed before character attempts. It is not a publishable Wolfram Group. Partial character results remain recoverable backend data. A Group is allocated only with complete, bound, independently checked character data.

A binding record is a producer claim until the coordinator has checked its owned worker protocol, result digest and coherent workspace, or an import has established trusted registered provenance or actual group correspondence. An embedded hash or boolean does not establish trust. In-memory validation receipts are kept outside portable files.

Optional-data schemas and representation data extend this schema through their owning implementations. Unknown populated optional fields are rejected until the appropriate validator is installed.

A populated `modularAssignment` has exactly `identity`, `sWord`, `tWord` and `verified=true`.
Both words use recorded generator IDs. The native producer rechecks S^4=1, (ST)^3=1,
centrality of S^2 and generation of the entire actual group before each export. Wolfram
decodes this as `Identity`, `S`, `T` and `Verified`, with GroupWord values. The decoder
checks structure and any explicit requested assignment; a portable verification flag
does not replace native provenance. A null assignment remains `Missing["NotAssigned"]`.

A populated `elements` field is a complete list of recorded-generator words. Its length
equals the group order and `availableData.Elements` is `"Complete"`. Native export
evaluates all words and verifies that they give distinct actual elements. Wolfram also
checks the word schema, length and syntactic duplicates. This payload is exposed by
`GroupElementWords` and stored in the group's `"Elements"` property.

For `GroupWordOrder`, `diagnostics.wordOrder` contains exactly `word` (generator-ID
syllables) and `order` (positive decimal string). The order divides the group order;
the coordinator matches the word to the request. Native reexport recomputes its order.

Complete catalogue constructions include `binding.generatorPresentation`; other complete
constructions may carry it after explicit certification. This is a typed presentation
on the exact recorded generator names. GAP certifies it using a bijective
map preserving every ordered generator. The trivial-group certificate kills every
recorded generator. Its proven finite order is the original owned group's order.
Typed reconstruction verifies equal order, actual generation and every certified
relator, establishing the prescribed generator isomorphism before transferring any
accepted characters. Direct permutation/matrix inputs and quotient presentations
already determine their generators through their literal construction.

Reconstruction evaluates accepted class words in the rebuilt group and checks a
bijection with matching class sizes/orders. Certified rows are transported through
that bijection. Reexport checks their values against the native rows while retaining
the original class/irrep IDs, ordering and words. The certificate and rows must come
from independently accepted data; importing these fields alone never supplies trust.

A populated `subgroupData` is an ordered list of records containing `query`, `items`,
`complete=true` and `provenance`. The query has `id`, `kind` (ConjugacyClasses, All or
Normal), positive decimal `order`/`index` filters or null, and a `descriptions` Boolean.
The query ID identifies its kind and filters; method/model and description enrichment
do not change that mathematical selection.

Each item contains `id`, `generatorWords`, `order`, `index`, `normal`, `classID`,
`classSize` and `description`. Words preserve the subgroup's actual embedding in the
recorded group. Order, index and conjugacy-class size are decimal strings. A null
description is uncomputed. A class-mode item is its chosen embedded representative;
all mode gives distinct embedding IDs to conjugate subgroups, sharing only class ID
and description. Descriptions are computed once per known class. Query provenance
records `stateID`, `requestID`, `method` and `model`.

Wolfram exposes a query under `SubgroupData[queryID]` with `QueryID`, `Items`, `Kind`,
`Filters`, `Complete`, `Descriptions` and `Provenance`. Item properties are `SubgroupID`,
`GeneratorWords`, `Order`, `Index`, `Normal`, `ConjugacyClassID`, `ConjugacyClassSize`
and `Description`. Filling descriptions preserves the accepted representative, item
ordering, words and identities. `availableData.Subgroups` lists each query's `QueryID`,
`Status="Complete"` and description status. Overall description availability is
NotComputed, Partial or Complete across those stored queries. An empty computed
query remains a complete record with `Items->{}`.

Reconstruction transports certified complete collections through the verified group
isomorphism. GAP rebuilds each actual subgroup from saved words, checks its invariants
and conjugacy, and requires exact equality of its native reexport. That does not
establish completeness for an unrecognized imported collection without separate
provenance validation. Portable booleans and descriptive strings do not prove it.

For `CheckGeneratorMap`, `diagnostics.generatorMap` contains Boolean `homomorphism`,
`injective`, `surjective` and `isomorphism`; `imageWords` (one named target word per
source generator); and `inverseImageWords` (named source words for target generators
only for an isomorphism, otherwise null). Unlike general result words, these words
use the named source/target namespaces recorded in the map. The report also contains
`sourceStateID`, `sourceGeneratorIdentity`, `targetStateID`, `targetGeneratorIdentity`,
`targetNames` and decimal `targetOrder`. Identities, requested images, arities and flag/order
invariants are matched by Wolfram; the restored native worker rechecks the actual map.

A map request supplies an independently accepted target presentation certificate and
its finite order. GAP reconstructs precisely those target generators and retains the
actual target/map in the accepted source state. Certificate preparation is an internal
`GeneratorPresentation` enrichment. It requires a live accepted checkpoint or typed
reconstruction and is verified through the ordinary saved-state protocol. A certificate
already bound to a live group is sufficient for its use as a target after workspace
eviction, including a raw-code target; target construction does not execute that code.
An imported certificate alone never establishes such provenance.

## Worker checkpoint protocol

GAP/Driver.g emits one unwrapped line beginning with VVMF_PROTOCOL followed by a tab and JSON. checkpointReady contains requestID, stateID, generatorIdentity, stateGeneration, status, resultPath and workspacePath after the new JSON file has been written through an exclusive sibling temporary file and renamed. The paired workspace path is resultPath plus .wsp. Atomic output requires GAP packages json and io, reported by CheckGAP.

Only after matching readiness does the coordinator send a literal main-input SaveWorkspace command, followed by VVMF_ReportCheckpoint. checkpointSaved requires the actual save return value and nonempty regular result/workspace files. A failure packet never substitutes for readiness or completion.

A fresh restored process calls VVMF_ReportRestored with a new nonce. It revalidates the native state, exports it again, compares that envelope to the globally rooted saved envelope, and emits checkpointRestored with the nonce, original checkpoint request ID, mathematical identities, generation and status. The coordinator separately checks paths, ownership, artifact digests, build compatibility and publication before accepting a candidate.

For acceptance, VVMF_VerifyCheckpoint additionally writes the revalidated native envelope to a separate owned verification file and emits checkpointVerified. The coordinator must compare that file to the saved candidate JSON. This is required even when the request/identity/generation packet matches: otherwise a changed JSON character table could retain arithmetic invariants while no longer matching its workspace. checkpointRestored alone is not paired-artifact acceptance.

`representationData` is keyed by irrep ID. Each entry has exactly `dimension` (decimal string equal to
the character degree), `generatorIdentity`, `variants` (nonempty, keyed by variant ID), `activeVariant`
and `acceptedPartial` (variant IDs or null). A variant has `tier` (`Native`, `ScaledNative`, or the
inert `Wolfram` and `Numerical` tiers below), `arithmetic` (`Exact`), `matrices` (one matrix per
recorded generator, rows of integer/rational/cyclotomic scalar records; empty for a group without
generators; every irrational cyclotomic entry also carries `minimalPolynomial`, its primitive integer
minimal polynomial lowest degree first, which the producer recomputes and checks, so consumers obtain the
exact value by root isolation instead of reducing a sum over large conductors), `sourceMethod` (`method`, `model`) and `basisProperties` (`unitary`; `tDiagonal` and
`assignmentIdentity`, both null without a modular assignment). The producer recomputes basis properties
and rechecks class traces on every export. An accepted partial is a nonunitary variant and cannot coexist
with a unitary active variant.

A `ScaledNative` variant additionally has `scales`: one real cyclotomic record per basis vector (the first
exactly 1, not all equal to 1). Its `matrices` are native matrices N, verified in GAP like any native
variant; its visible matrices are F = L N L^-1 with L = DiagonalMatrix[Sqrt[scales]], entries
N_ij Sqrt[sigma_i/sigma_j]. The producer asserts `unitary` from N^dagger S N = S with S = DiagonalMatrix[scales]
and `tDiagonal` from N_T (a diagonal scaling does not change either). GAP cannot order real cyclotomics,
so the consumer must refuse a variant whose scales are not all positive; with positive scales, unitarity
of F follows from the producer's identity. Any variant may have `derivation` (`witness`, a variant ID of
the same irrep, and `conjugator`, a matrix C of representation scalar records with N = C W C^-1 for the
witness's matrices W), which the producer checks on import and the consumer checks for a present witness.
The realization identity of every variant is computed from its visible matrices.

`Wolfram` (arithmetic `Exact`) and `Numerical` (arithmetic `Numerical`, plus `precision`: `MachinePrecision` or
a decimal digit count of at least 16) variants are inert in GAP. Their `matrices` (and an optional
`derivation` conjugator) hold Wolfram representation scalar records: algebraic records (`polynomial`,
`rootRectangle`) or rational/integer records for `Wolfram`, and `numerical` records at the declared
precision for every `Numerical` entry. The coordinator verifies them in Wolfram before sending them (method
`Inert`, request field `inert`) and on correspondence import (relators of a certified presentation, class
values equal to the irrep's character exactly or within the automatic tolerance, recorded unitarity, and
T-diagonality when claimed); the receipt covers them on registered import (R1). GAP checks structure only
and exports the record as received, except `basisProperties`: `tDiagonal` stays true only under the
`assignmentIdentity` it was verified for and is false after a new assignment. A `Numerical` variant has
rank -1: it becomes active only through an explicit mutation (`replaceActive`), never satisfies a request,
and a later exact variant replaces it.
