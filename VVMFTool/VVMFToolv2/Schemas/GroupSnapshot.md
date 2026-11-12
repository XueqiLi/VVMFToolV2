# Mathematical group snapshot schemas 1, 2 and 3

`SaveGroupData` produces inert JSON with exactly these fields:

| Field | Meaning |
| --- | --- |
| `format` | `"VVMFToolGroup"` |
| `schemaVersion` | Integer `3` when the save carries presentation data (the optional keys below), otherwise `2`; schema `1` (without `irrepOrder`) remains importable |
| `name` | Display-name string |
| `group` | Complete [group-result envelope](GroupResult.md), including exact characters and computed optional mathematics |
| `gapCache` | `null`, or the retained reference below |
| `irrepOrder` | Schemas 2 and 3: the saved presentation order, a permutation of the character table's irrep IDs. Not mathematical data: it is outside the digested group envelope and identity bindings. Schema 1 imports use the canonical order |
| `representationCacheEpoch` | Schemas 2 and 3, optional (absent means 0): decimal string, the derived representation-cache eviction epoch (CleanRepresentationCache). Outside the digested envelope; derived cache entries themselves are recomputable and are not saved. Import restores the epoch with an empty cache |
| `irrepLabels` | Schema 3, optional: irrep ID -> user label in its plain grammar text (SetIrrepLabels; e.g. `2^iv`, `\hat{3}'`) |
| `classLabels` | Schema 3, optional: class ID -> `{"name": plain class label, "representative": word string or null}` (SetClassLabels) |
| `classOrder` | Schema 3, optional: presentation order of the classes, a permutation of the class IDs (ReorderGroupClasses) |
| `catalogueLabel` | Schema 3, optional: the paper's label (`24-3I`; a catalogue label, or `order-number` + roman suffix matching the GAP ID) |
| `titleTeX` | Schema 3, optional: the paper's TeX title (SetGroupTitle) |

The schema-3 keys are presentation data, like `irrepOrder`: outside the digested envelope, the identity bindings and
every context digest. A schema-2 file whose name is a catalogue label of its own presentation imports with that
catalogue label.

The snapshot is a value, independent of a live kernel handle. It contains no private
validation receipt, registry pointer or executable Wolfram expression. A retained GAP
recipe remains a string. Reading the JSON never executes a recipe or a workspace.

A retained reference has `path` and `metadata`. The path and metadata `Root` are absolute.
Metadata has `Root`, `CacheID`, `EntryID`, `Runtime`, `StateID`, `GeneratorIdentity`,
`StateGeneration` and `LastUsed`. Its mathematical identities and generation match the
group envelope. Generation and last-use time are nonnegative integers. The reference
may outlive its workspace file; it does not authorize loading that file. A later explicit
restore must pass independent managed-cache admission and native state verification.

Saving atomically replaces the requested JSON file, then registers the exact completed
bytes in the independent local export ledger. A failed registration returns `Failure`
with `SavedFile`: the mathematical file remains available, without a claim that its
provenance was registered. Save verifies its input group's private receipt/native envelope,
starts no GAP worker and does not mutate the group.

The ledger defaults to `$UserBaseDirectory/ApplicationData/VVMFTool/ExportLedger`, separately
from configurable `CacheDirectory`. `CleanGAPCache` cannot evict it. Its `ledger.json` has
`SchemaVersion=2` and `Entries`, keyed by lowercase SHA256. Each entry has `Bytes`,
`RegisteredAt`, `Bindings`, `SubgroupClasses`, and `Identity` (`StateID`, `GeneratorIdentity`, `CharacterIdentity`, positive
decimal `Order`). Only a completed independent validation/export operation registers an
entry. Changes occur under a directory lock and an atomic file replacement. Moving an
unchanged snapshot preserves its recognized digest; modifying bytes removes that match.

`Bindings` stores scoped identity-to-mathematics SHA256 fingerprints independently of the
snapshot. Mandatory group/generator/character bindings normalize row and column order by
opaque ID, but preserve each ID's exact recorded data. Optional modular-assignment and
embedded-subgroup bindings are included when present; new optional data and new assignment
identities are permitted. Descriptions and request bookkeeping do not define those bindings.
`SubgroupClasses` stores accepted named-generator witnesses with `StateID`, `GeneratorIdentity`,
`ClassID`, and `Words`. Native import checks actual conjugacy against those witnesses; different
representatives of the same subgroup class remain valid. These witness records are local
provenance, never read from the snapshot as evidence of their own truth.

Before publication, import rejects conflicting known bindings from live accepted groups or
the independent ledger. A fresh unknown identifier may acquire a binding after native
validation. A known identifier cannot be assigned different mathematical data. This includes
valid character tables whose rows or class words were reassigned without their IDs.
Saved subgroup query IDs must match their kind and order/index selection; public cache reuse
also checks that selection. Character ordering changes are accepted when IDs and all associated
rows/columns move consistently. Import does not rewrite recorded words under reused identities.

Schema checks and character orthogonality are necessary but do not prove group/character
correspondence. A digest embedded in a snapshot is neither part of this schema nor independent
provenance.

`ImportGroupData` reads inert JSON between matching file digests and checks the complete
schema. Exact independently registered bytes import without GAP when ValidationGroup is
Automatic, even after cache eviction. The user's ledger is consulted first, then the package's read-only library
ledger (`Library/ledger`, written only by `Tools/UpdateLibrary.wls`): the library's files import through the same
registered path (`LastComputation` Validation `LibraryRegisteredExport`), a modified library file is validated like
any unregistered file (`LibraryFileModified` without GAP), and a save whose identities conflict with the library's
bindings fails at registration. `.gitattributes` keeps `Library/**` byte-exact. A new live handle preserves saved mathematical
identities and ordering. StoreGAPState=False omits the saved cache reference from that
handle without deleting retained files.

An unknown typed snapshot is checked against an independently constructed finite group
and its complete native-bound characters. ValidationGroup supplies an already accepted
native source instead. The native import verifies the ordered generating set, any
presentation certificate, actual class words and complete character rows, all element
words, modular assignment and complete subgroup query selections/descriptions. Consistent
row/class permutations retain their saved IDs. Orthogonal rows attached to wrong class
words fail. Revalidation then saves and freshly restores one coherent candidate before
publishing a Group. The validation source is unchanged.

Unregistered raw recipes require ValidationGroup independently constructed from the same
explicit recipe and recorded generators. Source text is compared as inert metadata and
never replayed by import. Missing raw state must be explicitly rebuilt by the caller.
Explicit ValidationGroup is checked even when the file has a matching ledger entry.
Later computations preserve opaque saved generator, class and irrep IDs through retained
state and verified typed reconstruction. A JSON path, checksum or binding flag cannot
authorize a GAP workspace load.
