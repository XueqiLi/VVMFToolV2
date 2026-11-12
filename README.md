# VVMFToolV2

Two projects for vector-valued modular forms (VVMFs) and modular flavour symmetry, in the Wolfram Language. Each folder
is self-contained and has its own release.

| | [VVMFTool](VVMFTool) | [VVMFHandbook](VVMFHandbook) |
|---|---|---|
| **What it gives** | The group theory of finite modular groups: representations, character tables, tensor products and Clebsch–Gordan coefficients | The q-expansions of the vector-valued modular forms of the handbook |
| **Coverage** | 61 finite modular groups in the library; new groups computed with GAP | 61 finite modular groups, 820 generating VVMFs |
| **Package** | `VVMFToolv2/` | `VVMF_Engine.wl` |
| **Data** | `VVMFToolv2/Library/` | `VVMF_Results_Data.wl` |
| **Notebooks** | <ul><li>`Library.nb` — inspect the library</li><li>`PlayGround.nb` — build a group, modular forms, models</li></ul> | <ul><li>`VVMF_Results.nb` — query the results, LaTeX export</li><li>`VVMF_Compute.nb` — recompute to any order</li></ul> |
| **Needs** | Wolfram Language 15; GAP 4.15 only for new groups | Wolfram Language |
| **Guide** | [`VVMFTool/README.md`](VVMFTool/README.md) | [`VVMFHandbook/README.txt`](VVMFHandbook/README.txt) |
| **Release** | [VVMFTool v2.0.0-alpha](https://github.com/XueqiLi/VVMFToolV2/releases/tag/VVMFTool-v2.0.0-alpha) · [zip](https://github.com/XueqiLi/VVMFToolV2/releases/download/VVMFTool-v2.0.0-alpha/VVMFTool-v2.0.0-alpha.zip) | [VVMFHandbook r6](https://github.com/XueqiLi/VVMFToolV2/releases/tag/VVMFHandbook-r6) · [zip](https://github.com/XueqiLi/VVMFToolV2/releases/download/VVMFHandbook-r6/VVMFHandbook-r6.zip) |

## VVMFTool

Keep `Library.nb` and `PlayGround.nb` next to the package folder `VVMFToolv2/`.

- **Inspect** — open `Library.nb` and evaluate its first input cell, which loads the package from the folder next to
  it (no GAP is started):

  ```wolfram
  LibraryGroups[]                          (* the 61 groups: label, title, GAP ID, order, irreps, status *)
  GroupTp = LoadGroup["24-3I"]             (* T' *)
  RepresentationTable[GroupTp]             (* rho(S), rho(T) of every irrep, with its index, label and name *)
  TensorDecompositionView[GroupTp, {4, 5}] (* 2 x 2' = 1 + 3 *)
  va = MakeRepVector[GroupTp, 4, a]; vb = MakeRepVector[GroupTp, 5, b];
  VectorComponents[TensorProductVectors[GroupTp, {va, vb}]]   (* CG coefficients as polynomials in a[i], b[j] *)
  ```

  Groups are labelled by their GAP id, with I or II where a group has several realizations (`24-3I` is T',
  `24-3II` is 2T); irreps are referred to by their index in `RepresentationTable`.
- **Compute** — build a group that is not in the library from a presentation, a GAP catalogue id or GAP itself
  (needs GAP 4.15); `PlayGround.nb` builds a group in GAP and goes on to tensor products,
  modular forms and model building. From any other notebook, load the package with
  `Get[FileNameJoin[{"<path to>/VVMFToolv2", "Kernel", "init.m"}]]`.
- **Verification** — every stored result carries its status ("Exact", "Numerical" or "Unverified"); the library holds
  exactly verified data only, bound to its files by `VVMFToolv2/Library/ledger`.

Details are in [`VVMFTool/README.md`](VVMFTool/README.md); reference pages are in
`VVMFToolv2/Documentation/English/ReferencePages/Symbols`.

## VVMFHandbook

Keep the four files `VVMF_Compute.nb`, `VVMF_Engine.wl`, `VVMF_Results.nb` and `VVMF_Results_Data.wl` together.

- **Query** — open `VVMF_Results.nb` and evaluate its first input cell, which loads `VVMF_Results_Data.wl` next to
  it:

  ```wolfram
  VVMFNames["72-42"]              (* the generators of [72,42]: Y72x42R1One, ..., Y72x42R3pF, ... *)
  Y72x42R3pF[q, 2]                (* components to relative order 2: q^(1/12) + 2 q^(13/12) - 5 q^(25/12) + O(q^(37/12)), ... *)
  VVMFTeX["Y72x42R3pF", 2]        (* LaTeX, with any algebraic parameters defined *)
  VVMFStatus[]                    (* Ready, data version, stored order, 820 vectors, 174 independent models *)
  ```

  Names are `Y<n>x<k>…R<irrep name>…` for the group with GAP id [n,k], with I or II where a group has several
  realizations, and the irrep's name with primes written `p`, `pp`, … (not its index in VVMFTool). Without an order a
  function uses the order stored in the data file; keep `q` unassigned.
- **Compute** — open `VVMF_Compute.nb` (it needs only `VVMF_Engine.wl`), set `qOrder = 20;` (or any order) and
  evaluate the notebook; it writes `VVMF_Results_Data.wl`, checked by reading it back.
- **Verification** — `validation/` records the checks of the stored coefficients against the exact reference data
  and of the file round trip.

Details (in Chinese) are in [`VVMFHandbook/README.txt`](VVMFHandbook/README.txt).
