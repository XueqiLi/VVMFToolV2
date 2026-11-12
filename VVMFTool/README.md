# VVMFTool

- `VVMFToolv2/` — the package VVMFTool v2 for the Wolfram Language: finite groups (from presentations, GAP catalogue
  IDs or GAP), their irreducible representations verified exactly, Clebsch–Gordan coefficients,
  representation-valued vectors and tensor products, contractions and models, and vector-valued modular forms. Every
  stored result carries its verification status ("Exact", "Numerical" or "Unverified").
- `Library.nb` — inspects the package's library of groups: representation tables, character tables, tensor products
  and CG coefficients.
- `PlayGround.nb` — further examples.

## Load

The notebooks load the package from the folder `VVMFToolv2` next to them. From any other notebook:

```wolfram
$VVMFToolV2Root = "<path to>/VVMFToolv2";
Get[FileNameJoin[{$VVMFToolV2Root, "Kernel", "init.m"}]]
```

## Library

`VVMFToolv2/Library/` holds 61 groups computed and fully verified in the VVMFUse project: irreps in the paper's basis,
the S and T assignment, all CG coefficients, element words and the paper's names of irreps and classes.

```wolfram
LibraryGroups[]                 (* label, title, GAP ID, order, irreps, status *)
GroupTp = LoadGroup["24-3I"]
RepresentationTable[GroupTp]
TensorDecompositionView[GroupTp, {4, 5}]
va = MakeRepVector[GroupTp, 4, a];   (* components a[1], a[2] *)
vb = MakeRepVector[GroupTp, 5, b];
VectorComponents[TensorProductVectors[GroupTp, {va, vb}]]
```

A library file is trusted through the read-only ledger in `VVMFToolv2/Library/ledger`: an unchanged file loads without
GAP and without re-checking (`LoadGroup[label, Verification -> "Exact"]` re-checks everything in GAP). Do not edit or
re-save files in `Library/`; a changed byte makes the file untrusted.

## Requirements

- Wolfram Language 15 (tested with 15.0.1).
- GAP 4.15 for anything that computes new groups or representations, with the packages json and io; optional
  packages enable more methods: repsn, InduceReduce, SL2Reps, AtlasRep, LINS (bounded normal-subgroup search).
  `ConfigureVVMFTool[GAPExecutable -> "/path/to/gap"]` selects the executable.

## Documentation

Reference pages: `VVMFToolv2/Documentation/English/ReferencePages/Symbols` (open a page notebook in place, so its
loading cell finds `Kernel/init.m`); see `VVMFToolv2/Documentation/README.md`. The APIs are alpha.
