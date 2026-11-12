# VVMFToolv2

The VVMFTool v2 package for the Wolfram Language. Load it with

```wolfram
Get[FileNameJoin[{"<path to>/VVMFToolv2", "Kernel", "init.m"}]]
```

- `Kernel/` — the package; `VVMFTool.wl` lists its public symbols.
- `GAP/` — the GAP side (needed only to compute new groups; GAP 4.15 with json and io).
- `Library/` — 61 fully verified groups for `LoadGroup` (`LibraryGroups[]` lists them); do not edit these files.
- `Documentation/` — reference pages, one notebook per symbol (`Documentation/English/ReferencePages/Symbols`).
- `Schemas/`, `Data/` — formats of saved files and package data. `StyleGuide.md` — the code conventions.

The notebooks `Library.nb` and `PlayGround.nb` next to this folder show it in use; see `../README.md`.
