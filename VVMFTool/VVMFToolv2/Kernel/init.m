(*
    :Title: VVMFTool package entry point
    :Context: VVMFTool`
    :Summary: Load the package relative to this entry point.
    :Responsibilities: Resolve source files without changing the working directory.
    :Dependencies: VVMFTool.wl in the package root.
    :See Also: VVMFArch/step1Plan.md
*)
Get[FileNameJoin[{DirectoryName[DirectoryName[$InputFileName]], "VVMFTool.wl"}]]
