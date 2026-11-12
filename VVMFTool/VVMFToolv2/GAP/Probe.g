# Title: GAP capability probe
# Summary: Emit version/package records before the main-input workspace test.
# Effects: Loads available optional packages; no download or mathematical calculation.
# Output: VVMF_PROBE tab-separated records, consumed by parseGAPProbe.
# The coordinator performs SaveWorkspace at the main prompt after reading this file.
Print("VVMF_PROBE\tVersion\t", GAPInfo.Version, "\n");
Print("VVMF_PROBE\tKernelVersion\t", GAPInfo.KernelVersion, "\n");
Print("VVMF_PROBE\tArchitecture\t", GAPInfo.Architecture, "\n");
Print("VVMF_PROBE\tBuildVersion\t", GAPInfo.BuildVersion, "\n");
Print("VVMF_PROBE\tBuildDateTime\t", GAPInfo.BuildDateTime, "\n");
VVMF_PROBE_PACKAGES := ["json", "io", "smallgrp", "ctbllib", "repsn",
    "irredsol", "inducereduce", "lins", "fga", "sl2reps", "repndecomp", "atlasrep"];;
for VVMF_packageName in VVMF_PROBE_PACKAGES do
    LoadPackage(VVMF_packageName);
od;
# AtlasRep is loaded for its version only; remote table access stays disabled.
if IsBound(GAPInfo.PackagesLoaded.atlasrep) then
    SetUserPreference("AtlasRep", "AtlasRepAccessRemoteFiles", false);
fi;
# Include loaded transitive dependencies once; workspace compatibility concerns them too.
for VVMF_packageName in SortedList(RecNames(GAPInfo.PackagesLoaded)) do
    Print("VVMF_PROBE\tPackage:", VVMF_packageName, "\t",
        GAPInfo.PackagesLoaded.(VVMF_packageName)[2], "\n");
od;
for VVMF_packageName in Difference(VVMF_PROBE_PACKAGES,RecNames(GAPInfo.PackagesLoaded)) do
    Print("VVMF_PROBE\tPackage:", VVMF_packageName, "\tunavailable\n");
od;
# Metadata does not load every optional package. An explicit recipe may load a package
# outside the standard method set; its owned producer must match an installed version.
for VVMF_packageName in SortedList(RecNames(GAPInfo.PackagesInfo)) do
    for VVMF_packageIndex in [1..Length(GAPInfo.PackagesInfo.(VVMF_packageName))] do
        Print("VVMF_PROBE\tInstalledPackage:",VVMF_packageName,":",VVMF_packageIndex,"\t",
            GAPInfo.PackagesInfo.(VVMF_packageName)[VVMF_packageIndex].Version,"\n");
    od;
od;
# Distinguishes a restored workspace from an empty new process.
VVMF_PROBE_TOKEN := [17, 23, 42];;
