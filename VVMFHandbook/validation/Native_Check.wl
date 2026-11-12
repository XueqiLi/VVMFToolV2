(* Optional native Mathematica check. Run after the first Results notebook cell.
   This file is not a dependency of either notebook. *)
TestReport[{
  VerificationTest[VVMFStatus[]["Version"],6,TestID->"revision"],
  VerificationTest[VVMFStatus[]["Ready"],True,TestID->"ready"],
  VerificationTest[Length[VVMFNames[]],820,TestID->"generator-count"],
  VerificationTest[Length[$VVMFModels],174,TestID->"model-count"],
  VerificationTest[Y72x42R3pF[],Y72x42R3pF[q,$VVMFMaxOrder],TestID->"default-order"],
  VerificationTest[VVMFGet["72-42|3'|1",Min[4,$VVMFMaxOrder]]["Coefficients"][[1]],
    Take[{1,2,-5,-10,9},Min[4,$VVMFMaxOrder]+1],TestID->"sample-coefficients"],
  VerificationTest[StringQ[VVMFTeX["Y72x42R3pF",0]],True,TestID->"latex-output"]
}]
