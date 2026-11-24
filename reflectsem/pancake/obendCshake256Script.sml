(* CakeML's verified parser on Obend's cshake256.pnk, the proved optimizer's
   output printed and parsed back, and their agreement (pancakeKernelLib). *)
Theory obendCshake256
Ancestors
  pancakeKernel
Libs
  pancakeKernelLib

val _ = pancakeKernelLib.ingest "cshake256"
