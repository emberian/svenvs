(* CakeML's verified parser on Obend's keccakF1600.pnk, the proved optimizer's
   output printed and parsed back, and their agreement (pancakeKernelLib). *)
Theory obendKeccakF1600
Ancestors
  pancakeKernel
Libs
  pancakeKernelLib

val _ = pancakeKernelLib.ingest "keccakF1600"
