(* CakeML's verified parser on Obend's kmac256.pnk, the proved optimizer's
   output printed and parsed back, and their agreement (pancakeKernelLib). *)
Theory obendKmac256
Ancestors
  pancakeKernel
Libs
  pancakeKernelLib

val _ = pancakeKernelLib.ingest "kmac256"
