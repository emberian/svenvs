(* CakeML's verified parser on Obend's beltLatch.pnk, the proved optimizer's
   output printed and parsed back, and their agreement (pancakeKernelLib). *)
Theory obendBeltLatch
Ancestors
  pancakeKernel
Libs
  pancakeKernelLib

val _ = pancakeKernelLib.ingest "beltLatch"
