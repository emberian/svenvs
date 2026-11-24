(* CakeML's verified parser on Obend's macaroonVerify.pnk, the proved optimizer's
   output printed and parsed back, and their agreement (pancakeKernelLib). *)
Theory obendMacaroonVerify
Ancestors
  pancakeKernel
Libs
  pancakeKernelLib

val _ = pancakeKernelLib.ingest "macaroonVerify"
