(* ===================================================================== *)
(*  APEX — an IN-PROCESS swap of a KERNEL PRIMITIVE, under the WHOLE       *)
(*  running prover, on the real `cake`/Candle binary.                       *)
(*                                                                         *)
(*  candle/kernel.ml was re-architected so the kernel interface `REFL` the  *)
(*  ENTIRE prover calls is a live indirection (`_apex_refl`), installed     *)
(*  BEFORE the derived layer loads. The verified primitive `Kernel.REFL`    *)
(*  (compiled into cake.S) is untouched — so every swap is SOUND BY         *)
(*  CONSTRUCTION: any implementation must mint its `thm` through the         *)
(*  unforgeable verified `Kernel`, and so can never produce a false theorem.*)
(*  The gate (`apex_swap_refl`) enforces behavioural CORRECTNESS: a          *)
(*  candidate is adopted only if it returns the same theorem as the genuine  *)
(*  `Kernel.REFL` on a battery of checks.                                    *)
(*                                                                         *)
(*  This swaps the kernel primitive the live prover is mid-flight using,     *)
(*  then keeps proving through the swapped primitive; accumulates; rejects   *)
(*  a wrong swap. The verified core stays fixed — that is the safety.        *)
(* ===================================================================== *)

(* (0) the WHOLE prover funnels through the indirected REFL: prove, watch the
       counter climb (every internal REFL call goes through `_apex_refl`). *)
let _ = (_apex_refl_uses := 0);;
let T1 = ARITH_RULE `2 + 2 = 4`;;
let uses_genesis = !_apex_refl_uses;;            (* > 0 : prover used the indirected REFL *)

(* (1) a DIFFERENT but sound REFL: |- tm = tm via TRANS(REFL,REFL) — a distinct
       derivation, built only from verified Kernel primitives. *)
let refl_alt tm = Kernel.TRANS (Kernel.REFL tm) (Kernel.REFL tm);;

(* (2) GATE + SWAP, in-process, while the prover is live. *)
let swap_ok = apex_swap_refl refl_alt [`x:num`; `2 + 2`; `T`; `p /\ q`];;
let swaps_after = !_apex_refl_swaps;;

(* (3) the prover keeps proving — now THROUGH the swapped kernel primitive. *)
let _ = (_apex_refl_uses := 0);;
let T2 = ARITH_RULE `40 + 2 = 42`;;
let uses_after_swap = !_apex_refl_uses;;          (* > 0 : ran on the swapped REFL *)

(* (4) a BAD swap — a wrong REFL that ignores its argument (always |- T = T).
       Still a true theorem (can't forge), but NOT reflexivity-of-tm: the gate
       sees the behavioural mismatch and REJECTS it. *)
let refl_bad tm = Kernel.REFL `T`;;
let bad_ok = apex_swap_refl refl_bad [`x:num`; `2 + 2`];;   (* false *)

(* (5) prover still sound AND correct after the rejection. *)
let T3 = ARITH_RULE `1 + 1 = 2`;;
let verdict =
  if uses_genesis > 0 && swap_ok && swaps_after = 1 && uses_after_swap > 0
     && not bad_ok && concl T2 = `40 + 2 = 42` && concl T3 = `1 + 1 = 2`
  then "KERNEL_INPROCESS_SWAP_OK" else "FAILED";;
