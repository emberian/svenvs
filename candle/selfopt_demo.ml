(* ===================================================================== *)
(*  A LIVE SELF-OPTIMIZATION LOOP, certified by the running Candle kernel. *)
(*  The prover (1) proves a new rule SOUND, (2) ADOPTS it as a reusable    *)
(*  derived inference rule — its toolkit grows, safely — and (3) USES the  *)
(*  new capability to prove fresh theorems, then (4) ITERATES. Every step   *)
(*  is certified by the verified kernel (each `val NAME = |- ...` echo).    *)
(*  This is the LCF self-extension discipline = self-optimization: the      *)
(*  prover improves its own proven-safe rule set and continues running.    *)
(* ===================================================================== *)

(* (1) prove the new rule sound (the inhabitant's testimony, kernel-checked) *)
let SYM_LEMMA = prove (`!(a:A) b. a = b ==> b = a`, MESON_TAC[]);;

(* (2) ADOPT it as a reusable derived rule — self-extension. SYM_RULE can
       only ever build VALID thms: it is MATCH_MP of a proven theorem (the
       LCF discipline makes the new capability safe by construction). *)
let SYM_RULE (th:thm) : thm = MATCH_MP SYM_LEMMA th;;

(* (3) USE the adopted capability to prove fresh theorems, live. *)
let FACT1 = ARITH_RULE `1 + 1 = 2`;;
let FACT1_SYM = SYM_RULE FACT1;;            (* |- 2 = 1 + 1, via the new rule *)

(* (4) ITERATE — the adopted rule composes into further capability. *)
let SYM_TWICE (th:thm) : thm = SYM_RULE (SYM_RULE th);;
let FACT1_ROUNDTRIP = SYM_TWICE FACT1;;     (* |- 1 + 1 = 2, round-tripped *)
