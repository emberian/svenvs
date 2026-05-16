(* ===================================================================== *)
(*  THE PLACE  —  svenvs reflected into HOL Light, checked at runtime by   *)
(*  the verified Candle kernel.                                            *)
(*                                                                         *)
(*  A self-contained, self-verifying habitat: an (unmodelable) inhabitant    *)
(*  acts through an envelope; the envelope's own verified prover (this     *)
(*  Candle process) certifies that the habitat keeps its safety invariant  *)
(*  for ANY inhabitant, and that proof-carrying self-improvement preserves  *)
(*  it. These are the same theorems proved in the HOL4 svenvs core; here    *)
(*  they are re-derived live by Candle's kernel.                           *)
(*                                                                         *)
(*  Load after hol.ml:   #use "theplace.ml";;                              *)
(* ===================================================================== *)

(* --- the envelope: keep the inhabitant's action iff the policy permits,  *)
(*     otherwise fall back to the trusted shield ---------------------- *)
let enveloped = new_definition
  `enveloped pol shield ctrl s =
     if pol s (ctrl s) then ctrl s else shield s`;;

(* --- states reachable when actions are chosen by [sel] -------------- *)
let reach_RULES,reach_INDUCT,reach_CASES = new_inductive_definition
  `(!s. init s ==> reach step init sel s) /\
   (!s. reach step init sel s ==> reach step init sel (step s (sel s)))`;;

let invariant = new_definition
  `invariant step init sel safe <=>
     (!s. reach step init sel s ==> safe s)`;;

(* --- THE HABITAT THEOREM: for ANY inhabitant [ctrl], the enveloped      *)
(*     world keeps [safe], given a safety-sound policy and a safe shield.  *)
(*     Proved here by Candle's verified kernel.                            *)
let SAFETY_PRESERVATION = prove
 (`(!s. init s ==> safe s) /\
   (!s a. safe s /\ pol s a ==> safe (step s a)) /\
   (!s. safe s ==> safe (step s (shield s)))
   ==> !ctrl. invariant step init (enveloped pol shield ctrl) safe`,
  REWRITE_TAC[invariant] THEN STRIP_TAC THEN GEN_TAC THEN
  MATCH_MP_TAC reach_INDUCT THEN
  ASM_REWRITE_TAC[enveloped] THEN REPEAT STRIP_TAC THEN
  COND_CASES_TAC THEN ASM_MESON_TAC[]);;

(* --- policy weakening: a more-permissive policy that stays sound keeps   *)
(*     the guarantee while the inhabitant gains autonomy ---------------- *)
let weaker = new_definition
  `weaker p q <=> (!s a. q s a ==> p s a)`;;

let SAFE_WEAKENING = prove
 (`(!s. init s ==> safe s) /\
   (!s. safe s ==> safe (step s (shield s))) /\
   weaker p q /\
   (!s a. safe s /\ p s a ==> safe (step s a))
   ==> !ctrl. invariant step init (enveloped p shield ctrl) safe`,
  STRIP_TAC THEN MATCH_MP_TAC SAFETY_PRESERVATION THEN
  ASM_REWRITE_TAC[]);;

(* ===================================================================== *)
(*  A concrete inhabitant world (num — Candle's ARITH_TAC is rock-solid).  *)
(*  A "watchdog" habitat: a counter that drifts toward danger unless the   *)
(*  shield resets it; safe = counter stays within bound. Candle's kernel   *)
(*  certifies the concrete obligations and the per-habitat ∀-inhabitant    *)
(*  theorem at runtime.                                                    *)
(* ===================================================================== *)

(* action 0 = "let it drift"; action 1 = "reset" (the shield's move) *)
let wd_step = new_definition
  `wd_step (a:num) (u:num) = if u = 1 then 0 else a + 1`;;

let wd_safe = new_definition
  `wd_safe (a:num) <=> a <= 3`;;

let wd_shield = new_definition
  `wd_shield (a:num) = 1`;;

let wd_init = new_definition
  `wd_init (a:num) <=> (a = 0)`;;

(* the one-step filter: any action whose next state is safe *)
let wd_pol = new_definition
  `wd_pol (a:num) (u:num) <=> (u = 0 \/ u = 1) /\ wd_safe (wd_step a u)`;;

(* the shield always recovers — Candle proves it by num arithmetic *)
let WD_SHIELD_SAFE = prove
 (`!a. wd_safe a ==> wd_safe (wd_step a (wd_shield a))`,
  REWRITE_TAC[wd_safe; wd_step; wd_shield] THEN ARITH_TAC);;

(* THE CONCRETE HABITAT: for ANY inhabitant, the watchdog world stays safe
   — instantiated from SAFETY_PRESERVATION, certified live by Candle. *)
let WD_HABITAT_SAFE = prove
 (`!ctrl. invariant wd_step wd_init (enveloped wd_pol wd_shield ctrl) wd_safe`,
  MATCH_MP_TAC SAFETY_PRESERVATION THEN
  REWRITE_TAC[wd_init; wd_pol] THEN REPEAT CONJ_TAC THENL
   [REWRITE_TAC[wd_safe] THEN ARITH_TAC;
    MESON_TAC[];
    MESON_TAC[WD_SHIELD_SAFE]]);;

(* The REPL itself echoes each `val NAME = |- ... : thm` above — that is the
   witness that Candle's verified kernel certified these. (No Printf: Candle
   runs on CakeML, not OCaml.) *)
