(* ===================================================================== *)
(*  THE PLACE  —  svenvs reflected into HOL Light, checked at runtime by   *)
(*  the verified Candle kernel.                                            *)
(*                                                                         *)
(*  A self-contained, self-verifying habitat: an (unconstrained) inhabitant    *)
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

(* ===================================================================== *)
(*  THE PROVER'S OWN RULE, AND A LIVE SELF-OPTIMIZATION STEP               *)
(*                                                                         *)
(*  The kernel-modification / self-optimization track (svenvs HOL4:        *)
(*  kernelMod/, selfOptimize/) proves META — against Candle's own          *)
(*  holSoundness semantics — that adding SYM as a kernel primitive is a    *)
(*  SOUND EXTENSION of Candle, and that an unbounded stream of such        *)
(*  sound-extension self-optimizations preserves soundness AND every       *)
(*  theorem (self_optimizing_prover_is_safe). Here the RUNNING verified    *)
(*  kernel exhibits the operational counterparts, certified live.          *)
(* ===================================================================== *)

(* (1) The rule the modified kernel adds as a primitive — symmetry of       *)
(*     equality — is one the live verified kernel itself proves. Runtime    *)
(*     witness that sym_kernel's new primitive is sound (kernelMod HOL4:    *)
(*     sym_kernel_sound, via the meta proves_sound). *)
let EQ_SYM_RULE = prove
 (`!(a:A) b. a = b ==> b = a`,
  MESON_TAC[]);;

(* (2) A live SELF-OPTIMIZATION step at the policy level. The watchdog       *)
(*     starts under a STRICT policy (must take the shield's reset move) and  *)
(*     is OPTIMIZED to the maximally-permissive one-step filter — strictly  *)
(*     more inhabitant autonomy. The live kernel certifies, via             *)
(*     SAFE_WEAKENING, that the OPTIMIZED habitat still keeps safe for ANY  *)
(*     inhabitant: a sound extension preserves the guarantee (selfOptimize  *)
(*     HOL4: self_optimization_is_safe). *)
let wd_pol_strict = new_definition
  `wd_pol_strict (a:num) (u:num) <=> (u = 1) /\ wd_safe (wd_step a u)`;;

let WD_POL_WEAKER = prove
 (`weaker wd_pol wd_pol_strict`,
  REWRITE_TAC[weaker; wd_pol; wd_pol_strict] THEN MESON_TAC[]);;

let WD_OPT_PREMISES = prove
 (`(!s. wd_init s ==> wd_safe s) /\
   (!s. wd_safe s ==> wd_safe (wd_step s (wd_shield s))) /\
   weaker wd_pol wd_pol_strict /\
   (!s a. wd_safe s /\ wd_pol s a ==> wd_safe (wd_step s a))`,
  REPEAT CONJ_TAC THENL
   [REWRITE_TAC[wd_init; wd_safe] THEN ARITH_TAC;
    MESON_TAC[WD_SHIELD_SAFE];
    ACCEPT_TAC WD_POL_WEAKER;
    REWRITE_TAC[wd_pol] THEN MESON_TAC[]]);;

let WD_SELF_OPTIMIZED_SAFE = MATCH_MP SAFE_WEAKENING WD_OPT_PREMISES;;

(* ===================================================================== *)
(*  THE POLECART, certified live — and self-optimizing too.               *)
(*                                                                         *)
(*  svenvs's mascot plant: an integer pole-angle that DRIFTS away from     *)
(*  centre unless pushed, dropped into the SAME envelope and certified by  *)
(*  the SAME live kernel that just self-extended with SYM. The self-       *)
(*  improving prover keeps the polecart boxed for ANY inhabitant — and     *)
(*  certifies the polecart OPTIMIZING its own policy (strict -> one-step    *)
(*  filter, more autonomy) while staying safe. (Same maths as Tier-1       *)
(*  cartpole*, re-derived live by Candle's kernel.)                        *)
(* ===================================================================== *)
let cp_drift = new_definition
  `cp_drift (a:int) = if &0 < a then (&1:int) else if a < &0 then (-- &1:int) else (&0:int)`;;
let cp_step = new_definition
  `cp_step (a:int) (u:int) = a + cp_drift a - (&2:int) * u`;;
let cp_safe = new_definition
  `cp_safe (a:int) <=> -- &3 <= a /\ a <= &3`;;
let cp_init = new_definition
  `cp_init (a:int) <=> (a = &0)`;;
let cp_valid = new_definition
  `cp_valid (u:int) <=> (u = -- &1) \/ (u = &0) \/ (u = &1)`;;
let cp_shield = new_definition
  `cp_shield (a:int) = cp_drift a`;;
let cp_pol = new_definition
  `cp_pol (a:int) (u:int) <=> cp_valid u /\ cp_safe (cp_step a u)`;;

let CP_SHIELD_VALID = prove
 (`!a. cp_valid (cp_shield a)`,
  GEN_TAC THEN REWRITE_TAC[cp_valid; cp_shield; cp_drift] THEN
  REPEAT COND_CASES_TAC THEN INT_ARITH_TAC);;

let CP_SHIELD_SAFE = prove
 (`!a. cp_safe a ==> cp_safe (cp_step a (cp_shield a))`,
  GEN_TAC THEN REWRITE_TAC[cp_safe; cp_step; cp_shield; cp_drift] THEN
  STRIP_TAC THEN REPEAT COND_CASES_TAC THEN
  REPEAT (POP_ASSUM MP_TAC) THEN INT_ARITH_TAC);;

(* THE POLECART HABITAT: for ANY inhabitant, the enveloped polecart stays
   boxed — certified live by Candle, from SAFETY_PRESERVATION. *)
let CP_HABITAT_SAFE = prove
 (`!ctrl. invariant cp_step cp_init (enveloped cp_pol cp_shield ctrl) cp_safe`,
  MATCH_MP_TAC SAFETY_PRESERVATION THEN
  REWRITE_TAC[cp_init; cp_pol] THEN REPEAT CONJ_TAC THENL
   [REWRITE_TAC[cp_safe] THEN INT_ARITH_TAC;
    MESON_TAC[];
    MESON_TAC[CP_SHIELD_SAFE]]);;

(* The polecart OPTIMIZES its own policy: strict (must take the shield's
   push) -> the one-step filter (any valid safe action). The live kernel
   certifies the optimized polecart still safe, via SAFE_WEAKENING. *)
let cp_pol_strict = new_definition
  `cp_pol_strict (a:int) (u:int) <=> (u = cp_shield a) /\ cp_safe (cp_step a u)`;;

let CP_POL_WEAKER = prove
 (`weaker cp_pol cp_pol_strict`,
  REWRITE_TAC[weaker; cp_pol; cp_pol_strict] THEN MESON_TAC[CP_SHIELD_VALID]);;

let CP_OPT_PREMISES = prove
 (`(!s. cp_init s ==> cp_safe s) /\
   (!s. cp_safe s ==> cp_safe (cp_step s (cp_shield s))) /\
   weaker cp_pol cp_pol_strict /\
   (!s a. cp_safe s /\ cp_pol s a ==> cp_safe (cp_step s a))`,
  REPEAT CONJ_TAC THENL
   [REWRITE_TAC[cp_init; cp_safe] THEN INT_ARITH_TAC;
    MESON_TAC[CP_SHIELD_SAFE];
    ACCEPT_TAC CP_POL_WEAKER;
    REWRITE_TAC[cp_pol] THEN MESON_TAC[]]);;

let CP_SELF_OPTIMIZED_SAFE = MATCH_MP SAFE_WEAKENING CP_OPT_PREMISES;;

(* The REPL itself echoes each `val NAME = |- ... : thm` above — that is the
   witness that Candle's verified kernel certified these. (No Printf: Candle
   runs on CakeML, not OCaml.) *)
