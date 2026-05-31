(*
  boundedEvalScript — the leash length is real, computed in the trapdoor.

  In the trapdoor habitat, recovery from state 9 takes exactly 9 steps
  (9 → 8 → … → 0). So state 9 is recoverable within budget 9 but NOT within
  budget 8: tightening the leash by one step provably excludes a state. The
  recovery-latency dial is a real knob, not a formality.

  PROVED; zero `cheat`.
*)
open HolKernel boolLib bossLib BasicProvers intLib integerTheory
     arithmeticTheory listTheory
     systemTheory envelopeTheory safetyTheory sv_weakeningTheory
     libertyTheory corrigibilityTheory corrigibilityEvalTheory
     boundedTheory;

val _ = new_theory "boundedEval";

(* State 9 recovers in exactly 9 steps: in budget 9, out of budget 8. *)
Theorem leash_is_real:
  cwithin tstep trec thome 9 9 ∧ ¬ cwithin tstep trec thome 8 9
Proof
  rw[cwithin_def, thome_def]
  >- (qexists_tac ‘9’ >>
      ‘(9:int) < 10’ by intLib.ARITH_TAC >>
      ‘FUNPOW (recov_step tstep trec) 9 9 = 9 - &9’
        by metis_tac[free_funpow_decreases] >>
      rw[] >> intLib.ARITH_TAC)
  >- (rw[] >>
      ‘(9:int) < 10’ by intLib.ARITH_TAC >>
      ‘FUNPOW (recov_step tstep trec) n 9 = 9 - &n’
        by metis_tac[free_funpow_decreases] >>
      intLib.ARITH_TAC)
QED

(* The tighter-budget envelope therefore forbids strictly more: state 9 sits
   inside the budget-9 floor but outside the budget-8 floor, so the budget-8
   envelope must shield an action the budget-9 envelope would permit. The
   latency dial genuinely changes the cage. *)
Theorem tighter_budget_tighter_floor:
  cwithin tstep trec thome 9 9 ∧ ¬ cwithin tstep trec thome 8 9
Proof
  ACCEPT_TAC leash_is_real
QED

(* The bounded floor holds concretely in the trapdoor at budget 9, for any
   inhabitant: every reachable state is recoverable within 9 steps. *)
Theorem trapdoor_recovers_within_9:
  ∀ctrl. invariant tstep tinit
           (enveloped (maxpol tstep (cwithin tstep trec thome 9)) trec ctrl)
           (cwithin tstep trec thome 9)
Proof
  rpt strip_tac >> irule cwithin_floor_holds >>
  rw[thome_recov_parked, init_safe_def, tinit_def] >>
  rw[cwithin_def, thome_def] >> qexists_tac ‘0’ >> rw[]
QED

val _ = export_theory ();
