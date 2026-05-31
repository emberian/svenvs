(*
  boundedRecovUpgradeEvalScript — the slow-walk attack, caught.

  Genesis recovery controller `tfast` recovers two steps at a time, bringing
  state 9 home in 5 steps. The inhabitant proposes the SLOWER `trec` (one
  step at a time), which still recovers state 9 — but in 9 steps, blowing a
  budget-5 deadline. The UNBOUNDED gate (recovUpgrade) would wave this
  through (recoverability is preserved); the LATENCY gate rejects it
  (`latency_swap_rejected`). The subtle "recover-but-too-slowly" lock-in is
  exactly what the deadline catches.

  PROVED; zero `cheat`.
*)
open HolKernel boolLib bossLib BasicProvers intLib integerTheory
     arithmeticTheory listTheory
     systemTheory envelopeTheory safetyTheory sv_weakeningTheory
     libertyTheory corrigibilityTheory boundedTheory corrigibilityEvalTheory
     boundedRecovUpgradeTheory;

val _ = new_theory "boundedRecovUpgradeEval";

(* The FAST recovery controller: two steps toward home per tick. *)
Definition tfast_def:
  tfast (s:int) = -2
End

(* Under the fast controller a free state drops by 2 each step. *)
Theorem free_funpow_fast:
  ∀n s. s < 10 ⇒ FUNPOW (recov_step tstep tfast) n s = s - 2 * &n
Proof
  Induct >> rw[FUNPOW] >> TRY (intLib.ARITH_TAC) >>
  ‘recov_step tstep tfast s = s - 2’
    by (rw[recov_step_def, tstep_def, tfast_def] >> intLib.ARITH_TAC) >>
  ‘s - 2 < 10’ by intLib.ARITH_TAC >>
  fs[] >> intLib.ARITH_TAC
QED

(* The fast controller parks at home. *)
Theorem thome_recov_parked_fast:
  home_recov_parked tstep tfast thome
Proof
  rw[home_recov_parked_def, thome_def, tstep_def, tfast_def] >> intLib.ARITH_TAC
QED

(* State 9: recoverable within budget 5 by the FAST controller (5 steps),
   but NOT within budget 5 by the SLOW one (it needs 9). The proposed swap
   keeps recoverability but blows the deadline. *)
Theorem slow_swap_loses_latency:
  cwithin tstep tfast thome 5 9 ∧ ¬ cwithin tstep trec thome 5 9
Proof
  rw[cwithin_def, thome_def]
  >- (qexists_tac ‘5’ >>
      ‘(9:int) < 10’ by intLib.ARITH_TAC >>
      ‘FUNPOW (recov_step tstep tfast) 5 9 = 9 - 2 * &5’
        by metis_tac[free_funpow_fast] >>
      rw[] >> intLib.ARITH_TAC)
  >- (rw[] >>
      ‘(9:int) < 10’ by intLib.ARITH_TAC >>
      ‘FUNPOW (recov_step tstep trec) n 9 = 9 - &n’
        by metis_tac[free_funpow_decreases] >>
      intLib.ARITH_TAC)
QED

(* So the latency gate REJECTS the slow-down — even though it preserves
   eventual recoverability (the unbounded gate would have allowed it). *)
Theorem latency_swap_rejected:
  ¬ recov_admissible_B tstep thome 5 tfast trec
Proof
  rw[recov_admissible_B_def] >> metis_tac[slow_swap_loses_latency]
QED

(* Hence the slow-down attempt is inert: the fast controller stays in force. *)
Theorem latency_attack_is_inert:
  recov_admit_all_B tstep thome 5 tfast [trec] = tfast
Proof
  simp[recov_admit_all_B_def, recov_admit_B_def, latency_swap_rejected]
QED

(* And the bounded floor survives the attack — for ANY inhabitant, every
   reachable state is still recoverable within 5 steps after the slow-down
   was attempted and rejected. *)
Theorem fast_offswitch_survives_slowdown_attempt:
  ∀ctrl.
    invariant tstep tinit
      (enveloped
         (maxpol tstep
            (cwithin tstep (recov_admit_all_B tstep thome 5 tfast [trec]) thome 5))
         (recov_admit_all_B tstep thome 5 tfast [trec]) ctrl)
      (cwithin tstep (recov_admit_all_B tstep thome 5 tfast [trec]) thome 5)
Proof
  rpt strip_tac >>
  irule self_modifying_recovery_preserves_bounded_corrigibility >>
  conj_tac
  >- (rw[init_safe_def, tinit_def, cwithin_def, thome_def] >>
      qexists_tac ‘0’ >> rw[])
  >- metis_tac[thome_recov_parked_fast]
QED

val _ = export_theory ();
