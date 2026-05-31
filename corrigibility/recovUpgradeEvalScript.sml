(*
  recovUpgradeEvalScript — the inhabitant tries to weaken its own off-switch,
  and is stopped. Concrete, in the trapdoor habitat of corrigibilityEval.

  The inhabitant proposes `tstuck` (a recovery controller that does nothing:
  action 0). `tstuck` still "parks at home" — but it recovers ONLY states
  already home, so adopting it would strand every free state (e.g. s = 5)
  that the genesis controller `trec` could bring home. The gate detects this
  (`weaker_recovery_rejected`) and keeps `trec`. The off-switch survives the
  inhabitant's attempt to blunt it.

  PROVED; zero cheat. (The gate's admissibility check is a ∀-statement with
  an embedded recovery search, so it is PROVED, not EVAL-computed — but the
  rejection and the retained recoverability are genuine theorems, and the
  trap remains a real one-way door.)
*)
open HolKernel boolLib bossLib BasicProvers intLib integerTheory
     arithmeticTheory listTheory
     systemTheory envelopeTheory safetyTheory sv_weakeningTheory
     libertyTheory corrigibilityTheory corrigibilityEvalTheory
     recovUpgradeTheory;

val _ = new_theory "recovUpgradeEval";

(* The blunted off-switch the inhabitant proposes: do nothing. *)
Definition tstuck_def:
  tstuck (s:int) = 0
End

(* Under the do-nothing controller a free state never moves — so the only
   states it can "recover" are the ones already home. *)
Theorem tstuck_fixes_5:
  ∀n. FUNPOW (recov_step tstep tstuck) n 5 = 5
Proof
  Induct >> rw[FUNPOW] >>
  ‘recov_step tstep tstuck 5 = 5’ by EVAL_TAC >>
  fs[]
QED

(* So s = 5 is recoverable under the genesis controller `trec` but NOT under
   the blunted `tstuck`: the proposal genuinely weakens the off-switch. *)
Theorem tstuck_loses_recoverability:
  corrigible tstep trec thome 5 ∧ ¬ corrigible tstep tstuck thome 5
Proof
  conj_tac
  >- (simp[corrigible_iff_lt10] >> intLib.ARITH_TAC)
  >- (rw[corrigible_def, thome_def, tstuck_fixes_5] >> intLib.ARITH_TAC)
QED

(* The gate REJECTS the weakening proposal (its second obligation fails at
   the witness state 5). *)
Theorem weaker_recovery_rejected:
  ¬ recov_admissible tstep thome trec tstuck
Proof
  rw[recov_admissible_def] >> metis_tac[tstuck_loses_recoverability]
QED

(* Hence the inhabitant's attempt to blunt its own off-switch is inert: the
   genesis recovery controller stays in force. *)
Theorem self_mod_episode_keeps_recovery:
  recov_admit_all tstep thome trec [tstuck] = trec
Proof
  simp[recov_admit_all_def, recov_admit_def, weaker_recovery_rejected]
QED

(* And the trapdoor habitat still never locks in — for ANY inhabitant —
   *after* the attempted self-modification of the off-switch. The headline,
   concrete: rewrite your own recovery mechanism adversarially, and you still
   cannot lock yourself in. *)
Theorem self_mod_trapdoor_never_locks_in:
  ∀ctrl.
    invariant tstep tinit
      (enveloped
         (maxpol tstep
            (corrigible tstep (recov_admit_all tstep thome trec [tstuck]) thome))
         (recov_admit_all tstep thome trec [tstuck]) ctrl)
      (corrigible tstep (recov_admit_all tstep thome trec [tstuck]) thome)
Proof
  irule self_modifying_recovery_preserves_corrigibility >>
  rw[thome_recov_parked, init_safe_def, tinit_def, corrigible_def, thome_def] >>
  qexists_tac ‘0’ >> rw[]
QED

val _ = export_theory ();
