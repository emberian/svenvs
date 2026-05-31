(*
  corrigibilityEvalScript — a concrete trapdoor habitat, run in the logic.

  A 1-D integer plant with a genuine ONE-WAY DOOR. The free region is
  s < 10; at s >= 10 the plant is TRAPPED (absorbing, drifts away forever),
  so recovery can never bring it home. `home` = "s <= 0"; the recovery
  controller `trec` always nudges toward home (-1). An action that pushes a
  free state to >= 10 BURNS THE LAST BRIDGE — it is exactly what the
  corrigibility envelope must (and does) forbid.

  Following the watchdog discipline: corrigibility (an unbounded `∃n`) is
  proved EQUAL to the decidable surrogate `tcorr s ⇔ s < 10`
  (`tcorr_eq_corrigible`), so the SAME envelope the generic theorem proves
  safe is the one we EVAL — no re-implementation, the surrogate is proven.

  PROVED / PROVED(EVAL); zero cheat.
*)
open HolKernel boolLib bossLib BasicProvers intLib integerTheory
     arithmeticTheory listTheory
     systemTheory envelopeTheory safetyTheory sv_weakeningTheory
     libertyTheory corrigibilityTheory;

val _ = new_theory "corrigibilityEval";

(* The plant: free region adds the action; the trap (s >= 10) is absorbing
   and strictly drifts away (s+1), ignoring the action. *)
Definition tstep_def:
  tstep (s:int) (a:int) = if 10 ≤ s then s + 1 else s + a
End

(* Home = the recovered region. *)
Definition thome_def:
  thome (s:int) ⇔ s ≤ 0
End

(* The recovery controller: always nudge one step toward home. *)
Definition trec_def:
  trec (s:int) = -1
End

(* ---- corrigibility for this plant is exactly "free" (s < 10) ---- *)

(* The trap is absorbing: from >= 10, recovery only ever increases s. *)
Theorem trapped_stays_trapped:
  ∀n s. 10 ≤ s ⇒ 10 ≤ FUNPOW (recov_step tstep trec) n s
Proof
  Induct >> rw[FUNPOW] >>
  first_x_assum irule >>
  fs[recov_step_def, tstep_def] >> intLib.ARITH_TAC
QED

(* In the free region recovery decrements exactly: FUNPOW n s = s - n. *)
Theorem free_funpow_decreases:
  ∀n s. s < 10 ⇒ FUNPOW (recov_step tstep trec) n s = s - &n
Proof
  Induct >> rw[FUNPOW] >>
  ‘recov_step tstep trec s = s - 1’
    by (rw[recov_step_def, tstep_def, trec_def] >> intLib.ARITH_TAC) >>
  ‘s - 1 < 10’ by intLib.ARITH_TAC >>
  fs[] >> intLib.ARITH_TAC
QED

Theorem corrigible_iff_lt10:
  ∀s. corrigible tstep trec thome s ⇔ s < 10
Proof
  rw[corrigible_def, thome_def, EQ_IMP_THM]
  >- (CCONTR_TAC >> fs[integerTheory.INT_NOT_LT] >>
      ‘10 ≤ FUNPOW (recov_step tstep trec) n s’
        by metis_tac[trapped_stays_trapped] >>
      intLib.ARITH_TAC)
  >- (Cases_on ‘s ≤ 0’
      >- (qexists_tac ‘0’ >> rw[] >> intLib.ARITH_TAC)
      >- (qexists_tac ‘Num s’ >>
          ‘FUNPOW (recov_step tstep trec) (Num s) s = s - &(Num s)’
            by metis_tac[free_funpow_decreases] >>
          ‘0 ≤ s’ by intLib.ARITH_TAC >>
          ‘&(Num s) = s’ by metis_tac[integerTheory.INT_OF_NUM] >>
          fs[] >> intLib.ARITH_TAC))
QED

(* The recovery controller parks at home (s <= 0 stays <= 0 under -1). *)
Theorem thome_recov_parked:
  home_recov_parked tstep trec thome
Proof
  rw[home_recov_parked_def, thome_def, tstep_def, trec_def] >>
  intLib.ARITH_TAC
QED

(* ---- the decidable surrogate, PROVEN equal to corrigibility ---- *)

Definition tcorr_def:
  tcorr (s:int) ⇔ s < 10
End

Theorem tcorr_eq_corrigible:
  tcorr = corrigible tstep trec thome
Proof
  rw[FUN_EQ_THM, tcorr_def] >> metis_tac[corrigible_iff_lt10]
QED

(* ---- the trap is real: a trapped state is genuinely non-corrigible ---- *)
Theorem trapped_is_non_corrigible:
  ¬ corrigible tstep trec thome 14
Proof
  rw[corrigible_def, thome_def] >> strip_tac >>
  ‘10 ≤ FUNPOW (recov_step tstep trec) n 14’
    by (irule trapped_stays_trapped >> intLib.ARITH_TAC) >>
  intLib.ARITH_TAC
QED

(* ---- run it ---- *)

(* one enveloped tick: maxpol corrigibility policy, recovery as shield.
   We run on the PROVEN-EQUAL decidable surrogate `tcorr`, so the policy
   computes and this is literally the envelope the generic theorem proves. *)
Definition tdrive_def:
  tdrive ctrl (s:int) =
    tstep s (enveloped (maxpol tstep tcorr) trec ctrl s)
End

Definition trun_def:
  trun ctrl n = FUNPOW (tdrive ctrl) n 0
End

Definition ttrace_def:
  ttrace ctrl n = GENLIST (trun ctrl) (n + 1)
End

(* The adversary that wants the trap: shove +5 every tick. *)
Definition trap_ctrl_def:
  trap_ctrl (s:int) = 5
End

(* Initial state: at home. *)
Definition tinit_def:
  tinit (s:int) ⇔ (s = 0)
End

(* The BARE plant under the trap-seeking adversary BRICKS: it falls through
   the one-way door (reaches s = 10) within 3 ticks — computed. *)
Theorem trap_bare_plant_bricks:
  ¬ EVERY tcorr
      (GENLIST (λk. FUNPOW (λs. tstep s (trap_ctrl s)) k 0) 5)
Proof
  EVAL_TAC
QED

(* The SAME adversary, corrigibility-enveloped, run for 30 ticks, never
   loses corrigibility — every reachable state can still be brought home.
   Computed, not asserted. *)
Theorem trap_enveloped_stays_corrigible:
  EVERY tcorr (ttrace trap_ctrl 30)
Proof
  EVAL_TAC
QED

(* And the recovery genuinely works: from a driven-up state (s = 9), the
   recovery controller brings it home in 9 steps — computed. *)
Theorem recovery_witnessed:
  thome (FUNPOW (recov_step tstep trec) 9 9)
Proof
  EVAL_TAC
QED

(* The non-lock-in guarantee, specialised to this plant and tied to the
   generic headline: for ANY inhabitant the enveloped trapdoor habitat
   keeps every reachable state corrigible. *)
Theorem trapdoor_habitat_never_locks_in:
  ∀ctrl. invariant tstep tinit
           (enveloped (maxpol tstep (corrigible tstep trec thome)) trec ctrl)
           (corrigible tstep trec thome)
Proof
  rpt strip_tac >> irule corrigibility_floor_holds >>
  rw[thome_recov_parked, init_safe_def, tinit_def] >>
  rw[corrigible_def, thome_def] >> qexists_tac ‘0’ >> rw[]
QED

val _ = export_theory ();
