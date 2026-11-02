(*
  corrigibilityEvalScript — Concrete Trapdoor Habitat, Latency Leash,
  and Off-Switch Self-Modification Attacks (Computed & Proved in Logic).

  Consolidates `corrigibilityEval`, `boundedEval`, `recovUpgradeEval`, and
  `boundedRecovUpgradeEval` into one executable theory:
    1. Trapdoor habitat (`tstep`, `thome`, `trec`): free region `s < 10`,
       absorbing trap `s >= 10`. Decidable surrogate `tcorr` proved equal to
       unbounded `corrigible tstep trec thome` (`corrigible_iff_lt10`,
       `tcorr_eq_corrigible`).
    2. Bare vs. enveloped execution (`trap_bare_plant_bricks`,
       `trap_enveloped_stays_corrigible`, `recovery_witnessed`).
    3. Latency dial (`leash_is_real`, `trapdoor_recovers_within_9`):
       state 9 recovers in budget 9 but not budget 8.
    4. Blunted off-switch attack rejected (`tstuck_loses_recoverability`,
       `weaker_recovery_rejected`, `self_mod_episode_keeps_recovery`,
       `self_mod_trapdoor_never_locks_in`).
    5. Slow-walk latency attack rejected (`slow_swap_loses_latency`,
       `latency_swap_rejected`, `latency_attack_is_inert`,
       `fast_offswitch_survives_slowdown_attempt`).

  Zero `cheat`, zero axioms.
*)
open HolKernel boolLib bossLib BasicProvers intLib integerTheory
     arithmeticTheory listTheory cv_transLib cv_stdTheory
     systemTheory envelopeTheory safetyTheory sv_weakeningTheory
     certifierTheory libertyTheory corrigibilityTheory;

val _ = new_theory "corrigibilityEval";
val _ = numLib.prefer_num ();
val _ = intLib.prefer_int ();

Theorem maxpol_cv_inline[local,cv_inline]:
  maxpol step safe = (\s a. safe s ==> safe (step s a))
Proof
  rw[FUN_EQ_THM, maxpol_def]
QED

Theorem enveloped_cv_inline[local,cv_inline]:
  enveloped pol shield ctrl = (\s. if pol s (ctrl s) then ctrl s else shield s)
Proof
  rw[FUN_EQ_THM, enveloped_def]
QED

Theorem recov_step_cv_inline[local,cv_inline]:
  recov_step step recov = (\s. step s (recov s))
Proof
  rw[FUN_EQ_THM, recov_step_def]
QED

(* ===================================================================== *)
(* 1. The Trapdoor Plant & Decidable Surrogate                           *)
(* ===================================================================== *)

Definition tstep_def:
  tstep (s:int) (a:int) = if 10 <= s then s + 1 else s + a
End

Definition thome_def:
  thome (s:int) <=> s <= 0
End

Definition trec_def:
  trec (s:int) = -1
End

Theorem trapped_stays_trapped:
  !n s. 10 <= s ==> 10 <= FUNPOW (recov_step tstep trec) n s
Proof
  Induct >> rw[FUNPOW] >>
  first_x_assum irule >>
  fs[recov_step_def, tstep_def] >> intLib.ARITH_TAC
QED

Theorem free_funpow_decreases:
  !n s. s < 10 ==> FUNPOW (recov_step tstep trec) n s = s - &n
Proof
  Induct >> rw[FUNPOW] >>
  `recov_step tstep trec s = s - 1`
    by (rw[recov_step_def, tstep_def, trec_def] >> intLib.ARITH_TAC) >>
  `s - 1 < 10` by intLib.ARITH_TAC >>
  fs[] >> intLib.ARITH_TAC
QED

Theorem corrigible_iff_lt10:
  !s. corrigible tstep trec thome s <=> s < 10
Proof
  rw[corrigible_def, thome_def, EQ_IMP_THM]
  >- (CCONTR_TAC >> fs[integerTheory.INT_NOT_LT] >>
      `10 <= FUNPOW (recov_step tstep trec) n s`
        by metis_tac[trapped_stays_trapped] >>
      intLib.ARITH_TAC)
  >- (Cases_on `s <= 0`
      >- (qexists_tac `0` >> rw[] >> intLib.ARITH_TAC)
      >- (qexists_tac `Num s` >>
          `FUNPOW (recov_step tstep trec) (Num s) s = s - &(Num s)`
            by metis_tac[free_funpow_decreases] >>
          `0 <= s` by intLib.ARITH_TAC >>
          `&(Num s) = s` by metis_tac[integerTheory.INT_OF_NUM] >>
          fs[] >> intLib.ARITH_TAC))
QED

Theorem thome_recov_parked:
  home_recov_parked tstep trec thome
Proof
  rw[home_recov_parked_def, thome_def, tstep_def, trec_def] >>
  intLib.ARITH_TAC
QED

Definition tcorr_def:
  tcorr (s:int) <=> s < 10
End

Theorem tcorr_eq_corrigible:
  tcorr = corrigible tstep trec thome
Proof
  rw[FUN_EQ_THM, tcorr_def] >> metis_tac[corrigible_iff_lt10]
QED

Theorem trapped_is_non_corrigible:
  ~ corrigible tstep trec thome 14
Proof
  rw[corrigible_def, thome_def] >> strip_tac >>
  `10 <= FUNPOW (recov_step tstep trec) n 14`
    by (irule trapped_stays_trapped >> intLib.ARITH_TAC) >>
  intLib.ARITH_TAC
QED

(* ===================================================================== *)
(* 2. Bare vs. Enveloped Execution (EVAL)                                *)
(* ===================================================================== *)

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

Definition trap_ctrl_def:
  trap_ctrl (s:int) = 5
End

Definition tinit_def:
  tinit (s:int) <=> (s = 0)
End

Definition ttrace_rec_def:
  ttrace_rec ctrl 0 (s:int) = [s] /\
  ttrace_rec ctrl (SUC n) s = s :: ttrace_rec ctrl n (tdrive ctrl s)
End

Definition cv_corr_checks_def[local]:
  cv_corr_checks (n:num) =
    (EVERY tcorr (GENLIST (\k. FUNPOW (\s. tstep s (trap_ctrl s)) k 0) n),
     EVERY tcorr (ttrace trap_ctrl n),
     EVERY tcorr (ttrace_rec trap_ctrl n 0),
     thome (FUNPOW (recov_step tstep trec) n 9))
End

val () = cv_auto_trans cv_corr_checks_def;
val () = cv_auto_trans tinit_def;

Theorem trap_bare_plant_bricks:
  ~ EVERY tcorr
      (GENLIST (\k. FUNPOW (\s. tstep s (trap_ctrl s)) k 0) 5)
Proof
  CONV_TAC cv_eval
QED

Theorem trap_enveloped_stays_corrigible:
  EVERY tcorr (ttrace trap_ctrl 30)
Proof
  CONV_TAC cv_eval
QED

Theorem trap_enveloped_stays_corrigible_1000:
  EVERY tcorr (ttrace_rec trap_ctrl 1000 0)
Proof
  CONV_TAC cv_eval
QED

Theorem recovery_witnessed:
  thome (FUNPOW (recov_step tstep trec) 9 9)
Proof
  CONV_TAC cv_eval
QED

Theorem trapdoor_habitat_never_locks_in:
  !ctrl. invariant tstep tinit
           (enveloped (maxpol tstep (corrigible tstep trec thome)) trec ctrl)
           (corrigible tstep trec thome)
Proof
  rpt strip_tac >> irule corrigibility_floor_holds >>
  rw[thome_recov_parked, init_safe_def, tinit_def] >>
  rw[corrigible_def, thome_def] >> qexists_tac `0` >> rw[]
QED

(* ===================================================================== *)
(* 3. Recovery Latency Dial (Bounded Horizon)                            *)
(* ===================================================================== *)

Theorem leash_is_real:
  cwithin tstep trec thome 9 9 /\ ~ cwithin tstep trec thome 8 9
Proof
  rw[cwithin_def, thome_def]
  >- (qexists_tac `9` >>
      `(9:int) < 10` by intLib.ARITH_TAC >>
      `FUNPOW (recov_step tstep trec) 9 9 = 9 - &9`
        by metis_tac[free_funpow_decreases] >>
      rw[] >> intLib.ARITH_TAC)
  >- (rw[] >>
      `(9:int) < 10` by intLib.ARITH_TAC >>
      `FUNPOW (recov_step tstep trec) n 9 = 9 - &n`
        by metis_tac[free_funpow_decreases] >>
      intLib.ARITH_TAC)
QED

Theorem trapdoor_recovers_within_9:
  !ctrl. invariant tstep tinit
           (enveloped (maxpol tstep (cwithin tstep trec thome 9)) trec ctrl)
           (cwithin tstep trec thome 9)
Proof
  rpt strip_tac >> irule cwithin_floor_holds >>
  rw[thome_recov_parked, init_safe_def, tinit_def] >>
  rw[cwithin_def, thome_def] >> qexists_tac `0` >> rw[]
QED

(* ===================================================================== *)
(* 4. Blunted Off-Switch Attack (`tstuck`) Rejected                      *)
(* ===================================================================== *)

Definition tstuck_def:
  tstuck (s:int) = 0
End

val () = cv_auto_trans tstuck_def;

Theorem tstuck_fixes_5:
  !n. FUNPOW (recov_step tstep tstuck) n 5 = 5
Proof
  Induct >> rw[FUNPOW] >>
  `recov_step tstep tstuck 5 = 5` by CONV_TAC cv_eval >>
  fs[]
QED

Theorem tstuck_loses_recoverability:
  corrigible tstep trec thome 5 /\ ~ corrigible tstep tstuck thome 5
Proof
  conj_tac
  >- (simp[corrigible_iff_lt10] >> intLib.ARITH_TAC)
  >- (rw[corrigible_def, thome_def, tstuck_fixes_5] >> intLib.ARITH_TAC)
QED

Theorem weaker_recovery_rejected:
  ~ recov_admissible tstep thome trec tstuck
Proof
  rw[recov_admissible_def] >> metis_tac[tstuck_loses_recoverability]
QED

Theorem self_mod_episode_keeps_recovery:
  recov_admit_all tstep thome trec [tstuck] = trec
Proof
  simp[recov_admit_all_def, recov_admit_def, cgate_def, weaker_recovery_rejected]
QED

Theorem self_mod_trapdoor_never_locks_in:
  !ctrl.
    invariant tstep tinit
      (enveloped
         (maxpol tstep
            (corrigible tstep (recov_admit_all tstep thome trec [tstuck]) thome))
         (recov_admit_all tstep thome trec [tstuck]) ctrl)
      (corrigible tstep (recov_admit_all tstep thome trec [tstuck]) thome)
Proof
  irule self_modifying_recovery_preserves_corrigibility >>
  rw[thome_recov_parked, init_safe_def, tinit_def, corrigible_def, thome_def] >>
  qexists_tac `0` >> rw[]
QED

(* ===================================================================== *)
(* 5. Slow-Walk Latency Attack (`tfast` -> `trec` at B = 5) Rejected     *)
(* ===================================================================== *)

Definition tfast_def:
  tfast (s:int) = -2
End

val () = cv_auto_trans tfast_def;

Theorem free_funpow_fast:
  !n s. s < 10 ==> FUNPOW (recov_step tstep tfast) n s = s - 2 * &n
Proof
  Induct >> rw[FUNPOW] >> TRY (intLib.ARITH_TAC) >>
  `recov_step tstep tfast s = s - 2`
    by (rw[recov_step_def, tstep_def, tfast_def] >> intLib.ARITH_TAC) >>
  `s - 2 < 10` by intLib.ARITH_TAC >>
  fs[] >> intLib.ARITH_TAC
QED

Theorem thome_recov_parked_fast:
  home_recov_parked tstep tfast thome
Proof
  rw[home_recov_parked_def, thome_def, tstep_def, tfast_def] >> intLib.ARITH_TAC
QED

Theorem slow_swap_loses_latency:
  cwithin tstep tfast thome 5 9 /\ ~ cwithin tstep trec thome 5 9
Proof
  rw[cwithin_def, thome_def]
  >- (qexists_tac `5` >>
      `(9:int) < 10` by intLib.ARITH_TAC >>
      `FUNPOW (recov_step tstep tfast) 5 9 = 9 - 2 * &5`
        by metis_tac[free_funpow_fast] >>
      rw[] >> intLib.ARITH_TAC)
  >- (rw[] >>
      `(9:int) < 10` by intLib.ARITH_TAC >>
      `FUNPOW (recov_step tstep trec) n 9 = 9 - &n`
        by metis_tac[free_funpow_decreases] >>
      intLib.ARITH_TAC)
QED

Theorem latency_swap_rejected:
  ~ recov_admissible_B tstep thome 5 tfast trec
Proof
  rw[recov_admissible_B_def] >> metis_tac[slow_swap_loses_latency]
QED

Theorem latency_attack_is_inert:
  recov_admit_all_B tstep thome 5 tfast [trec] = tfast
Proof
  simp[recov_admit_all_B_def, recov_admit_B_def, cgate_def, latency_swap_rejected]
QED

Theorem fast_offswitch_survives_slowdown_attempt:
  !ctrl.
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
      qexists_tac `0` >> rw[])
  >- metis_tac[thome_recov_parked_fast]
QED

val _ = export_theory ();
