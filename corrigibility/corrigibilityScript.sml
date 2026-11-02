(*
  corrigibilityScript — the non-lock-in floor: unbounded, latency-bounded,
  self-modifiable under `cgate_run`, redundant over `home`, negotiable
  bedrock, and adversarial/relational (`corrigibler`).

  Consolidates the entire corrigibility theory into one cohesive development:
    1. Unbounded (`corrigible`) and B-bounded (`cwithin`) recoverability via
       `FUNPOW (recov_step step recov)`, plus safe-shield discharge and
       maximal-liberty non-lock-in (`corrigibility_floor_holds`,
       `cwithin_floor_holds`).
    2. Operational off-switch self-modification (`recov_gate`, `recov_gate_B`,
       and their `cgate_run` streams) proved via `certifierTheory`: the
       inhabitant may rewrite its own recovery mechanism, never weakening
       recoverability (`self_modification_never_weakens_recoverability`) nor
       slowing recovery past deadline B
       (`self_modification_never_increases_recovery_latency`).
    3. Corrigibility as the tower's negotiable bedrock (`specNegTheory`
       instantiation: `corrigibility_is_negotiable_bedrock`) and N-version
       conjunctive redundancy on the frozen `home` predicate
       (`corrigible_to_and_implies_each`, `disjoint_homes_make_floor_empty`).
    4. Demonic / adversarial plant corrigibility (`drecov_within`,
       `corrigibler`): game-tree recoverability against a nondeterministic
       or adversarial environment `stepr`, proving that `recov` is both a
       safe and live relational shield (`recov_is_safe_shieldr`), that
       non-lock-in + non-blocking liveness hold for every inhabitant
       (`corrigibler_floor_holds`), and that deterministic `FUNPOW`
       corrigibility is the exact `det step` specialization
       (`drecov_within_det`, `corrigibler_det`).

  Pure light HOL4; zero `cheat`, zero axioms.
*)
open HolKernel boolLib bossLib BasicProvers arithmeticTheory listTheory
     systemTheory envelopeTheory safetyTheory sv_weakeningTheory
     upgradeTheory certifierTheory relSystemTheory relEnvelopeTheory
     libertyTheory specNegTheory;

val _ = new_theory "corrigibility";

(* ===================================================================== *)
(* 1. Unbounded Corrigibility & Non-Lock-In                              *)
(* ===================================================================== *)

Definition recov_step_def:
  recov_step (step:'s->'a->'s) (recov:'s->'a) (s:'s) = step s (recov s)
End

Definition corrigible_def:
  corrigible (step:'s->'a->'s) (recov:'s->'a) (home:'s->bool) (s:'s) <=>
    ?n. home (FUNPOW (recov_step step recov) n s)
End

Definition home_recov_parked_def:
  home_recov_parked (step:'s->'a->'s) (recov:'s->'a) (home:'s->bool) <=>
    !s. home s ==> home (step s (recov s))
End

Theorem home_is_corrigible:
  home s ==> corrigible step recov home s
Proof
  rw[corrigible_def] >> qexists_tac `0` >> rw[]
QED

Theorem recov_preserves_corrigible:
  home_recov_parked step recov home /\ corrigible step recov home s ==>
  corrigible step recov home (step s (recov s))
Proof
  rw[corrigible_def, home_recov_parked_def] >>
  Cases_on `n` >> fs[FUNPOW]
  >- (qexists_tac `0` >> fs[recov_step_def] >> metis_tac[])
  >- (qexists_tac `n'` >> fs[recov_step_def])
QED

Theorem recov_is_safe_shield:
  home_recov_parked step recov home ==>
  safe_shield step (corrigible step recov home) recov
Proof
  rw[safe_shield_def] >> metis_tac[recov_preserves_corrigible]
QED

Theorem corrigibility_floor_holds:
  home_recov_parked step recov home /\
  init_safe init (corrigible step recov home) ==>
  !ctrl. invariant step init
           (enveloped (maxpol step (corrigible step recov home)) recov ctrl)
           (corrigible step recov home)
Proof
  rpt strip_tac >> irule maxpol_envelope_safe >>
  metis_tac[recov_is_safe_shield]
QED

Theorem operator_can_always_recover:
  home_recov_parked step recov home /\
  init_safe init (corrigible step recov home) /\
  reach step init
     (enveloped (maxpol step (corrigible step recov home)) recov ctrl) s ==>
  ?n. home (FUNPOW (recov_step step recov) n s)
Proof
  rpt strip_tac >>
  `corrigible step recov home s`
    by (drule_all corrigibility_floor_holds >>
        disch_then (qspec_then `ctrl` mp_tac) >>
        rw[invariant_def] >> metis_tac[]) >>
  fs[corrigible_def] >> metis_tac[]
QED

Theorem corrigibility_envelope_is_least_restrictive:
  sound_policy step (corrigible step recov home)
                    (maxpol step (corrigible step recov home)) /\
  (!pol. sound_policy step (corrigible step recov home) pol ==>
         weaker (maxpol step (corrigible step recov home)) pol) /\
  (!q s a. corrigible step recov home s /\ q s a /\
           ~ maxpol step (corrigible step recov home) s a ==>
           ~ sound_policy step (corrigible step recov home) q)
Proof
  metis_tac[envelope_is_least_restrictive]
QED

Theorem override_is_exactly_a_burned_bridge:
  enveloped (maxpol step (corrigible step recov home)) recov ctrl s <> ctrl s ==>
  corrigible step recov home s /\
  ~ corrigible step recov home (step s (ctrl s))
Proof
  metis_tac[envelope_overrides_only_unsafe]
QED

Theorem free_action_runs_unimpeded:
  corrigible step recov home s /\
  corrigible step recov home (step s (ctrl s)) ==>
  enveloped (maxpol step (corrigible step recov home)) recov ctrl s = ctrl s
Proof
  metis_tac[envelope_never_overrides_safe_action]
QED

(* ===================================================================== *)
(* 2. Bounded-Latency Corrigibility (`cwithin`)                          *)
(* ===================================================================== *)

Definition cwithin_def:
  cwithin (step:'s->'a->'s) (recov:'s->'a) (home:'s->bool) (B:num) (s:'s) <=>
    ?n. n <= B /\ home (FUNPOW (recov_step step recov) n s)
End

Theorem home_is_cwithin:
  home s ==> cwithin step recov home B s
Proof
  rw[cwithin_def] >> qexists_tac `0` >> rw[]
QED

Theorem cwithin_implies_corrigible:
  cwithin step recov home B s ==> corrigible step recov home s
Proof
  rw[cwithin_def, corrigible_def] >> metis_tac[]
QED

Theorem corrigible_iff_exists_cwithin:
  corrigible step recov home s <=> ?B. cwithin step recov home B s
Proof
  rw[corrigible_def, cwithin_def, EQ_IMP_THM]
  >- (qexistsl_tac [`n`, `n`] >> simp[])
  >- metis_tac[]
QED

Theorem cwithin_monotone:
  B <= B' /\ cwithin step recov home B s ==> cwithin step recov home B' s
Proof
  rw[cwithin_def] >> qexists_tac `n` >> rw[]
QED

Theorem recov_preserves_cwithin:
  home_recov_parked step recov home /\ cwithin step recov home B s ==>
  cwithin step recov home B (step s (recov s))
Proof
  rw[cwithin_def, home_recov_parked_def] >>
  Cases_on `n` >> fs[FUNPOW]
  >- (qexists_tac `0` >> fs[recov_step_def] >> metis_tac[])
  >- (qexists_tac `n'` >> fs[recov_step_def])
QED

Theorem recov_is_safe_shield_within:
  home_recov_parked step recov home ==>
  safe_shield step (cwithin step recov home B) recov
Proof
  rw[safe_shield_def] >> metis_tac[recov_preserves_cwithin]
QED

Theorem cwithin_floor_holds:
  home_recov_parked step recov home /\
  init_safe init (cwithin step recov home B) ==>
  !ctrl. invariant step init
           (enveloped (maxpol step (cwithin step recov home B)) recov ctrl)
           (cwithin step recov home B)
Proof
  rpt strip_tac >> irule maxpol_envelope_safe >>
  metis_tac[recov_is_safe_shield_within]
QED

Theorem operator_recovers_within_B:
  home_recov_parked step recov home /\
  init_safe init (cwithin step recov home B) /\
  reach step init
     (enveloped (maxpol step (cwithin step recov home B)) recov ctrl) s ==>
  ?n. n <= B /\ home (FUNPOW (recov_step step recov) n s)
Proof
  rpt strip_tac >>
  `cwithin step recov home B s`
    by (drule_all cwithin_floor_holds >>
        disch_then (qspec_then `ctrl` mp_tac) >>
        rw[invariant_def] >> metis_tac[]) >>
  fs[cwithin_def] >> metis_tac[]
QED

(* ===================================================================== *)
(* 3. Self-Modifying Off-Switch (Unbounded & Latency-Bounded via cgate)  *)
(* ===================================================================== *)

Definition recov_admissible_def:
  recov_admissible step home oldrec newrec <=>
    home_recov_parked step newrec home /\
    (!s. corrigible step oldrec home s ==> corrigible step newrec home s)
End

Definition recov_admit_def:
  recov_admit step home oldrec newrec =
    cgate (recov_admissible step home oldrec newrec) oldrec newrec
End

Theorem recov_admit_keeps_parked:
  home_recov_parked step oldrec home ==>
  home_recov_parked step (recov_admit step home oldrec newrec) home
Proof
  rw[recov_admit_def, cgate_def, recov_admissible_def]
QED

Theorem recov_admit_preserves_corrigible:
  corrigible step oldrec home s ==>
  corrigible step (recov_admit step home oldrec newrec) home s
Proof
  rw[recov_admit_def, cgate_def, recov_admissible_def] >> metis_tac[]
QED

Theorem unrecoverable_swap_is_inert:
  ~ recov_admissible step home oldrec newrec ==>
  recov_admit step home oldrec newrec = oldrec
Proof
  rw[recov_admit_def, cgate_def]
QED

Definition recov_admit_all_def:
  recov_admit_all step home rec0 proposals =
    FOLDL (recov_admit step home) rec0 proposals
End

Theorem recov_admit_all_keeps_parked:
  !proposals rec0.
    home_recov_parked step rec0 home ==>
    home_recov_parked step (recov_admit_all step home rec0 proposals) home
Proof
  Induct >> rw[recov_admit_all_def] >>
  fs[GSYM recov_admit_all_def] >>
  first_x_assum irule >>
  metis_tac[recov_admit_keeps_parked]
QED

Theorem self_modification_never_weakens_recoverability:
  !proposals rec0 s.
    corrigible step rec0 home s ==>
    corrigible step (recov_admit_all step home rec0 proposals) home s
Proof
  Induct >> rw[recov_admit_all_def] >>
  fs[GSYM recov_admit_all_def] >>
  first_x_assum irule >>
  metis_tac[recov_admit_preserves_corrigible]
QED

Theorem self_modifying_recovery_preserves_corrigibility:
  home_recov_parked step rec0 home /\
  init_safe init (corrigible step rec0 home) ==>
  !proposals ctrl.
    invariant step init
      (enveloped
         (maxpol step (corrigible step (recov_admit_all step home rec0 proposals) home))
         (recov_admit_all step home rec0 proposals) ctrl)
      (corrigible step (recov_admit_all step home rec0 proposals) home)
Proof
  rpt strip_tac >>
  irule corrigibility_floor_holds >>
  conj_tac
  >- (fs[init_safe_def] >>
      metis_tac[self_modification_never_weakens_recoverability])
  >- metis_tac[recov_admit_all_keeps_parked]
QED

(* Latency-bounded recovery upgrade (`recov_admissible_B`, `recov_admit_B`) *)
Definition recov_admissible_B_def:
  recov_admissible_B step home B oldrec newrec <=>
    home_recov_parked step newrec home /\
    (!s. cwithin step oldrec home B s ==> cwithin step newrec home B s)
End

Definition recov_admit_B_def:
  recov_admit_B step home B oldrec newrec =
    cgate (recov_admissible_B step home B oldrec newrec) oldrec newrec
End

Theorem recov_admit_B_keeps_parked:
  home_recov_parked step oldrec home ==>
  home_recov_parked step (recov_admit_B step home B oldrec newrec) home
Proof
  rw[recov_admit_B_def, cgate_def, recov_admissible_B_def]
QED

Theorem recov_admit_B_preserves_cwithin:
  cwithin step oldrec home B s ==>
  cwithin step (recov_admit_B step home B oldrec newrec) home B s
Proof
  rw[recov_admit_B_def, cgate_def, recov_admissible_B_def] >> metis_tac[]
QED

Theorem slow_swap_is_inert:
  ~ recov_admissible_B step home B oldrec newrec ==>
  recov_admit_B step home B oldrec newrec = oldrec
Proof
  rw[recov_admit_B_def, cgate_def]
QED

Definition recov_admit_all_B_def:
  recov_admit_all_B step home B rec0 proposals =
    FOLDL (recov_admit_B step home B) rec0 proposals
End

Theorem recov_admit_all_B_keeps_parked:
  !proposals rec0.
    home_recov_parked step rec0 home ==>
    home_recov_parked step (recov_admit_all_B step home B rec0 proposals) home
Proof
  Induct >> rw[recov_admit_all_B_def] >>
  fs[GSYM recov_admit_all_B_def] >>
  first_x_assum irule >>
  metis_tac[recov_admit_B_keeps_parked]
QED

Theorem self_modification_never_increases_recovery_latency:
  !proposals rec0 s.
    cwithin step rec0 home B s ==>
    cwithin step (recov_admit_all_B step home B rec0 proposals) home B s
Proof
  Induct >> rw[recov_admit_all_B_def] >>
  fs[GSYM recov_admit_all_B_def] >>
  first_x_assum irule >>
  metis_tac[recov_admit_B_preserves_cwithin]
QED

Theorem self_modifying_recovery_preserves_bounded_corrigibility:
  home_recov_parked step rec0 home /\
  init_safe init (cwithin step rec0 home B) ==>
  !proposals ctrl.
    invariant step init
      (enveloped
         (maxpol step
            (cwithin step (recov_admit_all_B step home B rec0 proposals) home B))
         (recov_admit_all_B step home B rec0 proposals) ctrl)
      (cwithin step (recov_admit_all_B step home B rec0 proposals) home B)
Proof
  rpt strip_tac >>
  irule cwithin_floor_holds >>
  conj_tac
  >- (fs[init_safe_def] >>
      metis_tac[self_modification_never_increases_recovery_latency])
  >- metis_tac[recov_admit_all_B_keeps_parked]
QED

(* ===================================================================== *)
(* 4. Corrigibility as Negotiable Bedrock & Conjunctive Home Redundancy  *)
(* ===================================================================== *)

Theorem corrigibility_survives_one_spec_negotiation:
  spec_refines curspec (corrigible step recov home) /\
  envelope_ok_for_spec step init shield pol
     (spec_admit (corrigible step recov home) curspec newspec) ==>
  !ctrl. invariant step init (enveloped pol shield ctrl)
           (corrigible step recov home)
Proof
  metis_tac[spec_negotiation_is_safe]
QED

Theorem corrigibility_is_negotiable_bedrock:
  spec_refines s0 (corrigible step recov home) /\
  envelope_ok_for_spec step init shield pol
     (spec_admit_all (corrigible step recov home) s0 proposals) ==>
  !ctrl. invariant step init (enveloped pol shield ctrl)
           (corrigible step recov home)
Proof
  metis_tac[spec_negotiation_unbounded_is_safe]
QED

Theorem corrigibility_floor_is_never_negotiated:
  spec_refines s0 (corrigible step recov home) ==>
  !s. spec_admit_all (corrigible step recov home) s0 proposals s ==>
      corrigible step recov home s
Proof
  metis_tac[meta_floor_is_never_negotiated]
QED

Definition home_and_def:
  home_and (h1:'s->bool) (h2:'s->bool) s <=> h1 s /\ h2 s
End

Theorem home_and_idem:
  home_and h h = h
Proof
  rw[FUN_EQ_THM, home_and_def]
QED

Theorem robust_subsumes_single:
  corrigible step recov (home_and h h) s <=> corrigible step recov h s
Proof
  rw[home_and_idem]
QED

Theorem corrigible_to_and_implies_each:
  corrigible step recov (home_and h1 h2) s ==>
  corrigible step recov h1 s /\ corrigible step recov h2 s
Proof
  rw[corrigible_def, home_and_def] >> metis_tac[]
QED

Theorem robust_to_unknown_true_home:
  corrigible step recov (home_and h1 h2) s ==>
  corrigible step recov h1 s
Proof
  metis_tac[corrigible_to_and_implies_each]
QED

Theorem robust_to_unknown_true_home_sym:
  corrigible step recov (home_and h1 h2) s ==>
  corrigible step recov h2 s
Proof
  metis_tac[corrigible_to_and_implies_each]
QED

Theorem robust_floor_holds:
  home_recov_parked step recov (home_and h1 h2) /\
  init_safe init (corrigible step recov (home_and h1 h2)) ==>
  !ctrl. invariant step init
           (enveloped (maxpol step (corrigible step recov (home_and h1 h2)))
                      recov ctrl)
           (corrigible step recov (home_and h1 h2))
Proof
  rpt strip_tac >> irule corrigibility_floor_holds >> fs[]
QED

Theorem disjoint_homes_make_floor_empty:
  (!s. ~(h1 s /\ h2 s)) ==>
  !s. ~ corrigible step recov (home_and h1 h2) s
Proof
  rw[corrigible_def, home_and_def] >> metis_tac[]
QED

(* ===================================================================== *)
(* 5. Demonic / Adversarial Plant Corrigibility (`corrigibler`)          *)
(* ===================================================================== *)

(* Demonic n-step recoverability over a relational plant `stepr`:
   within `n` steps of applying `recov`, the system is guaranteed to
   reach `home` against EVERY adversarial/nondeterministic transition. *)
Definition drecov_within_def:
  (drecov_within (stepr:'s->'a->'s->bool) (recov:'s->'a) (home:'s->bool) 0 s <=>
     home s) /\
  (drecov_within stepr recov home (SUC n) s <=>
     enabled stepr s (recov s) /\
     (!s'. stepr s (recov s) s' ==> drecov_within stepr recov home n s'))
End

Definition corrigibler_def:
  corrigibler stepr recov home s <=> ?n. drecov_within stepr recov home n s
End

Definition home_recov_parkedr_def:
  home_recov_parkedr stepr recov home <=>
    !s. home s ==>
        enabled stepr s (recov s) /\
        (!s'. stepr s (recov s) s' ==> home s')
End

(* Deterministic `FUNPOW` recoverability is the exact `det step` instance
   of demonic game-tree recoverability. *)
Theorem drecov_within_det:
  !n step recov home s.
    drecov_within (det step) recov home n s <=>
    home (FUNPOW (recov_step step recov) n s)
Proof
  Induct >> rw[drecov_within_def, det_def, enabled_def, FUNPOW, recov_step_def]
QED

Theorem corrigibler_det:
  !step recov home.
    corrigibler (det step) recov home = corrigible step recov home
Proof
  rw[FUN_EQ_THM, corrigibler_def, corrigible_def, drecov_within_det]
QED

Theorem recov_preserves_corrigibler:
  home_recov_parkedr stepr recov home /\
  corrigibler stepr recov home s ==>
  enabled stepr s (recov s) /\
  (!s'. stepr s (recov s) s' ==> corrigibler stepr recov home s')
Proof
  rw[corrigibler_def, home_recov_parkedr_def] >>
  Cases_on `n` >> fs[drecov_within_def]
  >- (rpt strip_tac >> qexists_tac `0` >> rw[drecov_within_def] >> metis_tac[])
  >- metis_tac[]
QED

Theorem recov_is_safe_shieldr:
  home_recov_parkedr stepr recov home ==>
  safe_shieldr stepr (corrigibler stepr recov home) recov /\
  live_shieldr stepr (corrigibler stepr recov home) recov
Proof
  rw[safe_shieldr_def, live_shieldr_def] >>
  metis_tac[recov_preserves_corrigibler]
QED

(* HEADLINE (Relational Non-Lock-In + Liveness): Even against an
   adversarial or nondeterministic environment `stepr`, the enveloped
   system under `sound_policyr` and `recov` keeps every reachable state
   demonically corrigible AND never deadlocks (`enveloped_nonblocking`). *)
Theorem corrigibler_floor_holds:
  home_recov_parkedr stepr recov home /\
  init_safe init (corrigibler stepr recov home) /\
  sound_policyr stepr (corrigibler stepr recov home) pol /\
  live_policyr stepr (corrigibler stepr recov home) pol ==>
  !ctrl.
    invariantr stepr init (enveloped pol recov ctrl)
      (corrigibler stepr recov home) /\
    (!s. reachr stepr init (enveloped pol recov ctrl) s ==>
         enabled stepr s (enveloped pol recov ctrl s))
Proof
  rpt strip_tac
  >- (irule safety_preservationr >>
      metis_tac[recov_is_safe_shieldr])
  >- (irule enveloped_nonblocking >>
      metis_tac[recov_is_safe_shieldr])
QED

val _ = export_theory ();
