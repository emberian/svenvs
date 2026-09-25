(*
  transparencyScript — minimal intervention, as theorems.

  libertyTheory shows the maximal sound policy `maxpol` is the largest
  sound cage. This file measures the cage from the controller's side: how
  often does the envelope actually OVERRIDE what the controller proposed?

   * `intervenes pol shield ctrl s`  the envelope's action differs from the
       controller's. `intervenes_iff`: exactly when the policy forbade the
       controller's action AND the shield proposes something else.
   * `sound_policy_intervenes_on_unsafe`  every sound envelope with a safe
       shield stops every unsafe action (`_tight`: each hypothesis needed).
   * `maxpol_intervenes_exactly` / `maxpol_intervenes_iff_unsafe`  at maxpol
       the envelope intervenes on precisely the unsafe actions (`_tight`).
   * `intervention_monotone`, `maxpol_intervenes_least`  a weaker policy
       overrides no more often; maxpol overrides least of all sound policies.
   * `envelope_transparent`, `envelope_transparent_run`  a controller that
       is safe on its own is never overridden at maxpol along its run, and
       its enveloped run IS its bare run; `envelope_transparent_iff`: under
       safe init and a safe shield that coincidence characterizes the
       controllers that are safe on their own.

  Pure light HOL4 over the generic core + libertyTheory.
*)
open HolKernel boolLib bossLib BasicProvers
     systemTheory envelopeTheory safetyTheory sv_weakeningTheory libertyTheory;

val _ = new_theory "transparency";

Definition intervenes_def:
  intervenes (pol:('s,'a)policy) (shield:('s,'a)selector)
             (ctrl:('s,'a)selector) s ⇔
    enveloped pol shield ctrl s ≠ ctrl s
End

Theorem intervenes_iff:
  intervenes pol shield ctrl s ⇔ ¬pol s (ctrl s) ∧ shield s ≠ ctrl s
Proof
  rw[intervenes_def, enveloped_def] >> Cases_on ‘pol s (ctrl s)’ >> simp[]
QED

(* A sound policy forbids every unsafe action from a safe state. *)
Theorem sound_policy_forbids_unsafe:
  sound_policy step safe pol ∧ safe s ∧ ¬safe (step s a) ⇒ ¬pol s a
Proof
  rw[sound_policy_def] >> metis_tac[]
QED

(* Every sound envelope with a safe shield stops every unsafe action: the
   policy forbids it, and the safe shield's action cannot coincide with it
   (one successor is safe, the other not). *)
Theorem sound_policy_intervenes_on_unsafe:
  sound_policy step safe pol ∧ safe_shield step safe shield ∧
  safe s ∧ ¬safe (step s (ctrl s)) ⇒
  intervenes pol shield ctrl s
Proof
  rw[intervenes_iff]
  >- metis_tac[sound_policy_forbids_unsafe]
  >> fs[safe_shield_def] >> metis_tac[]
QED

(* Each hypothesis is needed (all witnesses: step s a = a, safe = {0}). *)
Theorem sound_policy_intervenes_on_unsafe_tight:
  (* unsound policy: waves the unsafe action through *)
  (∃(step:num -> num -> num) safe pol shield ctrl s.
     ¬sound_policy step safe pol ∧ safe_shield step safe shield ∧
     safe s ∧ ¬safe (step s (ctrl s)) ∧ ¬intervenes pol shield ctrl s) ∧
  (* unsafe shield: proposes the very same unsafe action *)
  (∃(step:num -> num -> num) safe pol shield ctrl s.
     sound_policy step safe pol ∧ ¬safe_shield step safe shield ∧
     safe s ∧ ¬safe (step s (ctrl s)) ∧ ¬intervenes pol shield ctrl s) ∧
  (* unsafe state: soundness does not constrain it *)
  (∃(step:num -> num -> num) safe pol shield ctrl s.
     sound_policy step safe pol ∧ safe_shield step safe shield ∧
     ¬safe s ∧ ¬safe (step s (ctrl s)) ∧ ¬intervenes pol shield ctrl s) ∧
  (* safe action: a permissive sound policy lets it through *)
  (∃(step:num -> num -> num) safe pol shield ctrl s.
     sound_policy step safe pol ∧ safe_shield step safe shield ∧
     safe s ∧ safe (step s (ctrl s)) ∧ ¬intervenes pol shield ctrl s)
Proof
  rpt conj_tac
  >- (qexistsl_tac [‘λs a. a’, ‘λs. s = 0’, ‘λs a. T’, ‘λs. 0’,
                    ‘λs. 1’, ‘0’] >>
      simp[sound_policy_def, safe_shield_def, intervenes_iff])
  >- (qexistsl_tac [‘λs a. a’, ‘λs. s = 0’, ‘λs a. a = 0’, ‘λs. 1’,
                    ‘λs. 1’, ‘0’] >>
      simp[sound_policy_def, safe_shield_def, intervenes_iff])
  >- (qexistsl_tac [‘λs a. a’, ‘λs. s = 0’, ‘λs a. s ≠ 0 ∨ a = 0’,
                    ‘λs. 0’, ‘λs. 1’, ‘1’] >>
      simp[sound_policy_def, safe_shield_def, intervenes_iff])
  >> qexistsl_tac [‘λs a. a’, ‘λs. s = 0’, ‘λs a. a = 0’, ‘λs. 0’,
                   ‘λs. 0’, ‘0’] >>
  simp[sound_policy_def, safe_shield_def, intervenes_iff]
QED

(* At maxpol, from a safe state, the envelope intervenes exactly on the
   unsafe actions the shield would replace (no side condition). *)
Theorem maxpol_intervenes_exactly:
  safe s ⇒
  (intervenes (maxpol step safe) shield ctrl s ⇔
   ¬safe (step s (ctrl s)) ∧ shield s ≠ ctrl s)
Proof
  rw[intervenes_iff, maxpol_def]
QED

(* With a safe shield: at maxpol the envelope intervenes on precisely the
   unsafe actions. *)
Theorem maxpol_intervenes_iff_unsafe:
  safe_shield step safe shield ∧ safe s ⇒
  (intervenes (maxpol step safe) shield ctrl s ⇔ ¬safe (step s (ctrl s)))
Proof
  rw[maxpol_intervenes_exactly] >> fs[safe_shield_def] >> metis_tac[]
QED

Theorem maxpol_intervenes_iff_unsafe_tight:
  (* unsafe state: maxpol permits everything there *)
  (∃(step:num -> num -> num) safe shield ctrl s.
     safe_shield step safe shield ∧ ¬safe s ∧
     ¬(intervenes (maxpol step safe) shield ctrl s ⇔
       ¬safe (step s (ctrl s)))) ∧
  (* unsafe shield equal to the controller: nothing to intervene with *)
  (∃(step:num -> num -> num) safe shield ctrl s.
     ¬safe_shield step safe shield ∧ safe s ∧
     ¬(intervenes (maxpol step safe) shield ctrl s ⇔
       ¬safe (step s (ctrl s))))
Proof
  conj_tac
  >- (qexistsl_tac [‘λs a. a’, ‘λs. s = 0’, ‘λs. 0’, ‘λs. 1’, ‘1’] >>
      simp[safe_shield_def, intervenes_iff, maxpol_def])
  >> qexistsl_tac [‘λs a. a’, ‘λs. s = 0’, ‘λs. 1’, ‘λs. 1’, ‘0’] >>
  simp[safe_shield_def, intervenes_iff, maxpol_def]
QED

(* Fewer overrides under weakening: every intervention of the weaker policy
   p is an intervention of q. The contrapositive face of authority_monotone. *)
Theorem intervention_monotone:
  weaker p q ⇒
  ∀s. intervenes p shield ctrl s ⇒ intervenes q shield ctrl s
Proof
  rpt strip_tac >> fs[intervenes_iff] >> strip_tac >>
  ‘enveloped q shield ctrl s = ctrl s’ by simp[enveloped_def] >>
  ‘enveloped p shield ctrl s = ctrl s’ by metis_tac[authority_monotone] >>
  gs[enveloped_def]
QED

Theorem intervention_monotone_needs_weaker:
  ∃(p:num -> num -> bool) q shield ctrl s.
    ¬weaker p q ∧ intervenes p shield ctrl s ∧ ¬intervenes q shield ctrl s
Proof
  qexistsl_tac [‘λs a. F’, ‘λs a. T’, ‘λs. 0’, ‘λs. 1’, ‘0’] >>
  simp[weaker_def, intervenes_iff]
QED

(* maxpol overrides least: every sound policy intervenes wherever maxpol
   does. *)
Theorem maxpol_intervenes_least:
  sound_policy step safe pol ⇒
  ∀s. intervenes (maxpol step safe) shield ctrl s ⇒
      intervenes pol shield ctrl s
Proof
  metis_tac[intervention_monotone, maxpol_is_greatest_sound]
QED

Theorem maxpol_intervenes_least_needs_sound:
  ∃(step:num -> num -> num) safe pol shield ctrl s.
    ¬sound_policy step safe pol ∧
    intervenes (maxpol step safe) shield ctrl s ∧
    ¬intervenes pol shield ctrl s
Proof
  qexistsl_tac [‘λs a. a’, ‘λs. s = 0’, ‘λs a. T’, ‘λs. 0’, ‘λs. 1’, ‘0’] >>
  simp[sound_policy_def, intervenes_iff, maxpol_def]
QED

(* ------------------------------------------------------------------ *)
(*  Transparency along a run.                                          *)
(* ------------------------------------------------------------------ *)

(* Two selectors that agree on the second's run have the same run. *)
Theorem reach_agree:
  ∀s. reach step init sel s ⇒
      (∀t. reach step init ctrl t ⇒ sel t = ctrl t) ⇒
      reach step init ctrl s
Proof
  Induct_on ‘reach’ >> rw[] >- metis_tac[reach_rules] >>
  ‘reach step init ctrl s’ by metis_tac[] >>
  ‘sel s = ctrl s’ by metis_tac[] >>
  metis_tac[reach_rules]
QED

(* Globally: a controller safe from every safe state is never overridden
   at maxpol (the envelope is the identity on it). *)
Theorem envelope_transparent_global:
  (∀s. safe s ⇒ safe (step s (ctrl s))) ⇒
  enveloped (maxpol step safe) shield ctrl = ctrl
Proof
  rw[FUN_EQ_THM, enveloped_def, maxpol_def]
QED

(* Along its run: a controller whose bare run stays safe is never
   overridden at maxpol anywhere on that run. *)
Theorem envelope_transparent_on_bare_run:
  invariant step init ctrl safe ⇒
  ∀s. reach step init ctrl s ⇒
      enveloped (maxpol step safe) shield ctrl s = ctrl s
Proof
  rw[invariant_def, enveloped_def, maxpol_def] >>
  metis_tac[reach_rules]
QED

(* THE TRACE-LEVEL THEOREM: the enveloped run of a controller that is safe
   on its own IS its bare run (reachable sets coincide) ... *)
Theorem envelope_transparent_run:
  invariant step init ctrl safe ⇒
  ∀s. reach step init (enveloped (maxpol step safe) shield ctrl) s ⇔
      reach step init ctrl s
Proof
  strip_tac >>
  ‘∀s. reach step init (enveloped (maxpol step safe) shield ctrl) s ⇒
       reach step init ctrl s’
    by (rpt strip_tac >> irule reach_agree >>
        qexists_tac ‘enveloped (maxpol step safe) shield ctrl’ >>
        metis_tac[envelope_transparent_on_bare_run]) >>
  rw[EQ_IMP_THM] >> irule reach_agree >> qexists_tac ‘ctrl’ >>
  metis_tac[envelope_transparent_on_bare_run]
QED

(* ... and along the ENVELOPED run the envelope never overrides it. *)
Theorem envelope_transparent:
  invariant step init ctrl safe ⇒
  ∀s. reach step init (enveloped (maxpol step safe) shield ctrl) s ⇒
      enveloped (maxpol step safe) shield ctrl s = ctrl s
Proof
  metis_tac[envelope_transparent_run, envelope_transparent_on_bare_run]
QED

(* The hypotheses of envelope_transparent_global / _on_bare_run / _run /
   envelope_transparent are needed: a controller that leaves safe (0 -> 1)
   is overridden at the reachable state 0, and its run differs. *)
Theorem envelope_transparent_needs_safe_controller:
  ∃(step:num -> num -> num) safe init shield ctrl.
    init_safe init safe ∧ safe_shield step safe shield ∧
    ¬invariant step init ctrl safe ∧
    ¬(∀s. safe s ⇒ safe (step s (ctrl s))) ∧
    enveloped (maxpol step safe) shield ctrl ≠ ctrl ∧
    reach step init (enveloped (maxpol step safe) shield ctrl) 0 ∧
    enveloped (maxpol step safe) shield ctrl 0 ≠ ctrl 0 ∧
    reach step init ctrl 1 ∧
    ¬reach step init (enveloped (maxpol step safe) shield ctrl) 1
Proof
  qexistsl_tac [‘λs a. a’, ‘λs. s = 0’, ‘λs. s = 0’, ‘λs. 0’, ‘λs. 1’] >>
  ‘reach (λs a. a) (λs. s = 0) (λs. 1) 0’ by simp[Once reach_cases] >>
  ‘reach (λs a. a) (λs. s = 0) (λs. 1) 1’
    by (simp[Once reach_cases] >> metis_tac[]) >>
  ‘reach (λs a. a) (λs. s = 0) (enveloped (maxpol (λs a. a) (λs. s = 0))
          (λs. 0) (λs. 1)) 0’ by simp[Once reach_cases] >>
  ‘∀t. reach (λs a. a) (λs. s = 0)
         (enveloped (maxpol (λs a. a) (λs. s = 0)) (λs. 0) (λs. 1)) t ⇒
       t = 0’
    by (Induct_on ‘reach’ >> simp[enveloped_def, maxpol_def]) >>
  rpt conj_tac
  >- simp[init_safe_def]
  >- simp[safe_shield_def]
  >- (simp[invariant_def] >> qexists_tac ‘1’ >> simp[])
  >- (simp[] >> qexists_tac ‘0’ >> simp[])
  >- (simp[FUN_EQ_THM, enveloped_def, maxpol_def] >> qexists_tac ‘0’ >>
      simp[])
  >- fs[]
  >- simp[enveloped_def, maxpol_def]
  >- fs[]
  >> strip_tac >> res_tac >> fs[]
QED

(* With safe init and a safe shield, run coincidence CHARACTERIZES the
   controllers that are safe on their own. *)
Theorem envelope_transparent_iff:
  init_safe init safe ∧ safe_shield step safe shield ⇒
  (invariant step init ctrl safe ⇔
   ∀s. reach step init (enveloped (maxpol step safe) shield ctrl) s ⇔
       reach step init ctrl s)
Proof
  strip_tac >> eq_tac
  >- metis_tac[envelope_transparent_run]
  >> strip_tac >>
  ‘invariant step init (enveloped (maxpol step safe) shield ctrl) safe’
    by metis_tac[maxpol_envelope_safe] >>
  fs[invariant_def]
QED

(* Both hypotheses of the ⇐ half are needed. (1) Unsafe init: maxpol
   permits everything from the unsafe initial state 1, the runs coincide,
   yet the controller is not safe. (2) A shield equal to the unsafe
   controller: the envelope changes nothing, the runs coincide, the run
   leaves safe. *)
Theorem envelope_transparent_iff_tight:
  (∃(step:num -> num -> num) safe init shield ctrl.
     ¬init_safe init safe ∧ safe_shield step safe shield ∧
     (∀s. reach step init (enveloped (maxpol step safe) shield ctrl) s ⇔
          reach step init ctrl s) ∧
     ¬invariant step init ctrl safe) ∧
  (∃(step:num -> num -> num) safe init shield ctrl.
     init_safe init safe ∧ ¬safe_shield step safe shield ∧
     (∀s. reach step init (enveloped (maxpol step safe) shield ctrl) s ⇔
          reach step init ctrl s) ∧
     ¬invariant step init ctrl safe)
Proof
  conj_tac
  >- (qexistsl_tac [‘λs a. s’, ‘λs. s = 0’, ‘λs. s = 1’, ‘λs. 0’,
                    ‘λs. 0’] >>
      ‘enveloped (maxpol (λs a. s) (λs. s = 0)) (λs. 0) (λs. 0) = (λs. 0)’
        by simp[FUN_EQ_THM, enveloped_def] >>
      simp[init_safe_def, safe_shield_def, invariant_def] >>
      qexists_tac ‘1’ >> simp[Once reach_cases])
  >> qexistsl_tac [‘λs a. a’, ‘λs. s = 0’, ‘λs. s = 0’, ‘λs. 1’,
                   ‘λs. 1’] >>
  ‘enveloped (maxpol (λs a. a) (λs. s = 0)) (λs. 1) (λs. 1) = (λs. 1)’
    by simp[FUN_EQ_THM, enveloped_def] >>
  simp[init_safe_def, safe_shield_def, invariant_def] >>
  qexists_tac ‘1’ >>
  ‘reach (λs a. a) (λs. s = 0) (λs. 1) 0’ by simp[Once reach_cases] >>
  drule reach_step >> simp[]
QED

val _ = export_theory ();
