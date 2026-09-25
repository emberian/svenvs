(*
  relTransparencyScript — maximal liberty and minimal intervention over a
  relational plant.

   * maxpolr: from a safe state permit exactly the actions ALL of whose
     successors are safe (blocked actions are permitted: vacuously sound).
     maxpolr_sound, maxpolr_is_greatest_sound, maxpolr_envelope_safe,
     maxpolr_det (= libertyTheory.maxpol on det).
   * maxpolr_intervenes_exactly: at maxpolr, from a safe state, the envelope
     overrides exactly the actions that MAY lead out of safe (some successor
     unsafe) when the shield proposes something else.
     maxpolr_intervenes_iff_unsafe (+ _tight): with a safe shield, exactly
     the possibly-unsafe actions -- even if the plant would in fact have
     resolved that step safely. Liveness of the shield is NOT needed.
   * envelope_transparent_runr: a controller whose bare relational run is
     safe (for every resolution of the plant) has enveloped run = bare run;
     envelope_transparent_iffr characterizes those controllers;
     envelope_transparent_runr_needs_safe_controller.
   * Deterministic collapse: maxpol_intervenes_exactly_from_rel and
     envelope_transparent_run_from_rel re-derive transparencyTheory's
     statements verbatim.
*)
open HolKernel boolLib bossLib BasicProvers
     systemTheory envelopeTheory safetyTheory sv_weakeningTheory
     libertyTheory transparencyTheory relSystemTheory relEnvelopeTheory;

val _ = new_theory "relTransparency";

Definition maxpolr_def:
  maxpolr (stepr:'s -> 'a -> 's -> bool) safe : 's -> 'a -> bool =
    λs a. safe s ⇒ ∀s'. stepr s a s' ⇒ safe s'
End

Theorem maxpolr_sound:
  sound_policyr stepr safe (maxpolr stepr safe)
Proof
  rw[sound_policyr_def, maxpolr_def] >> metis_tac[]
QED

Theorem maxpolr_is_greatest_sound:
  sound_policyr stepr safe pol ⇒ weaker (maxpolr stepr safe) pol
Proof
  rw[weaker_def, maxpolr_def] >> fs[sound_policyr_def] >> metis_tac[]
QED

Theorem maxpolr_envelope_safe:
  init_safe init safe ∧ safe_shieldr stepr safe shield ⇒
  ∀ctrl. invariantr stepr init (enveloped (maxpolr stepr safe) shield ctrl)
                    safe
Proof
  rpt strip_tac >> irule safety_preservationr >>
  metis_tac[maxpolr_sound]
QED

Theorem maxpolr_det:
  maxpolr (det step) safe = maxpol step safe
Proof
  simp[FUN_EQ_THM, maxpolr_def, maxpol_def, det_def]
QED

Theorem maxpolr_intervenes_exactly:
  safe s ⇒
  (intervenes (maxpolr stepr safe) shield ctrl s ⇔
   (∃s'. stepr s (ctrl s) s' ∧ ¬safe s') ∧ shield s ≠ ctrl s)
Proof
  rw[intervenes_iff, maxpolr_def] >> metis_tac[]
QED

Theorem maxpolr_intervenes_iff_unsafe:
  safe_shieldr stepr safe shield ∧ safe s ⇒
  (intervenes (maxpolr stepr safe) shield ctrl s ⇔
   ∃s'. stepr s (ctrl s) s' ∧ ¬safe s')
Proof
  rw[maxpolr_intervenes_exactly] >> fs[safe_shieldr_def] >> metis_tac[]
QED

(* Both hypotheses needed (stepr s a s' ⇔ s' = a, safe = {0}): (1) at the
   unsafe state 1 maxpolr permits everything; (2) a shield equal to the
   unsafe controller has nothing to intervene with. *)
Theorem maxpolr_intervenes_iff_unsafe_tight:
  (∃(stepr:num -> num -> num -> bool) safe shield ctrl s.
     safe_shieldr stepr safe shield ∧ ¬safe s ∧
     ¬(intervenes (maxpolr stepr safe) shield ctrl s ⇔
       ∃s'. stepr s (ctrl s) s' ∧ ¬safe s')) ∧
  (∃(stepr:num -> num -> num -> bool) safe shield ctrl s.
     ¬safe_shieldr stepr safe shield ∧ safe s ∧
     ¬(intervenes (maxpolr stepr safe) shield ctrl s ⇔
       ∃s'. stepr s (ctrl s) s' ∧ ¬safe s'))
Proof
  conj_tac
  >- (qexistsl_tac [‘λs a s'. s' = a’, ‘λs. s = 0’, ‘λs. 0’, ‘λs. 1’,
                    ‘1’] >>
      simp[safe_shieldr_def, intervenes_iff, maxpolr_def])
  >> qexistsl_tac [‘λs a s'. s' = a’, ‘λs. s = 0’, ‘λs. 1’, ‘λs. 1’, ‘0’] >>
  simp[safe_shieldr_def, intervenes_iff, maxpolr_def]
QED

(* ------------------------------------------------------------------ *)
(*  Transparency along a relational run.                               *)
(* ------------------------------------------------------------------ *)

Theorem reachr_agree:
  ∀s. reachr stepr init sel s ⇒
      (∀t. reachr stepr init ctrl t ⇒ sel t = ctrl t) ⇒
      reachr stepr init ctrl s
Proof
  Induct_on ‘reachr’ >> rw[] >- metis_tac[reachr_rules] >>
  ‘reachr stepr init ctrl s’ by metis_tac[] >>
  ‘sel s = ctrl s’ by metis_tac[] >>
  fs[] >> metis_tac[reachr_rules]
QED

Theorem envelope_transparent_on_bare_runr:
  invariantr stepr init ctrl safe ⇒
  ∀s. reachr stepr init ctrl s ⇒
      enveloped (maxpolr stepr safe) shield ctrl s = ctrl s
Proof
  rpt strip_tac >>
  ‘maxpolr stepr safe s (ctrl s)’
    by (simp[maxpolr_def] >> fs[invariantr_def] >>
        metis_tac[reachr_rules]) >>
  simp[enveloped_def]
QED

(* THE TRACE-LEVEL THEOREM over relations: the enveloped run of a
   controller that is safe on its own, whatever the plant does, IS its
   bare run. *)
Theorem envelope_transparent_runr:
  invariantr stepr init ctrl safe ⇒
  ∀s. reachr stepr init (enveloped (maxpolr stepr safe) shield ctrl) s ⇔
      reachr stepr init ctrl s
Proof
  strip_tac >>
  ‘∀s. reachr stepr init (enveloped (maxpolr stepr safe) shield ctrl) s ⇒
       reachr stepr init ctrl s’
    by (rpt strip_tac >> irule reachr_agree >>
        qexists_tac ‘enveloped (maxpolr stepr safe) shield ctrl’ >>
        metis_tac[envelope_transparent_on_bare_runr]) >>
  rw[EQ_IMP_THM] >> irule reachr_agree >> qexists_tac ‘ctrl’ >>
  metis_tac[envelope_transparent_on_bare_runr]
QED

Theorem envelope_transparentr:
  invariantr stepr init ctrl safe ⇒
  ∀s. reachr stepr init (enveloped (maxpolr stepr safe) shield ctrl) s ⇒
      enveloped (maxpolr stepr safe) shield ctrl s = ctrl s
Proof
  metis_tac[envelope_transparent_runr, envelope_transparent_on_bare_runr]
QED

Theorem envelope_transparent_iffr:
  init_safe init safe ∧ safe_shieldr stepr safe shield ⇒
  (invariantr stepr init ctrl safe ⇔
   ∀s. reachr stepr init (enveloped (maxpolr stepr safe) shield ctrl) s ⇔
       reachr stepr init ctrl s)
Proof
  strip_tac >> eq_tac
  >- metis_tac[envelope_transparent_runr]
  >> strip_tac >>
  ‘invariantr stepr init (enveloped (maxpolr stepr safe) shield ctrl) safe’
    by metis_tac[maxpolr_envelope_safe] >>
  fs[invariantr_def]
QED

(* The safe-controller hypothesis of the run theorems is needed:
   transported from transparencyTheory's deterministic witness. *)
Theorem envelope_transparent_runr_needs_safe_controller:
  ∃(stepr:num -> num -> num -> bool) safe init shield ctrl.
    init_safe init safe ∧ safe_shieldr stepr safe shield ∧
    ¬invariantr stepr init ctrl safe ∧
    ¬(∀s. reachr stepr init (enveloped (maxpolr stepr safe) shield ctrl) s ⇔
          reachr stepr init ctrl s)
Proof
  strip_assume_tac envelope_transparent_needs_safe_controller >>
  qexistsl_tac [‘det step’, ‘safe’, ‘init’, ‘shield’, ‘ctrl’] >>
  fs[safe_shieldr_det, invariantr_det, reachr_det, maxpolr_det] >>
  qexists_tac ‘1’ >> fs[]
QED

(* ------------------------------------------------------------------ *)
(*  Deterministic collapse: transparencyTheory's statements, verbatim.  *)
(* ------------------------------------------------------------------ *)

Theorem maxpol_intervenes_exactly_from_rel:
  safe s ⇒
  (intervenes (maxpol step safe) shield ctrl s ⇔
   ¬safe (step s (ctrl s)) ∧ shield s ≠ ctrl s)
Proof
  strip_tac >>
  ‘intervenes (maxpolr (det step) safe) shield ctrl s ⇔
   (∃s'. det step s (ctrl s) s' ∧ ¬safe s') ∧ shield s ≠ ctrl s’
    by metis_tac[maxpolr_intervenes_exactly] >>
  fs[maxpolr_det, det_def]
QED

Theorem envelope_transparent_run_from_rel:
  invariant step init ctrl safe ⇒
  ∀s. reach step init (enveloped (maxpol step safe) shield ctrl) s ⇔
      reach step init ctrl s
Proof
  rewrite_tac[GSYM invariantr_det, GSYM reachr_det, GSYM maxpolr_det] >>
  MATCH_ACCEPT_TAC envelope_transparent_runr
QED

val _ = export_theory ();
