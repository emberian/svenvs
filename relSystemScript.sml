(*
  relSystemScript — the plant as a RELATION.

  systemTheory's plant is a function `step : 's -> 'a -> 's`: one action,
  one successor. Here the plant is `stepr : 's -> 'a -> 's -> bool`: an
  action may have MANY successors (disturbance, an adversarial environment,
  a partial model) or NONE (a blocked action). Runs, invariants and the
  inductive-invariant principle are re-derived over it, and the
  deterministic plant is the instance `det step` (the graph of step):

    reachr_det         reachr (det step) init sel = reach step init sel
    invariantr_det, step_closedr_det, det_total
    invariant_intro_from_rel   systemTheory.invariant_intro, verbatim,
                               as a corollary of invariantr_intro.

  A blocked action simply ends the run: `reachr_blocked` shows a plant
  with no transitions reaches exactly its initial states. Invariance is a
  statement about the states that ARE reached; deadlock is not a safety
  violation (relEnvelopeTheory.enveloped_nonblocking is the liveness side).
*)
open HolKernel boolLib bossLib BasicProvers systemTheory;

val _ = new_theory "relSystem";

(* States reachable from [init] when [sel] picks the action and the plant
   picks ANY successor it allows. *)
Inductive reachr:
[~init:]
  (init s ⇒ reachr stepr init sel s)
[~step:]
  (reachr stepr init sel s ∧ stepr s (sel s) s' ⇒ reachr stepr init sel s')
End

Definition invariantr_def:
  invariantr (stepr:'s -> 'a -> 's -> bool) init sel safe ⇔
    ∀s. reachr stepr init sel s ⇒ safe s
End

(* Every successor of a safe state under the selected action is safe. *)
Definition step_closedr_def:
  step_closedr (stepr:'s -> 'a -> 's -> bool) sel safe ⇔
    ∀s s'. safe s ∧ stepr s (sel s) s' ⇒ safe s'
End

Theorem reachr_init_step:
  init s ∧ stepr s (sel s) s' ⇒ reachr stepr init sel s'
Proof
  metis_tac[reachr_rules]
QED

Theorem invariantr_intro:
  init_safe init safe ∧ step_closedr stepr sel safe ⇒
  invariantr stepr init sel safe
Proof
  strip_tac >> simp[invariantr_def] >>
  ho_match_mp_tac reachr_ind >>
  fs[init_safe_def, step_closedr_def] >> metis_tac[]
QED

(* Both hypotheses are needed. (1) unsafe initial state 1 (every step goes
   to the safe 0); (2) safe start 0, every step goes to the unsafe 1. *)
Theorem invariantr_intro_tight:
  (∃(stepr:num -> num -> num -> bool) init sel safe.
     step_closedr stepr sel safe ∧ ¬invariantr stepr init sel safe) ∧
  (∃(stepr:num -> num -> num -> bool) init sel safe.
     init_safe init safe ∧ ¬invariantr stepr init sel safe)
Proof
  conj_tac
  >- (qexistsl_tac [‘λs a s'. s' = 0’, ‘λs. s = 1’, ‘λs. 0’, ‘λs. s = 0’] >>
      simp[step_closedr_def, invariantr_def] >> qexists_tac ‘1’ >>
      simp[Once reachr_cases])
  >> qexistsl_tac [‘λs a s'. s' = 1’, ‘λs. s = 0’, ‘λs. 0’, ‘λs. s = 0’] >>
  simp[init_safe_def, invariantr_def] >> qexists_tac ‘1’ >> simp[] >>
  irule reachr_init_step >> qexists_tac ‘0’ >> simp[]
QED

(* ------------------------------------------------------------------ *)
(*  Enabledness and totality.                                          *)
(* ------------------------------------------------------------------ *)

Definition enabled_def:
  enabled (stepr:'s -> 'a -> 's -> bool) s a ⇔ ∃s'. stepr s a s'
End

Definition total_def:
  total (stepr:'s -> 'a -> 's -> bool) ⇔ ∀s a. enabled stepr s a
End

(* A plant with no transitions reaches exactly its initial states. *)
Theorem reachr_blocked:
  reachr (λs a s'. F) init sel s ⇔ init s
Proof
  simp[Once reachr_cases]
QED

(* ------------------------------------------------------------------ *)
(*  The deterministic plant is an instance.                            *)
(* ------------------------------------------------------------------ *)

Definition det_def:
  det (step:'s -> 'a -> 's) s a s' ⇔ s' = step s a
End

Theorem det_total:
  total (det step)
Proof
  simp[total_def, enabled_def, det_def]
QED

Theorem reachr_det:
  reachr (det step) init sel = reach step init sel
Proof
  simp[FUN_EQ_THM] >> gen_tac >> eq_tac
  >- (qid_spec_tac ‘x’ >> ho_match_mp_tac reachr_ind >>
      rw[det_def] >> metis_tac[reach_rules])
  >> qid_spec_tac ‘x’ >> ho_match_mp_tac reach_ind >> rw[] >>
  metis_tac[reachr_rules, det_def]
QED

Theorem invariantr_det:
  invariantr (det step) init sel safe ⇔ invariant step init sel safe
Proof
  simp[invariantr_def, invariant_def, reachr_det]
QED

Theorem step_closedr_det:
  step_closedr (det step) sel safe ⇔ step_closed step sel safe
Proof
  simp[step_closedr_def, step_closed_def, det_def]
QED

(* systemTheory.invariant_intro, verbatim, as the det instance. *)
Theorem invariant_intro_from_rel:
  init_safe init safe ∧ step_closed step sel safe ⇒
  invariant step init sel safe
Proof
  rewrite_tac[GSYM invariantr_det, GSYM step_closedr_det] >>
  MATCH_ACCEPT_TAC invariantr_intro
QED

val _ = export_theory ();
