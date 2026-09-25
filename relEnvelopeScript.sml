(*
  relEnvelopeScript — the envelope over a relational plant.

  Same envelope (envelopeTheory.enveloped, plant-independent), same gate
  (upgradeTheory.gate), same weakening order (sv_weakeningTheory.weaker,
  authority_monotone: both plant-independent). What changes is soundness:
  a permitted action from a safe state must keep EVERY possible successor
  safe (demonic). Contents:

   * sound_policyr / safe_shieldr, enveloped_step_closedr,
     safety_preservationr, enveloped_states_safer (+ _tight).
   * Blocked actions: soundness is vacuous on them (sound_policyr_blocked,
     sound_policyr_enabled_only, safe_shieldr_blocked). Safety needs no
     totality; NON-BLOCKING does: enveloped_nonblocking needs a live policy
     and a live shield (both automatic under `total`), _tight.
   * Many successors: angelic ("some successor is safe") soundness does not
     suffice (angelic_soundness_insufficient); on a deterministic plant the
     two coincide (angelic_soundr_det).
   * Weakening and the gate: sound_policyr_weaker, safe_weakeningr,
     gate_keeps_soundr, gate_preserves_safetyr, certified_gate_correctr,
     certifier_gate_preserves_safetyr (through certifierTheory.cgate_safe),
     with necessity witnesses transported from the det instance.
   * Disturbance: `disturbed dstep D` is the plant driven by an adversary
     choosing any admissible disturbance each step; `drun` is the run under
     a disturbance sequence, reachr_disturbed_iff_drun says the relational
     run IS the set of all such runs, and robust_envelope is the envelope
     theorem for every disturbance sequence. nominal_soundness_insufficient:
     soundness against the nominal disturbance is not enough.
   * Deterministic corollaries (the _det and _from_rel theorems): the existing envelope,
     safety, weakening and gate theorems, verbatim.
*)
open HolKernel boolLib bossLib BasicProvers
     systemTheory envelopeTheory safetyTheory sv_weakeningTheory
     certifierTheory upgradeTheory relSystemTheory;

val _ = new_theory "relEnvelope";

(* Every permitted action from a safe state keeps every successor safe.
   VACUOUS on blocked actions (no successor): see sound_policyr_blocked. *)
Definition sound_policyr_def:
  sound_policyr (stepr:'s -> 'a -> 's -> bool) safe (pol:'s -> 'a -> bool) ⇔
    ∀s a s'. safe s ∧ pol s a ∧ stepr s a s' ⇒ safe s'
End

Definition safe_shieldr_def:
  safe_shieldr (stepr:'s -> 'a -> 's -> bool) safe (shield:'s -> 'a) ⇔
    ∀s s'. safe s ∧ stepr s (shield s) s' ⇒ safe s'
End

Theorem enveloped_step_closedr:
  sound_policyr stepr safe pol ∧ safe_shieldr stepr safe shield ⇒
  step_closedr stepr (enveloped pol shield ctrl) safe
Proof
  rw[step_closedr_def] >> fs[sound_policyr_def, safe_shieldr_def] >>
  Cases_on ‘pol s (ctrl s)’ >> fs[enveloped_def] >> metis_tac[]
QED

Theorem safety_preservationr:
  init_safe init safe ∧
  sound_policyr stepr safe pol ∧
  safe_shieldr stepr safe shield ⇒
  ∀ctrl. invariantr stepr init (enveloped pol shield ctrl) safe
Proof
  rpt strip_tac >> irule invariantr_intro >>
  metis_tac[enveloped_step_closedr]
QED

Theorem enveloped_states_safer:
  init_safe init safe ∧
  sound_policyr stepr safe pol ∧
  safe_shieldr stepr safe shield ∧
  reachr stepr init (enveloped pol shield ctrl) s ⇒
  safe s
Proof
  metis_tac[safety_preservationr, invariantr_def]
QED

(* Each hypothesis is needed (stepr s a s' ⇔ s' = a, safe = {0}):
   (1) unsafe init 1; (2) a policy permitting the unsafe action 1;
   (3) a policy permitting nothing and a shield that picks 1. *)
Theorem safety_preservationr_tight:
  (∃(stepr:num -> num -> num -> bool) safe init pol shield ctrl.
     sound_policyr stepr safe pol ∧ safe_shieldr stepr safe shield ∧
     ¬invariantr stepr init (enveloped pol shield ctrl) safe) ∧
  (∃(stepr:num -> num -> num -> bool) safe init pol shield ctrl.
     init_safe init safe ∧ safe_shieldr stepr safe shield ∧
     ¬invariantr stepr init (enveloped pol shield ctrl) safe) ∧
  (∃(stepr:num -> num -> num -> bool) safe init pol shield ctrl.
     init_safe init safe ∧ sound_policyr stepr safe pol ∧
     ¬invariantr stepr init (enveloped pol shield ctrl) safe)
Proof
  rpt conj_tac
  >- (qexistsl_tac [‘λs a s'. s' = a’, ‘λs. s = 0’, ‘λs. s = 1’,
                    ‘λs a. a = 0’, ‘λs. 0’, ‘λs. 0’] >>
      simp[sound_policyr_def, safe_shieldr_def, invariantr_def] >>
      qexists_tac ‘1’ >> simp[Once reachr_cases])
  >- (qexistsl_tac [‘λs a s'. s' = a’, ‘λs. s = 0’, ‘λs. s = 0’,
                    ‘λs a. T’, ‘λs. 0’, ‘λs. 1’] >>
      simp[init_safe_def, safe_shieldr_def, invariantr_def] >>
      qexists_tac ‘1’ >> simp[] >>
      irule reachr_init_step >> qexists_tac ‘0’ >> simp[enveloped_def])
  >> qexistsl_tac [‘λs a s'. s' = a’, ‘λs. s = 0’, ‘λs. s = 0’,
                   ‘λs a. F’, ‘λs. 1’, ‘λs. 0’] >>
  simp[init_safe_def, sound_policyr_def, invariantr_def] >>
  qexists_tac ‘1’ >> simp[] >>
  irule reachr_init_step >> qexists_tac ‘0’ >> simp[enveloped_def]
QED

(* ------------------------------------------------------------------ *)
(*  (a) Blocked actions, totality, non-blocking.                       *)
(* ------------------------------------------------------------------ *)

(* Soundness says nothing about blocked actions: a policy permitting only
   blocked actions is sound, and a policy's blocked part is irrelevant. *)
Theorem sound_policyr_blocked:
  (∀s a. pol s a ⇒ ¬enabled stepr s a) ⇒ sound_policyr stepr safe pol
Proof
  rw[sound_policyr_def, enabled_def] >> metis_tac[]
QED

Theorem sound_policyr_enabled_only:
  sound_policyr stepr safe pol ⇔
  sound_policyr stepr safe (λs a. pol s a ∧ enabled stepr s a)
Proof
  rw[sound_policyr_def, enabled_def] >> metis_tac[]
QED

(* ... and a shield that always blocks is "safe": it saves by deadlock. *)
Theorem safe_shieldr_blocked:
  (∀s. ¬enabled stepr s (shield s)) ⇒ safe_shieldr stepr safe shield
Proof
  rw[safe_shieldr_def, enabled_def] >> metis_tac[]
QED

Definition live_policyr_def:
  live_policyr (stepr:'s -> 'a -> 's -> bool) safe (pol:'s -> 'a -> bool) ⇔
    ∀s a. safe s ∧ pol s a ⇒ enabled stepr s a
End

Definition live_shieldr_def:
  live_shieldr (stepr:'s -> 'a -> 's -> bool) safe (shield:'s -> 'a) ⇔
    ∀s. safe s ⇒ enabled stepr s (shield s)
End

Theorem total_live:
  total stepr ⇒ live_policyr stepr safe pol ∧ live_shieldr stepr safe shield
Proof
  rw[total_def, live_policyr_def, live_shieldr_def]
QED

(* Safety needs no totality (safety_preservationr); NON-BLOCKING does:
   the enveloped run can always take another step. *)
Theorem enveloped_nonblocking:
  init_safe init safe ∧
  sound_policyr stepr safe pol ∧ safe_shieldr stepr safe shield ∧
  live_policyr stepr safe pol ∧ live_shieldr stepr safe shield ⇒
  ∀ctrl s. reachr stepr init (enveloped pol shield ctrl) s ⇒
           enabled stepr s (enveloped pol shield ctrl s)
Proof
  rpt strip_tac >>
  ‘safe s’ by metis_tac[enveloped_states_safer] >>
  fs[live_policyr_def, live_shieldr_def] >>
  Cases_on ‘pol s (ctrl s)’ >> simp[enveloped_def] >> metis_tac[]
QED

(* Under totality nothing can block, anywhere. *)
Theorem enveloped_nonblocking_total:
  total stepr ⇒ ∀ctrl s. enabled stepr s (enveloped pol shield ctrl s)
Proof
  rw[total_def]
QED

(* Every hypothesis of enveloped_nonblocking is needed. Witnesses over num,
   safe = {0}, init = {0} unless said: (1) unsafe init 1, a plant that only
   moves 0; (2)-(3) a plant defined only at 0 that goes where the action
   says: an unsound policy / an unsafe shield leads to the blocked 1;
   (4)-(5) the empty plant: a policy permitting / a shield choosing a
   blocked action from 0. *)
Theorem enveloped_nonblocking_tight:
  (∃(stepr:num -> num -> num -> bool) safe init pol shield ctrl s.
     sound_policyr stepr safe pol ∧ safe_shieldr stepr safe shield ∧
     live_policyr stepr safe pol ∧ live_shieldr stepr safe shield ∧
     reachr stepr init (enveloped pol shield ctrl) s ∧
     ¬enabled stepr s (enveloped pol shield ctrl s)) ∧
  (∃(stepr:num -> num -> num -> bool) safe init pol shield ctrl s.
     init_safe init safe ∧ safe_shieldr stepr safe shield ∧
     live_policyr stepr safe pol ∧ live_shieldr stepr safe shield ∧
     reachr stepr init (enveloped pol shield ctrl) s ∧
     ¬enabled stepr s (enveloped pol shield ctrl s)) ∧
  (∃(stepr:num -> num -> num -> bool) safe init pol shield ctrl s.
     init_safe init safe ∧ sound_policyr stepr safe pol ∧
     live_policyr stepr safe pol ∧ live_shieldr stepr safe shield ∧
     reachr stepr init (enveloped pol shield ctrl) s ∧
     ¬enabled stepr s (enveloped pol shield ctrl s)) ∧
  (∃(stepr:num -> num -> num -> bool) safe init pol shield ctrl s.
     init_safe init safe ∧
     sound_policyr stepr safe pol ∧ safe_shieldr stepr safe shield ∧
     live_shieldr stepr safe shield ∧
     reachr stepr init (enveloped pol shield ctrl) s ∧
     ¬enabled stepr s (enveloped pol shield ctrl s)) ∧
  (∃(stepr:num -> num -> num -> bool) safe init pol shield ctrl s.
     init_safe init safe ∧
     sound_policyr stepr safe pol ∧ safe_shieldr stepr safe shield ∧
     live_policyr stepr safe pol ∧
     reachr stepr init (enveloped pol shield ctrl) s ∧
     ¬enabled stepr s (enveloped pol shield ctrl s))
Proof
  rpt conj_tac
  >- (qexistsl_tac [‘λs a s'. s = 0 ∧ s' = 0’, ‘λs. s = 0’, ‘λs. s = 1’,
                    ‘λs a. T’, ‘λs. 0’, ‘λs. 0’, ‘1’] >>
      simp[sound_policyr_def, safe_shieldr_def, live_policyr_def,
           live_shieldr_def, enabled_def, Once reachr_cases])
  >- (qexistsl_tac [‘λs a s'. s = 0 ∧ s' = a’, ‘λs. s = 0’, ‘λs. s = 0’,
                    ‘λs a. T’, ‘λs. 0’, ‘λs. 1’, ‘1’] >>
      simp[init_safe_def, safe_shieldr_def, live_policyr_def,
           live_shieldr_def, enabled_def, enveloped_def] >>
      irule reachr_init_step >> qexists_tac ‘0’ >> simp[enveloped_def])
  >- (qexistsl_tac [‘λs a s'. s = 0 ∧ s' = a’, ‘λs. s = 0’, ‘λs. s = 0’,
                    ‘λs a. F’, ‘λs. 1’, ‘λs. 0’, ‘1’] >>
      simp[init_safe_def, sound_policyr_def, live_policyr_def,
           live_shieldr_def, enabled_def, enveloped_def] >>
      irule reachr_init_step >> qexists_tac ‘0’ >> simp[enveloped_def])
  >- (qexistsl_tac [‘λs a s'. a = 0 ∧ s' = 0’, ‘λs. s = 0’, ‘λs. s = 0’,
                    ‘λs a. T’, ‘λs. 0’, ‘λs. 1’, ‘0’] >>
      simp[init_safe_def, sound_policyr_def, safe_shieldr_def,
           live_shieldr_def, enabled_def, enveloped_def, Once reachr_cases])
  >> qexistsl_tac [‘λs a s'. a = 0 ∧ s' = 0’, ‘λs. s = 0’, ‘λs. s = 0’,
                   ‘λs a. a = 0’, ‘λs. 1’, ‘λs. 1’, ‘0’] >>
  simp[init_safe_def, sound_policyr_def, safe_shieldr_def,
       live_policyr_def, enabled_def, enveloped_def, Once reachr_cases]
QED

(* ------------------------------------------------------------------ *)
(*  Many successors: demonic soundness is the right notion.            *)
(* ------------------------------------------------------------------ *)

Definition angelic_soundr_def:
  angelic_soundr (stepr:'s -> 'a -> 's -> bool) safe (pol:'s -> 'a -> bool) ⇔
    ∀s a. safe s ∧ pol s a ⇒ ∃s'. stepr s a s' ∧ safe s'
End

(* The plant may go anywhere up to the action: 0 is safe, 1 is not; the
   policy permits action 1 because SOME successor (0) is safe; the plant
   picks 1. *)
Theorem angelic_soundness_insufficient:
  ∃(stepr:num -> num -> num -> bool) safe init pol shield ctrl.
    init_safe init safe ∧ angelic_soundr stepr safe pol ∧
    safe_shieldr stepr safe shield ∧ live_shieldr stepr safe shield ∧
    ¬sound_policyr stepr safe pol ∧
    ¬invariantr stepr init (enveloped pol shield ctrl) safe
Proof
  qexistsl_tac [‘λs a s'. s' ≤ a’, ‘λs. s = 0’, ‘λs. s = 0’, ‘λs a. T’,
                ‘λs. 0’, ‘λs. 1’] >>
  rpt conj_tac
  >- simp[init_safe_def]
  >- (simp[angelic_soundr_def] >> rpt strip_tac >> qexists_tac ‘0’ >>
      simp[])
  >- simp[safe_shieldr_def]
  >- (simp[live_shieldr_def, enabled_def] >> rpt strip_tac >>
      qexists_tac ‘0’ >> simp[])
  >- (simp[sound_policyr_def] >>
      metis_tac[DECIDE “(1:num) ≤ 1 ∧ (1:num) ≠ 0”])
  >> simp[invariantr_def] >> qexists_tac ‘1’ >> simp[] >>
  irule reachr_init_step >> qexists_tac ‘0’ >> simp[enveloped_def]
QED

(* ------------------------------------------------------------------ *)
(*  Weakening and the gate.                                            *)
(* ------------------------------------------------------------------ *)

Theorem sound_policyr_weaker:
  weaker p q ∧ sound_policyr stepr safe p ⇒ sound_policyr stepr safe q
Proof
  rw[weaker_def, sound_policyr_def] >> metis_tac[]
QED

Theorem safe_weakeningr:
  init_safe init safe ∧
  safe_shieldr stepr safe shield ∧
  weaker p q ∧
  sound_policyr stepr safe p ⇒
  ∀ctrl. invariantr stepr init (enveloped p shield ctrl) safe ∧
         ∀s. enveloped q shield ctrl s = ctrl s ∧ q s (ctrl s) ⇒
             enveloped p shield ctrl s = ctrl s
Proof
  rpt strip_tac
  >- (irule safety_preservationr >> fs[])
  >> metis_tac[authority_monotone]
QED

Definition admissibler_def:
  admissibler (stepr:'s -> 'a -> 's -> bool) safe oldp newp ⇔
    sound_policyr stepr safe newp ∧ weaker newp oldp
End

Theorem gate_keeps_soundr:
  (cert ⇒ sound_policyr stepr safe newp) ∧
  sound_policyr stepr safe oldp ⇒
  sound_policyr stepr safe (gate cert oldp newp)
Proof
  metis_tac[gate_is_cgate, cgate_keeps]
QED

Theorem gate_preserves_safetyr:
  (cert ⇒ sound_policyr stepr safe newp) ∧
  init_safe init safe ∧
  safe_shieldr stepr safe shield ∧
  sound_policyr stepr safe oldp ⇒
  ∀ctrl. invariantr stepr init (enveloped (gate cert oldp newp) shield ctrl)
                    safe
Proof
  rpt strip_tac >> irule safety_preservationr >>
  metis_tac[gate_keeps_soundr]
QED

Theorem certified_gate_correctr:
  (cert ⇒ admissibler stepr safe oldp newp) ∧
  init_safe init safe ∧
  safe_shieldr stepr safe shield ∧
  sound_policyr stepr safe oldp ⇒
  (∀ctrl. invariantr stepr init (enveloped (gate cert oldp newp) shield ctrl)
                     safe) ∧
  weaker (gate cert oldp newp) oldp
Proof
  rpt strip_tac
  >- (irule gate_preserves_safetyr >> fs[admissibler_def])
  >> Cases_on ‘cert’ >> fs[gate_def, admissibler_def, weaker_refl]
QED

(* Any certifier, through the gate: certifierTheory.cgate_safe at the
   judge `sound_policyr stepr safe`. *)
Theorem certifier_gate_preserves_safetyr:
  sound_certifier chk sem ∧
  (sem ob ⇒ admissibler stepr safe oldp newp) ∧
  init_safe init safe ∧
  safe_shieldr stepr safe shield ∧
  sound_policyr stepr safe oldp ⇒
  ∀ctrl. invariantr stepr init
            (enveloped (gate (chk ob) oldp newp) shield ctrl) safe
Proof
  rpt strip_tac >> irule safety_preservationr >> simp[gate_is_cgate] >>
  irule cgate_safe >> fs[admissibler_def] >> metis_tac[]
QED

(* ------------------------------------------------------------------ *)
(*  Deterministic collapse.                                            *)
(* ------------------------------------------------------------------ *)

Theorem sound_policyr_det:
  sound_policyr (det step) safe pol ⇔ sound_policy step safe pol
Proof
  simp[sound_policyr_def, sound_policy_def, det_def]
QED

Theorem safe_shieldr_det:
  safe_shieldr (det step) safe shield ⇔ safe_shield step safe shield
Proof
  simp[safe_shieldr_def, safe_shield_def, det_def]
QED

Theorem admissibler_det:
  admissibler (det step) safe oldp newp ⇔ admissible step safe oldp newp
Proof
  simp[admissibler_def, admissible_def, sound_policyr_det]
QED

(* On a deterministic plant angelic and demonic soundness coincide: the
   gap in angelic_soundness_insufficient is exactly nondeterminism. *)
Theorem angelic_soundr_det:
  angelic_soundr (det step) safe pol ⇔ sound_policy step safe pol
Proof
  simp[angelic_soundr_def, sound_policy_def, det_def]
QED

Theorem enveloped_step_closed_from_rel:
  sound_policy step safe pol ∧ safe_shield step safe shield ⇒
  step_closed step (enveloped pol shield ctrl) safe
Proof
  rewrite_tac[GSYM sound_policyr_det, GSYM safe_shieldr_det,
              GSYM step_closedr_det] >>
  MATCH_ACCEPT_TAC enveloped_step_closedr
QED

Theorem safety_preservation_from_rel:
  init_safe init safe ∧
  sound_policy step safe pol ∧
  safe_shield step safe shield ⇒
  ∀ctrl. invariant step init (enveloped pol shield ctrl) safe
Proof
  rewrite_tac[GSYM sound_policyr_det, GSYM safe_shieldr_det,
              GSYM invariantr_det] >>
  MATCH_ACCEPT_TAC safety_preservationr
QED

Theorem enveloped_states_safe_from_rel:
  init_safe init safe ∧
  sound_policy step safe pol ∧
  safe_shield step safe shield ∧
  reach step init (enveloped pol shield ctrl) s ⇒
  safe s
Proof
  rewrite_tac[GSYM sound_policyr_det, GSYM safe_shieldr_det,
              GSYM reachr_det] >>
  MATCH_ACCEPT_TAC enveloped_states_safer
QED

Theorem sound_policy_weaker_from_rel:
  weaker p q ∧ sound_policy step safe p ⇒ sound_policy step safe q
Proof
  rewrite_tac[GSYM sound_policyr_det] >>
  MATCH_ACCEPT_TAC sound_policyr_weaker
QED

Theorem safe_weakening_from_rel:
  init_safe init safe ∧
  safe_shield step safe shield ∧
  weaker p q ∧
  sound_policy step safe p ⇒
  ∀ctrl. invariant step init (enveloped p shield ctrl) safe ∧
         ∀s. enveloped q shield ctrl s = ctrl s ∧ q s (ctrl s) ⇒
             enveloped p shield ctrl s = ctrl s
Proof
  rewrite_tac[GSYM sound_policyr_det, GSYM safe_shieldr_det,
              GSYM invariantr_det] >>
  MATCH_ACCEPT_TAC safe_weakeningr
QED

Theorem gate_keeps_sound_from_rel:
  (cert ⇒ sound_policy step safe newp) ∧
  sound_policy step safe oldp ⇒
  sound_policy step safe (gate cert oldp newp)
Proof
  rewrite_tac[GSYM sound_policyr_det] >>
  MATCH_ACCEPT_TAC gate_keeps_soundr
QED

Theorem gate_preserves_safety_from_rel:
  (cert ⇒ sound_policy step safe newp) ∧
  init_safe init safe ∧
  safe_shield step safe shield ∧
  sound_policy step safe oldp ⇒
  ∀ctrl. invariant step init (enveloped (gate cert oldp newp) shield ctrl) safe
Proof
  rewrite_tac[GSYM sound_policyr_det, GSYM safe_shieldr_det,
              GSYM invariantr_det] >>
  MATCH_ACCEPT_TAC gate_preserves_safetyr
QED

Theorem certified_gate_correct_from_rel:
  (cert ⇒ admissible step safe oldp newp) ∧
  init_safe init safe ∧
  safe_shield step safe shield ∧
  sound_policy step safe oldp ⇒
  (∀ctrl. invariant step init (enveloped (gate cert oldp newp) shield ctrl)
                    safe) ∧
  weaker (gate cert oldp newp) oldp
Proof
  rewrite_tac[GSYM admissibler_det, GSYM sound_policyr_det,
              GSYM safe_shieldr_det, GSYM invariantr_det] >>
  MATCH_ACCEPT_TAC certified_gate_correctr
QED

Theorem certifier_gate_preserves_safety_from_rel:
  sound_certifier chk sem ∧
  (sem ob ⇒ admissible step safe oldp newp) ∧
  init_safe init safe ∧
  safe_shield step safe shield ∧
  sound_policy step safe oldp ⇒
  ∀ctrl. invariant step init
            (enveloped (gate (chk ob) oldp newp) shield ctrl) safe
Proof
  rewrite_tac[GSYM admissibler_det, GSYM sound_policyr_det,
              GSYM safe_shieldr_det, GSYM invariantr_det] >>
  MATCH_ACCEPT_TAC certifier_gate_preserves_safetyr
QED

(* Necessity witnesses, transported from the deterministic ones through
   `det`: without `weaker p q` authority is lost; one unsound "yes" breaches
   safety. (gate_preserves_safetyr / certified_gate_correctr need exactly
   these hypotheses.) *)
Theorem safe_weakeningr_needs_weaker:
  ∃(stepr:num -> num -> num -> bool) safe init shield p q ctrl s.
    init_safe init safe ∧
    safe_shieldr stepr safe shield ∧
    sound_policyr stepr safe p ∧
    sound_policyr stepr safe q ∧
    ¬weaker p q ∧
    enveloped q shield ctrl s = ctrl s ∧ q s (ctrl s) ∧
    enveloped p shield ctrl s ≠ ctrl s
Proof
  strip_assume_tac safe_weakening_needs_weaker >>
  qexistsl_tac [‘det step’, ‘safe’, ‘init’, ‘shield’, ‘p’, ‘q’, ‘ctrl’,
                ‘s’] >>
  simp[sound_policyr_det, safe_shieldr_det]
QED

Theorem unsound_certificate_breachesr:
  ∃(stepr:num -> num -> num -> bool) safe init shield oldp newp ctrl.
    init_safe init safe ∧
    safe_shieldr stepr safe shield ∧
    sound_policyr stepr safe oldp ∧
    ¬sound_policyr stepr safe newp ∧
    ¬invariantr stepr init (enveloped (gate T oldp newp) shield ctrl) safe
Proof
  strip_assume_tac unsound_certificate_breaches >>
  qexistsl_tac [‘det step’, ‘safe’, ‘init’, ‘shield’, ‘oldp’, ‘newp’,
                ‘ctrl’] >>
  simp[sound_policyr_det, safe_shieldr_det, invariantr_det]
QED

(* ------------------------------------------------------------------ *)
(*  (b) Disturbance: an adversary picks the disturbance each step.     *)
(* ------------------------------------------------------------------ *)

(* dstep s a d: the successor of s under action a and disturbance d;
   D: the admissible disturbances. *)
Definition disturbed_def:
  disturbed (dstep:'s -> 'a -> 'd -> 's) (D:'d -> bool) s a s' ⇔
    ∃d. D d ∧ s' = dstep s a d
End

(* The run of selector [sel] from x0 under the disturbance sequence ds.
   Against a deterministic memoryless selector, an adaptive adversary is
   no stronger than a sequence: the run is determined by x0 and ds, so
   every history-dependent strategy is replayed by the sequence it
   produces (reachr_disturbed_iff_drun makes this exact). *)
Definition drun_def:
  (drun dstep (sel:'s -> 'a) (ds:num -> 'd) x0 0 = x0) ∧
  (drun dstep sel ds x0 (SUC n) =
     dstep (drun dstep sel ds x0 n) (sel (drun dstep sel ds x0 n)) (ds n))
End

Definition robust_policy_def:
  robust_policy (dstep:'s -> 'a -> 'd -> 's) D safe pol ⇔
    ∀s a d. safe s ∧ pol s a ∧ D d ⇒ safe (dstep s a d)
End

Definition robust_shield_def:
  robust_shield (dstep:'s -> 'a -> 'd -> 's) D safe shield ⇔
    ∀s d. safe s ∧ D d ⇒ safe (dstep s (shield s) d)
End

Theorem robust_policy_iff:
  sound_policyr (disturbed dstep D) safe pol ⇔ robust_policy dstep D safe pol
Proof
  simp[sound_policyr_def, robust_policy_def, disturbed_def] >>
  metis_tac[]
QED

Theorem robust_shield_iff:
  safe_shieldr (disturbed dstep D) safe shield ⇔
  robust_shield dstep D safe shield
Proof
  simp[safe_shieldr_def, robust_shield_def, disturbed_def] >>
  metis_tac[]
QED

(* The disturbed plant is total iff some disturbance is admissible: with
   D empty every action is blocked (and every policy vacuously sound). *)
Theorem disturbed_total:
  total (disturbed dstep D) ⇔ ∃d. D d
Proof
  simp[total_def, enabled_def, disturbed_def]
QED

(* The deterministic plant is the trivially disturbed one. *)
Theorem det_is_disturbed:
  disturbed (λs a (d:'d). step s a) (λd. T) = det step
Proof
  simp[FUN_EQ_THM, disturbed_def, det_def]
QED

Theorem drun_agree:
  ∀n. (∀m. m < n ⇒ ds m = ds' m) ⇒
      drun dstep sel ds x0 n = drun dstep sel ds' x0 n
Proof
  Induct >> rw[drun_def] >>
  ‘drun dstep sel ds x0 n = drun dstep sel ds' x0 n ∧ ds n = ds' n’
    suffices_by simp[] >>
  metis_tac[DECIDE “∀m n. m < n ⇒ m < SUC n”, DECIDE “∀n. n < SUC n”]
QED

Theorem drun_reachr:
  ∀n. init x0 ∧ (∀m. m < n ⇒ D (ds m)) ⇒
      reachr (disturbed dstep D) init sel (drun dstep sel ds x0 n)
Proof
  Induct >> rw[drun_def]
  >- (irule reachr_init >> simp[])
  >> irule reachr_step >> qexists_tac ‘drun dstep sel ds x0 n’ >>
  simp[disturbed_def] >>
  metis_tac[DECIDE “∀m n. m < n ⇒ m < SUC n”, DECIDE “∀n. n < SUC n”]
QED

Theorem reachr_disturbed_imp_drun:
  ∀s. reachr (disturbed dstep D) init sel s ⇒
      ∃x0 ds n. init x0 ∧ (∀m. m < n ⇒ D (ds m)) ∧
                drun dstep sel ds x0 n = s
Proof
  ho_match_mp_tac reachr_ind >> rw[disturbed_def]
  >- (qexistsl_tac [‘s’, ‘ARB’, ‘0’] >> simp[drun_def])
  >> qexistsl_tac [‘x0’, ‘λm. if m = n then d else ds m’, ‘SUC n’] >>
  ‘drun dstep sel (λm. if m = n then d else ds m) x0 n =
   drun dstep sel ds x0 n’
    by (irule drun_agree >> simp[]) >>
  rw[drun_def] >> Cases_on ‘m = n’ >> simp[]
QED

(* The relational run of the disturbed plant IS the set of all runs under
   admissible disturbance sequences. *)
Theorem reachr_disturbed_iff_drun:
  reachr (disturbed dstep D) init sel s ⇔
  ∃x0 ds n. init x0 ∧ (∀m. m < n ⇒ D (ds m)) ∧ drun dstep sel ds x0 n = s
Proof
  metis_tac[reachr_disturbed_imp_drun, drun_reachr]
QED

(* THE ROBUST ENVELOPE: a robustly sound policy and a robustly safe shield
   keep every state of every run safe, for every controller and every
   admissible disturbance sequence. The instance of safety_preservationr at
   the disturbed plant. *)
Theorem robust_safety_preservation:
  init_safe init safe ∧
  robust_policy dstep D safe pol ∧
  robust_shield dstep D safe shield ⇒
  ∀ctrl. invariantr (disturbed dstep D) init (enveloped pol shield ctrl) safe
Proof
  rw[GSYM robust_policy_iff, GSYM robust_shield_iff] >>
  metis_tac[safety_preservationr]
QED

Theorem robust_envelope:
  init_safe init safe ∧
  robust_policy dstep D safe pol ∧
  robust_shield dstep D safe shield ⇒
  ∀ctrl ds x0 n.
    init x0 ∧ (∀m. m < n ⇒ D (ds m)) ⇒
    safe (drun dstep (enveloped pol shield ctrl) ds x0 n)
Proof
  rpt strip_tac >>
  ‘invariantr (disturbed dstep D) init (enveloped pol shield ctrl) safe’
    by metis_tac[robust_safety_preservation] >>
  fs[invariantr_def] >> first_x_assum irule >>
  irule drun_reachr >> simp[]
QED

(* Soundness against the nominal disturbance (0) is not enough: position
   s' = a + d, safe = s ≤ 1, disturbances d ≤ 1. The policy "a ≤ 1" is
   nominally sound; the adversary adds 1 and the run reaches 2. *)
Theorem nominal_soundness_insufficient:
  ∃(dstep:num -> num -> num -> num) D safe init pol shield ctrl ds.
    init_safe init safe ∧ init 0 ∧ D 0 ∧ (∀m. D (ds m)) ∧
    sound_policy (λs a. dstep s a 0) safe pol ∧
    robust_shield dstep D safe shield ∧
    ¬robust_policy dstep D safe pol ∧
    ¬safe (drun dstep (enveloped pol shield ctrl) ds 0 1)
Proof
  qexistsl_tac [‘λs a d. a + d’, ‘λd. d ≤ 1’, ‘λs. s ≤ 1’, ‘λs. s = 0’,
                ‘λs a. a ≤ 1’, ‘λs. 0’, ‘λs. 1’, ‘λm. 1’] >>
  rpt conj_tac
  >- simp[init_safe_def]
  >- simp[]
  >- simp[]
  >- simp[]
  >- simp[sound_policy_def]
  >- simp[robust_shield_def]
  >- (simp[robust_policy_def] >> qexistsl_tac [‘0’, ‘1’, ‘1’] >> simp[])
  >> rewrite_tac[arithmeticTheory.ONE, drun_def] >> simp[enveloped_def]
QED

val _ = export_theory ();
