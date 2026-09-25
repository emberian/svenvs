(*
  viabilityScript — the assumption hiding inside `safe_shield`, made explicit.

  `safe_shield step safe shield` asks for an action from every safe state
  that lands in a safe state. That is a real property of the WORLD, not of
  the envelope: it says `safe` is a CONTROLLED-INVARIANT set. When it fails
  -- some safe state is doomed, every action from it leaves `safe` -- no
  shield exists and every theorem that assumes one is vacuous.

  This file names that property and proves the standard facts about it:

   * `controlled_inv step V`   V can be kept forever by SOME choice of action.
   * `viable step safe`        the VIABILITY KERNEL: states from which safety
                               can be kept forever. It is controlled-invariant
                               (`viable_is_controlled_inv`), inside `safe`
                               (`viable_sub_safe`) and the greatest such set
                               (`viable_greatest`, both hypotheses needed:
                               `viable_greatest_tight`).
   * `shield_exists_iff_viable`  a safe shield exists iff every safe state is
                               viable (Hilbert choice builds the shield).
   * `safe_shield_iff_chooses_viable` / `safe_shield_iff_keeps_viable`
                               what a safe shield IS, in kernel terms.
   * `viable_kernel_shield`, `viability_kernel_envelope`
                               when `safe` is NOT fully viable, the kernel is
                               the right target: there is always a shield for
                               it, and an envelope sound w.r.t. the kernel keeps
                               `safe` from viable initial states.
   * `gate_certificate_iff`    with viability, a sound certificate is not just
                               sufficient for the operational gate but
                               NECESSARY: `cert ⇒ sound newp` holds iff the
                               gated envelope is safe for every init, shield,
                               sound old policy and controller.
                               `unsound_certificate_breaches_general` recovers
                               upgradeTheory's necessity witness as corollaries.
   * `gate_iff_needs_viability` the viability hypothesis cannot be dropped: a
                               doomed safe state kills every shield, the
                               right-hand side holds vacuously, and an unsound
                               certified policy slips through the "iff".

  Pure light HOL4 over the generic core.
*)
open HolKernel boolLib bossLib BasicProvers
     systemTheory envelopeTheory safetyTheory sv_weakeningTheory upgradeTheory;

val _ = new_theory "viability";

(* V is controlled-invariant: from every V-state some action stays in V. *)
Definition controlled_inv_def:
  controlled_inv (step:'s -> 'a -> 's) (V:'s -> bool) ⇔
    ∀s. V s ⇒ ∃a. V (step s a)
End

(* The viability kernel of [safe]: the union of all controlled-invariant
   subsets of [safe]. *)
Definition viable_def:
  viable (step:'s -> 'a -> 's) (safe:'s -> bool) s ⇔
    ∃V. V s ∧ (∀t. V t ⇒ safe t) ∧ controlled_inv step V
End

Theorem viable_is_controlled_inv:
  controlled_inv step (viable step safe)
Proof
  simp[controlled_inv_def] >> rw[viable_def] >>
  metis_tac[controlled_inv_def]
QED

Theorem viable_sub_safe:
  viable step safe s ⇒ safe s
Proof
  rw[viable_def] >> metis_tac[]
QED

Theorem viable_greatest:
  (∀t. V t ⇒ safe t) ∧ controlled_inv step V ⇒
  ∀s. V s ⇒ viable step safe s
Proof
  rw[viable_def] >> metis_tac[]
QED

(* Both hypotheses of viable_greatest are needed: (1) V may leave safe
   (the unsafe 1 is never viable); (2) V inside safe but not
   controlled-invariant: 0 is safe yet every action goes to the unsafe 1. *)
Theorem viable_greatest_tight:
  (∃(step:num -> num -> num) safe V s.
     controlled_inv step V ∧ V s ∧ ¬viable step safe s) ∧
  (∃(step:num -> num -> num) safe V s.
     (∀t. V t ⇒ safe t) ∧ V s ∧ ¬viable step safe s)
Proof
  conj_tac
  >- (qexistsl_tac [‘λs a. s’, ‘λs. s = 0’, ‘λs. T’, ‘1’] >>
      simp[controlled_inv_def] >> strip_tac >>
      drule viable_sub_safe >> simp[])
  >> qexistsl_tac [‘λs a. 1’, ‘λs. s = 0’, ‘λs. s = 0’, ‘0’] >>
  simp[viable_def, controlled_inv_def] >>
  metis_tac[numLib.DECIDE “(1:num) ≠ 0”]
QED

(* A safe shield is exactly a Skolem function for controlled invariance. *)
Theorem shield_exists_iff_controlled_inv:
  (∃shield. safe_shield step safe shield) ⇔ controlled_inv step safe
Proof
  eq_tac >> rw[safe_shield_def, controlled_inv_def]
  >- metis_tac[]
  >> qexists_tac ‘λs. @a. safe (step s a)’ >> rw[] >>
  SELECT_ELIM_TAC >> metis_tac[]
QED

Theorem controlled_inv_iff_viable:
  controlled_inv step safe ⇔ ∀s. safe s ⇒ viable step safe s
Proof
  eq_tac >> rpt strip_tac
  >- (irule viable_greatest >> qexists_tac ‘safe’ >> simp[])
  >> rw[controlled_inv_def] >>
  ‘viable step safe s’ by metis_tac[] >>
  metis_tac[viable_is_controlled_inv, controlled_inv_def, viable_sub_safe]
QED

(* THE HEADLINE: a safe shield exists iff every safe state is viable. *)
Theorem shield_exists_iff_viable:
  (∃shield. safe_shield step safe shield) ⇔
  (∀s. safe s ⇒ viable step safe s)
Proof
  metis_tac[shield_exists_iff_controlled_inv, controlled_inv_iff_viable]
QED

(* What a safe shield is: a selector that, from every safe state, lands in
   the viability kernel. *)
Theorem safe_shield_iff_chooses_viable:
  safe_shield step safe shield ⇔
  ∀s. safe s ⇒ viable step safe (step s (shield s))
Proof
  eq_tac >> rpt strip_tac
  >- (‘∀t. safe t ⇒ viable step safe t’
        by metis_tac[shield_exists_iff_viable] >>
      fs[safe_shield_def])
  >> rw[safe_shield_def] >> metis_tac[viable_sub_safe]
QED

(* Equivalently: safe is entirely viable, and the shield keeps viable
   states viable. *)
Theorem safe_shield_iff_keeps_viable:
  safe_shield step safe shield ⇔
  (∀s. safe s ⇒ viable step safe s) ∧
  (∀s. viable step safe s ⇒ viable step safe (step s (shield s)))
Proof
  eq_tac >> rpt strip_tac
  >- metis_tac[shield_exists_iff_viable]
  >- metis_tac[safe_shield_iff_chooses_viable, viable_sub_safe]
  >> rw[safe_shield_def] >> metis_tac[viable_sub_safe]
QED

(* When [safe] is not fully viable, the kernel is: there is ALWAYS a shield
   that keeps the kernel. *)
Theorem viable_kernel_shield:
  ∃shield. safe_shield step (viable step safe) shield
Proof
  simp[shield_exists_iff_controlled_inv, viable_is_controlled_inv]
QED

(* ... so an envelope whose policy is sound w.r.t. the kernel keeps [safe]
   from viable initial states, for every controller. *)
Theorem viability_kernel_envelope:
  (∀s. init s ⇒ viable step safe s) ∧
  sound_policy step (viable step safe) pol ⇒
  ∃shield. ∀ctrl. invariant step init (enveloped pol shield ctrl) safe
Proof
  strip_tac >>
  ‘∃sh. safe_shield step (viable step safe) sh’
    by MATCH_ACCEPT_TAC viable_kernel_shield >>
  qexists_tac ‘sh’ >> rpt strip_tac >>
  ‘invariant step init (enveloped pol sh ctrl) (viable step safe)’
    by (irule safety_preservation >> simp[init_safe_def]) >>
  fs[invariant_def] >> metis_tac[viable_sub_safe]
QED

(* Both hypotheses are needed. (1) A doomed initial state: 0 is safe but
   every action goes to the unsafe 1; the policy is vacuously sound for the
   (empty) kernel, yet no shield saves it. (2) An unsound policy that
   permits leaving a viable state: from viable 0 the controller picks 1. *)
Theorem viability_kernel_envelope_tight:
  (∃(step:num -> num -> num) safe init pol.
     sound_policy step (viable step safe) pol ∧
     ¬∃shield. ∀ctrl. invariant step init (enveloped pol shield ctrl) safe) ∧
  (∃(step:num -> num -> num) safe init pol.
     (∀s. init s ⇒ viable step safe s) ∧
     ¬∃shield. ∀ctrl. invariant step init (enveloped pol shield ctrl) safe)
Proof
  conj_tac
  >- (qexistsl_tac [‘λs a. 1’, ‘λs. s = 0’, ‘λs. s = 0’, ‘λs a. F’] >>
      simp[sound_policy_def, invariant_def] >> rpt strip_tac >>
      qexistsl_tac [‘ARB’, ‘1’] >> simp[] >>
      ‘reach (λs a. 1) (λs. s = 0) (enveloped (λs a. F) shield ARB) 0’
        by simp[Once reach_cases] >>
      drule reach_step >> simp[])
  >> qexistsl_tac [‘λs a. a’, ‘λs. s = 0’, ‘λs. s = 0’, ‘λs a. T’] >>
  conj_tac
  >- (rw[viable_def, controlled_inv_def] >>
      qexists_tac ‘λs. s = 0’ >> simp[])
  >> simp[invariant_def] >> rpt strip_tac >>
  qexistsl_tac [‘λs. 1’, ‘1’] >> simp[] >>
  ‘reach (λs a. a) (λs. s = 0) (enveloped (λs a. T) shield (λs. 1)) 0’
    by simp[Once reach_cases] >>
  drule reach_step >> simp[enveloped_def]
QED

(* ===================================================================== *)
(*  THE GATE, CHARACTERIZED.                                             *)
(*  upgradeTheory proves `cert ⇒ sound newp` SUFFICES for the gated      *)
(*  envelope to be safe. Under viability it is also NECESSARY: if the    *)
(*  gated envelope is safe for every init, shield, sound old policy and  *)
(*  controller, then the certificate was sound.                          *)
(* ===================================================================== *)

Theorem gate_certificate_iff:
  (∃shield0. safe_shield step safe shield0) ⇒
  ((cert ⇒ sound_policy step safe newp) ⇔
   ∀init shield oldp ctrl.
     init_safe init safe ∧ safe_shield step safe shield ∧
     sound_policy step safe oldp ⇒
     invariant step init (enveloped (gate cert oldp newp) shield ctrl) safe)
Proof
  strip_tac >> eq_tac
  >- (rpt strip_tac >> irule gate_preserves_safety >> simp[])
  >> rpt strip_tac >> simp[sound_policy_def] >> rpt strip_tac >>
  ‘invariant step (λt. t = s)
     (enveloped (gate cert (λx y. F) newp) shield0 (λx. a)) safe’
    by (first_x_assum irule >> gs[init_safe_def, sound_policy_def]) >>
  fs[invariant_def] >>
  ‘reach step (λt. t = s)
     (enveloped (gate cert (λx y. F) newp) shield0 (λx. a)) s’
    by simp[Once reach_cases] >>
  drule reach_step >> strip_tac >> first_x_assum drule >>
  gs[enveloped_def, gate_def]
QED

(* Corollary: in EVERY viable system, one unsound certified policy can be
   made to breach safety by a sound old policy, a safe shield and safe
   initial states. *)
Theorem unsound_certificate_breaches_general:
  safe_shield step safe shield0 ∧ ¬sound_policy step safe newp ⇒
  ∃init shield oldp ctrl.
    init_safe init safe ∧ safe_shield step safe shield ∧
    sound_policy step safe oldp ∧
    ¬invariant step init (enveloped (gate T oldp newp) shield ctrl) safe
Proof
  strip_tac >>
  ‘(T ⇒ sound_policy step safe newp) ⇔
   ∀init shield oldp ctrl.
     init_safe init safe ∧ safe_shield step safe shield ∧
     sound_policy step safe oldp ⇒
     invariant step init (enveloped (gate T oldp newp) shield ctrl) safe’
    by (irule gate_certificate_iff >> metis_tac[]) >>
  gs[] >> metis_tac[]
QED

(* NECESSITY of viability for the iff: 0 is safe but doomed (every action
   goes to the unsafe 1). No safe shield exists, so the right-hand side
   holds vacuously, while the certified newp is unsound. *)
Theorem gate_iff_needs_viability:
  ∃(step:num -> num -> num) safe newp s.
    safe s ∧ ¬viable step safe s ∧
    ¬(∃shield. safe_shield step safe shield) ∧
    ¬((T ⇒ sound_policy step safe newp) ⇔
      ∀init shield oldp ctrl.
        init_safe init safe ∧ safe_shield step safe shield ∧
        sound_policy step safe oldp ⇒
        invariant step init (enveloped (gate T oldp newp) shield ctrl) safe)
Proof
  qexistsl_tac [‘λs a. 1’, ‘λs. s = 0’, ‘λs a. T’, ‘0’] >>
  rpt conj_tac >>
  simp[viable_def, safe_shield_def, sound_policy_def, controlled_inv_def] >>
  metis_tac[numLib.DECIDE “(1:num) ≠ 0”]
QED

val _ = export_theory ();
