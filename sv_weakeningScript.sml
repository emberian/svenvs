(*
  Policy weakening.

  [weaker p q] means p is at least as permissive as q (q's allowed actions
  are a subset of p's). Weakening the envelope = moving to a [weaker] policy.

  Results:
    1. soundness transfers downward along [weaker] (a sound permissive policy
       has sound restrictions);
    2. controller authority is monotone: any action the controller is allowed
       under the stricter policy it is still allowed under the weaker one
       (the envelope overrides no more often after weakening);
    3. SAFE WEAKENING: you may replace a policy by any weaker policy that is
       still safety-sound and retain the full safety-preservation guarantee
       for an arbitrary controller, while the controller loses no authority
       it had — i.e. the system can loosen its own envelope without losing
       safety. This is the self-improvement hook. The weakening premise is
       necessary for the authority half (safe_weakening_needs_weaker).
*)
open HolKernel boolLib bossLib BasicProvers
     systemTheory envelopeTheory safetyTheory;

val _ = new_theory "sv_weakening";

(* p is weaker (more permissive) than q. *)
Definition weaker_def:
  weaker (p:('s,'a)policy) (q:('s,'a)policy) ⇔
    ∀s a. q s a ⇒ p s a
End

Theorem weaker_refl:
  weaker p p
Proof
  rw[weaker_def]
QED

Theorem weaker_trans:
  weaker p q ∧ weaker q r ⇒ weaker p r
Proof
  rw[weaker_def] >> metis_tac[]
QED

(* 1. Soundness transfers from a permissive policy down to any restriction. *)
Theorem sound_policy_weaker:
  weaker p q ∧ sound_policy step safe p ⇒ sound_policy step safe q
Proof
  rw[weaker_def, sound_policy_def] >> metis_tac[]
QED

(* 2. Controller authority is monotone under weakening. *)
Theorem authority_monotone:
  weaker p q ⇒
  ∀s. (enveloped q shield ctrl s = ctrl s ∧ q s (ctrl s)) ⇒
      (enveloped p shield ctrl s = ctrl s)
Proof
  rw[weaker_def, enveloped_def] >> metis_tac[]
QED

(* 3. Safe weakening: replacing q by a weaker p that is still sound keeps
      the full safety-preservation guarantee for an arbitrary controller
      AND never takes authority away: wherever the controller acted freely
      under q, it still acts freely under p. Soundness of p carries the
      first conjunct; `weaker p q` carries the second
      (safe_weakening_needs_weaker shows it cannot be dropped). *)
Theorem safe_weakening:
  init_safe init safe ∧
  safe_shield step safe shield ∧
  weaker p q ∧
  sound_policy step safe p ⇒
  ∀ctrl. invariant step init (enveloped p shield ctrl) safe ∧
         ∀s. enveloped q shield ctrl s = ctrl s ∧ q s (ctrl s) ⇒
             enveloped p shield ctrl s = ctrl s
Proof
  rpt strip_tac
  >- (irule safety_preservation >> fs[])
  >- metis_tac[authority_monotone]
QED

(* NECESSITY of `weaker p q`: two sound policies, a safe shield, and a
   state where the controller acted freely under q but is overridden
   under p. Without the weakening premise the authority conjunct fails. *)
Theorem safe_weakening_needs_weaker:
  ∃(step:num -> num -> num) safe init shield p q ctrl s.
    init_safe init safe ∧
    safe_shield step safe shield ∧
    sound_policy step safe p ∧
    sound_policy step safe q ∧
    ¬weaker p q ∧
    enveloped q shield ctrl s = ctrl s ∧ q s (ctrl s) ∧
    enveloped p shield ctrl s ≠ ctrl s
Proof
  qexistsl_tac [‘λs a. s’, ‘λs. T’, ‘λs. T’, ‘λs. 0’, ‘λs a. F’,
                ‘λs a. T’, ‘λs. 1’, ‘0’] >>
  rw[init_safe_def, safe_shield_def, sound_policy_def, weaker_def,
     enveloped_def]
QED

val _ = export_theory ();
