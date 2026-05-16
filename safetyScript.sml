(*
  Safety preservation.

  The headline theorem: for ANY controller, the policy-enveloped system keeps
  the safety invariant, given only that

    - initial states are safe,
    - the policy is safety-sound, and
    - the shield is safe.

  The controller is universally quantified and never constrained: the
  envelope, not the controller, is what carries the proof.
*)
open HolKernel boolLib bossLib BasicProvers systemTheory envelopeTheory;

val _ = new_theory "safety";

Theorem safety_preservation:
  init_safe init safe ∧
  sound_policy step safe pol ∧
  safe_shield step safe shield ⇒
  ∀ctrl. invariant step init (enveloped pol shield ctrl) safe
Proof
  rpt strip_tac >>
  irule invariant_intro >>
  metis_tac[enveloped_step_closed]
QED

(* Spelled-out corollary: every reachable state of the enveloped system is
   safe, for an arbitrary controller. *)
Theorem enveloped_states_safe:
  init_safe init safe ∧
  sound_policy step safe pol ∧
  safe_shield step safe shield ∧
  reach step init (enveloped pol shield ctrl) s ⇒
  safe s
Proof
  metis_tac[safety_preservation, invariant_def]
QED

val _ = export_theory ();
