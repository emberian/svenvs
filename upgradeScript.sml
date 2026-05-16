(*
  Proof-carrying self-improvement.

  A running enveloped system may *propose to change its own policy* (loosen
  its envelope to gain autonomy). A proposal is admitted ONLY if it
  discharges a proof obligation:

      admissible step safe oldp newp ⇔
        sound_policy step safe newp ∧ weaker newp oldp

  i.e. the new policy must (1) still be safety-sound and (2) be a genuine
  weakening (≥ as permissive) of the current one. `admit` installs the new
  policy iff the obligation holds, and otherwise keeps the old one — an
  unproven proposal can never degrade safety.

  The point of this file: prove the *gate itself is sound*, and that this
  holds under an UNBOUNDED sequence of self-proposed upgrades. The proposer
  (a computationally irreducible agent) must pay for every increase in authority with
  a checkable proof; the kernel guarantees safety is never lost.

  This is the HOL-level layer. The "typed-in program" that denotes [newp]
  is reflected in cartpoleProgramScript; the same obligation lifts to
  CakeML-level evaluation via the candle/prover chain later.
*)
open HolKernel boolLib bossLib BasicProvers listTheory
     systemTheory envelopeTheory safetyTheory sv_weakeningTheory;

val _ = new_theory "upgrade";

(* The proof obligation a self-proposed policy must discharge. *)
Definition admissible_def:
  admissible step safe oldp newp ⇔
    sound_policy step safe newp ∧ weaker newp oldp
End

(* The gate: install [newp] iff it discharged the obligation. *)
Definition admit_def:
  admit step safe oldp newp =
    if admissible step safe oldp newp then newp else oldp
End

(* The gate never produces an unsound policy from a sound one. *)
Theorem admit_keeps_sound:
  sound_policy step safe oldp ⇒
  sound_policy step safe (admit step safe oldp newp)
Proof
  rw[admit_def, admissible_def]
QED

(* Gate soundness: after a self-proposed upgrade, the enveloped system is
   still safe for EVERY controller — whether or not the proposal was
   accepted. *)
Theorem admit_preserves_safety:
  init_safe init safe ∧
  safe_shield step safe shield ∧
  sound_policy step safe oldp ⇒
  ∀ctrl. invariant step init
            (enveloped (admit step safe oldp newp) shield ctrl) safe
Proof
  rpt strip_tac >>
  irule safety_preservation >>
  metis_tac[admit_keeps_sound]
QED

(* Iterated self-improvement: fold a whole stream of proposals through the
   gate. Each is independently obligation-checked; soundness is invariant. *)
Definition admit_all_def:
  admit_all step safe p0 proposals = FOLDL (admit step safe) p0 proposals
End

Theorem admit_all_keeps_sound:
  ∀proposals p0.
    sound_policy step safe p0 ⇒
    sound_policy step safe (admit_all step safe p0 proposals)
Proof
  Induct >> rw[admit_all_def] >>
  fs[GSYM admit_all_def] >>
  first_x_assum irule >>
  metis_tac[admit_keeps_sound]
QED

(* The headline self-improvement theorem: NO finite sequence of
   self-proposed envelope weakenings — adversarial or not — can ever make
   the enveloped system unsafe, for any controller. Authority is earned by
   proof; safety is unconditional. *)
Theorem self_improvement_is_safe:
  init_safe init safe ∧
  safe_shield step safe shield ∧
  sound_policy step safe p0 ⇒
  ∀proposals ctrl.
    invariant step init
      (enveloped (admit_all step safe p0 proposals) shield ctrl) safe
Proof
  rpt strip_tac >>
  irule safety_preservation >>
  metis_tac[admit_all_keeps_sound]
QED

val _ = export_theory ();
