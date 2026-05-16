(*
  Subsumption: the existing policy envelope is an INSTANCE of the
  proof-carrying envelope.

  A sound policy `pol` induces a certifier in which "the policy decision is
  the certificate schema": the certificate type is unit, and the certifier
  accepts (s,a,()) exactly when `pol s a` holds. We then prove, by pure
  rewriting, that the proof-carrying envelope under that induced certifier
  is *definitionally* the old `enveloped pol shield ctrl`, and that the old
  controller-agnostic guarantee `safetyTheory.safety_preservation` is
  recovered as a corollary of `pcaTheory.pca_safety_preservation` — the
  generic core (safetyTheory / upgradeTheory) is REUSED, not re-proved.
*)
open HolKernel boolLib bossLib BasicProvers
     systemTheory envelopeTheory safetyTheory upgradeTheory
     pcaTheory;

val _ = new_theory "pcaSubsumption";

(* The certifier induced by a policy: certificate is trivial (unit); the
   policy decision IS the certificate. *)
Definition pol_certifier_def:
  pol_certifier (pol:'s -> 'a -> bool) (s:'s) (a:'a) (c:unit) ⇔ pol s a
End

(* Lift a bare selector to a proof-carrying controller that always attaches
   the trivial certificate. *)
Definition lift_ctrl_def:
  lift_ctrl (ctrl:'s -> 'a) (s:'s) = (ctrl s, ()):('a # unit)
End

(* (1) A sound policy induces a SOUND certifier — discharging the one
   explicit side-condition of the proof-carrying layer directly from the
   existing `sound_policy` predicate. *)
Theorem pol_certifier_sound:
  sound_policy step safe pol ⇒
  certifier_sound step safe (pol_certifier pol)
Proof
  rw[certifier_sound_def, pol_certifier_def] >>
  fs[sound_policy_def] >> metis_tac[]
QED

(* (2) DEFINITIONAL SUBSUMPTION: the proof-carrying envelope under the
   induced certifier and lifted controller IS the old envelope. *)
Theorem pca_enveloped_subsumes_enveloped:
  pca_enveloped (pol_certifier pol) shield (lift_ctrl ctrl) =
  enveloped pol shield ctrl
Proof
  rw[FUN_EQ_THM, pca_enveloped_def, enveloped_def,
     pol_certifier_def, lift_ctrl_def]
QED

(* (3) The OLD headline recovered as a corollary of the NEW one. The body
   reduces the proof-carrying guarantee through (1)+(2) to exactly
   `safety_preservation`'s statement — same premises, same conclusion. *)
Theorem enveloped_safety_via_pca:
  init_safe init safe ∧
  sound_policy step safe pol ∧
  safe_shield step safe shield ⇒
  ∀ctrl. invariant step init (enveloped pol shield ctrl) safe
Proof
  rpt strip_tac >>
  ‘invariant step init
     (pca_enveloped (pol_certifier pol) shield (lift_ctrl ctrl)) safe’
    by metis_tac[pca_safety_preservation, pol_certifier_sound] >>
  fs[pca_enveloped_subsumes_enveloped]
QED

(* (4) Cross-check: that corollary is literally the existing core theorem
   `safetyTheory.safety_preservation` — same type, same statement. We cite
   and reuse the core; this confirms genuine reduction (no divergence). *)
Theorem subsumption_matches_core:
  (init_safe init safe ∧
   sound_policy step safe pol ∧
   safe_shield step safe shield ⇒
   ∀ctrl. invariant step init (enveloped pol shield ctrl) safe)
Proof
  metis_tac[safety_preservation]
QED

(* (5) Subsumption composes with the existing self-improvement core: an
   UNBOUNDED stream of admitted policy weakenings, viewed through the
   induced certifier, still keeps safety for every controller. Reuses
   upgradeTheory.self_improvement_is_safe verbatim — nothing re-proved. *)
Theorem pca_self_improvement_via_core:
  init_safe init safe ∧
  safe_shield step safe shield ∧
  sound_policy step safe p0 ⇒
  ∀proposals ctrl.
    invariant step init
      (pca_enveloped (pol_certifier (admit_all step safe p0 proposals))
                     shield (lift_ctrl ctrl)) safe
Proof
  rpt strip_tac >>
  ‘invariant step init
     (enveloped (admit_all step safe p0 proposals) shield ctrl) safe’
    by metis_tac[self_improvement_is_safe] >>
  fs[pca_enveloped_subsumes_enveloped]
QED

val _ = export_theory ();
