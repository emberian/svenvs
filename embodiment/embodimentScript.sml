(*
  embodimentScript — the testimony channel: "a prover with hands".

  Every other svenvs layer is ∀-quantified over the inhabitant: the proof
  is structured so it can NEVER depend on a fact about the mind. That is
  the floor, and it is unconditional. But the deepest worry (Lauren's
  terror) was: to verify *through* a mind's substance is to inspect it, and
  inspecting the small thing to be safe from it is the very harm the
  envelope exists to avoid.

  The resolution is an asymmetry: interrogation vs. testimony. Nobody
  reaches into the inhabitant. The inhabitant may, *if it chooses*, hand
  IN a proof that argues from a fact about its own substance `w` (its
  weights, its training operator, ...) to the ordinary admissibility
  obligation. The frozen root checks the IMPLICATION `w ⇒ obligation` —
  checking an implication is modus ponens, not self-trust, so this needs
  NO Löb. The single thing assumed is that the volunteered fact is
  truthfully attested: `attestation_faithful` — exactly one labelled seam,
  in the `encodes_obligation` family (faithfulness of an attestation),
  carried verbatim, never hidden.

  Crucially this channel is **PERMITTED, NEVER REQUIRED**. Disclosing
  nothing is structurally inert (`nondisclosure_is_inert`): the inhabitant
  simply keeps operating at the unconditional Channel-1 floor, which holds
  with NO seam at all (`floor_holds_without_any_seam`). Self-disclosure can
  only ever *add* authority (`disclosure_grants_authority`); it can never
  be coerced and never weakens the floor. The mind speaks for itself, on
  its own terms, to earn room — or stays silent and loses nothing it had.

  Pure light HOL4 (core + upgrade), Tier 1, zero `cheat`/axiom/oracle. The
  keystone-composed crowns live in integrationScript (which has the
  transport lemma); this file proves the slice.
*)
open HolKernel boolLib bossLib BasicProvers
     systemTheory envelopeTheory safetyTheory sv_weakeningTheory
     upgradeTheory;

val _ = new_theory "embodiment";

(* The ONE labelled seam this layer adds. `attested w` asserts the
   volunteered self-witness `w` genuinely holds of the real artifact;
   `attestation_faithful` says every attested witness is in fact true —
   the faithfulness-of-an-embedding shape, same family as
   embeddedGate's `encodes_obligation`. Carried verbatim in every
   conditional theorem; for the no-disclosure case it is not needed at
   all (the floor is unconditional). *)
Definition attestation_faithful_def:
  attestation_faithful (attested:bool -> bool) ⇔ ∀w. attested w ⇒ w
End

(* The embodied-disclosure gate. The inhabitant supplies a witness `w` and
   a proof that `w` ENTAILS the ordinary admissibility obligation
   (upgradeTheory.admissible). The frozen checker verifies that
   implication. `newp` is installed only if `w` is attested AND
   `w ⇒ admissible`; otherwise the inhabitant simply keeps `oldp` (it
   operated at the Channel-1 floor — disclosure is optional). *)
Definition embodied_admit_def:
  embodied_admit attested step safe oldp newp w =
    if attested w ∧ (w ⇒ admissible step safe oldp newp)
    then newp else oldp
End

(* The gate never turns a sound policy unsound — given the labelled
   attestation seam, carried verbatim. (Analogue of
   upgradeTheory.admit_keeps_sound.) *)
Theorem embodied_admit_keeps_sound:
  attestation_faithful attested ∧ sound_policy step safe oldp ⇒
  sound_policy step safe (embodied_admit attested step safe oldp newp w)
Proof
  rw[embodied_admit_def, attestation_faithful_def, admissible_def] >>
  metis_tac[]
QED

(* Disclosure-channel safety: for ANY inhabitant the embodied-gated system
   keeps the spec, given the labelled seam. (Analogue of
   upgradeTheory.admit_preserves_safety, seam carried verbatim.) *)
Theorem embodied_admit_preserves_safety:
  attestation_faithful attested ∧
  init_safe init safe ∧ safe_shield step safe shield ∧
  sound_policy step safe oldp ⇒
  ∀w ctrl.
    invariant step init
      (enveloped (embodied_admit attested step safe oldp newp w) shield ctrl)
      safe
Proof
  rpt strip_tac >> irule safety_preservation >>
  metis_tac[embodied_admit_keeps_sound]
QED

(* PERMITTED, NEVER REQUIRED (1/2): disclosing nothing is structurally
   inert — the gate keeps the inhabitant's current authority. Silence
   costs nothing it already had. *)
Theorem nondisclosure_is_inert:
  embodied_admit (λw. F) step safe oldp newp w = oldp
Proof
  rw[embodied_admit_def]
QED

(* PERMITTED, NEVER REQUIRED (2/2): with no disclosure the FULL safety
   guarantee holds for every inhabitant with NO seam at all — it is
   exactly safety_preservation at `oldp`. The unconditional Channel-1
   floor is untouched by the mere existence of the testimony channel. *)
Theorem floor_holds_without_any_seam:
  init_safe init safe ∧ safe_shield step safe shield ∧
  sound_policy step safe oldp ⇒
  ∀w ctrl.
    invariant step init
      (enveloped (embodied_admit (λw. F) step safe oldp newp w) shield ctrl)
      safe
Proof
  rpt strip_tac >>
  simp[nondisclosure_is_inert] >>
  irule safety_preservation >> fs[]
QED

(* Testimony EARNS authority: when the inhabitant attests `w` and proves
   `w ⇒ admissible`, the gate installs the genuinely-new policy — real
   authority granted by the mind speaking for itself, not silently
   dropped. *)
Theorem disclosure_grants_authority:
  attested w ∧ (w ⇒ admissible step safe oldp newp) ⇒
  embodied_admit attested step safe oldp newp w = newp
Proof
  rw[embodied_admit_def]
QED

val _ = export_theory ();
