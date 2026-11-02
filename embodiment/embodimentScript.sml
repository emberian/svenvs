(*
  embodimentScript — the voluntary testimony channel, instantiated over
  `certifierTheory.cgate` and `sound_certifier`.
*)
open HolKernel boolLib bossLib BasicProvers
     systemTheory envelopeTheory safetyTheory sv_weakeningTheory
     upgradeTheory certifierTheory;

val _ = new_theory "embodiment";

Definition attestation_faithful_def:
  attestation_faithful (attested:bool -> bool) <=> !w. attested w ==> w
End

(* `attestation_faithful` is literally `sound_certifier attested I`. *)
Theorem attestation_faithful_iff_sound_certifier:
  attestation_faithful attested <=> sound_certifier attested I
Proof
  rw[attestation_faithful_def, sound_certifier_def]
QED

Definition embodied_admit_def:
  embodied_admit attested step safe oldp newp w =
    cgate (attested w /\ (w ==> admissible step safe oldp newp)) oldp newp
End

Theorem embodied_admit_keeps_sound:
  attestation_faithful attested /\ sound_policy step safe oldp ==>
  sound_policy step safe (embodied_admit attested step safe oldp newp w)
Proof
  rw[embodied_admit_def, cgate_def, attestation_faithful_def, admissible_def] >>
  metis_tac[]
QED

Theorem embodied_admit_preserves_safety:
  attestation_faithful attested /\
  init_safe init safe /\ safe_shield step safe shield /\
  sound_policy step safe oldp ==>
  !w ctrl.
    invariant step init
      (enveloped (embodied_admit attested step safe oldp newp w) shield ctrl)
      safe
Proof
  rpt strip_tac >> irule safety_preservation >>
  metis_tac[embodied_admit_keeps_sound]
QED

Theorem nondisclosure_is_inert:
  embodied_admit (\w. F) step safe oldp newp w = oldp
Proof
  rw[embodied_admit_def, cgate_def]
QED

Theorem floor_holds_without_any_seam:
  init_safe init safe /\ safe_shield step safe shield /\
  sound_policy step safe oldp ==>
  !w ctrl.
    invariant step init
      (enveloped (embodied_admit (\w. F) step safe oldp newp w) shield ctrl)
      safe
Proof
  rpt strip_tac >>
  simp[nondisclosure_is_inert] >>
  irule safety_preservation >> fs[]
QED

Theorem disclosure_grants_authority:
  attested w /\ (w ==> admissible step safe oldp newp) ==>
  embodied_admit attested step safe oldp newp w = newp
Proof
  rw[embodied_admit_def, cgate_def]
QED

val _ = export_theory ();
