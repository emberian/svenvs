(*
  The real (deeply-embedded) admission gate.

  The shallow `cartpoleProgramScript` checked obligations with HOL4's own
  metis. Here the obligation is a term of Candle's *deeply-embedded* HOL
  (`holSyntax`), and it is discharged by Candle's *verified inference
  system* `|-` (`proves`). Soundness of that kernel —
  `holSoundnessTheory.proves_sound : is_set_theory mem ⇒ thyh |- c ⇒ thyh |= c`
  — is what makes a kernel-checked obligation trustworthy.

  We prove: a self-improvement upgrade whose obligation term is *derived by
  the Candle kernel* (and which faithfully encodes the meta obligation)
  provably preserves safety for every controller. The faithful-encoding
  predicate `encodes_obligation` is the single explicit seam that the
  hol-reflection proof-producing translator discharges automatically
  (`term_to_deep`/`termsem_cert`); everything else here is proved outright
  from the built Candle soundness theorem.
*)
open HolKernel boolLib bossLib BasicProvers
     holSyntaxTheory holSemanticsTheory holSoundnessTheory
     systemTheory envelopeTheory safetyTheory sv_weakeningTheory upgradeTheory;

val _ = new_theory "embeddedGate";

val _ = Parse.hide "mem";
val mem = ``mem:'U->'U->bool``;

(* The Candle kernel has derived the (closed) obligation term [obl] in
   theory [thy]. `|-` here is `proves`, the verified inference system. *)
Definition kernel_admits_def:
  kernel_admits ^mem thy obl ⇔ is_set_theory mem ∧ (thy,[]) |- obl
End

(* The seam: [obl]'s semantic content is exactly the meta-level
   admissibility obligation. hol-reflection's term_to_deep/termsem_cert
   produce precisely a theorem of this shape for the reflected obligation;
   we keep it abstract so the gate's soundness does not depend on the
   reflection automation (which is being ported in parallel). *)
Definition encodes_obligation_def:
  encodes_obligation ^mem thy obl step safe oldp newp ⇔
    ((thy,[]) |= obl ⇒ admissible step safe oldp newp)
End

(* Candle's verified kernel really does only certify semantic truths. *)
Theorem kernel_admits_is_sound:
  kernel_admits ^mem thy obl ⇒ (thy,[]) |= obl
Proof
  rw[kernel_admits_def] >> metis_tac[proves_sound]
QED

(* THE THEOREM: if the Candle kernel discharged a faithfully-encoded
   self-improvement obligation, the enveloped system stays safe for ANY
   controller — the admission gate is sound *because the verified prover
   checked it*. *)
Theorem embedded_admit_preserves_safety:
  init_safe init safe ∧
  safe_shield step safe shield ∧
  sound_policy step safe oldp ∧
  kernel_admits ^mem thy obl ∧
  encodes_obligation ^mem thy obl step safe oldp newp ⇒
  ∀ctrl. invariant step init
            (enveloped (admit step safe oldp newp) shield ctrl) safe
Proof
  rpt strip_tac >>
  irule admit_preserves_safety >>
  fs[]
QED

(* And when the obligation IS discharged, the upgrade is actually installed
   (authority genuinely granted), not silently rejected. *)
Theorem embedded_admit_installs:
  kernel_admits ^mem thy obl ∧
  encodes_obligation ^mem thy obl step safe oldp newp ⇒
  admit step safe oldp newp = newp
Proof
  rw[] >>
  ‘admissible step safe oldp newp’
    by metis_tac[kernel_admits_is_sound, encodes_obligation_def] >>
  rw[admit_def]
QED

val _ = export_theory ();
