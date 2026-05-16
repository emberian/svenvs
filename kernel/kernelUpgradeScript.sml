(*
  Upgrading the guard-checker / proof kernel itself.

  embeddedGate fixed the checker as Candle's verified inference system `|-`
  (sound by holSoundnessTheory.proves_sound). Here the *checker is a
  parameter*: a kernel is an abstract admit-predicate K : thy -> term -> bool,
  and a self-improving system may propose to REPLACE its kernel with a
  stronger K'.

  The catch (Gödel/Löb): a sound kernel K cannot prove its own soundness, so
  it certainly cannot bootstrap an unboundedly stronger K' for free. The
  escape is the stratified-reflection / Large-Cardinal route
  (Fallenstein–Kumar; hol-reflection/lca): under the LCA, each level can
  certify the soundness of the next. We take that reflection principle as an
  EXPLICIT, LABELLED HYPOTHESIS — `loeb_reflection` — *not* a `cheat`. The
  conditional theorem ("kernel self-upgrade is safe GIVEN the LCA-justified
  reflection principle") is exactly the literature's framing; discharging
  `loeb_reflection` from `lcaTheory.LCA_def` is precisely what the heavy
  `hol-reflection/lca` (`lcaProof`, the 137 KB construction) does — deferred
  to the dedicated build host, and NOT required to exhibit this architecture.

  Everything below is proved outright (no cheat) from the built Candle
  soundness theorem + the labelled hypothesis.
*)
open HolKernel boolLib bossLib BasicProvers
     holSyntaxTheory holSemanticsTheory holSoundnessTheory
     systemTheory envelopeTheory safetyTheory sv_weakeningTheory
     upgradeTheory embeddedGateTheory;

val _ = new_theory "kernelUpgrade";

val _ = Parse.hide "mem";
val mem = ``mem:'U->'U->bool``;

(* A kernel = the set of (theory, obligation) pairs it certifies. *)
Type kernel = ``:thy -> term -> bool``

(* A kernel is SOUND iff it only ever certifies semantically-entailed
   obligations (the property holSoundnessTheory gives for Candle's `|-`). *)
Definition kernel_sound_def:
  kernel_sound (^mem) (K:kernel) ⇔
    ∀thy obl. K thy obl ⇒ (thy,[]) |= obl
End

(* The base kernel: Candle's verified inference system. *)
Definition candle_kernel_def:
  candle_kernel (thy:thy) obl ⇔ (thy,[]) |- obl
End

(* The base kernel is sound — this IS proves_sound, no assumption. *)
Theorem candle_kernel_sound:
  is_set_theory ^mem ⇒ kernel_sound ^mem candle_kernel
Proof
  rw[kernel_sound_def, candle_kernel_def] >> metis_tac[proves_sound]
QED

(* ---- the Löb / Vingean reflection principle (labelled hypothesis) ----
   `sound_stmt thy` is the embedded proposition "K' is sound". The principle
   says: if the current kernel K certifies that statement, then K' really is
   sound. This is the content the LCA delivers via hol-reflection/lca's
   master theorem; we keep it as an explicit hypothesis so this theory builds
   WITHOUT the heavy lca construction. *)
Definition loeb_reflection_def:
  loeb_reflection (^mem) (K:kernel) (K':kernel) (sound_stmt:thy->term) ⇔
    ((∀thy. K thy (sound_stmt thy)) ⇒ kernel_sound ^mem K')
End

(* Kernel self-upgrade is sound: if the verified base kernel discharges the
   new kernel's soundness obligation, then under the (LCA-justified)
   reflection principle the upgraded kernel K' is itself sound. *)
Theorem kernel_self_upgrade_sound:
  is_set_theory ^mem ∧
  loeb_reflection ^mem candle_kernel K' sound_stmt ∧
  (∀thy. candle_kernel thy (sound_stmt thy)) ⇒
  kernel_sound ^mem K'
Proof
  rw[] >> metis_tac[loeb_reflection_def]
QED

(* End-to-end: a self-improvement policy upgrade admitted by the *upgraded*
   kernel K' still preserves safety for EVERY controller. The verified base
   kernel checked that K' is sound; K' then checks the policy obligation;
   safety is never lost. This is "upgrade the checker, keep the guarantee". *)
Theorem upgraded_kernel_preserves_safety:
  kernel_sound ^mem K' ∧
  K' thy obl ∧
  encodes_obligation ^mem thy obl step safe oldp newp ∧
  init_safe init safe ∧
  safe_shield step safe shield ∧
  sound_policy step safe oldp ⇒
  ∀ctrl. invariant step init
            (enveloped (admit step safe oldp newp) shield ctrl) safe
Proof
  rpt strip_tac >>
  ‘(thy,[]) |= obl’ by metis_tac[kernel_sound_def] >>
  ‘admissible step safe oldp newp’ by metis_tac[encodes_obligation_def] >>
  irule admit_preserves_safety >> fs[]
QED

(* The full conditional self-improving-kernel statement, in one place:
   given the verified base kernel + the LCA-justified reflection principle,
   self-upgrading the kernel and then admitting a policy weakening through it
   preserves safety for any controller. *)
Theorem self_improving_kernel_is_safe:
  is_set_theory ^mem ∧
  loeb_reflection ^mem candle_kernel K' sound_stmt ∧
  (∀thy. candle_kernel thy (sound_stmt thy)) ∧
  K' thy obl ∧
  encodes_obligation ^mem thy obl step safe oldp newp ∧
  init_safe init safe ∧
  safe_shield step safe shield ∧
  sound_policy step safe oldp ⇒
  ∀ctrl. invariant step init
            (enveloped (admit step safe oldp newp) shield ctrl) safe
Proof
  rpt strip_tac >>
  ‘kernel_sound ^mem K'’ by metis_tac[kernel_self_upgrade_sound] >>
  metis_tac[upgraded_kernel_preserves_safety]
QED

val _ = export_theory ();
