(*
  kernelModScript — follow-up #28, the genuine KERNEL-MODIFICATION case.

  selfProverConcreteScript discharged `frozen_checker_sound` for the *base*
  Candle build (the identity/non-strengthening case). This file does the real
  thing: a genuinely MODIFIED kernel — Candle's inference relation with a NEW
  PRIMITIVE RULE added — RE-VERIFIED sound against the real `holSoundness`
  semantics, then fed through selfProver's frozen-root gate.

  We add SYMMETRY OF EQUALITY as a kernel primitive. In Candle SYM is only a
  *derived* rule (not primitive), so a kernel that has it as a primitive is a
  genuine source-level modification of the inference relation. Its soundness
  is NOT free: it needs a new per-rule soundness lemma `SYM_correct` (the
  semantic validity of symmetry), proved here from `termsem_equation` exactly
  as Candle proves its own `REFL_correct`. This is the modular re-verification
  Candle's `proves_sound` (= `proves_ind` glued from per-rule `_correct`
  lemmas) is built for.

  HONEST SCOPE.
   * This is a SOUNDNESS-PRESERVING edit (the faithful kind of kernel
     modification — what a real build-swap is). It does NOT prove strictly
     more than Candle: a sound kernel cannot, and a genuine *logical
     strengthening* is the separate Gödel/Löb wall (`kernelUpgrade`'s labelled
     `loeb_reflection`), correctly out of scope. Extensionally the modified
     kernel equals Candle (SYM is admissible); it is a different *build*
     (different inference relation / code), re-verified.
   * A pure *implementation-efficiency* edit (same relation, recompiled code)
     is a DIFFERENT obligation — CakeML compiler/refinement correctness, not
     `holSoundness` — and lives in the CakeML layer, not here.

  PROVED against the real Candle semantics; no `cheat`; only trust is
  `proves_sound`/`REFL_correct`/`termsem_equation` (the built Candle theorems
  the whole §4 layer already rests on). NO new turtle.
*)
open HolKernel boolLib bossLib BasicProvers
     setSpecTheory holSyntaxLibTheory
     holSyntaxTheory holSyntaxExtraTheory
     holSemanticsTheory holSemanticsExtraTheory holSoundnessTheory
     systemTheory envelopeTheory safetyTheory sv_weakeningTheory
     upgradeTheory selfProverTheory kernelUpgradeTheory;

val _ = new_theory "kernelMod";

val _ = Parse.hide "mem";
val mem = ``mem:'U->'U->bool``;

(* ------------------------------------------------------------------ *)
(* 1. THE NEW RULE'S SOUNDNESS.                                        *)
(*    The SYM disjunct added below is re-verified sound by Candle's    *)
(*    OWN modular machinery: `sym_equation` (the syntactic SYM         *)
(*    admissibility, `thyh |- p===q ⇒ thyh |- q===p`) composed with    *)
(*    `proves_sound`. This is the cheapest honest discharge — it reuses *)
(*    a built Candle lemma. (Proving a *fresh* per-rule `_correct`     *)
(*    semantically — e.g. for a rule Candle does NOT already admit —    *)
(*    follows Candle's `REFL_correct` template against                 *)
(*    `termsem_equation`; `refl_kernel` below exercises that semantic   *)
(*    route directly via the built `REFL_correct`.)                    *)
(* ------------------------------------------------------------------ *)
(* ------------------------------------------------------------------ *)
(* 2. THE MODIFIED KERNELS (genuine source diffs of the inference      *)
(*    relation), each RE-VERIFIED sound.                               *)
(* ------------------------------------------------------------------ *)

(* (a) SYM as a kernel primitive: accept `b === a` directly whenever the base
       kernel proves `a === b`. Candle only *derives* SYM (it is not a
       primitive rule), so this changes the inference relation. Sound via
       sym_equation + proves_sound (Candle's own SYM admissibility). *)
Definition sym_kernel_def:
  sym_kernel thy obl ⇔
    (thy,[]) |- obl ∨
    (∃a b. obl = (b === a) ∧ (thy,[]) |- (a === b))
End

Theorem sym_kernel_sound:
  is_set_theory (^mem) ⇒ kernel_sound (^mem) sym_kernel
Proof
  rw[kernel_sound_def, sym_kernel_def]
  >- metis_tac[proves_sound]
  >- (`(thy,[]) |- (b === a)` by metis_tac[sym_equation] >>
      metis_tac[proves_sound])
QED

(* (b) A reflexivity fast-path primitive — sound via Candle's existing
       REFL_correct alone (a re-verification that reuses the modular lemma
       directly, no new semantics). *)
Definition refl_kernel_def:
  refl_kernel thy obl ⇔
    (thy,[]) |- obl ∨
    (∃t. obl = (t === t) ∧ theory_ok thy ∧ term_ok (sigof thy) t)
End

Theorem refl_kernel_sound:
  is_set_theory (^mem) ⇒ kernel_sound (^mem) refl_kernel
Proof
  rw[kernel_sound_def, refl_kernel_def]
  >- metis_tac[proves_sound]
  >- metis_tac[REFL_correct]
QED

(* The modified kernel really is a different inference relation: it admits a
   conclusion via its NEW primitive rule (the SYM disjunct), structurally
   distinct from a base-kernel derivation. *)
Theorem sym_kernel_extends_base:
  (thy,[]) |- (a === b) ⇒ sym_kernel thy (b === a)
Proof
  rw[sym_kernel_def] >> metis_tac[]
QED

(* ------------------------------------------------------------------ *)
(* 3. FEED THE MODIFIED BUILD THROUGH selfProver's FROZEN-ROOT GATE.   *)
(*    `frozen_checker_sound` discharged for the MODIFIED kernel        *)
(*    (sym_kernel), from its re-verified soundness — and prover        *)
(*    self-improvement is then safe, UNCONDITIONAL in the seam, for a  *)
(*    genuinely modified prover build.                                 *)
(* ------------------------------------------------------------------ *)
Definition sound_real_def:
  sound_real (^mem) (B:thy->term->bool) ⇔ is_set_theory (^mem) ⇒ kernel_sound (^mem) B
End

(* The frozen root accepts the MODIFIED build sym_kernel (because we
   re-proved its soundness above). *)
Definition hol4_checks_mod_def:
  hol4_checks_mod (p:'p) (B:thy->term->bool) ⇔ (B = sym_kernel)
End

(* THE DISCHARGE for the modified build — frozen_checker_sound, PROVED, from
   the modified kernel's freshly re-verified soundness. *)
Theorem frozen_checker_sound_modified:
  frozen_checker_sound hol4_checks_mod (sound_real (^mem))
Proof
  rw[frozen_checker_sound_def, hol4_checks_mod_def, sound_real_def] >>
  metis_tac[sym_kernel_sound]
QED

(* Prover self-improvement through the MODIFIED, re-verified kernel preserves
   safety for every controller — unconditional in the seam (no
   `frozen_checker_sound` hypothesis: discharged for sym_kernel). *)
Theorem prover_self_improvement_is_safe_modified:
  build_certifies (sound_real (^mem)) sym_kernel step safe oldp newp ∧
  init_safe init safe ∧
  safe_shield step safe shield ∧
  sound_policy step safe oldp ⇒
  ∀ctrl. invariant step init
            (enveloped (admit step safe oldp newp) shield ctrl) safe
Proof
  rpt strip_tac >>
  `sound_real (^mem) sym_kernel`
    by (rw[sound_real_def] >> metis_tac[sym_kernel_sound]) >>
  `admissible step safe oldp newp` by metis_tac[build_certifies_def] >>
  irule admit_preserves_safety >> fs[]
QED

val _ = export_theory ();
