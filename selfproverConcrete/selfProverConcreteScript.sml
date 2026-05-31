(*
  selfProverConcreteScript — follow-up #28, the BASE CASE, discharged.

  selfProverScript.sml establishes prover self-improvement *abstractly*: a
  proposed prover build is opaque DATA `B`, its soundness obligation an
  abstract `sound : 'b -> bool`, and the frozen-HOL4 checker an abstract
  `hol4_checks`, with the one labelled seam

      frozen_checker_sound hol4_checks sound ⇔ ∀p B. hol4_checks p B ⇒ sound B.

  This file makes the base case CONCRETE and discharges that seam — not for
  an opaque B, but for the *real* Candle build, using the *real* built
  soundness theorem `holSoundnessTheory.proves_sound` (via
  `kernelUpgradeTheory.candle_kernel_sound`). It is the exact analogue, for
  the prover seam, of:

    * the watchdog flip  `encodes_obligation`  ASSUMED → PROVED
      (`kernel/watchdogFiniteScript.sml`), and
    * the genealogy      `identity_vouch_unconditional`
      (`genealogy/genealogyScript.sml`),

  i.e. the NON-STRENGTHENING / already-verified case is unconditional, and
  the honest negative (a genuinely *new* build needs its own soundness proof)
  is stated, not papered over.

  Tier 2: requires the built CakeML candle chain. The seam here is *finite
  proof replay* against an already-built `proves_sound`, NOT the
  hol-reflection/lca RAM monster — so this builds and checks like any other
  light theory once the candle chain is present.

  PROVED; no `cheat`; the only trust is `proves_sound` itself (the built
  Candle soundness theorem — the same one the whole §4 layer already rests
  on). NO new turtle.
*)
open HolKernel boolLib bossLib BasicProvers
     holSyntaxTheory holSemanticsTheory holSoundnessTheory
     systemTheory envelopeTheory safetyTheory sv_weakeningTheory
     upgradeTheory selfProverTheory kernelUpgradeTheory;

val _ = new_theory "selfProverConcrete";

val _ = Parse.hide "mem";
val mem = ``mem:'U->'U->bool``;

(* ------------------------------------------------------------------ *)
(* 1. The concrete instances of selfProver's abstract parameters.      *)
(* ------------------------------------------------------------------ *)

(* The "build" is a kernel (a provability relation), exactly as in
   kernelUpgradeTheory. The concrete soundness obligation `sound_real` is the
   real `proves_sound`-shaped property — `kernel_sound` under a set theory. *)
Definition sound_real_def:
  sound_real (^mem) (B:thy->term->bool) ⇔
    is_set_theory (^mem) ⇒ kernel_sound (^mem) B
End

(* The concrete frozen-HOL4 checker: it accepts exactly the build whose
   soundness HOL4 has actually proved — the real Candle kernel
   `candle_kernel`. (`p` is the proof object; here the witnessing proof is
   the built `proves_sound`, so acceptance is determined by the build being
   the real one.) *)
Definition hol4_checks_real_def:
  hol4_checks_real (p:'p) (B:thy->term->bool) ⇔ (B = candle_kernel)
End

(* ------------------------------------------------------------------ *)
(* 2. THE DISCHARGE: frozen_checker_sound, PROVED for the real build.  *)
(*    Was the labelled selfProver seam; here it is a theorem, from the *)
(*    real candle_kernel_sound (= proves_sound). ASSUMED → PROVED.     *)
(* ------------------------------------------------------------------ *)
Theorem frozen_checker_sound_candle:
  frozen_checker_sound hol4_checks_real (sound_real (^mem))
Proof
  rw[frozen_checker_sound_def, hol4_checks_real_def, sound_real_def] >>
  metis_tac[candle_kernel_sound]
QED

(* The honest negative, stated as a theorem (analogue of
   `loeb_finite_obstruction` / `genealogy_irrelevant_to_vouch_sound`): the
   concrete frozen checker certifies EXACTLY the one build whose soundness is
   already a theorem. Extending to a genuinely *modified* kernel B' is not
   free — it requires B's own `proves_sound`-shaped theorem (re-running the
   soundness development for the modified kernel: the genuine #28 effort).
   This base case discharges the non-strengthening build only. *)
Theorem frozen_checker_covers_only_the_verified_build:
  hol4_checks_real p B ⇒ (B = candle_kernel)
Proof
  rw[hol4_checks_real_def]
QED

(* ------------------------------------------------------------------ *)
(* 3. The CONCRETE prover-self-improvement theorem — UNCONDITIONAL in  *)
(*    the seam. selfProver's `prover_self_improvement_is_safe` no      *)
(*    longer carries `frozen_checker_sound` as a hypothesis: it is     *)
(*    discharged for the real Candle build above.                      *)
(* ------------------------------------------------------------------ *)
Theorem prover_self_improvement_is_safe_candle:
  build_certifies (sound_real (^mem)) candle_kernel step safe oldp newp ∧
  init_safe init safe ∧
  safe_shield step safe shield ∧
  sound_policy step safe oldp ⇒
  ∀ctrl. invariant step init
            (enveloped (admit step safe oldp newp) shield ctrl) safe
Proof
  rpt strip_tac >>
  ‘sound_real (^mem) candle_kernel’
    by (rw[sound_real_def] >> metis_tac[candle_kernel_sound]) >>
  ‘admissible step safe oldp newp’ by metis_tac[build_certifies_def] >>
  irule admit_preserves_safety >> fs[]
QED

(* And the install corollary, concretely: when the candle build certified the
   proposal, the policy weakening genuinely installs. *)
Theorem prover_self_improvement_installs_candle:
  build_certifies (sound_real (^mem)) candle_kernel step safe oldp newp ⇒
  admit step safe oldp newp = newp
Proof
  rpt strip_tac >>
  ‘sound_real (^mem) candle_kernel’
    by (rw[sound_real_def] >> metis_tac[candle_kernel_sound]) >>
  ‘admissible step safe oldp newp’ by metis_tac[build_certifies_def] >>
  rw[admit_def]
QED

val _ = export_theory ();
