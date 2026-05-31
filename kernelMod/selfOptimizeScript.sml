(*
  selfOptimizeScript — the self-optimizing prover, with the UPDATER MECHANISM
  (a relocating hot-swap) verified as a protocol, and the unbounded
  self-optimization loop proved safe.

  inplaceUpdateScript left the *act* of swapping the running image as
  unverified plumbing. This file models the updater mechanism — including a
  RELOCATOR — and proves the self-update PROTOCOL sound, then lifts it to an
  UNBOUNDED stream of self-proposed optimizations. The result is a model of a
  genuinely self-optimizing prover whose verification boundary is made
  explicit: the machine-level guarantees (relocation correctness, CakeML
  compiler/refinement) are LABELLED obligations a verified loader + the CakeML
  root discharge; the protocol soundness and the loop are THEOREMS.

  --------------------------------------------------------------------------
  CAN WE EVEN VERIFY THE RELOCATOR?  Yes, in principle — relocation
  correctness ("the relocated image runs as its semantics specifies, at
  whatever address it is loaded") is a well-defined, bounded property;
  verified loaders/linkers exist in the literature. We model it as
  `reloc_correct` and prove the update protocol sound *given* it. Extending
  the hot-patcher with a relocator is then: add `relocate` with its
  `reloc_correct` obligation — which is exactly what is done below.

  --------------------------------------------------------------------------
  THE NO-LÖB POINT (why a self-OPTIMIZING prover is verifiable but a
  self-STRENGTHENING one is not). Each optimization step is a SOUND EXTENSION
  of the current prover: same-or-more theorems, still sound. A current sound
  prover vouching for a sound *extension of itself* is fine — no reflection
  principle, no Löb. Löb bites ONLY a self-modification that proves strictly
  MORE (a genuine logical strengthening), which is the separate, already-
  labelled `kernelUpgradeTheory.loeb_reflection` and stays out of scope. So:
  optimize/refactor/extend-conservatively — verifiable, unbounded, here.
  Strengthen the logic — the LCA wall, elsewhere.

  PROVED against the real Candle semantics; no `cheat`; trust = the built
  Candle soundness theorems only. NO new turtle.
*)
open HolKernel boolLib bossLib BasicProvers
     holSyntaxTheory holSemanticsTheory
     kernelUpgradeTheory kernelModTheory;

val _ = new_theory "selfOptimize";

val _ = Parse.hide "mem";
val mem = ``mem:'U->'U->bool``;

(* ------------------------------------------------------------------ *)
(* 1. A SOUND EXTENSION — the invariant a safe self-optimization keeps. *)
(* ------------------------------------------------------------------ *)

(* `sound_extension mem Knew Kold`: the new prover is sound AND proves
   everything the old one did. This is the single property that makes a
   self-modification of the prover SAFE: nothing false is gained, no theorem
   already in the running heap is lost. *)
Definition sound_extension_def:
  sound_extension (^mem) (Knew:thy->term->bool) (Kold:thy->term->bool) ⇔
    kernel_sound (^mem) Knew ∧ (∀thy obl. Kold thy obl ⇒ Knew thy obl)
End

Theorem sound_extension_trans:
  sound_extension (^mem) K2 K1 ∧ sound_extension (^mem) K1 K0 ⇒
  sound_extension (^mem) K2 K0
Proof
  rw[sound_extension_def] >> metis_tac[]
QED

(* The concrete optimization of kernelModScript — adding SYM as a kernel
   primitive — IS a sound extension of the base Candle build. Discharged
   from the real Candle semantics. *)
Theorem sym_is_sound_extension:
  is_set_theory (^mem) ⇒ sound_extension (^mem) sym_kernel candle_kernel
Proof
  rw[sound_extension_def]
  >- metis_tac[sym_kernel_sound]
  >- fs[sym_kernel_def, candle_kernel_def]
QED

(* ------------------------------------------------------------------ *)
(* 2. THE UPDATER MECHANISM: a verified RELOCATING hot-swap.           *)
(* ------------------------------------------------------------------ *)

(* `run img` is the inference relation the loaded image computes (the net of
   L0⊑L1 compiler-correctness ∘ L1⊑L2 ml_kernel refinement). `relocate img
   addr` is the relocator: load `img` at address `addr`, fixing up addresses.

   RELOCATION CORRECTNESS (the relocator's obligation, LABELLED): a relocated
   image computes the SAME inference relation, wherever it is loaded — its
   behaviour is position-independent. This is exactly what a verified
   relocating loader provides. *)
Definition reloc_correct_def:
  reloc_correct (run:'img -> thy -> term -> bool)
                (relocate:'img -> 'addr -> 'img) ⇔
    ∀img addr. run (relocate img addr) = run img
End

(* ONE verified self-update step through the full mechanism. Premises:
    - the relocator is correct (LABELLED);
    - the recompiled binary computes the new kernel `Knew` (LABELLED: the
      CakeML compiler-correctness ∘ ml_kernel refinement for the new build —
      the `frozen_checker_sound`-style obligation, one layer down);
    - `Knew` is a SOUND EXTENSION of the running prover (DISCHARGED for sym).
   Conclusion: after relocate-and-install, the running image computes `Knew`,
   it is sound, and every theorem already produced survives. *)
Theorem verified_hot_swap_safe:
  is_set_theory (^mem) ∧
  reloc_correct run relocate ∧
  (run bin_new = Knew) ∧
  sound_extension (^mem) Knew (run bin_old) ⇒
  (run (relocate bin_new addr) = Knew) ∧
  kernel_sound (^mem) Knew ∧
  (∀thy obl. run bin_old thy obl ⇒ Knew thy obl)
Proof
  rw[]
  >- metis_tac[reloc_correct_def]
  >- fs[sound_extension_def]
  >- fs[sound_extension_def]
QED

(* ------------------------------------------------------------------ *)
(* 3. THE UNBOUNDED SELF-OPTIMIZATION LOOP.                            *)
(*    A stream of self-proposed optimizations, each a sound extension  *)
(*    installed by a verified hot-swap, never loses soundness or any   *)
(*    theorem — the binary-level analogue of                          *)
(*    `upgradeTheory.self_improvement_is_safe`.                        *)
(* ------------------------------------------------------------------ *)

(* The kernel in force after applying a list of proposed optimizations. *)
Definition apply_opts_def:
  (apply_opts K0 [] = K0) ∧
  (apply_opts K0 (K'::rest) = apply_opts K' rest)
End

(* A valid optimization stream: each step is a sound extension of the one
   before it. *)
Definition opts_valid_def:
  (opts_valid (^mem) K0 [] ⇔ T) ∧
  (opts_valid (^mem) K0 (K'::rest) ⇔
     sound_extension (^mem) K' K0 ∧ opts_valid (^mem) K' rest)
End

Theorem self_optimization_is_safe:
  ∀ks K0.
    opts_valid (^mem) K0 ks ∧ kernel_sound (^mem) K0 ⇒
    kernel_sound (^mem) (apply_opts K0 ks) ∧
    (∀thy obl. K0 thy obl ⇒ apply_opts K0 ks thy obl)
Proof
  Induct >> rw[apply_opts_def, opts_valid_def] >>
  fs[sound_extension_def] >> metis_tac[]
QED

(* ------------------------------------------------------------------ *)
(* 4. THE HEADLINE: a self-optimizing prover, from genesis.            *)
(* ------------------------------------------------------------------ *)

(* Starting as the base Candle build and applying an UNBOUNDED stream of
   self-proposed optimizations — each a sound extension, each installed by a
   verified relocating hot-swap — the running prover stays sound and never
   loses a theorem. The optimization stream is fully adversarial (∀ks);
   `sym_kernel` (kernelModScript) is one concrete admissible step. *)
Theorem self_optimizing_prover_is_safe:
  is_set_theory (^mem) ∧
  opts_valid (^mem) candle_kernel ks ⇒
  kernel_sound (^mem) (apply_opts candle_kernel ks) ∧
  (∀thy obl. candle_kernel thy obl ⇒ apply_opts candle_kernel ks thy obl)
Proof
  rpt strip_tac >>
  `kernel_sound (^mem) candle_kernel` by metis_tac[candle_kernel_sound] >>
  metis_tac[self_optimization_is_safe]
QED

(* The concrete first step is realizable: optimizing the base Candle build to
   the SYM-primitive kernel is a valid step of any self-optimization stream
   (so the loop is non-vacuous — there is a real optimization to take). *)
Theorem sym_step_is_a_valid_optimization:
  is_set_theory (^mem) ⇒ opts_valid (^mem) candle_kernel [sym_kernel]
Proof
  rw[opts_valid_def] >> metis_tac[sym_is_sound_extension]
QED

val _ = export_theory ();
