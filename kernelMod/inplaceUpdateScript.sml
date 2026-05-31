(*
  inplaceUpdateScript — pushing the modified kernel through CakeML into an
  in-place update of the running prover, as far as the logic can carry it.

  --------------------------------------------------------------------------
  THE PIPELINE (bottom = what actually runs, top = what it means)

    L0  machine code (the running candle binary)
          ⊑  (CakeML COMPILER-CORRECTNESS: the verified `cake` compiler)
    L1  CakeML program semantics (ml_hol_kernelProg — the kernel as CakeML)
          ⊑  (ml_kernel REFINEMENT: the CakeML kernel functions only ever
              build `thm` values that lie in the inference relation)
    L2  the inference relation `|-`  (candle_kernel / sym_kernel)
          ⊑  (proves_sound)
    L3  set-theoretic validity `|=`

  An "in-place update" replaces the kernel: a modified source (implementing
  `sym_kernel`, kernelModScript) is recompiled by the verified CakeML compiler
  to a new binary, and swapped in. The honest question is: what makes that
  swap SAFE — and how much of it is a theorem vs. carried vs. genuinely open?

  --------------------------------------------------------------------------
  WHAT THIS FILE PROVES (and what it does not)

  THE KEY THEOREM: an in-place kernel swap is safe *exactly* because the new
  kernel is a SOUND EXTENSION of the old — i.e. it proves everything the old
  one did (so no `thm` already in the running heap is invalidated) and it is
  sound (so it produces nothing false). This is `sv_weakeningTheory`'s
  `safe_weakening` discipline lifted to the kernel: the swap loses no theorem
  and gains no unsoundness.

   * DISCHARGED (logic level, here): the new kernel is sound
     (`sym_kernel_sound`, kernelModScript), the old binary's kernel is sound
     (`candle_kernel_sound`), and the new kernel EXTENDS the old
     (`sym_extends_candle`) — so the running binary stays sound and every
     existing theorem survives the swap.

   * CARRIED (the genuine remaining CakeML re-proof), as a LABELLED premise
     `binary_implements produces bin_new sym_kernel`: that the recompiled
     binary really computes the modified inference relation. Concretely this
     is CakeML compiler-correctness ∘ the ml_kernel refinement
     (`candle/standard/ml_kernel/ml_hol_kernelProg…`) re-established for the
     modified kernel — the implementation-layer analogue of
     `frozen_checker_sound`, the same honest status, heavier (CakeML root).

   * OUT OF SCOPE (the open frontier, stated honestly): the *act* of swapping
     the running image in place — verified dynamic linking / hot-patch of the
     compiled binary. CakeML's verification is whole-program; there is no
     verified in-place machine-code update. What we prove is the SAFETY
     CONDITION such an updater must meet (sound extension + the new binary
     implements the new kernel), NOT the updater. With that condition met,
     the swap is non-destructive by construction.

  PROVED against the real Candle semantics; no `cheat`; trust = the built
  Candle soundness theorems only. NO new turtle.
*)
open HolKernel boolLib bossLib BasicProvers
     holSyntaxTheory holSemanticsTheory
     kernelUpgradeTheory kernelModTheory;

val _ = new_theory "inplaceUpdate";

val _ = Parse.hide "mem";
val mem = ``mem:'U->'U->bool``;

(* ------------------------------------------------------------------ *)
(* 1. KERNEL EXTENSION — the heap-preservation condition.              *)
(* ------------------------------------------------------------------ *)

(* `kernel_extends Knew Kold`: the new kernel proves everything the old one
   did. Operationally: every `thm` value the running prover has already
   produced (a witness of `Kold`) is still a valid `thm` under `Knew`, so an
   in-place swap to `Knew` invalidates nothing in the heap. *)
Definition kernel_extends_def:
  kernel_extends (Knew:thy->term->bool) (Kold:thy->term->bool) ⇔
    ∀thy obl. Kold thy obl ⇒ Knew thy obl
End

(* The modified kernel is a (sound) EXTENSION of the base Candle kernel. *)
Theorem sym_extends_candle:
  kernel_extends sym_kernel candle_kernel
Proof
  rw[kernel_extends_def, sym_kernel_def, candle_kernel_def]
QED

(* ------------------------------------------------------------------ *)
(* 2. THE BINARY ⊑ KERNEL REFINEMENT (the carried CakeML obligation).  *)
(* ------------------------------------------------------------------ *)

(* `binary_implements produces bin K`: the running binary `bin` only ever
   outputs theorems in the inference relation `K`. This abstracts the NET
   effect of L0⊑L1 (compiler-correctness) ∘ L1⊑L2 (ml_kernel refinement):
   both are real CakeML theorems; here their composite is the labelled
   premise carried per build, exactly as `frozen_checker_sound` is carried at
   the prover-build layer. *)
Definition binary_implements_def:
  binary_implements (produces:'bin->thy->term->bool) (bin:'bin)
                    (K:thy->term->bool) ⇔
    ∀thy obl. produces bin thy obl ⇒ K thy obl
End

(* A running binary implementing a SOUND kernel only ever outputs
   semantically-valid theorems: code-level soundness from logic-level
   soundness (`sym_kernel_sound`) composed through the refinement. This is
   L0 ⊑ … ⊑ L3 for the running new binary. *)
Theorem running_binary_sound:
  is_set_theory (^mem) ∧
  binary_implements produces bin sym_kernel ⇒
  ∀thy obl. produces bin thy obl ⇒ (thy,[]) |= obl
Proof
  rw[binary_implements_def] >>
  `kernel_sound (^mem) sym_kernel` by metis_tac[sym_kernel_sound] >>
  metis_tac[kernel_sound_def]
QED

(* ------------------------------------------------------------------ *)
(* 3. THE HEADLINE: the in-place update is safe.                       *)
(*    Old binary implements candle_kernel; the recompiled new binary   *)
(*    implements the modified sym_kernel (the carried CakeML            *)
(*    obligation). Then the swap (a) keeps every already-produced       *)
(*    theorem valid, (b) the new binary is sound, (c) loses no theorem. *)
(* ------------------------------------------------------------------ *)
Theorem inplace_update_is_safe:
  is_set_theory (^mem) ∧
  binary_implements produces bin_old candle_kernel ∧
  binary_implements produces bin_new sym_kernel ⇒
  (∀thy obl. produces bin_old thy obl ⇒ (thy,[]) |= obl) ∧
  (∀thy obl. produces bin_new thy obl ⇒ (thy,[]) |= obl) ∧
  (∀thy obl. candle_kernel thy obl ⇒ sym_kernel thy obl)
Proof
  rpt strip_tac
  >- (`kernel_sound (^mem) candle_kernel` by metis_tac[candle_kernel_sound] >>
      metis_tac[binary_implements_def, kernel_sound_def])
  >- (`kernel_sound (^mem) sym_kernel` by metis_tac[sym_kernel_sound] >>
      metis_tac[binary_implements_def, kernel_sound_def])
  >- metis_tac[sym_extends_candle, kernel_extends_def]
QED

(* The non-destruction property, isolated: no theorem already produced by the
   running (old) binary is invalidated by the swap — it remains valid under
   the new kernel's semantics. This is the precise sense in which the update
   may be done IN PLACE (the `thm` heap need not be discarded). *)
Theorem inplace_swap_preserves_heap:
  is_set_theory (^mem) ∧
  binary_implements produces bin_old candle_kernel ⇒
  ∀thy obl. produces bin_old thy obl ⇒
            sym_kernel thy obl ∧ (thy,[]) |= obl
Proof
  rw[]
  >- (`candle_kernel thy obl` by metis_tac[binary_implements_def] >>
      metis_tac[sym_extends_candle, kernel_extends_def])
  >- (`kernel_sound (^mem) candle_kernel` by metis_tac[candle_kernel_sound] >>
      metis_tac[binary_implements_def, kernel_sound_def])
QED

val _ = export_theory ();
