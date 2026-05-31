(*
  genesisRuntimeScript — "HOL4 stays out of execution", as a theorem.

  The architecture's claim: the root HOL4 prover vouches ONCE, at genesis,
  for the runtime checker (Candle) — and then drops out. The running system
  self-optimizes unboundedly, driven only by the running checker, with NO
  per-step HOL4 involvement. This file makes that precise.

  A RUNTIME CHECKER is the running Candle: a relation `checker Kold Knew`
  deciding "is the proposed edit Knew an acceptable self-optimization of the
  current kernel Kold". Its SOUNDNESS — that it only ever accepts sound
  extensions — is a SINGLE genesis fact (`checker_sound`), established once by
  HOL4 (it is the meta-theorem about Candle's checking, the proves_sound
  family). The runtime then applies `checker` per step, forever.

  THE HEADLINE (`genesis_certifies_runtime`): given the one genesis fact
  (`checker_sound`) and a sound genesis kernel, ANY unbounded stream of
  edits accepted AT RUNTIME by the checker keeps the prover sound and loses
  no theorem — with no further appeal to HOL4. The only HOL4 input is the
  single, genesis-time `checker_sound`; everything per-step is the running
  checker. That is exactly "sound once at genesis, certified forward; HOL4
  out of the hot loop".

  PROVED; trust = the built Candle soundness theorems only; no `cheat`.
*)
open HolKernel boolLib bossLib BasicProvers
     kernelUpgradeTheory kernelModTheory selfOptimizeTheory;

val _ = new_theory "genesisRuntime";

val _ = Parse.hide "mem";
val mem = ``mem:'U->'U->bool``;

(* The runtime checker's soundness — the ONE genesis fact. It says: whatever
   the running checker accepts is a sound extension. Established once, by
   HOL4, about Candle's checking (the proves_sound family); never re-invoked
   per step. *)
Definition checker_sound_def:
  checker_sound (^mem) (checker:(thy->term->bool)->(thy->term->bool)->bool) ⇔
    ∀Kold Knew. checker Kold Knew ⇒ sound_extension (^mem) Knew Kold
End

(* The runtime loop: each successive edit is accepted by the running checker.
   This is the only thing that happens at runtime — calls to `checker`. *)
Definition accepted_chain_def:
  (accepted_chain checker K0 [] ⇔ T) ∧
  (accepted_chain checker K0 (K'::rest) ⇔
     checker K0 K' ∧ accepted_chain checker K' rest)
End

(* A runtime-accepted chain is a valid sound-extension chain — using ONLY the
   single genesis fact checker_sound, reused (not re-proved) per step. *)
Theorem accepted_implies_valid:
  ∀ks K0.
    checker_sound (^mem) checker ∧ accepted_chain checker K0 ks ⇒
    opts_valid (^mem) K0 ks
Proof
  Induct >> rw[accepted_chain_def, opts_valid_def] >>
  metis_tac[checker_sound_def]
QED

(* THE HEADLINE: the unbounded runtime self-optimization loop is safe, given
   ONLY the genesis-established soundness of the runtime checker. Every edit
   is accepted at runtime by the running checker (`accepted_chain`); the only
   HOL4 input is the single `checker_sound`. The prover stays sound and loses
   no theorem — HOL4 never enters the per-step loop. *)
Theorem genesis_certifies_runtime:
  is_set_theory (^mem) ∧
  checker_sound (^mem) checker ∧
  accepted_chain checker candle_kernel ks ⇒
  kernel_sound (^mem) (apply_opts candle_kernel ks) ∧
  (∀thy obl. candle_kernel thy obl ⇒ apply_opts candle_kernel ks thy obl)
Proof
  rpt strip_tac >>
  `opts_valid (^mem) candle_kernel ks`
    by metis_tac[accepted_implies_valid] >>
  metis_tac[self_optimizing_prover_is_safe]
QED

(* And the genesis fact is REAL, not vacuous: a checker that accepts exactly
   the sym-kernel optimization is sound (its soundness is `sym_is_sound_
   extension` — established once, at genesis, by HOL4 from proves_sound). *)
Theorem sym_checker_is_sound:
  is_set_theory (^mem) ⇒
  checker_sound (^mem)
    (λKold Knew. (Kold = candle_kernel) ∧ (Knew = sym_kernel))
Proof
  rw[checker_sound_def] >> metis_tac[sym_is_sound_extension]
QED

val _ = export_theory ();
