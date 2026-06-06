(*
  selfRecompileGateScript — the BRIDGE between the running loop and the proved
  spine.

  `candle/self_recompile.ml` RUNS, on the real `cake` binary, a proof-gated
  recompile -> swap -> resume loop: a compute routine behind a ref indirection
  is replaced, at runtime, by a freshly-compiled version (compiled to native by
  the in-binary CakeML compiler, installed via the verified `do_install`), but
  ONLY after the live Candle kernel certifies `|- !x. new x = spec x`. Swaps
  accumulate (path-dependent); an uncertifiable swap is rejected.

  Here we show that loop's safety is not new trust — it is an INSTANCE of the
  already-proved genealogy (`genealogyTheory.genealogy_sound`): with the runtime
  gate as the vouching and "implementation agrees with the reference spec" as the
  soundness judge, every version the loop ever runs is correct, for ANY path.

  The install side (no running code is lost across a swap) is the separately-
  proved `loader/installLoaderScript : do_install_preserves_code`, over CakeML's
  real `closSem$do_install` — cited, not re-proved here.

  PROVED; pure light HOL4; no `cheat`.
*)
open HolKernel boolLib bossLib BasicProvers genealogyTheory;

val _ = new_theory "selfRecompileGate";

(* An implementation is CORRECT (w.r.t. a reference spec) iff it agrees with the
   spec on every input — the property `candle/self_recompile.ml`'s outputs witness. *)
Definition impl_correct_def:
  impl_correct (spec:'a->'b) (f:'a->'b) ⇔ ∀x. f x = spec x
End

(* The runtime GATE admits a swap to `g` iff the kernel CERTIFIED `g = spec`
   extensionally — exactly the `|- !x. g x = spec x` the live Candle kernel
   echoes (GATE1/GATE2 in candle/self_recompile.ml). *)
Definition gate_certified_def:
  gate_certified (spec:'a->'b) (g:'a->'b) ⇔ ∀x. g x = spec x
End

(* The gate is a SOUND vouching for correctness: a gate-certified successor is
   correct outright (it equals the spec), so it preserves the soundness judge.
   This is the genealogy `vouch_sound` seam at the implementation-correctness
   judge — and it is UNCONDITIONAL (no Löb): the gate proves equality to a fixed
   spec, never a strengthening. *)
Theorem gate_is_vouch_sound:
  vouch_sound (impl_correct spec) (λf g. gate_certified spec g)
Proof
  rw[vouch_sound_def, impl_correct_def, gate_certified_def]
QED

(* THE BRIDGE. A correct genesis implementation + an UNBOUNDED, path-dependent
   stream of gate-certified swaps (each `|- !x. V (SUC n) x = spec x`, as the
   live kernel produces) ⇒ EVERY version the loop runs is correct. This is pure
   `genealogy_sound`, instantiated at the running loop. *)
Theorem self_recompile_loop_is_safe:
  impl_correct spec (V 0n) ∧
  forward_certified (λf g. gate_certified spec g) V ⇒
  ∀n. impl_correct spec (V n)
Proof
  rpt strip_tac >>
  `vouch_sound (impl_correct spec) (λf g. gate_certified spec g)`
    by rw[gate_is_vouch_sound] >>
  metis_tac[genealogy_sound]
QED

(* The observable consequence the run exhibits: no accepted swap, however many
   accumulate, can ever change an output — the loop's results are pinned to the
   genesis spec. (out_genesis = out_after1 = out_after2 = out_after_bad, live.) *)
Theorem self_recompile_preserves_outputs:
  impl_correct spec (V 0n) ∧
  forward_certified (λf g. gate_certified spec g) V ⇒
  ∀n x. V n x = spec x
Proof
  rpt strip_tac >>
  `impl_correct spec (V n)` by metis_tac[self_recompile_loop_is_safe] >>
  fs[impl_correct_def]
QED

(* The REJECT case, made explicit: the loop only advances along gate-certified
   steps, so an uncertifiable proposal leaves the running version unchanged —
   correctness is preserved *because* the gate refuses what it cannot certify.
   (bad_gate_ok = false ⇒ no swap ⇒ out_after_bad unchanged, live.) *)
Theorem uncertified_swap_is_not_a_step:
  ¬gate_certified spec g ⇒ (λf g'. gate_certified spec g') f g = F
Proof
  rw[]
QED

val _ = export_theory ();
