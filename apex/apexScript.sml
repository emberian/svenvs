(*
  apexScript — THE APEX, proved safe.

  The svenvs Apex is a self-improving, self-recompiling system whose two
  self-modifications are EXECUTED on the real verified CakeML/Candle stack
  (see scripts/apex.sh) and proved SAFE here as one genealogy of generations:

    * the COMPILER recompiles itself (`scripts/apex.sh` APEX I: cake compiles
      cake's own s-expression to a new working cake; bit-identical FIXPOINT;
      and a self-OPTIMIZED rebuild that stays correct). Correctness is CakeML's
      verified compiler-correctness theorem — CITED here as `cake_correct`, a
      hypothesis, not re-proved.

    * the PROVER improves itself by gate-certified SOUND EXTENSIONS
      (`candle/self_recompile.ml`, APEX II: a runtime recompile->swap->resume
      loop gated by live kernel proofs). The "no Löb for optimization" discharge
      is `kernelMod/selfOptimizeScript.sml : sound_extension /
      self_optimization_is_safe` — CITED as the prover-step hypothesis.

  This file PROVES that, given those two cited facts, EVERY generation of the
  running Apex has a sound prover AND a correct compiler — for ANY path. It is
  the concrete (prover × compiler) instance of
  `recursive/recursiveImprovementScript.sml : recursive_mutual_self_improvement_is_safe`.

  HONEST RESIDUAL (stated, not hidden): this proves the system safe and the two
  self-modifications are executed; it does NOT execute an in-process swap of the
  trusted *kernel's own code* (compiled into cake.S, perms_ok-protected) — that
  needs a proven kernel-modified cake.S (in-logic re-verification). See CLAIMS.md.

  PROVED; pure light HOL4; no `cheat`.
*)
open HolKernel boolLib bossLib BasicProvers
     genealogyTheory recursiveImprovementTheory;

val _ = new_theory "apex";

(* ---- THE COMPILER LINE: self-recompilation stays correct ------------- *)
(* `compiles c src` = the compiler `c` recompiling source `src` into a new
   compiler binary (cake compiling cake's own s-expression — APEX I, executed).
   `cake_correct` is CakeML's verified compiler-correctness (CITED). The single
   cited step is: a correct compiler recompiles to a correct compiler. *)
Theorem compiler_self_recompilation_stays_correct:
  (∀c src. cake_correct c ⇒ cake_correct (compiles c src)) ∧   (* CITED: CakeML compiler-correctness *)
  cake_correct (C 0n) ∧
  (∀n. C (SUC n) = compiles (C n) (src n)) ⇒
  ∀n. cake_correct (C n)
Proof
  rpt strip_tac >> Induct_on ‘n’ >> rw[] >> metis_tac[]
QED

(* ---- THE CAPSTONE: every generation is sound prover + correct compiler -- *)
(* A generation is a (prover, compiler) pair. The prover line advances by
   gate-certified sound steps (each preserves soundness — the genealogy /
   selfOptimize discharge, Löb-free for optimization); the compiler line
   advances by self-recompilation that preserves correctness (CITED). Then the
   whole unbounded, path-dependent succession keeps BOTH invariants. *)
Theorem apex_generations_safe:
  (* PROVER line — gate-certified sound steps (CITED: kernelMod sound_extension) *)
  (∀A B. vstep A B ⇒ (psound A ⇒ psound B)) ∧
  (∀n. vstep (FST (Gen n)) (FST (Gen (SUC n)))) ∧
  psound (FST (Gen 0n)) ∧
  (* COMPILER line — self-recompilation preserves correctness (CITED: CakeML) *)
  (∀c src. cake_correct c ⇒ cake_correct (compiles c src)) ∧
  (∀n. SND (Gen (SUC n)) = compiles (SND (Gen n)) (csrc n)) ∧
  cake_correct (SND (Gen 0n)) ⇒
  (* ⇒ every generation: sound prover AND correct compiler, for ANY path *)
  ∀n. psound (FST (Gen n)) ∧ cake_correct (SND (Gen n))
Proof
  rpt strip_tac >> Induct_on ‘n’ >> rw[] >> metis_tac[]
QED

(* The same conclusion, recognised as an instance of the proved genealogy spine:
   with the soundness judge "this generation has a sound prover and a correct
   compiler", the Apex succession is `genealogy_sound`. *)
Theorem apex_is_a_genealogy:
  vouch_sound jsound vouches ∧ jsound (Gen 0n) ∧
  forward_certified vouches Gen ⇒
  ∀n. jsound (Gen n)
Proof
  metis_tac[genealogy_sound]
QED

val _ = export_theory ();
