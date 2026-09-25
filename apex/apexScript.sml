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

  PROVED; pure light HOL4.
*)
open HolKernel boolLib bossLib BasicProvers
     certifierTheory genealogyTheory recursiveImprovementTheory;

val _ = new_theory "apex";

(* ---- THE COMPILER LINE: self-recompilation stays correct ------------- *)
(* `compiles c src` = the compiler `c` recompiling source `src` into a new
   compiler binary (cake compiling cake's own s-expression — APEX I, executed).
   `cake_correct` is CakeML's verified compiler-correctness (CITED). The single
   cited step is: a correct compiler recompiles to a correct compiler.
   The compiler line is certifierTheory's ratchet_stream at judge
   cake_correct and step "recompile some source". *)
Theorem compiler_self_recompilation_stays_correct:
  (∀c src. cake_correct c ⇒ cake_correct (compiles c src)) ∧   (* CITED: CakeML compiler-correctness *)
  cake_correct (C 0n) ∧
  (∀n. C (SUC n) = compiles (C n) (src n)) ⇒
  ∀n. cake_correct (C n)
Proof
  strip_tac >>
  qspecl_then [‘cake_correct’, ‘λc c'. ∃s. c' = compiles c s’, ‘C’]
              mp_tac ratchet_stream >>
  impl_tac >- (rw[ratchet_def, follows_def] >> metis_tac[]) >>
  simp[]
QED

(* ---- THE APEX AS A GENEALOGY ------------------------------------------ *)
(* A generation is a (prover, compiler) pair. The Apex JUDGE of a generation:
   its prover is sound and its compiler is correct. The Apex VOUCHING from
   generation A to B: the prover advanced by a gate-certified step (`vstep`)
   and the compiler is A's compiler recompiling some source. *)
Definition apex_sound_def:
  apex_sound psound cake_correct g ⇔ psound (FST g) ∧ cake_correct (SND g)
End

Definition apex_vouch_def:
  apex_vouch vstep compiles A B ⇔
    vstep (FST A) (FST B) ∧ ∃src. SND B = compiles (SND A) src
End

(* The Apex's two cited facts (prover steps preserve soundness; CakeML
   recompilation preserves correctness) are exactly what makes the Apex
   vouching SOUND for the Apex judge: the genealogy's seam. *)
Theorem apex_vouch_sound:
  (∀A B. vstep A B ⇒ (psound A ⇒ psound B)) ∧
  (∀c src. cake_correct c ⇒ cake_correct (compiles c src)) ⇒
  vouch_sound (apex_sound psound cake_correct) (apex_vouch vstep compiles)
Proof
  rw[vouch_sound_def, apex_sound_def, apex_vouch_def] >> metis_tac[]
QED

(* The Apex succession (prover line advancing by `vstep`, compiler line by
   self-recompilation of `csrc n`) is FORWARD-CERTIFIED for the Apex
   vouching: the genealogy's other condition. *)
Theorem apex_forward_certified:
  (∀n. vstep (FST (Gen n)) (FST (Gen (SUC n)))) ∧
  (∀n. SND (Gen (SUC n)) = compiles (SND (Gen n)) (csrc n)) ⇒
  forward_certified (apex_vouch vstep compiles) Gen
Proof
  rw[forward_certified_def, apex_vouch_def] >> metis_tac[]
QED

(* The Apex IS a genealogy: under exactly `apex_generations_safe`'s
   hypotheses, the Apex vouching is sound for the Apex judge, the Apex
   succession is forward-certified for it, and so (by `genealogy_sound`,
   genesis = generation 0) every generation is Apex-sound. *)
Theorem apex_is_a_genealogy:
  (∀A B. vstep A B ⇒ (psound A ⇒ psound B)) ∧
  (∀n. vstep (FST (Gen n)) (FST (Gen (SUC n)))) ∧
  psound (FST (Gen 0n)) ∧
  (∀c src. cake_correct c ⇒ cake_correct (compiles c src)) ∧
  (∀n. SND (Gen (SUC n)) = compiles (SND (Gen n)) (csrc n)) ∧
  cake_correct (SND (Gen 0n)) ⇒
  vouch_sound (apex_sound psound cake_correct) (apex_vouch vstep compiles) ∧
  forward_certified (apex_vouch vstep compiles) Gen ∧
  ∀n. apex_sound psound cake_correct (Gen n)
Proof
  strip_tac >>
  ‘vouch_sound (apex_sound psound cake_correct) (apex_vouch vstep compiles)’
    by metis_tac[apex_vouch_sound] >>
  ‘forward_certified (apex_vouch vstep compiles) Gen’
    by metis_tac[apex_forward_certified] >>
  ‘apex_sound psound cake_correct (Gen 0)’ by rw[apex_sound_def] >>
  metis_tac[genealogy_sound]
QED

(* ---- THE CAPSTONE: every generation is sound prover + correct compiler -- *)
(* The whole unbounded, path-dependent succession keeps BOTH invariants:
   the Apex genealogy's conclusion, unfolded. *)
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
  strip_tac >> gen_tac >>
  ‘apex_sound psound cake_correct (Gen n)’
    by metis_tac[apex_is_a_genealogy] >>
  fs[apex_sound_def]
QED

val _ = export_theory ();
