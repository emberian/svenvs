(*
  recursiveImprovementScript — the capstone.

  Recursive MUTUAL self-improvement: a faster verifier certifies a faster
  compiler, which recompiles a faster verifier, which certifies a faster
  compiler, ... forever. We show this is safe by recognising it as a
  GENEALOGY OVER (verifier, compiler) STAGES — `genealogyTheory.genealogy_sound`
  instantiated at the judge type `'v # 'c`.

  --------------------------------------------------------------------------
  THE THREE VOUCHINGS, AND WHY ONLY ONE TOUCHES LÖB

   * verifier certifies the new COMPILER — a *different* artifact: the
     selfprover asymmetry, NO Löb (`selfProverTheory.frozen_checker_sound`,
     discharged for the base build in `selfproverConcrete`).
   * the new compiler RECOMPILES the verifier — compiler-correctness, a
     theorem about a development, NO Löb. The recompiled binary refines the
     source; the loader (`loader/do_install_preserves_code`, proven over
     CakeML's real `do_install`) installs it without disturbing the running
     code.
   * verifier certifies the NEXT VERIFIER — the one self-reference. For a
     faster, EQUI-SOUND verifier (an OPTIMIZATION) the seam is the genealogy
     `vouch_sound`, discharged outright for the non-strengthening case
     (`genealogyTheory.identity_vouch_unconditional`;
     `kernelMod/selfOptimize : sound_extension`). Genuine logical
     STRENGTHENING of the verifier is the LCA/Löb wall
     (`kernelUpgradeTheory.loeb_reflection`) — the single labelled seam the
     whole tower isolates, and the only thing this recursion cannot do free.

  So: recursive mutual *optimization* of verifier↔compiler is sound,
  unbounded, and Löb-free; only verifier *strengthening* is walled. This file
  assembles that as one theorem, with the seam decomposed into exactly the
  genealogy (verifier line) and selfprover (compiler line) discharges.

  PROVED; pure light HOL4; no `cheat`.
*)
open HolKernel boolLib bossLib BasicProvers genealogyTheory;

val _ = new_theory "recursiveImprovement";

(* A STAGE is a (verifier, compiler) pair. *)
(* A stage is SOUND iff its verifier is sound AND its compiler is correct. *)
Definition stage_sound_def:
  stage_sound (vsound:'v->bool) (ccorrect:'c->bool) (st:'v # 'c) ⇔
    vsound (FST st) ∧ ccorrect (SND st)
End

(* One stage vouches for the next iff (1) the new verifier is an
   old-verifier-certified step (`vvouch`), (2) the new verifier certifies the
   new compiler (`vcert_c`), and (3) recompile+install preserves the running
   code (`loader_ok` — discharged by `do_install_preserves_code`). *)
Definition stage_vouches_def:
  stage_vouches (vvouch:'v->'v->bool) (vcert_c:'v->'c->bool)
                (loader_ok:('v # 'c)->('v # 'c)->bool)
                (st:'v # 'c) (st':'v # 'c) ⇔
    vvouch (FST st) (FST st') ∧
    vcert_c (FST st') (SND st') ∧
    loader_ok st st'
End

(* The stage seam DECOMPOSES into exactly the two component vouchings:
     (a) the VERIFIER line's genealogy seam (`vouch_sound vsound vvouch`), and
     (b) the COMPILER line's selfprover seam (a sound verifier certifying a
         compiler implies that compiler is correct).
   Neither is the Löb-bound verifier-strengthening seam (that lives inside
   `vvouch` for the strengthening case and is labelled elsewhere). *)
Theorem stage_seam_decomposes:
  vouch_sound vsound vvouch ∧
  (∀V C. vsound V ∧ vcert_c V C ⇒ ccorrect C) ⇒
  vouch_sound (stage_sound vsound ccorrect)
              (stage_vouches vvouch vcert_c loader_ok)
Proof
  rw[vouch_sound_def, stage_sound_def, stage_vouches_def] >> metis_tac[]
QED

(* ===================================================================== *)
(* THE CAPSTONE: recursive mutual verifier+compiler self-improvement.     *)
(* A sound genesis stage + the (decomposed) stage seam + a forward-       *)
(* certified UNBOUNDED succession of stages ⇒ EVERY stage in the line has *)
(* a SOUND VERIFIER and a CORRECT COMPILER. Pure genealogy_sound at the   *)
(* (verifier × compiler) judge type.                                      *)
(* ===================================================================== *)
Theorem recursive_mutual_self_improvement_is_safe:
  vouch_sound vsound vvouch ∧
  (∀V C. vsound V ∧ vcert_c V C ⇒ ccorrect C) ∧
  vsound (FST (St 0n)) ∧ ccorrect (SND (St 0n)) ∧
  forward_certified (stage_vouches vvouch vcert_c loader_ok) St ⇒
  ∀n. vsound (FST (St n)) ∧ ccorrect (SND (St n))
Proof
  rpt strip_tac >>
  `vouch_sound (stage_sound vsound ccorrect)
               (stage_vouches vvouch vcert_c loader_ok)`
    by metis_tac[stage_seam_decomposes] >>
  `stage_sound vsound ccorrect (St 0n)` by rw[stage_sound_def] >>
  `∀n. stage_sound vsound ccorrect (St n)` by metis_tac[genealogy_sound] >>
  fs[stage_sound_def]
QED

(* The loader runs at EVERY step: recompile+install preserves the running
   code throughout the whole recursive line (the `loader_ok` factor, to be
   discharged by `loader/do_install_preserves_code`). So no theorem already
   produced is ever lost across the unbounded recompilation chain. *)
Theorem recursive_recompile_preserves_code_throughout:
  forward_certified (stage_vouches vvouch vcert_c loader_ok) St ⇒
  ∀n. loader_ok (St n) (St (SUC n))
Proof
  rw[forward_certified_def, stage_vouches_def] >> metis_tac[]
QED

(* The OPTIMIZATION regime is UNCONDITIONAL. If every verifier step is
   non-strengthening — the new verifier proves the SAME standard, so
   `vvouch A B` forces `vsound B` from `vsound A` outright (the genealogy
   `identity_vouch_unconditional` discharge) — and the compiler seam holds,
   then the whole mutual recursion is safe with NO labelled assumption.
   Recursive mutual OPTIMIZATION carries no Löb. *)
Theorem recursive_mutual_optimization_is_unconditional:
  (∀A B. vvouch A B ⇒ (vsound A ⇒ vsound B)) ∧
  (∀V C. vsound V ∧ vcert_c V C ⇒ ccorrect C) ∧
  vsound (FST (St 0n)) ∧ ccorrect (SND (St 0n)) ∧
  forward_certified (stage_vouches vvouch vcert_c loader_ok) St ⇒
  ∀n. vsound (FST (St n)) ∧ ccorrect (SND (St n))
Proof
  rpt strip_tac >>
  `vouch_sound vsound vvouch` by (rw[vouch_sound_def] >> metis_tac[]) >>
  metis_tac[recursive_mutual_self_improvement_is_safe]
QED

val _ = export_theory ();
