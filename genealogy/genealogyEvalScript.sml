(*
  genealogyEval - a small CONCRETE forward-certified succession, run in
  the logic. Pure light HOL4 (arithmeticTheory only). genealogyScript is
  the general principle; this instantiates it on a concrete num-indexed
  succession so "the root is a ratchet, not a rock" is computed, not only
  asserted - matching the project's concrete-episode discipline.

  Judges are version ids (num). gj_sound j : version j is within the
  trusted regime (j <= 5). gj_vouches a b : a certified successor b is
  adopted iff it too lies in the trusted regime. The genesis is version 0;
  the succession gj_succ n = MIN n 5 climbs and then holds at the trusted
  ceiling. Everything is closed by computation / arithmetic, reusing
  genealogyTheory verbatim.
*)
open HolKernel boolLib bossLib BasicProvers arithmeticTheory genealogyTheory;

val _ = new_theory "genealogyEval";

Definition gj_sound_def:
  gj_sound (j:num) ⇔ j ≤ 5
End

Definition gj_vouches_def:
  gj_vouches (a:num) (b:num) ⇔ b ≤ 5
End

Definition gj_succ_def:
  gj_succ (n:num) = MIN n 5
End

(* The forward-step seam is a THEOREM here (the eval discipline): a sound
   judge that vouches for b implies b sound, by construction. *)
Theorem gj_vouch_sound:
  vouch_sound gj_sound gj_vouches
Proof
  rw[vouch_sound_def, gj_sound_def, gj_vouches_def]
QED

(* Genesis version 0 is sound. *)
Theorem gj_genesis_sound:
  gj_sound (gj_succ 0)
Proof
  rw[gj_sound_def, gj_succ_def, MIN_DEF]
QED

(* The succession is forward-certified: each version certifies the next. *)
Theorem gj_forward_certified:
  forward_certified gj_vouches gj_succ
Proof
  rw[forward_certified_def, gj_vouches_def, gj_succ_def, MIN_DEF]
QED

(* HENCE, by genealogy_sound: EVERY version in the unbounded succession is
   sound - only the genesis soundness was assumed; no per-version
   assumption. "Frozen forever" -> "sound once, certified forward". *)
Theorem gj_all_versions_sound:
  ∀n. gj_sound (gj_succ n)
Proof
  metis_tac[genealogy_sound, gj_vouch_sound, gj_genesis_sound,
            gj_forward_certified]
QED

(* The non-strengthening (re-engineered, same regime) succession is
   UNCONDITIONAL: ANY succession from a sound genesis under the identity
   vouch stays sound, with no assumption at all - genealogyScript's
   nonstrengthening_genealogy_unconditional specialised to gj_sound. *)
Theorem gj_identity_succession_unconditional:
  ∀J. gj_sound (J 0n) ∧ forward_certified (λA B. B = A) J ⇒
      ∀n. gj_sound (J n)
Proof
  metis_tac[nonstrengthening_genealogy_unconditional]
QED

(* Concrete sanity, computed: the succession climbs to the trusted ceiling
   and holds; a far-future version is still sound. *)
Theorem gj_succession_runs:
  gj_succ 0 = 0 ∧ gj_succ 3 = 3 ∧ gj_succ 10 = 5 ∧
  gj_sound (gj_succ 100)
Proof
  rw[gj_succ_def, gj_sound_def, MIN_DEF]
QED

val _ = export_theory ();
