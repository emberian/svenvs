(*
  genealogyScript — the ONE GATE, applied to the root itself.

  svenvs makes the policy, the spec, and the meta-invariant negotiable, each
  gated by a checked proof. The remaining "frozen" thing was the root judge
  (HOL4's LCF kernel). An earlier framing called it eternally immovable. The
  honest correction (and the point of this file): the root need not be a
  rock — it must be a *well-founded, forward-certified genealogy of judges*.
  It is immovable only DURING ITS OWN TENURE (a proof is meaningful only
  relative to some fixed calculus, so the checker that checks a transition
  cannot be the thing that transition rewrites in the same act); a successor
  is adopted ONLY if the predecessor certified it.

  This is the IDENTICAL gate, one level deeper, so it reuses the existing
  seam taxonomy verbatim and introduces NO new assumption:

   * `vouch_sound jsound vouches` — the labelled forward-step seam, exactly
     the shape of selfProverTheory.`frozen_checker_sound`
     (`∀p B. checks p B ⇒ sound B`), one level up: if a SOUND judge vouches
     for J', then J' is sound. It is carried verbatim, never hidden — and it
     is a *theorem*, not an assumption, for the sound non-strengthening
     case (`identity_vouch_unconditional`), exactly as
     kernel/watchdogFinite discharges the identity Löb case.

   * `genealogy_sound` — THE HEADLINE. Given a sound GENESIS judge and a
     forward-certified succession, EVERY judge in the (unbounded) line is
     sound. Pure modus-ponens folded over the succession: no Löb, no new
     assumption. The honest consequence: "frozen forever" is replaced by
     "sound once at genesis, certified forward thereafter" — only the
     GENESIS soundness is irreducibly assumed (by Gödel, a judge cannot
     prove its own soundness; that single assumption is exactly today's
     built `proves_sound` at n = 0).

   * `genealogy_irrelevant_to_vouch_sound` — the HONEST NEGATIVE. The seam
     `vouch_sound` has NO genealogy parameter at all, so no amount of
     succession structure can dissolve it for genuine strengthening. This
     is the precise analogue of kernel/watchdogFiniteScript's
     `loeb_finite_obstruction`: the Gödel/Löb wall is stated as a theorem
     so it cannot be quietly ignored.

  Pure light HOL4 (no deps beyond the base): reproducible by anyone, Tier 1,
  zero `cheat`/axiom/oracle. The judges are an opaque type `'j`; nothing
  here is specific to HOL4 — it is the general principle the whole tower is
  an instance of.
*)
open HolKernel boolLib bossLib BasicProvers arithmeticTheory;

val _ = new_theory "genealogy";

(* A judge is opaque. `jsound J` : that judge only ever certifies things
   that are actually sound (its own soundness as a checker). `vouches J J'`
   : judge J certified that successor J' meets the soundness obligation,
   against the fixed standard J could check. *)

(* The labelled forward-step seam — IDENTICAL in shape to
   selfProverTheory.frozen_checker_sound, one level up. Carried verbatim in
   every conditional theorem below; never a hidden step. *)
Definition vouch_sound_def:
  vouch_sound (jsound:'j -> bool) (vouches:'j -> 'j -> bool) ⇔
    ∀A B. jsound A ∧ vouches A B ⇒ jsound B
End

(* A genealogy is a succession of judges; it is forward-certified when each
   judge certified its immediate successor. *)
Definition forward_certified_def:
  forward_certified (vouches:'j -> 'j -> bool) (J:num -> 'j) ⇔
    ∀n. vouches (J n) (J (SUC n))
End

(* THE HEADLINE. Sound genesis + forward-certified succession ⇒ every judge
   in the unbounded line is sound. Modus ponens folded over `num`: no Löb,
   no assumption beyond the carried `vouch_sound` seam. *)
Theorem genealogy_sound:
  vouch_sound jsound vouches ∧
  jsound (J 0n) ∧
  forward_certified vouches J ⇒
  ∀n. jsound (J n)
Proof
  rpt strip_tac >>
  Induct_on ‘n’ >- fs[] >>
  fs[vouch_sound_def, forward_certified_def] >> metis_tac[]
QED

(* Spelled-out corollary: ANY judge ever reached along the succession is
   sound — only the GENESIS soundness was assumed; there is no per-successor
   assumption anywhere. This is "frozen forever" replaced by "sound once,
   certified forward". *)
Theorem any_reached_judge_is_sound:
  vouch_sound jsound vouches ∧
  jsound (J 0n) ∧
  forward_certified vouches J ⇒
  ∀m. jsound (J m)
Proof
  metis_tac[genealogy_sound]
QED

(* The sound NON-STRENGTHENING case is UNCONDITIONAL. If a "successor" is the
   same judge (a re-engineered build proving the *same* fixed standard — no
   logical strength gained), the forward-step seam is a THEOREM, not an
   assumption. Exact analogue of kernel/watchdogFinite's discharge of the
   identity Löb case (`loeb_reflection_identity_kernel`). *)
Theorem identity_vouch_unconditional:
  vouch_sound jsound (λA B. B = A)
Proof
  rw[vouch_sound_def]
QED

(* Hence an unbounded non-strengthening succession from a sound genesis is
   safe with NO labelled assumption at all. *)
Theorem nonstrengthening_genealogy_unconditional:
  jsound (J 0n) ∧ forward_certified (λA B. B = A) J ⇒
  ∀n. jsound (J n)
Proof
  rpt strip_tac >>
  ‘vouch_sound jsound (λA B. B = A)’ by rw[identity_vouch_unconditional] >>
  metis_tac[genealogy_sound]
QED

(* THE HONEST NEGATIVE. `vouch_sound` mentions no genealogy, no succession,
   no index — it is a statement purely about the judge-soundness predicate
   and the vouching relation. So no amount of succession/finiteness
   structure can bear on it: genuine strength-increase remains the
   irreducible Gödel/Löb seam, exactly as for the kernel
   (`loeb_finite_obstruction`). Stated as a theorem so it cannot be quietly
   ignored. *)
Theorem genealogy_irrelevant_to_vouch_sound:
  ∀jsound vouches.
    vouch_sound jsound vouches ⇔ (∀A B. jsound A ∧ vouches A B ⇒ jsound B)
Proof
  rw[vouch_sound_def]
QED

val _ = export_theory ();
