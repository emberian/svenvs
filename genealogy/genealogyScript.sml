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

   * `genealogy_irrelevant_to_vouch_sound` — the HONEST NEGATIVE. Without
     `vouch_sound`, a forward-certified genealogy from a sound genesis can
     go unsound at step 1: succession structure (certification at every
     step, an unbounded well-founded index) cannot stand in for the seam.
     `vouch_sound_is_necessary` sharpens it: for any vouching relation
     that always offers some successor, `vouch_sound` is EQUIVALENT to
     "every forward-certified genealogy from a sound genesis stays sound",
     so `genealogy_sound`'s seam hypothesis cannot be weakened at all. The
     analogue of kernel/watchdogFiniteScript's `loeb_finite_obstruction`:
     the wall is stated as a theorem so it cannot be quietly ignored.

  Pure light HOL4 (no deps beyond the base): reproducible by anyone, Tier 1.
  The judges are an opaque type `'j`; nothing
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

(* THE HONEST NEGATIVE. Drop the seam and the rest of the structure buys
   nothing: over judges = num, with only judge 0 sound and each judge
   vouching for its numeric successor, the genealogy J = I is forward-
   certified at EVERY step and starts from a sound genesis, yet judge 1 is
   already unsound. So certification-at-every-step plus a sound genesis
   (plus an unbounded, well-founded index) does not imply soundness of the
   line; the only thing that does is `vouch_sound`, which mentions no
   genealogy at all — genuine strength-increase remains the Gödel/Löb seam
   (`loeb_finite_obstruction`). *)
Theorem genealogy_irrelevant_to_vouch_sound:
  ∃(jsound:num -> bool) (vouches:num -> num -> bool) (J:num -> num).
    forward_certified vouches J ∧ jsound (J 0) ∧
    ¬vouch_sound jsound vouches ∧ ¬(∀n. jsound (J n))
Proof
  qexistsl_tac [‘λn. n = 0’, ‘λA B. B = A + 1’, ‘I’] >>
  rw[forward_certified_def, vouch_sound_def, arithmeticTheory.ADD1] >>
  qexists_tac ‘1’ >> rw[]
QED

(* The sharp form: for any vouching relation that always offers SOME
   successor (a judge can always name a candidate, as the running loop
   does), `vouch_sound` is not merely sufficient for `genealogy_sound`'s
   conclusion but NECESSARY. A single sound judge vouching for an unsound
   one is extended, through the offered successors, to a forward-certified
   genealogy from a sound genesis that is unsound at step 1. So the seam
   hypothesis of `genealogy_sound` admits no weakening. *)
Theorem vouch_sound_is_necessary:
  (∀A. ∃B. vouches A B) ⇒
  (vouch_sound jsound vouches ⇔
   ∀J. jsound (J 0n) ∧ forward_certified vouches J ⇒ ∀n. jsound (J n))
Proof
  strip_tac >> eq_tac
  >- metis_tac[genealogy_sound] >>
  rw[vouch_sound_def] >> CCONTR_TAC >>
  ‘∃f. ∀X. vouches X (f X)’ by (simp[GSYM SKOLEM_THM] >> metis_tac[]) >>
  qabbrev_tac ‘J = λn. if n = 0 then A else FUNPOW f (n - 1) B’ >>
  ‘forward_certified vouches J’
    by (rw[forward_certified_def, Abbr ‘J’] >>
        Cases_on ‘n’ >> simp[arithmeticTheory.FUNPOW_SUC]) >>
  ‘jsound (J 0) ∧ ¬jsound (J 1)’ by simp[Abbr ‘J’] >>
  metis_tac[]
QED

val _ = export_theory ();
