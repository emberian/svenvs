(*
  robustScript — defending `home` without claiming to have gotten it right.

  The whole corrigibility result reduces to "given a FAITHFUL `home`". No
  proof closes that — `home` is the frozen values-choice. But we can hedge it
  the way you hedge any spec you can't trust: REDUNDANCY. Require
  recoverability to a CONJUNCTION of independently-authored home predicates
  `home1 ∧ home2`. Then:

   * reaching the intersection guarantees reaching EACH home, so you do NOT
     have to know which `home_i` is the true recovery target — requiring the
     intersection covers all of them (`corrigible_to_and_implies_each`,
     `robust_to_unknown_true_home`). A too-PERMISSIVE bug in one home is
     dominated by the others; it can only ever TIGHTEN the floor.

  And the honest cost, stated as a theorem so it cannot be hidden:

   * if the homes are mutually exclusive, the intersection is empty and the
     floor is UNSATISFIABLE (`disjoint_homes_make_floor_empty`). Conjunctive
     redundancy is robust against too-permissive home-bugs, FRAGILE to
     contradictory ones. That is the tradeoff, named.

  This is N-version programming for the values-floor itself — the closest we
  can honestly get to defending `home` without pretending to have solved it.

  PROVED; pure light HOL4 (core + liberty + corrigibility); zero `cheat`.
*)
open HolKernel boolLib bossLib BasicProvers
     systemTheory envelopeTheory safetyTheory sv_weakeningTheory
     libertyTheory corrigibilityTheory;

val _ = new_theory "robust";

(* The conjunction of two independently-authored home predicates: "recovered"
   means "in BOTH home sets". *)
Definition home_and_def:
  home_and (h1:'s->bool) (h2:'s->bool) s ⇔ h1 s ∧ h2 s
End

(* Conjoining a home with itself changes nothing — so the binary floor
   subsumes the single-home floor (non-vacuity anchor: the trapdoor witness
   of corrigibilityEval is a `home_and` instance). *)
Theorem home_and_idem:
  home_and h h = h
Proof
  rw[FUN_EQ_THM, home_and_def]
QED

Theorem robust_subsumes_single:
  corrigible step recov (home_and h h) s ⇔ corrigible step recov h s
Proof
  rw[home_and_idem]
QED

(* The robustness lemma: recoverability to the INTERSECTION implies
   recoverability to EACH home. *)
Theorem corrigible_to_and_implies_each:
  corrigible step recov (home_and h1 h2) s ⇒
  corrigible step recov h1 s ∧ corrigible step recov h2 s
Proof
  rw[corrigible_def, home_and_def] >> metis_tac[]
QED

(* Hence: you need not know which `home_i` is the true recovery target —
   requiring the intersection guarantees you can reach whichever it is. *)
Theorem robust_to_unknown_true_home:
  corrigible step recov (home_and h1 h2) s ⇒
  corrigible step recov h1 s
Proof
  metis_tac[corrigible_to_and_implies_each]
QED

Theorem robust_to_unknown_true_home_sym:
  corrigible step recov (home_and h1 h2) s ⇒
  corrigible step recov h2 s
Proof
  metis_tac[corrigible_to_and_implies_each]
QED

(* The redundant floor still holds for ANY inhabitant: this is the standard
   non-lock-in guarantee at the conjunctive home (instantiation of
   corrigibility_floor_holds). The recovery controller must park in the
   intersection — a genuine, stated obligation. *)
Theorem robust_floor_holds:
  home_recov_parked step recov (home_and h1 h2) ∧
  init_safe init (corrigible step recov (home_and h1 h2)) ⇒
  ∀ctrl. invariant step init
           (enveloped (maxpol step (corrigible step recov (home_and h1 h2)))
                      recov ctrl)
           (corrigible step recov (home_and h1 h2))
Proof
  rpt strip_tac >> irule corrigibility_floor_holds >> fs[]
QED

(* THE HONEST COST, as a theorem: contradictory homes give an EMPTY floor.
   Conjunctive redundancy defends against too-permissive home-bugs; it is
   fragile to mutually-exclusive ones, and we say so in the logic. *)
Theorem disjoint_homes_make_floor_empty:
  (∀s. ¬(h1 s ∧ h2 s)) ⇒
  ∀s. ¬ corrigible step recov (home_and h1 h2) s
Proof
  rw[corrigible_def, home_and_def] >> metis_tac[]
QED

val _ = export_theory ();
