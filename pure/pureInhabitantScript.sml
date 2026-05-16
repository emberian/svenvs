(*
  PureLang as the svenvs inhabitant — the ABSTRACT integration point.

  See DESIGN.md. This file deliberately builds in seconds with NO PureCake /
  CakeML / hol-reflection dependency: PureLang enters as an *abstract
  signature*, so the integration is exercised without the heavy artifacts.

    - [pureprog]      : an opaque type of "PureLang programs". In the real
                        (gated) version this is instantiated with
                        pure_exp$exp / pure_cexp$cexp.
    - [denote]        : the program's denotation as an svenvs controller
                        (a :'s -> 'a selector). In the real version this is
                        the world-coupling over pure_semantics$itree_of
                        (DESIGN.md §3). It is abstract here.
    - [safe_program]  : a well-formedness predicate standing in for the
                        pure_semantics side-conditions
                        safe_itree ∧ closed ∧ letrecs_distinct (DESIGN.md §4),
                        i.e. exactly the hypotheses of
                        pure_to_cakeProof$pure_to_cake_correct.

  The headline theorem reuses the GENERIC svenvs core verbatim — it is
  [safety$safety_preservation] instantiated at  ctrl := denote p . Nothing
  is reproved; this is the whole content of the opaque-controller design:
  ANY PureLang inhabitant is enveloped-safe, for free.

  We also reuse [upgrade$self_improvement_is_safe] to show that a PureLang
  inhabitant proposing an unbounded stream of self-improvements to its own
  policy can never make the Place unsafe.

  Cheat-free. No `cheat` tactic. Builds with INCLUDES=.. (svenvs core).
*)
open HolKernel boolLib bossLib BasicProvers
     systemTheory envelopeTheory safetyTheory
     sv_weakeningTheory upgradeTheory;

val _ = new_theory "pureInhabitant";

(* ------------------------------------------------------------------ *)
(*  Abstract PureLang signature (the real defs from ~/dev/pure plug in *)
(*  here in the gated heavy version; see DESIGN.md §6).                *)
(* ------------------------------------------------------------------ *)

(* An opaque "PureLang program". Real: pure_exp$exp / pure_cexp$cexp. *)
val _ = new_type ("pureprog", 0);

(* The program's denotation as an svenvs controller. Real: the world
   coupling over pure_semantics$itree_of (DESIGN.md §3). Total, opaque. *)
val _ = new_constant ("denote", “:pureprog -> ('s -> 'a)”);

(* Well-formedness of a program: the abstract stand-in for
   safe_itree (itree_of (exp_of p)) ∧ closed (exp_of p) ∧
   letrecs_distinct (exp_of p) — i.e. EXACTLY the hypotheses that
   pure_to_cakeProof$pure_to_cake_correct needs (DESIGN.md §4,§5). *)
val _ = new_constant ("safe_program", “:pureprog -> bool”);

(* ------------------------------------------------------------------ *)
(*  Integration theorem 1: any PureLang inhabitant is enveloped-safe.  *)
(*  This is safety$safety_preservation instantiated at the PureLang    *)
(*  denotation — the generic core is REUSED, not reproved.             *)
(* ------------------------------------------------------------------ *)

Theorem pure_inhabitant_safe:
  init_safe init safe ∧
  sound_policy step safe pol ∧
  safe_shield step safe shield ⇒
  ∀p. invariant step init (enveloped pol shield (denote p)) safe
Proof
  rpt strip_tac >>
  irule safety_preservation >>
  metis_tac[]
QED

(* Spelled-out corollary: every reachable state of the Place inhabited by
   ANY PureLang program is safe. *)
Theorem pure_inhabitant_states_safe:
  init_safe init safe ∧
  sound_policy step safe pol ∧
  safe_shield step safe shield ∧
  reach step init (enveloped pol shield (denote p)) s ⇒
  safe s
Proof
  metis_tac[pure_inhabitant_safe, invariant_def]
QED

(* ------------------------------------------------------------------ *)
(*  Integration theorem 2: a PureLang inhabitant that proposes an      *)
(*  unbounded stream of self-improvements to its own policy can never  *)
(*  make the Place unsafe. Reuses upgrade$self_improvement_is_safe.    *)
(* ------------------------------------------------------------------ *)

Theorem pure_inhabitant_self_improvement_safe:
  init_safe init safe ∧
  safe_shield step safe shield ∧
  sound_policy step safe p0 ⇒
  ∀proposals p.
    invariant step init
      (enveloped (admit_all step safe p0 proposals) shield (denote p)) safe
Proof
  rpt strip_tac >>
  irule self_improvement_is_safe >>
  metis_tac[]
QED

(* ------------------------------------------------------------------ *)
(*  The well-formedness predicate is not load-bearing for SAFETY (the  *)
(*  envelope carries that for an arbitrary controller). It is the      *)
(*  obligation that, in the heavy version, ALSO licenses compiling the *)
(*  program to CakeML via pure_to_cakeProof$pure_to_cake_correct       *)
(*  (DESIGN.md §4). We record it as an explicit, abstractly-stated      *)
(*  hypothesis so the integration point is visible in the theorem      *)
(*  statement; the safety conclusion holds regardless of it.           *)
(* ------------------------------------------------------------------ *)

Theorem wellformed_pure_inhabitant_safe:
  safe_program p ∧
  init_safe init safe ∧
  sound_policy step safe pol ∧
  safe_shield step safe shield ⇒
  invariant step init (enveloped pol shield (denote p)) safe
Proof
  rpt strip_tac >>
  irule pure_inhabitant_safe >>
  metis_tac[]
QED

val _ = export_theory ();
