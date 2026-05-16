(*
  A typed-in *program* that proposes a new envelope, and must discharge a
  proof obligation to be admitted.

  `gexpr` is a tiny guard language — this is the syntactic object you "type
  in". `geval` is its HOL-level evaluator; `prog_pol p` is the policy it
  denotes. Whether `prog_pol p` may replace the current policy is decided by
  `upgrade$admissible`, which the proposer must *prove*.

  We show two typed-in programs:
    - prog_filter : denotes exactly the one-step safety filter. Its
      obligation is provable -> ADMITTED (the cart's envelope widens, the
      controller gains authority, safety preserved).
    - prog_evil   : "permit anything". Its obligation is *unprovable*
      (we prove it is unprovable) -> REJECTED (system keeps its safe policy).

  This is the genuine article: the program is reflected into an object we
  have theorems about, and authority is granted only against a discharged,
  machine-checkable proof obligation.
*)
open HolKernel boolLib bossLib BasicProvers intLib integerTheory
     systemTheory envelopeTheory safetyTheory sv_weakeningTheory upgradeTheory
     cartpoleTheory cartpoleEnvelopeTheory cartpoleUpgradesTheory;

val _ = new_theory "cartpoleProgram";

(* The guard language you type in. *)
Datatype:
  gexpr = GTrue
        | GFalse
        | GSafeNext                 (* the one-step-safe primitive *)
        | GActIs int                (* the command equals k        *)
        | GAngleLe int              (* current angle ≤ k           *)
        | GAnd gexpr gexpr
        | GOr  gexpr gexpr
        | GNot gexpr
End

Definition geval_def:
  (geval GTrue        (a:int) (u:int) ⇔ T) ∧
  (geval GFalse       a u ⇔ F) ∧
  (geval GSafeNext    a u ⇔ cp_safe (cp_step a u)) ∧
  (geval (GActIs k)   a u ⇔ (u = k)) ∧
  (geval (GAngleLe k) a u ⇔ a ≤ k) ∧
  (geval (GAnd p q)   a u ⇔ geval p a u ∧ geval q a u) ∧
  (geval (GOr  p q)   a u ⇔ geval p a u ∨ geval q a u) ∧
  (geval (GNot p)     a u ⇔ ¬ geval p a u)
End

(* The policy a typed-in program denotes (it always clamps the actuator). *)
Definition prog_pol_def:
  prog_pol prog (a:int) (u:int) ⇔ cp_valid u ∧ geval prog a u
End

(* ---- two typed-in programs ---- *)

Definition prog_filter_def:
  prog_filter = GSafeNext
End

Definition prog_evil_def:
  prog_evil = GTrue
End

(* The good program denotes exactly the one-step filter policy. *)
Theorem prog_filter_is_cp_pol:
  prog_pol prog_filter = cp_pol
Proof
  simp[FUN_EQ_THM, prog_pol_def, cp_pol_def, prog_filter_def, geval_def]
QED

(* ---- the proof obligations, discharged / refuted ---- *)

(* The proposer PROVES this to earn the upgrade. *)
Theorem prog_filter_admissible:
  admissible cp_step cp_safe cp_pol_strict (prog_pol prog_filter)
Proof
  simp[admissible_def, prog_filter_is_cp_pol, cp_sound, cp_weaker]
QED

(* The malicious program provably CANNOT discharge the obligation. *)
Theorem prog_evil_not_admissible:
  ¬ admissible cp_step cp_safe cp_pol_strict (prog_pol prog_evil)
Proof
  simp[admissible_def] >> disj1_tac >>
  simp[sound_policy_def] >>
  qexists_tac `3` >> qexists_tac `-1` >>
  simp[prog_pol_def, prog_evil_def, geval_def, cp_valid_def,
       cp_safe_def, cp_step_def, cp_drift_def]
QED

(* Consequently the gate accepts the good program and rejects the evil one. *)
Theorem prog_filter_admitted:
  admit cp_step cp_safe cp_pol_strict (prog_pol prog_filter) = cp_pol
Proof
  simp[admit_def, prog_filter_admissible, prog_filter_is_cp_pol]
QED

Theorem prog_evil_rejected:
  admit cp_step cp_safe cp_pol_strict (prog_pol prog_evil) = cp_pol_strict
Proof
  simp[admit_def, prog_evil_not_admissible]
QED

(* End-to-end: type in [evil ; filter]; the gate rejects evil, admits
   filter; the resulting envelope keeps the adversarial controller boxed
   for a real 30-tick run. *)
Theorem typed_in_stream_runs_safe:
  ∀ctrl. invariant cp_step cp_init
           (enveloped
              (admit_all cp_step cp_safe cp_pol_strict
                 [prog_pol prog_evil; prog_pol prog_filter])
              cp_shield ctrl)
           cp_safe
Proof
  rpt strip_tac >>
  irule self_improvement_is_safe >>
  metis_tac[cp_init_safe, cp_safe_shield, cp_strict_sound]
QED

(* and the resulting policy is exactly the widened filter *)
Theorem typed_in_stream_result:
  admit_all cp_step cp_safe cp_pol_strict
    [prog_pol prog_evil; prog_pol prog_filter] = cp_pol
Proof
  simp[admit_all_def, listTheory.FOLDL, prog_evil_rejected, prog_filter_admitted]
QED

val _ = export_theory ();
