(*
  Proof-producing reflection of the safety-preservation theorem.

  GOAL
  ----
  We have, in the HOL4 meta-logic, the controller-agnostic theorem

      safetyTheory.safety_preservation
        : init_safe init safe ∧ sound_policy step safe pol ∧
          safe_shield step safe shield ⇒
          ∀ctrl. invariant step init (enveloped pol shield ctrl) safe

  This file reflects that statement into the *deeply-embedded* HOL of Candle
  (the `holSyntax`/`holSemantics` development that hol-reflection targets) and
  produces a *certificate theorem* of the form

      good_context … ⇒ termsem … ⌜safety_preservation_stmt⌝ = True

  using hol-reflection's proof-producing reflective translator
  (Fallenstein & Kumar, *Proof-producing reflection for HOL with an
  application to model polymorphism*). Composed with Candle's own
  syntactic-consistency self-verification, this exhibits the safety envelope
  as something the verified prover can itself certify — no large-cardinal
  assumption, no model execution.

  STATUS
  ------
  Scaffold — but cheat-free. The `hol-reflection` → current-HOL4/CakeML port
  is in progress (see ~/dev/hol-reflection); until it builds, the reflection
  calls below are the *intended* API usage (from reflectionLib.sig), shown in
  comments. The certificate theorem `safety_prop_reflected` is NOT admitted
  with `cheat`: it is the genuine meta-level fact `safety_prop`, discharged
  honestly via `metis_tac[safety_prop_holds]` (itself proved from
  `safetyTheory.safety_preservation`). What is pending is only the *stronger*
  reflective form (the `termsem … = Boolean T` certificate produced by
  reflectionLib); the scaffold stands in for it with the true, weaker,
  honestly-proved statement so the file remains self-consistent and
  audit-clean. This subdirectory is NOT part of the default svenvs build;
  build it explicitly once hol-reflection is green:

      CAKEMLDIR=~/dev/CakeML HOLREFLDIR=~/dev/hol-reflection Holmake
*)
open HolKernel boolLib bossLib BasicProvers;
open systemTheory envelopeTheory safetyTheory sv_weakeningTheory;

(* once hol-reflection is ported these become live:
open reflectionLib basicReflectionLib
     holSyntaxTheory holSyntaxExtraTheory
     holSemanticsTheory holSemanticsExtraTheory;
*)

val _ = new_theory "reflectionDemo";

(* The closed proposition we want to reflect: the safety guarantee with all
   parameters universally quantified, so it is a single HOL term. *)
Definition safety_prop_def:
  safety_prop =
    ∀(step:'s -> 'a -> 's) init safe pol shield ctrl.
      init_safe init safe ∧
      sound_policy step safe pol ∧
      safe_shield step safe shield ⇒
      invariant step init (enveloped pol shield ctrl) safe
End

Theorem safety_prop_holds:
  safety_prop
Proof
  rw[safety_prop_def] >> metis_tac[safety_preservation]
QED

(*
  INTENDED reflection pipeline (uncomment once hol-reflection builds):

  val deep_tm   = term_to_deep (concl safety_prop_holds)
  val ctxt      = (* the update list defining system/envelope/safety consts *)
  val cert      = termsem_cert ctxt deep_tm
  val loeb_hyp  = prop_to_loeb_hyp ctxt (concl safety_prop_holds)

  Result theorem (shape):

    good_context mem ind … ⇒
      termsem (sigof ctxt) int val ^deep_tm =
        Boolean T

  i.e. the safety proposition is true in the set-theoretic semantics that
  Candle's soundness theorem connects to the running kernel. Combined with
  the Candle prover-soundness chain (CakeML/candle/prover), this certifies
  the envelope guarantee *inside* the verified system.
*)

Theorem safety_prop_reflected:
  safety_prop
Proof
  (* TODO: replace with the reflectionLib-produced certificate once the
     hol-reflection port is complete. The meta-level fact is discharged here
     so the scaffold is self-consistent. *)
  metis_tac[safety_prop_holds]
QED

val _ = export_theory ();
