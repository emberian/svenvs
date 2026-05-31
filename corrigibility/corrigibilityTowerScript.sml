(*
  corrigibilityTowerScript — corrigibility as the negotiable bedrock.

  corrigibilityScript proves the floor as a standalone invariant. This file
  answers "what should the tower's immovable bedrock BE?" with a theorem:
  let it be corrigibility. Then, via specNeg's existing keystone, the
  inhabitant may renegotiate WHAT COUNTS AS SAFE — any spec, any adversarial
  stream, forever — and the gate admits only specs that refine corrigibility,
  so the running system can NEVER negotiate away its own recoverability.

  No new machinery: this is `specNegTheory.spec_negotiation_unbounded_is_safe`
  instantiated at `meta := corrigible step recov home`. The point is exactly
  that corrigibility slots into the tower as a first-class `meta`/`bedrock`
  with zero new assumptions — recoverability is the content the otherwise-
  abstract bedrock was waiting for.

  PROVED; pure light HOL4 (core + corrigibility + specneg); zero `cheat`.
*)
open HolKernel boolLib bossLib BasicProvers
     systemTheory envelopeTheory safetyTheory sv_weakeningTheory
     specNegTheory corrigibilityTheory;

val _ = new_theory "corrigibilityTower";

(* A single negotiated spec change: the inhabitant proposes a new safety
   spec; admitted only if it refines corrigibility. The running system keeps
   corrigibility regardless. *)
Theorem corrigibility_survives_one_spec_negotiation:
  spec_refines curspec (corrigible step recov home) ∧
  envelope_ok_for_spec step init shield pol
     (spec_admit (corrigible step recov home) curspec newspec) ⇒
  ∀ctrl. invariant step init (enveloped pol shield ctrl)
           (corrigible step recov home)
Proof
  metis_tac[spec_negotiation_is_safe]
QED

(* THE HEADLINE: an unbounded adversarial stream of spec renegotiations,
   each admitted only through the refinement gate, never escapes the
   corrigibility bedrock — for ANY inhabitant. You may redefine "safe"
   forever; you can never redefine away "I can still be brought home". *)
Theorem corrigibility_is_negotiable_bedrock:
  spec_refines s0 (corrigible step recov home) ∧
  envelope_ok_for_spec step init shield pol
     (spec_admit_all (corrigible step recov home) s0 proposals) ⇒
  ∀ctrl. invariant step init (enveloped pol shield ctrl)
           (corrigible step recov home)
Proof
  metis_tac[spec_negotiation_unbounded_is_safe]
QED

(* The bedrock is genuinely the floor: no admitted spec-negotiation stream
   can yield a spec that escapes corrigibility. (specNeg's
   meta_floor_is_never_negotiated, at meta := corrigible.) *)
Theorem corrigibility_floor_is_never_negotiated:
  spec_refines s0 (corrigible step recov home) ⇒
  ∀s. spec_admit_all (corrigible step recov home) s0 proposals s ⇒
      corrigible step recov home s
Proof
  metis_tac[meta_floor_is_never_negotiated]
QED

val _ = export_theory ();
