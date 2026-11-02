(*
  specNeg — Spec Negotiation and Constitutional Meta-Amendment over an
  Immovable Bedrock, driven by `certifierTheory.cgate` / `cgate_run`.

  Unifies spec-level negotiation (`specNeg`) and meta-level amendment
  (`amendment`) over both deterministic (`step`) and relational/adversarial
  (`stepr`) plants:
    1. `spec_refines` preorder and the selector-generic transport keystones
       `invariant_transports_to_meta` (deterministic) and
       `invariantr_transports_to_meta` (relational/demonic).
    2. Non-vacuous spec admissibility (`genuine_spec_change`,
       `spec_admissible` without redundant duplicate conjuncts) and the
       operational `cgate` / `cgate_run` spec gate (`spec_gate`,
       `spec_admit`, `spec_admit_all`), plus `spec_gate_keeps_refining_iff`.
    3. Multi-step spec negotiation (`spec_negotiation_unbounded_is_safe`,
       `meta_floor_is_never_negotiated`).
    4. Constitutional meta-amendment (`amended_meta`, `bedrock_is_eternal`,
       `meta_amendment_safe`, `amendment_subsumes_fixed_meta`).

  Pure light HOL4; zero `cheat`, zero axioms, no Löb.
*)
open HolKernel boolLib bossLib BasicProvers listTheory
     systemTheory envelopeTheory safetyTheory sv_weakeningTheory
     upgradeTheory certifierTheory relSystemTheory relEnvelopeTheory;

val _ = new_theory "specNeg";

(* ===================================================================== *)
(* 1. Spec Refinement & Selector-Generic Transport Keystones             *)
(* ===================================================================== *)

Type spec = “:'s -> bool”;

Definition spec_refines_def:
  spec_refines (newspec:'s spec) (meta:'s spec) <=>
    !s. newspec s ==> meta s
End

Theorem spec_refines_refl:
  spec_refines meta meta
Proof
  rw[spec_refines_def]
QED

Theorem spec_refines_trans:
  spec_refines a b /\ spec_refines b c ==> spec_refines a c
Proof
  rw[spec_refines_def] >> metis_tac[]
QED

Theorem invariant_transports_to_meta:
  invariant step init sel spec /\ spec_refines spec meta ==>
  invariant step init sel meta
Proof
  rw[invariant_def, spec_refines_def] >> metis_tac[]
QED

Theorem invariantr_transports_to_meta:
  invariantr stepr init sel spec /\ spec_refines spec meta ==>
  invariantr stepr init sel meta
Proof
  rw[invariantr_def, spec_refines_def] >> metis_tac[]
QED

(* ===================================================================== *)
(* 2. Non-Vacuous Spec Admissibility & Operational `cgate`               *)
(* ===================================================================== *)

Definition genuine_spec_change_def:
  genuine_spec_change (newspec:'s spec) (meta:'s spec) <=>
    spec_refines newspec meta /\ (newspec <> meta)
End

Theorem genuine_spec_change_not_meta:
  genuine_spec_change newspec meta ==> newspec <> meta
Proof
  rw[genuine_spec_change_def]
QED

Definition spec_admissible_def:
  spec_admissible (meta:'s spec) (newspec:'s spec) <=>
    genuine_spec_change newspec meta
End

Definition spec_admit_def:
  spec_admit (meta:'s spec) (curspec:'s spec) (newspec:'s spec) =
    cgate (spec_admissible meta newspec) curspec newspec
End

Theorem spec_admit_keeps_refining:
  spec_refines curspec meta ==>
  spec_refines (spec_admit meta curspec newspec) meta
Proof
  rw[spec_admit_def, cgate_def, spec_admissible_def, genuine_spec_change_def]
QED

(* Operational spec gate parameterized by an arbitrary certificate `cert`:
   keeping `spec_refines _ meta` across all initial refining specs is
   equivalent to `cert ==> spec_refines newspec meta` (`cgate` iff). *)
Theorem spec_gate_keeps_refining_iff:
  (!curspec. spec_refines curspec meta ==>
             spec_refines (cgate cert curspec newspec) meta) <=>
  (cert ==> spec_refines newspec meta)
Proof
  rw[cgate_def, EQ_IMP_THM]
  >- (first_x_assum (qspec_then `meta` mp_tac) >> rw[spec_refines_refl])
  >- rw[]
QED

Definition spec_admit_all_def:
  spec_admit_all (meta:'s spec) s0 proposals =
    FOLDL (spec_admit meta) s0 proposals
End

Theorem spec_admit_all_keeps_refining:
  !proposals s0.
    spec_refines s0 meta ==>
    spec_refines (spec_admit_all meta s0 proposals) meta
Proof
  Induct >> rw[spec_admit_all_def] >>
  fs[GSYM spec_admit_all_def] >>
  first_x_assum irule >>
  metis_tac[spec_admit_keeps_refining]
QED

(* ===================================================================== *)
(* 3. Spec Negotiation Preserves the Immovable Meta-Invariant            *)
(* ===================================================================== *)

Definition envelope_ok_for_spec_def:
  envelope_ok_for_spec step init shield pol (spec:'s spec) <=>
    init_safe init spec /\
    sound_policy step spec pol /\
    safe_shield step spec shield
End

Theorem envelope_keeps_its_spec:
  envelope_ok_for_spec step init shield pol spec ==>
  !ctrl. invariant step init (enveloped pol shield ctrl) spec
Proof
  rw[envelope_ok_for_spec_def] >>
  irule safety_preservation >> fs[]
QED

Theorem spec_negotiation_is_safe:
  !meta step init shield pol curspec newspec.
    spec_refines curspec meta /\
    envelope_ok_for_spec step init shield pol
        (spec_admit meta curspec newspec) ==>
    !ctrl.
      invariant step init
        (enveloped pol shield ctrl)
        meta
Proof
  rpt strip_tac >>
  `!ctrl. invariant step init (enveloped pol shield ctrl)
            (spec_admit meta curspec newspec)`
    by metis_tac[envelope_keeps_its_spec] >>
  `spec_refines (spec_admit meta curspec newspec) meta`
    by metis_tac[spec_admit_keeps_refining] >>
  metis_tac[invariant_transports_to_meta]
QED

Theorem spec_negotiation_states_meta_safe:
  spec_refines curspec meta /\
  envelope_ok_for_spec step init shield pol
      (spec_admit meta curspec newspec) /\
  reach step init (enveloped pol shield ctrl) s ==>
  meta s
Proof
  metis_tac[spec_negotiation_is_safe, invariant_def]
QED

Theorem spec_negotiation_unbounded_is_safe:
  !meta step init shield pol s0 proposals.
    spec_refines s0 meta /\
    envelope_ok_for_spec step init shield pol
        (spec_admit_all meta s0 proposals) ==>
    !ctrl.
      invariant step init (enveloped pol shield ctrl) meta
Proof
  rpt strip_tac >>
  `!ctrl. invariant step init (enveloped pol shield ctrl)
            (spec_admit_all meta s0 proposals)`
    by metis_tac[envelope_keeps_its_spec] >>
  `spec_refines (spec_admit_all meta s0 proposals) meta`
    by metis_tac[spec_admit_all_keeps_refining] >>
  metis_tac[invariant_transports_to_meta]
QED

Theorem meta_floor_is_never_negotiated:
  !meta s0 proposals.
    spec_refines s0 meta ==>
    !s. (spec_admit_all meta s0 proposals) s ==> meta s
Proof
  rpt strip_tac >>
  `spec_refines (spec_admit_all meta s0 proposals) meta`
    by metis_tac[spec_admit_all_keeps_refining] >>
  fs[spec_refines_def]
QED

Theorem unrefining_spec_proposal_is_inert:
  ~ spec_admissible meta newspec ==>
  spec_admit meta curspec newspec = curspec
Proof
  rw[spec_admit_def, cgate_def]
QED

(* ===================================================================== *)
(* 4. Constitutional Meta-Amendment over an Eternal Bedrock              *)
(* ===================================================================== *)

Definition amended_meta_def:
  amended_meta (bedrock:'s spec) (meta0:'s spec) mproposals =
    spec_admit_all bedrock meta0 mproposals
End

Theorem bedrock_is_eternal:
  spec_refines meta0 bedrock ==>
  !mproposals.
    spec_refines (amended_meta bedrock meta0 mproposals) bedrock
Proof
  rw[amended_meta_def] >> metis_tac[spec_admit_all_keeps_refining]
QED

Theorem meta_amendment_safe:
  spec_refines meta0 bedrock /\
  spec_refines curspec (amended_meta bedrock meta0 mproposals) /\
  envelope_ok_for_spec step init shield pol
     (spec_admit (amended_meta bedrock meta0 mproposals) curspec newspec) ==>
  !ctrl. invariant step init (enveloped pol shield ctrl) bedrock
Proof
  rpt strip_tac >>
  `!ctrl. invariant step init (enveloped pol shield ctrl)
            (amended_meta bedrock meta0 mproposals)`
    by metis_tac[spec_negotiation_is_safe] >>
  `spec_refines (amended_meta bedrock meta0 mproposals) bedrock`
    by metis_tac[bedrock_is_eternal] >>
  metis_tac[invariant_transports_to_meta]
QED

Theorem amendment_subsumes_fixed_meta:
  spec_refines curspec meta /\
  envelope_ok_for_spec step init shield pol
     (spec_admit meta curspec newspec) ==>
  !ctrl. invariant step init (enveloped pol shield ctrl) meta
Proof
  rpt strip_tac >>
  `amended_meta meta meta [] = meta`
    by rw[amended_meta_def, spec_admit_all_def] >>
  `spec_refines meta meta` by rw[spec_refines_refl] >>
  metis_tac[meta_amendment_safe]
QED

val _ = export_theory ();
