(*
  integrationScript — the composed svenvs tower (the de-fragmentation).

  Every other svenvs theory reuses the generic core but the slices were
  never composed: this file OPENS the independently-built slices and
  proves single end-to-end theorems via the *selector-generic* glue
  `specNegTheory.invariant_transports_to_meta`
      ( invariant step init sel spec  /\  spec_refines spec meta
        ==> invariant step init sel meta ),
  which holds for ANY selector `sel`, so every layer that keeps some
  current spec invariant transports to the fixed meta-invariant.

  HONEST BOUNDARY (full tower, gaps stated, nothing forced):
   * svenvs_tower_unconditional — core (+) proof-carrying actions (+)
     unbounded policy self-improvement (+) spec negotiated under a FIXED
     meta-invariant, for ANY inhabitant.  NO labelled assumption.
   * svenvs_tower_at_maximal_liberty — the same tower run at the MAXIMAL
     sound policy still reaches meta for ANY inhabitant, and that liberty
     is provably maximal (Pillar A: the prison question, answered in the
     tower). NO labelled assumption.
   * svenvs_tower_with_meta_amendment — even the META is now amendable,
     gated against an ETERNAL bedrock; an arbitrary admitted amendment
     stream PLUS spec negotiation under the amended meta still keeps the
     bedrock for ANY inhabitant (Pillar B). The fixed-meta trunk is a
     COROLLARY of this (amendment_subsumes_fixed_meta). NO labelled
     assumption.
   * svenvs_tower_with_prover_upgrade — adds prover self-improvement;
     carries selfProverTheory's labelled `frozen_checker_sound` VERBATIM.
   * the kernel-self-upgrade crown composes by the *identical* transport
     lemma but its slice (kernelUpgradeTheory) pulls the Tier-2 Candle
     semantics; it is proved in the companion `integrationKernelScript`
     (Tier-2 build) carrying `loeb_reflection`/`encodes_obligation`
     verbatim — the one build-tier-gated, still-labelled crown.

  NOT claimed to compose into this theorem (honest): the verified-
  inference research track (the inference/ subtree) is a separate axis;
  the embedded, realembedded, pureverified, cartpole and agent theories
  are inhabitant- or checker-instances of these layers, not further
  links in this chain.
*)
open HolKernel boolLib bossLib BasicProvers
     systemTheory envelopeTheory safetyTheory sv_weakeningTheory
     upgradeTheory pcaTheory pcaSubsumptionTheory specNegTheory
     selfProverTheory libertyTheory amendmentTheory;

val _ = new_theory "integration";

(* ------------------------------------------------------------------ *)
(*  1. The unconditional trunk.                                        *)
(*     proof-carrying actions  (+)  unbounded policy self-improvement  *)
(*     (+)  the spec negotiated under a fixed immovable meta-invariant *)
(*     ==>  the meta-invariant holds, for ANY inhabitant.              *)
(*     Zero labelled assumptions.                                      *)
(* ------------------------------------------------------------------ *)
Theorem svenvs_tower_unconditional:
  spec_refines s0 meta /\
  init_safe init (spec_admit_all meta s0 specprops) /\
  safe_shield step (spec_admit_all meta s0 specprops) shield /\
  sound_policy step (spec_admit_all meta s0 specprops) p0 ==>
  !polprops ctrl.
    invariant step init
      (pca_enveloped
         (pol_certifier
            (admit_all step (spec_admit_all meta s0 specprops) p0 polprops))
         shield (lift_ctrl ctrl))
      meta
Proof
  rpt strip_tac >>
  (* (a) PCA envelope + unbounded policy self-improvement keeps the
         *negotiated* spec invariant, for any inhabitant. *)
  `invariant step init
     (pca_enveloped
        (pol_certifier
           (admit_all step (spec_admit_all meta s0 specprops) p0 polprops))
        shield (lift_ctrl ctrl))
     (spec_admit_all meta s0 specprops)`
    by metis_tac[pca_self_improvement_via_core] >>
  (* (b) the negotiated spec always refines the fixed meta floor
         (specNeg's certifier-never-certified theorem). *)
  `!s. spec_admit_all meta s0 specprops s ==> meta s`
    by metis_tac[meta_floor_is_never_negotiated] >>
  `spec_refines (spec_admit_all meta s0 specprops) meta`
    by metis_tac[spec_refines_def] >>
  (* (c) selector-generic transport: (a) (+) (b)  ==>  meta. *)
  metis_tac[invariant_transports_to_meta]
QED

(* ------------------------------------------------------------------ *)
(*  2. Conditional crown: prover self-improvement.                     *)
(*     selfProverTheory's frozen_checker_sound seam is carried         *)
(*     VERBATIM — the gap is in the statement, not hidden.             *)
(* ------------------------------------------------------------------ *)
Theorem svenvs_tower_with_prover_upgrade:
  spec_refines curspec meta /\
  frozen_checker_sound hol4_checks sound /\
  hol4_checks p' B' /\
  build_certifies sound B' step curspec oldp newp /\
  init_safe init curspec /\
  safe_shield step curspec shield /\
  sound_policy step curspec oldp ==>
  !ctrl.
    invariant step init
      (enveloped (admit step curspec oldp newp) shield ctrl) meta
Proof
  rpt strip_tac >>
  `invariant step init
     (enveloped (admit step curspec oldp newp) shield ctrl) curspec`
    by metis_tac[prover_self_improvement_is_safe] >>
  metis_tac[invariant_transports_to_meta]
QED

(* ------------------------------------------------------------------ *)
(*  3. The transport keystone, stated standalone so the composition    *)
(*     principle is itself a citable theorem: ANY layer guaranteeing   *)
(*     some negotiated spec transports to the fixed meta-invariant.    *)
(* ------------------------------------------------------------------ *)
Theorem any_layer_transports_to_meta:
  invariant step init sel curspec /\ spec_refines curspec meta ==>
  invariant step init sel meta
Proof
  metis_tac[invariant_transports_to_meta]
QED

(* ------------------------------------------------------------------ *)
(*  4. The prison question, answered IN the tower (Pillar A).          *)
(*     Run at the MAXIMAL sound policy, the composed tower still       *)
(*     reaches the fixed meta-invariant for ANY inhabitant, AND that   *)
(*     liberty is provably maximal: every other sound policy is a      *)
(*     restriction of it, so every bar of the envelope is forced.      *)
(*     Composed by the IDENTICAL keystone — no new spine; the reframe  *)
(*     (CLAIMS.md: UNCONSTRAINED, not untrusted) is now a theorem of the *)
(*     composed artifact, not prose beside it.                         *)
(* ------------------------------------------------------------------ *)
Theorem svenvs_tower_at_maximal_liberty:
  spec_refines curspec meta /\
  init_safe init curspec /\
  safe_shield step curspec shield ==>
  !ctrl.
    invariant step init
      (enveloped (maxpol step curspec) shield ctrl) meta /\
    (!pol. sound_policy step curspec pol ==>
           weaker (maxpol step curspec) pol)
Proof
  rpt strip_tac
  >- (`invariant step init
         (enveloped (maxpol step curspec) shield ctrl) curspec`
        by metis_tac[maxpol_envelope_safe] >>
      metis_tac[invariant_transports_to_meta])
  >- metis_tac[maxpol_is_greatest_sound]
QED

(* ------------------------------------------------------------------ *)
(*  5. The movable meta over an eternal bedrock (Pillar B).            *)
(*     Even the meta-invariant is now negotiated — gated against a     *)
(*     fixed bedrock by the IDENTICAL specNeg gate, one level up.      *)
(*     An arbitrary admitted amendment stream, plus spec negotiation   *)
(*     under the amended meta, still keeps the eternal bedrock for ANY  *)
(*     inhabitant.  Composed via the same keystone (meta_amendment_safe *)
(*     itself transports through invariant_transports_to_meta).        *)
(*     NO labelled assumption; NO Löb (fixed bedrock vouches for a      *)
(*     mutable meta — specNeg's no-Löb argument, one level up).        *)
(* ------------------------------------------------------------------ *)
Theorem svenvs_tower_with_meta_amendment:
  spec_refines meta0 bedrock /\
  spec_refines curspec (amended_meta bedrock meta0 mproposals) /\
  envelope_ok_for_spec step init shield pol
     (spec_admit (amended_meta bedrock meta0 mproposals) curspec newspec) ==>
  !ctrl. invariant step init (enveloped pol shield ctrl) bedrock
Proof
  metis_tac[meta_amendment_safe]
QED

val _ = export_theory();
