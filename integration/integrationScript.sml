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
     selfProverTheory;

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

val _ = export_theory();
