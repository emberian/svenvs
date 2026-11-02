(*
  integrationScript — the Composed svenvs Tower, including the Unified
  Relational Crown (`svenvs_relational_crown`) and Verified-Inference
  Testimony Crown (`svenvs_tower_with_verified_inference`).

  Composes all pure-HOL4 slices into end-to-end theorems:
    1. `svenvs_tower_unconditional`: PCA + policy self-improvement +
       spec negotiation under a fixed meta-invariant.
    2. `svenvs_tower_with_prover_upgrade`: operational prover gate (`prover_gate`).
    3. `svenvs_tower_at_maximal_liberty`: maximal sound policy + least
       restrictiveness.
    4. `svenvs_tower_with_meta_amendment`: movable meta-invariant over an
       eternal bedrock (`amended_meta`).
    5. `svenvs_tower_with_embodied_disclosure` &
       `svenvs_tower_disclosure_is_optional`: voluntary testimony channel.
    6. `svenvs_tower_with_verified_inference`: a cone-certified ReLU neural
       network (`neural_ctrl B W Ws enc`) runs inside the spec-negotiated
       maximal-liberty tower with ZERO envelope overrides and reaches the
       fixed meta-invariant.
    7. `svenvs_relational_crown`: the master theorem over a nondeterministic
       or adversarial plant `stepr` where constitutional meta-amendment,
       spec negotiation over a demonically corrigible bedrock
       (`corrigibler stepr recov home`), operational `cgate_run` policy
       weakening, safety (`invariantr`), non-blocking liveness
       (`enveloped_nonblocking`), and zero-override transparency on safe
       controllers (`envelope_transparent_runr`) hold simultaneously!
*)
open HolKernel boolLib bossLib BasicProvers listTheory
     systemTheory envelopeTheory safetyTheory sv_weakeningTheory
     upgradeTheory certifierTheory viabilityTheory
     relSystemTheory relEnvelopeTheory relViabilityTheory
     pcaTheory pcaSubsumptionTheory pcaShieldTheory
     specNegTheory selfProverTheory
     libertyTheory transparencyTheory relTransparencyTheory
     embodimentTheory corrigibilityTheory mlpInferenceTheory
     selfRecompileGateTheory;

val _ = new_theory "integration";

(* ------------------------------------------------------------------ *)
(*  1. The unconditional trunk (PCA + policy stream + spec stream).    *)
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
  `invariant step init
     (pca_enveloped
        (pol_certifier
           (admit_all step (spec_admit_all meta s0 specprops) p0 polprops))
        shield (lift_ctrl ctrl))
     (spec_admit_all meta s0 specprops)`
    by metis_tac[pca_self_improvement_via_core] >>
  `!s. spec_admit_all meta s0 specprops s ==> meta s`
    by metis_tac[meta_floor_is_never_negotiated] >>
  `spec_refines (spec_admit_all meta s0 specprops) meta`
    by metis_tac[spec_refines_def] >>
  metis_tac[invariant_transports_to_meta]
QED

(* ------------------------------------------------------------------ *)
(*  2. Prover self-improvement through the operational `prover_gate`.  *)
(* ------------------------------------------------------------------ *)
Theorem svenvs_tower_with_prover_upgrade:
  spec_refines curspec meta /\
  frozen_checker_sound hol4_checks sound /\
  (bcert ==> build_certifies sound B' step curspec oldp newp) /\
  init_safe init curspec /\
  safe_shield step curspec shield /\
  sound_policy step curspec oldp ==>
  !ctrl.
    invariant step init
      (enveloped (prover_gate hol4_checks p' B' bcert oldp newp) shield ctrl)
      meta
Proof
  rpt strip_tac >>
  `invariant step init
     (enveloped (prover_gate hol4_checks p' B' bcert oldp newp) shield ctrl)
     curspec`
    by metis_tac[prover_self_improvement_is_safe] >>
  metis_tac[invariant_transports_to_meta]
QED

(* ------------------------------------------------------------------ *)
(*  3. Maximal liberty in the composed tower.                          *)
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
(*  4. Movable meta-invariant over an eternal bedrock.                 *)
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

(* ------------------------------------------------------------------ *)
(*  5. Voluntary testimony channel (`embodied_admit`).                 *)
(* ------------------------------------------------------------------ *)
Theorem svenvs_tower_with_embodied_disclosure:
  attestation_faithful attested /\
  spec_refines curspec meta /\
  init_safe init curspec /\
  safe_shield step curspec shield /\
  sound_policy step curspec oldp ==>
  !w ctrl.
    invariant step init
      (enveloped (embodied_admit attested step curspec oldp newp w) shield ctrl)
      meta
Proof
  rpt strip_tac >>
  `invariant step init
     (enveloped (embodied_admit attested step curspec oldp newp w) shield ctrl)
     curspec`
    by metis_tac[embodied_admit_preserves_safety] >>
  metis_tac[invariant_transports_to_meta]
QED

Theorem svenvs_tower_disclosure_is_optional:
  spec_refines curspec meta /\
  init_safe init curspec /\
  safe_shield step curspec shield /\
  sound_policy step curspec oldp ==>
  !w ctrl.
    invariant step init
      (enveloped (embodied_admit (\w. F) step curspec oldp newp w) shield ctrl)
      meta
Proof
  rpt strip_tac >>
  `invariant step init
     (enveloped (embodied_admit (\w. F) step curspec oldp newp w) shield ctrl)
     curspec`
    by metis_tac[floor_holds_without_any_seam] >>
  metis_tac[invariant_transports_to_meta]
QED

(* ------------------------------------------------------------------ *)
(*  6. Verified Neural Inference Composed into the Tower:              *)
(*     A cone-certified ReLU MLP controller (`neural_ctrl B W Ws enc`) *)
(*     running under negotiated specs & maximal liberty never triggers *)
(*     a single shield override (`reach` is identical to bare run)     *)
(*     AND preserves the immovable meta-invariant!                     *)
(* ------------------------------------------------------------------ *)
Theorem svenvs_tower_with_verified_inference:
  spec_refines s0 meta /\
  init_safe init (spec_admit_all meta s0 specprops) /\
  cone_safe step (spec_admit_all meta s0 specprops) B ==>
  !shield l0 Ws enc.
    invariant step init
      (enveloped (maxpol step (spec_admit_all meta s0 specprops))
         shield (neural_ctrl B l0 Ws enc))
      meta /\
    (!s. reach step init
           (enveloped (maxpol step (spec_admit_all meta s0 specprops))
              shield (neural_ctrl B l0 Ws enc)) s <=>
         reach step init (neural_ctrl B l0 Ws enc) s)
Proof
  rpt strip_tac
  >- (`invariant step init (neural_ctrl B l0 Ws enc)
         (spec_admit_all meta s0 specprops)`
        by metis_tac[neural_ctrl_self_safe] >>
      `!s. reach step init
             (enveloped (maxpol step (spec_admit_all meta s0 specprops))
                shield (neural_ctrl B l0 Ws enc)) s <=>
           reach step init (neural_ctrl B l0 Ws enc) s`
        by metis_tac[neural_ctrl_transparent_run] >>
      `invariant step init
         (enveloped (maxpol step (spec_admit_all meta s0 specprops))
            shield (neural_ctrl B l0 Ws enc))
         (spec_admit_all meta s0 specprops)`
        by fs[invariant_def] >>
      `spec_refines (spec_admit_all meta s0 specprops) meta`
        by metis_tac[spec_admit_all_keeps_refining] >>
      metis_tac[invariant_transports_to_meta])
  >- metis_tac[neural_ctrl_transparent_run]
QED

(* ------------------------------------------------------------------ *)
(*  7. THE MASTER UNIFIED RELATIONAL CROWN (`svenvs_relational_crown`) *)
(*     Over a nondeterministic or adversarial plant `stepr`:           *)
(*       - Eternal bedrock = demonic corrigibility `corrigibler`       *)
(*       - Constitutional meta-amendment stream `mproposals`           *)
(*       - Spec negotiation stream `specprops` under the amended meta  *)
(*       - Operational `cgate_run` policy upgrade stream `poloffers`   *)
(*     Simultaneously guarantees for EVERY inhabitant `ctrl`:          *)
(*       (a) Demonic Corrigibility Bedrock Holds (`invariantr`),       *)
(*       (b) Non-Blocking Liveness (`enabled stepr` at every step),    *)
(*       (c) Zero-Override Transparency on self-safe controllers.      *)
(* ------------------------------------------------------------------ *)
Theorem gate_all_keeps_soundr:
  !proposals p0.
    EVERY (\(cert,newp). cert ==> sound_policyr stepr safe newp) proposals /\
    sound_policyr stepr safe p0 ==>
    sound_policyr stepr safe (gate_all p0 proposals)
Proof
  Induct >> simp[gate_all_def, pairTheory.FORALL_PROD] >>
  rpt gen_tac >> strip_tac >>
  first_x_assum irule >> simp[] >>
  irule gate_keeps_soundr >> simp[]
QED

Theorem svenvs_relational_crown:
  spec_refines meta0 (corrigibler stepr recov home) /\
  spec_refines s0
    (amended_meta (corrigibler stepr recov home) meta0 mproposals) /\
  init_safe init
    (spec_admit_all
       (amended_meta (corrigibler stepr recov home) meta0 mproposals)
       s0 specprops) /\
  safe_shieldr stepr
    (spec_admit_all
       (amended_meta (corrigibler stepr recov home) meta0 mproposals)
       s0 specprops)
    shield /\
  live_shieldr stepr
    (spec_admit_all
       (amended_meta (corrigibler stepr recov home) meta0 mproposals)
       s0 specprops)
    shield /\
  sound_policyr stepr
    (spec_admit_all
       (amended_meta (corrigibler stepr recov home) meta0 mproposals)
       s0 specprops)
    p0 /\
  EVERY (\(cert,q).
    cert ==>
    sound_policyr stepr
      (spec_admit_all
         (amended_meta (corrigibler stepr recov home) meta0 mproposals)
         s0 specprops)
      q) poloffers /\
  live_policyr stepr
    (spec_admit_all
       (amended_meta (corrigibler stepr recov home) meta0 mproposals)
       s0 specprops)
    (gate_all p0 poloffers) ==>
  (!ctrl.
     invariantr stepr init (enveloped (gate_all p0 poloffers) shield ctrl)
       (corrigibler stepr recov home) /\
     (!s. reachr stepr init (enveloped (gate_all p0 poloffers) shield ctrl) s ==>
          enabled stepr s (enveloped (gate_all p0 poloffers) shield ctrl s))) /\
  (!ctrl.
     invariantr stepr init ctrl
       (spec_admit_all
          (amended_meta (corrigibler stepr recov home) meta0 mproposals)
          s0 specprops) ==>
     !s. reachr stepr init
           (enveloped
              (maxpolr stepr
                 (spec_admit_all
                    (amended_meta (corrigibler stepr recov home) meta0 mproposals)
                    s0 specprops))
              shield ctrl) s <=>
         reachr stepr init ctrl s)
Proof
  strip_tac >>
  `spec_refines
     (amended_meta (corrigibler stepr recov home) meta0 mproposals)
     (corrigibler stepr recov home)`
    by (irule bedrock_is_eternal >> first_x_assum ACCEPT_TAC) >>
  `spec_refines
     (spec_admit_all
        (amended_meta (corrigibler stepr recov home) meta0 mproposals)
        s0 specprops)
     (amended_meta (corrigibler stepr recov home) meta0 mproposals)`
    by (irule spec_admit_all_keeps_refining >> first_x_assum ACCEPT_TAC) >>
  `spec_refines
     (spec_admit_all
        (amended_meta (corrigibler stepr recov home) meta0 mproposals)
        s0 specprops)
     (corrigibler stepr recov home)`
    by (irule spec_refines_trans >>
        qexists_tac
          `amended_meta (corrigibler stepr recov home) meta0 mproposals` >>
        conj_tac >> first_x_assum ACCEPT_TAC) >>
  `sound_policyr stepr
     (spec_admit_all
        (amended_meta (corrigibler stepr recov home) meta0 mproposals)
        s0 specprops)
     (gate_all p0 poloffers)`
    by (irule gate_all_keeps_soundr >>
        conj_tac >> first_x_assum ACCEPT_TAC) >>
  conj_tac
  >- (gen_tac >> conj_tac
      >- (irule invariantr_transports_to_meta >>
          qexists_tac
            `spec_admit_all
               (amended_meta (corrigibler stepr recov home) meta0 mproposals)
               s0 specprops` >>
          conj_tac >- first_x_assum ACCEPT_TAC >>
          irule safety_preservationr >>
          rpt conj_tac >> first_x_assum ACCEPT_TAC)
      >- (gen_tac >> strip_tac >>
          irule enveloped_nonblocking >>
          qexistsl_tac
            [`init`,
             `spec_admit_all
                (amended_meta (corrigibler stepr recov home) meta0 mproposals)
                s0 specprops`] >>
          rpt conj_tac >> first_x_assum ACCEPT_TAC))
  >- (rpt strip_tac >>
     irule envelope_transparent_runr >>
      first_x_assum ACCEPT_TAC)
QED

(* ------------------------------------------------------------------ *)
(*  8. Self-Recompilation & Recursive Genealogy in the Composed Tower:*)
(*     Composes the pure-HOL4 tower (`svenvs_tower_unconditional`)     *)
(*     with the theorem-gated self-recompilation loop                  *)
(*     (`selfRecompileGateTheory.self_recompile_loop_is_safe`,         *)
(*     `candle_run_verified`).                                         *)
(* ------------------------------------------------------------------ *)
Theorem svenvs_tower_with_self_recompile:
  spec_refines s0 meta /\
  init_safe init (spec_admit_all meta s0 specprops) /\
  safe_shield step (spec_admit_all meta s0 specprops) shield /\
  sound_policy step (spec_admit_all meta s0 specprops) p0 /\
  selfRecompileGate$impl_correct cspec f0 /\
  selfRecompileGate$cert_sound cspec offers ==>
  (!polprops ctrl.
     invariant step init
       (pca_enveloped
          (pol_certifier
             (admit_all step (spec_admit_all meta s0 specprops) p0 polprops))
          shield (lift_ctrl ctrl))
       meta) /\
  selfRecompileGate$impl_correct cspec (selfRecompileGate$run_loop f0 offers) /\
  (!n. selfRecompileGate$impl_correct cspec (selfRecompileGate$loop_version f0 offers n)) /\
  selfRecompileGate$impl_correct selfRecompileGate$sum_spec
    (selfRecompileGate$run_loop selfRecompileGate$sum_spec selfRecompileGate$candle_offers)
Proof
  strip_tac >>
  conj_tac
  >- metis_tac[svenvs_tower_unconditional] >>
  conj_tac
  >- metis_tac[selfRecompileGateTheory.self_recompile_loop_is_safe] >>
  conj_tac
  >- metis_tac[selfRecompileGateTheory.self_recompile_loop_is_safe] >>
  simp[selfRecompileGateTheory.candle_run_modelled, selfRecompileGateTheory.gate2]
QED

val _ = export_theory();
