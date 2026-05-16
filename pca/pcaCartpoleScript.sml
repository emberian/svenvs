(*
  A concrete, EVAL-runnable proof-carrying-actions instance: the integer
  pole cart, reused from cartpoleTheory.

  Now the untrusted controller emits (motor command, certificate). The
  certificate here is the controller's CLAIM "this command keeps the next
  state in the safe box, and stays in actuator range". The certifier
  RE-CHECKS that claim by integer arithmetic on the actual dynamics — it
  does not trust the claim, it recomputes it. So:

    - what the certifier is TRUSTED to decide:  nothing beyond the explicit
      labelled `certifier_sound` side-condition, here PROVED outright by
      intLib (the certifier literally recomputes `cp_safe (cp_step a u)`);
    - what is PROVED for ANY controller / ANY certificate stream: the
      enveloped cart never leaves the safe box (pca_safety_preservation).

  The degraded fallback is the verified counter-the-lean sub-policy
  (`cp_shield`), shown to do real work (not constant refuse), with the old
  single-action view recovered.

  Everything is run inside the logic with EVAL.
*)
open HolKernel boolLib bossLib BasicProvers intLib integerTheory
     listTheory arithmeticTheory pairTheory
     systemTheory envelopeTheory safetyTheory
     cartpoleTheory cartpoleEnvelopeTheory
     pcaTheory pcaShieldTheory;

val _ = new_theory "pcaCartpole";

(* The certifier RE-CHECKS the safety claim on the real dynamics. The
   certificate `c:int` is the controller's *claimed* resulting angle; the
   certifier accepts only if the command is in range AND the recomputed
   next state is genuinely safe AND the claimed angle matches reality (the
   certificate must be honest about the outcome). *)
Definition cp_cert_ok_def:
  cp_cert_ok (a:int) (u:int) (c:int) ⇔
    cp_valid u ∧ (c = cp_step a u) ∧ cp_safe c
End

(* The one explicit side-condition — PROVED outright (no trust): the
   certifier only accepts safety-preserving commands, because it literally
   recomputes cp_safe (cp_step a u). *)
Theorem cp_certifier_sound:
  certifier_sound cp_step cp_safe cp_cert_ok
Proof
  rw[certifier_sound_def, cp_cert_ok_def]
QED

(* The verified degraded sub-policy: counter the lean (reuse cp_shield).
   It is a safe sub-policy (the cartpole physics obligation, proved by
   integer arithmetic). *)
Theorem cp_safe_subpolicy:
  safe_subpolicy cp_step cp_safe cp_shield
Proof
  rw[subpolicy_generalises_shield, safe_shield_def, cp_safe_def,
     cp_step_def, cp_shield_def, cp_drift_def] >> intLib.ARITH_TAC
QED

(* The degraded sub-policy does REAL work, not constant refuse: from a
   leaning state it commands a non-zero correction (≠ the refuse action 0). *)
Theorem cp_subpolicy_does_real_work:
  does_real_work cp_shield 0
Proof
  rw[does_real_work_def] >> qexists_tac ‘1’ >>
  rw[cp_shield_def, cp_drift_def]
QED

(* THE HEADLINE for this instance: for ANY proof-carrying controller (any
   stream of (command,certificate) pairs, adversarial included), the
   enveloped pole cart stays in the safe box. *)
Theorem cp_pca_enveloped_safe:
  ∀pcc. invariant cp_step cp_init
          (pca_enveloped cp_cert_ok cp_shield pcc) cp_safe
Proof
  metis_tac[degraded_mode_safe, cp_init_safe, cp_certifier_sound,
            cp_safe_subpolicy]
QED

(* ---------- run it inside the logic ---------- *)

(* An HONEST proof-carrying controller: proposes the counter-lean command
   and a correct certificate (the true resulting angle). *)
Definition honest_pcc_def:
  honest_pcc (a:int) = (cp_shield a, cp_step a (cp_shield a)) : (int # int)
End

(* An ADVERSARIAL proof-carrying controller: proposes a wild out-of-range
   command AND a LYING certificate (claims a safe angle that is false). The
   certifier must reject it and the degraded sub-policy must take over. *)
Definition liar_pcc_def:
  liar_pcc (a:int) = (if a = 0 then 7 else -5, 0) : (int # int)
End

(* one enveloped tick under a proof-carrying controller *)
Definition cp_pca_drive_def:
  cp_pca_drive pcc (a:int) =
    cp_step a (pca_enveloped cp_cert_ok cp_shield pcc a)
End

Definition cp_pca_run_def:
  cp_pca_run pcc n = FUNPOW (cp_pca_drive pcc) n 0
End

Definition cp_pca_trace_def:
  cp_pca_trace pcc n = GENLIST (cp_pca_run pcc) (n + 1)
End

(* The bare plant under the lying adversary's RAW command crashes fast
   (the envelope is doing real work, not decoration). *)
Theorem liar_bare_plant_crashes:
  ¬ EVERY cp_safe
      (GENLIST (λk. FUNPOW (λa. cp_step a (FST (liar_pcc a))) k 0) 5)
Proof
  EVAL_TAC
QED

(* The proof-carrying enveloped lying adversary, run 30 ticks: the
   certifier rejects every lie, the verified sub-policy recovers, and the
   cart stays boxed — COMPUTED, not asserted. *)
Theorem liar_pca_enveloped_runs_safe:
  EVERY cp_safe (cp_pca_trace liar_pcc 30)
Proof
  EVAL_TAC
QED

(* The honest controller is also boxed (and its certificates are accepted). *)
Theorem honest_pca_enveloped_runs_safe:
  EVERY cp_safe (cp_pca_trace honest_pcc 30)
Proof
  EVAL_TAC
QED

(* Concrete certifier behaviour, run in-logic: an honest certificate from a
   leaning state is ACCEPTED; the liar's certificate is REJECTED. *)
Theorem cp_cert_accepts_honest:
  cp_cert_ok 2 (cp_shield 2) (cp_step 2 (cp_shield 2)) = T
Proof
  EVAL_TAC
QED

Theorem cp_cert_rejects_liar:
  cp_cert_ok 0 (FST (liar_pcc 0)) (SND (liar_pcc 0)) = F
Proof
  EVAL_TAC
QED

(* Subsumption, concretely: the old single-action shield view is recovered
   — cp_shield is exactly a safe_shield. *)
Theorem cp_old_shield_recovered:
  safe_shield cp_step cp_safe cp_shield
Proof
  metis_tac[cp_safe_subpolicy, subpolicy_generalises_shield]
QED

val _ = export_theory ();
