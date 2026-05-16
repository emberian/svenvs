(*
  The safety envelope for the pole cart.

  Policy  : a one-step safety filter that also clamps the actuator range.
            Because the policy *itself* requires the next state to be safe,
            `sound_policy` is true by construction — the only real physical
            proof obligation is that the trusted fallback shield can always
            recover (`cp_safe_shield`).

  Shield  : push against the lean (u = sign of the angle). One tick later
            the angle has moved one unit *toward* upright, so the safe box
            is invariant under the shield.

  We then instantiate the generic, controller-agnostic
  `safety_preservation` theorem for this concrete cart.
*)
open HolKernel boolLib bossLib BasicProvers intLib integerTheory
     systemTheory envelopeTheory safetyTheory cartpoleTheory;

val _ = new_theory "cartpoleEnvelope";

(* Actuator range the envelope is willing to command. *)
Definition cp_valid_def:
  cp_valid (u:int) ⇔ (u = -1) ∨ (u = 0) ∨ (u = 1)
End

(* The policy: a valid command whose one-step outcome is still safe. *)
Definition cp_pol_def:
  cp_pol (a:int) (u:int) ⇔ cp_valid u ∧ cp_safe (cp_step a u)
End

(* The trusted shield: counter the lean. *)
Definition cp_shield_def:
  cp_shield (a:int) = cp_drift a
End

(* --- discharge the three premises of safety_preservation --- *)

Theorem cp_init_safe:
  init_safe cp_init cp_safe
Proof
  rw[init_safe_def, cp_init_def, cp_safe_def] >> intLib.ARITH_TAC
QED

(* Free, because cp_pol literally asserts the next state is safe. *)
Theorem cp_sound:
  sound_policy cp_step cp_safe cp_pol
Proof
  rw[sound_policy_def, cp_pol_def]
QED

(* The only genuine physics obligation, closed by integer arithmetic. *)
Theorem cp_safe_shield:
  safe_shield cp_step cp_safe cp_shield
Proof
  rw[safe_shield_def, cp_safe_def, cp_step_def, cp_shield_def,
     cp_drift_def] >> intLib.ARITH_TAC
QED

(* The headline: for ANY controller, the enveloped pole cart stays safe. *)
Theorem cp_enveloped_safe:
  ∀ctrl. invariant cp_step cp_init (enveloped cp_pol cp_shield ctrl) cp_safe
Proof
  metis_tac[safety_preservation, cp_init_safe, cp_sound, cp_safe_shield]
QED

val _ = export_theory ();
