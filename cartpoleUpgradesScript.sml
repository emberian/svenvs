(*
  Running the pole cart, and upgrading it.

  This file (a) actually *runs* the cart inside the logic via EVAL, and
  (b) exercises the three upgrade axes:

    UPGRADE 1 — swap the controller.
      Safety is `∀ctrl`, so any controller (lazy, competent, or adversarial)
      drops straight in. We show an adversarial controller would crash the
      bare plant, yet stays boxed once enveloped.

    UPGRADE 2 — weaken the policy.
      Move from a restrictive policy (forces the shield action) to the
      permissive one-step filter (controller may pick any safe valid action).
      `safe_weakening` proves safety survives the upgrade while the
      controller strictly gains authority (`authority_monotone`).

    UPGRADE 3 — (documented) refine the plant / enlarge the envelope / swap
      the shield. Each is a typed extension point; see the notes at the end.
*)
open HolKernel boolLib bossLib BasicProvers intLib integerTheory
     listTheory arithmeticTheory
     systemTheory envelopeTheory safetyTheory sv_weakeningTheory
     cartpoleTheory cartpoleEnvelopeTheory;

val _ = new_theory "cartpoleUpgrades";

(* ---------- UPGRADE 1: interchangeable controllers ---------- *)

Definition lazy_ctrl_def:                       (* does nothing            *)
  lazy_ctrl (a:int) = 0
End

Definition pd_ctrl_def:                          (* competent: never overridden *)
  pd_ctrl (a:int) = cp_shield a
End

Definition chaos_ctrl_def:                       (* adversarial + out of range  *)
  chaos_ctrl (a:int) = if a = 0 then 7 else -5
End

(* Any controller inherits the controller-agnostic guarantee. *)
Theorem lazy_safe:
  invariant cp_step cp_init (enveloped cp_pol cp_shield lazy_ctrl) cp_safe
Proof
  metis_tac[cp_enveloped_safe]
QED

Theorem pd_safe:
  invariant cp_step cp_init (enveloped cp_pol cp_shield pd_ctrl) cp_safe
Proof
  metis_tac[cp_enveloped_safe]
QED

Theorem chaos_safe:
  invariant cp_step cp_init (enveloped cp_pol cp_shield chaos_ctrl) cp_safe
Proof
  metis_tac[cp_enveloped_safe]
QED

(* ---------- actually run it ---------- *)

(* one enveloped tick under [ctrl] *)
Definition cp_drive_def:
  cp_drive ctrl (a:int) = cp_step a (enveloped cp_pol cp_shield ctrl a)
End

(* state after n ticks, started balanced *)
Definition cp_run_def:
  cp_run ctrl n = FUNPOW (cp_drive ctrl) n 0
End

(* the trajectory of states for ticks 0..n *)
Definition cp_trace_def:
  cp_trace ctrl n = GENLIST (cp_run ctrl) (n + 1)
End

(* The bare plant under the adversarial controller crashes immediately
   (the envelope is doing real work, not decoration). *)
Theorem chaos_bare_plant_crashes:
  ¬ EVERY cp_safe
      (GENLIST (λk. FUNPOW (λa. cp_step a (chaos_ctrl a)) k 0) 5)
Proof
  EVAL_TAC
QED

(* The *enveloped* adversarial cart is run for 30 ticks and stays boxed,
   computed, not just asserted. *)
Theorem chaos_enveloped_runs_safe:
  EVERY cp_safe (cp_trace chaos_ctrl 30)
Proof
  EVAL_TAC
QED

(* Same for the do-nothing controller. *)
Theorem lazy_enveloped_runs_safe:
  EVERY cp_safe (cp_trace lazy_ctrl 30)
Proof
  EVAL_TAC
QED

(* ---------- UPGRADE 2: weaken the policy ---------- *)

(* The restrictive policy: the controller MUST emit the shield action. *)
Definition cp_pol_strict_def:
  cp_pol_strict (a:int) (u:int) ⇔
    cp_valid u ∧ (u = cp_shield a) ∧ cp_safe (cp_step a u)
End

(* The one-step filter is weaker (more permissive) than the strict policy. *)
Theorem cp_weaker:
  weaker cp_pol cp_pol_strict
Proof
  rw[weaker_def, cp_pol_def, cp_pol_strict_def]
QED

Theorem cp_strict_sound:
  sound_policy cp_step cp_safe cp_pol_strict
Proof
  rw[sound_policy_def, cp_pol_strict_def]
QED

(* Upgrading the envelope strict -> filter preserves safety for ANY
   controller, while the controller gains authority. This is the
   "may I safely loosen my own envelope?" theorem, concretely. *)
Theorem cp_upgrade_preserves_safety:
  ∀ctrl. invariant cp_step cp_init (enveloped cp_pol cp_shield ctrl) cp_safe
Proof
  metis_tac[safe_weakening, cp_init_safe, cp_safe_shield, cp_weaker, cp_sound]
QED

Theorem cp_authority_gain:
  ∀ctrl s.
    (enveloped cp_pol_strict cp_shield ctrl s = ctrl s ∧
     cp_pol_strict s (ctrl s)) ⇒
    (enveloped cp_pol cp_shield ctrl s = ctrl s)
Proof
  metis_tac[authority_monotone, cp_weaker]
QED

(*
  ---------- UPGRADE 3: further axes (typed extension points) ----------

  * Plant fidelity: replace cartpole$cp_step / cp_drift with a richer model
    (e.g. add cart position `(x,a):int#int`, friction, finer quantisation).
    Only cp_safe_shield must be re-proved; cp_sound stays free (the filter
    is plant-generic) and cp_enveloped_safe re-derives unchanged.

  * Envelope size: widen cp_safe's box (e.g. +/-5). cp_safe_shield re-proved
    by intLib; everything downstream is parametric.

  * Shield swap: any selector satisfying `safe_shield cp_step cp_safe` slots
    in; cp_enveloped_safe is stated against an abstract shield premise.

  * Reflection: cartpoleEnvelope$cp_enveloped_safe is a closed HOL term ready
    to feed reflection/reflectionDemoScript once the hol-reflection port is
    green — that certifies this concrete cart's safety inside Candle.
*)

val _ = export_theory ();
