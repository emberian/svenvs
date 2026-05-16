(*
  Proven-safe degraded controller as the shield.

  In the existing layer the shield is ONE fallback action `shield s`. Here
  we generalise the fallback to a *verified conservative sub-policy*: a
  whole degraded controller `dctrl` that the runtime falls back to whenever
  the certifier rejects the inhabitant's proposal.

  We prove:
    (a) DEGRADED MODE IS SAFE — if `dctrl` is itself a safe selector
        (`safe_shield step safe dctrl`) it slots into the proof-carrying
        envelope as the shield and `pca_safety_preservation` applies
        unchanged (it is already abstract over the shield).
    (b) DEGRADED MODE IS NON-TRIVIAL — the verified sub-policy is not just
        a constant refuse: there is a witnessing state where the degraded
        controller's chosen action differs from a designated "refuse"
        action, and (in the concrete instance, pcaCartpole) it provably
        does useful recovery work.
    (c) OLD SINGLE-ACTION SHIELD AS AN INSTANCE — a one-action shield
        selector is the special (constant-image) case of the sub-policy.

  Pure, generic; the concrete non-triviality witness is in pcaCartpole.
*)
open HolKernel boolLib bossLib BasicProvers
     systemTheory envelopeTheory safetyTheory
     pcaTheory;

val _ = new_theory "pcaShield";

(* A degraded sub-policy is just a (trusted, verified) selector used as the
   fallback. It is "conservative" precisely when it is a safe shield. *)
Definition safe_subpolicy_def:
  safe_subpolicy step safe (dctrl:('s,'a)selector) ⇔
    safe_shield step safe dctrl
End

(* (a) The verified degraded controller, used as the proof-carrying
   envelope's fallback, preserves safety for ANY inhabitant. Direct
   instance of the (shield-abstract) headline. *)
Theorem degraded_mode_safe:
  init_safe init safe ∧
  certifier_sound step safe cert_ok ∧
  safe_subpolicy step safe dctrl ⇒
  ∀pcc. invariant step init (pca_enveloped cert_ok dctrl pcc) safe
Proof
  rw[safe_subpolicy_def] >>
  metis_tac[pca_safety_preservation]
QED

(* (b) Non-triviality, abstractly: a sub-policy is "does real work" w.r.t.
   a designated trivial/refuse action `refuse` if it differs from refuse on
   at least one state. A constant-refuse shield fails this. *)
Definition does_real_work_def:
  does_real_work (dctrl:'s -> 'a) (refuse:'a) ⇔
    ∃s. dctrl s ≠ refuse
End

Theorem constant_refuse_does_no_work:
  ¬ does_real_work (λs. refuse) refuse
Proof
  rw[does_real_work_def]
QED

(* (c) The old single-action shield is the special case: any bare selector
   `shield` is trivially a sub-policy, and `safe_subpolicy` reduces exactly
   to the existing `safe_shield`. So nothing is lost; the generalisation is
   conservative over envelopeTheory's notion. *)
Theorem single_action_shield_is_subpolicy:
  safe_shield step safe shield ⇒ safe_subpolicy step safe shield
Proof
  rw[safe_subpolicy_def]
QED

Theorem subpolicy_generalises_shield:
  safe_subpolicy step safe dctrl ⇔ safe_shield step safe dctrl
Proof
  rw[safe_subpolicy_def]
QED

val _ = export_theory ();
