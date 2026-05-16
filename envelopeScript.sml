(*
  The policy envelope.

  A [controller] is an arbitrary selector — unconstrained, so
  we model nothing about it. A [policy] says which
  actions are permitted in which states. A [shield] is a trusted fallback
  selector. The *enveloped* controller runs the controller's choice when the
  policy permits it, and otherwise substitutes the shield's action.

  Nothing here inspects the controller — it is a black box. This is the
  "wrap a policy envelope around a controller" construction.
*)
open HolKernel boolLib bossLib BasicProvers systemTheory;

val _ = new_theory "envelope";

(* A policy: permitted (state, action) pairs. *)
Type policy = “:'s -> 'a -> bool”;

(* Runtime enforcement: keep the controller's action iff the policy allows
   it, else fall back to the shield. *)
Definition enveloped_def:
  enveloped (pol:('s,'a)policy) (shield:('s,'a)selector)
            (ctrl:('s,'a)selector) s =
    if pol s (ctrl s) then ctrl s else shield s
End

(* The policy is safety-sound: every permitted action from a safe state lands
   in a safe state. *)
Definition sound_policy_def:
  sound_policy step safe (pol:('s,'a)policy) ⇔
    ∀s a. safe s ∧ pol s a ⇒ safe (step s a)
End

(* The shield is itself safe to invoke from any safe state. *)
Definition safe_shield_def:
  safe_shield step safe (shield:('s,'a)selector) ⇔
    ∀s. safe s ⇒ safe (step s (shield s))
End

(* Key lemma: under a sound policy and a safe shield, the enveloped
   controller is step-closed for [safe] — *regardless of the controller*. *)
Theorem enveloped_step_closed:
  sound_policy step safe pol ∧ safe_shield step safe shield ⇒
  step_closed step (enveloped pol shield ctrl) safe
Proof
  rw[step_closed_def, enveloped_def] >>
  fs[sound_policy_def, safe_shield_def] >>
  Cases_on ‘pol s (ctrl s)’ >> fs[]
QED

val _ = export_theory ();
