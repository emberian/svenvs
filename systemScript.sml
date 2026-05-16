(*
  An abstract reactive system.

  State (’s) and action (’a) are opaque type variables: we never run a
  controller, we only reason about the shape of its interaction with a
  deterministic environment.
*)
open HolKernel boolLib bossLib BasicProvers;

val _ = new_theory "system";

(* One environment step: a state and a chosen action yield a next state. *)
Type step_fn = “:'s -> 'a -> 's”;

(* An action selector: the (untrusted) thing that picks an action per state.
   The enveloped controller in envelopeScript will be one of these. *)
Type selector = “:'s -> 'a”;

(* States reachable from [init] when actions are chosen by [sel]. *)
Inductive reach:
[~init:]
  (init s ⇒ reach step init sel s)
[~step:]
  (reach step init sel s ⇒ reach step init sel (step s (sel s)))
End

(* A state predicate [safe] is an invariant of the [sel]-driven system if it
   holds on every reachable state. *)
Definition invariant_def:
  invariant step init sel safe ⇔
    ∀s. reach step init sel s ⇒ safe s
End

(* Standard discharge conditions for an inductive invariant. *)
Definition init_safe_def:
  init_safe init safe ⇔ ∀s. init s ⇒ safe s
End

Definition step_closed_def:
  step_closed step sel safe ⇔
    ∀s. safe s ⇒ safe (step s (sel s))
End

(* The textbook inductive-invariant principle, specialised to [reach]. *)
Theorem invariant_intro:
  init_safe init safe ∧ step_closed step sel safe ⇒
  invariant step init sel safe
Proof
  rpt strip_tac >>
  simp[invariant_def] >>
  ho_match_mp_tac reach_ind >>
  fs[init_safe_def, step_closed_def] >> metis_tac[]
QED

val _ = export_theory ();
