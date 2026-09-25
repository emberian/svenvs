(*
  Proven-safe degraded controller as the shield.

  In the existing layer the shield is ONE fallback selector `shield s`. Here
  we generalise the fallback to a *verified conservative sub-policy*: a SET
  of permitted fallback actions per state, `dpol : 's -> 'a -> bool`, from
  which the runtime may pick any action whenever the certifier rejects the
  inhabitant's proposal.

  We prove:
    (a) DEGRADED MODE IS SAFE — any selector chosen from a safe sub-policy
        slots into the proof-carrying envelope as the shield and
        `pca_safety_preservation` applies unchanged (`degraded_mode_safe`).
    (b) FALLBACK FREEDOM — the runtime may choose differently from the same
        sub-policy, even switching choice state by state, and stay safe; a
        single-action shield cannot express this (`fallback_freedom`).
    (c) DEGRADED MODE IS NON-TRIVIAL — a constant refuse does no work, and a
        sub-policy that forbids refusing at some safe state forces EVERY
        choice from it to do work (`subpolicy_forces_real_work`).
    (d) OLD SINGLE-ACTION SHIELD AS AN INSTANCE — the singleton sub-policy
        {shield s} is safe iff the shield is, and the safe shields are
        exactly the selectors chosen from safe sub-policies
        (`single_action_shield_is_subpolicy`, `subpolicy_generalises_shield`).

  Pure, generic; the concrete witnesses are in pcaCartpole.
*)
open HolKernel boolLib bossLib BasicProvers
     systemTheory envelopeTheory safetyTheory
     pcaTheory;

val _ = new_theory "pcaShield";

(* A degraded sub-policy is SAFE when every permitted fallback action from a
   safe state lands in a safe state, and it permits at least one action at
   every safe state (so it can always act as the fallback). *)
Definition safe_subpolicy_def:
  safe_subpolicy step safe (dpol:'s -> 'a -> bool) ⇔
    (∀s a. safe s ∧ dpol s a ⇒ safe (step s a)) ∧
    (∀s. safe s ⇒ ∃a. dpol s a)
End

(* A selector CHOOSES FROM a sub-policy when, at every safe state, its
   action is one the sub-policy permits. *)
Definition chooses_from_def:
  chooses_from safe (dpol:'s -> 'a -> bool) (choose:'s -> 'a) ⇔
    ∀s. safe s ⇒ dpol s (choose s)
End

(* A safe sub-policy can always be used: some selector chooses from it. *)
Theorem subpolicy_has_selector:
  safe_subpolicy step safe dpol ⇒ ∃choose. chooses_from safe dpol choose
Proof
  rw[safe_subpolicy_def, chooses_from_def] >>
  qexists_tac ‘λs. @a. dpol s a’ >> rw[] >>
  SELECT_ELIM_TAC >> metis_tac[]
QED

Theorem chosen_selector_is_safe_shield:
  safe_subpolicy step safe dpol ∧ chooses_from safe dpol choose ⇒
  safe_shield step safe choose
Proof
  rw[safe_subpolicy_def, chooses_from_def, safe_shield_def]
QED

(* (a) Any selector chosen from the verified degraded sub-policy, used as the
   proof-carrying envelope's fallback, preserves safety for ANY inhabitant. *)
Theorem degraded_mode_safe:
  init_safe init safe ∧
  certifier_sound step safe cert_ok ∧
  safe_subpolicy step safe dpol ∧ chooses_from safe dpol dctrl ⇒
  ∀pcc. invariant step init (pca_enveloped cert_ok dctrl pcc) safe
Proof
  metis_tac[chosen_selector_is_safe_shield, pca_safety_preservation]
QED

(* (b) Fallback freedom: two choices from one safe sub-policy, and ANY
   state-dependent switch between them, are all safe fallbacks. *)
Theorem fallback_freedom:
  init_safe init safe ∧
  certifier_sound step safe cert_ok ∧
  safe_subpolicy step safe dpol ∧
  chooses_from safe dpol c1 ∧ chooses_from safe dpol c2 ⇒
  ∀P pcc.
    invariant step init (pca_enveloped cert_ok c1 pcc) safe ∧
    invariant step init (pca_enveloped cert_ok c2 pcc) safe ∧
    invariant step init
      (pca_enveloped cert_ok (λs. if P s then c1 s else c2 s) pcc) safe
Proof
  rpt strip_tac >>
  ‘chooses_from safe dpol (λs. if P s then c1 s else c2 s)’
    by (fs[chooses_from_def] >> rw[]) >>
  metis_tac[degraded_mode_safe]
QED

(* (c) Non-triviality: a selector "does real work" w.r.t. a designated
   trivial/refuse action if it differs from refuse on at least one state. *)
Definition does_real_work_def:
  does_real_work (dctrl:'s -> 'a) (refuse:'a) ⇔
    ∃s. dctrl s ≠ refuse
End

Theorem constant_refuse_does_no_work:
  ¬ does_real_work (λs. refuse) refuse
Proof
  rw[does_real_work_def]
QED

(* A sub-policy that forbids refusing at some safe state makes EVERY choice
   from it do real work — non-triviality is a property of the sub-policy,
   not of one lucky selector. *)
Theorem subpolicy_forces_real_work:
  safe s ∧ ¬dpol s refuse ∧ chooses_from safe dpol choose ⇒
  does_real_work choose refuse
Proof
  rw[chooses_from_def, does_real_work_def] >> metis_tac[]
QED

(* (d) The old single-action shield is the singleton sub-policy {shield s}:
   it is chosen from by the shield itself, and it is safe iff the shield is. *)
Theorem single_action_shield_is_subpolicy:
  chooses_from safe (λs a. a = shield s) shield ∧
  (safe_subpolicy step safe (λs a. a = shield s) ⇔
   safe_shield step safe shield)
Proof
  rw[chooses_from_def, safe_subpolicy_def, safe_shield_def] >>
  metis_tac[]
QED

(* The generalisation is conservative and exact: the safe shields are
   precisely the selectors chosen from safe sub-policies. *)
Theorem subpolicy_generalises_shield:
  safe_shield step safe shield ⇔
  ∃dpol. safe_subpolicy step safe dpol ∧ chooses_from safe dpol shield
Proof
  metis_tac[chosen_selector_is_safe_shield,
            single_action_shield_is_subpolicy]
QED

val _ = export_theory ();
