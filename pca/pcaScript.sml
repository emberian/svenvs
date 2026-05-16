(*
  Proof-carrying actions (PCA).

  Generalisation of the policy envelope (envelopeTheory). In the old layer
  the controller is a bare selector and the trusted thing is a FIXED policy
  predicate `pol`; the inhabitant can only ever ask for "more permissiveness"
  by weakening that policy.

  Here the untrusted controller emits *(action, certificate)* pairs. The
  envelope executes the proposed action iff a *checkable certifier* accepts
  the certificate as a valid witness that the action preserves the safety
  invariant from the current state; otherwise the trusted shield acts.

  The certifier `cert_ok : 's -> 'a -> 'c -> bool` is an EXPLICIT predicate
  PARAMETER — a decidable check the runtime performs, NOT an oracle. The
  ONLY thing the certifier is trusted to decide correctly is captured by the
  single, labelled hypothesis

      certifier_sound step safe cert_ok ⇔
        ∀s a c. safe s ∧ cert_ok s a c ⇒ safe (step s a)

  i.e. "if the certifier accepts (a,c) from a safe state, then taking a is
  safe". That is an explicit, auditable side-condition on the certifier
  (exactly analogous to `sound_policy` for the old layer), NOT a `cheat`.

  Given only that side-condition (plus safe init + safe shield), the
  headline `pca_safety_preservation` holds for ANY controller emitting ANY
  stream of (action,certificate) pairs — controller-agnostic, exactly like
  `safety_preservation`. The controller is universally quantified and never
  constrained.
*)
open HolKernel boolLib bossLib BasicProvers
     systemTheory envelopeTheory safetyTheory;

val _ = new_theory "pca";

(* A proof-carrying controller proposes an action together with a
   certificate (of opaque type 'c) per state. *)
Type pc_controller = “:'s -> ('a # 'c)”;

(* A certifier: a decidable runtime check on (state, action, certificate).
   This is a PARAMETER, supplied per instance, not an oracle. *)
Type certifier = “:'s -> 'a -> 'c -> bool”;

(* The proof-carrying envelope: run the proposed action iff its certificate
   passes the certifier, else fall back to the trusted shield. *)
Definition pca_enveloped_def:
  pca_enveloped (cert_ok:'s -> 'a -> 'c -> bool)
                (shield:'s -> 'a)
                (pcc:'s -> ('a # 'c)) (s:'s) =
    if cert_ok s (FST (pcc s)) (SND (pcc s))
    then FST (pcc s)
    else shield s
End

(* The ONE explicit, labelled trust assumption on the certifier: whatever
   it accepts from a safe state really does preserve safety. This is a
   checkable side-condition on the certifier (an instance must discharge
   it), the proof-carrying analogue of `sound_policy`. It is NOT a cheat
   and NOT an oracle: it appears verbatim as a Definition and as a named
   antecedent of every theorem below. *)
Definition certifier_sound_def:
  certifier_sound (step:'s -> 'a -> 's) (safe:'s -> bool)
                  (cert_ok:'s -> 'a -> 'c -> bool) ⇔
    ∀s a c. safe s ∧ cert_ok s a c ⇒ safe (step s a)
End

(* Key lemma: a sound certifier + a safe shield make the proof-carrying
   enveloped controller step-closed for [safe] — for ANY controller and
   ANY stream of certificates. The controller (pcc) is free. *)
Theorem pca_enveloped_step_closed:
  certifier_sound step safe cert_ok ∧ safe_shield step safe shield ⇒
  step_closed step (pca_enveloped cert_ok shield pcc) safe
Proof
  rw[step_closed_def, pca_enveloped_def] >>
  fs[certifier_sound_def, safe_shield_def] >>
  Cases_on ‘cert_ok s (FST (pcc s)) (SND (pcc s))’ >> fs[] >>
  metis_tac[]
QED

(* THE HEADLINE. For ANY proof-carrying controller (any stream of
   (action,certificate)), the proof-carrying envelope keeps the safety
   invariant, given only:
     - initial states are safe,
     - the certifier is sound (the one explicit side-condition), and
     - the shield is safe.
   Controller-agnostic: `pcc` is universally quantified, no hypothesis on
   it whatsoever — exactly like safetyTheory.safety_preservation. *)
Theorem pca_safety_preservation:
  init_safe init safe ∧
  certifier_sound step safe cert_ok ∧
  safe_shield step safe shield ⇒
  ∀pcc. invariant step init (pca_enveloped cert_ok shield pcc) safe
Proof
  rpt strip_tac >>
  irule invariant_intro >>
  metis_tac[pca_enveloped_step_closed]
QED

(* Spelled-out corollary: every reachable state of the proof-carrying
   enveloped system is safe, for an arbitrary controller. *)
Theorem pca_enveloped_states_safe:
  init_safe init safe ∧
  certifier_sound step safe cert_ok ∧
  safe_shield step safe shield ∧
  reach step init (pca_enveloped cert_ok shield pcc) s ⇒
  safe s
Proof
  metis_tac[pca_safety_preservation, invariant_def]
QED

val _ = export_theory ();
