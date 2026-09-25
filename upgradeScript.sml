(*
  Proof-carrying self-improvement.

  A running enveloped system may *propose to change its own policy* (loosen
  its envelope to gain autonomy). A proposal is admitted ONLY if it
  discharges a proof obligation:

      admissible step safe oldp newp ⇔
        sound_policy step safe newp ∧ weaker newp oldp

  i.e. the new policy must (1) still be safety-sound and (2) be a genuine
  weakening (≥ as permissive) of the current one. `admit` installs the new
  policy iff the obligation holds, and otherwise keeps the old one — an
  unproven proposal can never degrade safety.

  The point of this file: prove the *gate itself is sound*, and that this
  holds under an UNBOUNDED sequence of self-proposed upgrades. The proposer
  (a unconstrained agent) must pay for every increase in authority with
  a checkable proof; the kernel guarantees safety is never lost.

  This is the HOL-level layer. The "typed-in program" that denotes [newp]
  is reflected in cartpoleProgramScript; the same obligation lifts to
  CakeML-level evaluation via the candle/prover chain later.
*)
open HolKernel boolLib bossLib BasicProvers listTheory pairTheory
     systemTheory envelopeTheory safetyTheory sv_weakeningTheory;

val _ = new_theory "upgrade";

(* The proof obligation a self-proposed policy must discharge. *)
Definition admissible_def:
  admissible step safe oldp newp ⇔
    sound_policy step safe newp ∧ weaker newp oldp
End

(* The gate: install [newp] iff it discharged the obligation. *)
Definition admit_def:
  admit step safe oldp newp =
    if admissible step safe oldp newp then newp else oldp
End

(* The gate never produces an unsound policy from a sound one. *)
Theorem admit_keeps_sound:
  sound_policy step safe oldp ⇒
  sound_policy step safe (admit step safe oldp newp)
Proof
  rw[admit_def, admissible_def]
QED

(* Gate soundness: after a self-proposed upgrade, the enveloped system is
   still safe for EVERY controller — whether or not the proposal was
   accepted. *)
Theorem admit_preserves_safety:
  init_safe init safe ∧
  safe_shield step safe shield ∧
  sound_policy step safe oldp ⇒
  ∀ctrl. invariant step init
            (enveloped (admit step safe oldp newp) shield ctrl) safe
Proof
  rpt strip_tac >>
  irule safety_preservation >>
  metis_tac[admit_keeps_sound]
QED

(* Iterated self-improvement: fold a whole stream of proposals through the
   gate. Each is independently obligation-checked; soundness is invariant. *)
Definition admit_all_def:
  admit_all step safe p0 proposals = FOLDL (admit step safe) p0 proposals
End

Theorem admit_all_keeps_sound:
  ∀proposals p0.
    sound_policy step safe p0 ⇒
    sound_policy step safe (admit_all step safe p0 proposals)
Proof
  Induct >> rw[admit_all_def] >>
  fs[GSYM admit_all_def] >>
  first_x_assum irule >>
  metis_tac[admit_keeps_sound]
QED

(* The headline self-improvement theorem: NO finite sequence of
   self-proposed envelope weakenings — adversarial or not — can ever make
   the enveloped system unsafe, for any controller. Authority is earned by
   proof; safety is unconditional. *)
Theorem self_improvement_is_safe:
  init_safe init safe ∧
  safe_shield step safe shield ∧
  sound_policy step safe p0 ⇒
  ∀proposals ctrl.
    invariant step init
      (enveloped (admit_all step safe p0 proposals) shield ctrl) safe
Proof
  rpt strip_tac >>
  irule safety_preservation >>
  metis_tac[admit_all_keeps_sound]
QED

(* ===================================================================== *)
(*  THE OPERATIONAL GATE.                                                 *)
(*                                                                       *)
(*  `admit` above branches on the SEMANTIC predicate `admissible`, so it  *)
(*  is safe for every proposal whatsoever: no certifier appears in it,    *)
(*  and any theorem that routes through it cannot make a certifier's      *)
(*  soundness do work. A real gate does not consult the truth; it         *)
(*  consults a CERTIFICATE -- the boolean verdict some checker returned.  *)
(*  `gate cert oldp newp` installs [newp] iff the certifier said yes.     *)
(*  Everything below proves that soundness of the certifier, and only     *)
(*  that, is what protects safety -- and the necessity theorems show a    *)
(*  single unsound "yes" breaches it.                                     *)
(* ===================================================================== *)

Definition gate_def:
  gate (cert:bool) (oldp:('s,'a) policy) newp = if cert then newp else oldp
End

(* `admit` is the gate driven by a perfect (oracle) certifier. *)
Theorem admit_is_gate:
  admit step safe oldp newp = gate (admissible step safe oldp newp) oldp newp
Proof
  rw[admit_def, gate_def]
QED

Theorem gate_installs:
  cert ⇒ gate cert oldp newp = newp
Proof
  rw[gate_def]
QED

Theorem gate_rejects:
  ¬cert ⇒ gate cert oldp newp = oldp
Proof
  rw[gate_def]
QED

(* Safety through the operational gate: the ONLY thing asked of the
   certifier is that its "yes" is sound. *)
Theorem gate_keeps_sound:
  (cert ⇒ sound_policy step safe newp) ∧
  sound_policy step safe oldp ⇒
  sound_policy step safe (gate cert oldp newp)
Proof
  rw[gate_def]
QED

Theorem gate_preserves_safety:
  (cert ⇒ sound_policy step safe newp) ∧
  init_safe init safe ∧
  safe_shield step safe shield ∧
  sound_policy step safe oldp ⇒
  ∀ctrl. invariant step init (enveloped (gate cert oldp newp) shield ctrl) safe
Proof
  rpt strip_tac >>
  irule safety_preservation >>
  metis_tac[gate_keeps_sound]
QED

(* A certifier whose "yes" implies the full obligation gives BOTH halves:
   safety for every controller, and authority that only grows. *)
Theorem certified_gate_correct:
  (cert ⇒ admissible step safe oldp newp) ∧
  init_safe init safe ∧
  safe_shield step safe shield ∧
  sound_policy step safe oldp ⇒
  (∀ctrl. invariant step init (enveloped (gate cert oldp newp) shield ctrl)
                    safe) ∧
  weaker (gate cert oldp newp) oldp
Proof
  rpt strip_tac
  >- (irule gate_preserves_safety >> fs[admissible_def])
  >- (Cases_on ‘cert’ >> fs[gate_def, admissible_def, weaker_refl])
QED

(* --- the stream form: an unbounded sequence of certified proposals --- *)

Definition gate_all_def:
  (gate_all p0 [] = p0) ∧
  (gate_all p0 ((cert,newp)::rest) = gate_all (gate cert p0 newp) rest)
End

Theorem gate_all_keeps_sound:
  ∀proposals p0.
    EVERY (λ(cert,newp). cert ⇒ sound_policy step safe newp) proposals ∧
    sound_policy step safe p0 ⇒
    sound_policy step safe (gate_all p0 proposals)
Proof
  Induct >> simp[gate_all_def, pairTheory.FORALL_PROD] >>
  rpt strip_tac >> first_x_assum irule >> fs[] >>
  irule gate_keeps_sound >> fs[]
QED

Theorem gated_self_improvement_is_safe:
  EVERY (λ(cert,newp). cert ⇒ sound_policy step safe newp) proposals ∧
  init_safe init safe ∧
  safe_shield step safe shield ∧
  sound_policy step safe p0 ⇒
  ∀ctrl. invariant step init
            (enveloped (gate_all p0 proposals) shield ctrl) safe
Proof
  rpt strip_tac >>
  irule safety_preservation >>
  metis_tac[gate_all_keeps_sound]
QED

(* A certified stream: each "yes" certifies the full obligation against the
   policy actually in force at that point of the stream. *)
Definition certified_stream_def:
  (certified_stream step safe p [] ⇔ T) ∧
  (certified_stream step safe p ((cert,newp)::rest) ⇔
     (cert ⇒ admissible step safe p newp) ∧
     certified_stream step safe (gate cert p newp) rest)
End

(* Along a certified stream, soundness is kept AND authority only grows:
   the final policy is weaker than (at least as permissive as) the first. *)
Theorem certified_stream_grows_authority:
  ∀proposals p0.
    certified_stream step safe p0 proposals ∧
    sound_policy step safe p0 ⇒
    sound_policy step safe (gate_all p0 proposals) ∧
    weaker (gate_all p0 proposals) p0
Proof
  Induct >> simp[gate_all_def, certified_stream_def, pairTheory.FORALL_PROD,
                 weaker_refl] >>
  rpt gen_tac >> strip_tac >>
  ‘sound_policy step safe (gate p_1 p0 p_2) ∧ weaker (gate p_1 p0 p_2) p0’
    by (Cases_on ‘p_1’ >> fs[gate_def, admissible_def, weaker_refl]) >>
  first_x_assum drule_all >> metis_tac[weaker_trans]
QED

(* `admit_all` is `gate_all` over the certificate trace an oracle certifier
   would issue; that trace is a certified stream, so self_improvement_is_safe
   is the special case of the operational theory with a perfect certifier. *)
Definition admit_trace_def:
  (admit_trace step safe p [] = []) ∧
  (admit_trace step safe p (newp::rest) =
     (admissible step safe p newp, newp) ::
     admit_trace step safe (admit step safe p newp) rest)
End

Theorem admit_all_is_gate_all:
  ∀proposals p0.
    admit_all step safe p0 proposals =
    gate_all p0 (admit_trace step safe p0 proposals)
Proof
  Induct >> fs[admit_all_def, admit_trace_def, gate_all_def] >>
  rw[GSYM admit_is_gate]
QED

Theorem admit_trace_certified:
  ∀proposals p0.
    certified_stream step safe p0 (admit_trace step safe p0 proposals)
Proof
  Induct >> fs[admit_trace_def, certified_stream_def] >>
  rw[GSYM admit_is_gate]
QED

(* --- NECESSITY: the certifier's soundness is what protects safety ---
   A single unsound "yes" installs an unsound policy and the enveloped
   system leaves the safe set, although the old policy, the shield and the
   initial states are all sound. Witness over num: every action moves to
   that state; safe = {0}; the shield goes to 0; oldp permits only 0; newp
   permits everything; the controller always picks 1. *)
Theorem unsound_certificate_breaches:
  ∃(step:num -> num -> num) safe init shield oldp newp ctrl.
    init_safe init safe ∧
    safe_shield step safe shield ∧
    sound_policy step safe oldp ∧
    ¬sound_policy step safe newp ∧
    ¬invariant step init (enveloped (gate T oldp newp) shield ctrl) safe
Proof
  qexistsl_tac [‘λs a. a’, ‘λs. s = 0’, ‘λs. s = 0’, ‘λs. 0’,
                ‘λs a. a = 0’, ‘λs a. T’, ‘λs. 1’] >>
  simp[init_safe_def, safe_shield_def, sound_policy_def, invariant_def,
       gate_def] >>
  qexists_tac ‘1’ >> simp[] >>
  ‘reach (λs a. a) (λs. s = 0) (enveloped (λs a. T) (λs. 0) (λs. 1)) 0’
    by simp[Once reach_cases] >>
  drule reach_step >> simp[enveloped_def]
QED

(* NECESSITY of the weakening half: a certificate for a sound but
   non-weakening proposal takes authority away. *)
Theorem unweakening_certificate_revokes_authority:
  ∃(step:num -> num -> num) safe oldp newp.
    sound_policy step safe oldp ∧
    sound_policy step safe newp ∧
    ¬weaker (gate T oldp newp) oldp
Proof
  qexistsl_tac [‘λs a. s’, ‘λs. T’, ‘λs a. T’, ‘λs a. F’] >>
  rw[sound_policy_def, weaker_def, gate_def]
QED

val _ = export_theory ();
