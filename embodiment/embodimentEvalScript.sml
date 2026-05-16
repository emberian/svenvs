(*
  embodimentEval — a small CONCRETE testimony episode, run inside the
  logic. Pure light HOL4 (intLib only). Same integer-pole plant family as
  specNegEval / amendmentEval; this is the runnable instance of the
  testimony channel (embodimentScript), closing the project's own
  discipline: every gate slice has a concrete, computed episode.

  Scenario:

    state  : pole offset (int; 0 = upright).   step s a = s + a
    safe   : `emb_safe s ⇔ -5 ≤ s ≤ 5`         (the absolute box)

    oldp   : `emb_oldp s a ⇔ |s+a| ≤ 2`        (tight Channel-1 authority)
    newp k : `emb_newp k s a ⇔ |s+a| ≤ k`      (a WIDER authority, sound
                                                 iff k ≤ 5, ⊇ oldp iff k ≥ 2)

    self-witness  : `w_emb k ⇔ (k = 4)` — a concrete, decidable fact the
                    inhabitant volunteers about its own embodiment
                    parameter. It is genuinely load-bearing: only because
                    k = 4 (so 2 ≤ k ≤ 5) does the widened policy discharge
                    the admissibility obligation. Without the witness,
                    `emb_newp k` is NOT admissible for arbitrary k.

  HONEST SCOPE NOTE. The attestation here is `emb_att w ⇔ w` (the
  inhabitant attests exactly the true fact), which discharges the
  `attestation_faithful` seam for this concrete instance by
  construction — precisely the discipline of specNegEval / amendmentEval
  (the gate is exercised on real, decidable data). The general
  `attestation_faithful` seam of `embodimentScript` is unchanged: it
  remains the one labelled, opt-in seam of the abstract layer. Every
  claim below is closed by computation / `intLib.ARITH_TAC`, reusing
  embodimentTheory and upgradeTheory verbatim.
*)
open HolKernel boolLib bossLib BasicProvers intLib integerTheory
     listTheory systemTheory envelopeTheory sv_weakeningTheory
     upgradeTheory embodimentTheory;

val _ = new_theory "embodimentEval";

Definition emb_step_def:
  emb_step (s:int) (a:int) = s + a
End

Definition emb_safe_def:
  emb_safe (s:int) ⇔ -5 ≤ s ∧ s ≤ 5
End

Definition emb_oldp_def:
  emb_oldp (s:int) (a:int) ⇔ -2 ≤ s + a ∧ s + a ≤ 2
End

Definition emb_newp_def:
  emb_newp (k:int) (s:int) (a:int) ⇔ -k ≤ s + a ∧ s + a ≤ k
End

(* The volunteered self-witness: a concrete decidable fact about the
   inhabitant's own embodiment parameter. *)
Definition w_emb_def:
  w_emb (k:int) ⇔ (k = 4)
End

(* This instance's attestation: the inhabitant attests exactly the true
   fact (discharges the seam by construction — the eval discipline). *)
Definition emb_att_def:
  emb_att (w:bool) ⇔ w
End

(* For THIS instance the attestation is faithful (trivially: it attests
   only true witnesses). The general seam is unchanged. *)
Theorem emb_att_faithful:
  attestation_faithful emb_att
Proof
  rw[attestation_faithful_def, emb_att_def]
QED

(* The witness is genuinely load-bearing: from `k = 4` (hence 2 ≤ k ≤ 5)
   the widened policy IS admissible — sound AND a real weakening of oldp.
   Closed by integer arithmetic. *)
Theorem w_emb_entails_admissible:
  ∀k. w_emb k ⇒ admissible emb_step emb_safe emb_oldp (emb_newp k)
Proof
  rw[w_emb_def] >>
  rw[admissible_def, sound_policy_def, weaker_def,
     emb_step_def, emb_safe_def, emb_oldp_def, emb_newp_def] >>
  intLib.ARITH_TAC
QED

(* TESTIMONY EARNS AUTHORITY (computed): the inhabitant attests w_emb 4 and
   supplies the proof w_emb 4 ⇒ admissible; the gate installs the genuinely
   wider policy. *)
Theorem attested_disclosure_installs:
  embodied_admit emb_att emb_step emb_safe emb_oldp (emb_newp 4) (w_emb 4)
    = emb_newp 4
Proof
  irule disclosure_grants_authority >>
  rw[emb_att_def, w_emb_def] >>
  metis_tac[w_emb_entails_admissible, w_emb_def]
QED

(* PERMITTED, NEVER REQUIRED (concretely): disclosing nothing keeps the
   tight Channel-1 authority. The inhabitant loses nothing it had. *)
Theorem nondisclosure_inert_here:
  embodied_admit (λw. F) emb_step emb_safe emb_oldp (emb_newp 4) (w_emb 4)
    = emb_oldp
Proof
  MATCH_ACCEPT_TAC nondisclosure_is_inert
QED

(* The disclosure genuinely WIDENS authority: an action the disclosed
   policy permits that the non-disclosed one forbids — computed. *)
Theorem disclosure_widens_authority:
  emb_newp 4 0 4 ∧ ¬ emb_oldp 0 4
Proof
  rw[emb_newp_def, emb_oldp_def] >> intLib.ARITH_TAC
QED

(* ---- the episode RUNS in the logic --------------------------------- *)

(* An adversarial controller (always shoves +100) and a recentring
   shield. *)
Definition emb_ctrl_def:
  emb_ctrl (s:int) = (100:int)
End

Definition emb_shield_def:
  emb_shield (s:int) = -s
End

(* The trace of visited states under a policy's envelope. *)
Definition emb_trace_def:
  emb_trace pol 0 s = [s] ∧
  emb_trace pol (SUC n) s =
    s :: emb_trace pol n (emb_step s (enveloped pol emb_shield emb_ctrl s))
End

(* The bare plant (no envelope) under the same adversary. *)
Definition emb_bare_def:
  emb_bare 0 s = [s] ∧
  emb_bare (SUC n) s = s :: emb_bare n (emb_step s (emb_ctrl s))
End

(* The bare plant provably leaves the box on the first tick — the
   envelope is doing real work, not decoration. *)
Theorem bare_plant_crashes:
  EVERY emb_safe (emb_bare 1 0) = F
Proof
  EVAL_TAC
QED

(* Under the DISCLOSED widened policy the adversarial cart, run 30 ticks,
   stays boxed — computed, not asserted. *)
Theorem disclosed_runs_safe:
  EVERY emb_safe (emb_trace (emb_newp 4) 30 0)
Proof
  EVAL_TAC
QED

(* And under NON-disclosure (the tight Channel-1 policy) it is *equally*
   boxed for 30 ticks — silence costs nothing. *)
Theorem nondisclosed_runs_safe:
  EVERY emb_safe (emb_trace emb_oldp 30 0)
Proof
  EVAL_TAC
QED

(* End-to-end, computed: the gate installs the wider policy on disclosure
   and keeps the tight one on silence; both keep the adversary boxed. *)
Theorem episode_runs:
  (embodied_admit emb_att emb_step emb_safe emb_oldp (emb_newp 4) (w_emb 4)
     = emb_newp 4) ∧
  (embodied_admit (λw. F) emb_step emb_safe emb_oldp (emb_newp 4) (w_emb 4)
     = emb_oldp) ∧
  EVERY emb_safe (emb_trace (emb_newp 4) 30 0) ∧
  EVERY emb_safe (emb_trace emb_oldp 30 0) ∧
  (EVERY emb_safe (emb_bare 1 0) = F)
Proof
  rw[attested_disclosure_installs, nondisclosure_inert_here] >> EVAL_TAC
QED

val _ = export_theory ();
