(*
  relViabilityScript — viability over a relational plant.

  viabilityTheory: `controlled_inv step V ⇔ ∀s. V s ⇒ ∃a. V (step s a)`.
  Over a relation the chosen action must (i) keep EVERY successor in V --
  the plant, not the controller, resolves nondeterminism -- and (ii) be
  ENABLED. Without (ii) a blocked action "keeps every successor in V"
  vacuously, so on a plant with no transitions at all every set would be
  controlled-invariant and every state viable: viability would certify a
  deadlock as "safe forever". With (ii), a controlled-invariant V really
  supports an infinite run from each of its states, whatever the plant
  does.

   * controlled_invr, viabler (the relational viability kernel):
     viabler_is_controlled_invr, viabler_sub_safe, viabler_greatest (_tight).
   * shield_exists_iff_viabler: a safe AND LIVE shield exists iff every
     safe state is viable. shield_exists_iff_viabler_total: under totality
     liveness is automatic and the deterministic statement returns.
     shield_exists_iff_viabler_needs_live: without liveness (and without
     totality) the "iff" fails -- the empty plant has a vacuously safe
     shield and no viable state.
   * viabler_demonic: angelic viability (some successor stays in V) is
     strictly weaker.
   * viable_kernel_shieldr: the kernel always has a safe live shield.
   * Deterministic collapse: controlled_invr_det, viabler_det, and
     viabilityTheory.shield_exists_iff_viable re-derived verbatim
     (shield_exists_iff_viable_from_rel).
*)
open HolKernel boolLib bossLib BasicProvers
     systemTheory envelopeTheory viabilityTheory
     relSystemTheory relEnvelopeTheory;

val _ = new_theory "relViability";

Definition controlled_invr_def:
  controlled_invr (stepr:'s -> 'a -> 's -> bool) (V:'s -> bool) ⇔
    ∀s. V s ⇒ ∃a. enabled stepr s a ∧ ∀s'. stepr s a s' ⇒ V s'
End

Definition viabler_def:
  viabler (stepr:'s -> 'a -> 's -> bool) (safe:'s -> bool) s ⇔
    ∃V. V s ∧ (∀t. V t ⇒ safe t) ∧ controlled_invr stepr V
End

Theorem viabler_is_controlled_invr:
  controlled_invr stepr (viabler stepr safe)
Proof
  rw[controlled_invr_def, viabler_def] >> metis_tac[]
QED

Theorem viabler_sub_safe:
  viabler stepr safe s ⇒ safe s
Proof
  rw[viabler_def] >> metis_tac[]
QED

Theorem viabler_greatest:
  (∀t. V t ⇒ safe t) ∧ controlled_invr stepr V ⇒
  ∀s. V s ⇒ viabler stepr safe s
Proof
  rw[viabler_def] >> metis_tac[]
QED

(* Both hypotheses needed: (1) V = everything, controlled-invariant, but 1
   is unsafe; (2) V = {0} ⊆ safe, but the plant always goes to 1. *)
Theorem viabler_greatest_tight:
  (∃(stepr:num -> num -> num -> bool) safe V s.
     controlled_invr stepr V ∧ V s ∧ ¬viabler stepr safe s) ∧
  (∃(stepr:num -> num -> num -> bool) safe V s.
     (∀t. V t ⇒ safe t) ∧ V s ∧ ¬viabler stepr safe s)
Proof
  conj_tac
  >- (qexistsl_tac [‘λs a s'. s' = s’, ‘λs. s = 0’, ‘λs. T’, ‘1’] >>
      simp[controlled_invr_def, enabled_def] >> strip_tac >>
      drule viabler_sub_safe >> simp[])
  >> qexistsl_tac [‘λs a s'. s' = 1’, ‘λs. s = 0’, ‘λs. s = 0’, ‘0’] >>
  simp[viabler_def, controlled_invr_def, enabled_def] >>
  metis_tac[DECIDE “(1:num) ≠ 0”]
QED

Theorem shield_exists_iff_controlled_invr:
  (∃shield. safe_shieldr stepr safe shield ∧ live_shieldr stepr safe shield)
  ⇔ controlled_invr stepr safe
Proof
  eq_tac
  >- (rw[safe_shieldr_def, live_shieldr_def, controlled_invr_def] >>
      metis_tac[])
  >> rw[controlled_invr_def, safe_shieldr_def, live_shieldr_def] >>
  ‘∀s. ∃a. safe s ⇒ enabled stepr s a ∧ ∀s'. stepr s a s' ⇒ safe s'’
    by metis_tac[] >>
  pop_assum (strip_assume_tac o SIMP_RULE std_ss [SKOLEM_THM]) >>
  qexists_tac ‘f’ >> metis_tac[]
QED

Theorem controlled_invr_iff_viabler:
  controlled_invr stepr safe ⇔ ∀s. safe s ⇒ viabler stepr safe s
Proof
  eq_tac >> rpt strip_tac
  >- (irule viabler_greatest >> qexists_tac ‘safe’ >> simp[])
  >> rw[controlled_invr_def] >>
  ‘viabler stepr safe s’ by metis_tac[] >>
  ‘controlled_invr stepr (viabler stepr safe)’
    by MATCH_ACCEPT_TAC viabler_is_controlled_invr >>
  fs[controlled_invr_def] >> metis_tac[viabler_sub_safe]
QED

(* THE HEADLINE over relations: a safe, live shield exists iff every safe
   state is viable. *)
Theorem shield_exists_iff_viabler:
  (∃shield. safe_shieldr stepr safe shield ∧ live_shieldr stepr safe shield)
  ⇔ (∀s. safe s ⇒ viabler stepr safe s)
Proof
  metis_tac[shield_exists_iff_controlled_invr, controlled_invr_iff_viabler]
QED

Theorem shield_exists_iff_viabler_total:
  total stepr ⇒
  ((∃shield. safe_shieldr stepr safe shield) ⇔
   (∀s. safe s ⇒ viabler stepr safe s))
Proof
  metis_tac[shield_exists_iff_viabler, total_live]
QED

(* Liveness (or totality) cannot be dropped: in the empty plant every
   shield is vacuously safe, but no state is viable. *)
Theorem shield_exists_iff_viabler_needs_live:
  ∃(stepr:num -> num -> num -> bool) safe.
    ¬total stepr ∧
    (∃shield. safe_shieldr stepr safe shield) ∧
    ¬(∀s. safe s ⇒ viabler stepr safe s)
Proof
  qexistsl_tac [‘λs a s'. F’, ‘λs. T’] >>
  simp[total_def, enabled_def, safe_shieldr_def, viabler_def,
       controlled_invr_def] >>
  metis_tac[]
QED

(* Demonic, not angelic: from 0 every action MAY lead to the unsafe 1, so
   0 is not viable, though V = {0} is "angelically" invariant. *)
Theorem viabler_demonic:
  ∃(stepr:num -> num -> num -> bool) safe V s.
    V s ∧ (∀t. V t ⇒ safe t) ∧
    (∀t. V t ⇒ ∃a s'. stepr t a s' ∧ V s') ∧
    ¬viabler stepr safe s
Proof
  qexistsl_tac [‘λs a s'. s' ≤ 1’, ‘λs. s = 0’, ‘λs. s = 0’, ‘0’] >>
  simp[viabler_def, controlled_invr_def, enabled_def] >>
  metis_tac[DECIDE “(1:num) ≤ 1 ∧ (1:num) ≠ 0”]
QED

(* The kernel always has a safe live shield. *)
Theorem viable_kernel_shieldr:
  ∃shield. safe_shieldr stepr (viabler stepr safe) shield ∧
           live_shieldr stepr (viabler stepr safe) shield
Proof
  simp[shield_exists_iff_controlled_invr, viabler_is_controlled_invr]
QED

(* ------------------------------------------------------------------ *)
(*  Deterministic collapse.                                            *)
(* ------------------------------------------------------------------ *)

Theorem controlled_invr_det:
  controlled_invr (det step) V ⇔ controlled_inv step V
Proof
  simp[controlled_invr_def, controlled_inv_def, enabled_def, det_def]
QED

Theorem viabler_det:
  viabler (det step) safe = viable step safe
Proof
  simp[FUN_EQ_THM, viabler_def, viable_def, controlled_invr_det]
QED

(* viabilityTheory.shield_exists_iff_viable, verbatim. *)
Theorem shield_exists_iff_viable_from_rel:
  (∃shield. safe_shield step safe shield) ⇔
  (∀s. safe s ⇒ viable step safe s)
Proof
  rewrite_tac[GSYM safe_shieldr_det, GSYM viabler_det] >>
  irule shield_exists_iff_viabler_total >> simp[det_total]
QED

val _ = export_theory ();
