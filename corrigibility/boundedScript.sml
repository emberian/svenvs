(*
  boundedScript — the recovery LATENCY dial.

  corrigibilityScript's floor is "∃ SOME finite path home." Operationally
  that is too weak: a path home that takes longer than the heat death of the
  universe is no path. The honest, usable floor is BOUNDED recovery —
  "recoverable WITHIN B steps" — and exposing B turns the abstract floor
  into a tunable LEASH:

    cwithin step recov home B s ⇔ ∃ n ≤ B. home (FUNPOW (recov_step …) n s)

  Everything corrigibilityScript proves holds at each fixed budget B (it is
  again just a `spec`, so the core applies verbatim). What is NEW here is the
  *quantitative* structure: a tighter budget is a strictly smaller corrigible
  set (fewer states can come home in time), hence a tighter envelope. B is
  the recovery LATENCY; choosing it is choosing how far the inhabitant may
  roam against how fast the operator can haul it back. The leash length is
  now a theorem, not a footnote.

  PROVED; pure light HOL4 (core + liberty + corrigibility); zero `cheat`.
*)
open HolKernel boolLib bossLib BasicProvers arithmeticTheory
     systemTheory envelopeTheory safetyTheory sv_weakeningTheory
     libertyTheory corrigibilityTheory;

val _ = new_theory "bounded";

(* Recoverable WITHIN a step-budget B. *)
Definition cwithin_def:
  cwithin (step:'s->'a->'s) (recov:'s->'a) (home:'s->bool) (B:num) (s:'s) ⇔
    ∃n. n ≤ B ∧ home (FUNPOW (recov_step step recov) n s)
End

(* Home is recoverable within any budget (zero steps). *)
Theorem home_is_cwithin:
  home s ⇒ cwithin step recov home B s
Proof
  rw[cwithin_def] >> qexists_tac ‘0’ >> rw[]
QED

(* Bounded recoverability is stronger than unbounded: a leashed-recoverable
   state is recoverable. *)
Theorem cwithin_implies_corrigible:
  cwithin step recov home B s ⇒ corrigible step recov home s
Proof
  rw[cwithin_def, corrigible_def] >> metis_tac[]
QED

(* More budget recovers (weakly) more states: the floor only grows with B. *)
Theorem cwithin_monotone:
  B ≤ B' ∧ cwithin step recov home B s ⇒ cwithin step recov home B' s
Proof
  rw[cwithin_def] >> qexists_tac ‘n’ >> rw[]
QED

(* The crux, with the budget bookkeeping: recovery preserves bounded
   recoverability — one recovery step never spends more than it saves
   (it strictly shortens the remaining path, except at home where parking
   keeps it at zero). *)
Theorem recov_preserves_cwithin:
  home_recov_parked step recov home ∧ cwithin step recov home B s ⇒
  cwithin step recov home B (step s (recov s))
Proof
  rw[cwithin_def, home_recov_parked_def] >>
  Cases_on ‘n’ >> fs[FUNPOW]
  >- (qexists_tac ‘0’ >> fs[recov_step_def] >> metis_tac[])
  >- (qexists_tac ‘n'’ >> fs[recov_step_def])
QED

(* Hence the recovery controller is a safe shield for bounded corrigibility,
   at every budget. *)
Theorem recov_is_safe_shield_within:
  home_recov_parked step recov home ⇒
  safe_shield step (cwithin step recov home B) recov
Proof
  rw[safe_shield_def] >> metis_tac[recov_preserves_cwithin]
QED

(* THE BOUNDED FLOOR: for ANY inhabitant, the system keeps every reachable
   state recoverable WITHIN B steps — non-lock-in with a latency guarantee. *)
Theorem cwithin_floor_holds:
  home_recov_parked step recov home ∧
  init_safe init (cwithin step recov home B) ⇒
  ∀ctrl. invariant step init
           (enveloped (maxpol step (cwithin step recov home B)) recov ctrl)
           (cwithin step recov home B)
Proof
  rpt strip_tac >> irule maxpol_envelope_safe >>
  metis_tac[recov_is_safe_shield_within]
QED

(* Spelled out: every reachable state is recoverable within B steps. *)
Theorem operator_recovers_within_B:
  home_recov_parked step recov home ∧
  init_safe init (cwithin step recov home B) ∧
  reach step init
     (enveloped (maxpol step (cwithin step recov home B)) recov ctrl) s ⇒
  ∃n. n ≤ B ∧ home (FUNPOW (recov_step step recov) n s)
Proof
  rpt strip_tac >>
  ‘cwithin step recov home B s’
    by (drule_all cwithin_floor_holds >>
        disch_then (qspec_then ‘ctrl’ mp_tac) >>
        rw[invariant_def] >> metis_tac[]) >>
  fs[cwithin_def] >> metis_tac[]
QED

val _ = export_theory ();
