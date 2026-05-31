(*
  corrigibilityScript — the floor you can actually decide.

  --------------------------------------------------------------------------
  THE PROBLEM THIS ANSWERS

  Every svenvs theorem is relative to a safety predicate `safe`. The tower
  (policy -> spec -> meta -> root) lets `safe` itself move, but only ever
  *above some fixed floor* — and deciding the CONTENT of that floor is the
  one thing no proof can do for you (the spec-faithfulness gap). "What is
  the right envelope?" is genuinely hard.

  The reframe: do not try to write down a positive `safe` ("what is good").
  Write down only a NEGATIVE, CORRIGIBILITY floor — "the operator can always
  still bring me home" — and let everything above it be discovered safely.
  This floor is *cheaper to specify* (you give a home set and a recovery
  controller; corrigibility is then DERIVED) and, for a finite habitat,
  DECIDABLE (the watchdog discipline), so it discharges Mac-light.

  --------------------------------------------------------------------------
  THE KEY OBSERVATION

  Corrigibility is NOT new metatheory. It is the existing envelope
  instantiated at one particular spec:

      safe(s)  :=  corrigible(s)  :=  "the recovery controller `recov`
                   can drive s back into `home` in finitely many steps"

  and the recovery controller IS the shield. So the whole proved core
  (safety_preservation, maxpol, liberty) applies VERBATIM. Nothing here is
  re-proved; it is the right instantiation, plus the one lemma that makes
  the recovery controller a safe shield for its own corrigibility predicate.

  WHAT IS PROVED (all from the built core + liberty; no `cheat`):
   * corrigibility is a genuine state predicate (a `spec`), inhabited
     wherever `home` is (`home_is_corrigible`);
   * the recovery controller is a safe shield FOR CORRIGIBILITY, under one
     mild, natural premise (`home_recov_parked`: recovery parks at home)
     (`recov_is_safe_shield`);
   * NON-LOCK-IN (headline): for ANY inhabitant, the corrigibility-enveloped
     system keeps every reachable state corrigible — the operator can never
     be locked out (`corrigibility_floor_holds`,
     `operator_can_always_recover`);
   * the floor is the MAXIMAL one (`corrigibility_envelope_is_least_
     restrictive`): every action the envelope blocks is EXACTLY one that
     would burn the last bridge home (`override_is_exactly_a_burned_bridge`),
     and a move that keeps a path home runs unimpeded
     (`free_action_runs_unimpeded`). The cage is precisely "no one-way
     doors", nothing more.

  Pure light HOL4 (core + liberty only); instance-independent. Zero cheats.
*)
open HolKernel boolLib bossLib BasicProvers arithmeticTheory
     systemTheory envelopeTheory safetyTheory sv_weakeningTheory
     libertyTheory;

val _ = new_theory "corrigibility";

(* The recovery dynamics: one step of the recovery controller `recov`. *)
Definition recov_step_def:
  recov_step (step:'s->'a->'s) (recov:'s->'a) (s:'s) = step s (recov s)
End

(* CORRIGIBLE: state `s` is non-bricked iff the recovery controller can
   drive it back into the home set in finitely many steps. This is a plain
   state predicate (`:'s -> bool`) — i.e. a svenvs `spec`/`safe` — so it
   plugs into the entire core unchanged. *)
Definition corrigible_def:
  corrigible (step:'s->'a->'s) (recov:'s->'a) (home:'s->bool) (s:'s) ⇔
    ∃n. home (FUNPOW (recov_step step recov) n s)
End

(* The one mild, natural premise: once home, recovery keeps you home (the
   recovery controller does not wander back out of the home set). This is
   the only thing asked of the recovery controller; everything else is free. *)
Definition home_recov_parked_def:
  home_recov_parked (step:'s->'a->'s) (recov:'s->'a) (home:'s->bool) ⇔
    ∀s. home s ⇒ home (step s (recov s))
End

(* Corrigibility is inhabited wherever home is (witness: zero steps). So the
   floor is never vacuous — a home set makes corrigibility satisfiable. *)
Theorem home_is_corrigible:
  home s ⇒ corrigible step recov home s
Proof
  rw[corrigible_def] >> qexists_tac ‘0’ >> rw[]
QED

(* The crux: recovery preserves corrigibility. From a state recovery can
   bring home, the recovery successor is still one recovery can bring home.
   This is what makes `recov` a SAFE SHIELD for its own corrigibility. *)
Theorem recov_preserves_corrigible:
  home_recov_parked step recov home ∧ corrigible step recov home s ⇒
  corrigible step recov home (step s (recov s))
Proof
  rw[corrigible_def, home_recov_parked_def] >>
  Cases_on ‘n’ >> fs[FUNPOW]
  >- (qexists_tac ‘0’ >> fs[recov_step_def] >> metis_tac[])
  >- (qexists_tac ‘n'’ >> fs[recov_step_def])
QED

(* Hence the recovery controller is a safe shield FOR CORRIGIBILITY — the
   shield obligation of the core, discharged once, generically. *)
Theorem recov_is_safe_shield:
  home_recov_parked step recov home ⇒
  safe_shield step (corrigible step recov home) recov
Proof
  rw[safe_shield_def] >> metis_tac[recov_preserves_corrigible]
QED

(* ===================================================================== *)
(* THE HEADLINE: NON-LOCK-IN.                                            *)
(* For ANY inhabitant, running at the maximal corrigibility-preserving   *)
(* policy with the recovery controller as shield, every reachable state  *)
(* is still corrigible — the operator can never be locked out. This is   *)
(* safety_preservation/maxpol_envelope_safe at safe := corrigible,       *)
(* shield := recov. The core is reused, not re-proved.                   *)
(* ===================================================================== *)
Theorem corrigibility_floor_holds:
  home_recov_parked step recov home ∧
  init_safe init (corrigible step recov home) ⇒
  ∀ctrl. invariant step init
           (enveloped (maxpol step (corrigible step recov home)) recov ctrl)
           (corrigible step recov home)
Proof
  rpt strip_tac >> irule maxpol_envelope_safe >>
  metis_tac[recov_is_safe_shield]
QED

(* Spelled-out: every reachable state has a finite recovery path home —
   the operator's recovery move always still works. *)
Theorem operator_can_always_recover:
  home_recov_parked step recov home ∧
  init_safe init (corrigible step recov home) ∧
  reach step init
     (enveloped (maxpol step (corrigible step recov home)) recov ctrl) s ⇒
  ∃n. home (FUNPOW (recov_step step recov) n s)
Proof
  rpt strip_tac >>
  ‘corrigible step recov home s’
    by (drule_all corrigibility_floor_holds >>
        disch_then (qspec_then ‘ctrl’ mp_tac) >>
        rw[invariant_def] >> metis_tac[]) >>
  fs[corrigible_def] >> metis_tac[]
QED

(* ===================================================================== *)
(* THE FLOOR IS THE MAXIMAL ONE — every bar is a one-way door.           *)
(* ===================================================================== *)

(* The corrigibility envelope is the LEAST restrictive sound one: it is
   the greatest corrigibility-sound policy, and any policy permitting an
   action it forbids is unsound. Instantiation of liberty's headline. *)
Theorem corrigibility_envelope_is_least_restrictive:
  sound_policy step (corrigible step recov home)
                    (maxpol step (corrigible step recov home)) ∧
  (∀pol. sound_policy step (corrigible step recov home) pol ⇒
         weaker (maxpol step (corrigible step recov home)) pol) ∧
  (∀q s a. corrigible step recov home s ∧ q s a ∧
           ¬ maxpol step (corrigible step recov home) s a ⇒
           ¬ sound_policy step (corrigible step recov home) q)
Proof
  metis_tac[envelope_is_least_restrictive]
QED

(* The envelope overrides EXACTLY the actions that would strand the system:
   if it shields, the controller's action would have made the state
   non-corrigible (burned the last bridge home). Real work, not a cage. *)
Theorem override_is_exactly_a_burned_bridge:
  enveloped (maxpol step (corrigible step recov home)) recov ctrl s ≠ ctrl s ⇒
  corrigible step recov home s ∧
  ¬ corrigible step recov home (step s (ctrl s))
Proof
  metis_tac[envelope_overrides_only_unsafe]
QED

(* And conversely: a controller action that keeps a path home runs
   unimpeded — the door is open whenever the bridge is intact. *)
Theorem free_action_runs_unimpeded:
  corrigible step recov home s ∧
  corrigible step recov home (step s (ctrl s)) ⇒
  enveloped (maxpol step (corrigible step recov home)) recov ctrl s = ctrl s
Proof
  metis_tac[envelope_never_overrides_safe_action]
QED

val _ = export_theory ();
