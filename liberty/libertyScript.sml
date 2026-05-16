(*
  libertyScript — the prison question, answered as a theorem.

  svenvs has always answered "isn't this just a cage?" in prose. This file
  answers it in HOL4. The center (CLAIMS.md): the inhabitant is the
  UNCONSTRAINED term in every theorem — the proof never reasons about it.
  The remaining honest worry is the *opposite* of distrust: is the envelope
  gratuitously restrictive? A cage that forbids more than safety strictly
  requires would indeed be a prison.

  We prove it is not. Define the MAXIMAL sound policy `maxpol`: permit an
  action exactly when, from a safe state, it preserves safety (from an
  unsafe state it permits everything — `sound_policy` only ever constrains
  behaviour from safe states, and only safe states are ever reachable).
  Then:

   * `maxpol_sound`              — it is sound.
   * `maxpol_is_greatest_sound`  — every sound policy is a RESTRICTION of it
                                   (it is the unique ⊆-greatest sound policy).
   * `envelope_is_least_restrictive` — the headline: any policy that permits,
       from a safe state, an action `maxpol` forbids is UNSOUND. Every
       restriction the envelope imposes is load-bearing: remove any one and
       the world is provably unsafe for *some* inhabitant. The cage has the
       largest interior any sound cage can have.
   * `envelope_never_overrides_safe_action` — the door is open whenever the
       floor holds: a controller proposing a safe action is passed through
       untouched, never gratuitously shielded (non-vacuity / no starvation).
   * `envelope_overrides_only_unsafe` — and the envelope acts ONLY on actions
       that would actually break safety (it is not decoration; pairs with
       the cartpole's executed `chaos_*` demonstrations).
   * `maxpol_envelope_safe` — and with this maximal policy the FULL safety
       guarantee still holds for every inhabitant: maximal autonomy and
       safety simultaneously, no trade-off.

  Pure light HOL4 (core deps only); instance-independent, so it is the
  answer for *every* svenvs instance, not one demo. Zero cheats.
*)
open HolKernel boolLib bossLib BasicProvers
     systemTheory envelopeTheory safetyTheory sv_weakeningTheory;

val _ = new_theory "liberty";

(* The maximal sound policy: from a safe state, permit exactly the
   safety-preserving actions; from an unsafe state, permit anything
   (vacuous — unsafe states are never reachable under the envelope, and
   `sound_policy` only constrains transitions out of safe states). This is
   the weakest policy that is still sound: the largest interior a sound
   cage can have. *)
Definition maxpol_def:
  maxpol step safe : ('s,'a)policy = λ s a. safe s ⇒ safe (step s a)
End

Theorem maxpol_sound:
  sound_policy step safe (maxpol step safe)
Proof
  rw[sound_policy_def, maxpol_def]
QED

(* Maximality: nothing a sound policy permits is forbidden by maxpol, so
   maxpol is the unique ⊆-greatest sound policy. *)
Theorem maxpol_is_greatest_sound:
  sound_policy step safe pol ⇒ weaker (maxpol step safe) pol
Proof
  rw[weaker_def, maxpol_def] >> fs[sound_policy_def] >> metis_tac[]
QED

(* THE HEADLINE — the formal answer to "isn't this a prison?".
   Three conjuncts: maxpol is sound; it is the greatest sound policy; and
   every restriction it imposes is FORCED — any policy that, from a safe
   state, permits an action maxpol forbids is unsound, i.e. it admits an
   action that breaks safety for some inhabitant. There is no slack: every
   bar in the cage is load-bearing. *)
Theorem envelope_is_least_restrictive:
  sound_policy step safe (maxpol step safe) ∧
  (∀pol. sound_policy step safe pol ⇒ weaker (maxpol step safe) pol) ∧
  (∀q s a. safe s ∧ q s a ∧ ¬ maxpol step safe s a ⇒
           ¬ sound_policy step safe q)
Proof
  rpt conj_tac
  >- MATCH_ACCEPT_TAC maxpol_sound
  >- MATCH_ACCEPT_TAC maxpol_is_greatest_sound
  >- (rpt strip_tac >> fs[sound_policy_def, maxpol_def] >> metis_tac[])
QED

(* Non-vacuity / no starvation: the envelope NEVER overrides a controller
   action that was already safe — a controller proposing safe actions runs
   completely unimpeded. "You may go anywhere the floor provably holds." *)
Theorem envelope_never_overrides_safe_action:
  safe s ∧ safe (step s (ctrl s)) ⇒
  enveloped (maxpol step safe) shield ctrl s = ctrl s
Proof
  rw[enveloped_def, maxpol_def] >> fs[]
QED

(* And conversely the envelope acts ONLY when the controller's own action
   would actually break safety from a safe state — it is doing real work,
   not decoration (pairs with cartpole's executed chaos demonstrations). *)
Theorem envelope_overrides_only_unsafe:
  enveloped (maxpol step safe) shield ctrl s ≠ ctrl s ⇒
  safe s ∧ ¬ safe (step s (ctrl s))
Proof
  rw[enveloped_def, maxpol_def] >>
  Cases_on ‘safe s ⇒ safe (step s (ctrl s))’ >> fs[]
QED

(* The punchline: with the MAXIMALLY permissive sound policy the full
   safety-preservation guarantee still holds for every inhabitant. Maximal
   autonomy and safety hold simultaneously — there is no trade-off, and the
   guarantee is exactly the original `safety_preservation`. *)
Theorem maxpol_envelope_safe:
  init_safe init safe ∧ safe_shield step safe shield ⇒
  ∀ctrl. invariant step init (enveloped (maxpol step safe) shield ctrl) safe
Proof
  rpt strip_tac >> irule safety_preservation >>
  metis_tac[maxpol_sound]
QED

val _ = export_theory ();
