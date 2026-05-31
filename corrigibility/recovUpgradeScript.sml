(*
  recovUpgradeScript — the inhabitant may rewrite its own off-switch, and
  still can never weaken it.

  --------------------------------------------------------------------------
  WHAT THIS EARNS

  corrigibilityScript proves non-lock-in *assuming* the recovery controller
  `recov` is fixed and outside the inhabitant's reach — i.e. it assumes the
  off-switch is sacred. That assumption is doing enormous load-bearing work
  for a *self-modifying* inhabitant, which could otherwise just rewrite
  `recov` into something that no longer brings it home.

  Here we DISCHARGE that assumption by construction. `recov` becomes a
  MUTABLE artifact the inhabitant may propose to replace — gated so that a
  replacement is admitted ONLY if it (1) still parks at home and (2) recovers
  at least every state the old one did. A proposal that would lose
  recoverability is rejected; the old controller is kept. Hence:

    NO sequence of self-proposed recovery-controller rewrites — adversarial
    or not — can ever make a previously-recoverable state unrecoverable.
    The off-switch can be UPGRADED but never WEAKENED, even by the
    inhabitant itself.

  --------------------------------------------------------------------------
  NO LÖB (the asymmetry)

  `home` — the GOAL, what "recovered / operator-in-control" MEANS — is the
  frozen root and never moves. `recov` — the MECHANISM, *how* you get home —
  is mutable. A fixed `home` plus the monotonicity check vouching for a
  mutable `recov` is a fixed lower property vouching for a higher mutable
  artifact (the selfprover/genealogy asymmetry), NOT a controller vouching
  for itself. So this layer needs no reflection principle and no Löb. The
  only thing that stays frozen is the values-choice (`home`); everything
  mechanical above it self-improves under the gate.

  This is the honest residual, stated plainly: we do not prove `home` is the
  right home (that an operator truly controls it, that the inhabitant cannot
  manipulate it). We prove that, given a frozen `home`, the inhabitant can
  rewrite everything about *how* it returns there and never lose the ability
  to return. PROVED; pure light HOL4 (core + liberty + corrigibility); zero
  cheat.
*)
open HolKernel boolLib bossLib BasicProvers listTheory
     systemTheory envelopeTheory safetyTheory sv_weakeningTheory
     libertyTheory corrigibilityTheory;

val _ = new_theory "recovUpgrade";

(* The proof obligation a self-proposed recovery controller must discharge:
   (1) it still parks at home, and (2) it recovers AT LEAST every state the
   current one does (a genuine non-weakening — more recovery power is fine,
   less is rejected). Exactly upgradeTheory.admissible in shape, for the
   recovery primitive instead of the policy. *)
Definition recov_admissible_def:
  recov_admissible step home oldrec newrec ⇔
    home_recov_parked step newrec home ∧
    (∀s. corrigible step oldrec home s ⇒ corrigible step newrec home s)
End

(* The gate: install the proposed controller iff it discharged the
   obligation, else keep the current one. An unproven proposal can never
   move the off-switch. *)
Definition recov_admit_def:
  recov_admit step home oldrec newrec =
    if recov_admissible step home oldrec newrec then newrec else oldrec
End

(* The gate keeps the parking invariant. *)
Theorem recov_admit_keeps_parked:
  home_recov_parked step oldrec home ⇒
  home_recov_parked step (recov_admit step home oldrec newrec) home
Proof
  rw[recov_admit_def, recov_admissible_def]
QED

(* The gate never loses recoverability: anything the old controller could
   bring home, the gate's result can bring home. *)
Theorem recov_admit_preserves_corrigible:
  corrigible step oldrec home s ⇒
  corrigible step (recov_admit step home oldrec newrec) home s
Proof
  rw[recov_admit_def, recov_admissible_def] >> metis_tac[]
QED

(* A swap that would lose recoverability (or fail to park) is INERT: it is
   dropped, the old controller stays in force. "You tried to weaken your own
   off-switch; the floor said no." *)
Theorem unrecoverable_swap_is_inert:
  ¬ recov_admissible step home oldrec newrec ⇒
  recov_admit step home oldrec newrec = oldrec
Proof
  rw[recov_admit_def]
QED

(* Iterate: fold a whole adversarial STREAM of recovery-controller rewrites
   through the gate. Each is independently obligation-checked. *)
Definition recov_admit_all_def:
  recov_admit_all step home rec0 proposals =
    FOLDL (recov_admit step home) rec0 proposals
End

Theorem recov_admit_all_keeps_parked:
  ∀proposals rec0.
    home_recov_parked step rec0 home ⇒
    home_recov_parked step (recov_admit_all step home rec0 proposals) home
Proof
  Induct >> rw[recov_admit_all_def] >>
  fs[GSYM recov_admit_all_def] >>
  first_x_assum irule >>
  metis_tac[recov_admit_keeps_parked]
QED

(* THE OFF-SWITCH CAN NEVER BE WEAKENED BY SELF-MODIFICATION: any state
   recoverable at genesis is still recoverable after ANY admitted stream of
   the inhabitant's own recovery-controller rewrites. *)
Theorem self_modification_never_weakens_recoverability:
  ∀proposals rec0 s.
    corrigible step rec0 home s ⇒
    corrigible step (recov_admit_all step home rec0 proposals) home s
Proof
  Induct >> rw[recov_admit_all_def] >>
  fs[GSYM recov_admit_all_def] >>
  first_x_assum irule >>
  metis_tac[recov_admit_preserves_corrigible]
QED

(* ===================================================================== *)
(* THE HEADLINE.                                                         *)
(* The inhabitant rewrites its own recovery mechanism by an arbitrary    *)
(* admitted stream of proposals, AND drives the plant with any           *)
(* controller — and the system still keeps every reachable state         *)
(* recoverable (w.r.t. the self-modified recovery controller now in      *)
(* force). Self-modification of the off-switch + adversarial control,    *)
(* and non-lock-in survives both.                                        *)
(* ===================================================================== *)
Theorem self_modifying_recovery_preserves_corrigibility:
  home_recov_parked step rec0 home ∧
  init_safe init (corrigible step rec0 home) ⇒
  ∀proposals ctrl.
    invariant step init
      (enveloped
         (maxpol step (corrigible step (recov_admit_all step home rec0 proposals) home))
         (recov_admit_all step home rec0 proposals) ctrl)
      (corrigible step (recov_admit_all step home rec0 proposals) home)
Proof
  rpt strip_tac >>
  irule corrigibility_floor_holds >>
  conj_tac
  >- (fs[init_safe_def] >>
      metis_tac[self_modification_never_weakens_recoverability])
  >- metis_tac[recov_admit_all_keeps_parked]
QED

val _ = export_theory ();
