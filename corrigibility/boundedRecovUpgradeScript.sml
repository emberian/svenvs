(*
  boundedRecovUpgradeScript — rewrite your off-switch, keep the DEADLINE.

  recovUpgradeScript proved the inhabitant cannot self-modify its recovery
  controller into one that LOSES recoverability. But that left a subtler
  attack open: a replacement that still brings the system home *eventually*,
  yet so slowly that the deadline is blown — recovery that takes longer than
  anyone can wait is lock-in by another name.

  This file closes it, by gating recovery-controller rewrites against the
  BOUNDED floor (`bounded : cwithin … B`): a swap is admitted only if the new
  controller (1) still parks at home and (2) recovers WITHIN THE SAME BUDGET
  B everything the old one did within B. Hence:

    NO sequence of self-proposed recovery-controller rewrites can ever
    INCREASE recovery latency past B for a previously-in-budget state. The
    off-switch can be made faster, never slower than the deadline.

  Mechanically this is recovUpgradeScript with the spec `corrigible` replaced
  by `cwithin … B` — `cwithin … B` is just another `spec`, and B never moves,
  so the gate machinery lifts verbatim. The frozen root is still `home` (and
  now the deadline B); no Löb. PROVED; pure light HOL4
  (core + liberty + corrigibility + bounded); zero `cheat`.
*)
open HolKernel boolLib bossLib BasicProvers listTheory
     systemTheory envelopeTheory safetyTheory sv_weakeningTheory
     libertyTheory corrigibilityTheory boundedTheory;

val _ = new_theory "boundedRecovUpgrade";

(* A recovery-controller rewrite is admissible at budget B iff the new
   controller still parks at home AND recovers, WITHIN B steps, at least
   every state the old one did within B. (recovUpgrade.recov_admissible with
   the deadline added.) *)
Definition recov_admissible_B_def:
  recov_admissible_B step home B oldrec newrec ⇔
    home_recov_parked step newrec home ∧
    (∀s. cwithin step oldrec home B s ⇒ cwithin step newrec home B s)
End

Definition recov_admit_B_def:
  recov_admit_B step home B oldrec newrec =
    if recov_admissible_B step home B oldrec newrec then newrec else oldrec
End

Theorem recov_admit_B_keeps_parked:
  home_recov_parked step oldrec home ⇒
  home_recov_parked step (recov_admit_B step home B oldrec newrec) home
Proof
  rw[recov_admit_B_def, recov_admissible_B_def]
QED

(* The gate never increases latency: anything the old controller brought home
   within B, the gate's result brings home within B. *)
Theorem recov_admit_B_preserves_cwithin:
  cwithin step oldrec home B s ⇒
  cwithin step (recov_admit_B step home B oldrec newrec) home B s
Proof
  rw[recov_admit_B_def, recov_admissible_B_def] >> metis_tac[]
QED

(* A swap that would blow the deadline (or fail to park) is inert. *)
Theorem slow_swap_is_inert:
  ¬ recov_admissible_B step home B oldrec newrec ⇒
  recov_admit_B step home B oldrec newrec = oldrec
Proof
  rw[recov_admit_B_def]
QED

Definition recov_admit_all_B_def:
  recov_admit_all_B step home B rec0 proposals =
    FOLDL (recov_admit_B step home B) rec0 proposals
End

Theorem recov_admit_all_B_keeps_parked:
  ∀proposals rec0.
    home_recov_parked step rec0 home ⇒
    home_recov_parked step (recov_admit_all_B step home B rec0 proposals) home
Proof
  Induct >> rw[recov_admit_all_B_def] >>
  fs[GSYM recov_admit_all_B_def] >>
  first_x_assum irule >>
  metis_tac[recov_admit_B_keeps_parked]
QED

(* THE DEADLINE IS NEVER BLOWN BY SELF-MODIFICATION: any state recoverable
   within B at genesis is still recoverable within B after ANY admitted
   stream of the inhabitant's own recovery-controller rewrites. The
   off-switch can be sped up, never slowed past the deadline. *)
Theorem self_modification_never_increases_recovery_latency:
  ∀proposals rec0 s.
    cwithin step rec0 home B s ⇒
    cwithin step (recov_admit_all_B step home B rec0 proposals) home B s
Proof
  Induct >> rw[recov_admit_all_B_def] >>
  fs[GSYM recov_admit_all_B_def] >>
  first_x_assum irule >>
  metis_tac[recov_admit_B_preserves_cwithin]
QED

(* THE HEADLINE: rewrite your own recovery mechanism by an arbitrary admitted
   stream AND drive the plant with any controller — every reachable state is
   still recoverable WITHIN B steps. Self-modification of the off-switch,
   adversarial control, and the latency guarantee survives both. *)
Theorem self_modifying_recovery_preserves_bounded_corrigibility:
  home_recov_parked step rec0 home ∧
  init_safe init (cwithin step rec0 home B) ⇒
  ∀proposals ctrl.
    invariant step init
      (enveloped
         (maxpol step
            (cwithin step (recov_admit_all_B step home B rec0 proposals) home B))
         (recov_admit_all_B step home B rec0 proposals) ctrl)
      (cwithin step (recov_admit_all_B step home B rec0 proposals) home B)
Proof
  rpt strip_tac >>
  irule cwithin_floor_holds >>
  conj_tac
  >- (fs[init_safe_def] >>
      metis_tac[self_modification_never_increases_recovery_latency])
  >- metis_tac[recov_admit_all_B_keeps_parked]
QED

val _ = export_theory ();
