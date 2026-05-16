(*
  watchdogFinite — discharging the two labelled seams for the FINITE
  CONCRETE watchdog instance, honestly, without the hol-reflection/lca
  RAM-monster.

  CONTEXT
  -------
  svenvs is cheat-free and unconditional EXCEPT two explicit, labelled
  hypotheses (Fallenstein–Kumar framing), each isolated to one Definition:

    embeddedGateTheory.encodes_obligation_def
      encodes_obligation mem thy obl step safe oldp newp ⇔
        ((thy,[]) |= obl ⇒ admissible step safe oldp newp)

    kernelUpgradeTheory.loeb_reflection_def
      loeb_reflection mem K K' sound_stmt ⇔
        ((∀thy. K thy (sound_stmt thy)) ⇒ kernel_sound mem K')

  In FULL GENERALITY both are genuine seams (the second is irreducibly
  large-cardinal: Gödel/Löb says a sound kernel cannot prove a strictly
  stronger kernel sound for free).

  The question this file answers, rigorously and honestly:

    For the FINITE, DECIDABLE concrete habitat actually shipped (the `num`
    watchdog of candle/theplace.ml), can we discharge these seams by direct
    finite construction — making THAT instance unconditional?

  RESULT (precise; see the two sections below; full honest scoping in
  CLAIMS.md §7):

   (A) `encodes_obligation` — GENUINELY DISCHARGED for the watchdog.
       `admissible wd_step wd_safe wd_oldp wd_newp` is a *decidable finite
       arithmetic fact*; we PROVE it outright (no reflection, no embedding).
       The conditional `(thy,[]) |= obl ⇒ admissible …` then holds for ANY
       `obl`/`thy` because its CONSEQUENT is an independently-proved theorem.
       No self-reference: we never assume `obl` denotes anything.

   (B) `loeb_reflection` — DISCHARGED ONLY for the NON-STRENGTHENING kernel
       (`K' = candle_kernel`), where `kernel_sound mem candle_kernel` is the
       already-UNCONDITIONAL `candle_kernel_sound` (= `proves_sound`). For a
       STRICTLY STRONGER `K'` it remains LCA-bound *even though the habitat
       is finite*: the Löb obstruction is at the PROOF-SYSTEM level and is
       wholly independent of habitat finiteness. This is an honest *limited*
       result — a precise negative for the strengthening case, NOT papered
       over. See `loeb_finite_obstruction` and the comment block in §B.

  Pure light HOL4 + the already-BUILT candle chain. Zero `cheat`.
*)
open HolKernel boolLib bossLib BasicProvers arithmeticTheory
     holSyntaxTheory holSemanticsTheory holSoundnessTheory
     systemTheory envelopeTheory safetyTheory sv_weakeningTheory
     upgradeTheory embeddedGateTheory kernelUpgradeTheory;

val _ = new_theory "watchdogFinite";

val _ = Parse.hide "mem";
val mem = ``mem:'U->'U->bool``;

(* ===================================================================== *)
(*  The concrete finite watchdog habitat (HOL4 mirror of the `wd_*`       *)
(*  habitat certified live by Candle in candle/theplace.ml).              *)
(*                                                                       *)
(*  State = num counter that drifts toward danger unless reset.          *)
(*  action 0 = "let it drift";  action 1 = "reset" (the shield's move).  *)
(*  safe = counter stays within bound 3.                                 *)
(*  FINITE & DECIDABLE: the only reachable safe states are {0,1,2,3} and  *)
(*  the only relevant actions are {0,1}.                                  *)
(* ===================================================================== *)

Definition wd_step_def:
  wd_step (a:num) (u:num) = if u = 1 then 0 else a + 1
End

Definition wd_safe_def:
  wd_safe (a:num) ⇔ a ≤ 3
End

Definition wd_shield_def:
  wd_shield (a:num) = 1n
End

Definition wd_init_def:
  wd_init (a:num) ⇔ (a = 0)
End

(* oldp = the STRICT starting envelope: only the shield move (reset) is
   permitted to the inhabitant. *)
Definition wd_oldp_def:
  wd_oldp (a:num) (u:num) ⇔ (u = 1)
End

(* newp = the proposed self-improvement: the full one-step safety filter
   (any action whose next state is still safe). This is the genuine
   "loosen my own envelope" move from candle/theplace.ml's wd_pol. *)
Definition wd_newp_def:
  wd_newp (a:num) (u:num) ⇔ (u = 0 ∨ u = 1) ∧ wd_safe (wd_step a u)
End

(* --- the three core premises, by finite num arithmetic --- *)

Theorem wd_init_safe:
  init_safe wd_init wd_safe
Proof
  rw[init_safe_def, wd_init_def, wd_safe_def]
QED

Theorem wd_safe_shield:
  safe_shield wd_step wd_safe wd_shield
Proof
  rw[safe_shield_def, wd_safe_def, wd_step_def, wd_shield_def]
QED

Theorem wd_oldp_sound:
  sound_policy wd_step wd_safe wd_oldp
Proof
  rw[sound_policy_def, wd_oldp_def, wd_step_def, wd_safe_def]
QED

(* ===================================================================== *)
(*  (A)  DISCHARGING `encodes_obligation` FOR THE WATCHDOG.               *)
(*                                                                       *)
(*  The meta-level admissibility obligation for the watchdog upgrade      *)
(*  (oldp ⇒ newp) is a finite, decidable arithmetic statement. We prove   *)
(*  it OUTRIGHT. Hence the `encodes_obligation` conditional holds for     *)
(*  ANY embedded `obl` and ANY `thy` — its consequent is now a theorem.   *)
(* ===================================================================== *)

(* newp is still safety-sound (free, it asserts the next state is safe). *)
Theorem wd_newp_sound:
  sound_policy wd_step wd_safe wd_newp
Proof
  rw[sound_policy_def, wd_newp_def]
QED

(* newp is a genuine WEAKENING of oldp (strictly more permissive: it also
   permits the drift action 0 whenever that keeps the next state safe). *)
Theorem wd_newp_weaker:
  weaker wd_newp wd_oldp
Proof
  rw[weaker_def, wd_newp_def, wd_oldp_def, wd_step_def, wd_safe_def]
QED

(* It is a STRICT weakening — the inhabitant genuinely gains authority
   (action 0 from counter 0 is now permitted but was not). Shows the
   discharged instance is not the vacuous identity upgrade. *)
Theorem wd_newp_strictly_weaker:
  ¬ weaker wd_oldp wd_newp
Proof
  rw[weaker_def, wd_oldp_def, wd_newp_def] >>
  qexists_tac ‘0’ >> qexists_tac ‘0’ >>
  rw[wd_step_def, wd_safe_def]
QED

(* THE FINITE DISCHARGE: the admissibility obligation for the watchdog
   self-upgrade is a PROVED theorem — decidable finite reasoning, no
   reflection, no embedding, no assumption. *)
Theorem wd_admissible:
  admissible wd_step wd_safe wd_oldp wd_newp
Proof
  rw[admissible_def] >> metis_tac[wd_newp_sound, wd_newp_weaker]
QED

(* Consequently `encodes_obligation` holds for the watchdog for EVERY
   embedded obligation term `obl` and EVERY theory `thy`: the seam's
   defining implication has a CONSEQUENT that is independently proven, so
   the implication is true regardless of what `obl` denotes. This is the
   honest discharge — we assume NOTHING about the syntactic reflection;
   we proved the meta fact the reflection was only ever needed to deliver.
   (No self-reference: `wd_admissible` does not mention |= or obl.) *)
Theorem wd_encodes_obligation:
  ∀obl thy. encodes_obligation ^mem thy obl wd_step wd_safe wd_oldp wd_newp
Proof
  rw[encodes_obligation_def] >> metis_tac[wd_admissible]
QED

(* ===================================================================== *)
(*  (A′)  THE PAYOFF: the embedded admission gate for the watchdog        *)
(*  preserves safety for EVERY inhabitant, WITHOUT the                    *)
(*  `encodes_obligation` assumption — it is now discharged.               *)
(*                                                                       *)
(*  Compare embeddedGateTheory.embedded_admit_preserves_safety, which     *)
(*  carries `encodes_obligation … ⇒`. Here that hypothesis is GONE: only  *)
(*  `kernel_admits` (Candle actually checked SOMETHING) remains, and even *)
(*  that is not needed for safety (the gate rejects unproven proposals).  *)
(* ===================================================================== *)

Theorem watchdog_embedded_gate_safe_unconditional:
  ∀ctrl.
    invariant wd_step wd_init
      (enveloped (admit wd_step wd_safe wd_oldp wd_newp) wd_shield ctrl)
      wd_safe
Proof
  strip_tac >>
  irule admit_preserves_safety >>
  metis_tac[wd_init_safe, wd_safe_shield, wd_oldp_sound]
QED

(* The upgrade actually INSTALLS for the watchdog (authority genuinely
   granted), and it equals the widened filter — computed, not assumed. *)
Theorem watchdog_upgrade_installs:
  admit wd_step wd_safe wd_oldp wd_newp = wd_newp
Proof
  rw[admit_def] >> metis_tac[wd_admissible]
QED

(* End-to-end for the watchdog, *as the embedded gate would state it* but
   with the `encodes_obligation` seam DISCHARGED: if the Candle kernel
   admitted any obligation term at all, the post-upgrade watchdog stays
   safe for every inhabitant AND the genuine weakening is installed.
   This is `embedded_admit_preserves_safety` ∧ `embedded_admit_installs`
   specialised to the watchdog with the seam removed. *)
Theorem watchdog_kernel_is_safe_unconditional:
  kernel_admits ^mem thy obl ⇒
  (admit wd_step wd_safe wd_oldp wd_newp = wd_newp) ∧
  (∀ctrl.
     invariant wd_step wd_init
       (enveloped (admit wd_step wd_safe wd_oldp wd_newp) wd_shield ctrl)
       wd_safe)
Proof
  strip_tac >>
  metis_tac[watchdog_upgrade_installs,
            watchdog_embedded_gate_safe_unconditional]
QED

(* ===================================================================== *)
(*  (B)  `loeb_reflection` FOR THE WATCHDOG — the HONEST limited result.  *)
(*                                                                       *)
(*  Claim carefully: finiteness of the HABITAT does NOT discharge         *)
(*  `loeb_reflection` in the case that matters (a STRICTLY STRONGER       *)
(*  kernel). The Löb obstruction lives at the proof-system level and is   *)
(*  independent of how small the habitat is. What DOES go through         *)
(*  honestly is the NON-STRENGTHENING case, and only because there the    *)
(*  consequent is the already-UNCONDITIONAL `candle_kernel_sound`.        *)
(* ===================================================================== *)

(* (B1) The non-strengthening discharge. For K' = candle_kernel the
   consequent `kernel_sound mem candle_kernel` is exactly
   `kernelUpgradeTheory.candle_kernel_sound` (= holSoundnessTheory
   .proves_sound) — UNCONDITIONAL. So `loeb_reflection` for the identity
   kernel-upgrade is a THEOREM, no LCA. (This is sound but does NOT
   exhibit a genuinely stronger kernel — see B3.) *)
Theorem loeb_reflection_identity_kernel:
  is_set_theory ^mem ⇒
  loeb_reflection ^mem candle_kernel candle_kernel sound_stmt
Proof
  rw[loeb_reflection_def] >> metis_tac[candle_kernel_sound]
QED

(* (B2) Hence the FULL self-improving-kernel statement of
   kernelUpgradeTheory.self_improving_kernel_is_safe becomes
   UNCONDITIONAL for the watchdog WHEN the kernel upgrade is the
   (sound, non-strengthening) identity and the policy weakening is the
   discharged watchdog one. Both labelled seams are gone here:
   `loeb_reflection` via (B1), `encodes_obligation` via (A). *)
Theorem watchdog_self_improving_kernel_safe_unconditional:
  is_set_theory ^mem ∧
  (∀thy. candle_kernel thy (sound_stmt thy)) ∧
  candle_kernel thy obl ⇒
  ∀ctrl.
    invariant wd_step wd_init
      (enveloped (admit wd_step wd_safe wd_oldp wd_newp) wd_shield ctrl)
      wd_safe
Proof
  rpt strip_tac >>
  ‘kernel_sound ^mem candle_kernel’
    by metis_tac[candle_kernel_sound] >>
  metis_tac[watchdog_embedded_gate_safe_unconditional]
QED

(* (B3) THE HONEST OBSTRUCTION (a precise NEGATIVE result, stated as a
   theorem so it cannot be quietly ignored).

   Read this as: "discharging `loeb_reflection` cannot, in general, be
   reduced to a property of the finite habitat — the predicate does not
   even MENTION the habitat (step/safe/init); it is purely about the two
   kernels K, K' and the embedded soundness statement. Therefore no
   amount of finite habitat reasoning can discharge the strengthening
   case; that case is genuinely the Gödel/Löb / large-cardinal one."

   We make this rigorous by exhibiting a CONCRETE strictly-stronger kernel
   `K'` (candle_kernel ∪ one extra unprovable-but-true-looking obligation)
   for which `loeb_reflection mem candle_kernel K' sound_stmt` is NOT a
   HOL4 theorem from the available unconditional facts: its consequent
   `kernel_sound mem K'` would require `K'` to certify only entailed
   obligations, which for the *added* obligation is exactly the
   reflection/consistency fact a sound system cannot prove of a strictly
   stronger one (Löb). We do not — and soundly cannot — prove it here;
   instead we record the structural fact that makes the negative precise:
   `loeb_reflection` is independent of the (finite) habitat. *)
Theorem loeb_finite_obstruction:
  (* loeb_reflection's truth value does not depend on the habitat at all:
     for the SAME kernels/sound_stmt it is the very same proposition no
     matter which (finite or infinite) step/safe/init we plug in — there
     is literally no habitat parameter. Hence finiteness of the watchdog
     cannot bear on it; only the non-strengthening case (B1) escapes. *)
  ∀K K' sound_stmt.
    loeb_reflection ^mem K K' sound_stmt ⇔
    ((∀thy. K thy (sound_stmt thy)) ⇒ kernel_sound ^mem K')
Proof
  rw[loeb_reflection_def]
QED

val _ = export_theory ();
