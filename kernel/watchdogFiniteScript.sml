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
      loeb_reflection mem K K' thy sound_stmt ⇔
        (K thy sound_stmt ⇒ kernel_sound mem K')

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
       over. See `loeb_finite_obstruction`: with every watchdog fact
       present, a strictly stronger kernel extending Candle still fails the
       reflection principle.

   The gates here are the OPERATIONAL ones (kernel_gate / kgate: install
   iff the kernel said yes). For the watchdog, safety holds on BOTH
   branches because wd_oldp and wd_newp are both sound: that is the honest
   content of the "unconditional" theorems -- the finite discharge makes
   the proposal safe no matter which kernel decides, even an unsound one.

  Pure light HOL4 + the already-BUILT candle chain. Zero `cheat`.
*)
open HolKernel boolLib bossLib BasicProvers arithmeticTheory
     holSyntaxTheory holSyntaxExtraTheory holSemanticsTheory holSoundnessTheory
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

(* End-to-end for the watchdog, through the OPERATIONAL embedded gate
   (install iff Candle derived the obligation term), with the
   `encodes_obligation` seam DISCHARGED (wd_encodes_obligation): whatever
   Candle did or did not derive, the post-upgrade watchdog stays safe for
   every inhabitant; and when Candle derived the obligation, the genuine
   weakening is installed. Safety here needs no hypothesis because BOTH
   branches of the gate are sound policies (wd_oldp_sound, wd_newp_sound);
   it is proved through embedded_admit_preserves_safety to show the
   discharged seam composing with the real gate. *)
Theorem watchdog_kernel_is_safe_unconditional:
  (kernel_admits ^mem thy obl ⇒
     kernel_gate ^mem thy obl wd_oldp wd_newp = wd_newp) ∧
  (∀ctrl.
     invariant wd_step wd_init
       (enveloped (kernel_gate ^mem thy obl wd_oldp wd_newp) wd_shield ctrl)
       wd_safe)
Proof
  conj_tac
  >- metis_tac[embedded_admit_installs, wd_encodes_obligation]
  >- (strip_tac >> irule embedded_admit_preserves_safety >>
      metis_tac[wd_encodes_obligation, wd_init_safe, wd_safe_shield,
                wd_oldp_sound])
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
  loeb_reflection ^mem candle_kernel candle_kernel thy sound_stmt
Proof
  rw[loeb_reflection_def] >> metis_tac[candle_kernel_sound]
QED

(* (B2) Hence the self-improving-kernel statement of
   kernelUpgradeTheory.self_improving_kernel_is_safe holds for the watchdog
   through the operational gate kgate: for the identity kernel upgrade the
   reflection principle is (B1), the encoding is (A), and self_improving_
   kernel_is_safe applies whenever Candle certifies a statement. The second
   conjunct is the honest strengthening: because both watchdog policies are
   sound, the gate is safe whichever kernel K' decides, sound or not. *)
Theorem watchdog_self_improving_kernel_safe_unconditional:
  (is_set_theory ^mem ∧ candle_kernel sthy sound_stmt ⇒
   ∀ctrl.
     invariant wd_step wd_init
       (enveloped (kgate candle_kernel thy obl wd_oldp wd_newp) wd_shield ctrl)
       wd_safe) ∧
  (∀K' ctrl.
     invariant wd_step wd_init
       (enveloped (kgate K' thy obl wd_oldp wd_newp) wd_shield ctrl)
       wd_safe)
Proof
  conj_tac
  >- (rpt strip_tac >> irule self_improving_kernel_is_safe >>
      metis_tac[loeb_reflection_identity_kernel, wd_encodes_obligation,
                wd_init_safe, wd_safe_shield, wd_oldp_sound])
  >- (rpt strip_tac >> simp[kgate_def] >> irule gate_preserves_safety >>
      metis_tac[wd_newp_sound, wd_init_safe, wd_safe_shield, wd_oldp_sound])
QED

(* (B3) THE HONEST OBSTRUCTION, as a genuine negative theorem.

   Every fact the finite habitat supplies is present in the statement --
   the watchdog obligation is admissible, its encoding is discharged for
   every term and theory, both policies are sound -- and a real Candle
   certificate exists (x = x in the initial context). Yet there is a kernel
   K' that EXTENDS Candle's (certifies everything Candle certifies) and is
   STRICTLY stronger (certifies a term Candle never derives) for which the
   reflection principle from that certificate FAILS, because K' is unsound.
   So no amount of finite habitat reasoning yields loeb_reflection for a
   strengthening upgrade: the obstruction is at the proof-system level, and
   the strengthening case is genuinely the Gödel/Löb / large-cardinal one.
   Only the non-strengthening case (B1) escapes. *)
Theorem loeb_finite_obstruction:
  ∃K' sthy sound_stmt.
    admissible wd_step wd_safe wd_oldp wd_newp ∧
    (∀obl thy. encodes_obligation ^mem thy obl wd_step wd_safe wd_oldp wd_newp) ∧
    sound_policy wd_step wd_safe wd_oldp ∧
    sound_policy wd_step wd_safe wd_newp ∧
    (∀thy obl. candle_kernel thy obl ⇒ K' thy obl) ∧
    (∃thy obl. K' thy obl ∧ ¬candle_kernel thy obl) ∧
    candle_kernel sthy sound_stmt ∧
    ¬kernel_sound ^mem K' ∧
    ¬loeb_reflection ^mem candle_kernel K' sthy sound_stmt
Proof
  qexistsl_tac [‘λthy obl. T’, ‘thyof init_ctxt’,
                ‘Var x Bool === Var x Bool’] >>
  simp[wd_admissible, wd_encodes_obligation, wd_oldp_sound, wd_newp_sound,
       reflection_is_not_soundness] >>
  qexistsl_tac [‘thyof init_ctxt’, ‘Var y (Tyvar a)’] >>
  rw[candle_kernel_def] >> strip_tac >>
  imp_res_tac proves_term_ok >> fs[] >>
  qpat_x_assum ‘_ has_type _’ mp_tac >> simp[Once has_type_cases]
QED

val _ = export_theory ();
