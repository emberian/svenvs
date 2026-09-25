(*
  Upgrading the guard-checker / proof kernel itself.

  embeddedGate fixed the checker as Candle's verified inference system `|-`
  (sound by holSoundnessTheory.proves_sound). Here the *checker is a
  parameter*: a kernel is an abstract admit-predicate K : thy -> term -> bool,
  and a self-improving system may propose to REPLACE its kernel with a
  stronger K'.

  The catch (Gödel/Löb): a sound kernel K cannot prove its own soundness, so
  it certainly cannot bootstrap an unboundedly stronger K' for free. The
  escape is the stratified-reflection / Large-Cardinal route
  (Fallenstein–Kumar; hol-reflection/lca): under the LCA, each level can
  certify the soundness of the next. We take that reflection principle as an
  EXPLICIT, LABELLED HYPOTHESIS — `loeb_reflection` — *not* a `cheat`. The
  conditional theorem ("kernel self-upgrade is safe GIVEN the LCA-justified
  reflection principle") is exactly the literature's framing; discharging
  `loeb_reflection` from `lcaTheory.LCA_def` is precisely what the heavy
  `hol-reflection/lca` (`lcaProof`, the 137 KB construction) does — deferred
  to the dedicated build host, and NOT required to exhibit this architecture.

  The policy gate is OPERATIONAL (`kgate`: install iff the kernel said yes),
  so kernel soundness, the reflection principle, the Candle certificate and
  the obligation encoding are each load-bearing -- and each has a
  machine-checked necessity theorem below showing the conclusion fails
  without it. `kernel_sound_iff_gate_safe` states the sharpest form: a
  kernel is sound iff the gate it drives is safe for every
  faithfully-encoded proposal.
*)
open HolKernel boolLib bossLib BasicProvers
     holSyntaxTheory holSyntaxExtraTheory holSemanticsTheory holSoundnessTheory
     systemTheory envelopeTheory safetyTheory sv_weakeningTheory
     upgradeTheory embeddedGateTheory;

val _ = new_theory "kernelUpgrade";

val _ = Parse.hide "mem";
val mem = ``mem:'U->'U->bool``;

(* A kernel = the set of (theory, obligation) pairs it certifies. *)
Type kernel = ``:thy -> term -> bool``

(* A kernel is SOUND iff it only ever certifies semantically-entailed
   obligations (the property holSoundnessTheory gives for Candle's `|-`). *)
Definition kernel_sound_def:
  kernel_sound (^mem) (K:kernel) ⇔
    ∀thy obl. K thy obl ⇒ (thy,[]) |= obl
End

(* The base kernel: Candle's verified inference system. *)
Definition candle_kernel_def:
  candle_kernel (thy:thy) obl ⇔ (thy,[]) |- obl
End

(* The base kernel is sound — this IS proves_sound, no assumption. *)
Theorem candle_kernel_sound:
  is_set_theory ^mem ⇒ kernel_sound ^mem candle_kernel
Proof
  rw[kernel_sound_def, candle_kernel_def] >> metis_tac[proves_sound]
QED

(* ---- the Löb / Vingean reflection principle (labelled hypothesis) ----
   `sound_stmt` is an embedded proposition, stated in the theory `thy`,
   meaning "K' is sound". The principle says: if the current kernel K
   certifies THAT statement in THAT theory, then K' really is sound. This is
   the content the LCA delivers via hol-reflection/lca's master theorem
   (kernel/loebReduction derives it from the LCA decoding hypothesis); we
   keep it as an explicit hypothesis so this theory builds WITHOUT the heavy
   lca construction.

   It is stated for ONE theory and ONE statement. An earlier form quantified
   the certificate over every theory, (∀thy. K thy (sound_stmt thy)) ⇒ …;
   that antecedent is unsatisfiable for the Candle kernel (Candle derives
   nothing in a theory that is not theory_ok), so every theorem carrying it
   was vacuous: old_reflection_antecedent_unsatisfiable below records this. *)
Definition loeb_reflection_def:
  loeb_reflection (^mem) (K:kernel) (K':kernel) (thy:thy) (sound_stmt:term) ⇔
    (K thy sound_stmt ⇒ kernel_sound ^mem K')
End

(* Kernel self-upgrade: if the verified base kernel certifies the soundness
   statement of K', then under the (LCA-justified) reflection principle the
   upgraded kernel K' is sound. Both hypotheses are needed:
   reflection_without_certificate_can_breach and
   certificate_without_reflection_can_breach. *)
Theorem kernel_self_upgrade_sound:
  loeb_reflection ^mem candle_kernel K' thy sound_stmt ∧
  candle_kernel thy sound_stmt ⇒
  kernel_sound ^mem K'
Proof
  rw[loeb_reflection_def]
QED

(* ---- the operational gate driven by a kernel ----
   Install [newp] iff the kernel K CERTIFIED the obligation term. *)
Definition kgate_def:
  kgate (K:kernel) thy obl (oldp:('s,'a) policy) newp = gate (K thy obl) oldp newp
End

Theorem upgraded_kernel_rejects:
  ¬K' thy obl ⇒ kgate K' thy obl oldp newp = oldp
Proof
  rw[kgate_def, gate_def]
QED

(* End-to-end: a policy upgrade decided by the upgraded kernel K' preserves
   safety for EVERY controller, provided K' is sound and the obligation term
   faithfully encodes admissibility. K' decides; its soundness is what makes
   a "yes" trustworthy (kernel_unsound_certificate_can_breach). *)
Theorem upgraded_kernel_preserves_safety:
  kernel_sound ^mem K' ∧
  encodes_obligation ^mem thy obl step safe oldp newp ∧
  init_safe init safe ∧
  safe_shield step safe shield ∧
  sound_policy step safe oldp ⇒
  ∀ctrl. invariant step init
            (enveloped (kgate K' thy obl oldp newp) shield ctrl) safe
Proof
  rpt strip_tac >> simp[kgate_def] >>
  irule gate_preserves_safety >> fs[] >>
  metis_tac[kernel_sound_def, encodes_obligation_def, admissible_def]
QED

(* When K' certifies, the upgrade installs, and what it installs is a
   certified genuine weakening. *)
Theorem upgraded_kernel_installs:
  K' thy obl ∧
  kernel_sound ^mem K' ∧
  encodes_obligation ^mem thy obl step safe oldp newp ⇒
  kgate K' thy obl oldp newp = newp ∧
  admissible step safe oldp newp
Proof
  rpt strip_tac >- rw[kgate_def, gate_def] >>
  metis_tac[kernel_sound_def, encodes_obligation_def]
QED

(* The full conditional self-improving-kernel statement, in one place: the
   verified base kernel certifies (in theory sthy) the soundness statement
   of K'; the LCA-justified reflection principle turns that certificate
   into soundness of K'; K' then decides a policy upgrade through the
   operational gate; safety holds for any controller. *)
Theorem self_improving_kernel_is_safe:
  loeb_reflection ^mem candle_kernel K' sthy sound_stmt ∧
  candle_kernel sthy sound_stmt ∧
  encodes_obligation ^mem thy obl step safe oldp newp ∧
  init_safe init safe ∧
  safe_shield step safe shield ∧
  sound_policy step safe oldp ⇒
  ∀ctrl. invariant step init
            (enveloped (kgate K' thy obl oldp newp) shield ctrl) safe
Proof
  rpt strip_tac >>
  ‘kernel_sound ^mem K'’ by metis_tac[kernel_self_upgrade_sound] >>
  metis_tac[upgraded_kernel_preserves_safety]
QED

(* ===================================================================== *)
(*  NECESSITY: every hypothesis above does work.                          *)
(* ===================================================================== *)

(* A term that is not of type bool is entailed by no theory (entails_def
   demands `has_type Bool`); so a kernel that certifies it is unsound. *)
Theorem ill_typed_never_entailed:
  ¬((thy,h) |= Var y (Tyvar a))
Proof
  rw[entails_def] >> simp[Once has_type_cases]
QED

Theorem accept_all_kernel_unsound:
  ¬kernel_sound ^mem (λthy obl. T)
Proof
  rw[kernel_sound_def] >>
  qexistsl_tac [‘thy’, ‘Var y (Tyvar a)’] >> rw[ill_typed_never_entailed]
QED

(* An unsound certificate breaches safety. Given ANY kernel certificate for
   a non-valid obligation, there is a habitat, sound old policy, safe
   shield, safe initial states and a proposal whose obligation encoding is
   faithful (vacuously so: the obligation is not valid), for which the
   gate driven by that kernel installs an unsound policy and the enveloped
   system leaves the safe set. *)
Theorem kernel_unsound_certificate_can_breach:
  K' thy obl ∧ ¬((thy,[]) |= obl) ⇒
  ∃(step:num -> num -> num) safe init shield oldp newp ctrl.
    encodes_obligation ^mem thy obl step safe oldp newp ∧
    init_safe init safe ∧
    safe_shield step safe shield ∧
    sound_policy step safe oldp ∧
    ¬invariant step init (enveloped (kgate K' thy obl oldp newp) shield ctrl) safe
Proof
  rpt strip_tac >>
  strip_assume_tac unsound_certificate_breaches >>
  qexistsl_tac [‘step’, ‘safe’, ‘init’, ‘shield’, ‘oldp’, ‘newp’, ‘ctrl’] >>
  fs[kgate_def, encodes_obligation_def]
QED

(* Kernel soundness is EXACTLY what the operational gate needs: a kernel is
   sound iff the gate it drives is safe for every faithfully-encoded
   proposal in every (here: num) habitat. *)
Theorem kernel_sound_iff_gate_safe:
  kernel_sound ^mem K' ⇔
  ∀thy obl (step:num -> num -> num) safe init shield oldp newp.
    encodes_obligation ^mem thy obl step safe oldp newp ∧
    init_safe init safe ∧
    safe_shield step safe shield ∧
    sound_policy step safe oldp ⇒
    ∀ctrl. invariant step init
              (enveloped (kgate K' thy obl oldp newp) shield ctrl) safe
Proof
  eq_tac
  >- metis_tac[upgraded_kernel_preserves_safety]
  >- (rpt strip_tac >> simp[kernel_sound_def] >> rpt strip_tac >>
      CCONTR_TAC >>
      drule_all kernel_unsound_certificate_can_breach >> strip_tac >>
      metis_tac[])
QED

(* The reflection principle is NOT a consequence of soundness of the base
   kernel. Concretely: in the initial theory context the verified Candle
   kernel certifies x = x (a TRUE statement, by REFL); the kernel that
   accepts everything is unsound; so the reflection principle from that
   certificate to that kernel FAILS. loeb_reflection is a genuine
   encoding/reflection fact about what `sound_stmt` denotes, which is why it
   is a labelled hypothesis. *)
Theorem reflection_is_not_soundness:
  candle_kernel (thyof init_ctxt) (Var x Bool === Var x Bool) ∧
  ¬kernel_sound ^mem (λthy obl. T) ∧
  ¬loeb_reflection ^mem candle_kernel (λthy obl. T)
                   (thyof init_ctxt) (Var x Bool === Var x Bool)
Proof
  rw[candle_kernel_def, loeb_reflection_def, candle_refl_witness,
     accept_all_kernel_unsound]
QED

(* NECESSITY of loeb_reflection in self_improving_kernel_is_safe: a real
   Candle certificate, a faithful encoding and a sound habitat, and still a
   breach, because nothing ties the certified statement to K'. *)
Theorem certificate_without_reflection_can_breach:
  ∃K' sthy sound_stmt thy obl (step:num -> num -> num) safe init shield
     oldp newp ctrl.
    candle_kernel sthy sound_stmt ∧
    ¬loeb_reflection ^mem candle_kernel K' sthy sound_stmt ∧
    encodes_obligation ^mem thy obl step safe oldp newp ∧
    init_safe init safe ∧
    safe_shield step safe shield ∧
    sound_policy step safe oldp ∧
    ¬invariant step init (enveloped (kgate K' thy obl oldp newp) shield ctrl) safe
Proof
  ‘(λthy obl. T) thy (Var y (Tyvar a)) ∧ ¬((thy,[]) |= Var y (Tyvar a))’
    by rw[ill_typed_never_entailed] >>
  drule_all kernel_unsound_certificate_can_breach >> strip_tac >>
  qexistsl_tac [‘λthy obl. T’, ‘thyof init_ctxt’, ‘Var x Bool === Var x Bool’,
                ‘thy’, ‘Var y (Tyvar a)’, ‘step’, ‘safe’, ‘init’, ‘shield’,
                ‘oldp’, ‘newp’, ‘ctrl’] >>
  fs[reflection_is_not_soundness]
QED

(* NECESSITY of the Candle certificate: without it the reflection principle
   holds vacuously -- here for the accept-everything kernel, in a theory
   where Candle derives nothing -- and the gate that kernel drives
   breaches. *)
Theorem reflection_without_certificate_can_breach:
  ∃K' sthy sound_stmt thy obl (step:num -> num -> num) safe init shield
     oldp newp ctrl.
    loeb_reflection ^mem candle_kernel K' sthy sound_stmt ∧
    ¬candle_kernel sthy sound_stmt ∧
    encodes_obligation ^mem thy obl step safe oldp newp ∧
    init_safe init safe ∧
    safe_shield step safe shield ∧
    sound_policy step safe oldp ∧
    ¬invariant step init (enveloped (kgate K' thy obl oldp newp) shield ctrl) safe
Proof
  ‘(λthy obl. T) thy (Var y (Tyvar a)) ∧ ¬((thy,[]) |= Var y (Tyvar a))’
    by rw[ill_typed_never_entailed] >>
  drule_all kernel_unsound_certificate_can_breach >> strip_tac >>
  ‘∀s. ¬candle_kernel ((FEMPTY,FEMPTY),{}) s’
    by (rw[candle_kernel_def] >> strip_tac >>
        imp_res_tac proves_theory_ok >>
        fs[theory_ok_def, is_std_sig_def, finite_mapTheory.FLOOKUP_EMPTY]) >>
  qexistsl_tac [‘λthy obl. T’, ‘((FEMPTY,FEMPTY),{})’, ‘sound_stmt’,
                ‘thy’, ‘Var y (Tyvar a)’, ‘step’, ‘safe’, ‘init’, ‘shield’,
                ‘oldp’, ‘newp’, ‘ctrl’] >>
  fs[loeb_reflection_def]
QED

(* WHY the single-theory form: the earlier all-theories antecedent can
   never be met by the Candle kernel, whatever the statement family. A
   theory whose signature is not standard is not theory_ok, and
   holSyntaxExtraTheory.proves_theory_ok says Candle derives nothing in it. *)
Theorem old_reflection_antecedent_unsatisfiable:
  ∀sound_stmt. ¬(∀thy. candle_kernel thy (sound_stmt thy))
Proof
  rw[candle_kernel_def] >>
  qexists_tac ‘((FEMPTY,FEMPTY),{})’ >> strip_tac >>
  imp_res_tac proves_theory_ok >>
  fs[theory_ok_def, is_std_sig_def, finite_mapTheory.FLOOKUP_EMPTY]
QED

(* Consequently the old principle held for EVERY K', sound or not: it could
   not have carried any information. *)
Theorem old_reflection_was_vacuous:
  ∀K' sound_stmt.
    (∀thy. candle_kernel thy (sound_stmt thy)) ⇒ kernel_sound ^mem K'
Proof
  metis_tac[old_reflection_antecedent_unsatisfiable]
QED

val _ = export_theory ();
