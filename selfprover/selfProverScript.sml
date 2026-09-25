(*
  selfProver — the capstone layer: the verified PROVER itself self-improves,
  gated by the FROZEN HOL4 root. Pure light HOL4 (no CakeML / candle /
  hol-reflection); the architecture is established UNCONDITIONALLY here.

  --------------------------------------------------------------------------
  THE TOWER OF TURTLES (what is frozen vs verified-in-HOL4-hence-mutable vs
  assumed)

    HOL4's LCF kernel ............ FROZEN. The immovable bottom turtle.
                                   Deliberately NOT self-improving: if the
                                   unconstrained inhabitant could edit it, an
                                   unsound HOL4 could 'prove' its own unsound
                                   successor. So it never moves.

    Candle / CakeML compiler ..... VERIFIED IN HOL4, hence MUTABLE. Their
                                   soundness/correctness are HOL4 *theorems
                                   about a development* (Candle:
                                   holSoundnessTheory.proves_sound; CakeML:
                                   the compiler-correctness theorem). So the
                                   inhabitant CAN propose a modified build B'
                                   — adoption is gated on whether FROZEN HOL4
                                   still proves the soundness theorem for the
                                   *proposed* artifact.

    The svenvs policy envelope ... MUTABLE, gated by the prover (upgradeTheory:
                                   admissible / gate / gated_self_improvement_is_safe).

  The crucial asymmetry: the fixed trusted root (frozen HOL4) vouches for a
  *mutable* layer (the proposed Candle build). That is NOT a system vouching
  for *itself*. Therefore this layer needs NO reflection principle and NO
  `loeb_reflection`. (Löb only bites the *kernel-replacing-itself* seam, which
  is the SEPARATE, already-labelled `kernelUpgradeTheory.loeb_reflection`
  hypothesis — a different turtle, see the no-Löb argument at the bottom.)

  --------------------------------------------------------------------------
  WHAT IS ABSTRACTED, AND WHY THAT IS HONEST

  We do NOT rebuild real Candle here (that needs the heavy CakeML root and is
  the documented follow-up #28). We model:

    * a proposed prover build as opaque DATA `B : 'b`;
    * the soundness OBLIGATION on a build as an abstract predicate
      `sound : 'b -> bool`. It stands for the real `proves_sound`-shaped
      statement `is_set_theory mem ⇒ (thy |- c ⇒ thy |= c)` for the build's
      kernel — kept abstract so this theory carries no CakeML dependency;
    * the frozen HOL4 checker as `hol4_checks : 'p -> 'b -> bool`, taking a
      proof object `p:'p` and a build `B:'b`. `hol4_checks p B` means: the
      FROZEN HOL4 kernel, replaying proof `p`, accepts that build `B`
      satisfies the soundness obligation.

  The ONE new piece of trust is the clearly LABELLED, named assumption
  `frozen_checker_sound` (definition + explicit antecedent of every theorem
  that uses it), in EXACTLY the honest style of the existing
  `kernelUpgradeTheory.loeb_reflection` / `embeddedGateTheory.encodes_obligation`
  labels. It is the trust-in-the-frozen-root axiom — strictly MORE honest /
  WEAKER than assuming Candle sound outright (we assume only that the *frozen
  HOL4 LCF kernel*, replaying a concrete proof, is sound about builds — which
  is just the soundness of the immovable bottom turtle that the entire stack
  already rests on; we assume nothing about Candle directly).
*)
open HolKernel boolLib bossLib BasicProvers listTheory
     systemTheory envelopeTheory safetyTheory sv_weakeningTheory
     upgradeTheory;

val _ = new_theory "selfProver";

(* --------------------------------------------------------------------- *)
(* 1. A proposed prover build, abstractly.                               *)
(* --------------------------------------------------------------------- *)

(* `B : 'b` is opaque DATA: a proposed Candle/CakeML build artifact. We never
   inspect it; the inhabitant may produce any `B` whatsoever. *)

(* The abstract soundness obligation on a build. Concretely (follow-up #28)
   this is the `proves_sound`-shaped statement for B's kernel:
       is_set_theory mem ⇒ ((thy,h) |- c ⇒ (thy,h) |= c).
   Here it is an abstract predicate so the layer is pure HOL4. *)
Type prover_obligation = “:'b -> bool”;

(* `sound B` : the build B discharges the soundness obligation, i.e. B's
   kernel only ever certifies semantically-entailed conclusions. *)

(* Faithfulness of a build's verdict. A theorem uses it guarded by the
   build's actual answer: `bcert ⇒ build_certifies sound B …` reads "if B
   said yes to this proposal and B is sound, the proposal is admissible" --
   i.e. a sound build only certifies admissible proposals. Same shape as
   embeddedGateTheory.encodes_obligation, with the prover build (not a
   single embedded term) as the certifier; abstract (no CakeML) and
   parametric in the build. *)
Definition build_certifies_def:
  build_certifies (sound:'b prover_obligation) (B:'b)
                  step safe oldp newp ⇔
    (sound B ⇒ admissible step safe oldp newp)
End

(* --------------------------------------------------------------------- *)
(* 2. The FROZEN checker, abstractly + the LABELLED trust axiom.          *)
(* --------------------------------------------------------------------- *)

(* `hol4_checks p B` : the immutable HOL4 LCF kernel, replaying proof object
   `p:'p`, accepts that build `B:'b` meets the soundness obligation. The
   kernel is FROZEN: nothing in this theory (or anywhere the inhabitant can
   reach) ever redefines `hol4_checks`. *)

(* ---- LABELLED ASSUMPTION: frozen-checker soundness --------------------
   This is the trust-in-the-frozen-root axiom, stated EXACTLY in the honest
   style of kernelUpgradeTheory.loeb_reflection / embeddedTheory
   .encodes_obligation: a named Definition, used as an explicit antecedent
   of every theorem that needs it, NEVER a `cheat`.

     frozen_checker_sound hol4_checks sound ⇔
       ∀p B. hol4_checks p B ⇒ sound B

   Reading: if the FROZEN HOL4 kernel, replaying a concrete proof p, accepts
   that build B satisfies the soundness obligation, then B really is sound.

   Why this is MORE honest than the alternatives:
     * It is NOT "assume Candle is sound" — we assume nothing about any
       particular prover build. We assume only the soundness of the FROZEN
       HOL4 LCF kernel *as a checker of soundness theorems about builds*.
       That is the very bottom turtle the WHOLE stack (incl. Tier-1
       safety_preservation, which is itself a HOL4 theorem) already rests
       on. Adding this changes the trust base by zero new turtles.
     * It is NOT loeb_reflection. loeb_reflection assumes a system can
       certify its OWN successor's soundness (self-reference; needs the LCA
       escape). Here the FROZEN root — which is explicitly never the thing
       being upgraded — vouches for a DIFFERENT, mutable artifact. Fixed
       root → mutable layer is not self-reference. (Full argument at file
       bottom.)
     * It is discharged, for a concrete build, by literally running frozen
       HOL4 on the (existing, built) holSoundnessTheory development for that
       build — that is follow-up #28, NOT a heavy RAM-monster reflection
       proof. The seam here is strictly smaller than the §4 seams. *)
Definition frozen_checker_sound_def:
  frozen_checker_sound (hol4_checks:'p -> 'b -> bool)
                       (sound:'b prover_obligation) ⇔
    ∀p B. hol4_checks p B ⇒ sound B
End

(* --------------------------------------------------------------------- *)
(* 3. THE META-THEOREM: prover self-improvement is safe.                 *)
(* --------------------------------------------------------------------- *)

(* The OPERATIONAL prover gate. The inhabitant proposes a NEW prover build
   B' with a proof object p', and B' returns a verdict `bcert` on a policy
   proposal (oldp ↦ newp). The envelope installs newp iff the FROZEN root
   accepted the build AND the build said yes. Nothing in the decision
   consults the semantic `admissible`: the frozen checker's soundness and
   the build's faithfulness are what make a "yes" trustworthy. *)
Definition prover_gate_def:
  prover_gate (hol4_checks:'p -> 'b -> bool) p' B' (bcert:bool)
              (oldp:('s,'a) policy) newp =
    gate (hol4_checks p' B' ∧ bcert) oldp newp
End

(* Claim: through the prover gate, safety holds for EVERY controller. The
   hypotheses on the certifiers are both load-bearing:
     * `frozen_checker_sound` turns the frozen root's acceptance into
       soundness of B' (unsound_frozen_checker_can_breach: without it an
       unsound build is adopted and breaches);
     * `bcert ⇒ build_certifies sound B' …` says a sound B' only says yes to
       admissible proposals (uncertified_build_can_breach: without it a
       vouched, sound-by-fiat build certifies an unsound policy).
   `hol4_checks p' B'` is no longer a hypothesis: it is the gate's input.
   If the root did not vouch, the gate rejects and safety is the original
   guarantee (unvouched_prover_swap_is_inert). *)
Theorem prover_self_improvement_is_safe:
  frozen_checker_sound hol4_checks sound ∧
  (bcert ⇒ build_certifies sound B' step safe oldp newp) ∧
  init_safe init safe ∧
  safe_shield step safe shield ∧
  sound_policy step safe oldp ⇒
  ∀ctrl. invariant step init
            (enveloped (prover_gate hol4_checks p' B' bcert oldp newp)
                       shield ctrl) safe
Proof
  rpt strip_tac >> simp[prover_gate_def] >>
  irule gate_preserves_safety >> rw[] >>
  metis_tac[frozen_checker_sound_def, build_certifies_def, admissible_def]
QED

(* When the frozen root accepted the build and the build said yes, the
   policy weakening is genuinely INSTALLED, and what was installed is a
   certified genuine weakening (sound, at least as permissive). *)
Theorem prover_self_improvement_installs:
  hol4_checks p' B' ∧ bcert ∧
  frozen_checker_sound hol4_checks sound ∧
  build_certifies sound B' step safe oldp newp ⇒
  prover_gate hol4_checks p' B' bcert oldp newp = newp ∧
  admissible step safe oldp newp
Proof
  rpt strip_tac >- rw[prover_gate_def, gate_def] >>
  metis_tac[frozen_checker_sound_def, build_certifies_def]
QED

(* A build that the frozen root did NOT accept changes nothing, whatever it
   certifies and however unsound it is: the gate keeps the old policy and
   safety holds via the ORIGINAL guarantee. No hypothesis on the build. *)
Theorem unvouched_prover_swap_is_inert:
  ¬hol4_checks p' B' ∧
  init_safe init safe ∧
  safe_shield step safe shield ∧
  sound_policy step safe oldp ⇒
  prover_gate hol4_checks p' B' bcert oldp newp = oldp ∧
  ∀ctrl. invariant step init
            (enveloped (prover_gate hol4_checks p' B' bcert oldp newp)
                       shield ctrl) safe
Proof
  strip_tac >>
  ‘prover_gate hol4_checks p' B' bcert oldp newp = oldp’
    by rw[prover_gate_def, gate_def] >>
  simp[] >> metis_tac[safety_preservation]
QED

(* NECESSITY of frozen_checker_sound: a checker that vouches for a build
   whose soundness obligation fails lets that build certify an unsound
   policy, and the enveloped system breaches. *)
Theorem unsound_frozen_checker_can_breach:
  ∃(hol4_checks:num -> num -> bool) sound p' B' bcert
   (step:num -> num -> num) safe init shield oldp newp ctrl.
    ¬frozen_checker_sound hol4_checks sound ∧
    hol4_checks p' B' ∧
    (bcert ⇒ build_certifies sound B' step safe oldp newp) ∧
    init_safe init safe ∧
    safe_shield step safe shield ∧
    sound_policy step safe oldp ∧
    ¬invariant step init
       (enveloped (prover_gate hol4_checks p' B' bcert oldp newp) shield ctrl)
       safe
Proof
  strip_assume_tac unsound_certificate_breaches >>
  qexistsl_tac [‘λp B. T’, ‘λB. F’, ‘0’, ‘0’, ‘T’, ‘step’, ‘safe’, ‘init’,
                ‘shield’, ‘oldp’, ‘newp’, ‘ctrl’] >>
  fs[frozen_checker_sound_def, build_certifies_def, prover_gate_def]
QED

(* NECESSITY of the build premise: the frozen checker is sound, the root
   vouched for the build, the build said yes -- and without the build
   being faithful to admissibility the installed policy breaches. *)
Theorem uncertified_build_can_breach:
  ∃(hol4_checks:num -> num -> bool) sound p' B'
   (step:num -> num -> num) safe init shield oldp newp ctrl.
    frozen_checker_sound hol4_checks sound ∧
    hol4_checks p' B' ∧
    ¬build_certifies sound B' step safe oldp newp ∧
    init_safe init safe ∧
    safe_shield step safe shield ∧
    sound_policy step safe oldp ∧
    ¬invariant step init
       (enveloped (prover_gate hol4_checks p' B' T oldp newp) shield ctrl)
       safe
Proof
  strip_assume_tac unsound_certificate_breaches >>
  qexistsl_tac [‘λp B. T’, ‘λB. T’, ‘0’, ‘0’, ‘step’, ‘safe’, ‘init’,
                ‘shield’, ‘oldp’, ‘newp’, ‘ctrl’] >>
  fs[frozen_checker_sound_def, build_certifies_def, prover_gate_def,
     admissible_def]
QED

(* --------------------------------------------------------------------- *)
(* 4. COMPOSITION with the existing self-improvement core.               *)
(* --------------------------------------------------------------------- *)

(* The stream form of the prover gate: every verdict of B' on a stream of
   proposals passes through the frozen root's acceptance of B'. *)
Definition prover_gate_all_def:
  prover_gate_all (hol4_checks:'p -> 'b -> bool) p' B' (p0:('s,'a) policy)
                  proposals =
    gate_all p0 (MAP (λ(bcert,newp). (hol4_checks p' B' ∧ bcert, newp))
                     proposals)
End

(* After a frozen-root-vouched prover swap, an UNBOUNDED stream of policy
   proposals decided by the new build B' keeps safety for every controller.
   The premise is on B' only through the frozen root: IF B' is sound, every
   yes it gives is to a sound policy. frozen_checker_sound turns the root's
   acceptance into soundness of B'; if the root did not accept, every
   proposal is rejected. This is upgradeTheory's gated_self_improvement_
   is_safe with certificates issued by the new prover. *)
Theorem prover_then_unbounded_policy_self_improvement_is_safe:
  frozen_checker_sound hol4_checks sound ∧
  (sound B' ⇒
     EVERY (λ(bcert,newp). bcert ⇒ sound_policy step safe newp) proposals) ∧
  init_safe init safe ∧
  safe_shield step safe shield ∧
  sound_policy step safe p0 ⇒
  ∀ctrl.
    invariant step init
      (enveloped (prover_gate_all hol4_checks p' B' p0 proposals) shield ctrl)
      safe
Proof
  rpt strip_tac >> simp[prover_gate_all_def] >>
  irule gated_self_improvement_is_safe >> simp[] >>
  simp[EVERY_MAP, EVERY_MEM, pairTheory.FORALL_PROD] >>
  rpt strip_tac >>
  ‘sound B'’ by metis_tac[frozen_checker_sound_def] >>
  fs[EVERY_MEM, pairTheory.FORALL_PROD] >> metis_tac[]
QED

(* And it composes the OTHER direction too: a frozen-root-vouched build B'
   certifies loosening the envelope from q to p; through the prover gate the
   system keeps the full safety guarantee AND the controller loses no
   authority it had under q (sv_weakeningTheory.safe_weakening, whose
   weakening premise is here SUPPLIED by B''s certificate). *)
Theorem prover_swap_then_safe_weakening:
  frozen_checker_sound hol4_checks sound ∧
  (bcert ⇒ build_certifies sound B' step safe q p) ∧
  init_safe init safe ∧
  safe_shield step safe shield ∧
  sound_policy step safe q ⇒
  ∀ctrl.
    invariant step init
      (enveloped (prover_gate hol4_checks p' B' bcert q p) shield ctrl) safe ∧
    ∀s. enveloped q shield ctrl s = ctrl s ∧ q s (ctrl s) ⇒
        enveloped (prover_gate hol4_checks p' B' bcert q p) shield ctrl s =
        ctrl s
Proof
  rpt gen_tac >> strip_tac >> gen_tac >>
  Cases_on ‘hol4_checks p' B' ∧ bcert’
  >- (‘prover_gate hol4_checks p' B' bcert q p = p’
        by fs[prover_gate_def, gate_def] >>
      ‘admissible step safe q p’
        by metis_tac[frozen_checker_sound_def, build_certifies_def] >>
      fs[admissible_def] >> metis_tac[safe_weakening])
  >- (‘prover_gate hol4_checks p' B' bcert q p = q’
        by (fs[prover_gate_def, gate_def] >> metis_tac[]) >>
      simp[] >> metis_tac[safety_preservation])
QED

(* --------------------------------------------------------------------- *)
(* 5. THE NO-LÖB SOUNDNESS ARGUMENT (precise).                           *)
(* --------------------------------------------------------------------- *)

(*
  Why this layer needs NO reflection principle / NO loeb_reflection.

  loeb_reflection (kernelUpgradeTheory) has the shape

      K thy sound_stmt ⇒ kernel_sound mem K'

  where K is the CURRENT kernel and K' is its PROPOSED REPLACEMENT, and
  `sound_stmt` is the embedded proposition "K' is sound". The certifier (K)
  and the upgrade target (K') are the SAME KIND OF OBJECT on the SAME LEVEL:
  a kernel certifying a statement about a kernel that will REPLACE IT. That
  is genuine self-reference. Gödel/Löb: a sound K cannot prove that schema
  for free; the only escape is the stratified Large-Cardinal route (LCA),
  which is precisely why `loeb_reflection` is a labelled, LCA-discharged
  hypothesis there.

  `frozen_checker_sound` here has the shape

      ∀p B. hol4_checks p B ⇒ sound B

  with `hol4_checks` the FROZEN HOL4 LCF kernel and `B` a Candle/CakeML
  *build*. Three facts make this NOT self-reference:

    (a) DIFFERENT LEVELS. `hol4_checks` is the immovable bottom turtle. `B`
        is an artifact on the layer ABOVE it. A fixed lower level vouching
        for a higher mutable artifact is the ordinary, sound LCF discipline
        (it is exactly how Candle's soundness is established TODAY:
        holSoundnessTheory.proves_sound is a HOL4 theorem ABOUT Candle).

    (b) THE ROOT NEVER MOVES. `hol4_checks` is FROZEN by fiat — the
        inhabitant cannot propose a new HOL4 kernel here (that distinct,
        genuinely self-referential seam is the SEPARATE
        kernelUpgradeTheory.loeb_reflection turtle, kept and labelled
        elsewhere). There is no `K'` for `hol4_checks`; `B'` is not a HOL4
        kernel, it is a Candle build whose soundness is a theorem the frozen
        HOL4 proves. No fixed point of the checker is ever asserted.

    (c) NO DIAGONALISATION. The antecedent is "frozen HOL4 replayed a
        concrete proof p and accepted B", not "the system proved its own
        global soundness". Discharging it for a concrete B is just running
        the frozen kernel on the (already-built) holSoundness development for
        that build — finite proof replay, NOT a reflection/LCA construction.

  Hence `prover_self_improvement_is_safe` carries `frozen_checker_sound` (a
  finite-proof-replay trust axiom, load-bearing: see
  unsound_frozen_checker_can_breach) and NOT `loeb_reflection`. The two are
  independent turtles: this layer's seam is strictly smaller and is
  discharged by ordinary proof replay (follow-up #28), whereas the
  kernel-replacing-itself seam genuinely needs the LCA. We checked: the
  abstraction does NOT smuggle in self-reference — `hol4_checks` and `B`
  inhabit different type variables ('p/'b) and `hol4_checks` is never the
  thing varied/upgraded.
*)

val _ = export_theory ();
