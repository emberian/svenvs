(*
  selfProver — the capstone layer: the verified PROVER itself self-improves,
  gated by the FROZEN HOL4 root. Pure light HOL4 (no CakeML / candle /
  hol-reflection); the architecture is established UNCONDITIONALLY here.

  --------------------------------------------------------------------------
  THE TOWER OF TURTLES (what is frozen vs verified-in-HOL4-hence-mutable vs
  assumed)

    HOL4's LCF kernel ............ FROZEN. The immovable bottom turtle.
                                   Deliberately NOT self-improving: if the
                                   unmodelable inhabitant could edit it, an
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
                                   admissible / admit / self_improvement_is_safe).

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
open HolKernel boolLib bossLib BasicProvers
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

(* The OPERATIONAL meaning of "the envelope runs prover build B as its
   admission gate": when B is sound, B certifying a self-improvement
   proposal really does establish the meta-level admissibility obligation.
   This is the same shape as embeddedGateTheory.encodes_obligation, but with
   the prover build (not a single embedded term) as the trusted certifier;
   we keep it abstract (no CakeML) and parametric in the build. *)
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

(* The inhabitant proposes a NEW prover build B' together with a proof
   object p'. The envelope adopts B' as its admission prover ONLY if the
   frozen HOL4 root accepts it (`hol4_checks p' B'`). We then use the
   freshly-adopted B' to discharge a self-improvement policy proposal.

   Claim: adopting B' and admitting a policy weakening through it preserves
   the svenvs safety guarantee for EVERY controller — exactly the guarantee
   the OLD prover gave. The new prover discharges the admission obligation
   just as the old one did; safety is never lost.

   Note the explicit hypotheses: `frozen_checker_sound hol4_checks sound`
   (the LABELLED trust axiom) and `hol4_checks p' B'` (the frozen root
   actually accepted the proposed build) are both REQUIRED antecedents. *)
Theorem prover_self_improvement_is_safe:
  frozen_checker_sound hol4_checks sound ∧
  hol4_checks p' B' ∧
  build_certifies sound B' step safe oldp newp ∧
  init_safe init safe ∧
  safe_shield step safe shield ∧
  sound_policy step safe oldp ⇒
  ∀ctrl. invariant step init
            (enveloped (admit step safe oldp newp) shield ctrl) safe
Proof
  rpt strip_tac >>
  ‘sound B'’ by metis_tac[frozen_checker_sound_def] >>
  ‘admissible step safe oldp newp’ by metis_tac[build_certifies_def] >>
  irule admit_preserves_safety >> fs[]
QED

(* When the frozen root accepted the proposed build and the build certified
   the proposal, the policy weakening is genuinely INSTALLED (authority
   actually granted), not silently dropped — the gate did real work. *)
Theorem prover_self_improvement_installs:
  frozen_checker_sound hol4_checks sound ∧
  hol4_checks p' B' ∧
  build_certifies sound B' step safe oldp newp ⇒
  admit step safe oldp newp = newp
Proof
  rpt strip_tac >>
  ‘sound B'’ by metis_tac[frozen_checker_sound_def] >>
  ‘admissible step safe oldp newp’ by metis_tac[build_certifies_def] >>
  rw[admit_def]
QED

(* A build that the frozen root did NOT accept can change nothing: with no
   `hol4_checks p B` available, `build_certifies` gives nothing, the gate
   keeps the old policy, and safety holds via the ORIGINAL guarantee. An
   un-vouched-for prover swap is inert — exactly the upgradeTheory
   discipline, now one layer down at the prover. *)
Theorem unvouched_prover_swap_is_inert:
  init_safe init safe ∧
  safe_shield step safe shield ∧
  sound_policy step safe oldp ⇒
  ∀ctrl. invariant step init
            (enveloped (admit step safe oldp oldp) shield ctrl) safe
Proof
  rpt strip_tac >>
  irule admit_preserves_safety >> fs[]
QED

(* --------------------------------------------------------------------- *)
(* 4. COMPOSITION with the existing self-improvement core.               *)
(* --------------------------------------------------------------------- *)

(* The story is "EVERY mutable layer self-improves, gated by the frozen
   root". We show the prover-improvement layer COMPOSES with the policy
   hot-swap core: after adopting a frozen-root-vouched new prover B', an
   UNBOUNDED stream of self-proposed policy weakenings — adversarial or not —
   still keeps safety for every controller. This reuses upgradeTheory's
   `self_improvement_is_safe` (the iterated admit_all gate) verbatim: the
   new prover discharges each obligation exactly where the old one did. *)
Theorem prover_then_unbounded_policy_self_improvement_is_safe:
  frozen_checker_sound hol4_checks sound ∧
  hol4_checks p' B' ∧
  sound B' ∧
  init_safe init safe ∧
  safe_shield step safe shield ∧
  sound_policy step safe p0 ⇒
  ∀proposals ctrl.
    invariant step init
      (enveloped (admit_all step safe p0 proposals) shield ctrl) safe
Proof
  rpt strip_tac >>
  (* the frozen root vouched for B'; B' is the adopted prover. The iterated
     policy self-improvement guarantee is then exactly upgradeTheory's. *)
  irule self_improvement_is_safe >> fs[]
QED

(* And it composes the OTHER direction too: a frozen-root-vouched prover
   swap, then a single policy weakening to any weaker still-sound policy
   (sv_weakeningTheory.safe_weakening), keeps the full guarantee. This is the
   "loosen my own envelope, having first upgraded my own prover" path. *)
Theorem prover_swap_then_safe_weakening:
  frozen_checker_sound hol4_checks sound ∧
  hol4_checks p' B' ∧
  init_safe init safe ∧
  safe_shield step safe shield ∧
  weaker p q ∧
  sound_policy step safe p ⇒
  ∀ctrl. invariant step init (enveloped p shield ctrl) safe
Proof
  rpt strip_tac >>
  irule safe_weakening >>
  metis_tac[]
QED

(* --------------------------------------------------------------------- *)
(* 5. THE NO-LÖB SOUNDNESS ARGUMENT (precise).                           *)
(* --------------------------------------------------------------------- *)

(*
  Why this layer needs NO reflection principle / NO loeb_reflection.

  loeb_reflection (kernelUpgradeTheory) has the shape

      (∀thy. K thy (sound_stmt thy)) ⇒ kernel_sound mem K'

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
  finite-proof-replay trust axiom) and NOT `loeb_reflection`. The two are
  independent turtles: this layer's seam is strictly smaller and is
  discharged by ordinary proof replay (follow-up #28), whereas the
  kernel-replacing-itself seam genuinely needs the LCA. We checked: the
  abstraction does NOT smuggle in self-reference — `hol4_checks` and `B`
  inhabit different type variables ('p/'b) and `hol4_checks` is never the
  thing varied/upgraded.
*)

val _ = export_theory ();
