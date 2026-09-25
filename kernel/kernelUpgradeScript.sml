(*
  Upgrading the guard-checker / proof kernel itself.

  embeddedGate fixed the checker as Candle's verified inference system `|-`
  (sound by holSoundnessTheory.proves_sound). Here the *checker is a
  parameter*: a kernel is an abstract admit-predicate K : thy -> term -> bool,
  and a self-improving system may propose to REPLACE its kernel with a
  stronger K'.

  THE SHAPE OF THE ARGUMENT. Soundness of a kernel is exactly the property
  that its "yes" transfers to every fact the certified term faithfully
  encodes (`kernel_sound_iff_transfers`). Two facts then carry everything:

    * an ENCODING seam `encodes_soundness mem thy s K'`
        ⇔ ((thy,[]) |= s ⇒ kernel_sound mem K')
      -- the same kind of seam as embeddedGate's `encodes_obligation`, with
      "K' is sound" in place of "the proposal is admissible"; and
    * a DERIVATION `candle_kernel thy s`.

  Together they make K' sound by a plain theorem (`candle_lifts_soundness`):
  no reflection principle is assumed anywhere. `loeb_reflection` survives as
  the NAME of the derived notion (`loeb_reflection_from_soundness`).

  THE TRAP, stated as a theorem. An encoding seam of the form (|= s ⇒ Q)
  holds whenever Q already holds; so "there is a derived s encoding K''s
  soundness" (`soundness_witness`) is EQUIVALENT to "K' is sound"
  (`soundness_witness_iff_sound`). The predicate therefore carries no
  information beyond soundness. The genuine content is the PROVENANCE of
  the encoding certificate: the hol-reflection translator (termsem_cert /
  build_master_theorem over the LCA model, kernel/loebReduction) produces
  `encodes_soundness` theorems by construction, not by already knowing K'
  sound. Gödel/Löb says that for a strictly stronger K' the construction
  cannot be carried out inside K's own strength; the large-cardinal route
  (Fallenstein–Kumar; hol-reflection/lca) is how it is done. The open
  residue is CONSTRUCTING that witness (theory, term, Candle derivation,
  encoding certificate) for a strictly stronger K' -- not an assumed
  principle.

  The policy gate is OPERATIONAL (`kgate`: install iff the kernel said yes),
  so the kernel's soundness, the Candle derivation, the soundness encoding
  and the obligation encoding are each load-bearing, and each has a
  machine-checked necessity theorem below.
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

(* ===================================================================== *)
(*  Soundness IS transfer.                                               *)
(* ===================================================================== *)

(* A kernel is sound exactly when its "yes" transfers to every fact P that
   the certified term faithfully encodes ((thy,[]) |= t ⇒ P). This is the
   kernel instance of the abstract certifier_sound_iff_transfers; the
   theorems below that turn a kernel's yes into a real fact (a soundness
   lift, an admissible upgrade, a safe gate) are instances of it. *)
(* kernel_sound IS certifier soundness at meaning := entailment
   (certifierTheory, via embeddedGateTheory's two-argument form). *)
Theorem kernel_sound_is_sound_certifier:
  kernel_sound ^mem K0 ⇔ sound_certifier (UNCURRY K0) (kernel_meaning ^mem)
Proof
  rw[kernel_sound_def, kernel_soundness_is_sound_certifier]
QED

Theorem kernel_sound_iff_transfers:
  kernel_sound ^mem K0 ⇔
  ∀thy t P. K0 thy t ∧ ((thy,[]) |= t ⇒ P) ⇒ P
Proof
  rw[kernel_sound_def, kernel_soundness_iff_transfers]
QED

(* ===================================================================== *)
(*  Lifting soundness to a new kernel: an encoding seam, not a principle. *)
(* ===================================================================== *)

(* The ENCODING seam for kernel upgrade, the same kind as
   embeddedGateTheory.encodes_obligation: the semantic content of the term
   s in thy implies that K' is sound. *)
Definition encodes_soundness_def:
  encodes_soundness (^mem) (thy:thy) (s:term) (K':kernel) ⇔
    ((thy,[]) |= s ⇒ kernel_sound ^mem K')
End

(* A sound kernel that certifies a term encoding K''s soundness makes K'
   sound. An instance of kernel_sound_iff_transfers at P = kernel_sound K'. *)
Theorem sound_kernel_lifts_soundness:
  kernel_sound ^mem K0 ∧ K0 thy s ∧ encodes_soundness ^mem thy s K' ⇒
  kernel_sound ^mem K'
Proof
  rw[encodes_soundness_def] >>
  qpat_x_assum ‘kernel_sound _ K0’
    (mp_tac o PURE_ONCE_REWRITE_RULE [kernel_sound_iff_transfers]) >>
  disch_then (qspecl_then [‘thy’, ‘s’, ‘kernel_sound ^mem K'’] mp_tac) >>
  simp[]
QED

(* The Candle instance: the base kernel's derivation of an encoding term
   makes K' sound. *)
Theorem candle_lifts_soundness:
  is_set_theory ^mem ∧ candle_kernel thy s ∧ encodes_soundness ^mem thy s K' ⇒
  kernel_sound ^mem K'
Proof
  metis_tac[sound_kernel_lifts_soundness, candle_kernel_sound]
QED

(* `loeb_reflection` — the historical name, now for a DERIVED notion. It is
   NOT an assumption anywhere in svenvs any more: no theorem carries it as a
   hypothesis. It reads "if K certifies s in thy then K' is sound", and
   loeb_reflection_from_soundness proves it from K's soundness plus the
   encoding seam encodes_soundness. By itself it relates an ARBITRARY term s
   to K' and says nothing about what s denotes, which is why it was the
   wrong thing to assume (reflection_is_not_soundness).

   It is stated for ONE theory and ONE statement. An earlier form quantified
   the certificate over every theory, (∀thy. K thy (sound_stmt thy)) ⇒ …;
   that antecedent is unsatisfiable for the Candle kernel (Candle derives
   nothing in a theory that is not theory_ok), so every theorem carrying it
   was vacuous: old_reflection_antecedent_unsatisfiable below records this. *)
Definition loeb_reflection_def:
  loeb_reflection (^mem) (K:kernel) (K':kernel) (thy:thy) (sound_stmt:term) ⇔
    (K thy sound_stmt ⇒ kernel_sound ^mem K')
End

(* The "reflection principle" is a CONSEQUENCE of soundness of the certifying
   kernel plus a faithful encoding of K''s soundness. *)
Theorem loeb_reflection_from_soundness:
  kernel_sound ^mem K0 ∧ encodes_soundness ^mem thy s K' ⇒
  loeb_reflection ^mem K0 K' thy s
Proof
  metis_tac[loeb_reflection_def, sound_kernel_lifts_soundness]
QED

Theorem loeb_reflection_candle:
  is_set_theory ^mem ∧ encodes_soundness ^mem thy s K' ⇒
  loeb_reflection ^mem candle_kernel K' thy s
Proof
  metis_tac[loeb_reflection_from_soundness, candle_kernel_sound]
QED

(* Kernel self-upgrade (the historical name for candle_lifts_soundness):
   Candle derives s in thy, s encodes K''s soundness, so K' is sound.
   Each hypothesis is needed: certificate_without_reflection_can_breach
   (encoding) and reflection_without_certificate_can_breach (derivation). *)
Theorem kernel_self_upgrade_sound:
  is_set_theory ^mem ∧ candle_kernel thy s ∧ encodes_soundness ^mem thy s K' ⇒
  kernel_sound ^mem K'
Proof
  metis_tac[candle_lifts_soundness]
QED

(* ===================================================================== *)
(*  The residue, as a WITNESS obligation -- and the trap in it.           *)
(* ===================================================================== *)

(* A soundness witness for K': a theory and a term that Candle derives and
   whose semantic content implies K' is sound. *)
Definition soundness_witness_def:
  soundness_witness (^mem) (K':kernel) ⇔
    ∃thy s. candle_kernel thy s ∧ encodes_soundness ^mem thy s K'
End

Theorem witness_suffices:
  is_set_theory ^mem ∧ soundness_witness ^mem K' ⇒ kernel_sound ^mem K'
Proof
  metis_tac[soundness_witness_def, candle_lifts_soundness]
QED

(* THE TRAP (1): the encoding seam holds for EVERY theory and term as soon
   as K' is already sound -- its consequent is then a theorem. *)
Theorem sound_kernel_encoded_by_every_term:
  kernel_sound ^mem K' ⇒ ∀thy s. encodes_soundness ^mem thy s K'
Proof
  rw[encodes_soundness_def]
QED

(* THE TRAP (2): hence, given a set-theoretic model (the only side
   condition; the reverse direction needs none, since Candle derives x = x
   in the initial context by REFL -- embeddedGateTheory.candle_refl_witness),
   having a soundness witness is EQUIVALENT to being sound. The predicate
   soundness_witness is therefore not where the content lies: any sound K'
   has one trivially. What is genuine is the PROVENANCE of the encoding
   certificate -- whether encodes_soundness was produced by a construction
   (the hol-reflection translator's termsem certificate over a model; see
   kernel/loebReduction) rather than by already knowing K' sound. *)
Theorem soundness_witness_iff_sound:
  is_set_theory ^mem ⇒ (soundness_witness ^mem K' ⇔ kernel_sound ^mem K')
Proof
  strip_tac >> eq_tac
  >- metis_tac[witness_suffices]
  >- (rw[soundness_witness_def] >>
      qexistsl_tac [‘thyof init_ctxt’, ‘Var x Bool === Var x Bool’] >>
      rw[candle_kernel_def, candle_refl_witness,
         sound_kernel_encoded_by_every_term])
QED

(* The contrapositive, used for the obstruction in watchdogFinite: an
   unsound K' has no witness at all -- no Candle-derived term encodes its
   soundness. *)
Theorem unsound_kernel_has_no_witness:
  is_set_theory ^mem ∧ ¬kernel_sound ^mem K' ⇒ ¬soundness_witness ^mem K'
Proof
  metis_tac[witness_suffices]
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

(* A sound kernel's yes on a faithfully-encoded obligation yields
   admissibility: kernel_sound_iff_transfers at P = admissible. *)
Theorem sound_kernel_certifies_admissible:
  kernel_sound ^mem K' ∧ K' thy obl ∧
  encodes_obligation ^mem thy obl step safe oldp newp ⇒
  admissible step safe oldp newp
Proof
  rw[encodes_obligation_def] >>
  qpat_x_assum ‘kernel_sound _ K'’
    (mp_tac o PURE_ONCE_REWRITE_RULE [kernel_sound_iff_transfers]) >>
  disch_then (qspecl_then [‘thy’, ‘obl’, ‘admissible step safe oldp newp’]
                          mp_tac) >>
  simp[]
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
  metis_tac[sound_kernel_certifies_admissible, admissible_def]
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
  metis_tac[sound_kernel_certifies_admissible]
QED

(* The full self-improving-kernel statement, in one place: the verified base
   kernel derives, in theory sthy, a term s whose content implies K' is
   sound; so K' is sound (candle_lifts_soundness); K' then decides a policy
   upgrade through the operational gate; safety holds for any controller.
   No reflection principle is assumed. The two seams are both encodings:
   encodes_soundness (s says K' is sound) and encodes_obligation (obl says
   the proposal is admissible). *)
Theorem self_improving_kernel_is_safe:
  is_set_theory ^mem ∧
  candle_kernel sthy s ∧
  encodes_soundness ^mem sthy s K' ∧
  encodes_obligation ^mem thy obl step safe oldp newp ∧
  init_safe init safe ∧
  safe_shield step safe shield ∧
  sound_policy step safe oldp ⇒
  ∀ctrl. invariant step init
            (enveloped (kgate K' thy obl oldp newp) shield ctrl) safe
Proof
  rpt strip_tac >>
  ‘kernel_sound ^mem K'’ by metis_tac[candle_lifts_soundness] >>
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
   proposal in every (here: num) habitat. Forward: the transfer instance
   upgraded_kernel_preserves_safety. Backward: into the transfer form of
   soundness -- a certified t with (|= t ⇒ P) and ¬P would have t not
   entailed, and kernel_unsound_certificate_can_breach turns that into an
   unsafe gate. *)
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
  rw[kernel_sound_def, kgate_def, kernel_sound_certifier_iff_gate_safe]
QED

(* A Candle certificate of an UNRELATED true term encodes nothing about K'.
   In the initial theory context Candle derives x = x (REFL); the kernel
   that accepts everything is unsound; so "Candle certified x = x, hence
   the accept-all kernel is sound" (the loeb_reflection reading) FAILS, and,
   given a set-theoretic model, the reason is exactly that x = x does not
   encode the accept-all kernel's soundness: it is true, and that kernel is
   not sound. A sound certificate transfers only what the term encodes. *)
Theorem reflection_is_not_soundness:
  candle_kernel (thyof init_ctxt) (Var x Bool === Var x Bool) ∧
  ¬kernel_sound ^mem (λthy obl. T) ∧
  ¬loeb_reflection ^mem candle_kernel (λthy obl. T)
                   (thyof init_ctxt) (Var x Bool === Var x Bool) ∧
  (is_set_theory ^mem ⇒
   ¬encodes_soundness ^mem (thyof init_ctxt) (Var x Bool === Var x Bool)
                          (λthy obl. T))
Proof
  rw[candle_kernel_def, loeb_reflection_def, encodes_soundness_def,
     candle_refl_witness, accept_all_kernel_unsound] >>
  metis_tac[proves_sound, candle_refl_witness]
QED

(* NECESSITY of encodes_soundness in self_improving_kernel_is_safe: a set
   theory, a real Candle derivation, a faithful obligation encoding and a
   sound habitat, and still a breach, because the derived term does not
   encode K''s soundness. (The historical name refers to the reflection
   principle that the encoding seam replaces.) *)
Theorem certificate_without_reflection_can_breach:
  is_set_theory ^mem ⇒
  ∃K' sthy s thy obl (step:num -> num -> num) safe init shield
     oldp newp ctrl.
    candle_kernel sthy s ∧
    ¬encodes_soundness ^mem sthy s K' ∧
    ¬loeb_reflection ^mem candle_kernel K' sthy s ∧
    encodes_obligation ^mem thy obl step safe oldp newp ∧
    init_safe init safe ∧
    safe_shield step safe shield ∧
    sound_policy step safe oldp ∧
    ¬invariant step init (enveloped (kgate K' thy obl oldp newp) shield ctrl) safe
Proof
  strip_tac >>
  ‘(λthy obl. T) thy (Var y (Tyvar a)) ∧ ¬((thy,[]) |= Var y (Tyvar a))’
    by rw[ill_typed_never_entailed] >>
  drule_all kernel_unsound_certificate_can_breach >> strip_tac >>
  qexistsl_tac [‘λthy obl. T’, ‘thyof init_ctxt’, ‘Var x Bool === Var x Bool’,
                ‘thy’, ‘Var y (Tyvar a)’, ‘step’, ‘safe’, ‘init’, ‘shield’,
                ‘oldp’, ‘newp’, ‘ctrl’] >>
  metis_tac[reflection_is_not_soundness]
QED

(* NECESSITY of the Candle derivation: without it the encoding seam holds
   vacuously -- here for the accept-everything kernel and an ill-typed term,
   which nothing entails and Candle never derives -- and the gate that
   kernel drives breaches. *)
Theorem reflection_without_certificate_can_breach:
  ∃K' sthy s thy obl (step:num -> num -> num) safe init shield
     oldp newp ctrl.
    encodes_soundness ^mem sthy s K' ∧
    loeb_reflection ^mem candle_kernel K' sthy s ∧
    ¬candle_kernel sthy s ∧
    encodes_obligation ^mem thy obl step safe oldp newp ∧
    init_safe init safe ∧
    safe_shield step safe shield ∧
    sound_policy step safe oldp ∧
    ¬invariant step init (enveloped (kgate K' thy obl oldp newp) shield ctrl) safe
Proof
  ‘(λthy obl. T) thy (Var y (Tyvar a)) ∧ ¬((thy,[]) |= Var y (Tyvar a))’
    by rw[ill_typed_never_entailed] >>
  drule_all kernel_unsound_certificate_can_breach >> strip_tac >>
  ‘¬candle_kernel thy (Var y (Tyvar a))’
    by (rw[candle_kernel_def] >> strip_tac >>
        imp_res_tac proves_term_ok >> fs[] >>
        qpat_x_assum ‘_ has_type _’ mp_tac >> simp[Once has_type_cases]) >>
  qexistsl_tac [‘λthy obl. T’, ‘thy’, ‘Var y (Tyvar a)’,
                ‘thy’, ‘Var y (Tyvar a)’, ‘step’, ‘safe’, ‘init’, ‘shield’,
                ‘oldp’, ‘newp’, ‘ctrl’] >>
  fs[loeb_reflection_def, encodes_soundness_def, ill_typed_never_entailed]
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

val _ = export_theory ();
