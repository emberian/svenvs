(*
  The real (deeply-embedded) admission gate.

  The shallow `cartpoleProgramScript` checked obligations with HOL4's own
  metis. Here the obligation is a term of Candle's *deeply-embedded* HOL
  (`holSyntax`), and it is discharged by Candle's *verified inference
  system* `|-` (`proves`). Soundness of that kernel —
  `holSoundnessTheory.proves_sound : is_set_theory mem ⇒ thyh |- c ⇒ thyh |= c`
  — is what makes a kernel-checked obligation trustworthy.

  We prove: the embedded gate `kernel_gate` -- which installs a proposal iff
  the Candle kernel DERIVED its obligation term -- preserves safety for
  every controller whenever the term faithfully encodes the meta
  obligation. The gate decides on the derivation, not on the truth, so
  `proves_sound` is load-bearing; and `unfaithful_encoding_can_breach`
  shows the encoding hypothesis is load-bearing too. The faithful-encoding
  predicate `encodes_obligation` is the single explicit seam that the
  hol-reflection proof-producing translator discharges automatically
  (`term_to_deep`/`termsem_cert`); everything else here is proved outright
  from the built Candle soundness theorem.
*)
open HolKernel boolLib bossLib BasicProvers
     holSyntaxTheory holSyntaxExtraTheory holSemanticsTheory holSoundnessTheory
     systemTheory envelopeTheory safetyTheory sv_weakeningTheory upgradeTheory;

val _ = new_theory "embeddedGate";

val _ = Parse.hide "mem";
val mem = ``mem:'U->'U->bool``;

(* The Candle kernel has derived the (closed) obligation term [obl] in
   theory [thy]. `|-` here is `proves`, the verified inference system. *)
Definition kernel_admits_def:
  kernel_admits ^mem thy obl ⇔ is_set_theory mem ∧ (thy,[]) |- obl
End

(* The seam: [obl]'s semantic content is exactly the meta-level
   admissibility obligation. hol-reflection's term_to_deep/termsem_cert
   produce precisely a theorem of this shape for the reflected obligation;
   we keep it abstract so the gate's soundness does not depend on the
   reflection automation (which is being ported in parallel). *)
Definition encodes_obligation_def:
  encodes_obligation ^mem thy obl step safe oldp newp ⇔
    ((thy,[]) |= obl ⇒ admissible step safe oldp newp)
End

(* Candle's verified kernel really does only certify semantic truths. *)
Theorem kernel_admits_is_sound:
  kernel_admits ^mem thy obl ⇒ (thy,[]) |= obl
Proof
  rw[kernel_admits_def] >> metis_tac[proves_sound]
QED

(* The embedded gate: install [newp] iff the Candle kernel DERIVED the
   obligation term. The decision is syntactic (a `|-` derivation), never
   the semantic `admissible`; `proves_sound` is what connects the two. *)
Definition kernel_gate_def:
  kernel_gate ^mem thy obl oldp newp = gate (kernel_admits ^mem thy obl) oldp newp
End

(* THE THEOREM: the enveloped system stays safe for ANY controller through
   the embedded gate, whatever the Candle kernel did or did not derive.
   If it derived [obl], proves_sound makes [obl] valid, the faithful
   encoding turns validity into admissibility, and the installed policy is
   sound; if it did not, the old policy stays. Both hypotheses on the
   certificate are load-bearing: kernel_admits_is_sound (proves_sound) and
   encodes_obligation (unfaithful_encoding_can_breach shows it cannot be
   dropped). *)
Theorem embedded_admit_preserves_safety:
  init_safe init safe ∧
  safe_shield step safe shield ∧
  sound_policy step safe oldp ∧
  encodes_obligation ^mem thy obl step safe oldp newp ⇒
  ∀ctrl. invariant step init
            (enveloped (kernel_gate ^mem thy obl oldp newp) shield ctrl) safe
Proof
  rpt strip_tac >>
  simp[kernel_gate_def] >>
  irule gate_preserves_safety >> fs[] >>
  metis_tac[kernel_admits_is_sound, encodes_obligation_def, admissible_def]
QED

(* When the kernel derived the obligation, the upgrade is installed, and
   (through proves_sound and the faithful encoding) what was installed is a
   certified genuine weakening: sound and at least as permissive. *)
Theorem embedded_admit_installs:
  kernel_admits ^mem thy obl ∧
  encodes_obligation ^mem thy obl step safe oldp newp ⇒
  kernel_gate ^mem thy obl oldp newp = newp ∧
  admissible step safe oldp newp
Proof
  rpt strip_tac >- rw[kernel_gate_def, gate_def] >>
  metis_tac[kernel_admits_is_sound, encodes_obligation_def]
QED

(* When the kernel derived nothing, nothing changes. *)
Theorem embedded_gate_rejects:
  ¬kernel_admits ^mem thy obl ⇒ kernel_gate ^mem thy obl oldp newp = oldp
Proof
  rw[kernel_gate_def, gate_def]
QED

(* On a certified, faithfully-encoded proposal the operational gate and the
   oracle gate `admit` agree. *)
Theorem embedded_gate_agrees_with_admit:
  kernel_admits ^mem thy obl ∧
  encodes_obligation ^mem thy obl step safe oldp newp ⇒
  kernel_gate ^mem thy obl oldp newp = admit step safe oldp newp
Proof
  metis_tac[embedded_admit_installs, admit_def]
QED

(* ---------------------------------------------------------------------
   A concrete Candle derivation: in the initial theory context (theory_ok
   by holSyntaxExtraTheory.init_theory_ok), REFL derives x = x at bool.
   Used below and in kernelUpgrade to exhibit certificates that exist.
   --------------------------------------------------------------------- *)
Theorem candle_refl_witness:
  (thyof init_ctxt, []) |- Var x Bool === Var x Bool
Proof
  irule proves_REFL >> simp[init_theory_ok] >>
  assume_tac (MATCH_MP theory_ok_sig init_theory_ok) >>
  fs[is_std_sig_def, term_ok_def, type_ok_def]
QED

(* NECESSITY of the faithful encoding: with a set theory present, the Candle
   kernel genuinely derives an obligation term, the old policy, shield and
   initial states are all sound, and yet the embedded gate breaches safety
   -- because the derived term does not encode the admissibility of the
   proposal. So `encodes_obligation` is doing real work in
   embedded_admit_preserves_safety. *)
Theorem unfaithful_encoding_can_breach:
  is_set_theory ^mem ⇒
  ∃thy obl (step:num -> num -> num) safe init shield oldp newp ctrl.
    kernel_admits ^mem thy obl ∧
    ¬encodes_obligation ^mem thy obl step safe oldp newp ∧
    init_safe init safe ∧
    safe_shield step safe shield ∧
    sound_policy step safe oldp ∧
    ¬invariant step init
       (enveloped (kernel_gate ^mem thy obl oldp newp) shield ctrl) safe
Proof
  strip_tac >>
  ‘kernel_admits ^mem (thyof init_ctxt) (Var x Bool === Var x Bool)’
    by rw[kernel_admits_def, candle_refl_witness] >>
  strip_assume_tac unsound_certificate_breaches >>
  qexistsl_tac [‘thyof init_ctxt’, ‘Var x Bool === Var x Bool’, ‘step’,
                ‘safe’, ‘init’, ‘shield’, ‘oldp’, ‘newp’, ‘ctrl’] >>
  fs[kernel_gate_def, encodes_obligation_def, admissible_def] >>
  metis_tac[kernel_admits_is_sound]
QED

val _ = export_theory ();
