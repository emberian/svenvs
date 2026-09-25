(*
  loebReduction — where a soundness WITNESS for an upgraded kernel K' comes
  from: the Large-Cardinal reflection construction of hol-reflection/lca
  (Fallenstein–Kumar), with the semantic chain done in-logic.

  kernelUpgradeTheory reduces kernel self-upgrade to a witness
    soundness_witness mem K' ⇔
      ∃thy s. candle_kernel thy s ∧ encodes_soundness mem thy s K'
  and proves (soundness_witness_iff_sound) that the PREDICATE is equivalent
  to K' being sound: an encoding seam (|= s ⇒ Q) holds whenever Q already
  does. So the content is not the predicate but the PROVENANCE of the
  encoding half. This theory says where that half comes from.

  WHAT THIS IS / IS NOT
  ---------------------
  PURE candle-semantics HOL4. It does NOT discharge the LCA itself: that is
  the 137 KB `lcaProofTheory.intermediate_thm` + `lcaLib.build_master_theorem`
  construction, CPU/RAM-walled (tens of GB resident, ~CPU-hours per
  prerequisite theory — CLAIMS.md §9), and NOT required for this reduction.

  What it DOES, machine-checked and cheat-free: the witness splits into

    (1) the DERIVATION half, `candle_kernel lca_thy s` — a Candle proof in
        the LCA theory; its semantic force is `kernel_proves_satisfied`
        (reflectionTheory.provable_imp_eq_true, re-derived here from
        candle's `proves_sound`): a certified term holds in EVERY model;

    (2) the ENCODING half, `encodes_soundness mem lca_thy s K'`, which
        `lca_encodes_soundness` DERIVES from the ingredient
        `lca_reflects_soundness`: a model of lca_thy (intermediate_thm,
        valid under LCA (SUC l)) in which s being true DECODES to the
        external `kernel_sound mem K'` (the termsem certificate of
        build_master_theorem for the reflected predicate φ = the encoding
        of `kernel_sound mem K'`). The translator produces that decoding by
        construction, from the syntax of φ, not from knowing K' sound; for
        a strictly stronger K' the model must come from the LCA.

  `kernel_self_upgrade_sound_from_lca` puts the halves together into a
  witness and soundness of K'. The residue is exactly: CONSTRUCT
  lca_reflects_soundness (and the derivation) for a strictly stronger K' by
  the lca route.

  The svenvs definitions (kernel_sound, candle_kernel, encodes_soundness,
  soundness_witness, loeb_reflection) are kernelUpgradeTheory's OWN
  constants, opened below — not restated copies.
*)
open HolKernel boolLib bossLib BasicProvers
     holSyntaxTheory holSemanticsTheory holSemanticsExtraTheory
     holSoundnessTheory kernelUpgradeTheory;

val _ = new_theory "loebReduction";

val _ = Parse.hide "mem";
val mem = ``mem:'U->'U->bool``;

(* ----------------------------------------------------------------------
   Ingredient (1): the Candle kernel's certificates are semantically valid.
   This is `reflectionTheory.provable_imp_eq_true` specialised to empty
   hypotheses, re-derived here directly from `proves_sound` (no cheat). It says:
   if the base kernel certifies `sound_stmt` in `thy`, then `sound_stmt` holds in
   EVERY model i of thy, under any valuation.

   `satisfies` for a model is the candle notion: (sigof thy, h, c) is satisfied
   by i iff every valuation making all of h true makes c true (termsem = True).
   With h = [] this is just: termsem of c is True in i under every valuation.
   ---------------------------------------------------------------------- *)

Theorem kernel_proves_satisfied:
  is_set_theory ^mem ⇒
  ∀thy c.
    candle_kernel thy c ⇒
    ∀i. i models thy ⇒ i satisfies (sigof thy,[],c)
Proof
  rw[candle_kernel_def] >>
  `(thy,[]) |= c` by metis_tac[proves_sound] >>
  fs[entails_def]
QED

(* ----------------------------------------------------------------------
   Ingredient (2): the LCA reflection-and-decoding hypothesis (CITED).

   This packages what hol-reflection/lca's master theorem provides for the
   reflected predicate φ = (encoding of) `kernel_sound mem K'`:

     - there is a model `lca_model` of theory `lca_thy` (from
       `intermediate_thm`, valid under LCA (SUC l)); and
     - in that model, with valuation `lca_val`, the internal statement
       `sound_stmt` being satisfied DECODES to the external truth
       `kernel_sound mem K'` (the termsem-cert / decoding step of
       `build_master_theorem`).

   Like every encoding seam its last conjunct is met trivially by a K'
   already known sound (kernelUpgradeTheory.sound_kernel_encoded_by_every_term);
   its value is that the lca construction PRODUCES it without that
   knowledge. It is a named antecedent, never a cheat. *)

Definition lca_reflects_soundness_def:
  lca_reflects_soundness (^mem) (K':kernel) (sound_stmt:term)
                         (lca_thy:thy) lca_model lca_val ⇔
    lca_model models lca_thy ∧
    is_valuation (tysof (sigof lca_thy)) (tyaof lca_model) lca_val ∧
    (termsem (tmsof (sigof lca_thy)) lca_model lca_val sound_stmt = True
       ⇒ kernel_sound ^mem K')
End

(* ----------------------------------------------------------------------
   The ENCODING half, derived: a model in which s decodes to K''s soundness
   makes s encode K''s soundness. If (lca_thy,[]) |= s then s is satisfied
   in every model of lca_thy, in particular in lca_model at lca_val, so
   termsem = True there, and the decoding gives kernel_sound mem K'.
   ---------------------------------------------------------------------- *)

Theorem lca_encodes_soundness:
  lca_reflects_soundness ^mem K' sound_stmt lca_thy lca_model lca_val ⇒
  encodes_soundness ^mem lca_thy sound_stmt K'
Proof
  rw[lca_reflects_soundness_def, encodes_soundness_def] >>
  `lca_model satisfies (sigof lca_thy,[],sound_stmt)`
    by fs[entails_def] >>
  `termsem (tmsof (sigof lca_thy)) lca_model lca_val sound_stmt = True`
    by (qpat_x_assum `_ satisfies _` mp_tac >>
        simp[satisfies_def] >> disch_then (qspec_then `lca_val` mp_tac) >>
        simp[]) >>
  metis_tac[]
QED

(* The two halves: the derivation half plus the LCA-derived encoding half
   give K' sound (via kernelUpgradeTheory.candle_lifts_soundness). *)
Theorem kernel_sound_from_lca:
  is_set_theory ^mem ∧
  candle_kernel lca_thy sound_stmt ∧
  lca_reflects_soundness ^mem K' sound_stmt lca_thy lca_model lca_val ⇒
  kernel_sound ^mem K'
Proof
  metis_tac[lca_encodes_soundness, candle_lifts_soundness]
QED

(* The derived reading `loeb_reflection` in the LCA theory, from the LCA
   ingredient alone: the ingredient yields the encoding half, and the base
   kernel's soundness (proves_sound) turns any Candle derivation of the
   term into K''s soundness (kernelUpgradeTheory.loeb_reflection_candle). *)
Theorem loeb_reflection_from_lca:
  is_set_theory ^mem ∧
  lca_reflects_soundness ^mem K' sound_stmt lca_thy lca_model lca_val ⇒
  encodes_soundness ^mem lca_thy sound_stmt K' ∧
  loeb_reflection ^mem candle_kernel K' lca_thy sound_stmt
Proof
  metis_tac[lca_encodes_soundness, loeb_reflection_candle]
QED

(* End-to-end: the LCA ingredient plus a Candle derivation in the LCA
   theory are a soundness WITNESS for K', and K' is sound. *)
Theorem kernel_self_upgrade_sound_from_lca:
  is_set_theory ^mem ∧
  lca_reflects_soundness ^mem K' sound_stmt lca_thy lca_model lca_val ∧
  candle_kernel lca_thy sound_stmt ⇒
  soundness_witness ^mem K' ∧ kernel_sound ^mem K'
Proof
  strip_tac >>
  ‘soundness_witness ^mem K'’
    by (rw[soundness_witness_def] >> metis_tac[lca_encodes_soundness]) >>
  metis_tac[witness_suffices]
QED

val _ = export_theory ();
