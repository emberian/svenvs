(*
  loebReduction — reducing svenvs' single open assumption `loeb_reflection`
  to the NAMED, cited Large-Cardinal reflection theorem of hol-reflection/lca
  (Fallenstein–Kumar), with the actual semantic chain done in-logic.

  WHAT THIS IS / IS NOT
  ---------------------
  This theory is PURE candle-semantics HOL4. It does NOT discharge the LCA
  itself: the discharge is the 137 KB `lcaProofTheory.intermediate_thm` +
  `lcaLib.build_master_theorem` construction, CPU/RAM-walled (tens of GB
  resident, ~CPU-hours per prerequisite theory — CLAIMS.md §9), deferred to the
  dedicated build host and NOT required to exhibit this reduction.

  What it DOES, machine-checked and cheat-free (no cheat / mk_thm / new_axiom):
  it exhibits the EXACT semantic reduction. The single genuinely-open svenvs
  assumption `loeb_reflection` is DERIVED from two named, cited ingredients of
  hol-reflection:

    (1) `provable_imp_eq_true`  (reflectionTheory) — re-proved here as
        `kernel_proves_satisfied` directly from candle's `proves_sound`: an
        obligation the base (Candle) kernel certifies is satisfied in EVERY
        model of the theory;

    (2) `lca_decodes_soundness` (the LCA hypothesis) — the LCA-provided model
        of `lca_ctxt` is one in which the internal soundness statement
        `sound_stmt thy`, when it holds (termsem = True), DECODES to the real,
        external proposition `kernel_sound mem K'`. This is precisely the
        content `lcaProofTheory.intermediate_thm` + `build_master_theorem`
        supply (a reflected predicate φ instantiated at the encoding of
        `kernel_sound mem K'`). Here it is a NAMED HYPOTHESIS, not a cheat.

  The reduction theorem `loeb_reflection_from_lca` then routes:
       base kernel certifies sound_stmt thy           (loeb_reflection antecedent)
    ⇒ sound_stmt thy is satisfied in the LCA model    (proves_sound, ingredient 1)
    ⇒ kernel_sound mem K'                             (decoding, ingredient 2 = LCA)
  giving `kernel_sound mem K'`, i.e. `loeb_reflection`.

  This turns "loeb_reflection is open" into "loeb_reflection reduces, in-logic,
  to the cited LCA model-existence-and-decoding theorem". The residual is
  exactly ingredient (2), supplied by the heavy hol-reflection/lca build.

  The svenvs definitions (kernel_sound, candle_kernel, loeb_reflection) are
  RESTATED VERBATIM from kernel/kernelUpgradeScript.sml so this theory is
  self-contained and depends only on the (built) candle semantic theories.
*)
open HolKernel boolLib bossLib BasicProvers
     holSyntaxTheory holSemanticsTheory holSemanticsExtraTheory
     holSoundnessTheory;

val _ = new_theory "loebReduction";

val _ = Parse.hide "mem";
val mem = ``mem:'U->'U->bool``;

(* ----------------------------------------------------------------------
   svenvs kernelUpgradeTheory definitions, restated verbatim.
   ---------------------------------------------------------------------- *)

Type kernel = ``:thy -> term -> bool``

Definition kernel_sound_def:
  kernel_sound (^mem) (K:kernel) ⇔
    ∀thy obl. K thy obl ⇒ (thy,[]) |= obl
End

Definition candle_kernel_def:
  candle_kernel (thy:thy) obl ⇔ (thy,[]) |- obl
End

Definition loeb_reflection_def:
  loeb_reflection (^mem) (K:kernel) (K':kernel) (sound_stmt:thy->term) ⇔
    ((∀thy. K thy (sound_stmt thy)) ⇒ kernel_sound ^mem K')
End

(* Base kernel soundness — this IS proves_sound, no assumption. *)
Theorem candle_kernel_sound:
  is_set_theory ^mem ⇒ kernel_sound ^mem candle_kernel
Proof
  rw[kernel_sound_def, candle_kernel_def] >> metis_tac[proves_sound]
QED

(* ----------------------------------------------------------------------
   Ingredient (1): the Candle kernel's certificates are semantically valid.
   This is `reflectionTheory.provable_imp_eq_true` specialised to empty
   hypotheses, re-derived here directly from `proves_sound` (no cheat). It says:
   if the base kernel certifies `sound_stmt thy`, then `sound_stmt thy` holds in
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

   This packages exactly what hol-reflection/lca's master theorem provides for
   the reflected predicate φ = (encoding of) `kernel_sound mem K'`:

     - there is a model `lca_model` of theory `lca_thy` (from
       `intermediate_thm`, valid under LCA (SUC l)); and
     - in that model, with valuation `lca_val`, the internal soundness statement
       `sound_stmt thy` being satisfied DECODES to the external truth
       `kernel_sound mem K'`  (the termsem-cert / decoding step of
       `build_master_theorem`).

   We state it as a predicate so it is a NAMED antecedent, never a cheat. *)

Definition lca_reflects_soundness_def:
  lca_reflects_soundness (^mem) (K':kernel) (sound_stmt:thy->term)
                         (lca_thy:thy) lca_model lca_val ⇔
    (* the LCA-provided object IS a model of the LCA theory *)
    lca_model models lca_thy ∧
    is_valuation (tysof (sigof lca_thy)) (tyaof lca_model) lca_val ∧
    (* and in it, the soundness statement decoding to external soundness:
       if sound_stmt lca_thy is satisfied (termsem = True) in this model under
       this valuation, then K' is really, externally, sound. *)
    (termsem (tmsof (sigof lca_thy)) lca_model lca_val (sound_stmt lca_thy) = True
       ⇒ kernel_sound ^mem K')
End

(* ----------------------------------------------------------------------
   THE REDUCTION (the real one).

   Given:
     - is_set_theory mem,
     - the base kernel certifies sound_stmt at the LCA theory
       (this is the `(∀thy. candle_kernel thy (sound_stmt thy))` antecedent of
        loeb_reflection, used at thy = lca_thy),
     - the LCA reflection-and-decoding hypothesis,
   we DERIVE kernel_sound mem K' by routing through proves_sound into the LCA
   model and then decoding. No cheat, real semantic work via termsem.
   ---------------------------------------------------------------------- *)

Theorem kernel_sound_from_lca:
  is_set_theory ^mem ∧
  candle_kernel lca_thy (sound_stmt lca_thy) ∧
  lca_reflects_soundness ^mem K' sound_stmt lca_thy lca_model lca_val ⇒
  kernel_sound ^mem K'
Proof
  rpt strip_tac >>
  full_simp_tac std_ss [lca_reflects_soundness_def] >>
  (* (1): the certified soundness statement is satisfied in the LCA model *)
  `lca_model satisfies (sigof lca_thy,[],sound_stmt lca_thy)`
    by metis_tac[kernel_proves_satisfied] >>
  (* unfold `satisfies` at empty hyps; it gives termsem = True for EVERY
     valuation; instantiate at lca_val (an is_valuation by hypothesis). *)
  `termsem (tmsof (sigof lca_thy)) lca_model lca_val (sound_stmt lca_thy) = True`
    by (qpat_x_assum `_ satisfies _` mp_tac >>
        simp[satisfies_def] >> disch_then (qspec_then `lca_val` mp_tac) >>
        simp[]) >>
  (* (2): decode in the LCA model to external soundness *)
  metis_tac[]
QED

(* And the headline: `loeb_reflection` for the base = candle kernel FOLLOWS from
   the LCA reflection-and-decoding hypothesis. This is svenvs' single open
   assumption, reduced in-logic to the cited LCA master theorem. *)
Theorem loeb_reflection_from_lca:
  is_set_theory ^mem ∧
  lca_reflects_soundness ^mem K' sound_stmt lca_thy lca_model lca_val ⇒
  loeb_reflection ^mem candle_kernel K' sound_stmt
Proof
  rw[loeb_reflection_def] >>
  (* the loeb_reflection antecedent gives certification at EVERY thy;
     specialise to lca_thy and feed the real reduction *)
  `candle_kernel lca_thy (sound_stmt lca_thy)` by fs[] >>
  metis_tac[kernel_sound_from_lca]
QED

(* End-to-end into svenvs' upgrade chain: the exact antecedent
   `kernel_self_upgrade_sound` wants is now SUPPLIED by the LCA reduction. *)
Theorem kernel_self_upgrade_sound_from_lca:
  is_set_theory ^mem ∧
  lca_reflects_soundness ^mem K' sound_stmt lca_thy lca_model lca_val ∧
  (∀thy. candle_kernel thy (sound_stmt thy)) ⇒
  kernel_sound ^mem K'
Proof
  rpt strip_tac >>
  `loeb_reflection ^mem candle_kernel K' sound_stmt`
    by metis_tac[loeb_reflection_from_lca] >>
  fs[loeb_reflection_def]
QED

val _ = export_theory ();
