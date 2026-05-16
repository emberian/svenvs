(*
  amendmentEval — a small CONCRETE constitutional-amendment episode, run
  inside the logic. Pure light HOL4 (intLib only). It is specNegEval's
  scenario lifted ONE level: now the META-INVARIANT itself is what gets
  negotiated, against an eternal bedrock.

  Scenario (integer pole, same plant family):

    BEDROCK         : `bedrock_box a ⇔ -9 ≤ a ≤ 9`.
                      The genuinely eternal floor — nothing negotiates it,
                      no `bedrock_box'` exists.

    genesis meta    : `meta0_box a ⇔ -3 ≤ a ≤ 3`. Refines bedrock.

    AMENDMENT A     : `meta_relax a ⇔ -7 ≤ a ≤ 7`.
                      A real meta-amendment that STILL refines bedrock
                      (±7 ⊆ ±9) and is a genuine change. Expected: ADMITTED.

    AMENDMENT B     : `meta_overreach a ⇔ -20 ≤ a ≤ 20`.
                      Amends the meta PAST bedrock. Expected: REJECTED;
                      the gate keeps the previous meta, bedrock intact.

  Every claim is closed by computation / `intLib.ARITH_TAC`, reusing
  specNegTheory's gate and amendmentTheory verbatim.
*)
open HolKernel boolLib bossLib BasicProvers intLib integerTheory
     specNegTheory amendmentTheory;

val _ = new_theory "amendmentEval";

Definition bedrock_box_def:
  bedrock_box (a:int) ⇔ -9 ≤ a ∧ a ≤ 9
End

Definition meta0_box_def:
  meta0_box (a:int) ⇔ -3 ≤ a ∧ a ≤ 3
End

Definition meta_relax_def:
  meta_relax (a:int) ⇔ -7 ≤ a ∧ a ≤ 7
End

Definition meta_overreach_def:
  meta_overreach (a:int) ⇔ -20 ≤ a ∧ a ≤ 20
End

(* Genesis meta sits above the eternal bedrock. *)
Theorem meta0_refines_bedrock:
  spec_refines meta0_box bedrock_box
Proof
  rw[spec_refines_def, meta0_box_def, bedrock_box_def] >> intLib.ARITH_TAC
QED

(* AMENDMENT A genuinely refines bedrock and is a real change. *)
Theorem relax_is_admissible:
  spec_admissible bedrock_box meta_relax
Proof
  rw[spec_admissible_def, genuine_spec_change_def]
  >- (rw[spec_refines_def, meta_relax_def, bedrock_box_def] >>
      intLib.ARITH_TAC)
  >- (rw[spec_refines_def, meta_relax_def, bedrock_box_def] >>
      intLib.ARITH_TAC) >>
  simp[FUN_EQ_THM] >> qexists_tac ‘9’ >>
  rw[meta_relax_def, bedrock_box_def]
QED

(* ... so the amendment gate INSTALLS it (real constitutional change). *)
Theorem relax_is_installed:
  spec_admit bedrock_box meta0_box meta_relax = meta_relax
Proof
  rw[spec_admit_def, relax_is_admissible]
QED

(* AMENDMENT B amends past bedrock: state 20 escapes the eternal floor. *)
Theorem overreach_does_not_refine:
  ¬ spec_refines meta_overreach bedrock_box
Proof
  rw[spec_refines_def, meta_overreach_def, bedrock_box_def] >>
  qexists_tac ‘20’ >> intLib.ARITH_TAC
QED

Theorem overreach_not_admissible:
  ¬ spec_admissible bedrock_box meta_overreach
Proof
  rw[spec_admissible_def] >> metis_tac[overreach_does_not_refine]
QED

(* The end-to-end adversarial AMENDMENT episode, computed:
   genesis meta0, propose [relax ; overreach].
   Result: relax admitted, overreach rejected → the meta in force is
   meta_relax, which provably still refines the eternal bedrock. *)
Theorem amendment_episode_final_meta:
  amended_meta bedrock_box meta0_box [meta_relax; meta_overreach]
    = meta_relax
Proof
  rw[amended_meta_def, spec_admit_all_def] >>
  ‘spec_admit bedrock_box meta0_box meta_relax = meta_relax’
    by rw[relax_is_installed] >>
  ‘spec_admit bedrock_box meta_relax meta_overreach = meta_relax’
    by metis_tac[unrefining_spec_proposal_is_inert, overreach_not_admissible] >>
  rw[]
QED

(* BEDROCK IS ETERNAL after the whole adversarial amendment episode:
   every state the finally-amended meta admits is still within bedrock.
   `bedrock_is_eternal` made concrete. *)
Theorem amendment_episode_bedrock_intact:
  ∀a. amended_meta bedrock_box meta0_box [meta_relax; meta_overreach] a ⇒
      bedrock_box a
Proof
  rpt strip_tac >>
  ‘spec_refines (amended_meta bedrock_box meta0_box
                   [meta_relax; meta_overreach]) bedrock_box’
    by metis_tac[bedrock_is_eternal, meta0_refines_bedrock] >>
  fs[spec_refines_def]
QED

(* Concrete sanity by computation: state 7 is admitted by the finally
   amended meta and is bedrock-safe; state 15 is bedrock-UNSAFE and the
   amended meta correctly never admits it (no amendment path reaches 15). *)
Theorem amendment_episode_pointwise_check:
  amended_meta bedrock_box meta0_box [meta_relax; meta_overreach] 7 ∧
  bedrock_box 7 ∧
  ¬ amended_meta bedrock_box meta0_box [meta_relax; meta_overreach] 15 ∧
  ¬ bedrock_box 15
Proof
  rw[amendment_episode_final_meta, meta_relax_def, bedrock_box_def] >>
  intLib.ARITH_TAC
QED

val _ = export_theory ();
