(*
  specNegEval — Concrete Spec Negotiation & Meta-Amendment Episodes
  (Computed in Logic via EVAL).
*)
open HolKernel boolLib bossLib BasicProvers intLib integerTheory
     cv_transLib cv_stdTheory certifierTheory specNegTheory;

val _ = new_theory "specNegEval";
val _ = numLib.prefer_num ();
val _ = intLib.prefer_int ();

(* ---- 1. Spec-level negotiation under fixed `meta_box` ---------------- *)
Definition meta_box_def:
  meta_box (a:int) <=> -5 <= a /\ a <= 5
End

Definition spec_tight_def:
  spec_tight (a:int) <=> -2 <= a /\ a <= 2
End

Definition spec_relaxed_def:
  spec_relaxed (a:int) <=> -4 <= a /\ a <= 4
End

Definition spec_overreach_def:
  spec_overreach (a:int) <=> -9 <= a /\ a <= 9
End

val () = cv_auto_trans meta_box_def;
val () = cv_auto_trans spec_tight_def;
val () = cv_auto_trans spec_relaxed_def;
val () = cv_auto_trans spec_overreach_def;

Theorem tight_refines_meta:
  spec_refines spec_tight meta_box
Proof
  rw[spec_refines_def, spec_tight_def, meta_box_def] >> intLib.ARITH_TAC
QED

Theorem relaxed_refines_meta:
  spec_refines spec_relaxed meta_box
Proof
  rw[spec_refines_def, spec_relaxed_def, meta_box_def] >> intLib.ARITH_TAC
QED

Theorem relaxed_is_genuine_change:
  genuine_spec_change spec_relaxed meta_box
Proof
  rw[genuine_spec_change_def, relaxed_refines_meta] >>
  simp[FUN_EQ_THM] >> qexists_tac `5` >>
  rw[spec_relaxed_def, meta_box_def]
QED

Theorem relaxed_is_admissible:
  spec_admissible meta_box spec_relaxed
Proof
  rw[spec_admissible_def, relaxed_is_genuine_change]
QED

Theorem relaxed_is_installed:
  spec_admit meta_box spec_tight spec_relaxed = spec_relaxed
Proof
  rw[spec_admit_def, cgate_def, relaxed_is_admissible]
QED

Theorem overreach_does_not_refine:
  ~ spec_refines spec_overreach meta_box
Proof
  rw[spec_refines_def, spec_overreach_def, meta_box_def] >>
  qexists_tac `9` >> intLib.ARITH_TAC
QED

Theorem overreach_not_admissible:
  ~ spec_admissible meta_box spec_overreach
Proof
  rw[spec_admissible_def, genuine_spec_change_def] >>
  metis_tac[overreach_does_not_refine]
QED

Theorem overreach_is_rejected:
  spec_admit meta_box spec_relaxed spec_overreach = spec_relaxed
Proof
  metis_tac[unrefining_spec_proposal_is_inert, overreach_not_admissible]
QED

Theorem episode_final_spec:
  spec_admit_all meta_box spec_tight [spec_relaxed; spec_overreach]
    = spec_relaxed
Proof
  rw[spec_admit_all_def] >>
  `spec_admit meta_box spec_tight spec_relaxed = spec_relaxed`
    by rw[relaxed_is_installed] >>
  `spec_admit meta_box spec_relaxed spec_overreach = spec_relaxed`
    by rw[overreach_is_rejected] >>
  rw[]
QED

Theorem episode_meta_floor_intact:
  !a. (spec_admit_all meta_box spec_tight
          [spec_relaxed; spec_overreach]) a ==> meta_box a
Proof
  rpt strip_tac >>
  `spec_refines spec_tight meta_box` by rw[tight_refines_meta] >>
  metis_tac[meta_floor_is_never_negotiated]
QED

Theorem episode_pointwise_check:
  (spec_admit_all meta_box spec_tight [spec_relaxed; spec_overreach]) 4 /\
  meta_box 4 /\
  ~ (spec_admit_all meta_box spec_tight [spec_relaxed; spec_overreach]) 7 /\
  ~ meta_box 7
Proof
  REWRITE_TAC[episode_final_spec] >> CONV_TAC cv_eval
QED

(* ---- 2. Constitutional meta-amendment episode over `bedrock_box` ------ *)
Definition bedrock_box_def:
  bedrock_box (a:int) <=> -9 <= a /\ a <= 9
End

Definition meta0_box_def:
  meta0_box (a:int) <=> -3 <= a /\ a <= 3
End

Definition meta_relax_def:
  meta_relax (a:int) <=> -7 <= a /\ a <= 7
End

Definition meta_overreach_def:
  meta_overreach (a:int) <=> -20 <= a /\ a <= 20
End

val () = cv_auto_trans bedrock_box_def;
val () = cv_auto_trans meta0_box_def;
val () = cv_auto_trans meta_relax_def;
val () = cv_auto_trans meta_overreach_def;

Theorem meta0_refines_bedrock:
  spec_refines meta0_box bedrock_box
Proof
  rw[spec_refines_def, meta0_box_def, bedrock_box_def] >> intLib.ARITH_TAC
QED

Theorem relax_is_admissible:
  spec_admissible bedrock_box meta_relax
Proof
  rw[spec_admissible_def, genuine_spec_change_def]
  >- (rw[spec_refines_def, meta_relax_def, bedrock_box_def] >>
      intLib.ARITH_TAC) >>
  simp[FUN_EQ_THM] >> qexists_tac `9` >>
  rw[meta_relax_def, bedrock_box_def]
QED

Theorem relax_is_installed:
  spec_admit bedrock_box meta0_box meta_relax = meta_relax
Proof
  rw[spec_admit_def, cgate_def, relax_is_admissible]
QED

Theorem meta_overreach_not_admissible:
  ~ spec_admissible bedrock_box meta_overreach
Proof
  rw[spec_admissible_def, genuine_spec_change_def, spec_refines_def,
     meta_overreach_def, bedrock_box_def] >>
  DISJ1_TAC >> qexists_tac `20` >> intLib.ARITH_TAC
QED

Theorem amendment_episode_final_meta:
  amended_meta bedrock_box meta0_box [meta_relax; meta_overreach]
    = meta_relax
Proof
  rw[amended_meta_def, spec_admit_all_def] >>
  `spec_admit bedrock_box meta0_box meta_relax = meta_relax`
    by rw[relax_is_installed] >>
  `spec_admit bedrock_box meta_relax meta_overreach = meta_relax`
    by metis_tac[unrefining_spec_proposal_is_inert, meta_overreach_not_admissible] >>
  rw[]
QED

Theorem amendment_episode_bedrock_intact:
  !a. amended_meta bedrock_box meta0_box [meta_relax; meta_overreach] a ==>
      bedrock_box a
Proof
  rpt strip_tac >>
  `spec_refines (amended_meta bedrock_box meta0_box
                   [meta_relax; meta_overreach]) bedrock_box`
    by metis_tac[bedrock_is_eternal, meta0_refines_bedrock] >>
  fs[spec_refines_def]
QED

Theorem amendment_episode_pointwise_check:
  amended_meta bedrock_box meta0_box [meta_relax; meta_overreach] 7 /\
  bedrock_box 7 /\
  ~ amended_meta bedrock_box meta0_box [meta_relax; meta_overreach] 15 /\
  ~ bedrock_box 15
Proof
  REWRITE_TAC[amendment_episode_final_meta] >> CONV_TAC cv_eval
QED

Theorem spec_episode_cv_eval:
  spec_relaxed 4 /\ meta_box 4 /\ ~spec_relaxed 7 /\ ~meta_box 7 /\
  meta_relax 7 /\ bedrock_box 7 /\ ~meta_relax 15 /\ ~bedrock_box 15
Proof
  CONV_TAC cv_eval
QED

val _ = export_theory ();
