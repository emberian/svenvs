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
     cv_transLib cv_stdTheory setSpecTheory setModelTheory
     holSyntaxTheory holSyntaxExtraTheory holSemanticsTheory holSemanticsExtraTheory
     holSoundnessTheory kernelUpgradeTheory watchdogFiniteTheory;

val _ = new_theory "loebReduction";
val _ = numLib.prefer_num ();

Theorem MEM_cv_inline[local,cv_inline]:
  !x xs. MEM x xs = list_mem x xs
Proof
  GEN_TAC >> Induct >> rw[list_mem_def] >> metis_tac[]
QED

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

(* ----------------------------------------------------------------------
   Ingredient (3): the `hol-reflection` boolean semantic decoding bridge
   (`bool_to_inner`, `finv`) and `cv_compute`-accelerated syntax checking.

   In `hol-reflection/reflectionScript.sml`, a reflected HOL proposition P
   is connected to its inner-syntax term `sound_stmt` via the semantic
   equation
     termsem (tmsof (sigof lca_thy)) lca_model lca_val sound_stmt =
       bool_to_inner mem P
   where `bool_to_inner mem b = Boolean b`. Under `is_set_theory mem`,
   `True <> False` (`mem_bool`), so `bool_to_inner mem` is injective and
   invertible via `finv (bool_to_inner mem)`, directly discharging
   `lca_reflects_soundness`.
   ---------------------------------------------------------------------- *)

Definition bool_to_inner_def:
  bool_to_inner ^mem (b:bool) = Boolean b
End

Definition finv_def:
  finv (f:'a -> 'b) (y:'b) = @x. f x = y
End

Theorem bool_to_inner_inj:
  is_set_theory ^mem ⇒
  ∀b1 b2. bool_to_inner ^mem b1 = bool_to_inner ^mem b2 ⇔ b1 = b2
Proof
  strip_tac >> Cases >> Cases >>
  rw[bool_to_inner_def, boolean_def] >>
  metis_tac[true_neq_false]
QED

Theorem finv_bool_to_inner:
  is_set_theory ^mem ⇒
  ∀b. finv (bool_to_inner ^mem) (bool_to_inner ^mem b) = b
Proof
  rw[finv_def] >>
  `∀x. bool_to_inner ^mem x = bool_to_inner ^mem b ⇔ x = b`
    by metis_tac[bool_to_inner_inj] >>
  rw[]
QED

Theorem lca_reflects_soundness_from_boolean_decoding:
  is_set_theory ^mem ∧
  lca_model models lca_thy ∧
  is_valuation (tysof (sigof lca_thy)) (tyaof lca_model) lca_val ∧
  termsem (tmsof (sigof lca_thy)) lca_model lca_val sound_stmt =
    bool_to_inner ^mem (kernel_sound ^mem K') ⇒
  lca_reflects_soundness ^mem K' sound_stmt lca_thy lca_model lca_val
Proof
  rw[lca_reflects_soundness_def] >>
  `bool_to_inner ^mem T = True` by rw[bool_to_inner_def, boolean_def] >>
  metis_tac[bool_to_inner_inj]
QED

Theorem kernel_self_upgrade_sound_from_boolean_decoding:
  is_set_theory ^mem ∧
  lca_model models lca_thy ∧
  is_valuation (tysof (sigof lca_thy)) (tyaof lca_model) lca_val ∧
  termsem (tmsof (sigof lca_thy)) lca_model lca_val sound_stmt =
    bool_to_inner ^mem (kernel_sound ^mem K') ∧
  candle_kernel lca_thy sound_stmt ⇒
  soundness_witness ^mem K' ∧ kernel_sound ^mem K'
Proof
  strip_tac >>
  `lca_reflects_soundness ^mem K' sound_stmt lca_thy lca_model lca_val`
    by metis_tac[lca_reflects_soundness_from_boolean_decoding] >>
  metis_tac[kernel_self_upgrade_sound_from_lca]
QED

(* ----------------------------------------------------------------------
   Full holSyntax cv_compute Checker Stack & Bridge Theorems
   ---------------------------------------------------------------------- *)

open pairTheory listTheory rich_listTheory pred_setTheory stringTheory alistTheory
     finite_mapTheory relationTheory holSyntaxLibTheory;

val () = cv_auto_trans init_ctxt_def;
val () = cv_auto_trans axexts_of_upd_def;
val () = cv_auto_trans REV_ASSOCD_def;
val () = cv_auto_trans ALPHAVARS_def;
val () = cv_auto_trans LIST_INSERT_def;
val () = cv_auto_trans LIST_UNION_def;
val () = cv_auto_trans stringTheory.string_lt_def;
val () = cv_auto_trans INORDER_INSERT_def;
val () = cv_auto_trans STRING_SORT_def;
val () = cv_auto_trans mlstringTheory.explode_thm;
val () = cv_auto_trans mlstring_sort_def;
Definition app_tyarg_def:
  app_tyarg a (Tyapp v args) = Tyapp v (a :: args) ∧
  app_tyarg _ ty = ty
End
val () = cv_auto_trans app_tyarg_def;

Definition type_subst_c_def:
  type_subst_c i (Tyvar v) = REV_ASSOCD (Tyvar v) i (Tyvar v) ∧
  type_subst_c i (Tyapp v []) = Tyapp v [] ∧
  type_subst_c i (Tyapp v (a::args)) =
    app_tyarg (type_subst_c i a) (type_subst_c i (Tyapp v args))
Termination
  WF_REL_TAC `measure (type_size o SND)` >>
  rw[type_size_def]
End
val () = cv_auto_trans type_subst_c_def;

Theorem TYPE_SUBST_eq_c[cv_inline]:
  ∀i ty. TYPE_SUBST i ty = type_subst_c i ty
Proof
  ho_match_mp_tac type_subst_c_ind >>
  rw[type_subst_c_def, TYPE_SUBST_def, app_tyarg_def] >>
  pop_assum (SUBST1_TAC o SYM) >>
  rw[TYPE_SUBST_def, app_tyarg_def]
QED

Theorem type1_size_append[local,simp]:
  ∀l1 l2. type1_size (l1 ++ l2) = type1_size l1 + type1_size l2
Proof
  Induct >> rw[type_size_def]
QED

val tymatch_pre_def = cv_auto_trans_pre "" tymatch_def;

Theorem tymatch_pre[cv_pre]:
  ∀ps obs sids. tymatch_pre ps obs sids
Proof
  ho_match_mp_tac holSyntaxExtraTheory.tymatch_ind >>
  rpt strip_tac >> TRY (Cases_on `sids`) >>
  simp[Once tymatch_pre_def] >>
  fs[MEM_cv_inline]
QED

val () = cv_auto_trans match_type_def;

Definition tyvars_c_def:
  tyvars_c (Tyvar v) = [v] ∧
  tyvars_c (Tyapp v []) = [] ∧
  tyvars_c (Tyapp v (a::args)) =
    LIST_UNION (tyvars_c a) (tyvars_c (Tyapp v args))
Termination
  WF_REL_TAC `measure type_size` >>
  rw[type_size_def]
End
val () = cv_auto_trans tyvars_c_def;

Theorem tyvars_eq_c[cv_inline]:
  ∀ty. tyvars ty = tyvars_c ty
Proof
  ho_match_mp_tac tyvars_c_ind >>
  rw[tyvars_c_def, tyvars_def] >>
  pop_assum (SUBST1_TAC o SYM) >>
  rw[tyvars_def]
QED

val () = cv_auto_trans tvars_def;
val () = cv_auto_trans types_of_upd_def;

Definition map_tyvar_def:
  map_tyvar [] = [] ∧
  map_tyvar (v :: vs) = Tyvar v :: map_tyvar vs
End
val () = cv_auto_trans map_tyvar_def;

Theorem map_tyvar_eq[cv_inline]:
  ∀vs. MAP Tyvar vs = map_tyvar vs
Proof
  Induct >> rw[map_tyvar_def]
QED

Definition map_typeof_snd_def:
  map_typeof_snd [] = [] ∧
  map_typeof_snd ((s, t) :: rest) = (s, typeof t) :: map_typeof_snd rest
End
val () = cv_auto_trans map_typeof_snd_def;

Theorem map_typeof_snd_eq:
  ∀eqs. MAP (λ(s,t). (s, typeof t)) eqs = map_typeof_snd eqs
Proof
  Induct >> TRY PairCases >> rw[map_typeof_snd_def]
QED

Theorem consts_of_upd_cv_eq:
  (∀name arity. consts_of_upd (NewType name arity) = []) ∧
  (∀name ty. consts_of_upd (NewConst name ty) = [(name, ty)]) ∧
  (∀prop. consts_of_upd (NewAxiom prop) = []) ∧
  (∀eqs prop.
     consts_of_upd (ConstSpec eqs prop) = map_typeof_snd eqs) ∧
  (∀name pred abs_name rep_name.
     consts_of_upd (TypeDefn name pred abs_name rep_name) =
     (let args = map_tyvar (mlstring_sort (tvars pred)) in
      let rty = domain (typeof pred) in
      let aty = Tyapp name args in
        [(abs_name, Fun rty aty); (rep_name, Fun aty rty)]))
Proof
  rw[consts_of_upd_def, mlstring_sort_def, map_typeof_snd_eq, map_tyvar_eq]
QED
val () = cv_auto_trans consts_of_upd_cv_eq;

Definition type_list_c_def:
  type_list_c [] = [] ∧
  type_list_c (u :: us) = types_of_upd u ++ type_list_c us
End
val () = cv_auto_trans type_list_c_def;

Theorem type_list_c_eq[cv_inline]:
  ∀ctxt. FLAT (MAP types_of_upd ctxt) = type_list_c ctxt
Proof
  Induct >> rw[type_list_c_def]
QED

Definition const_list_c_def:
  const_list_c [] = [] ∧
  const_list_c (u :: us) = consts_of_upd u ++ const_list_c us
End
val () = cv_auto_trans const_list_c_def;

Theorem const_list_c_eq[cv_inline]:
  ∀ctxt. FLAT (MAP consts_of_upd ctxt) = const_list_c ctxt
Proof
  Induct >> rw[const_list_c_def]
QED

Definition axexts_list_c_def:
  axexts_list_c [] = [] ∧
  axexts_list_c (u :: us) = axexts_of_upd u ++ axexts_list_c us
End
val () = cv_auto_trans axexts_list_c_def;

Theorem axexts_list_c_eq[cv_inline]:
  ∀ctxt. FLAT (MAP axexts_of_upd ctxt) = axexts_list_c ctxt
Proof
  Induct >> rw[axexts_list_c_def]
QED

Definition LIST_DIFF_def:
  LIST_DIFF l1 l2 = FILTER (λx. ¬MEM x l2) l1
End
val () = cv_auto_trans LIST_DIFF_def;

Definition init_ctxt_axexts_def:
  init_ctxt_axexts = axexts_list_c init_ctxt
End
val () = cv_auto_trans init_ctxt_axexts_def;

(* ----------------------------------------------------------------------
   Exact executable type-instance checking (`can_match_type` ⇔ `is_instance`)
   ---------------------------------------------------------------------- *)

Definition can_match_type_def:
  can_match_type ty0 ty =
    case match_type ty0 ty of
      NONE => F
    | SOME s => (TYPE_SUBST s ty0 = ty)
End
val () = cv_auto_trans can_match_type_def;

Definition check_instance_def:
  check_instance ty ty0 = can_match_type ty0 ty
End
val () = cv_auto_trans check_instance_def;

Theorem EVERY_arities_match_singleton[local]:
  ∀args i.
    EVERY (λty. arities_match [ty] [TYPE_SUBST i ty]) args ⇒
    arities_match args (MAP (TYPE_SUBST i) args)
Proof
  Induct >> rw[arities_match_def] >>
  Cases_on `h` >> fs[TYPE_SUBST_def, arities_match_def] >>
  qpat_x_assum `arities_match _ _` mp_tac >>
  REWRITE_TAC[ETA_AX] >> simp[]
QED

Theorem arities_match_TYPE_SUBST:
  ∀i ty. arities_match [ty] [TYPE_SUBST i ty]
Proof
  gen_tac >> ho_match_mp_tac type_ind >>
  simp[TYPE_SUBST_def, arities_match_def] >>
  REWRITE_TAC[ETA_AX] >>
  rpt strip_tac >>
  irule EVERY_arities_match_singleton >> simp[]
QED

Theorem tymatch_COMPLETE:
  ∀i ps obs sids.
    obs = MAP (TYPE_SUBST i) ps ∧
    (∀name.
       (REV_ASSOCD (Tyvar name) (FST sids) (Tyvar name) ≠ Tyvar name ∨
        MEM name (SND sids)) ⇒
       REV_ASSOCD (Tyvar name) (FST sids) (Tyvar name) =
       REV_ASSOCD (Tyvar name) i (Tyvar name)) ⇒
    IS_SOME (tymatch ps obs sids)
Proof
  gen_tac >> ho_match_mp_tac holSyntaxExtraTheory.tymatch_ind >>
  simp[tymatch_def, TYPE_SUBST_def] >>
  REWRITE_TAC[ETA_AX] >>
  rpt gen_tac >> PairCases_on `sids` >> simp[] >>
  strip_tac >> strip_tac >> fs[] >>
  Cases_on `REV_ASSOCD (Tyvar name) sids0 (Tyvar name) = Tyvar name` >> fs[] >>
  Cases_on `MEM name sids1` >> fs[] >>
  Cases_on `REV_ASSOCD (Tyvar name) i (Tyvar name) = Tyvar name` >> fs[] >>
  first_x_assum irule >>
  rw[REV_ASSOCD] >> fs[] >> metis_tac[]
QED

Theorem match_type_COMPLETE:
  ∀ty i. ∃s. match_type ty (TYPE_SUBST i ty) = SOME s ∧
              TYPE_SUBST s ty = TYPE_SUBST i ty
Proof
  rpt gen_tac >>
  qspecl_then [`i`, `[ty]`, `[TYPE_SUBST i ty]`, `([],[])`] mp_tac
    tymatch_COMPLETE >>
  impl_tac >- rw[REV_ASSOCD] >>
  rw[optionTheory.IS_SOME_EXISTS] >>
  `match_type ty (TYPE_SUBST i ty) = SOME (FST x)`
    by rw[match_type_def] >>
  qexists_tac `FST x` >> simp[] >>
  qspecl_then [`ty`, `TYPE_SUBST i ty`, `FST x`] mp_tac
    holSyntaxExtraTheory.match_type_SOME >>
  simp[arities_match_TYPE_SUBST]
QED

Theorem can_match_type_eq_is_instance:
  ∀ty0 ty. can_match_type ty0 ty ⇔ is_instance ty0 ty
Proof
  rw[can_match_type_def] >> eq_tac >> strip_tac
  >- (Cases_on `match_type ty0 ty` >> fs[] >> metis_tac[])
  >- (rw[] >>
      qspecl_then [`ty0`, `i`] strip_assume_tac match_type_COMPLETE >>
      simp[])
QED

Theorem check_instance_eq:
  ∀ty ty0. check_instance ty ty0 ⇔ is_instance ty0 ty
Proof
  rw[check_instance_def, can_match_type_eq_is_instance]
QED

(* ----------------------------------------------------------------------
   Executable alpha-equivalence (`raconv_check`, `aconv_check`)
   ---------------------------------------------------------------------- *)

Definition raconv_check_def:
  raconv_check env (Var s1 ty1) t2 =
    (case t2 of
       Var s2 ty2 => ALPHAVARS env (Var s1 ty1, Var s2 ty2)
     | _ => F) ∧
  raconv_check env (Const s1 ty1) t2 =
    (case t2 of
       Const s2 ty2 => (s1 = s2 ∧ ty1 = ty2)
     | _ => F) ∧
  raconv_check env (Comb s1 u1) t2 =
    (case t2 of
       Comb s2 u2 => (raconv_check env s1 s2 ∧ raconv_check env u1 u2)
     | _ => F) ∧
  raconv_check env (Abs v1 u1) t2 =
    (case t2 of
       Abs v2 u2 => (typeof v1 = typeof v2 ∧ raconv_check ((v1,v2)::env) u1 u2)
     | _ => F)
End
val () = cv_auto_trans raconv_check_def;

Theorem raconv_check_eq:
  ∀env t1 t2. raconv_check env t1 t2 ⇔ RACONV env (t1, t2)
Proof
  Induct_on `t1` >>
  rpt gen_tac >> TRY strip_tac >>
  Cases_on `t2` >> rw[raconv_check_def, holSyntaxExtraTheory.RACONV]
QED

Definition aconv_check_def:
  aconv_check t1 t2 = raconv_check [] t1 t2
End
val () = cv_auto_trans aconv_check_def;

Theorem aconv_check_eq[cv_inline]:
  ∀t1 t2. ACONV t1 t2 = aconv_check t1 t2
Proof
  rw[aconv_check_def, ACONV_def, raconv_check_eq]
QED

(* ----------------------------------------------------------------------
   Executable well-typedness (`welltyped_check` and direct `welltyped`)
   ---------------------------------------------------------------------- *)

Definition is_fun_type_from_def:
  is_fun_type_from (Tyapp name [d; r]) d0 = (name = «fun» ∧ d = d0) ∧
  is_fun_type_from _ _ = F
End
val () = cv_auto_trans is_fun_type_from_def;

Theorem is_fun_type_from_eq:
  ∀ty d0. is_fun_type_from ty d0 ⇔ ∃r. ty = Fun d0 r
Proof
  Cases >> rw[is_fun_type_from_def] >>
  Cases_on `l` >> rw[is_fun_type_from_def] >>
  Cases_on `t` >> rw[is_fun_type_from_def] >>
  Cases_on `t'` >> rw[is_fun_type_from_def] >>
  metis_tac[]
QED

Definition is_var_tm_def:
  is_var_tm (Var _ _) = T ∧
  is_var_tm _ = F
End
val () = cv_auto_trans is_var_tm_def;

Theorem is_var_tm_eq:
  ∀tm. is_var_tm tm ⇔ ∃n ty. tm = Var n ty
Proof
  Cases >> rw[is_var_tm_def]
QED

Definition welltyped_check_def:
  welltyped_check (Var _ _) = T ∧
  welltyped_check (Const _ _) = T ∧
  welltyped_check (Comb s t) =
    (welltyped_check s ∧ welltyped_check t ∧
     is_fun_type_from (typeof s) (typeof t)) ∧
  welltyped_check (Abs v t) =
    (is_var_tm v ∧ welltyped_check t)
End
val () = cv_auto_trans welltyped_check_def;

Theorem welltyped_check_eq:
  ∀tm. welltyped_check tm ⇔ welltyped tm
Proof
  Induct >>
  rw[welltyped_check_def, is_fun_type_from_eq, is_var_tm_eq] >>
  metis_tac[WELLTYPED_LEMMA, welltyped_def]
QED

Theorem welltyped_cv_inline[cv_inline]:
  ∀tm. welltyped tm = welltyped_check tm
Proof
  rw[welltyped_check_eq]
QED

(* ----------------------------------------------------------------------
   Executable signature/context lookup and `type_ok` / `term_ok` / `is_std_sig`
   with `[cv_inline]` bridge theorems so `CONV_TAC cv_eval` discharges
   `FLOOKUP`, `type_ok`, `term_ok`, `is_std_sig` directly on `init_ctxt`
   and context extensions.
   ---------------------------------------------------------------------- *)

Definition consts_of_upd_c_def:
  consts_of_upd_c u = consts_of_upd u
End
val () = cv_auto_trans consts_of_upd_c_def;

Theorem consts_of_upd_c_eq:
  consts_of_upd_c = consts_of_upd
Proof
  rw[FUN_EQ_THM, consts_of_upd_c_def]
QED

Theorem FLOOKUP_alist_to_fmap_cv_inline[cv_inline]:
  ∀al k. FLOOKUP (alist_to_fmap al) k = ALOOKUP al k
Proof
  rw[]
QED

Theorem IN_FDOM_alist_to_fmap_cv_inline[cv_inline]:
  ∀k al. (k ∈ FDOM (alist_to_fmap al)) = MEM k (MAP FST al)
Proof
  rw[FDOM_alist_to_fmap]
QED

Theorem ALOOKUP_FLAT_types_of_upd:
  ∀ctxt name.
    ALOOKUP (FLAT (MAP types_of_upd ctxt)) name =
    FLOOKUP (tysof ctxt) name
Proof
  rw[]
QED

Theorem ALOOKUP_FLAT_consts_of_upd_c:
  ∀ctxt name.
    ALOOKUP (FLAT (MAP consts_of_upd_c ctxt)) name =
    FLOOKUP (tmsof ctxt) name
Proof
  rw[consts_of_upd_c_eq]
QED

Definition type_ok_list_c_def:
  type_ok_list_c tysig [] = T ∧
  type_ok_list_c tysig (Tyvar _ :: rest) = type_ok_list_c tysig rest ∧
  type_ok_list_c tysig (Tyapp name args :: rest) =
    (case ALOOKUP tysig name of
       NONE => F
     | SOME a => (a = LENGTH args ∧ type_ok_list_c tysig (args ++ rest)))
Termination
  WF_REL_TAC `measure (type1_size o SND)` >>
  rw[type_size_def]
End
val type_ok_list_c_pre_def = cv_auto_trans_pre "" type_ok_list_c_def;

Theorem type_ok_list_c_pre[cv_pre]:
  ∀tysig l. type_ok_list_c_pre tysig l
Proof
  ho_match_mp_tac type_ok_list_c_ind >>
  rpt strip_tac >>
  simp[Once type_ok_list_c_pre_def] >>
  CASE_TAC >> fs[]
QED

Theorem type_ok_list_c_EVERY:
  ∀tys l.
    type_ok_list_c tys l ⇔ EVERY (type_ok (alist_to_fmap tys)) l
Proof
  ho_match_mp_tac type_ok_list_c_ind >>
  rw[type_ok_list_c_def, type_ok_def] >>
  REWRITE_TAC[ETA_AX] >>
  CASE_TAC >> rw[] >> eq_tac >> rw[]
QED

Definition type_ok_alist_def:
  type_ok_alist tysig ty = type_ok_list_c tysig [ty]
End
val () = cv_auto_trans type_ok_alist_def;

Theorem type_ok_alist_thm[cv_inline]:
  ∀tys ty. type_ok (alist_to_fmap tys) ty = type_ok_alist tys ty
Proof
  rw[type_ok_alist_def, type_ok_list_c_EVERY]
QED

Theorem type_ok_alist_eq:
  ∀ctxt ty.
    type_ok_alist (FLAT (MAP types_of_upd ctxt)) ty ⇔
    type_ok (tysof ctxt) ty
Proof
  rw[type_ok_alist_thm]
QED

Definition term_ok_alist_def:
  term_ok_alist tysig tmsig (Var _ ty) = type_ok_alist tysig ty ∧
  term_ok_alist tysig tmsig (Const name ty) =
    (case ALOOKUP tmsig name of
       NONE => F
     | SOME ty0 => (type_ok_alist tysig ty ∧ can_match_type ty0 ty)) ∧
  term_ok_alist tysig tmsig (Comb t1 t2) =
    (term_ok_alist tysig tmsig t1 ∧
     term_ok_alist tysig tmsig t2 ∧
     welltyped_check (Comb t1 t2)) ∧
  term_ok_alist tysig tmsig (Abs v t) =
    (case v of
       Var _ ty => (type_ok_alist tysig ty ∧ term_ok_alist tysig tmsig t)
     | _ => F)
End
val () = cv_auto_trans term_ok_alist_def;

Theorem term_ok_alist_thm[cv_inline]:
  ∀tys tms tm.
    term_ok (alist_to_fmap tys, alist_to_fmap tms) tm =
    term_ok_alist tys tms tm
Proof
  rpt gen_tac >> Induct_on `tm` >>
  simp[Excl "can_match_type_def", term_ok_alist_def, term_ok_def,
       type_ok_alist_thm, can_match_type_eq_is_instance,
       welltyped_check_eq, is_fun_type_from_eq] >>
  rpt gen_tac >> TRY strip_tac >>
  TRY CASE_TAC >>
  rw[Excl "can_match_type_def", type_ok_alist_thm,
     can_match_type_eq_is_instance] >>
  metis_tac[]
QED

Theorem term_ok_alist_eq:
  ∀ctxt tm.
    term_ok_alist (FLAT (MAP types_of_upd ctxt))
                  (FLAT (MAP consts_of_upd_c ctxt)) tm ⇔
    term_ok (sigof ctxt) tm
Proof
  rw[consts_of_upd_c_eq, term_ok_alist_thm]
QED

Definition ctxt_sig_alist_def:
  ctxt_sig_alist ctxt =
    (type_list ctxt, const_list ctxt)
End
val () = cv_auto_trans ctxt_sig_alist_def;

Definition term_ok_ctxt_check_def:
  term_ok_ctxt_check ctxt tm =
    term_ok_alist (type_list ctxt) (const_list ctxt) tm
End
val () = cv_auto_trans term_ok_ctxt_check_def;

Theorem term_ok_ctxt_check_eq:
  ∀ctxt tm. term_ok_ctxt_check ctxt tm ⇔ term_ok (sigof ctxt) tm
Proof
  rw[term_ok_ctxt_check_def, term_ok_alist_thm]
QED

Definition is_std_sig_alist_pair_def:
  is_std_sig_alist_pair tysig tmsig ⇔
    ALOOKUP tysig «fun» = SOME 2 ∧
    ALOOKUP tysig «bool» = SOME 0 ∧
    ALOOKUP tmsig «=» = SOME (Fun (Tyvar «A») (Fun (Tyvar «A») Bool))
End
val () = cv_auto_trans is_std_sig_alist_pair_def;

Theorem is_std_sig_alist_thm[cv_inline]:
  ∀tys tms.
    is_std_sig (alist_to_fmap tys, alist_to_fmap tms) =
    is_std_sig_alist_pair tys tms
Proof
  rw[is_std_sig_def, is_std_sig_alist_pair_def]
QED

Definition is_std_sig_alist_def:
  is_std_sig_alist ctxt =
    is_std_sig_alist_pair (type_list ctxt) (const_list ctxt)
End
val () = cv_auto_trans is_std_sig_alist_def;

Theorem is_std_sig_alist_eq:
  ∀ctxt. is_std_sig_alist ctxt ⇔ is_std_sig (sigof ctxt)
Proof
  rw[is_std_sig_alist_def, is_std_sig_alist_thm]
QED

(* ----------------------------------------------------------------------
   Executable `CLOSED` and subset checks
   ---------------------------------------------------------------------- *)

Definition filter_neq_def:
  filter_neq (v : 'a) [] = [] ∧
  filter_neq v (x :: xs) =
    if x = v then filter_neq v xs else x :: filter_neq v xs
End
val () = cv_auto_trans filter_neq_def;

Theorem MEM_filter_neq:
  ∀l (v : 'a) x. MEM x (filter_neq v l) ⇔ MEM x l ∧ x ≠ v
Proof
  Induct >> rw[filter_neq_def] >> metis_tac[]
QED

Definition free_vars_tm_def:
  free_vars_tm (Var s ty) = [Var s ty] ∧
  free_vars_tm (Const _ _) = [] ∧
  free_vars_tm (Comb s t) = free_vars_tm s ++ free_vars_tm t ∧
  free_vars_tm (Abs v t) = filter_neq v (free_vars_tm t)
End
val () = cv_auto_trans free_vars_tm_def;

Theorem MEM_Var_free_vars_tm:
  ∀tm name vty.
    MEM (Var name vty) (free_vars_tm tm) ⇔ VFREE_IN (Var name vty) tm
Proof
  Induct >> rw[free_vars_tm_def, VFREE_IN_def, MEM_filter_neq] >>
  metis_tac[]
QED

Theorem EVERY_filter_neq:
  ∀l (v : 'a) P. EVERY P l ⇒ EVERY P (filter_neq v l)
Proof
  Induct >> rw[filter_neq_def]
QED

Theorem EVERY_is_var_tm_free_vars_tm:
  ∀tm. EVERY is_var_tm (free_vars_tm tm)
Proof
  Induct >> rw[free_vars_tm_def, is_var_tm_def, EVERY_filter_neq]
QED

Definition closed_check_def:
  closed_check tm = NULL (free_vars_tm tm)
End
val () = cv_auto_trans closed_check_def;

Theorem closed_check_eq[cv_inline]:
  ∀tm. CLOSED tm = closed_check tm
Proof
  gen_tac >>
  qspec_then `tm` mp_tac EVERY_is_var_tm_free_vars_tm >>
  Cases_on `free_vars_tm tm` >>
  rw[closed_check_def, CLOSED_def, is_var_tm_eq] >>
  metis_tac[MEM_Var_free_vars_tm, MEM]
QED

Definition list_subset_def:
  list_subset ([] : 'a list) (l2 : 'a list) = T ∧
  list_subset (x :: xs) l2 = (MEM x l2 ∧ list_subset xs l2)
End
val () = cv_auto_trans list_subset_def;

Theorem list_subset_EVERY:
  ∀(l1 : 'a list) l2. list_subset l1 l2 ⇔ EVERY (λx. MEM x l2) l1
Proof
  Induct >> rw[list_subset_def]
QED

Theorem SUBSET_LIST_TO_SET_cv_inline[cv_inline]:
  ∀(l1 : 'a list) l2. (set l1 ⊆ set l2) = list_subset l1 l2
Proof
  Induct >> rw[list_subset_def]
QED

(* ----------------------------------------------------------------------
   Executable `VSUBST` (`vsubst_c`), `conexts_of_upd`, `axioms_of_upd`,
   and `constrainable_update` (`holConstrainedExtensionTheory`)
   ---------------------------------------------------------------------- *)

Definition filter_neq_snd_def:
  filter_neq_snd (v : 'b) ([] : ('a # 'b) list) = [] ∧
  filter_neq_snd v ((a, b) :: xs) =
    if b = v then filter_neq_snd v xs else (a, b) :: filter_neq_snd v xs
End
val () = cv_auto_trans filter_neq_snd_def;

Theorem filter_neq_snd_eq_FILTER:
  ∀(l : ('a # 'b) list) v.
    filter_neq_snd v l = FILTER (λ(s', s). s ≠ v) l
Proof
  Induct >> TRY PairCases >> rw[filter_neq_snd_def]
QED

Definition vsubst_const_def:
  vsubst_const ilist (Var x ty) = REV_ASSOCD (Var x ty) ilist (Var x ty) ∧
  vsubst_const ilist (Const x ty) = Const x ty ∧
  vsubst_const ilist (Comb s t) = Comb (vsubst_const ilist s) (vsubst_const ilist t) ∧
  vsubst_const ilist (Abs v t) =
    Abs v (vsubst_const (filter_neq_snd v ilist) t)
End
val () = cv_auto_trans vsubst_const_def;

Definition abs_vars_ok_def:
  abs_vars_ok (Var _ _) = T ∧
  abs_vars_ok (Const _ _) = T ∧
  abs_vars_ok (Comb s t) = (abs_vars_ok s ∧ abs_vars_ok t) ∧
  abs_vars_ok (Abs v t) = (is_var_tm v ∧ abs_vars_ok t)
End
val () = cv_auto_trans abs_vars_ok_def;

Theorem welltyped_imp_abs_vars_ok:
  ∀tm. welltyped tm ⇒ abs_vars_ok tm
Proof
  Induct >> rw[abs_vars_ok_def, is_var_tm_eq] >>
  metis_tac[WELLTYPED_LEMMA]
QED

Definition is_const_tm_def:
  is_const_tm (Const _ _) = T ∧
  is_const_tm _ = F
End
val () = cv_auto_trans is_const_tm_def;

Theorem NOT_EXISTS_VFREE_IN_is_const_tm:
  ∀ilist v t.
    is_var_tm v ∧ EVERY (λ(s',s). is_const_tm s') ilist ⇒
    ¬EXISTS (λ(s',s). VFREE_IN v s' ∧ VFREE_IN s t) ilist
Proof
  Induct >> TRY PairCases >>
  rw[is_const_tm_def] >>
  Cases_on `v` >> Cases_on `h0` >>
  fs[is_var_tm_def, is_const_tm_def, VFREE_IN_def]
QED

Theorem vsubst_const_eq_VSUBST:
  ∀tm ilist.
    abs_vars_ok tm ∧ EVERY (λ(s',s). is_const_tm s') ilist ⇒
    vsubst_const ilist tm = VSUBST ilist tm
Proof
  Induct >>
  simp[vsubst_const_def, filter_neq_snd_eq_FILTER, VSUBST_def, LET_THM,
       abs_vars_ok_def] >>
  rpt strip_tac >>
  `EVERY (λ(s',s). is_const_tm s') (FILTER (λ(s',s). s ≠ tm) ilist)`
    by fs[EVERY_MEM, MEM_FILTER] >>
  `¬EXISTS (λ(s',s). VFREE_IN tm s' ∧ VFREE_IN s tm')
           (FILTER (λ(s',s). s ≠ tm) ilist)`
    by metis_tac[NOT_EXISTS_VFREE_IN_is_const_tm] >>
  fs[Excl "NOT_EXISTS"]
QED

Definition mk_constspec_ilist_def:
  mk_constspec_ilist [] = [] ∧
  mk_constspec_ilist ((x, t) :: rest) =
    (Const x (typeof t), Var x (typeof t)) :: mk_constspec_ilist rest
End
val () = cv_auto_trans mk_constspec_ilist_def;

Theorem mk_constspec_ilist_eq_MAP:
  ∀eqs. mk_constspec_ilist eqs =
        MAP (λ(x,t). let ty = typeof t in (Const x ty, Var x ty)) eqs
Proof
  Induct >> TRY PairCases >> rw[mk_constspec_ilist_def, LET_THM]
QED

Definition conexts_of_upd_c_def:
  conexts_of_upd_c (ConstSpec eqs prop) =
    [vsubst_const (mk_constspec_ilist eqs) prop] ∧
  conexts_of_upd_c (TypeDefn name pred abs_name rep_name) =
    (let args = MAP Tyvar (mlstring_sort (tvars pred)) in
     let rty = domain (typeof pred) in
     let aty = Tyapp name args in
     let rep = Const rep_name (Fun aty rty) in
     let abs = Const abs_name (Fun rty aty) in
     let a = Var «a» aty in
     let r = Var «r» rty in
       [Comb abs (Comb rep a) === a;
        Comb pred r === (Comb rep (Comb abs r) === r)]) ∧
  conexts_of_upd_c _ = []
End
val () = cv_auto_trans conexts_of_upd_c_def;

Definition axioms_of_upd_c_def:
  axioms_of_upd_c u = axexts_of_upd u ++ conexts_of_upd_c u
End
val () = cv_auto_trans axioms_of_upd_c_def;

(* Mirror of `holConstrainedExtensionTheory.constrainable_update_def` *)
Definition constrainable_update_def:
  constrainable_update upd ⇔
    ∃vars.
      FINITE vars ∧
      EVERY ($= vars) (MAP (set o tvars) (axioms_of_upd upd)) ∧
      EVERY ($= vars) (MAP (set o tyvars o SND) (consts_of_upd upd)) ∧
      EVERY (λp. ∀name ty ty'.
                    VFREE_IN (Const name ty) p ∧
                    MEM (name,ty') (consts_of_upd upd)
                    ⇒ ty' = ty)
            (axioms_of_upd upd) ∧
      let all_types =
        BIGUNION (set (MAP types_in (axioms_of_upd upd))) ∪
        set (MAP SND (consts_of_upd upd)) in
      ∀name arity.
        MEM (name,arity) (types_of_upd upd) ⇒
        arity = CARD vars ∧
        ∀args ty.
          Tyapp name args subtype ty ∧ ty ∈ all_types ⇒
          args = MAP Tyvar (mlstring_sort (SET_TO_LIST vars))
End

Definition free_consts_list_def:
  free_consts_list (Var _ _) = [] ∧
  free_consts_list (Const x ty) = [(x, ty)] ∧
  free_consts_list (Comb t1 t2) =
    free_consts_list t1 ++ free_consts_list t2 ∧
  free_consts_list (Abs _ t) = free_consts_list t
End
val () = cv_auto_trans free_consts_list_def;

Definition types_in_list_def:
  types_in_list (Var _ ty) = [ty] ∧
  types_in_list (Const _ ty) = [ty] ∧
  types_in_list (Comb t1 t2) = types_in_list t1 ++ types_in_list t2 ∧
  types_in_list (Abs v t) = types_in_list v ++ types_in_list t
End
val () = cv_auto_trans types_in_list_def;

Definition subtype_name_args_list_ok_def:
  subtype_name_args_list_ok name expected_args [] = T ∧
  subtype_name_args_list_ok name expected_args (Tyvar _ :: rest) =
    subtype_name_args_list_ok name expected_args rest ∧
  subtype_name_args_list_ok name expected_args (Tyapp n args :: rest) =
    ((n = name ⇒ args = expected_args) ∧
     subtype_name_args_list_ok name expected_args (args ++ rest))
Termination
  WF_REL_TAC `measure (type1_size o SND o SND)` >>
  rw[type_size_def]
End
val subtype_name_args_list_ok_pre_def =
  cv_auto_trans_pre "" subtype_name_args_list_ok_def;

Theorem subtype_name_args_list_ok_pre[cv_pre]:
  ∀name expected_args l. subtype_name_args_list_ok_pre name expected_args l
Proof
  ho_match_mp_tac subtype_name_args_list_ok_ind >>
  rpt strip_tac >>
  simp[Once subtype_name_args_list_ok_pre_def] >>
  fs[]
QED

Definition subtype_name_args_ok_def:
  subtype_name_args_ok name expected_args ty =
    subtype_name_args_list_ok name expected_args [ty]
End
val () = cv_auto_trans subtype_name_args_ok_def;

Definition list_set_eq_def:
  list_set_eq (l1 : 'a list) (l2 : 'a list) ⇔
    list_subset l1 l2 ∧ list_subset l2 l1
End
val () = cv_auto_trans list_set_eq_def;

Theorem list_set_eq_iff:
  ∀(l1 : 'a list) l2. list_set_eq l1 l2 ⇔ set l1 = set l2
Proof
  rw[list_set_eq_def, list_subset_EVERY, EXTENSION, EVERY_MEM] >> metis_tac[]
QED

Definition eqs_abs_vars_ok_def:
  eqs_abs_vars_ok ([] : (mlstring # term) list) = T ∧
  eqs_abs_vars_ok ((_, t) :: rest) = (abs_vars_ok t ∧ eqs_abs_vars_ok rest)
End
val () = cv_auto_trans eqs_abs_vars_ok_def;

Theorem eqs_abs_vars_ok_EVERY:
  ∀eqs. eqs_abs_vars_ok eqs ⇔ EVERY (abs_vars_ok o SND) eqs
Proof
  Induct >> TRY PairCases >> rw[eqs_abs_vars_ok_def]
QED

Definition upd_abs_vars_ok_def:
  upd_abs_vars_ok (ConstSpec eqs prop) =
    (abs_vars_ok prop ∧ eqs_abs_vars_ok eqs) ∧
  upd_abs_vars_ok (TypeDefn _ pred _ _) = abs_vars_ok pred ∧
  upd_abs_vars_ok _ = T
End
val () = cv_auto_trans upd_abs_vars_ok_def;

Theorem axioms_of_upd_c_eq:
  ∀upd. upd_abs_vars_ok upd ⇒ axioms_of_upd_c upd = axioms_of_upd upd
Proof
  Cases >>
  simp[upd_abs_vars_ok_def, eqs_abs_vars_ok_EVERY, axioms_of_upd_c_def,
       conexts_of_upd_c_def, conexts_of_upd_def, LET_THM,
       mk_constspec_ilist_eq_MAP, mlstring_sort_def] >>
  strip_tac >>
  irule vsubst_const_eq_VSUBST >>
  rw[EVERY_MAP, EVERY_MEM, FORALL_PROD, is_const_tm_def]
QED

Definition eqs_tvars_ok_def:
  eqs_tvars_ok pvars ([] : (mlstring # term) list) = T ∧
  eqs_tvars_ok pvars ((_, t) :: rest) =
    (list_set_eq (tyvars (typeof t)) pvars ∧ eqs_tvars_ok pvars rest)
End
val () = cv_auto_trans eqs_tvars_ok_def;

Theorem eqs_tvars_ok_EVERY:
  ∀eqs pvars.
    eqs_tvars_ok pvars eqs ⇔
    EVERY (λ(x,t). set (tyvars (typeof t)) = set pvars) eqs
Proof
  Induct >> TRY PairCases >>
  rw[Excl "list_set_eq_def", eqs_tvars_ok_def, list_set_eq_iff]
QED

Definition subtype_name_args_list_all_def:
  subtype_name_args_list_all name args [] = T ∧
  subtype_name_args_list_all name args (tm :: rest) =
    (subtype_name_args_list_ok name args (types_in_list tm) ∧
     subtype_name_args_list_all name args rest)
End
val () = cv_auto_trans subtype_name_args_list_all_def;

Definition constrainable_update_check_def:
  constrainable_update_check (NewType _ _) = T ∧
  constrainable_update_check (NewConst _ _) = T ∧
  constrainable_update_check (NewAxiom _) = T ∧
  constrainable_update_check (ConstSpec eqs prop) =
    (upd_abs_vars_ok (ConstSpec eqs prop) ∧
     ALL_DISTINCT (MAP FST eqs) ∧
     eqs_tvars_ok (tvars prop) eqs) ∧
  constrainable_update_check (TypeDefn name pred abs rep) =
    (upd_abs_vars_ok (TypeDefn name pred abs rep) ∧
     let args = MAP Tyvar (mlstring_sort (tvars pred)) in
     let axs = axioms_of_upd_c (TypeDefn name pred abs rep) in
       subtype_name_args_list_all name args axs)
End
val () = cv_auto_trans constrainable_update_check_def;

Definition all_constrainable_updates_def:
  all_constrainable_updates [] = T ∧
  all_constrainable_updates (u :: us) =
    (constrainable_update_check u ∧ all_constrainable_updates us)
End
val () = cv_auto_trans all_constrainable_updates_def;

Theorem all_constrainable_updates_EVERY[cv_inline]:
  ∀us. EVERY constrainable_update_check us = all_constrainable_updates us
Proof
  Induct >> rw[all_constrainable_updates_def]
QED

Theorem tvars_VSUBST_same_type:
  ∀tm ilist.
    welltyped tm ∧
    EVERY (λ(x,y). ∃n n' ty. (x = Const n ty ∨ x = Var n' ty) ∧ (y = Var n ty)) ilist ⇒
    tvars (VSUBST ilist tm) = tvars tm
Proof
  ho_match_mp_tac term_induction >>
  conj_tac >- (
    rw[tvars_def,VSUBST_def] >>
    rw[REV_ASSOCD_ALOOKUP] >>
    BasicProvers.CASE_TAC >> rw[tvars_def] >>
    imp_res_tac ALOOKUP_MEM >>
    fs[EVERY_MEM,MEM_MAP,EXISTS_PROD] >>
    res_tac >> fs[] >> simp[tvars_def] ) >>
  conj_tac >- rw[VSUBST_def,tvars_def] >>
  conj_tac >- rw[VSUBST_def,tvars_def] >>
  rw[] >> fs[] >>
  rw[tvars_def] >>
  srw_tac[][VSUBST_def] >>
  rw[tvars_def,Abbr`z`] >- (
    fs[tvars_def] >>
    AP_TERM_TAC >>
    first_x_assum match_mp_tac >>
    simp[Abbr`ilist''`,Abbr`ilist'`,EVERY_FILTER] >>
    fs[EVERY_MEM] ) >>
  simp[Abbr`t'`] >>
  AP_TERM_TAC >>
  first_x_assum match_mp_tac >>
  simp[Abbr`ilist'`,EVERY_FILTER] >>
  fs[EVERY_MEM]
QED

Theorem VFREE_IN_Const_VSUBST:
  ∀tm name ty ilist.
    welltyped tm ⇒
    VFREE_IN (Const name ty) (VSUBST ilist tm) ⇒
    VFREE_IN (Const name ty) tm ∨
    ∃x xy. VFREE_IN (Var x xy) tm ∧ VFREE_IN (Const name ty) (VSUBST ilist (Var x xy))
Proof
  ho_match_mp_tac term_induction >>
  simp[] >>
  conj_tac >- simp[VSUBST_def] >>
  conj_tac >- (
    rw[VSUBST_def] >>
    metis_tac[] ) >>
  rw[VSUBST_def] >>
  fs[LET_THM] >>
  pop_assum mp_tac >>
  rw[EXISTS_MEM,MEM_FILTER,UNCURRY] >>
  fs[VSUBST_def] >>
  res_tac >> rw[] >>
  fs[REV_ASSOCD,REV_ASSOCD_FILTER] >>
  pop_assum mp_tac >> rw[] >> fs[] >>
  metis_tac[]
QED

Theorem ConstSpec_constrainable:
  ∀eqs prop ctxt.
    ConstSpec eqs prop updates ctxt ∧
    EVERY (λ(x,t). set (tyvars (typeof t)) = set (tvars prop)) eqs ⇒
    constrainable_update (ConstSpec eqs prop)
Proof
  rpt strip_tac >>
  simp[constrainable_update_def,conexts_of_upd_def] >>
  `welltyped prop` by (
    fs[updates_cases] >>
    imp_res_tac proves_term_ok >>
    fs[welltyped_def] >> metis_tac[]) >>
  conj_tac >- (
    rw[LET_THM,EVERY_MAP,UNCURRY,EVERY_MEM,
       FORALL_PROD,EXISTS_PROD,MEM_MAP] >>
    fs[EVERY_MEM,FORALL_PROD] >>
    res_tac >>
    pop_assum(SUBST1_TAC) >>
    AP_TERM_TAC >>
    match_mp_tac tvars_VSUBST_same_type >>
    simp[EVERY_MAP,UNCURRY]) >>
  simp[MEM_MAP,PULL_EXISTS,EXISTS_PROD] >>
  rw[] >>
  imp_res_tac VFREE_IN_Const_VSUBST >- (
    fs[updates_cases] >>
    imp_res_tac proves_term_ok >> fs[] >>
    imp_res_tac term_ok_VFREE_IN >>
    fs[term_ok_def] >>
    imp_res_tac ALOOKUP_MEM >>
    fs[MEM_MAP,EXISTS_PROD,PULL_EXISTS] >>
    metis_tac[] ) >>
  fs[VSUBST_def,REV_ASSOCD_ALOOKUP] >>
  pop_assum mp_tac >>
  BasicProvers.CASE_TAC >- (
    imp_res_tac ALOOKUP_FAILS >>
    fs[MEM_MAP] ) >>
  strip_tac >>
  imp_res_tac ALOOKUP_MEM >>
  fs[MEM_MAP,EXISTS_PROD] >> fs[] >> rw[] >>
  fs[updates_cases] >>
  imp_res_tac ALOOKUP_ALL_DISTINCT_MEM >> fs[]
QED

Theorem ConstSpec_constrainable_cv:
  ∀eqs prop ctxt.
    ConstSpec eqs prop updates ctxt ∧
    constrainable_update_check (ConstSpec eqs prop) ⇒
    constrainable_update (ConstSpec eqs prop)
Proof
  rw[constrainable_update_check_def, eqs_tvars_ok_EVERY] >>
  metis_tac[ConstSpec_constrainable]
QED

Theorem NewConst_constrainable:
  ∀name ty. constrainable_update (NewConst name ty)
Proof
  rw[constrainable_update_def, axexts_of_upd_def,
     conexts_of_upd_def, consts_of_upd_def, types_of_upd_def]
QED

Theorem NewAxiom_constrainable:
  ∀prop. constrainable_update (NewAxiom prop)
Proof
  rw[constrainable_update_def, axexts_of_upd_def,
     conexts_of_upd_def, consts_of_upd_def, types_of_upd_def]
QED

(* ----------------------------------------------------------------------
   Executable `updates` and `extends` context checker (`check_update_ctxt`,
   `check_updates_chain`) using `holSyntaxExtraTheory.ConstDef_updates`
   ---------------------------------------------------------------------- *)

Definition check_update_ctxt_def:
  check_update_ctxt (NewType name arity) ctxt =
    ¬MEM name (MAP FST (type_list ctxt)) ∧
  check_update_ctxt (NewConst name ty) ctxt =
    (type_ok_alist (type_list ctxt) ty ∧
     ¬MEM name (MAP FST (const_list ctxt))) ∧
  check_update_ctxt (NewAxiom prop) ctxt =
    (term_ok_ctxt_check ctxt prop ∧ typeof prop = Bool) ∧
  check_update_ctxt (ConstSpec [(name, tm)] prop) ctxt =
    (prop = (Var name (typeof tm) === tm) ∧
     closed_check tm ∧
     list_subset (tvars tm) (tyvars (typeof tm)) ∧
     term_ok_ctxt_check ctxt tm ∧
     ¬MEM name (MAP FST (const_list ctxt))) ∧
  check_update_ctxt _ _ = F
End
val () = cv_auto_trans check_update_ctxt_def;

Theorem check_update_ctxt_updates:
  ∀upd ctxt.
    theory_ok (thyof ctxt) ∧ check_update_ctxt upd ctxt ⇒
    upd updates ctxt
Proof
  Cases >> simp[check_update_ctxt_def]
  >- (rpt gen_tac >>
      Cases_on `l` >> simp[check_update_ctxt_def] >>
      Cases_on `t'` >> simp[check_update_ctxt_def] >>
      PairCases_on `h` >> simp[check_update_ctxt_def] >>
      strip_tac >> rw[] >>
      irule ConstDef_updates >>
      fs[FDOM_alist_to_fmap, closed_check_eq, closed_check_def,
         term_ok_alist_thm, term_ok_ctxt_check_def,
         SUBSET_LIST_TO_SET_cv_inline])
  >- (rw[Once updates_cases, FDOM_alist_to_fmap])
  >- (rw[Once updates_cases, FDOM_alist_to_fmap, type_ok_alist_thm])
  >- (rw[Once updates_cases, term_ok_alist_thm, term_ok_ctxt_check_def] >>
      `term_ok (sigof ctxt) t` by fs[term_ok_alist_thm] >>
      imp_res_tac term_ok_welltyped >>
      metis_tac[WELLTYPED])
QED

Theorem check_update_ctxt_sound:
  ∀upd ctxt.
    theory_ok (thyof ctxt) ∧ check_update_ctxt upd ctxt ⇒
    upd updates ctxt ∧ theory_ok (thyof (upd::ctxt))
Proof
  rpt strip_tac
  >- metis_tac[check_update_ctxt_updates]
  >- (irule updates_theory_ok >>
      metis_tac[check_update_ctxt_updates])
QED

Definition check_updates_chain_def:
  check_updates_chain [] ctxt = T ∧
  check_updates_chain (u::us) ctxt =
    (check_update_ctxt u ctxt ∧ check_updates_chain us (u::ctxt))
End
val () = cv_auto_trans check_updates_chain_def;

Theorem check_updates_chain_sound:
  ∀upds ctxt.
    theory_ok (thyof ctxt) ∧ check_updates_chain upds ctxt ⇒
    (REVERSE upds ++ ctxt) extends ctxt ∧
    theory_ok (thyof (REVERSE upds ++ ctxt))
Proof
  Induct
  >- SIMP_TAC (srw_ss()) [check_updates_chain_def, extends_def] >>
  rpt gen_tac >>
  REWRITE_TAC [check_updates_chain_def, listTheory.REVERSE_DEF,
               GSYM listTheory.APPEND_ASSOC, listTheory.APPEND] >>
  strip_tac >>
  mp_tac (Q.SPECL [`h`, `ctxt`] check_update_ctxt_sound) >>
  ASM_REWRITE_TAC [] >> strip_tac >>
  first_x_assum (qspec_then `h::ctxt` mp_tac) >>
  ASM_REWRITE_TAC [] >> strip_tac >>
  ASM_REWRITE_TAC [] >>
  match_mp_tac extends_trans >>
  qexists_tac `h::ctxt` >> ASM_REWRITE_TAC [] >>
  simp[extends_def, Once relationTheory.RTC_CASES1]
QED

(* ----------------------------------------------------------------------
   Concrete `cv_eval`-Verified Context, Term, Update & Constrainable
   Certificates on `init_ctxt` and `lca_ext_ctxt`
   ---------------------------------------------------------------------- *)

Theorem FST_thyof_cv_inline[cv_inline]:
  ∀ctxt. FST (thyof ctxt) = sigof ctxt
Proof
  rw[]
QED

Theorem IN_LIST_TO_SET_cv_inline[cv_inline]:
  ∀(x : 'a) l. (x ∈ LIST_TO_SET l) = list_mem x l
Proof
  rw[MEM_cv_inline]
QED

Definition axiom_list_c_def:
  axiom_list_c [] = [] ∧
  axiom_list_c (u :: us) = axioms_of_upd_c u ++ axiom_list_c us
End
val () = cv_auto_trans axiom_list_c_def;

Definition lca_ext_upds_def:
  lca_ext_upds =
    [ConstDef «k_sound» (Abs (Var «b» Bool) (Var «b» Bool) ===
                         Abs (Var «b» Bool) (Var «b» Bool));
     NewAxiom (Const «k_sound» Bool)]
End
val () = cv_auto_trans lca_ext_upds_def;

Definition lca_ext_ctxt_def:
  lca_ext_ctxt = REVERSE lca_ext_upds ++ init_ctxt
End
val () = cv_auto_trans lca_ext_ctxt_def;

Theorem axsof_thyof_init_ctxt_cv_inline[cv_inline]:
  axsof (thyof init_ctxt) = LIST_TO_SET (axiom_list_c init_ctxt)
Proof
  EVAL_TAC
QED

Theorem axsof_thyof_lca_ext_ctxt_cv_inline[cv_inline]:
  axsof (thyof lca_ext_ctxt) = LIST_TO_SET (axiom_list_c lca_ext_ctxt)
Proof
  EVAL_TAC
QED

Theorem init_ctxt_syntax_cv_verified:
  init_ctxt_axexts = [] ∧
  is_std_sig (sigof init_ctxt) ∧
  FLOOKUP (tysof (thyof init_ctxt)) «bool» = SOME 0 ∧
  FLOOKUP (tysof (thyof init_ctxt)) «fun» = SOME 2 ∧
  FLOOKUP (tysof (thyof init_ctxt)) «ind» = NONE ∧
  FLOOKUP (tmsof (thyof init_ctxt)) «=» = SOME (Fun (Tyvar «A») (Fun (Tyvar «A») Bool)) ∧
  FLOOKUP (tmsof (thyof init_ctxt)) «@» = NONE ∧
  type_ok (tysof (thyof init_ctxt)) (Fun Bool Bool) ∧
  term_ok (sigof (thyof init_ctxt))
    (Comb (Abs (Var «x» Bool) (Var «x» Bool)) (Var «x» Bool) === Var «x» Bool) ∧
  all_constrainable_updates init_ctxt ∧
  all_constrainable_updates lca_ext_upds ∧
  check_updates_chain lca_ext_upds init_ctxt ∧
  FLOOKUP (tmsof (thyof lca_ext_ctxt)) «k_sound» = SOME Bool ∧
  (Const «k_sound» Bool) ∈ axsof (thyof lca_ext_ctxt) ∧
  term_ok (sigof (thyof lca_ext_ctxt)) (Const «k_sound» Bool) ∧
  welltyped (Comb (Abs (Var «x» Bool) (Var «x» Bool)) (Const «k_sound» Bool)
             === Const «k_sound» Bool) ∧
  ACONV (Abs (Var «x» Bool) (Var «x» Bool))
        (Abs (Var «y» Bool) (Var «y» Bool)) ∧
  CLOSED (Abs (Var «x» Bool) (Var «x» Bool)) ∧
  typeof (Var «s» Bool === Var «s» Bool) = Bool ∧
  ¬VFREE_IN (Var «x» Bool) (Abs (Var «x» Bool) (Var «x» Bool)) ∧
  sizeof (Comb (Abs (Var «x» Bool) (Var «x» Bool)) (Var «x» Bool)
          === Var «x» Bool) = 9
Proof
  CONV_TAC cv_eval
QED

Theorem init_ctxt_std_sig_cv:
  is_std_sig (sigof init_ctxt)
Proof
  CONV_TAC cv_eval
QED

Theorem lca_ext_ctxt_extends_init_cv:
  lca_ext_ctxt extends init_ctxt ∧
  theory_ok (thyof lca_ext_ctxt) ∧
  term_ok (sigof lca_ext_ctxt) (Const «k_sound» Bool) ∧
  EVERY constrainable_update_check init_ctxt ∧
  EVERY constrainable_update_check lca_ext_upds
Proof
  strip_assume_tac
    (SIMP_RULE bool_ss [pairTheory.FST] init_ctxt_syntax_cv_verified) >>
  mp_tac (Q.SPECL [`lca_ext_upds`, `init_ctxt`] check_updates_chain_sound) >>
  ASM_REWRITE_TAC [init_theory_ok, GSYM lca_ext_ctxt_def,
                   all_constrainable_updates_EVERY] >>
  strip_tac >> ASM_REWRITE_TAC []
QED

val _ = export_theory ();

