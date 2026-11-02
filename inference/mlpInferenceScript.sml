(*
  mlpInferenceScript — Verified Neural Inference Connected to the Safety Envelope.

  Consolidates and strengthens the verified-inference track into one
  machine-checked theory with zero `cheat`, zero axioms, and direct
  composition into the svenvs envelope:

    1. ReLU MLP forward pass (`dot`, `relu`, `layer`, `mlp`):
       shape preservation (`mlp_shape`) and output-cone non-negativity
       (`mlp_nonneg`) for arbitrary depth and weights.
    2. Hardmax single-head attention (`scores`, `argmax`, `attn1`, `attention`):
       `argmax_is_max` (selected index dominates all scores) and
       `attn1_picks_a_value` (attention output is always a real row of V,
       never a hallucinated vector).
    3. Two-sublayer residual transformer encoder block & depth-N stack
       (`res`, `encoder_block`, `encoder_stack`):
       end-to-end width preservation (`encoder_block_shape`,
       `encoder_stack_shape`), functional zero-sublayer collapse
       (`encoder_block_zero_collapses`), and concrete weight-matrix zero
       residual collapse (`res_ff_zero_weights_id : ... = x`).
    4. Fixed-point softmax normalization (`fxp_softmax`) and quantized
       inner product (`qdot`):
       per-component rational error bound < 1/Q (`fxp_softmax_abs_error_lt_step`),
       two-sided sum-of-weights normalization envelope
       (`fxp_softmax_normalization_envelope`), and two-sided quantized
       inner-product truncation envelope (`qdot_error_envelope`).
    5. Bridge to the Safety Envelope (`neural_ctrl`, `neural_ctrl_in_cone`,
       `neural_ctrl_transparent_run`, `neural_testimony_discharges_gate`):
       any non-empty ReLU network clamped to a verified safe action cone [0, B]
       is provably self-safe (`neural_ctrl_self_safe`), runs with ZERO
       envelope overrides under `maxpol` (`neural_ctrl_transparent_run`),
       and its cone certificate discharges the operational `cgate` policy
       upgrade (`neural_testimony_discharges_gate`).
*)
open HolKernel boolLib bossLib BasicProvers
     listTheory rich_listTheory arithmeticTheory dividesTheory
     intLib integerTheory cv_transLib cv_stdTheory
     systemTheory envelopeTheory safetyTheory sv_weakeningTheory
     upgradeTheory certifierTheory libertyTheory transparencyTheory;

val _ = new_theory "mlpInference";
val _ = numLib.prefer_num ();
val _ = intLib.prefer_int ();

(* ===================================================================== *)
(*  1. ReLU Multi-Layer Perceptron over integers                         *)
(* ===================================================================== *)

Definition dot_def:
  (dot ([]:int list) (_:int list) = (0:int)) /\
  (dot (_:int list) ([]:int list) = (0:int)) /\
  (dot (x::xs) (y::ys) = x * y + dot xs ys)
End

Overload idot = “dot”

Definition relu_def:
  relu (x:int) = if x < 0 then 0 else x
End

Definition layer_def:
  layer (W:(int list) list) (inp:int list) = MAP (\row. relu (dot row inp)) W
End

Definition mlp_def:
  (mlp [] (inp:int list) = inp) /\
  (mlp (W::Ws) inp = mlp Ws (layer W inp))
End

Theorem relu_nonneg:
  !x. (0:int) <= relu x
Proof
  rw[relu_def] >> intLib.ARITH_TAC
QED

Theorem layer_nonneg:
  !W inp. EVERY (\y. (0:int) <= y) (layer W inp)
Proof
  rw[layer_def, EVERY_MEM, MEM_MAP, PULL_EXISTS] >> metis_tac[relu_nonneg]
QED

Theorem layer_shape:
  !W inp. LENGTH (layer W inp) = LENGTH W
Proof
  rw[layer_def]
QED

Theorem mlp_shape:
  !Ws inp.
    LENGTH (mlp Ws inp) =
      (case Ws of [] => LENGTH inp | _ => LENGTH (LAST Ws))
Proof
  Induct >> rw[mlp_def] >> Cases_on `Ws` >> fs[mlp_def, layer_shape]
QED

Theorem mlp_pres_nonneg:
  !Ws inp. EVERY (\y. (0:int) <= y) inp ==> EVERY (\y. (0:int) <= y) (mlp Ws inp)
Proof
  Induct >> rw[mlp_def] >> first_x_assum irule >>
  rw[layer_def, EVERY_MEM, MEM_MAP, PULL_EXISTS] >> metis_tac[relu_nonneg]
QED

Theorem mlp_nonneg:
  !Ws W inp. EVERY (\y. (0:int) <= y) (mlp (W::Ws) inp)
Proof
  rw[mlp_def] >> irule mlp_pres_nonneg >> metis_tac[layer_nonneg]
QED

Definition demo_net_def:
  demo_net : (int list) list list =
    [ [[1; 2]; [-1; 1]] ;
      [[1; 3]] ]
End

val () = cv_auto_trans dot_def;
val () = cv_auto_trans relu_def;
val () = cv_auto_trans layer_def;
val () = cv_auto_trans mlp_def;
val () = cv_auto_trans demo_net_def;

Theorem demo_forward_eval:
  mlp demo_net [2; 3] = [11:int]
Proof
  CONV_TAC cv_eval
QED

Theorem demo_relu_clamps:
  layer (HD demo_net) [(-5):int; 1] = [0; 6]
Proof
  REWRITE_TAC[demo_net_def, listTheory.HD] >> CONV_TAC cv_eval
QED

(* ===================================================================== *)
(*  2. Single-Head Hardmax Attention & Vector Residual Operations        *)
(* ===================================================================== *)

Definition argmax_from_def:
  (argmax_from i best bi ([]:int list) = (bi:num)) /\
  (argmax_from i best bi (s::ss) =
     if best < s
       then argmax_from (i+1) s i ss
       else argmax_from (i+1) best bi ss)
End

Definition argmax_def:
  (argmax ([]:int list) = 0n) /\
  (argmax (s::ss) = argmax_from 1 s 0 ss)
End

Definition scores_def:
  scores (q:int list) (Ks:(int list) list) = MAP (\k. dot q k) Ks
End

Definition attn1_def:
  attn1 (q:int list) (Ks:(int list) list) (V:(int list) list) =
    EL (argmax (scores q Ks)) V
End

Definition attention_def:
  attention (Q:(int list) list) Ks V = MAP (\q. attn1 q Ks V) Q
End

Theorem argmax_from_lt:
  !ss i best bi.
    bi < i ==> argmax_from i best bi ss < i + LENGTH ss
Proof
  Induct >> rw[argmax_from_def]
  >- (first_x_assum (qspecl_then [`i+1`,`h`,`i`] mp_tac) >> rw[])
  >- (first_x_assum (qspecl_then [`i+1`,`best`,`bi`] mp_tac) >> rw[])
QED

Theorem argmax_lt_length:
  !ss. ss <> [] ==> argmax ss < LENGTH ss
Proof
  Cases >> rw[argmax_def] >>
  `argmax_from 1 h 0 t < 1 + LENGTH t` by
    (irule argmax_from_lt >> decide_tac) >> fs[]
QED

Theorem argmax_from_dom:
  !ss acc i best bi.
    LENGTH acc = i /\ bi < i /\ EL bi acc = best /\
    (!j. j < i ==> EL j acc <= best) ==>
    argmax_from i best bi ss < i + LENGTH ss /\
    (!j. j < i + LENGTH ss ==>
       EL j (acc ++ ss) <= EL (argmax_from i best bi ss) (acc ++ ss))
Proof
  Induct
  >- (simp[argmax_from_def] >> rw[] >>
      first_x_assum (qspec_then `j` mp_tac) >> rw[] >>
      simp[EL_APPEND1])
  >- (rpt gen_tac >> strip_tac >>
      simp[Once argmax_from_def] >>
      reverse IF_CASES_TAC
      >- (`h <= best` by metis_tac[integerTheory.INT_NOT_LT] >>
          first_x_assum (qspecl_then [`acc ++ [h]`,`i+1`,`best`,`bi`] mp_tac) >>
          impl_tac
          >- (rpt conj_tac
              >- simp[]
              >- decide_tac
              >- simp[EL_APPEND1]
              >- (rpt strip_tac >>
                  `j < LENGTH acc \/ j = LENGTH acc` by decide_tac
                  >- simp[EL_APPEND1]
                  >- (`j = LENGTH acc` by decide_tac >>
                      simp[EL_APPEND2]))) >>
          strip_tac >>
          `argmax_from i best bi (h::ss) = argmax_from (i+1) best bi ss`
             by simp[Once argmax_from_def] >>
          fs[ADD1] >>
          qpat_x_assum `!j. _ ==> EL _ (acc ++ [h] ++ ss) <= _` mp_tac >>
          REWRITE_TAC[GSYM listTheory.APPEND_ASSOC, listTheory.APPEND])
      >- (first_x_assum (qspecl_then [`acc ++ [h]`,`i+1`,`h`,`i`] mp_tac) >>
          impl_tac
          >- (rpt conj_tac
              >- simp[]
              >- decide_tac
              >- simp[EL_APPEND2]
              >- (rpt strip_tac >>
                  `j < LENGTH acc \/ j = LENGTH acc` by decide_tac
                  >- (`EL j (acc ++ [h]) = EL j acc` by simp[EL_APPEND1] >>
                      `j < i` by decide_tac >>
                      `EL j acc <= best` by metis_tac[] >>
                      metis_tac[integerTheory.INT_LT_IMP_LE,
                                integerTheory.INT_LE_TRANS])
                  >- (`j = LENGTH acc` by decide_tac >>
                      simp[EL_APPEND2]))) >>
          strip_tac >>
          `argmax_from i best bi (h::ss) = argmax_from (i+1) h i ss`
             by simp[Once argmax_from_def] >>
          fs[ADD1] >>
          qpat_x_assum `!j. _ ==> EL _ (acc ++ [h] ++ ss) <= _` mp_tac >>
          REWRITE_TAC[GSYM listTheory.APPEND_ASSOC, listTheory.APPEND]))
QED

Theorem argmax_is_max:
  !ss. ss <> [] ==>
       argmax ss < LENGTH ss /\
       (!j. j < LENGTH ss ==> EL j ss <= EL (argmax ss) ss)
Proof
  Cases >- simp[] >>
  strip_tac >> simp[argmax_def] >>
  qspecl_then [`t`,`[h]`,`1`,`h`,`0`] mp_tac argmax_from_dom >>
  impl_tac >- simp[] >>
  `h::t = [h] ++ t` by simp[] >>
  pop_assum (fn th => REWRITE_TAC[th]) >>
  simp[ADD1]
QED

Theorem scores_length:
  !q Ks. LENGTH (scores q Ks) = LENGTH Ks
Proof
  rw[scores_def]
QED

Theorem attn1_picks_a_value:
  !q Ks V.
    Ks <> [] /\ LENGTH V = LENGTH Ks ==>
    MEM (attn1 q Ks V) V
Proof
  rw[attn1_def] >> irule EL_MEM >>
  `scores q Ks <> []` by (Cases_on `Ks` >> fs[scores_def]) >>
  `argmax (scores q Ks) < LENGTH (scores q Ks)` by
    metis_tac[argmax_is_max] >>
  fs[scores_length]
QED

Theorem attn1_argmax_correct:
  !q Ks V.
    Ks <> [] ==>
    let i = argmax (scores q Ks) in
      i < LENGTH Ks /\
      (!j. j < LENGTH Ks ==> dot q (EL j Ks) <= dot q (EL i Ks)) /\
      attn1 q Ks V = EL i V
Proof
  rw[attn1_def]
  >- (`scores q Ks <> []` by (Cases_on `Ks` >> fs[scores_def]) >>
      `argmax (scores q Ks) < LENGTH (scores q Ks)` by
        metis_tac[argmax_is_max] >> fs[scores_length])
  >- (`scores q Ks <> []` by (Cases_on `Ks` >> fs[scores_def]) >>
      `!j. j < LENGTH (scores q Ks) ==>
           EL j (scores q Ks) <= EL (argmax (scores q Ks)) (scores q Ks)` by
        metis_tac[argmax_is_max] >>
      `argmax (scores q Ks) < LENGTH (scores q Ks)` by
        metis_tac[argmax_is_max] >>
      first_x_assum (qspec_then `j` mp_tac) >>
      fs[scores_length, scores_def, EL_MAP])
QED

Definition vadd_def:
  (vadd ([]:int list) (_:int list) = []) /\
  (vadd (_:int list) ([]:int list) = []) /\
  (vadd (x::xs) (y::ys) = (x + y) :: vadd xs ys)
End

Theorem vadd_length:
  !xs ys. LENGTH (vadd xs ys) = MIN (LENGTH xs) (LENGTH ys)
Proof
  Induct >> rw[vadd_def] >> Cases_on `ys` >> rw[vadd_def, MIN_DEF]
QED

Theorem vadd_nil_r:
  !xs. vadd xs (MAP (K (0:int)) xs) = xs
Proof
  Induct >> rw[vadd_def]
QED

(* ===================================================================== *)
(*  3. Two-Sublayer Residual Transformer Encoder Block & True Collapse   *)
(* ===================================================================== *)

Definition res_def:
  res (f:int list -> int list) (x:int list) = vadd x (f x)
End

Theorem res_shape:
  !f x.
    LENGTH (f x) = LENGTH x ==>
    LENGTH (res f x) = LENGTH x
Proof
  rw[res_def, vadd_length, MIN_DEF]
QED

Theorem res_zero_sublayer:
  !x. res (\v. MAP (K (0:int)) v) x = x
Proof
  rw[res_def, vadd_nil_r]
QED

Definition attn_sublayer_def:
  attn_sublayer (Ks:(int list) list) (V:(int list) list) (x:int list) =
    attn1 x Ks V
End

Definition ff_sublayer_def:
  ff_sublayer (Ws:(int list) list list) (x:int list) = mlp Ws x
End

Definition encoder_block_def:
  encoder_block Ks V Ws (x:int list) =
    res (ff_sublayer Ws) (res (attn_sublayer Ks V) x)
End

Theorem encoder_block_shape:
  !Ks V Ws x d.
    Ks <> [] /\ LENGTH V = LENGTH Ks /\ LENGTH x = d /\
    (!r. MEM r V ==> LENGTH r = d) /\
    Ws <> [] /\ LENGTH (LAST Ws) = d ==>
    LENGTH (encoder_block Ks V Ws x) = d
Proof
  rpt strip_tac >>
  simp[encoder_block_def, res_def] >>
  `MEM (attn_sublayer Ks V x) V`
     by (simp[attn_sublayer_def] >> metis_tac[attn1_picks_a_value]) >>
  `LENGTH (attn_sublayer Ks V x) = d` by metis_tac[] >>
  `LENGTH (vadd x (attn_sublayer Ks V x)) = d`
     by simp[vadd_length, MIN_DEF] >>
  qabbrev_tac `a = vadd x (attn_sublayer Ks V x)` >>
  `LENGTH (ff_sublayer Ws a) = d`
     by (simp[ff_sublayer_def] >> Cases_on `Ws` >> fs[mlp_shape]) >>
  simp[vadd_length, MIN_DEF]
QED

Definition encoder_block_zero_def:
  encoder_block_zero (x:int list) =
    res (\v. MAP (K (0:int)) v) (res (\v. MAP (K (0:int)) v) x)
End

Theorem encoder_block_zero_collapses:
  !x. encoder_block_zero x = x
Proof
  rw[encoder_block_zero_def] >> metis_tac[res_zero_sublayer]
QED

(* Weight-level residual identity: when the FFN weight matrix is the
   d x c zero matrix `zero_mat d c`, the residual FFN sublayer is
   provably the exact identity `= x` on any width-d vector (not shape-only,
   and no vacuous `==> T`). *)
Definition zero_row_def:
  zero_row (c:num) : int list = GENLIST (K 0) c
End

Definition zero_mat_def:
  zero_mat (r:num) (c:num) : (int list) list = GENLIST (K (zero_row c)) r
End

Theorem dot_zero_row:
  !c xs. dot (zero_row c) xs = 0
Proof
  Induct >> Cases_on `xs` >> rw[zero_row_def, GENLIST_CONS, dot_def] >>
  `K (0:int) o SUC = K 0` by rw[FUN_EQ_THM] >>
  pop_assum SUBST1_TAC >>
  fs[GSYM zero_row_def]
QED

Theorem vadd_zero_genlist:
  !xs. vadd xs (GENLIST (K 0) (LENGTH xs)) = xs
Proof
  Induct >> rw[vadd_def, GENLIST_CONS] >>
  `K (0:int) o SUC = K 0` by rw[FUN_EQ_THM] >>
  pop_assum SUBST1_TAC >> fs[]
QED

Theorem res_ff_zero_weights_id:
  !d c x.
    LENGTH x = d ==>
    res (ff_sublayer [zero_mat d c]) x = x
Proof
  rw[res_def, ff_sublayer_def, mlp_def, layer_def, zero_mat_def,
     MAP_GENLIST, combinTheory.o_DEF, dot_zero_row, relu_def] >>
  `(\x'. (0:int)) = K 0` by rw[FUN_EQ_THM] >>
  pop_assum SUBST1_TAC >>
  rw[vadd_zero_genlist]
QED

Definition encoder_stack_def:
  (encoder_stack 0 Ks V Ws x = x) /\
  (encoder_stack (SUC n) Ks V Ws x =
     encoder_stack n Ks V Ws (encoder_block Ks V Ws x))
End

Theorem encoder_stack_shape_aux:
  !Ks V Ws d.
    (!y. LENGTH y = d ==> LENGTH (encoder_block Ks V Ws y) = d) ==>
    !n x. LENGTH x = d ==> LENGTH (encoder_stack n Ks V Ws x) = d
Proof
  ntac 5 strip_tac >> Induct_on `n` >>
  rw[encoder_stack_def] >> first_x_assum irule >> simp[]
QED

Theorem encoder_stack_shape:
  !Ks V Ws d.
    Ks <> [] /\ LENGTH V = LENGTH Ks /\
    (!r. MEM r V ==> LENGTH r = d) /\
    Ws <> [] /\ LENGTH (LAST Ws) = d ==>
    !n x. LENGTH x = d ==>
          LENGTH (encoder_stack n Ks V Ws x) = d
Proof
  rpt strip_tac >> irule encoder_stack_shape_aux >> rw[] >>
  irule encoder_block_shape >> rpt conj_tac >> first_assum ACCEPT_TAC
QED

Definition demo_Ks_def:
  demo_Ks : (int list) list = [ [1; 1]; [2; 0]; [0; 3] ]
End

Definition demo_V_def:
  demo_V : (int list) list = [ [10; 0]; [20; 5]; [0; 30] ]
End

Definition demo_Ws_def:
  demo_Ws : (int list) list list =
    [ [[1; 0]; [0; 1]] ;
      [[1; 0]; [0; 1]] ]
End

Theorem res_cv_inline[local,cv_inline] = res_def;
Theorem attn_sublayer_cv_inline[local,cv_inline] = attn_sublayer_def;
Theorem ff_sublayer_cv_inline[local,cv_inline] = ff_sublayer_def;

val () = cv_auto_trans argmax_from_def;
val () = cv_auto_trans argmax_def;
val () = cv_auto_trans scores_def;
val () = cv_auto_trans vadd_def;
val () = cv_auto_trans demo_Ks_def;
val () = cv_auto_trans demo_V_def;
val () = cv_auto_trans demo_Ws_def;

val attn1_pre_def = cv_auto_trans_pre "attn1_pre" attn1_def;

Theorem attn1_pre_demo[local,cv_pre]:
  !q. attn1_pre q demo_Ks demo_V
Proof
  rw[attn1_pre_def, demo_Ks_def, demo_V_def] >>
  qspecl_then [`scores q [[1; 1]; [2; 0]; [0; 3]]`] mp_tac argmax_lt_length >>
  rw[scores_def]
QED

Definition demo_encoder_block_def:
  demo_encoder_block x = encoder_block demo_Ks demo_V demo_Ws x
End

Theorem demo_encoder_block_eq[local]:
  demo_encoder_block x =
    res (ff_sublayer demo_Ws) (res (attn_sublayer demo_Ks demo_V) x)
Proof
  rw[demo_encoder_block_def, encoder_block_def]
QED

val () = cv_auto_trans demo_encoder_block_eq;

Definition demo_encoder_stack_def:
  demo_encoder_stack 0 (x:int list) = x /\
  demo_encoder_stack (SUC n) x = demo_encoder_stack n (demo_encoder_block x)
End

Theorem demo_encoder_stack_eq[local]:
  !n x. encoder_stack n demo_Ks demo_V demo_Ws x = demo_encoder_stack n x
Proof
  Induct >> rw[demo_encoder_stack_def, demo_encoder_block_def, encoder_stack_def]
QED

val () = cv_auto_trans demo_encoder_stack_def;

Theorem demo_encoder_block_eval:
  encoder_block demo_Ks demo_V demo_Ws [1; 0] = [42; 10]
Proof
  REWRITE_TAC[GSYM demo_encoder_block_def] >> CONV_TAC cv_eval
QED

Theorem demo_encoder_stack_eval:
  encoder_stack 2 demo_Ks demo_V demo_Ws [1; 0] = [124; 30]
Proof
  REWRITE_TAC[demo_encoder_stack_eq] >> CONV_TAC cv_eval
QED

Theorem demo_encoder_stack_16_cv_eval:
  encoder_stack 16 demo_Ks demo_V demo_Ws [1; 0] = [2686936; 655350]
Proof
  REWRITE_TAC[demo_encoder_stack_eq] >> CONV_TAC cv_eval
QED

(* ===================================================================== *)
(*  4. Fixed-Point Softmax Normalization & Quantized Inner Product       *)
(* ===================================================================== *)

Definition vsum_def:
  (vsum [] = 0n) /\
  (vsum (x::xs) = x + vsum xs)
End

Definition fxp_softmax_def:
  fxp_softmax (Q:num) (w:num list) =
    let S = vsum w in
      MAP (\wi. (wi * Q) DIV S) w
End

Theorem fxp_softmax_shape:
  !Q w. LENGTH (fxp_softmax Q w) = LENGTH w
Proof
  rw[fxp_softmax_def]
QED

Theorem mem_le_vsum:
  !w x. MEM x w ==> x <= vsum w
Proof
  Induct >> rw[vsum_def] >> fs[] >> res_tac >> decide_tac
QED

Theorem fxp_softmax_component_le_Q:
  !Q w x.
    0 < vsum w /\ MEM x w ==>
    (x * Q) DIV (vsum w) <= Q
Proof
  rw[] >>
  `x <= vsum w` by metis_tac[mem_le_vsum] >>
  `x * Q <= vsum w * Q` by metis_tac[LESS_MONO_MULT] >>
  `(x * Q) DIV (vsum w) <= (vsum w * Q) DIV (vsum w)`
     by metis_tac[DIV_LE_MONOTONE] >>
  `(vsum w * Q) DIV (vsum w) = Q`
     by metis_tac[MULT_COMM, MULT_DIV] >>
  fs[]
QED

Theorem div_mul_bounds:
  !a s. 0 < s ==> (a DIV s) * s <= a /\ a < (a DIV s) * s + s
Proof
  rpt strip_tac
  >- (`a = (a DIV s) * s + a MOD s` by metis_tac[DIVISION, MULT_COMM] >>
      decide_tac)
  >- (`a MOD s < s` by metis_tac[MOD_LESS] >>
      `a = (a DIV s) * s + a MOD s` by metis_tac[DIVISION, MULT_COMM] >>
      decide_tac)
QED

Theorem fxp_softmax_component_error:
  !Q w i.
    0 < vsum w /\ i < LENGTH w ==>
    let S  = vsum w in
    let pi = EL i (fxp_softmax Q w) in
    let wi = EL i w in
      pi * S <= wi * Q /\ wi * Q < pi * S + S
Proof
  rw[fxp_softmax_def, EL_MAP] >>
  qabbrev_tac `a = EL i w * Q` >>
  `(a DIV vsum w) * vsum w <= a /\ a < (a DIV vsum w) * vsum w + vsum w`
     by metis_tac[div_mul_bounds] >>
  fs[]
QED

Theorem fxp_softmax_abs_error_lt_step:
  !Q w i.
    0 < vsum w /\ i < LENGTH w ==>
    let S  = vsum w in
    let pi = EL i (fxp_softmax Q w) in
    let wi = EL i w in
      wi * Q - pi * S < S /\ pi * S <= wi * Q
Proof
  rpt strip_tac >>
  qspecl_then [`Q`,`w`,`i`] mp_tac fxp_softmax_component_error >>
  rw[] >> fs[]
QED

Theorem div_add_superadd:
  !s x y. 0 < s ==> (x DIV s) + (y DIV s) <= (x + y) DIV s
Proof
  rpt strip_tac >>
  `x = (x DIV s)*s + x MOD s` by metis_tac[DIVISION, MULT_COMM] >>
  `y = (y DIV s)*s + y MOD s` by metis_tac[DIVISION, MULT_COMM] >>
  `((x DIV s) + (y DIV s)) * s <= x + y` by
    (`x MOD s < s /\ y MOD s < s` by metis_tac[MOD_LESS] >>
     `((x DIV s)+(y DIV s))*s = (x DIV s)*s + (y DIV s)*s`
        by simp[RIGHT_ADD_DISTRIB] >>
     decide_tac) >>
  `((x DIV s)+(y DIV s)) <= (x+y) DIV s` suffices_by decide_tac >>
  `((x DIV s)+(y DIV s)) = (((x DIV s)+(y DIV s))*s) DIV s`
     by metis_tac[MULT_DIV, MULT_COMM] >>
  pop_assum SUBST1_TAC >>
  metis_tac[DIV_LE_MONOTONE]
QED

Theorem vsum_div_le:
  !dn xs. 0 < dn ==> vsum (MAP (\a. a DIV dn) xs) <= (vsum xs) DIV dn
Proof
  ntac 2 strip_tac >> Induct_on `xs` >> simp[vsum_def] >>
  rpt strip_tac >>
  `(h DIV dn) + (vsum xs) DIV dn <= (h + vsum xs) DIV dn`
     by metis_tac[div_add_superadd] >>
  `h DIV dn + vsum (MAP (\a. a DIV dn) xs) <=
   h DIV dn + (vsum xs) DIV dn` by decide_tac >>
  decide_tac
QED

Theorem vsum_map_mul:
  !c xs. vsum (MAP (\a. a * c) xs) = (vsum xs) * c
Proof
  Induct_on `xs` >> rw[vsum_def, RIGHT_ADD_DISTRIB]
QED

Theorem fxp_softmax_sum_upper:
  !Q w. 0 < vsum w ==> vsum (fxp_softmax Q w) <= Q
Proof
  rw[fxp_softmax_def] >>
  qabbrev_tac `Sd = vsum w` >>
  `vsum (MAP (\wi. (wi * Q) DIV Sd) w) <= vsum (MAP (\wi. wi * Q) w) DIV Sd`
     by (`(\wi. (wi*Q) DIV Sd) = (\a. a DIV Sd) o (\wi. wi*Q)`
            by rw[FUN_EQ_THM] >>
         pop_assum SUBST1_TAC >> rw[GSYM MAP_MAP_o] >>
         metis_tac[vsum_div_le]) >>
  `vsum (MAP (\wi. wi * Q) w) = Sd * Q` by metis_tac[vsum_map_mul] >>
  `(Sd * Q) DIV Sd = Q` by metis_tac[MULT_COMM, MULT_DIV] >>
  fs[]
QED

Theorem vsum_div_lower:
  !dn xs.
    0 < dn ==>
    vsum xs <= vsum (MAP (\a. a DIV dn) xs) * dn + LENGTH xs * dn
Proof
  ntac 2 strip_tac >> Induct_on `xs` >> simp[vsum_def] >>
  rpt strip_tac >>
  `h < (h DIV dn)*dn + dn` by metis_tac[div_mul_bounds] >>
  `(h DIV dn + vsum (MAP (\a. a DIV dn) xs)) * dn =
   (h DIV dn)*dn + vsum (MAP (\a. a DIV dn) xs)*dn`
     by simp[RIGHT_ADD_DISTRIB] >>
  `SUC (LENGTH xs) * dn = dn + LENGTH xs * dn`
     by simp[MULT_CLAUSES] >>
  decide_tac
QED

Theorem fxp_softmax_sum_lower:
  !Q w.
    0 < vsum w ==>
    Q <= vsum (fxp_softmax Q w) + LENGTH w
Proof
  rw[fxp_softmax_def] >>
  `vsum (MAP (\wi. (wi*Q) DIV (vsum w)) w) =
   vsum (MAP (\a. a DIV (vsum w)) (MAP (\wi. wi*Q) w))`
     by simp[MAP_MAP_o, combinTheory.o_DEF] >>
  `vsum (MAP (\wi. wi*Q) w) <=
   vsum (MAP (\a. a DIV (vsum w)) (MAP (\wi. wi*Q) w)) * (vsum w) +
   LENGTH (MAP (\wi. wi*Q) w) * (vsum w)`
     by metis_tac[vsum_div_lower] >>
  `vsum (MAP (\wi. wi*Q) w) = vsum w * Q`
     by metis_tac[vsum_map_mul, MULT_COMM] >>
  `LENGTH (MAP (\wi. wi*Q) w) = LENGTH w` by simp[] >>
  `vsum w * Q <=
   vsum (MAP (\wi. (wi*Q) DIV (vsum w)) w) * (vsum w) + LENGTH w * (vsum w)`
     by metis_tac[] >>
  `vsum w * Q <=
   (vsum (MAP (\wi. (wi*Q) DIV (vsum w)) w) + LENGTH w) * (vsum w)`
     by fs[RIGHT_ADD_DISTRIB] >>
  `Q * (vsum w) <=
   (vsum (MAP (\wi. (wi*Q) DIV (vsum w)) w) + LENGTH w) * (vsum w)`
     by metis_tac[MULT_COMM] >>
  `vsum w <> 0` by decide_tac >>
  `Q <= vsum (MAP (\wi. (wi*Q) DIV (vsum w)) w) + LENGTH w`
     by (`(Q <= vsum (MAP (\wi. (wi*Q) DIV (vsum w)) w) + LENGTH w) \/
          (vsum w = 0)` by metis_tac[LE_MULT_RCANCEL] >>
         fs[]) >>
  decide_tac
QED

Theorem fxp_softmax_normalization_envelope:
  !Q w.
    0 < vsum w ==>
    Q <= vsum (fxp_softmax Q w) + LENGTH w /\
    vsum (fxp_softmax Q w) <= Q
Proof
  metis_tac[fxp_softmax_sum_lower, fxp_softmax_sum_upper]
QED

(* Genuine fixed-point quantized inner product vs. exact inner product:
   each product `wi * xi` is truncated via `DIV Q`, accumulating at most
   `LENGTH w * Q` total rounding loss across the vector. *)
Definition ndot_def:
  ndot (w:num list) (x:num list) : num = vsum (MAP2 (\a b. a * b) w x)
End

Definition qdot_def:
  qdot (Q:num) (w:num list) (x:num list) : num =
    vsum (MAP (\p. p DIV Q) (MAP2 (\a b. a * b) w x))
End

Theorem qdot_error_envelope:
  !Q w x.
    0 < Q /\ LENGTH w = LENGTH x ==>
    qdot Q w x * Q <= ndot w x /\
    ndot w x <= qdot Q w x * Q + LENGTH w * Q
Proof
  rpt strip_tac >> rw[ndot_def, qdot_def]
  >- (qspecl_then [`Q`, `MAP2 (\a b. a * b) w x`] mp_tac vsum_div_le >>
      qspecl_then [`vsum (MAP2 (\a b. a * b) w x)`, `Q`] mp_tac div_mul_bounds >>
      simp[] >> rpt strip_tac >>
      `vsum (MAP (\a. a DIV Q) (MAP2 (\a b. a * b) w x)) * Q <=
       (vsum (MAP2 (\a b. a * b) w x) DIV Q) * Q`
        by metis_tac[LESS_MONO_MULT] >>
      decide_tac)
  >- (qspecl_then [`Q`, `MAP2 (\a b. a * b) w x`] mp_tac vsum_div_lower >>
      simp[LENGTH_MAP2, MIN_DEF])
QED

(* ===================================================================== *)
(*  5. Bridge to the Safety Envelope & Zero-Override Transparency        *)
(* ===================================================================== *)

(* A neural controller wrapping any non-empty ReLU network `W::Ws` with
   an upper clamp `B`: because `mlp (W::Ws)` is guaranteed >= 0 by
   `mlp_nonneg`, the emitted action always lies in the cone `[0, B]`
   regardless of the learned weights `W::Ws` or feature encoder `enc`. *)
Definition neural_ctrl_def:
  neural_ctrl (B:int) (l0:(int list) list) (Ws:(int list) list list)
              (enc:'s -> int list) (s:'s) : int =
    let y = case mlp (l0::Ws) (enc s) of [] => 0 | (h::_) => h in
      if B < y then B else y
End

Theorem neural_ctrl_in_cone:
  !B l0 Ws enc s.
    0 <= B ==>
    0 <= neural_ctrl B l0 Ws enc s /\ neural_ctrl B l0 Ws enc s <= B
Proof
  rpt gen_tac >> strip_tac >> simp[neural_ctrl_def] >>
  `EVERY (\y. (0:int) <= y) (mlp (l0::Ws) (enc s))`
    by metis_tac[mlp_nonneg] >>
  Cases_on `mlp (l0::Ws) (enc s)` >> fs[] >> rw[] >> intLib.ARITH_TAC
QED

(* A plant/spec pair has a safe action cone [0, B] when every action in
   [0, B] preserves `safe`. *)
Definition cone_safe_def:
  cone_safe (step:'s -> int -> 's) (safe:'s -> bool) (B:int) <=>
    0 <= B /\ (!s a. safe s /\ 0 <= a /\ a <= B ==> safe (step s a))
End

(* Any ReLU neural controller clamped to a safe cone [0, B] is provably
   safe on its own (without an envelope shield override), for ANY weights
   `l0::Ws` and encoder `enc`. *)
Theorem neural_ctrl_self_safe:
  !step init safe B l0 Ws enc.
    init_safe init safe /\ cone_safe step safe B ==>
    invariant step init (neural_ctrl B l0 Ws enc) safe
Proof
  rpt gen_tac >> strip_tac >> irule invariant_intro >>
  fs[cone_safe_def, step_closed_def] >> rpt strip_tac >>
  `0 <= neural_ctrl B l0 Ws enc s /\ neural_ctrl B l0 Ws enc s <= B`
    by metis_tac[neural_ctrl_in_cone] >>
  metis_tac[]
QED

(* HEADLINE BRIDGE 1 (Transparency): Under the maximal sound policy
   `maxpol step safe`, a cone-certified ReLU neural controller runs with
   ZERO envelope overrides — its enveloped reachable states are identical
   to its bare reachable states (`envelope_transparent_run`). *)
Theorem neural_ctrl_transparent_run:
  !step init safe shield B l0 Ws enc s.
    init_safe init safe /\ cone_safe step safe B ==>
    (reach step init
       (enveloped (maxpol step safe) shield (neural_ctrl B l0 Ws enc)) s <=>
     reach step init (neural_ctrl B l0 Ws enc) s)
Proof
  rpt gen_tac >> strip_tac >>
  `invariant step init (neural_ctrl B l0 Ws enc) safe`
    by metis_tac[neural_ctrl_self_safe] >>
  metis_tac[envelope_transparent_run]
QED

(* HEADLINE BRIDGE 2 (Testimony / Operational Gate): A policy `newp`
   permitting the whole verified cone `[0, B]` is certified sound by
   `cone_safe step safe B`, so volunteering that cone certificate through
   the operational `cgate` (`upgradeTheory.gate`) installs `newp` and
   preserves the envelope guarantee for every inhabitant. *)
Definition cone_policy_def:
  cone_policy (B:int) (s:'s) (a:int) <=> 0 <= a /\ a <= B
End

Theorem cone_policy_sound:
  !step safe B.
    cone_safe step safe B ==> sound_policy step safe (cone_policy B)
Proof
  rw[cone_safe_def, sound_policy_def, cone_policy_def]
QED

Theorem neural_testimony_discharges_gate:
  !step init safe shield oldp B ctrl.
    init_safe init safe /\ safe_shield step safe shield /\
    sound_policy step safe oldp /\
    cone_safe step safe B /\ weaker (cone_policy B) oldp ==>
    gate T oldp (cone_policy B) = cone_policy B /\
    invariant step init
      (enveloped (gate T oldp (cone_policy B)) shield ctrl) safe
Proof
  rpt strip_tac
  >- rw[gate_def]
  >- (irule gate_preserves_safety >> simp[] >>
      rw[admissible_def] >> metis_tac[cone_policy_sound])
QED

val _ = export_theory ();
