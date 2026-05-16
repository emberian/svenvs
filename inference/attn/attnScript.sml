(*
  Research track B — a TOY *verified* attention micro-block.

  We climb from the verified ReLU MLP (../mlpInferenceScript.sml) toward a
  verified transformer block, at TOY scale and over a TRACTABLE numeric
  domain (integers only — NO real-valued softmax, NO floats).

  The softmax of real attention is replaced by a *hardmax* (argmax)
  abstraction: attention deterministically selects the value row whose key
  row scores highest against the query.  This is the standard "hard
  attention" limit of softmax (temperature -> 0) and lets us prove genuine
  structural correctness mechanically:

    * the output is a value actually PRESENT in V (a convex/one-hot
      selection — no hallucinated vectors);
    * the selected index is the argmax of the score vector;
    * shape correctness for multi-query single-head attention;
    * a residual-skip block  block x = x (+) sublayer x  with shape and a
      structural invariant;
    * an EVAL-runnable concrete tiny attention computation.

  FAITHFULLY captured: the routing/selection structure of attention
  (scores -> argmax -> gather a value), residual skip plumbing, shapes.
  ABSTRACTED away: real softmax weighting (-> hardmax), floating point
  (-> int), learned projections / multi-head mixing, normalisation
  statistics (-> a fixed integer "centering" stand-in).
*)
open HolKernel boolLib bossLib BasicProvers listTheory arithmeticTheory
     rich_listTheory intLib integerTheory;

val _ = new_theory "attn";

(* ------------------------------------------------------------------ *)
(*  Integer dot product (reused shape/idea from mlpInference).         *)
(* ------------------------------------------------------------------ *)

Definition idot_def:
  (idot ([]:int list) (_:int list) = (0:int)) ∧
  (idot (_:int list) ([]:int list) = (0:int)) ∧
  (idot (x::xs) (y::ys) = x * y + idot xs ys)
End

(* ------------------------------------------------------------------ *)
(*  argmax over a non-empty int list: index of a maximal element.     *)
(*  Ties resolved to the FIRST (smallest index) maximal element.      *)
(* ------------------------------------------------------------------ *)

Definition argmax_from_def:
  (argmax_from i best bi ([]:int list) = (bi:num)) ∧
  (argmax_from i best bi (s::ss) =
     if best < s
       then argmax_from (i+1) s i ss
       else argmax_from (i+1) best bi ss)
End

Definition argmax_def:
  (argmax ([]:int list) = 0n) ∧
  (argmax (s::ss) = argmax_from 1 s 0 ss)
End

(* ------------------------------------------------------------------ *)
(*  Scores of a query against every key row.                          *)
(* ------------------------------------------------------------------ *)

Definition scores_def:
  scores (q:int list) (K:(int list) list) = MAP (λk. idot q k) K
End

(* ------------------------------------------------------------------ *)
(*  Single-head HARDMAX attention for one query: pick the V row whose  *)
(*  key scores highest against q.  (softmax temperature -> 0 limit.)   *)
(* ------------------------------------------------------------------ *)

Definition attn1_def:
  attn1 (q:int list) (K:(int list) list) (V:(int list) list) =
    EL (argmax (scores q K)) V
End

(* Multi-query single-head attention: one output row per query. *)
Definition attention_def:
  attention (Q:(int list) list) K V = MAP (λq. attn1 q K V) Q
End

(* ------------------------------------------------------------------ *)
(*  argmax correctness lemmas                                          *)
(* ------------------------------------------------------------------ *)

(* the running best index stays inside the already-seen prefix *)
Theorem argmax_from_lt:
  ∀ss i best bi.
    bi < i ⇒ argmax_from i best bi ss < i + LENGTH ss
Proof
  Induct >> rw[argmax_from_def]
  >- (first_x_assum (qspecl_then [‘i+1’,‘h’,‘i’] mp_tac) >> rw[])
  >- (first_x_assum (qspecl_then [‘i+1’,‘best’,‘bi’] mp_tac) >> rw[])
QED

Theorem argmax_lt_length:
  ∀ss. ss ≠ [] ⇒ argmax ss < LENGTH ss
Proof
  Cases >> rw[argmax_def] >>
  ‘argmax_from 1 h 0 t < 1 + LENGTH t’ by
    (irule argmax_from_lt >> decide_tac) >> fs[]
QED

(* The selected index points at a maximal element.  Invariant: the
   accumulator `acc` (the already-scanned prefix, length i) has its
   running maximum at index bi with value `best`; argmax_from then
   returns an index of (acc ++ ss) dominating every position. *)

(* argmax_from dominates every position of (acc ++ ss), given
   the running best at bi already dominates the whole prefix acc. *)
Theorem argmax_from_dom:
  ∀ss acc i best bi.
    LENGTH acc = i ∧ bi < i ∧ EL bi acc = best ∧
    (∀j. j < i ⇒ EL j acc ≤ best) ⇒
    argmax_from i best bi ss < i + LENGTH ss ∧
    (∀j. j < i + LENGTH ss ⇒
       EL j (acc ++ ss) ≤ EL (argmax_from i best bi ss) (acc ++ ss))
Proof
  Induct
  >- (simp[argmax_from_def] >> rw[] >>
      first_x_assum (qspec_then ‘j’ mp_tac) >> rw[] >>
      simp[EL_APPEND1])
  >- (rpt gen_tac >> strip_tac >>
      simp[Once argmax_from_def] >>
      reverse IF_CASES_TAC
      >- (* ¬(best < h): keep running max at bi *)
         (‘h ≤ best’ by metis_tac[integerTheory.INT_NOT_LT] >>
          first_x_assum (qspecl_then [‘acc ++ [h]’,‘i+1’,‘best’,‘bi’] mp_tac) >>
          impl_tac
          >- (rpt conj_tac
              >- simp[]
              >- decide_tac
              >- simp[EL_APPEND1]
              >- (rpt strip_tac >>
                  ‘j < LENGTH acc ∨ j = LENGTH acc’ by decide_tac
                  >- (‘EL j (acc ++ [h]) = EL j acc’ by simp[EL_APPEND1] >>
                      simp[])
                  >- (‘EL j (acc ++ [h]) = h’ by
                        (‘j = LENGTH acc’ by decide_tac >>
                         simp[EL_APPEND2]) >>
                      simp[]))) >>
          strip_tac >>
          ‘argmax_from i best bi (h::ss) = argmax_from (i+1) best bi ss’
             by simp[Once argmax_from_def] >>
          ‘acc ++ h::ss = acc ++ [h] ++ ss’ by simp[] >>
          fs[ADD1] >> simp[GSYM APPEND_ASSOC])
      >- (* best < h : new running max is h at index i *)
         (first_x_assum (qspecl_then [‘acc ++ [h]’,‘i+1’,‘h’,‘i’] mp_tac) >>
          impl_tac
          >- (rpt conj_tac
              >- simp[]
              >- decide_tac
              >- (‘EL i (acc ++ [h]) = h’ by
                    (‘i = LENGTH acc’ by decide_tac >> simp[EL_APPEND2]) >>
                  simp[])
              >- (rpt strip_tac >>
                  ‘j < LENGTH acc ∨ j = LENGTH acc’ by decide_tac
                  >- (‘EL j (acc ++ [h]) = EL j acc’ by simp[EL_APPEND1] >>
                      ‘j < i’ by decide_tac >>
                      ‘EL j acc ≤ best’ by metis_tac[] >>
                      metis_tac[integerTheory.INT_LT_IMP_LE,
                                integerTheory.INT_LE_TRANS])
                  >- (‘EL j (acc ++ [h]) = h’ by
                        (‘j = LENGTH acc’ by decide_tac >>
                         simp[EL_APPEND2]) >>
                      simp[]))) >>
          strip_tac >>
          ‘argmax_from i best bi (h::ss) = argmax_from (i+1) h i ss’
             by simp[Once argmax_from_def] >>
          ‘acc ++ h::ss = acc ++ [h] ++ ss’ by simp[] >>
          fs[ADD1] >> simp[GSYM APPEND_ASSOC]))
QED

(* Headline argmax correctness: for any non-empty score list ss,
   argmax ss is a valid index and its element is ≥ every element. *)
Theorem argmax_is_max:
  ∀ss. ss ≠ [] ⇒
       argmax ss < LENGTH ss ∧
       (∀j. j < LENGTH ss ⇒ EL j ss ≤ EL (argmax ss) ss)
Proof
  Cases >> strip_tac >> rw[argmax_def]
  >- (irule argmax_lt_length >> simp[])
  >- (qspecl_then [‘t’,‘[h]’,‘1’,‘h’,‘0’] mp_tac argmax_from_dom >>
      impl_tac >- rw[] >>
      strip_tac >>
      ‘h::t = [h] ++ t’ by simp[] >>
      pop_assum (fn th => once_rewrite_tac[th]) >>
      first_x_assum (qspec_then ‘j’ mp_tac) >> simp[])
QED

(* ------------------------------------------------------------------ *)
(*  Attention selection correctness                                    *)
(* ------------------------------------------------------------------ *)

(* scores has exactly one entry per key row *)
Theorem scores_length:
  ∀q K. LENGTH (scores q K) = LENGTH K
Proof
  rw[scores_def]
QED

(* (a) attn1 returns a value actually PRESENT in V (one-hot / convex
       selection: no hallucinated vector), provided V is aligned w/ K. *)
Theorem attn1_picks_a_value:
  ∀q K V.
    K ≠ [] ∧ LENGTH V = LENGTH K ⇒
    MEM (attn1 q K V) V
Proof
  rw[attn1_def] >> irule EL_MEM >>
  ‘scores q K ≠ []’ by (Cases_on ‘K’ >> fs[scores_def]) >>
  ‘argmax (scores q K) < LENGTH (scores q K)’ by
    metis_tac[argmax_is_max] >>
  fs[scores_length]
QED

(* (a') the selected index = argmax of the score vector, and that index
       maximises the query-key score. *)
Theorem attn1_argmax_correct:
  ∀q K V.
    K ≠ [] ⇒
    let i = argmax (scores q K) in
      i < LENGTH K ∧
      (∀j. j < LENGTH K ⇒ idot q (EL j K) ≤ idot q (EL i K)) ∧
      attn1 q K V = EL i V
Proof
  rw[attn1_def]
  >- (‘scores q K ≠ []’ by (Cases_on ‘K’ >> fs[scores_def]) >>
      ‘argmax (scores q K) < LENGTH (scores q K)’ by
        metis_tac[argmax_is_max] >> fs[scores_length])
  >- (‘scores q K ≠ []’ by (Cases_on ‘K’ >> fs[scores_def]) >>
      ‘∀j. j < LENGTH (scores q K) ⇒
           EL j (scores q K) ≤ EL (argmax (scores q K)) (scores q K)’ by
        metis_tac[argmax_is_max] >>
      ‘argmax (scores q K) < LENGTH (scores q K)’ by
        metis_tac[argmax_is_max] >>
      first_x_assum (qspec_then ‘j’ mp_tac) >>
      fs[scores_length, scores_def, EL_MAP])
QED

(* (b) shape correctness: one output row per query. *)
Theorem attention_shape:
  ∀Q K V. LENGTH (attention Q K V) = LENGTH Q
Proof
  rw[attention_def]
QED

(* every attention output row is one of the supplied V rows. *)
Theorem attention_rows_from_V:
  ∀Q K V.
    K ≠ [] ∧ LENGTH V = LENGTH K ⇒
    EVERY (λr. MEM r V) (attention Q K V)
Proof
  rw[attention_def, EVERY_MEM, MEM_MAP, PULL_EXISTS] >>
  metis_tac[attn1_picks_a_value]
QED

(* structural: permuting the queries permutes the output identically. *)
Theorem attention_query_map:
  ∀f Q K V.
    attention (MAP f Q) K V = MAP (λq. attn1 (f q) K V) Q
Proof
  rw[attention_def, MAP_MAP_o, combinTheory.o_DEF]
QED

(* ------------------------------------------------------------------ *)
(*  Residual + (layernorm-ish) skip BLOCK                              *)
(*                                                                     *)
(*  Real transformer block: x |-> LN(x + Sublayer(x)).  We keep the    *)
(*  residual skip exactly, and use a TRACTABLE integer "centering"     *)
(*  stand-in for layernorm: subtract the integer mean (rounded toward  *)
(*  zero) of the vector.  This preserves the structural invariant we   *)
(*  prove (length) and the key residual-plumbing property; it does NOT *)
(*  model variance normalisation (honestly abstracted).                *)
(* ------------------------------------------------------------------ *)

Definition vadd_def:
  (vadd ([]:int list) (_:int list) = []) ∧
  (vadd (_:int list) ([]:int list) = []) ∧
  (vadd (x::xs) (y::ys) = (x + y) :: vadd xs ys)
End

Theorem vadd_length:
  ∀xs ys. LENGTH (vadd xs ys) = MIN (LENGTH xs) (LENGTH ys)
Proof
  Induct >> rw[vadd_def] >> Cases_on ‘ys’ >> rw[vadd_def, MIN_DEF]
QED

(* integer "centering": subtract sum-div-length (toward zero). *)
Definition isum_def:
  (isum ([]:int list) = (0:int)) ∧
  (isum (x::xs) = x + isum xs)
End

Definition center_def:
  center (v:int list) =
    let n = &(LENGTH v) in
      if n = 0 then v else MAP (λx. x - isum v / n) v
End

Theorem center_length:
  ∀v. LENGTH (center v) = LENGTH v
Proof
  rw[center_def]
QED

(* A transformer-style block: residual skip then centering. *)
Definition block_def:
  block (sublayer:int list -> int list) (x:int list) =
    center (vadd x (sublayer x))
End

(* (d) block shape invariant: when the sublayer preserves dimension,
       so does the whole residual+center block. *)
Theorem block_shape:
  ∀sublayer x.
    LENGTH (sublayer x) = LENGTH x ⇒
    LENGTH (block sublayer x) = LENGTH x
Proof
  rw[block_def, center_length, vadd_length, MIN_DEF]
QED

(* structural residual property: a ZERO sublayer leaves the (centered)
   input — i.e. the skip connection genuinely carries x through. *)
Theorem vadd_nil_r:
  ∀xs. vadd xs (MAP (K (0:int)) xs) = xs
Proof
  Induct >> rw[vadd_def] >> Cases_on ‘xs’ >> fs[vadd_def]
QED

Theorem block_zero_sublayer:
  ∀x. block (λx. MAP (K (0:int)) x) x = center x
Proof
  rw[block_def, vadd_nil_r]
QED

(* Compose: a single-query attention sublayer fed into the block. *)
Definition attn_block_def:
  attn_block K V (x:int list) =
    block (λq. attn1 q K V) x
End

(* (e) end-to-end shape: attention rows aligned to query width make the
       attention block dimension-preserving. *)
Theorem attn_block_shape:
  ∀K V x.
    LENGTH (attn1 x K V) = LENGTH x ⇒
    LENGTH (attn_block K V x) = LENGTH x
Proof
  rw[attn_block_def] >> irule block_shape >> rw[]
QED

(* ------------------------------------------------------------------ *)
(*  Runnable verified attention: concrete tiny computations in-logic.  *)
(* ------------------------------------------------------------------ *)

(* Keys: 3 rows in R^2.  Query [1;0] aligns best with key row 1
   (idot [1;0] [2;0] = 2 is the max), so attention returns V row 1. *)
Definition demo_K_def:
  demo_K : (int list) list = [ [1; 1]; [2; 0]; [0; 3] ]
End

Definition demo_V_def:
  demo_V : (int list) list = [ [10; 0]; [20; 5]; [0; 30] ]
End

Theorem demo_scores_eval:
  scores [1; 0] demo_K = [1; 2; 0] : int list
Proof
  EVAL_TAC
QED

Theorem demo_argmax_eval:
  argmax (scores [1; 0] demo_K) = 1
Proof
  EVAL_TAC
QED

Theorem demo_attn1_eval:
  attn1 [1; 0] demo_K demo_V = [20; 5] : int list
Proof
  EVAL_TAC
QED

(* multi-query: q0 favours key 1, q1=[0;1] favours key 2 (score 3). *)
Theorem demo_attention_eval:
  attention [[1; 0]; [0; 1]] demo_K demo_V = [[20; 5]; [0; 30]] : int list list
Proof
  EVAL_TAC
QED

(* tie-break to the FIRST maximal index: [0;1] both score the same -> idx 0. *)
Theorem demo_argmax_tie_eval:
  argmax [5; 5; 5 : int] = 0
Proof
  EVAL_TAC
QED

(* residual+center block on a concrete vector, computed in-logic. *)
Theorem demo_block_eval:
  block (λq. attn1 q demo_K demo_V) [1; 0] = [8; -8] : int list
Proof
  EVAL_TAC
QED

val _ = export_theory ();
