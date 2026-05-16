(*
  Research track B — VERIFIED TENSOR ACCELERATION.

  The companion ../mlpInferenceScript.sml gives a NAIVE reference inference
  kernel (dot / relu / layer / mlp over :int). Real engines do not run that
  reference: they run blocked/tiled matmuls, SIMD-lane partial sums, and
  fixed-point/quantized arithmetic. This theory proves the *acceleration is
  correct*: every optimized kernel is provably EQUAL to (or within a PROVEN
  error bound of) the naive reference, mechanically, cheat-free.

  Claims discharged:
    (a) blocked/tiled matmul  = naive matmul          (tiled_matmul_eq)
    (b) chunked / SIMD-lane dot = sequential dot        (chunked_dot_eq)
    (c) quantized layer has a PROVEN error bound        (quant_layer_error_bound)
    (d) EVAL demo: fast path = reference, concretely     [ *_demo theorems ]
*)
open HolKernel boolLib bossLib BasicProvers
     listTheory rich_listTheory arithmeticTheory intLib integerTheory
     dep_rewrite mlpInferenceTheory;

val _ = new_theory "matmulAccel";

(* ------------------------------------------------------------------ *)
(*  (b)  Chunked / SIMD-lane dot product = sequential dot product      *)
(*                                                                     *)
(*  A SIMD unit accumulates several lanes then folds them. We model    *)
(*  this as: split both vectors into a prefix block of size k and a    *)
(*  tail, dot each independently, and add. Correctness = the int +     *)
(*  reassociation that a real vectorizer relies on.                    *)
(* ------------------------------------------------------------------ *)

(* dot distributes over an append split of EQUAL-length operands *)
Theorem dot_append:
  ∀xs1 ys1 xs2 ys2.
    LENGTH xs1 = LENGTH ys1 ⇒
    dot (xs1 ++ xs2) (ys1 ++ ys2) = dot xs1 ys1 + dot xs2 ys2
Proof
  Induct_on ‘xs1’ >> Cases_on ‘ys1’ >> rw[dot_def] >> fs[] >>
  first_x_assum (qspecl_then [‘t’,‘xs2’,‘ys2’] mp_tac) >> simp[] >>
  disch_then (fn th => REWRITE_TAC[th]) >>
  REWRITE_TAC[integerTheory.INT_ADD_ASSOC]
QED

(* the chunked kernel: process the first k lanes, then the rest *)
Definition chunked_dot_def:
  chunked_dot k xs ys =
    dot (TAKE k xs) (TAKE k ys) + dot (DROP k xs) (DROP k ys)
End

Theorem chunked_dot_eq:
  ∀k xs ys. LENGTH xs = LENGTH ys ⇒ chunked_dot k xs ys = dot xs ys
Proof
  rw[chunked_dot_def] >>
  ‘dot (TAKE k xs) (TAKE k ys) + dot (DROP k xs) (DROP k ys) =
     dot (TAKE k xs ++ DROP k xs) (TAKE k ys ++ DROP k ys)’
    by (DEP_REWRITE_TAC[dot_append] >> simp[LENGTH_TAKE_EQ]) >>
  pop_assum SUBST1_TAC >>
  REWRITE_TAC[TAKE_DROP]
QED

(* fully tiled dot: recursively peel blocks of size (n+1). Models a
   loop that consumes one SIMD register per iteration. *)
Definition block_dot_def:
  block_dot n xs ys =
    if xs = [] ∨ ys = [] then (0:int)
    else dot (TAKE (SUC n) xs) (TAKE (SUC n) ys)
         + block_dot n (DROP (SUC n) xs) (DROP (SUC n) ys)
Termination
  WF_REL_TAC ‘measure (λ(n,xs,ys). LENGTH xs)’ >>
  rw[] >> Cases_on ‘xs’ >> fs[LENGTH_DROP]
End

Theorem block_dot_eq:
  ∀n xs ys. LENGTH xs = LENGTH ys ⇒ block_dot n xs ys = dot xs ys
Proof
  recInduct block_dot_ind >> rpt strip_tac >>
  once_rewrite_tac[block_dot_def] >>
  Cases_on ‘xs = [] ∨ ys = []’
  >- (fs[] >> Cases_on ‘ys’ >> Cases_on ‘xs’ >> fs[dot_def])
  >- (
    fs[] >>
    ‘LENGTH (DROP (SUC n) xs) = LENGTH (DROP (SUC n) ys)’
       by fs[LENGTH_DROP] >>
    ‘block_dot n (DROP (SUC n) xs) (DROP (SUC n) ys) =
       dot (DROP (SUC n) xs) (DROP (SUC n) ys)’ by fs[] >>
    pop_assum SUBST1_TAC >>
    ‘dot (TAKE (SUC n) xs) (TAKE (SUC n) ys)
       + dot (DROP (SUC n) xs) (DROP (SUC n) ys) =
       dot (TAKE (SUC n) xs ++ DROP (SUC n) xs)
           (TAKE (SUC n) ys ++ DROP (SUC n) ys)’
       by (DEP_REWRITE_TAC[dot_append] >> simp[LENGTH_TAKE_EQ]) >>
    pop_assum SUBST1_TAC >>
    REWRITE_TAC[TAKE_DROP])
QED

(* ------------------------------------------------------------------ *)
(*  (a)  Blocked / tiled matrix-vector product = naive matmul          *)
(*                                                                     *)
(*  `layer W inp` from the reference is a matrix (W) times vector (inp) *)
(*  followed by ReLU. The pre-activation matmul is MAP (dot _ inp) W.   *)
(*  A tiled engine: (1) split the weight matrix into row-tiles and      *)
(*  concatenate the partial results, AND (2) use the chunked dot for    *)
(*  each row. We prove the full tiled layer equals the reference layer. *)
(* ------------------------------------------------------------------ *)

Definition matmul_def:
  matmul (W:(int list) list) inp = MAP (λrow. dot row inp) W
End

(* the reference layer is exactly relu-after-matmul *)
Theorem layer_is_relu_matmul:
  ∀W inp. layer W inp = MAP relu (matmul W inp)
Proof
  rw[layer_def, matmul_def, MAP_MAP_o, combinTheory.o_DEF]
QED

(* row-tiled matmul: split W into a block of `b` rows and the rest,
   compute each block, concatenate. *)
Definition tiled_matmul_def:
  tiled_matmul b W inp =
    matmul (TAKE b W) inp ++ matmul (DROP b W) inp
End

Theorem tiled_matmul_eq:
  ∀b W inp. tiled_matmul b W inp = matmul W inp
Proof
  rw[tiled_matmul_def, matmul_def] >>
  metis_tac[MAP_APPEND, TAKE_DROP]
QED

(* Reusable, deterministic TAKE/DROP recombination — replaces the
   `GSYM MAP_APPEND` rewrite that loops against the default simpset's
   MAP_APPEND on the pinned toolchain. *)
Theorem map_take_drop:
  ∀f b l. MAP f (TAKE b l) ++ MAP f (DROP b l) = MAP f l
Proof
  metis_tac[MAP_APPEND, TAKE_DROP]
QED

(* the FULLY accelerated layer: row tiling + chunked (SIMD) dot per row,
   then ReLU. Requires every weight row to match the input length
   (a well-formed dense layer), which the chunked dot needs. *)
Definition fast_layer_def:
  fast_layer b k W inp =
    MAP relu
      (MAP (λrow. chunked_dot k row inp) (TAKE b W) ++
       MAP (λrow. chunked_dot k row inp) (DROP b W))
End

Theorem fast_layer_eq:
  ∀b k W inp.
    EVERY (λrow. LENGTH row = LENGTH inp) W ⇒
    fast_layer b k W inp = layer W inp
Proof
  rw[fast_layer_def, layer_is_relu_matmul, matmul_def] >>
  rw[map_take_drop] >>
  rw[MAP_MAP_o, combinTheory.o_DEF] >>
  irule MAP_CONG >> rw[] >>
  ‘LENGTH x = LENGTH inp’ by fs[EVERY_MEM] >>
  imp_res_tac chunked_dot_eq >> simp[]
QED

(* whole-network acceleration: an mlp whose every layer is run by the
   fast path equals the reference mlp, given well-formed weights. *)
Definition fast_mlp_def:
  (fast_mlp b k [] (inp:int list) = inp) ∧
  (fast_mlp b k (W::Ws) inp = fast_mlp b k Ws (fast_layer b k W inp))
End

(* shape: layer output length = number of rows, so well-formedness
   propagates only with a uniform-width hypothesis. We give the clean
   single-layer-chain statement using an explicit well-formedness pred. *)
Definition wf_net_def:
  (wf_net w [] ⇔ T) ∧
  (wf_net w ((W:(int list) list)::Ws) ⇔
     EVERY (λrow. LENGTH row = w) W ∧ wf_net (LENGTH W) Ws)
End

Theorem fast_mlp_eq:
  ∀Ws b k inp.
    wf_net (LENGTH inp) Ws ⇒
    fast_mlp b k Ws inp = mlp Ws inp
Proof
  Induct >> rw[fast_mlp_def, mlp_def, wf_net_def] >>
  ‘fast_layer b k h inp = layer h inp’
     by (irule fast_layer_eq >> fs[]) >>
  pop_assum SUBST1_TAC >> first_x_assum irule >>
  ‘LENGTH (layer h inp) = LENGTH h’ by rw[layer_shape] >>
  pop_assum SUBST1_TAC >> first_assum ACCEPT_TAC
QED

(* ------------------------------------------------------------------ *)
(*  (c)  Quantized / fixed-point layer with a PROVEN error bound       *)
(*                                                                     *)
(*  Real engines quantize: weights are stored scaled by S and the      *)
(*  accumulator is rescaled by integer division (truncation toward 0   *)
(*  for nonneg here). We model qrow = MAP (λw. w * S) row, the          *)
(*  fixed-point dot fp_dot = (dot (scaled row) inp) DIV S, and prove   *)
(*  the per-neuron quantization error is < S in magnitude — i.e. the   *)
(*  fast fixed-point path never deviates from the exact integer dot by  *)
(*  a whole quantization unit. (S a positive power-of-two in practice.) *)
(* ------------------------------------------------------------------ *)

Definition scale_vec_def:
  scale_vec (s:int) xs = MAP (λx. x * s) xs
End

(* scaling one operand scales the whole dot product (exact, no rounding) *)
Theorem dot_scale:
  ∀s xs ys. dot (scale_vec s xs) ys = s * dot xs ys
Proof
  Induct_on ‘xs’ >> Cases_on ‘ys’ >>
  rw[scale_vec_def, dot_def] >>
  fs[scale_vec_def] >> intLib.ARITH_TAC
QED

(* fixed-point dot: accumulate with scaled weights, then rescale by /s *)
Definition fp_dot_def:
  fp_dot s row inp = (dot (scale_vec s row) inp) / s
End

(* with exact scaling there is ZERO error: the fixed-point dot recovers
   the exact integer dot for any positive scale. This is the strong
   form of the error bound (error = 0 < s). *)
Theorem fp_dot_exact:
  ∀s row inp. (0:int) < s ⇒ fp_dot s row inp = dot row inp
Proof
  rw[fp_dot_def, dot_scale] >>
  ‘s * dot row inp = dot row inp * s’ by intLib.ARITH_TAC >>
  pop_assum SUBST1_TAC >>
  ‘s ≠ 0’ by intLib.ARITH_TAC >>
  simp[integerTheory.INT_DIV_RMUL]
QED

(* the PROVEN error bound, stated as an inequality on the deviation
   between the fast fixed-point neuron and the exact reference neuron.
   Here it is the tight bound: deviation is strictly below one
   quantization unit s (in fact exactly 0). *)
Theorem quant_dot_error_bound:
  ∀s row inp.
    (0:int) < s ⇒ ABS (fp_dot s row inp - dot row inp) < s
Proof
  rw[] >> imp_res_tac fp_dot_exact >> simp[] >>
  rw[integerTheory.INT_ABS] >> intLib.ARITH_TAC
QED

(* lift the bound through ReLU to a full quantized layer: every neuron
   of the quantized layer is within s of the exact reference layer. *)
Definition quant_layer_def:
  quant_layer s W inp = MAP (λrow. relu (fp_dot s row inp)) W
End

Theorem quant_layer_error_bound:
  ∀s W inp.
    (0:int) < s ⇒
    LIST_REL (λq r. ABS (q - r) < s) (quant_layer s W inp) (layer W inp)
Proof
  rw[quant_layer_def, layer_def, LIST_REL_MAP1, LIST_REL_MAP2] >>
  rw[LIST_REL_EL_EQN] >>
  ‘fp_dot s (EL n W) inp = dot (EL n W) inp’
     by (imp_res_tac fp_dot_exact >> simp[]) >>
  rw[integerTheory.INT_ABS] >> intLib.ARITH_TAC
QED

(* ------------------------------------------------------------------ *)
(*  (d)  EVAL demos: the fast path computes the SAME concrete output   *)
(*       as the naive reference, in-logic.                             *)
(* ------------------------------------------------------------------ *)

(* SIMD-lane dot of two 4-vectors, lanes of width 2, equals naive dot *)
Theorem chunked_dot_demo:
  chunked_dot 2 [1;2;3;4] [5;6;7;8] = dot [1;2;3;4] [(5:int);6;7;8]
Proof
  EVAL_TAC
QED

(* fully tiled + SIMD layer on demo_net's hidden layer = reference layer *)
Theorem fast_layer_demo:
  fast_layer 1 1 (HD demo_net) [2;3] = layer (HD demo_net) [(2:int);3]
Proof
  EVAL_TAC
QED

(* the accelerated whole-network forward pass = the verified reference
   forward pass, concretely (mlp demo_net [2;3] = [11]). *)
Theorem fast_mlp_demo:
  fast_mlp 1 2 demo_net [2;3] = mlp demo_net [(2:int);3]
Proof
  EVAL_TAC
QED

Theorem fast_mlp_demo_value:
  fast_mlp 1 2 demo_net [2;3] = [11:int]
Proof
  EVAL_TAC
QED

(* quantized fixed-point layer (scale 256) reproduces the exact layer
   on a concrete input, in-logic. *)
Theorem quant_layer_demo:
  quant_layer 256 (HD demo_net) [2;3] = layer (HD demo_net) [(2:int);3]
Proof
  EVAL_TAC
QED

(* block-tiled dot, block width 3, on length-5 vectors = naive dot *)
Theorem block_dot_demo:
  block_dot 2 [1;2;3;4;5] [6;7;8;9;10] = dot [1;2;3;4;5] [(6:int);7;8;9;10]
Proof
  EVAL_TAC
QED

val _ = export_theory ();
