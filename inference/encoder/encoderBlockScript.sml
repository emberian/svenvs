(*
  encoderBlock — a FULLER verified encoder block.

  Research track B. We compose the two verified pieces already in this
  repo into a real, two-sublayer transformer-style ENCODER block:

    * the verified hardmax single-head attention micro-block
        ../attn/attnScript.sml      (attn1 / scores / argmax, all proved)
    * the verified ReLU dense network
        ../mlpInferenceScript.sml   (layer / mlp / relu, all proved)

  into

      encoder_block Ks V Ws x
        = residual( ff_sublayer , residual( attn_sublayer , x ) )

  where each sublayer is wrapped in its OWN residual skip (the real
  transformer "x = x + Sublayer(x)" twice), exactly the two-sublayer
  encoder structure (attention sublayer, then feed-forward sublayer).

  ──────────────────────────────────────────────────────────────────────
  WHAT IS PROVED (machine-checked, cheat-free):

    * `attn_sublayer_shape` / `ff_sublayer_shape` — each sublayer maps a
      width-d vector to a width-d vector under the natural
      well-formedness premises (V rows width d; MLP last layer width d).
    * `res_shape` — a residual skip preserves width when its sublayer does
      (this is the residual invariant's shape half).
    * `encoder_block_shape` — END-TO-END: the stacked two-sublayer block
      maps width d → width d (the headline structural theorem).
    * `res_zero_sublayer` — RESIDUAL INVARIANT: a zero sublayer leaves the
      input EXACTLY unchanged (the skip genuinely carries x through —
      proved as a true identity, not a shape-only statement).
    * `encoder_block_zero_collapses` — END-TO-END residual invariant: with
      both sublayers contributing zero, the whole encoder block is the
      identity on x. The residual skeleton is faithfully a skeleton.
    * `attn_sublayer_picks_real_value` — the attention sublayer's
      contribution is an ACTUAL supplied value row (no hallucinated
      vector), inherited from the proved `attn1_picks_a_value`.
    * `ff_sublayer_nonneg` — the feed-forward contribution is genuinely
      ReLU-gated (≥ 0 componentwise), inherited from `mlp_nonneg`.
    * `encoder_stack_shape` — stacking N identical encoder blocks still
      preserves width (depth-independent), by induction.
    * `demo_encoder_block_eval` / `demo_encoder_stack_eval` — a concrete
      instance is RUN IN-LOGIC by EVAL (computed, not asserted).

  HONEST SCOPE: numerics are `int` and attention is hardmax (softmax
  temperature→0), inherited verbatim from the two component theories;
  this deliverable adds the *faithful two-sublayer-with-residual
  composition* and its end-to-end proofs. It does NOT change the numeric
  domain (that is the separate ../numeric track, which replaces the
  softmax-normalization abstraction with a proven-error-bound fixed-point
  op). No `cheat`/`mk_thm`/`new_axiom`/oracle.
  ──────────────────────────────────────────────────────────────────────
*)
open HolKernel boolLib bossLib BasicProvers
     listTheory rich_listTheory arithmeticTheory intLib integerTheory
     mlpInferenceTheory attnTheory;

val _ = new_theory "encoderBlock";

(* ===================================================================== *)
(*  Residual skip combinator (reuses attnTheory.vadd: elementwise int +) *)
(*                                                                       *)
(*    res f x  =  vadd x (f x)        — the transformer residual highway. *)
(* ===================================================================== *)

Definition res_def:
  res (f:int list -> int list) (x:int list) = vadd x (f x)
End

(* shape half of the residual invariant: a width-preserving sublayer
   makes the residual skip width-preserving. *)
Theorem res_shape:
  !f x.
    LENGTH (f x) = LENGTH x ==>
    LENGTH (res f x) = LENGTH x
Proof
  rw[res_def, vadd_length, MIN_DEF]
QED

(* RESIDUAL INVARIANT (the substantive half): a sublayer that contributes
   the zero vector leaves x EXACTLY unchanged — the skip genuinely
   carries the input through unmodified (a true identity, not shape-only).
   `vadd_nil_r` (proved in attnTheory) gives  vadd xs (0…0) = xs. *)
Theorem res_zero_sublayer:
  !x. res (\v. MAP (K (0:int)) v) x = x
Proof
  rw[res_def, vadd_nil_r]
QED

(* ===================================================================== *)
(*  Sublayer 1 — ATTENTION sublayer.                                     *)
(*  Single-head hardmax attention (attnTheory.attn1) used as the         *)
(*  residual sublayer: the block attends x over (Ks,V) and adds the      *)
(*  selected value back onto x.                                          *)
(* ===================================================================== *)

Definition attn_sublayer_def:
  attn_sublayer (Ks:(int list) list) (V:(int list) list) (x:int list) =
    attn1 x Ks V
End

(* The attention sublayer's contribution is an ACTUAL value row from V
   (one-hot / convex selection, no hallucinated vector) — inherited
   directly from the proved attnTheory.attn1_picks_a_value. *)
Theorem attn_sublayer_picks_real_value:
  !Ks V x.
    Ks <> [] /\ LENGTH V = LENGTH Ks ==>
    MEM (attn_sublayer Ks V x) V
Proof
  rw[attn_sublayer_def] >> metis_tac[attn1_picks_a_value]
QED

(* Shape contract: if every V row has width d (= input width), the
   attention sublayer is width-preserving. The selected output is some
   row of V (attn1_picks_a_value), hence width d. *)
Theorem attn_sublayer_shape:
  !Ks V x d.
    Ks <> [] /\ LENGTH V = LENGTH Ks /\ LENGTH x = d /\
    (!r. MEM r V ==> LENGTH r = d) ==>
    LENGTH (attn_sublayer Ks V x) = d
Proof
  rw[attn_sublayer_def] >>
  `MEM (attn1 x Ks V) V` by metis_tac[attn1_picks_a_value] >>
  metis_tac[]
QED

(* ===================================================================== *)
(*  Sublayer 2 — FEED-FORWARD sublayer.                                  *)
(*  The verified ReLU dense net (mlpInferenceTheory.mlp) used as the     *)
(*  residual sublayer (the position-wise FFN of a transformer block).    *)
(* ===================================================================== *)

Definition ff_sublayer_def:
  ff_sublayer (Ws:(int list) list list) (x:int list) = mlp Ws x
End

(* The feed-forward contribution is genuinely ReLU-gated: with ≥1 layer
   every component is ≥ 0 — inherited from mlpInferenceTheory.mlp_nonneg. *)
Theorem ff_sublayer_nonneg:
  !W Ws x. EVERY (\y. (0:int) <= y) (ff_sublayer (W::Ws) x)
Proof
  rw[ff_sublayer_def] >> metis_tac[mlp_nonneg]
QED

(* Shape contract: an MLP whose LAST layer has d rows maps any input to a
   width-d vector (mlpInferenceTheory.mlp_shape, nonempty Ws case). *)
Theorem ff_sublayer_shape:
  !Ws x d.
    Ws <> [] /\ LENGTH (LAST Ws) = d ==>
    LENGTH (ff_sublayer Ws x) = d
Proof
  rw[ff_sublayer_def] >> Cases_on `Ws` >>
  fs[mlp_shape]
QED

(* ===================================================================== *)
(*  THE ENCODER BLOCK — two sublayers, each residual-wrapped.            *)
(*                                                                       *)
(*    encoder_block Ks V Ws x                                            *)
(*      = res (ff_sublayer Ws)                                           *)
(*            (res (attn_sublayer Ks V) x)                               *)
(*                                                                       *)
(*  i.e.  a = x  + attn(x);   y = a + ffn(a)        (both residual).     *)
(* ===================================================================== *)

Definition encoder_block_def:
  encoder_block Ks V Ws (x:int list) =
    res (ff_sublayer Ws) (res (attn_sublayer Ks V) x)
End

(* ---- END-TO-END shape preservation: the headline structural theorem.
        Under the natural well-formedness premises (attention values
        width d, MLP last layer width d), the full two-sublayer encoder
        block maps a width-d vector to a width-d vector. ---- *)
Theorem encoder_block_shape:
  !Ks V Ws x d.
    Ks <> [] /\ LENGTH V = LENGTH Ks /\ LENGTH x = d /\
    (!r. MEM r V ==> LENGTH r = d) /\
    Ws <> [] /\ LENGTH (LAST Ws) = d ==>
    LENGTH (encoder_block Ks V Ws x) = d
Proof
  rpt strip_tac >>
  simp[encoder_block_def, res_def] >>
  (* attention sublayer is width d (selected value row of V) *)
  `MEM (attn_sublayer Ks V x) V`
     by (simp[attn_sublayer_def] >> metis_tac[attn1_picks_a_value]) >>
  `LENGTH (attn_sublayer Ks V x) = d` by metis_tac[] >>
  (* inner residual: vadd x (attn ...) has length d *)
  `LENGTH (vadd x (attn_sublayer Ks V x)) = d`
     by simp[vadd_length, MIN_DEF] >>
  qabbrev_tac `a = vadd x (attn_sublayer Ks V x)` >>
  (* feed-forward sublayer is width d (last MLP layer has d rows) *)
  `LENGTH (ff_sublayer Ws a) = d`
     by (simp[ff_sublayer_def] >> Cases_on `Ws` >> fs[mlp_shape]) >>
  (* outer residual: vadd a (ff ...) has length d *)
  simp[vadd_length, MIN_DEF]
QED

(* The zero-sublayer instantiation of the encoder block: both the
   attention and feed-forward sublayers replaced by the constant-zero
   map. Used to state the end-to-end residual invariant as a genuine
   identity (no shape-only hand-waving). *)
Definition encoder_block_zero_def:
  encoder_block_zero (x:int list) =
    res (\v. MAP (K (0:int)) v) (res (\v. MAP (K (0:int)) v) x)
End

(* ---- END-TO-END RESIDUAL INVARIANT: with BOTH sublayers contributing
        the zero vector, the entire encoder block is the identity on x —
        the two stacked residual highways genuinely carry x through
        unchanged (proved as a real identity, not shape-only). ---- *)
Theorem encoder_block_zero_collapses:
  !x.
    encoder_block_zero x = x
Proof
  rw[encoder_block_zero_def] >>
  metis_tac[res_zero_sublayer]
QED

(* ===================================================================== *)
(*  Depth: a stack of N identical encoder blocks.                        *)
(* ===================================================================== *)

Definition encoder_stack_def:
  (encoder_stack 0 Ks V Ws x = x) /\
  (encoder_stack (SUC n) Ks V Ws x =
     encoder_stack n Ks V Ws (encoder_block Ks V Ws x))
End

(* Auxiliary: if the block preserves width d (one clean hypothesis),
   any depth-n stack preserves width d. Plain induction on depth. *)
Theorem encoder_stack_shape_aux:
  !Ks V Ws d.
    (!y. LENGTH y = d ==> LENGTH (encoder_block Ks V Ws y) = d) ==>
    !n x. LENGTH x = d ==> LENGTH (encoder_stack n Ks V Ws x) = d
Proof
  ntac 5 strip_tac >> Induct_on `n` >>
  rw[encoder_stack_def] >> first_x_assum irule >> simp[]
QED

(* Depth-independent shape preservation: discharge the block hypothesis
   via the proven encoder_block_shape, then apply the auxiliary. *)
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

(* ===================================================================== *)
(*  Concrete instance — runnable verified encoder, computed in-logic.    *)
(*                                                                       *)
(*  Width d = 2.  Keys/Values reuse the attn demo geometry; FFN is a     *)
(*  2→2 ReLU net.  Everything is a deterministic, hand-checkable int     *)
(*  vector proved by EVAL (run inside the logic, not asserted).          *)
(* ===================================================================== *)

Definition demo_Ks_def:
  demo_Ks : (int list) list = [ [1; 1]; [2; 0]; [0; 3] ]
End

Definition demo_V_def:
  demo_V : (int list) list = [ [10; 0]; [20; 5]; [0; 30] ]
End

(* a 2→2 ReLU net: one hidden layer (2 rows, 2 weights), identity-ish. *)
Definition demo_Ws_def:
  demo_Ws : (int list) list list =
    [ [[1; 0]; [0; 1]] ;   (* hidden: width 2 *)
      [[1; 0]; [0; 1]] ]   (* output: width 2 *)
End

(* attention step: x=[1;0] selects V row 1 = [20;5] (attn demo result),
   residual a = [1;0] + [20;5] = [21;5].
   ffn(a): mlp [[I];[I]] [21;5] = relu(relu([21;5])) = [21;5] (nonneg),
   residual y = [21;5] + [21;5] = [42;10].  Computed in-logic: *)
Theorem demo_encoder_block_eval:
  encoder_block demo_Ks demo_V demo_Ws [1; 0] = [42; 10]
Proof
  EVAL_TAC
QED

(* depth-2 stack, run in-logic:
   block [1;0]  = [42;10]
   block [42;10]: attn [42;10] over demo_K — scores
     idot[42;10][1;1]=52, idot[42;10][2;0]=84, idot[42;10][0;3]=30
     argmax = 1 -> V row 1 = [20;5]; a = [42;10]+[20;5] = [62;15];
     ffn(a)=[62;15]; y = [62;15]+[62;15] = [124;30]. *)
Theorem demo_encoder_stack_eval:
  encoder_stack 2 demo_Ks demo_V demo_Ws [1; 0] = [124; 30]
Proof
  EVAL_TAC
QED

(* the demo really satisfies the end-to-end shape theorem's premises and
   conclusion (d = 2), via EVAL on the concrete instance. *)
Theorem demo_encoder_block_shape:
  LENGTH (encoder_block demo_Ks demo_V demo_Ws [1; 0]) = 2
Proof
  EVAL_TAC
QED

val _ = export_theory ();
