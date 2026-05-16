(*
  Research track B — a TOY *verified* inference kernel.

  A ReLU dense network over integers, forward pass proved correct in HOL4
  (structural correctness + shape + an EVAL-runnable concrete net). The seed
  of "verified inference": NOT Gemma-scale, but a real mechanically-checked
  tensor computation. Substrate arc: this (or a catgrad-style compositional
  representation) compiled by verified PureCake → CakeML, checked by Candle.
*)
open HolKernel boolLib bossLib BasicProvers listTheory intLib integerTheory;

val _ = new_theory "mlpInference";

Definition dot_def:
  (dot ([]:int list) (_:int list) = (0:int)) ∧
  (dot (_:int list) ([]:int list) = (0:int)) ∧
  (dot (x::xs) (y::ys) = x * y + dot xs ys)
End

Definition relu_def:
  relu (x:int) = if x < 0 then 0 else x
End

Definition layer_def:
  layer (W:(int list) list) (inp:int list) = MAP (λrow. relu (dot row inp)) W
End

Definition mlp_def:
  (mlp [] (inp:int list) = inp) ∧
  (mlp (W::Ws) inp = mlp Ws (layer W inp))
End

(* --- structural correctness, mechanically proved --- *)

Theorem relu_nonneg:
  ∀x. (0:int) ≤ relu x
Proof
  rw[relu_def] >> intLib.ARITH_TAC
QED

Theorem layer_nonneg:
  ∀W inp. EVERY (λy. (0:int) ≤ y) (layer W inp)
Proof
  rw[layer_def, EVERY_MEM, MEM_MAP, PULL_EXISTS] >> metis_tac[relu_nonneg]
QED

Theorem layer_shape:
  ∀W inp. LENGTH (layer W inp) = LENGTH W
Proof
  rw[layer_def]
QED

Theorem mlp_shape:
  ∀Ws inp.
    LENGTH (mlp Ws inp) =
      (case Ws of [] => LENGTH inp | _ => LENGTH (LAST Ws))
Proof
  Induct >> rw[mlp_def] >> Cases_on ‘Ws’ >> fs[mlp_def, layer_shape]
QED

(* the forward pass preserves non-negativity *)
Theorem mlp_pres_nonneg:
  ∀Ws inp. EVERY (λy. (0:int) ≤ y) inp ⇒ EVERY (λy. (0:int) ≤ y) (mlp Ws inp)
Proof
  Induct >> rw[mlp_def] >> first_x_assum irule >>
  rw[layer_def, EVERY_MEM, MEM_MAP, PULL_EXISTS] >> metis_tac[relu_nonneg]
QED

(* with ≥1 layer, every output is a non-negative (ReLU'd) activation *)
Theorem mlp_nonneg:
  ∀Ws W inp. EVERY (λy. (0:int) ≤ y) (mlp (W::Ws) inp)
Proof
  rw[mlp_def] >> irule mlp_pres_nonneg >> metis_tac[layer_nonneg]
QED

(* --- runnable verified inference: a concrete net, computed in-logic --- *)

Definition demo_net_def:
  demo_net : (int list) list list =
    [ [[1; 2]; [-1; 1]] ;   (* hidden: 2 rows, 2 weights *)
      [[1; 3]] ]            (* output: 1 row, 2 weights  *)
End

Theorem demo_forward_eval:
  mlp demo_net [2; 3] = [11:int]
Proof
  EVAL_TAC
QED

(* a negative pre-activation is genuinely clamped by ReLU in the net *)
Theorem demo_relu_clamps:
  layer (HD demo_net) [(-5):int; 1] = [0; 6]
Proof
  EVAL_TAC
QED

val _ = export_theory ();
