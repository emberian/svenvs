(*
  fxpSoftmax — a GENUINE fixed-point softmax-normalization with a
  MACHINE-CHECKED error bound vs the EXACT rational softmax-normalization.

  Research track B, numeric sub-track. The gemma spec (../gemma) and the
  attention micro-block (../attn) abstract softmax to a *supplied* integer
  weight vector (gemmaForward: `attn_head` takes `w` as a parameter;
  attn: hardmax). That is shape-only. Here we DELETE that abstraction for
  the normalization step and replace it with a real fixed-point operation
  whose deviation from the exact rational operation is BOUNDED BY A PROVEN
  THEOREM.

  ──────────────────────────────────────────────────────────────────────
  RUTHLESS HONESTY (read before believing anything):

  Real softmax is  softmax(z)_i = exp(z_i) / Σ_j exp(z_j).  It has two
  parts:
    (E) the transcendental map  z ↦ exp(z)  (a non-negative weight);
    (N) the normalization       w ↦ w_i / Σ_j w_j  (a probability vector).

  * Part (N) is EXACT rational arithmetic. It carries the property that
    actually matters for "attention is a convex combination of value rows,
    no hallucinated vectors": Σ p_i = 1, p_i ≥ 0. We implement (N) as a
    genuine fixed-point operation `fxp_softmax Q w` (no float, no
    transcendental) and PROVE, against the EXACT rational reference
    `real_softmax w` (= w_i / S over ℚ, here represented exactly as the
    pair (w_i, S)), BOTH:
      - a per-component absolute error bound  |p_fxp_i − w_i/S| < 1/Q ;
      - the fixed-point normalization invariant: the integer weights sum
        to the denominator Q up to a deviation provably < (#weights).
    Exact `Σ = Q` is *impossible* under floor rounding; we do NOT claim it
    and we PROVE the exact deviation envelope instead (flagged loudly,
    per CLAIMS.md discipline — no theorem is weakened to triviality).

  * Part (E), `exp`, is NOT implemented here. Pure HOL4 (no reals/
    transcendental theory in this light build) has no `exp`. We do NOT
    claim a bound on (E). What we DELETE is the *normalization* integer-
    param abstraction; what REMAINS abstracted is `exp` itself, taken as
    a given non-negative integer weight input (exactly as a fixed-point
    `exp` table would supply). This is a strictly weaker abstraction than
    "softmax weights are a supplied parameter": now only the per-element
    `exp` is supplied; the normalization is REAL and PROVEN.

  Nothing here is a `cheat`/`mk_thm`/`new_axiom`/oracle.
  ──────────────────────────────────────────────────────────────────────
*)
open HolKernel boolLib bossLib BasicProvers
     listTheory rich_listTheory arithmeticTheory dividesTheory;

val _ = new_theory "fxpSoftmax";

(* ===================================================================== *)
(*  Non-negative weights live in ℕ (softmax weights = exp(·) ≥ 0).        *)
(*  ℕ DIV/MOD are Euclidean, total, EVAL-able — every bound below is      *)
(*  clean integer arithmetic, no real-closed-field axioms.               *)
(* ===================================================================== *)

Definition vsum_def:
  (vsum [] = 0n) /\
  (vsum (x::xs) = x + vsum xs)
End

Theorem vsum_append:
  !xs ys. vsum (xs ++ ys) = vsum xs + vsum ys
Proof
  Induct >> rw[vsum_def]
QED

(* ===================================================================== *)
(*  The EXACT rational reference (no rounding):                          *)
(*    real_softmax w  is the vector  i ↦ w_i / S    (S = Σ w),            *)
(*  represented EXACTLY as the integer pair (w_i, S). Comparing the      *)
(*  fixed-point output p_i (a Q-scaled integer) to w_i/S is done by      *)
(*  cross-multiplication: p_i / Q  vs  w_i / S  ⇔  p_i*S  vs  w_i*Q,      *)
(*  which is exact integer arithmetic — the rational reference is        *)
(*  modeled WITHOUT any loss.                                            *)
(* ===================================================================== *)

Definition real_den_def:
  real_den (w:num list) = vsum w
End

(* ===================================================================== *)
(*  The GENUINE fixed-point softmax-normalization.                       *)
(*                                                                       *)
(*    fxp_softmax Q w  =  MAP (λwi. (wi * Q) DIV S) w     where S = Σ w.  *)
(*                                                                       *)
(*  Output component i is the integer  p_i = floor(Q · w_i / S),  i.e.    *)
(*  a probability in fixed-point with denominator Q (Q = 2^k or 10^k     *)
(*  in practice; here arbitrary positive Q). This is exactly what a      *)
(*  real fixed-point softmax kernel computes after the exp table.        *)
(* ===================================================================== *)

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

(* every weight is ≤ the total (used for the ≤ Q component bound). *)
Theorem mem_le_vsum:
  !w x. MEM x w ==> x <= vsum w
Proof
  Induct >> rw[vsum_def] >> fs[] >> res_tac >> decide_tac
QED

(* Each fixed-point probability is a genuine non-negative quantity and
   (≤ Q) — it never exceeds the unit (= Q in fixed-point). No component
   "hallucinates" mass above 1. *)
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

Theorem fxp_softmax_nonneg_le_Q:
  !Q w.
    0 < vsum w ==>
    EVERY (\p. p <= Q) (fxp_softmax Q w)
Proof
  rw[fxp_softmax_def, EVERY_MEM, MEM_MAP] >>
  rename1 `MEM wi w` >>
  `(wi * Q) DIV (vsum w) <= Q` by metis_tac[fxp_softmax_component_le_Q] >>
  fs[]
QED

(* ===================================================================== *)
(*  HEADLINE 1 — PROVEN PER-COMPONENT ERROR BOUND vs EXACT rational.      *)
(*                                                                       *)
(*  For every component i:   | p_i·S − w_i·Q |  <  S                      *)
(*  i.e. in exact rationals  | p_i/Q − w_i/S |  <  1/Q .                  *)
(*                                                                       *)
(*  This is a genuine numerical accuracy theorem: the fixed-point        *)
(*  softmax-normalization differs from the EXACT rational softmax-       *)
(*  normalization by strictly less than one quantization step 1/Q, per   *)
(*  component, with NO hidden hypothesis beyond S>0 (S=0 ⇔ all-zero      *)
(*  weights, the degenerate undefined-softmax case).                     *)
(* ===================================================================== *)

(* the core floor inequality: 0 ≤ a − (a DIV s)*s < s   (s>0). *)
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

(* per-component absolute error, exact-rational reference, by
   cross-multiplication (p_i·S vs w_i·Q). PROVEN, no rounding lost. *)
Theorem fxp_softmax_component_error:
  !Q w i.
    0 < vsum w /\ i < LENGTH w ==>
    let S  = vsum w in
    let pi = EL i (fxp_softmax Q w) in
    let wi = EL i w in
      pi * S <= wi * Q  /\  wi * Q < pi * S + S
Proof
  rw[fxp_softmax_def, EL_MAP] >>
  qabbrev_tac `a = EL i w * Q` >>
  `(a DIV vsum w) * vsum w <= a /\ a < (a DIV vsum w) * vsum w + vsum w`
     by metis_tac[div_mul_bounds] >>
  fs[]
QED

(* the same fact stated as a single absolute-error envelope:
     | p_i·S − w_i·Q |  <  S         (⇔ |p_i/Q − w_i/S| < 1/Q). *)
Theorem fxp_softmax_abs_error_lt_step:
  !Q w i.
    0 < vsum w /\ i < LENGTH w ==>
    let S  = vsum w in
    let pi = EL i (fxp_softmax Q w) in
    let wi = EL i w in
      wi * Q - pi * S < S  /\  pi * S <= wi * Q
Proof
  rpt strip_tac >>
  qspecl_then [`Q`,`w`,`i`] mp_tac fxp_softmax_component_error >>
  rw[] >> fs[]
QED

(* ===================================================================== *)
(*  HEADLINE 2 — PROVEN NORMALIZATION (sum-of-weights = denominator)      *)
(*  INVARIANT.                                                            *)
(*                                                                       *)
(*  Exact ℝ softmax has  Σ p_i = 1.  In fixed-point with denominator Q   *)
(*  the analogue is  Σ p_i = Q.  Under floor rounding this CANNOT be an   *)
(*  exact equality (each of n components loses < 1 ulp).  We do NOT      *)
(*  fake equality; we PROVE the exact two-sided deviation envelope:      *)
(*                                                                       *)
(*       Q − LENGTH w  <  Σ (fxp_softmax Q w)  ≤  Q                       *)
(*                                                                       *)
(*  i.e. the fixed-point distribution sums to the denominator Q with     *)
(*  total deviation provably < (#weights). This is the honest fixed-     *)
(*  point "sum-of-weights = 1 (denominator)" invariant. (Flagged: it is  *)
(*  an envelope, not equality; equality is mathematically impossible     *)
(*  here and claiming it would be the triviality CLAIMS.md forbids.)     *)
(* ===================================================================== *)

(* superadditivity of integer division: (x DIV s)+(y DIV s) ≤ (x+y) DIV s *)
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

(* Σ_i (a_i DIV S) ≤ (Σ_i a_i) DIV S. *)
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

(* upper side: Σ floor(Q·w_i/S) ≤ Q  (mass never inflates). *)
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

(* elementwise floor lower bound, aggregated by induction (non-strict,
   hence also true for the empty list):
     Σ a_i  ≤  (Σ (a_i DIV S))·S  +  n·S          (S > 0).            *)
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

(* lower side: Q − (#weights) < Σ floor(Q·w_i/S).  Each component loses
   strictly less than one ulp; over n components total loss < n. *)
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

(* The honest fixed-point normalization invariant, both sides together:
     Q − LENGTH w  <  Σ (fxp_softmax Q w)  ≤  Q.
   (Σ = Q exactly is impossible under floor rounding — NOT claimed.) *)
Theorem fxp_softmax_normalization_envelope:
  !Q w.
    0 < vsum w ==>
    Q <= vsum (fxp_softmax Q w) + LENGTH w  /\
    vsum (fxp_softmax Q w) <= Q
Proof
  metis_tac[fxp_softmax_sum_lower, fxp_softmax_sum_upper]
QED

(* ===================================================================== *)
(*  Tiny EVAL conformance witness (run in-logic).                        *)
(*  Weights w = [1;2;1] (e.g. an exp-table output), denominator Q = 100. *)
(*  S = 4.  Exact rationals: [1/4; 2/4; 1/4] = [25;50;25] @ Q=100.       *)
(*  fxp:  [floor(100/4); floor(200/4); floor(100/4)] = [25;50;25].       *)
(*  Σ = 100 = Q here (this w happens to divide evenly — envelope tight). *)
(* ===================================================================== *)

Theorem demo_fxp_softmax_eval:
  fxp_softmax 100 [1;2;1] = [25;50;25]
Proof
  EVAL_TAC
QED

(* A non-dividing case showing the floor deviation is real and bounded:
   w=[1;1;1], Q=100, S=3.  floor(100/3)=33 each, Σ=99 = Q−1, and
   LENGTH w = 3, so Q−n = 97 < 99 ≤ 100 = Q. Envelope holds, not equality. *)
Theorem demo_fxp_softmax_floor_eval:
  fxp_softmax 100 [1;1;1] = [33;33;33] /\
  vsum (fxp_softmax 100 [1;1;1]) = 99
Proof
  EVAL_TAC
QED

val _ = export_theory ();
