# inference/numeric — exactly what is PROVED vs still ABSTRACTED

Skeptic-facing scope ledger for `fxpSoftmaxScript.sml`, same honesty
discipline as the repo-root `CLAIMS.md`. Zero `cheat`/`mk_thm`/
`new_axiom`/oracle steps; the theory builds in light HOL4 in ~1 s.

This directory exists to **delete one shape-only integer-param
abstraction** from `../gemma` (softmax-as-supplied-weight-vector) and
replace it with a **genuine fixed-point operation carrying a machine-
checked error bound vs the EXACT rational reference operation**.

## What softmax is, split honestly

`softmax(z)_i = exp(z_i) / Σ_j exp(z_j)` decomposes into:

- **(E)** the transcendental `z ↦ exp(z)` (a non-negative weight);
- **(N)** the normalization `w ↦ w_i / Σ_j w_j` (a probability vector).

## PROVED (machine-checked HOL4 theorems, unconditional up to `0 < Σw`)

`fxp_softmax Q w = MAP (λwi. (wi*Q) DIV (Σw)) w` is a real fixed-point
implementation of **(N)** with denominator `Q` (no float, no `exp`).

| Property | Theorem |
|----------|---------|
| Shape preserved | `fxp_softmax_shape` |
| Every component ≤ Q (no component exceeds the fixed-point unit; no mass "hallucinated" above 1) | `fxp_softmax_component_le_Q`, `fxp_softmax_nonneg_le_Q` |
| **Per-component error bound vs the EXACT rational softmax-normalization**: `pᵢ·S ≤ wᵢ·Q < pᵢ·S + S`, i.e. `\|pᵢ/Q − wᵢ/S\| < 1/Q` (strictly less than one quantization step, per component) | `fxp_softmax_component_error`, `fxp_softmax_abs_error_lt_step` |
| **Fixed-point normalization (sum-of-weights = denominator) invariant**: `Q − LENGTH w  <  Σ(fxp_softmax Q w)  ≤  Q` — the fixed-point distribution sums to the denominator `Q` with total deviation provably `< (#weights)` | `fxp_softmax_sum_upper`, `fxp_softmax_sum_lower`, `fxp_softmax_normalization_envelope` |
| Supporting exact integer-division facts | `div_mul_bounds`, `div_add_superadd`, `vsum_div_le`, `vsum_div_lower`, `vsum_map_mul`, `mem_le_vsum`, `vsum_append` |
| Concrete EVAL witnesses (run in-logic) | `demo_fxp_softmax_eval` (`[1;2;1]@Q=100 → [25;50;25]`, exact), `demo_fxp_softmax_floor_eval` (`[1;1;1]@Q=100 → [33;33;33]`, Σ=99: the floor deviation is real and inside the proven envelope) |

The error bound is against the **EXACT** rational reference — modeled
losslessly by cross-multiplication (`pᵢ·S` vs `wᵢ·Q`), no real-closed-
field axioms, no `exp`. This is a genuine numerical-accuracy theorem,
not a shape statement.

## ABSTRACTED — stated loudly, never hidden

- **(E) `exp` is NOT implemented here.** Pure light HOL4 has no `exp`.
  The non-negative weight vector `w` (the per-element `exp` values, or
  any non-negative scores) is taken as a **given input**, exactly as a
  fixed-point `exp` table would supply it. We prove **nothing** about
  the accuracy of `exp` itself. This is strictly *weaker* than the
  `../gemma` abstraction "softmax weights are a supplied parameter":
  there the whole softmax was supplied; here only the per-element `exp`
  is supplied and **the normalization (N) is real and proven**.

- **Exact `Σ = Q` is mathematically impossible** under floor rounding
  and is **NOT claimed**. Claiming it would be the triviality the
  honesty discipline forbids. We prove the exact two-sided deviation
  envelope instead (`Q − n < Σ ≤ Q`), which is the honest, non-trivial
  invariant. `demo_fxp_softmax_floor_eval` exhibits a real Σ=99≠100=Q
  case inside the proven envelope.

## NOT CLAIMED

- A bit-exact f32/bf16 softmax result.
- Any bound involving the transcendental `exp`.
- That this is wired into the `../gemma` `attn_head` yet (the parameter
  there is `∀`-quantified; instantiating it with `fxp_softmax`-produced
  weights is a one-line substitution but the *end-to-end* conformance
  run against `catgrad gemma4.rs` remains the documented next step in
  `../gemma/conformance/README.md`). What is delivered here is the
  proven fixed-point op + its proven error bound — the load-bearing
  numerical content the gemma abstraction was missing.
