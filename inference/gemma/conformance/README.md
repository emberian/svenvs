# gemma-4-e2b forward pass — conformance harness

A skeptic-facing note on **exactly what `../gemmaForwardScript.sml` proves**
and what it deliberately does not. Same honesty discipline as the
repo-root `CLAIMS.md`: every line is either a machine-checked HOL4 theorem
(**PROVED**), an explicit labeled abstraction (**ABSTRACTED**), or
not-yet-wired scaffolding (**GAP**). There are **zero `cheat`/`mk_thm`/
`new_axiom`/oracle steps** in the theory — verified two ways:

1. source scan
   `grep -rnE '(^|[[:space:]>(])cheat([[:space:]]|$|\))' ../gemmaForwardScript.sml`
   is empty; no `mk_thm`/`mk_oracle_thm`/`new_axiom`;
2. every one of the 37 theorems in the built `gemmaForwardTheory`
   carries **only the `DISK_THM` tag** (no oracle tag) — checked by
   inspecting `Thm.tag` on `DB.theorems "gemmaForward"`.

`cd .. && ~/dev/HOL/bin/Holmake` rebuilds the whole theory in ~4 s, pure
light HOL4 (no CakeML / hol-reflection / Candle).

---

## 1. What is PROVED (machine-checked, unconditional up to stated premises)

The HOL4 definitions re-derive the gemma-4 dense text forward pass from
scratch, op-by-op, following `catgrad gemma4.rs` (architecture oracle) with
mistral.rs `GEMMA4.md` corroboration — see `../DESIGN.md` for the 1:1 op
correspondence table. The theorems establish **structural / dataflow
correctness over `int`**:

| Property | Theorem(s) |
|----------|------------|
| Every primitive op preserves the expected shape | `matvec_shape`, `linear_shape`, `rmsnorm_shape`, `rmsnorm_raw_shape`, `rmsnorm_gemma_shape`, `hadamard_shape`, `vadd_shape`, `mlp_shape`, `attn_scores_shape`, `repeat_kv_shape`, `rotate_half_shape`, `apply_rope_shape`, `embed_shape` |
| The full double-norm decoder block maps hidden→hidden (length preserved) under the natural well-formedness premises | `gemma_layer_shape` |
| The stacked model output length = `vocab_size` (= #rows of `lm_head`), for **any** depth `n` and any shape-preserving block | `gemma_stack_shape`, `gemma_forward_shape` |
| GQA head grouping is the real `repeat_interleave` combinatorics (Q-head `q` reads KV-head `q DIV rep`) | `repeat_kv_grouping`, `el_flat_replicate` |
| Structural skeleton sanity: zeroed sublayers + identity norms ⇒ residual highway is a true identity skeleton | `residual_identity`, `residual_comm_len`, `vadd_repl_zero`, `gemma_layer_residual_skeleton` |
| RMSNorm with unit scale/γ is the identity; gate is a genuine non-negative gate; RoPE at position 0 is the identity (matches the real model) | `rmsnorm_identity`, `map2_repl_one`, `mlp_gate_nonneg`, `gelu_i_nonneg`, `apply_rope_pos0_identity` |
| The tiny concrete instance **computes in-logic** (deterministic, hand-checkable) | `toy_block_eval`, `toy_gemma_forward_eval`, `toy_gemma_forward_shape`, `toy_rope_eval`, `toy_gqa_eval`, `gemma_stack_compute` |

The `toy_*_eval` theorems are `EVAL_TAC` — the spec is *run inside the
logic* and the output equality is proved, not asserted. Worked example
(`toy_gemma_forward_eval`, 2 blocks, identity final-norm, 3×4 `lm_head`):

```
toy_block [1;2;0;3]  = [2;6;0;12]      (block = x + x*x for nonneg x)
toy_block [2;6;0;12] = [6;42;0;156]
rmsnorm 1 [1;1;1;1]  = identity        -> h = [6;42;0;156]
matvec lm_head h     = [ r0.h ; r1.h ; r2.h ]
                     = [ 6 ; 42 ; 6+42+0+156 ] = [6;42;204]
```

> **Correction made while completing the build.** The expected value of
> `toy_gemma_forward_eval` was originally written `[6;42;96]`; that is an
> arithmetic error (the third logit is `r2 · h = 6+42+0+156 = 204`, not
> 96). The theorem now states the **EVAL-true value `[6;42;204]`** and is
> proved by `EVAL_TAC`. No theorem was weakened to triviality; this is the
> genuine in-logic computation. (`toy_block_eval = [2;6;0;12]`,
> `toy_rope_eval`, `toy_gqa_eval = [10;10;10;20;20;20]`, and
> `toy_gemma_forward_shape = 3` were already correct.)

## 2. "Verified inference" — precise scope

This is **shape + dataflow correctness of a faithful reference
specification** against the catgrad/mistral.rs gemma-4 architecture, under
the abstractions in §3. It is explicitly **NOT** a bit-exact float gemma-4
proof, **NOT** a proof on the real ~4 B-parameter weights, and **NOT** an
IEEE bf16/f32 semantics result. "Verified inference" here means: *the
op graph, its composition order, and every tensor shape through the full
embed → N×(double-norm decoder block) → final-norm → lm_head pipeline are
machine-checked to match the reference, and the pipeline provably computes
in-logic on a concrete instance.*

## 3. ABSTRACTED — explicit, labeled, literature-standard substitutions

Each is a deliberate modeling choice, stated in the source and in
`../DESIGN.md §3`, never a hidden `cheat`. The *dataflow* around each is
exact; only the named scalar/elementwise numeric is abstracted:

| Real gemma-4 | Spec abstraction | Why faithful for *structural* correctness |
|--------------|------------------|-------------------------------------------|
| f32/bf16 activations | `int` | shapes & dataflow are numeric-domain-independent; that is exactly the proved property |
| `1/sqrt(mean x²+ε)` RMS scalar | integer parameter `s` (caller-supplied) | isolates the only transcendental into one named input; the per-vector reduction + elementwise γ scale + length preservation are exact |
| tanh-approx GeLU | `gelu_i = max(0,·)` | same monotone non-negative gating role; the gate⊙up→down dataflow is exact (`mlp_gate_nonneg`) |
| softmax over scores | integer weight vector `w` parameter | the weighted-sum-of-values dataflow is exact; the softmax weights are *supplied*, not computed |
| cos/sin RoPE tables (trig) | integer parameter vectors | `rotate_half` + `cos⊙x + sin⊙rot` dataflow exact (`apply_rope_pos0_identity`); tables are supplied |
| token embedding lookup | `embed table scale tok` over a given table; tokenizer not modeled | embedding row-lookup + scale shape proved (`embed_shape`); tokenizer/table are *given inputs* |
| final logit softcapping + argmax | omitted — raw pre-softcap logits exposed | decoding-side; raw logits are the verifiable quantity |
| sliding/full attn split, MoE, per-layer-input gate | dense e2b base path only | structurally additive; out of scope by design |
| per-layer distinct parameters | uniform `blk` iterate (`gemma_stack n blk`) | the real per-layer-param stack is the identical `FOLDL`-over-params shape; see §4 |

## 4. GAP — what this directory is for, and what is not yet wired

This `conformance/` directory is the intended home of the **(i)→(ii)
bridge** described in `../DESIGN.md §4`: take a tiny catgrad gemma-4
config, fixed-point-quantize the abstracted scalars (the RMS reciprocal,
softmax weights, RoPE cos/sin tables) at a chosen `Q`, instantiate the
HOL4 spec's parameter inputs with them, `EVAL` the spec, and assert
equality with the catgrad/mistral.rs reference output to the quantization
tolerance — plus the per-layer-parameter stack refactor
(`FOLDL (λx p. gemma_layer_p p x)`), whose shape proof is structurally the
present `gemma_forward_shape`.

**Status: not yet wired.** What exists today is the verified spec + the 37
structural theorems above (PROVED) and this honest scope ledger. The
fixed-point parameter extraction and the comparison driver are the
concrete next milestone, deliberately not claimed as done. Nothing here
relies on that gap being closed; the theorems are `∀`-quantified over the
abstracted parameters and stand on their own.
