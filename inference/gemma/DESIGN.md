# gemma-4-e2b verified forward pass — DESIGN

Research track B ("verified inference"), scaled up from the toy ReLU MLP
(`../mlpInferenceScript.sml`) toward a **faithful structural reference
specification** of a real modern transformer: the **gemma-4** decoder, as
implemented compositionally (open-hypergraph / catgrad `Builder` graph) in
`~/src/catgrad/catgrad-llm-models/src/models/gemma4.rs`.

This is **NOT a wrapper/bridge**. `gemmaForwardScript.sml` re-derives the
gemma-4 dataflow from scratch as HOL4 definitions and proves genuine
theorems about it. The catgrad source is the *architecture oracle* (what
ops, in what order, with what shapes); mistral.rs `docs/GEMMA4.md` /
`examples/python/gemma4.py` corroborate the model family.

---

## 1. The gemma-4-e2b text forward pass, fully decomposed

Decomposition follows `gemma4.rs` exactly. Citations are
`gemma4.rs:<line>` unless noted (`tensors.rs` = catgrad-llm-models helpers,
`nn/mod.rs` = catgrad stdlib).

### 1.1 Token embedding
`scaled_embeddings` (gemma4.rs:554): `x = embeddings(tok) * scale`,
`scale = hidden_size ** -0.5`-ish (gemma normalizer-style embedding
scaling). `embeddings` = row lookup (tensors.rs:255).

→ HOL: `embed table scale tok = MAP (λe. scale*e) (EL tok table)`.
Theorem **`embed_shape`**: output length = embedding dim.

### 1.2 Decoder layer (gemma4.rs `layer`, 898–995) — the dense path
gemma-4 uses a **double-norm sandwich** around each sublayer (this is the
distinctive gemma-2/3/4 structure, vs llama's single pre-norm):

```
residual = x
x = RMSNorm_input(x)              # input_layernorm        (913)
x = Attention(x)                  # self_attn              (919)
x = RMSNorm_post_attn(x)          # post_attention_ln      (931)
x = residual + x                  # residual               (937)
residual = x
x = RMSNorm_pre_ff(x)             # pre_feedforward_ln     (940)
x = MLP(x)                        # mlp (GeGLU)            (946)
x = RMSNorm_post_ff(x)            # post_feedforward_ln    (958)
x = residual + x                  # residual               (964)
x = x * layer_scalar              # per-layer scale        (992)
```
(The optional MoE branch 947–957, per-layer-input gate 966–990, and
sliding-vs-full attention split are real gemma-4 features but **out of
scope for the e2b dense base path** — see §3 Feasibility / Abstractions.)

→ HOL: `gemma_layer` (definition mirrors the 9 steps 1:1).
Theorem **`gemma_layer_shape`**: hidden→hidden length preservation under
the natural well-formedness hypotheses.
Theorem **`gemma_layer_residual_skeleton`**: identity-collapse sanity.

### 1.3 RMSNorm (tensors.rs:82 `rmsnorm_raw`, :105 `rmsnorm`, :114 gemma)
Real: `x / sqrt(mean(x²) + ε) * γ`. gemma's variant uses `(γ+1)`.

→ HOL: `rmsnorm_raw` / `rmsnorm` / `rmsnorm_gemma`. The reciprocal-RMS
scalar is **abstracted to an integer parameter `s`** (see §3). Dataflow
(per-vector last-dim reduction, elementwise γ scale, length preserved) is
exact. Theorems **`rmsnorm_shape`**, **`rmsnorm_gemma_shape`**,
**`rmsnorm_raw_shape`**, **`rmsnorm_identity`** (s=1,γ=1 ⇒ id),
**`map2_repl_one`**.

### 1.4 GeGLU MLP (gemma4.rs:644–668)
`mlp(x) = down_proj( gelu(gate_proj(x)) ⊙ up_proj(x) )`, no biases.
catgrad `gelu` is the tanh-approx (nn/mod.rs:158).

→ HOL: `mlp Wg Wu Wd x = matvec Wd (hadamard (MAP gelu_i (matvec Wg x))
(matvec Wu x))`. GeLU **abstracted** to `gelu_i = max(0,·)` (the monotone
non-negative gate surrogate; §3). Theorems **`mlp_shape`** (out = hidden),
**`mlp_gate_nonneg`**, **`hadamard_shape`**, **`gelu_i_nonneg`**.

### 1.5 Grouped-Query Attention (gemma4.rs `attention`, 767–887)
- q/k/v projections (`linear_b`, 787–814); q has `num_heads` heads, k/v
  have `num_kv_heads`, `rep = num_heads / num_kv_heads`.
- per-head **q_norm / k_norm RMSNorm** (824–836) — gemma-4 specific.
- **RoPE** applied to q,k (838–839).
- KV cache update; **`repeat_kv`** replicates each KV head `rep`× (865–866,
  tensors.rs:149 `repeat_interleave`).
- scores = `matmul(q, kᵀ)` + mask (868–872); `softmax` (874);
  `matmul(attn, v)` (875); reshape; `o_proj` (879).

→ HOL: `attn_scores q K = MAP (λk. dot q k) K` (exact, 868);
`repeat_kv rep kv = FLAT (MAP (REPLICATE rep) kv)` (exact head
combinatorics); `attn_head w V` = weighted value sum (softmax **abstracted**
to integer weight vector `w`; §3). Theorems **`attn_scores_shape`**,
**`repeat_kv_shape`** (len = rep·#kv), **`repeat_kv_grouping`** (Q-head q
pairs with KV-head `q DIV rep` — the actual GQA correctness property),
**`el_flat_replicate`**.

### 1.6 RoPE (rope.rs `rotate_half`, `apply_rope_embedding`)
`rotate_half([a‖b]) = [-b ‖ a]`; `out = cos⊙x + sin⊙rotate_half(x)`.

→ HOL: `rotate_half`, `apply_rope cos sin x`. cos/sin tables **abstracted
to integer parameter vectors** (precomputed fixed-point; §3); the rotation
*dataflow* is exact. Theorems **`rotate_half_shape`**,
**`apply_rope_shape`**, **`apply_rope_pos0_identity`** (cos=1,sin=0 ⇒ id,
i.e. position-0 leaves the token unmoved — matches the real model).

### 1.7 Final norm + LM head (gemma4.rs:1089–1115)
`x = RMSNorm_final(x)`; `logits = lm_head(x)` (tied to embeddings if
`tie_word_embeddings`); optional `final_logit_softcapping`
(`softcap·tanh(x/softcap)`); then `argmax`.

→ HOL: `gemma_forward blk n s_f g_f Wlm x = matvec Wlm (rmsnorm s_f g_f
(gemma_stack n blk x))`. Softcap+argmax are decoding-side and **abstracted
away** (we expose pre-softcap logits, the verifiable quantity). Theorems
**`gemma_stack_shape`**, **`gemma_forward_shape`** (out length =
vocab_size, any depth n).

### 1.8 Stacked model (gemma4.rs:1051–1094)
Loop over `num_hidden_layers`, then final norm. → `gemma_stack n blk`
(uniform-param iterate; real per-layer-param stack is the identical
`FOLDL`-over-param-list shape — milestone §4).

---

## 2. catgrad correspondence (compositional representation)

catgrad builds an **open hypergraph** (string diagram) via `Builder`:
every `op` (matmul, add, broadcast, reshape, rmsnorm, …) is a hyperedge;
`Var`s are wires; `Shape` carries `Nat` symbolic dims. This is a *typed
dataflow IR*, which is exactly why a HOL4 structural spec is the right
abstraction: our `int list` / `int list list` carry the same dataflow and
shapes as catgrad's `Var`/`Shape`, minus the f32 numeric semantics.

| gemma-4 op            | catgrad                                  | HOL4 def            |
|-----------------------|------------------------------------------|---------------------|
| embedding lookup      | `embeddings` tensors.rs:255              | `embed`             |
| RMSNorm / gemma RMS   | `rmsnorm`/`rmsnorm_gemma` tensors.rs:105 | `rmsnorm(_gemma)`   |
| linear (±bias)        | `linear_b(_param)` nn/mod.rs:251         | `matvec`/`linear`   |
| GeLU                  | `gelu` nn/mod.rs:158                     | `gelu_i` (abstr.)   |
| GeGLU MLP             | `mlp` gemma4.rs:644                      | `mlp`               |
| elementwise ⊙ / +     | catgrad `*` / `+`                        | `hadamard`/`vadd`   |
| repeat_kv (GQA)       | `repeat_interleave` tensors.rs:149       | `repeat_kv`         |
| attn scores           | `matmul(q,kᵀ)` gemma4.rs:868            | `attn_scores`       |
| softmax               | `softmax` nn/mod.rs:175                  | weight param (abs.) |
| RoPE rotate_half      | `rotate_half` rope.rs                    | `rotate_half`       |
| apply RoPE            | `apply_rope_embedding` rope.rs           | `apply_rope`        |
| decoder layer         | `layer` gemma4.rs:898                    | `gemma_layer`       |
| layer loop + norm     | `forward_embeddings` gemma4.rs:1051      | `gemma_stack`/`_forward` |

The long arc: a **verified evaluator for catgrad's hypergraph IR** (parse
the `Builder` graph, give it the `gemmaForward` denotational semantics,
prove the evaluator sound), and/or pushing the `int`/fixed-point spec
through the **verified PureCake→CakeML** compile path and Candle-checking
the result (the svenvs substrate; `~/.../svenvs-demo.md`).

---

## 3. Honest feasibility gradient

### (i) PROVABLE NOW — done in `gemmaForwardScript.sml`
Verified reference spec + structural theorems, cheat-free, builds in
seconds, pure HOL4:
- shape correctness for every op and for the full block & stacked model
  (`*_shape` family, `gemma_layer_shape`, `gemma_forward_shape`);
- structural invariants: `repeat_kv_grouping` (GQA head grouping is
  correct), `residual_identity` (residual highway is a true skeleton),
  `apply_rope_pos0_identity`, `rmsnorm_identity`, `mlp_gate_nonneg`;
- an EVAL-runnable tiny concrete instance (`toy_*_eval`) computing a
  deterministic output in-logic.

### (ii) CONFORMANCE-TESTABLE — harness in `conformance/`
HOL4 spec EVAL output `==` catgrad/mistral.rs output on tiny test
vectors, **once the numeric abstractions are instantiated with fixed-point
quantization** of the precomputed scalars. Real now: the harness, the test
config, the comparison driver. Gap: wiring fixed-point params (explicit).

### (iii) ASPIRATIONAL — NOT CLAIMED
A FLOP-level proof on the real 4.x-B-parameter gemma-4-e2b weights with
bit-exact bf16/f32 IEEE semantics. We do not claim this, do not approach
it, and flag it as the far end of the arc.

### Abstractions vs the real model (every one is deliberate & documented)
| Real gemma-4                         | Spec abstraction                         | Why faithful enough |
|--------------------------------------|------------------------------------------|---------------------|
| f32/bf16 activations                 | `int`                                    | shapes/dataflow are domain-independent; this is what we prove |
| `1/sqrt(mean x²+ε)` RMS scalar       | integer param `s`                        | isolates the only transcendental into one named input; conformance supplies `round(1/rms·Q)` |
| tanh-approx GeLU                     | `gelu_i = max(0,·)`                       | same monotone non-negative gate role; gating *dataflow* exact |
| softmax over scores                  | integer weight vector `w` param          | weighted-sum-of-values dataflow exact; conformance supplies fixed-point softmax weights |
| cos/sin RoPE tables (trig)           | integer param vectors                    | rotate_half + cos·x+sin·rot dataflow exact; conformance supplies fixed-point tables |
| final logit softcapping + argmax     | omitted (expose raw logits)              | decoding-side; raw logits are the verifiable quantity |
| sliding/full attn split, MoE, PLI    | dense base path only                     | e2b base text path; structurally additive — §4 |
| per-layer distinct params            | uniform `blk` iterate                    | real stack is the same `FOLDL`-shape — §4 |

---

## 4. Concrete next milestone

**Per-layer-parameter stack + instantiated conformance.** Replace
`gemma_stack n blk` with `FOLDL (λx p. gemma_layer_p p x) x params` over a
list of per-layer parameter records, re-prove `gemma_forward_shape` by
list induction (the proof is structurally the present one), then run the
`conformance/` harness with fixed-point-quantized RMS/softmax/RoPE
parameters extracted from a tiny catgrad gemma-4 config and assert
EVAL-output == catgrad-output to the chosen quantization tolerance. That
closes the (i)→(ii) gap for the dense path and is the springboard to the
verified-IR-evaluator long arc.
