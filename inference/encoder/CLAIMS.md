# inference/encoder — exactly what is PROVED vs still ABSTRACTED

Skeptic-facing scope ledger for `encoderBlockScript.sml`, same honesty
discipline as the repo-root `CLAIMS.md`. Zero `cheat`/`mk_thm`/
`new_axiom`/oracle (source-scanned; built locally — "Cache miss; theory
will be built locally" — not restored via any cache oracle). Builds in
~0.4 s in light HOL4, on top of the already-cheat-free
`../mlpInferenceTheory` and `../attn/attnTheory`.

## What this delivers

A **real two-sublayer transformer-style encoder block**, composing the
two verified pieces already in the repo:

- attention sublayer = the verified hardmax single-head attention
  micro-block (`../attn/attnScript.sml : attn1`, with its proved
  `argmax_is_max` / `attn1_picks_a_value`);
- feed-forward sublayer = the verified ReLU dense net
  (`../mlpInferenceScript.sml : mlp`, with its proved `mlp_nonneg`);

each wrapped in its **own residual skip** (`res f x = vadd x (f x)`,
i.e. the real transformer `x = x + Sublayer(x)` applied twice):

```
encoder_block Ks V Ws x = res (ff_sublayer Ws) (res (attn_sublayer Ks V) x)
```

## PROVED (machine-checked HOL4 theorems)

| Property | Theorem |
|----------|---------|
| Residual skip preserves width when its sublayer does | `res_shape` |
| **Residual invariant** (substantive half): a zero sublayer leaves x EXACTLY unchanged — the skip genuinely carries x through (true identity, not shape-only) | `res_zero_sublayer` |
| Attention sublayer contributes an ACTUAL V row (no hallucinated vector) | `attn_sublayer_picks_real_value` |
| Attention sublayer is width-preserving (V rows width d) | `attn_sublayer_shape` |
| Feed-forward contribution is genuinely ReLU-gated (≥ 0) | `ff_sublayer_nonneg` |
| Feed-forward sublayer is width-preserving (last MLP layer d rows) | `ff_sublayer_shape` |
| **END-TO-END shape preservation**: the full two-sublayer block maps width d → width d under natural well-formedness premises | `encoder_block_shape` |
| **END-TO-END residual invariant**: both sublayers zero ⇒ the whole encoder block is the identity on x (proved as a real identity) | `encoder_block_zero_collapses` (+ `encoder_block_zero_def`) |
| Depth-N stack preserves width, depth-independent (induction on depth) | `encoder_stack_shape`, `encoder_stack_shape_aux` |
| Concrete instance runs in-logic (computed, not asserted): block `[1;0] → [42;10]`, depth-2 stack `[1;0] → [124;30]`, shape = 2 | `demo_encoder_block_eval`, `demo_encoder_stack_eval`, `demo_encoder_block_shape` |

The `demo_*_eval` are `EVAL_TAC` — the composed encoder is *run inside
the logic* and the output equality is proved.

## ABSTRACTED — inherited verbatim from the two component theories,
   stated loudly, not introduced here

- **Numeric domain is `int`**, not f32/bf16. Inherited from
  `../mlpInferenceTheory` / `../attn`. Shapes & residual/identity
  structure are numeric-domain-independent; that is exactly what is
  proved.
- **Attention is hardmax** (softmax temperature → 0), inherited from
  `../attn`. The *routing/selection + residual plumbing* is exact; real
  softmax weighting is not modeled here (that is the separate
  `../numeric` track, which replaces the softmax-normalization
  abstraction with a proven-error-bound fixed-point op).
- The `center`/layernorm stand-in of `../attn`'s `block` is **not**
  used here: `encoder_block` uses pure residual skips (`res`), so the
  residual invariant is a clean, exact identity (`res_zero_sublayer`,
  `encoder_block_zero_collapses`) rather than a centered approximation.

## NOT CLAIMED

- Bit-exact f32 transformer behaviour.
- Real softmax / GeLU-tanh / RMSNorm numerics inside this block (domain
  is `int`, attention is hardmax).
- That this is gemma-4-scale. It is a *faithful, end-to-end-proved,
  EVAL-runnable two-sublayer-with-residual encoder block built from two
  independently verified pieces* — the substantive composition step the
  prior toy MLP / lone attention micro-block did not have.
