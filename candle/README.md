# `candle/` — Fused Verified Candle Substrate

This directory contains the live HOL Light / Candle programs executed by the
verified `cake` binary (`scripts/tier3-place-candle.sh` and
`scripts/reflectsem-live.sh`). Rather than a collection of disconnected toy
scripts, the Candle layer is organized into two unified pipelines:

## 1. `theplace.ml` — Unified Habitat, Self-Optimizing Rule & Proof-Gated Compiler Cell

Loaded directly on top of `hol.ml` (`scripts/tier3-place-candle.sh`):

- **Habitat & Policy Weakening**: `SAFETY_PRESERVATION`, `SAFE_WEAKENING`,
  `WD_HABITAT_SAFE`, `WD_SELF_OPTIMIZED_SAFE`, `CP_HABITAT_SAFE`,
  `CP_SELF_OPTIMIZED_SAFE`, and `EQ_SYM_RULE`.
- **Derived `SYM_RULE` Self-Optimization**: `SYM_LEMMA`, `SYM_RULE`, `FACT1`,
  `FACT1_SYM`, `SYM_TWICE`, and `FACT1_ROUNDTRIP`.
- **Proof-Gated Code Replacement & Compiler Cell (`cmap`)**:
  - `GATE1`, `GATE2`, and rejection of non-universal `BAD_NON_GATE`
    (`bad_gate_ok = false`, `bad_swap = false`).
  - `GATE_B`, `GATE_C`, rejection of `BAD_AT_ZERO` (`bad_ok = false`,
    `upBad = false`), history-preserving generation map `cmap`, and native
    `Kernel.compute` verification (`THEPLACE_COMPUTE_THM`,
    `compiler_cell_verdict = "COMPILER_CELL_CANDLE_OK"`,
    `verdict = "APEX_SUBSTRATE_OK"`).

## 2. `reflectsem_*.ml` + `ouroboros_rewrites.ml` + `ouroboros.ml` — Fused Reflective Compiler & Prover Loop

Loaded on top of `hol.ml` (`scripts/reflectsem-live.sh --ouroboros`):

1. `reflectsem_datatypes.ml` & `reflectsem_functions.ml`: Real CakeML AST
   (`:exp`) and fuel-indexed big-step operational semantics (`eval_n`) exported
   from HOL4 (`reflectsem/`).
2. `reflectsem_gate_smoke.ml`: Concrete `eval_n` gate theorems (`rs_thm1`,
   `rs_thm2`, `rs_thm3`, `RS_SMOKE_VERDICT = "RS_SMOKE_OK: 3 eval_n theorems proved by the Candle kernel"`).
3. `ouroboros_rewrites.ml`:
   - Kernel-proved AST rewriter theorems (`orw_oeq`, `orw_exp_preserves`,
     `ofold_preserves`, `oeq_preserves`, `OEQ_DOUBLE`, `OEQ_COLLECT1`,
     `OEQ_COLLECT2`, `OEQ_REASSOC`, `OEQ_OFOLD`, `OEVAL`, `ofold_frag`).
   - Verified `:cval` compute mirror (`cvo_def`, `cval_nodes_def`,
     `cval_fuel_def`, `cval_eval_def`, `cval_fold_def`,
     `OURO_KERNEL_COMPUTE_PRIMITIVE_THM`, `OURO_CVAL_COMPUTE_THM`) executed
     directly through `Kernel.compute (COMPUTE_INIT_THMS, ouro_cval_eqs)` with
     zero fallback.
4. `ouroboros.ml`:
   - Proof-gated `:exp -> :exp` compiler cell (`ouro_compiler_cell`,
     `active_pass`, `ouro_compiler_cell_thm`, history-preserving `ouro_cmap`),
     upgraded live in-loop across verified compiler passes
     (`orw_exp_preserves` -> `ofold_preserves`) while refusing unproved passes.
   - Per-generation `:cval` compute verification (`ouro_cval_check`) and
     `active_pass` wired directly into `ouro_step`, `ouro_rw_route`,
     `ouro_batch_install`, and `ouro_loop` across all 5 accepted generations
     (AST size `19 -> 15 -> 13 -> 11 -> 7 -> 5`, 2 kernel refusals of `drop`,
     improver upgraded from v1 to v3).
5. `kernel_apex.patch`: Patch adding live indirection around `Kernel.REFL` in
   `candle/kernel.ml` (`scripts/apex-kernel-swap.sh`).
6. `compute_if.patch`: Patch aligning `candle/compute.ml`'s `Cexp_if` pair
   clause (`Cexp_if (Cexp_pair p2 q2) p1 q1 = q1`) with CakeML commit
   `1af98e502b4d13fe06c561012f002b7e3c15d609`'s `compute_thms_def` so
   `Kernel.compute` runs natively (`scripts/place-server.sh` also stages this
   automatically on `Cakeml.loadPath`).
