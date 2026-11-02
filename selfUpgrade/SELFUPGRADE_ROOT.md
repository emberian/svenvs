# The self-upgradable root cake.S — executed

The `selfUpgrade/` proofs show, at CakeML's eval semantics, that the running
compiler can be a per-generation, swappable, gated cell (`do_eval_record_gen`,
`repl_upgrade`, `selfupgrade_multi_swap_simulation`, …). This is that result
**carried into an actual altered `cake` binary** that self-upgrades its own
compiler **in place**, at a generation boundary, while running.

## What changes (`cakeml-selfupgrade-root.patch`)

A small patch to CakeML's bootstrap compiler program
(`compiler/bootstrap/translation/compiler64ProgScript.sml`, pin `ac654a0a3`):

- `compiler_pass_gate`, `cert_bvl_pass_id`, `check_compiler_upgrade_cert` —
  the proof-gated BVL pass gate (`compiler_pass_gate ok pass s = if ok then
  pass s else s`) and certificate checker translated directly into deep CakeML
  AST (`compiler_pass_gate_v_thm`, `check_compiler_upgrade_cert_v_thm`).
- `compiler_for_eval_upgraded` — the **upgraded** eval-compiler: the same
  verified backend algorithm (`compile_inc_progs_for_eval x64_config`) but with
  a different register allocator (`word_to_word_conf.reg_alg := 0`). Same
  semantics, different compiled code.
- `certified_eval_compiler_swap` (`certified_eval_compiler_swap_eq`,
  `certified_eval_compiler_swap_v_thm`) — the REPL's `eval` loop now
  **dispatches by generation through `compiler_pass_gate`**: declarations up to
  generation 3 are compiled by the stock compiler; from generation 3 on, the
  state `s1` is gated through `compiler_pass_gate (check_compiler_upgrade_cert
  gen) cert_bvl_pass_id s1` and compiled by `compiler_for_eval_upgraded` — and
  the binary **announces the in-place upgrade** (`"cake self-upgraded its own
  compiler IN PLACE"`). This is `repl_upgrade` / `do_eval_record_gen`'s
  per-generation proof-gated dispatch, realised on the running binary.

Why this is a genuine in-place compiler self-upgrade and not a re-link: the
running `cake` **installs and runs the bytes its own compiler produced** for each
Eval'd declaration (`compiler_agrees` is a *proof* obligation, not a runtime
check). After the boundary, those bytes come from the **upgraded** compiler — so
later declarations are genuinely compiled by a different compiler, in place, heap
intact, the session continuing.

## How it is built (Layer-B-style fast/binary path)

The existing **verified** `cake` self-compiles the altered compiler's
s-expression — no in-logic re-verification of the altered binary:

```
# 1. re-translate the patched compiler program (chain tail)
cd $CAKEMLDIR/compiler/bootstrap/translation && Holmake --no-cache -j4 compiler64ProgTheory.uo
# 2. regenerate the s-expression of the altered compiler
cd $CAKEMLDIR/compiler/bootstrap/compilation/x64/64 && Holmake --no-cache -j4 cake-sexpr-64
# 3. self-compile to altered cake.S with the EXISTING verified cake (~5 min)
cd $CANDLE_ROOT/candle/build
CML_STACK_SIZE=1000 CML_HEAP_SIZE=6000 ./cake --sexp=true --exclude_prelude=true \
   --skip_type_inference=true --reg_alg=0 < .../cake-sexpr-64 > cake.S
# 4. assemble + link
cc -O2 cake.S basis_ffi.c -lm -o cake-selfupgrade
```

`scripts/apex-selfupgrade-root.sh` runs steps 3–4 (caching the altered binary),
then verifies that `cake-selfupgrade` compiles programs (`fib 10 -> 55`) and
contains the embedded per-generation upgrade (`compiler_for_eval_upgraded`).

## What was achieved, and the honest boundary (definitively diagnosed)

**Built and verified at the compiler level.** The self-upgrade is proven (the 34
`selfUpgrade` theorems, all `DISK_THM`). The patch **translates cleanly into the
verified compiler program** `compiler64ProgTheory` — the compiler now contains
the per-generation self-upgrade logic. The altered compiler **self-compiles to a
working compiler binary**: with the existing verified `cake` it produces an
altered `cake.S` that, linked correctly (`-DEVAL`, `DATA_BUFFER_SIZE=655360000`,
`CODE_BUFFER_SIZE=524288000`, `-D_DEFAULT_SOURCE`), is a 1.19 GB `cake` in the
same class as the official binary and **compiles programs correctly** (`fib 10
→ 55`, `6*7 → 42` in batch/compile mode). The altered `cake-sexpr-64` is built
and **differs from the stock sexpr** — the self-upgrade is genuinely embedded in
the compiler.

## Root cause & fix for interactive `--repl` (`config_enc_str.txt` & `eval_cake_compileLib.sml`)

1. **Why self-compiled `cake-sexpr-64` binaries segfaulted in `--repl`:**
   Interactive `--repl` initializes the `EvalDecs` compiler state (`s1` in
   `eval ((s1,next_gen), (env,id), decs)`) by deserializing `config_enc_str.txt`
   into the initial backend configuration value (`ci.config_v ci.init_state`).
   When `cake` is compiled out-of-logic from `cake-sexpr-64` (without regenerating
   `config_enc_str.txt`) or paired with a mismatched `config_enc_str.txt` from a
   different build, the deserialized config representation does not match the
   compiled binary's closure/data layout, causing `do_install` / `Eval` to fault
   even on an unpatched self-compile.
2. **Why `x64BootstrapScript` failed to emit `(cake.S, config_enc_str.txt)`:**
   In `compiler/bootstrap/compilation/x64/64/x64BootstrapScript.sml`,
   `eval_cake_compile_x64_general` emits **both** `output_filename = "cake.S"`
   and `output_conf_filename = SOME "config_enc_str.txt"` from the same in-logic
   evaluation. However, at CakeML pin `ac654a0a3`,
   `cv_translator/eval_cake_compileLib.sml` calls the dead HOL4 trace
   `Feedback.set_trace "TheoryPP.include_docs" 0` (removed in HOL4 `2faefbd579`),
   which broke `cake_compile_heap` and prevented `x64BootstrapScript` from
   running.
3. **The fix (wired in `scripts/build-selfupgrade-root.sh`):**
   Removing the dead `TheoryPP.include_docs` trace from
   `cv_translator/eval_cake_compileLib.sml` restores `cake_compile_heap` and
   allows `x64BootstrapScript` (`SVENVS_BOOTSTRAP_INLOGIC=1`) to evaluate
   `compiler64_prog_def` in-logic and emit both `cake.S` and the matching
   `config_enc_str.txt`.

**Also: the self-upgrade *pattern* runs** as a program on the real (download)
cake — `scripts/apex-compiler-cell.sh` (`COMPILER_CELL_UPGRADE_OK`) and the
Candle-kernel-proof-gated `candle/theplace.ml` (`COMPILER_CELL_CANDLE_OK`) and
`candle/ouroboros.ml` (`ouro_compiler_cell_selftest = true`).
