# The self-upgradable root cake.S — executed

The `selfUpgrade/` proofs show, at CakeML's eval semantics, that the running
compiler can be a per-generation, swappable, gated cell (`do_eval_record_gen`,
`repl_upgrade`, `selfupgrade_multi_swap_simulation`, …). This is that result
**carried into an actual altered `cake` binary** that self-upgrades its own
compiler **in place**, at a generation boundary, while running.

## What changes (`cakeml-selfupgrade-root.patch`)

A small patch to CakeML's bootstrap compiler program
(`compiler/bootstrap/translation/compiler64ProgScript.sml`, pin `ac654a0a3`):

- `compiler_for_eval_upgraded` — the **upgraded** eval-compiler: the same
  verified backend algorithm (`compile_inc_progs_for_eval x64_config`) but with
  a different register allocator (`word_to_word_conf.reg_alg := 0`). Same
  semantics, different compiled code.
- the REPL's `eval` loop now **dispatches by generation**: declarations up to
  generation 3 are compiled by the stock compiler; from generation 3 on, by the
  upgraded compiler — and the binary **announces the in-place upgrade**. This is
  exactly `repl_upgrade` / `do_eval_record_gen`'s per-generation dispatch,
  realised on the running binary.

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
then feeds `candle/selfupgrade_root_demo.repl` to `cake-selfupgrade --repl` and
asserts: the **in-place compiler self-upgrade is announced**, the upgrade is a
**genuine compiler change** (register allocator switched), and the **observable
is preserved** across it (`RESULT=99` for `a=2,b=6,c=10,d=100,e=99`).

## Honest residual (stated, not blurred)

The altered binary is produced by **self-compilation, not in-logic
re-verification** — like Layer B, its `cake.S` carries no fresh
`x64BootstrapTheory` correctness theorem. And the post-upgrade compilations leave
the unmodified `backendProof` envelope: `opt_eval_config_wf` (backendProofScript)
pins `ci.compiler_fun = compile_inc_progs_for_eval asm_conf`, a single compiler.
The **generalised soundness of the per-generation swap is the `selfUpgrade`
proofs** (`do_eval_record_gen_preserves_wf`, `selfupgrade_multi_swap_simulation`,
`repl_upgrade_then_eval_preserves_wf`, all `DISK_THM`); the concrete
`backendProof` re-composition for the altered compiler is the remaining
gold-standard step (the same shape as Layer B's "one FFI-trace subgoal away").
What RUNS: an altered `cake` that swaps its own compiler in place at a generation
boundary and keeps computing correctly. What is NOT claimed: that the altered
binary is re-verified end-to-end in logic.
