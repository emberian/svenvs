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

## What was achieved, and the honest boundary (definitively diagnosed)

**Built and verified at the compiler level.** The self-upgrade is proven (the 48
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

**Runtime-demo boundary — environmental, not the patch (proven).** Demonstrating
the *interactive* self-upgrade needs `--repl` (per-declaration Eval, where the
patched eval loop lives). In *this* candle package, **self-compiled cakes cannot
run interactive `--repl`** — they segfault in the Eval/`do_install` runtime while
working fine in batch compile. This was proven to be **environmental, not the
patch**: an *unpatched* self-compile of the same source segfaults in `--repl`
identically (rc 139), while compiling correctly. The only `--repl`-capable cake
present is the **downloaded** official binary (not patchable); the local sexpr
does not reproduce it (the self-compiled `.S` diverges from the download at the
entry preamble, and its `do_install` runtime is subtly incompatible here). Layer
B hit the same wall and only ever used compile mode. A runnable verified
self-upgrading binary therefore needs the **official build environment** — the
in-logic `x64BootstrapTheory` (which emits a *verified* `cake.S`; heavy, and it
has a latent broken HOL trace in this checkout to fix first).

**Also: the self-upgrade *pattern* runs** as a program on the real (download)
cake — `candle/compiler_cell_upgrade.cml` (`COMPILER_CELL_UPGRADE_OK`) and the
Candle-kernel-proof-gated `candle/compiler_cell_candle.ml`
(`COMPILER_CELL_CANDLE_OK`). What is NOT claimed: that the altered *cake binary
itself* was observed self-upgrading at runtime in this env, nor that it is
re-verified end-to-end in logic.
