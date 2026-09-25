# The self-optimizing prover — what is proved, run, and walled

*An honest ledger. Engineering artifact, not a position paper. Every theorem
named here is cited `dir/file : theorem` and was machine-checked against the
real CakeML/Candle development; every live result was run on the real `cake`
binary. Where execution stops and proof takes over is stated, not blurred.*

---

## 0. The question

> *"How can it improve the theorem prover itself? As in, has it ever tried
> doing that?"* — Daniel Nezamabadi, HOL4 Zulip

The answer this artifact gives: **a fully machine-checked architecture for
safely improving the prover — its policy, its inference relation, its prover
build, and the recursion that mutually improves verifier and compiler — with
a live demonstration of the self-extension it permits, and a clearly-marked
line where machine-checked execution stops and machine-checked *proof* takes
over.** What ran live reaches the kernel *interface*: the `REFL` primitive
the whole prover calls was swapped in-process (§3 d). What never runs, by
design, is a swap of the *verified primitive* `Kernel` compiled into `cake.S`,
the root every swap is anchored to. The compiler has been rebuilt by itself
and has carried a new proved pass, generationally; the running compiler's
in-place self-upgrade is proved at eval semantics and runs as a program on
`cake`, while the patched root binary is built but not yet observed
self-upgrading (`selfUpgrade/SELFUPGRADE_ROOT.md`).

## 1. The chain, link by link

The canonical row-by-row ledger for this arc is [`CLAIMS.md`](../CLAIMS.md)
§5 (labels PROVED / RAN / ASSUMED as defined there; `verify-claims.sh`
checks its citations). This section keeps only what §5 does not itemise:
the supporting lemmas behind its rows, and one label the root table does not define —
**CITED**, a pre-existing verified CakeML/Candle theorem we depend on.

| Supporting link | Status | Citation |
|------|--------|----------|
| The modified relation *extends* the base one; prover self-improvement through the modified kernel preserves safety. | **PROVED** | `kernelMod/kernelModScript.sml : sym_kernel_extends_base, prover_self_improvement_is_safe_modified` |
| The in-place swap keeps the heap; SYM is a sound extension of Candle. | **PROVED** | `kernelMod/inplaceUpdateScript.sml : inplace_swap_preserves_heap, sym_extends_candle` |
| The self-optimization loop loses no theorem; one verified relocating hot-swap step. | **PROVED** | `kernelMod/selfOptimizeScript.sml : self_optimization_is_safe, verified_hot_swap_safe, sym_is_sound_extension` |
| The runtime checker's soundness is the single genesis fact. | **PROVED** | `kernelMod/genesisRuntimeScript.sml : sym_checker_is_sound` |
| A toy-but-real verified *relocator* (position-independence) discharging the abstract `reloc_correct`. | **PROVED** | `kernelMod/relocatorScript.sml : relocator_preserves_semantics, reloc_correct_discharged` |
| Compiler-correctness (the recompiled binary refines its source); `do_install` *requires* it. | **CITED** | CakeML compiler-correctness; `closSem$do_install`'s `compile_oracle` check |
| The recursive seam decomposes into the genealogy (verifier line) and selfprover (compiler line); recompile preserves code at every step. | **PROVED** | `recursive/recursiveImprovementScript.sml : stage_seam_decomposes, recursive_recompile_preserves_code_throughout` |
| The live self-extension, sentinel by sentinel. | **RAN** | `candle/selfopt_demo.ml` (`SYM_LEMMA`, `SYM_RULE`, `FACT1_SYM`, `FACT1_ROUNDTRIP`) |
| The compiler's self-recompilation, mechanically: self-host, fixpoint via `cmp`, self-optimize via `--inline_size`/`--max_app`. | **RAN** | `scripts/apex.sh` (APEX I) |
| Succession structure cannot dissolve the strengthening seam (a second negative beside `loeb_finite_obstruction`). | **PROVED (negative)** | `genealogy/genealogyScript.sml : genealogy_irrelevant_to_vouch_sound` |

## 2. The one Löb, and why mutual optimization escapes it

Three vouchings thread the recursion; only one is self-referential:

- verifier certifies the new **compiler** — a *different* artifact: **no Löb**.
- the new compiler **recompiles** the verifier — compiler-correctness: **no Löb**.
- verifier certifies the **next verifier** — the self-reference. An
  *equi-sound* (faster) successor is a sound extension the current verifier
  proves: **no Löb**. A *logically stronger* successor: **the LCA wall**.

So recursive mutual *optimization* of verifier↔compiler carries **no labelled
assumption** (`recursive_mutual_optimization_is_unconditional`); only verifier
*strengthening* reaches the one seam the whole tower isolates.

## 3. Where execution stops (the honest line)

- **Run live:** (a) a verified program self-*extending its own code* (proven
  derived rules), via the same verified `Install`/`do_install` the loader
  theorem is about; and (b) a full **proof-gated recompile→swap→resume loop**
  (`candle/self_recompile.ml`): the running system replaces its own executing
  *compute* code with a freshly-compiled version (the in-binary CakeML compiler
  compiles the new closure; the real `do_install` installs it), but only after
  the live kernel *proves* the new version equal to the old; swaps accumulate
  path-dependently; an unprovable swap is rejected. Candle *proves*
  (`candle_prover`'s `perms_ok`) that REPL code **cannot** touch the trusted
  kernel — so the swapped object is *application/toolkit* code behind a
  program-controlled indirection, never the *verifier* itself. And (c) **the
  verified compiler recompiles itself** (`scripts/apex.sh`): `cake` compiles its
  own s-expression into a new working `cake` — a bit-identical **fixpoint**, and
  a self-**optimized** variant that stays correct (CakeML compiler-correctness,
  CITED). This is a *generational* rebuild (a new, correct binary), not an
  in-process heap-preserving swap. And (d) **an in-process swap of a KERNEL
  PRIMITIVE under the whole live prover** (`scripts/apex-kernel-swap.sh`): the
  kernel interface the entire prover calls (`REFL`) is re-architected into a live
  indirection (`candle/kernel_apex.patch`, applied *before* the derived layer
  loads), and the running prover's `REFL` is swapped mid-flight for a different
  sound derivation — gated, accumulating, a wrong swap rejected — while the prover
  keeps proving through it. **Heap-preserving and in-process.**
- **The fixed root — by design, not a gap:** the *verified primitive* `Kernel`
  (the unforgeable `thm` constructors compiled into `cake.S`) is never swapped.
  (d) swaps the kernel *interface* — everything the prover invokes as the kernel —
  while the verified primitive underneath stays put. That is deliberate: the
  primitive is the immutable root of trust the swap is anchored to; swapping *it*
  is neither possible (no way to forge a `thm`) nor desirable (it would dissolve
  the guarantee). Self-improvement reaches **all the way down to the kernel
  interface, gated by an immutable verified root**.
- **The compiler's own pipeline:** distinct from (b)/(c), which *use* the
  compiler and recompile it under its existing optimizations, a genuinely
  new verified pass (BVL `optimise`) is proved against the real `bvlSem` and
  baked into an altered root that runs it (Layer B, `compilerOpt/LAYERB.md`).
  Open: the whole-pipeline `compile_correct` re-composition, one FFI-trace
  subgoal short. The running compiler's in-place self-upgrade is proved at
  eval semantics (`selfUpgrade/`) and runs as a program on `cake`; the
  patched root binary is built, its `--repl` run env-blocked
  (`selfUpgrade/SELFUPGRADE_ROOT.md`).

## 4. The discipline holds

Every theorem in this arc is `DISK_THM`-clean (zero added axioms, zero oracle tags
beyond the benign disk tag), zero `cheat`. The CakeML-semantics theorems
(`do_install_preserves_code`, `candle_SYM_implements_sym_extension`) carry the
*identical* tag profile as CakeML's own kernel theorems — they add **no new
turtle**; their only trust is the built CakeML/Candle development the whole
Candle-checked tower (`CLAIMS.md` §4) already rests on.

If anything here is found to exceed what is proved, run, or cited, that is a
bug — file it.
