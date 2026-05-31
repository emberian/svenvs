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
over.** It does **not** claim to have run a live edit of the trusted kernel or
the compiler; it claims to have *proved every link of that* and run the part
that is safe to run.

## 1. The chain, link by link

Labels: **PROVED** (HOL4 theorem, no cheat) · **CITED** (a pre-existing
verified CakeML/Candle theorem we depend on) · **RAN** (executed on the real
`cake` binary) · **WALLED** (Gödel/Löb-irreducible, isolated + labelled).

| Link | Status | Citation |
|------|--------|----------|
| A modified *inference relation* (Candle + SYM as a primitive) is sound, re-verified against the real `holSoundness` semantics. | **PROVED** | `kernelMod/kernelModScript.sml : sym_kernel_sound` (extension: `sym_kernel_extends_base`) |
| Prover self-improvement through the *modified* kernel preserves safety; `frozen_checker_sound` discharged for the modified build. | **PROVED** | `kernelMod/kernelModScript.sml : frozen_checker_sound_modified, prover_self_improvement_is_safe_modified` |
| `frozen_checker_sound` discharged for the *base* Candle build from the real `proves_sound`. | **PROVED** | `selfproverConcrete/selfProverConcreteScript.sml : frozen_checker_sound_candle, prover_self_improvement_is_safe_candle` |
| An in-place kernel swap is safe iff the new kernel is a sound *extension* — heap survives, soundness held. | **PROVED** | `kernelMod/inplaceUpdateScript.sml : inplace_update_is_safe, inplace_swap_preserves_heap, sym_extends_candle` |
| The unbounded self-optimization loop stays sound and loses no theorem; one verified relocating hot-swap step. | **PROVED** | `kernelMod/selfOptimizeScript.sml : self_optimizing_prover_is_safe, self_optimization_is_safe, verified_hot_swap_safe, sym_is_sound_extension` |
| "HOL4 stays out of execution": the runtime loop's safety depends only on one genesis fact (the runtime checker's soundness), never a per-step HOL4 call. | **PROVED** | `kernelMod/genesisRuntimeScript.sml : genesis_certifies_runtime, sym_checker_is_sound` |
| **The loader, for real:** over CakeML's *actual* `closSem$do_install`, runtime code installation preserves every existing code entry — the running kernel and all compiled functions survive the self-modification. | **PROVED** (real CakeML semantics) | `loader/installLoaderScript.sml : do_install_preserves_code, do_install_preserves_FLOOKUP` |
| A toy-but-real verified *relocator* (position-independence) discharging the abstract `reloc_correct`. | **PROVED** | `kernelMod/relocatorScript.sml : relocator_preserves_semantics, reloc_correct_discharged` |
| **The heavy link, closed:** Candle's *executable* monadic SYM kernel function soundly implements the modified rule — from `a===b` it yields a valid `\|-` judgment of `b===a` — by citing CakeML's own `SYM_thm`/`THM_def`. | **PROVED** (real monadic kernel) | `kernelImpl/kernelImplSymScript.sml : candle_SYM_implements_sym_extension` |
| Compiler-correctness (the recompiled binary refines its source); `do_install` *requires* it. | **CITED** | CakeML compiler-correctness; `closSem$do_install`'s `compile_oracle` check |
| **The capstone:** recursive *mutual* verifier+compiler self-improvement is a genealogy over `(verifier, compiler)` stages — every stage's verifier sound and compiler correct, unbounded; the seam decomposes into the genealogy (verifier line) and selfprover (compiler line); recompile preserves code at every step. | **PROVED** | `recursive/recursiveImprovementScript.sml : recursive_mutual_self_improvement_is_safe, stage_seam_decomposes, recursive_recompile_preserves_code_throughout, recursive_mutual_optimization_is_unconditional` |
| A running verified program self-extends its own code with a proven-safe derived rule and uses it. | **RAN** on the real `cake` binary | `candle/selfopt_demo.ml` (`SYM_LEMMA`, `SYM_RULE`, `FACT1_SYM`, `FACT1_ROUNDTRIP`); the SYM rule + a live policy self-optimization also certified in `candle/theplace.ml` (`EQ_SYM_RULE`, `WD_SELF_OPTIMIZED_SAFE`) |
| Genuine *logical strengthening* of the verifier (proving strictly more). | **WALLED** | the labelled `kernelUpgradeTheory.loeb_reflection` (LCA); negatives `loeb_finite_obstruction`, `genealogy_irrelevant_to_vouch_sound` |

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

- **Run live:** a verified program self-*extending its own code* (proven
  derived rules), via the same verified `Install`/`do_install` the loader
  theorem is about. Candle further *proves* (`candle_prover`'s `perms_ok`)
  that REPL code **cannot** touch the trusted kernel — so the live self-edit
  is of the *toolkit*, never the *verifier*.
- **Proved, not run:** a live edit of the trusted *kernel* or *compiler*. The
  kernel-swap chain is machine-checked end to end, but executing it needs a
  **host CakeML program** that embeds the kernel and drives the
  recompile-relocate-resume loop (the host is not REPL code, so it is not
  bound by `perms_ok`). That host program is the remaining systems work; every
  link it would invoke is already a theorem above.
- **Not attempted:** verified *optimization of the compiler itself* (a large
  separate development).

## 4. The discipline holds

Every theorem above is `DISK_THM`-clean (zero added axioms, zero oracle tags
beyond the benign disk tag), zero `cheat`. The CakeML-semantics theorems
(`do_install_preserves_code`, `candle_SYM_implements_sym_extension`) carry the
*identical* tag profile as CakeML's own kernel theorems — they add **no new
turtle**; their only trust is the built CakeML/Candle development the whole §4
tower already rests on.

If anything here is found to exceed what is proved, run, or cited, that is a
bug — file it.
