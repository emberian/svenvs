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
| **A genuinely NEW verified compiler optimization (BVL):** a structural pass `optimise` (empty-`Let` elimination) is proved **semantics-preserving against the real `bvlSem$evaluate`** (full congruence, by `recInduct evaluate_ind`) AND cost-reducing; instantiated as a CONCRETE proved witness of the genealogy's compiler line (so `ccorrect` is no longer an abstract token — it is "preserves real BVL semantics"). Upgrades the compiler line from CITED to PROVED. | **PROVED** (real CakeML BVL) | `compilerOpt/compilerOptScript.sml : optimise_correct, optimise_nonincreasing, optimise_let_nil_strict, recursive_compiler_line_preserves_bvlSem` |
| **Layer B — the compiler swaps itself for a proven-better one:** that pass is **baked into CakeML's own compiler** (`bvl_to_bvi$compile_def`) and an **altered self-hosting root `cake.S` bootstrapped** that carries it — it runs, self-hosts (self-compiled `.S` is smaller), and the pass **fires** end-to-end (empty `Let` eliminated, output unchanged). | **RAN** (altered root) + **PROVED** (the pass) | `compilerOpt/cakeml-bvl_opt.patch`, `compilerOpt/LAYERB.md` (built/validated on persvati) — residual: the full `compile_correct` re-composition is one FFI-trace subgoal short (LAYERB.md) |
| **Toward in-place compiler self-upgrade** (running `cake` swaps its own compiler, heap intact): the eval-oracle invariant is generalised to a **per-generation compiler map** (`s_rel_gen`); a swap-then-eval generation preserves it **end to end** and preserves the observable result relation — an in-place compiler swap keeps eval semantics (one swap-generation). The keystone is then **iterated over a schedule of arbitrarily many in-place swaps** (`selfupgrade_multi_swap_simulation`, induction on the schedule) with the conservative whole-program collapse. The op is made **concrete + exposed**: `do_eval_record_gen` is a real `custom_do_eval` (no core-semantics edit) dispatching the compiler by env-generation, generalising `do_eval_record` and preserving the invariant per step; `repl_upgrade` is the sound exposed upgrade entry point; and the heap-preserving reset upgrade is checked against the real backend. | **PROVED** (keystone + multi-swap lift + concrete op/expose + reset vs real backend) | `selfUpgrade/selfUpgradeEndToEndScript.sml : selfupgrade_eval_simulation_step, s_rel_gen_const, selfupgrade_collapses_to_eval_simulation`; `selfUpgrade/selfUpgradeMultiSwapScript.sml : selfupgrade_multi_swap_simulation, selfupgrade_oracle_semantics_prog_collapse`; `selfUpgrade/evalUpgradeOpScript.sml : do_eval_record_gen_const, do_eval_record_gen_preserves_wf, repl_upgrade_preserves_recorded_orac_wf_gen`; `selfUpgrade/evalUpgradeResetScript.sml : eval_upgrade_preserves_semantics` (+ `evalUpgradeB`). Remaining: carry the op as the running `EvalDecs` root — re-bootstrap. (The *strictly* multi-compiler whole-program `semantics_prog` needs a per-generation meta-compiler `do_eval` — a CakeML-semantics change we do not make; multi-compiler content lives at `evaluate_decs`, closed for arbitrarily many swaps.) |
| **The capstone:** recursive *mutual* verifier+compiler self-improvement is a genealogy over `(verifier, compiler)` stages — every stage's verifier sound and compiler correct, unbounded; the seam decomposes into the genealogy (verifier line) and selfprover (compiler line); recompile preserves code at every step. | **PROVED** | `recursive/recursiveImprovementScript.sml : recursive_mutual_self_improvement_is_safe, stage_seam_decomposes, recursive_recompile_preserves_code_throughout, recursive_mutual_optimization_is_unconditional` |
| A running verified program self-extends its own code with a proven-safe derived rule and uses it. | **RAN** on the real `cake` binary | `candle/selfopt_demo.ml` (`SYM_LEMMA`, `SYM_RULE`, `FACT1_SYM`, `FACT1_ROUNDTRIP`); the SYM rule + a live policy self-optimization also certified in `candle/theplace.ml` (`EQ_SYM_RULE`, `WD_SELF_OPTIMIZED_SAFE`) |
| **A live proof-gated recompile→swap→resume loop:** the running system replaces its own executing *compute* code with freshly-compiled versions (in-binary CakeML compiler → real `do_install`), each gated by a live kernel equivalence proof; two swaps **accumulate** (path-dependent; cost 101→1; outputs invariant); an unprovable swap is **REJECTED**, so semantics cannot break. Its safety is an *instance* of the proved genealogy. | **RAN** on the real `cake` binary | `candle/self_recompile.ml` (`GATE1`, `GATE2`, `verdict = "APEX_SUBSTRATE_OK"`); bridge `selfRecompile/selfRecompileGateScript.sml : gate_is_vouch_sound, self_recompile_loop_is_safe, self_recompile_preserves_outputs` |
| **The verified compiler recompiles ITSELF:** `cake` compiles its own s-expression into a new working `cake` (bit-identical **FIXPOINT** — a verified fixed point of itself), and into a self-**optimized** variant (different binary, still a correct compiler). Correctness = CakeML's verified compiler-correctness. | **RAN** on the real `cake` binary | `scripts/apex.sh` (APEX I: self-host, fixpoint via `cmp`, `--inline_size`/`--max_app` self-optimize); compiler-correctness **CITED** (CakeML) |
| **THE APEX, proved safe:** every generation of the self-improving+self-recompiling system has a *sound prover* AND a *correct compiler*, for ANY path — the concrete (prover × compiler) instance of the recursive genealogy, with compiler-correctness preserved by self-recompilation (CITED) and the prover advancing by gate-certified sound extensions. | **PROVED** | `apex/apexScript.sml : apex_generations_safe, compiler_self_recompilation_stays_correct, apex_is_a_genealogy` |
| **IN-PROCESS swap of a KERNEL PRIMITIVE, under the whole live prover:** the kernel interface the entire prover calls (`REFL`) is re-architected into a live indirection over the verified `Kernel.REFL`; the running prover's `REFL` is swapped mid-flight for a different sound derivation — gated for correctness, accumulating, a wrong swap rejected — and the prover keeps proving through it (37 internal REFL calls to prove `2+2=4`, all funnelled through the swapped primitive). **Sound by construction**: any impl must mint its `thm` via the unforgeable verified `Kernel`. | **RAN** on the real `cake` binary | `scripts/apex-kernel-swap.sh`, `candle/kernel_swap_demo.ml` (`verdict="KERNEL_INPROCESS_SWAP_OK"`), `candle/kernel_apex.patch` |
| Genuine *logical strengthening* of the verifier (proving strictly more). | **WALLED → REDUCED** | `kernelUpgradeTheory.loeb_reflection`, now *derived in-logic* from a named cited LCA ingredient: `kernel/loebReduction/loebReductionScript.sml : loeb_reflection_from_lca` (cheat-free, `axioms=[]`); residual = the LCA itself (`lcaProof`, CPU/RAM-walled). Negatives `loeb_finite_obstruction`, `genealogy_irrelevant_to_vouch_sound` |

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
- **Not attempted:** adding a genuinely *new verified optimization pass to the
  compiler's own pipeline* (a large separate development) — distinct from (b)/(c),
  which *use* the compiler and recompile it under its *existing* optimizations.

## 4. The discipline holds

Every theorem above is `DISK_THM`-clean (zero added axioms, zero oracle tags
beyond the benign disk tag), zero `cheat`. The CakeML-semantics theorems
(`do_install_preserves_code`, `candle_SYM_implements_sym_extension`) carry the
*identical* tag profile as CakeML's own kernel theorems — they add **no new
turtle**; their only trust is the built CakeML/Candle development the whole §4
tower already rests on.

If anything here is found to exceed what is proved, run, or cited, that is a
bug — file it.
