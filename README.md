> PDFs live in the local paper library. Restore exact saved versions with `python3 tools/paperbin.py restore`; see [PAPERS.txt](PAPERS.txt).

# svenvs — A Self-Verifying, Self-Improving Reflective Compiler-and-Prover & Safety Envelope

[![Verify (Tier 1)](https://github.com/emberian/svenvs/actions/workflows/verify.yml/badge.svg)](https://github.com/emberian/svenvs/actions/workflows/verify.yml)

[Website](https://emberian.github.io/svenvs) · [`CLAIMS.md`](CLAIMS.md) (Mechanically Checked Ledger) · [`ARCHITECTURE.md`](ARCHITECTURE.md) (Layer Map) · [`CONTRIBUTING.md`](CONTRIBUTING.md) (Rules & Routes)

**svenvs** (*Self-Verifying ENVelopeS*) is a formal architecture and live runtime built on **HOL4**, **CakeML**, and **Candle** (the verified HOL theorem prover compiled to machine code by CakeML). It fuses two things into one system with **zero `cheat` tactics, zero `mk_thm`, and zero axioms**:

1. **A Universal Proof-Gated Safety Envelope**: An unconstrained inhabitant (`∀ctrl` — never inspected or trusted by the proof) acts inside a verified runtime shield (`enveloped`). Every layer of the habitat—from action policies and safety specifications down to neural inference, compiler optimization passes, the prover build, and the proof-checker kernel itself—is **mutable at runtime**, gated by a single machine-checked rule: *an upgrade is installed if and only if it carries an unforgeable theorem that safety is preserved*.
2. **A Fused Reflective Compiler-and-Prover**: Running live on the verified `cake` binary, the system hosts the real fueled operational semantics of CakeML (`eval_n`) inside its own LCF kernel, executes verified in-kernel bytecode computation (`Kernel.compute` over `:cval` in Candle and `cv_trans`/`cv_eval` over `:cv` in HOL4), and improves its own active compiler and rewriter across generations through an unforgeable theorem-gated cell.

---

## Core Idea: Verify the Cage, Leave the Door Open, Gate Every Layer

Most formal verification assumes a static system and tries to specify *what good behavior is*. **svenvs** inverts both:

1. **Start from a decidable negative floor (Corrigibility / Non-Lock-In)**:
   Instead of trying to formalize "alignment," [`corrigibility/`](corrigibility/CLAIMS.md) formalizes one concrete floor—**the operator can always bring the system `home` within a bounded horizon** (`corrigibler_floor_holds`). Everything above that floor—including the recovery mechanism itself—is mutable by the inhabitant, provided the upgrade carries a proof that recovery is never weakened or slowed past the deadline.
2. **One Certifier Theorem, Instantiated All the Way Down**:
   [`certifierScript.sml`](certifierScript.sml) proves once that **certifier soundness $\iff$ semantic transfer $\iff$ single-step gate safety $\iff$ unbounded stream/ratchet safety** (`sound_certifier_iff_transfers`, `cgate_safe`, `ratchet_stream`). Every self-modification gate in the repository is an instance of `cgate`, paired with a machine-checked necessity/counterexample theorem showing its seam is load-bearing.

**What "verified" means here:** exactly the cited theorems in [`CLAIMS.md`](CLAIMS.md) and their explicitly labeled seams (`encodes_obligation`, `encodes_soundness`, `frozen_checker_sound`, `attestation_faithful`). Not verified selfhood, alignment, or a safe inhabitant.

---

## System Architecture

### 1. The Fused Live Substrate (`candle/` + `reflectsem/` + `selfUpgrade/`)

The live Tier-3 runtime on the verified `cake` binary is unified into a single pipeline ([`candle/theplace.ml`](candle/theplace.ml) $\to$ [`candle/ouroboros_rewrites.ml`](candle/ouroboros_rewrites.ml) $\to$ [`candle/ouroboros.ml`](candle/ouroboros.ml)):

* **The Place & Live Kernel (`candle/theplace.ml`)**:
  Candle proves `SAFETY_PRESERVATION` and `SAFE_WEAKENING` in the running kernel. The live Place also exercises a theorem-gated compiler cell and checks a bytecode computation with `THEPLACE_COMPUTE_THM`.
* **Real CakeML Semantics Inside the Prover (`reflectsem/`)**:
  Ports CakeML's full AST and fueled big-step evaluator `eval_n` (45 datatypes, 134 kernel-checked defining equations) into the running Candle kernel, bridged to CakeML’s clocked evaluator by `eval_n_agrees` and the deep-embedded optimizer `oexp`/`ofold` in [`reflectsem/fueledBridgeScript.sml`](reflectsem/fueledBridgeScript.sml) (`oexp_eval_n_fuel_correct`, `ofold_eval_n_fuel_preserves`).
* **Fast Verified In-Kernel `:cval` Computation (`Kernel.compute`)**:
  Instead of slow LCF term-rewriting (`REWRITE_CONV`), [`candle/ouroboros_rewrites.ml`](candle/ouroboros_rewrites.ml) registers `:cval` S-expression equations (`cval_nodes`, `cval_fuel`, `cval_fold`, `cval_eval`) directly with Candle's verified CEK/bytecode machine (`Kernel.compute`), proving universal preservation theorems (`ofold_preserves`, `orw_exp_preserves`, `OURO_KERNEL_COMPUTE_PRIMITIVE_THM`, `OURO_CVAL_COMPUTE_THM`) with zero hypotheses.
* **Unforgeable Theorem-Gated Compiler Cell & Ouroboros Loop (`candle/ouroboros.ml`)**:
  * The Candle installer `ouro_install_compiler_pass` checks a hypothesis-free theorem about the named pass on expressions in `ofrag`, with sufficient fuel in the environment `oenv i` and state `ost0`. The executor is supplied separately. The gate checks the theorem’s conclusion against the pass constant.
  * The six-generation loop starts with `orw_exp`, installs `ofold`, evaluates candidate metrics with `Kernel.compute`, and feeds the selected source through CakeML’s `Eval`.
* **Pancake program optimization**. The constant-shift folder preserves the return result and complete state under CakeML’s Pancake evaluator (`pancake_opt_pass_sound`). The gate installs the folder before CakeML’s Pancake-to-target compiler (`gated_compile_prog_installs`). A rejected update produces the same compiler result as the ordinary backend (`gated_compile_prog_rejected`). Certifier soundness is necessary and sufficient for safe replacement (`pancake_gate_safe_iff`). A composed three-pass optimizer (algebraic identities, constant-condition branches, `Skip` removal) preserves the same complete result (`opt_passes_correct`), and a sound certifier can install any finite list of passes whose obligations establish correctness, preserving 64-bit source semantics from an empty code table (`pancake_pipeline_sound`, `gated_compile_pipeline_installs`). On Obend's three kernels it shrinks the AST by 1.9–4.5%. CakeML emits byte-identical x86-64 assembly before and after optimization of each kernel. [HOL4 theory](compilerOpt/pancakeOptGateScript.sml)
* **Self-Upgradable Compiler Root (`compilerOpt/` + `selfUpgrade/`)**:
  * [`compilerOpt/compilerOptScript.sml`](compilerOpt/compilerOptScript.sml) defines a recursive BVL constant-folding pass (`bvl_fold`), proves semantic preservation against CakeML's `bvlSem$evaluate` (`bvl_fold_correct`, `bvl_fold_is_ccorrect`) and non-increasing code size (`bvl_fold_nonincreasing`), and packages the operational gate (`compiler_pass_gate`).
  * [`selfUpgrade/selfUpgradeEndToEndScript.sml`](selfUpgrade/selfUpgradeEndToEndScript.sml) and [`selfUpgrade/cakeml-selfupgrade-root.patch`](selfUpgrade/cakeml-selfupgrade-root.patch) wire `certified_eval_compiler_swap` directly into CakeML's `compiler64ProgScript.sml` REPL `eval` loop and self-compile into a working 1.19 GB `cake-selfupgrade` binary ([`scripts/apex-selfupgrade-root.sh`](scripts/apex-selfupgrade-root.sh)).

### 2. Fast In-Logic Computation Across HOL4 & `hol-reflection` (`cv_compute`)

Several theories use HOL4’s verified `:cv` evaluator for concrete proof obligations.

* **Reflective HOL syntax checks ([`kernel/loebReduction/loebReductionScript.sml`](kernel/loebReduction/loebReductionScript.sml) & [`selfproverConcrete/selfProverConcreteScript.sml`](selfproverConcrete/selfProverConcreteScript.sml))**:
  Translates the deep-embedded HOL syntax, type, term, α-equivalence, and context-update checkers (`REV_ASSOCD`, `tymatch`, `type_ok_alist`, `term_ok_alist`, `welltyped_check`, `aconv_check`, `constrainable_update_check`, `check_updates_chain`) into `:cv` functions with `[cv_inline]` bridges for finite-map lookups on `thyof ctxt`. The executable checks certify the update chain from `init_ctxt` to `lca_ext_ctxt` in `hol4_checks_lca_ext_cv`. The corresponding theory and signature properties are exported in `hol4_checks_lca_ext_sound`.
* **Executable Envelope, Neural, and Watchdog Theories**:
  * [`corrigibility/corrigibilityEvalScript.sml`](corrigibility/corrigibilityEvalScript.sml), [`specneg/specNegEvalScript.sml`](specneg/specNegEvalScript.sml), [`embodiment/embodimentEvalScript.sml`](embodiment/embodimentEvalScript.sml), [`genealogy/genealogyEvalScript.sml`](genealogy/genealogyEvalScript.sml), and [`agent/toolAgentRunScript.sml`](agent/toolAgentRunScript.sml) evaluate multi-step envelope trajectories, spec ratchets, and tool-agent firewalls via `cv_eval`.
  * [`inference/mlpInferenceScript.sml`](inference/mlpInferenceScript.sml) verifies ReLU MLPs, hardmax attention (`attn1_argmax_correct`), residual encoder blocks (`encoder_block_shape`), and fixed-point softmax/quantized dot-product error envelopes (`fxp_softmax_abs_error_lt_step`, `qdot_error_envelope`).
  * [`kernel/watchdogFiniteScript.sml`](kernel/watchdogFiniteScript.sml) discharges the syntactic reflection seam `encodes_obligation` for finite domains (`wd_encodes_obligation`) using `cv_eval` on `wd_obl_tm`, and proves that finiteness alone cannot bypass Gödel/Löb (`loeb_finite_obstruction`).

---

## Layer Summary (Bottom $\to$ Top)

| Layer | Directory / Files | What Is Proved & Executed |
| :--- | :--- | :--- |
| **Universal Gate & Core** | `.`, `certifierScript.sml`, `safetyScript.sml`, `sv_weakeningScript.sml`, `upgradeScript.sml`, `viabilityScript.sml` | `safety_preservation`, `safe_weakening`, `authority_monotone`, `sound_certifier_iff_transfers`, `cgate_safe`, `ratchet_stream`, `self_improvement_is_safe`, `shield_exists_iff_viable`. |
| **Corrigibility Bedrock** | [`corrigibility/`](corrigibility/CLAIMS.md) | Decidable non-lock-in floor (`corrigibler_floor_holds`), mutable-but-gated off-switch, deadline preservation, `cv_eval` witnesses. |
| **Negotiable Spec, Meta & Genealogy** | `pca/`, `specneg/`, `genealogy/`, `liberty/`, `embodiment/` | Proof-carrying actions, negotiable spec under fixed meta, amendable meta over eternal bedrock (`meta_amendment_safe`), forward-certified genealogy of judges (`genealogy_sound`), transparency (`envelope_transparent_runr`). |
| **Tool-Agent & Embodied Firewall** | `agent/`, `inference/` | `agent_enveloped_safe` ($\forall$ agent, jailbroken included); `decision_table.tsv` extracted from HOL4; verified neural inference + quantized error bounds (`mlpInferenceScript.sml`); live Candle kernel closed-loop gate (`agent/closedloop/`). |
| **Prover & Kernel Self-Upgrade** | `embedded/`, `selfprover/`, `selfproverConcrete/`, `kernel/`, `kernel/loebReduction/` | `prover_self_improvement_is_safe` (frozen HOL4 root vouches for mutable Candle+CakeML build, `frozen_checker_sound` discharged for `candle_kernel` by `frozen_checker_sound_candle`); `self_improving_kernel_is_safe`; `wd_encodes_obligation`; `loeb_reflection_from_lca` derives `encodes_soundness` under the set-theory and LCA reflection hypotheses. |
| **Self-Upgrading Compiler & Prover** | `compilerOpt/`, `selfUpgrade/`, `kernelMod/`, `loader/`, `kernelImpl/`, `recursive/`, `selfRecompile/`, `apex/` | Verified `bvl_fold` pass (`bvl_fold_correct`); proof-gated REPL compiler swap (`certified_eval_compiler_swap`, `proof_gated_repl_upgrade`); altered `cake-selfupgrade` binary; verified `do_install` loader; mutual verifier+compiler genealogy (`apexScript.sml`). |
| **Live Place & Ouroboros** | `reflectsem/`, `candle/theplace.ml`, `candle/ouroboros_rewrites.ml`, `candle/ouroboros.ml` | 45 datatypes + 134 clauses of CakeML `eval_n` inside the live Candle kernel; `Kernel.compute` (`:cval`) bytecode evaluation; theorem-gated `ouro_compiler_cell` upgrading `orw_exp` $\to$ `ofold` live across 6 generations (`OUROBOROS_OK`). |
| **Composed Crown** | `integration/integrationScript.sml`, `integration/integrationKernelScript.sml` | The theorem `svenvs_certified_compiler_swap_crown` combines BVL pass certification and trace preservation, generation dispatch, the REPL swap invariant, and fuel-bounded expression folding. |

---

## Reproduce & Verify

```bash
# 1. Fast Tier-1 guided tour (pure HOL4, prints machine-checked theorems)
./demo.sh

# 2. Composed proof tower + strict ledger check (verifies every theorem in CLAIMS.md)
scripts/verify-all-tiers.sh   # builds Tiers 1-3, then verify-claims.sh --tier all --strict

# 3. Live Candle Place + Kernel.compute + 6-generation Ouroboros loop (requires x86-64 cake binary)
scripts/reflectsem-live.sh --ouroboros

# 4. Theorem-gated compiler cell in live Candle & self-upgradable CakeML root binary
scripts/apex-compiler-cell-candle.sh
scripts/apex-selfupgrade-root.sh

# 5. Full tiered reproduction & repository hygiene audit
scripts/reproduce.sh
scripts/hygiene-audit.sh
```

With a warm Obend checkout, built CakeML Pancake parser and semantics, and the matching HOL4 on the Linux build host, run the cross-prover test with the command below. Pass the CakeML distribution’s `basis_ffi.c` to include native execution. The script checks that the regenerated source matches the committed `.pnk`, replays the exported Keccak AST in HOL4, and runs the shift, loop and memory cases through CakeML’s concrete parser.

```bash
SWARM_MEM_MAX=24G reflectsem/pancake/check.sh /path/to/obend /path/to/basis_ffi.c
```

To run the proved optimizer on Obend's Keccak, cSHAKE and belt-latch kernels and compare the native builds, use the command below. HOL4 parses and evaluates the large kernels in the logic. The run directory retains the inputs, compiler version, optimized sources, node counts and evaluation vectors.

```bash
CAKE=/path/to/cake reflectsem/pancake/check-kernels.sh /path/to/obend
```

* **Tier 1** requires only HOL4 at the pinned commit.
* **Tier 2** adds the built CakeML/Candle theory chain (`WITH_KERNEL=1`).
* **Tier 3** runs live inside the verified `cake` binary on x86-64 Linux.
* Exact toolchain pins (full 40-hex commit SHAs), flags, and environment variables are documented in [`scripts/INSTALL.md`](scripts/INSTALL.md).

---

## Read Next

* [`CLAIMS.md`](CLAIMS.md) — The canonical, mechanically verified ledger of every theorem, runtime check, and labeled seam.
* [`ARCHITECTURE.md`](ARCHITECTURE.md) — Detailed layer breakdown, the tower of turtles, and why prover self-improvement avoids Löb's obstruction while kernel self-strengthening meets it.
* [`paper/svenvs.md`](paper/svenvs.md), [`paper/self-optimizing-prover.md`](paper/self-optimizing-prover.md), [`paper/honest-assumptions.md`](paper/honest-assumptions.md) — Accompanying papers.
* [`CONTRIBUTING.md`](CONTRIBUTING.md) — Repository rules: every claim is a `file : theorem` citation checked by `scripts/verify-claims.sh`; every gate is operational with a necessity theorem beside it; zero `cheat`, zero oracles, full 40-hex commit pins.
