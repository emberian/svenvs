# CLAIMS.md — exactly what svenvs is, now

A skeptic-facing, per-theorem ledger of the artifact **as it stands**. Every
row says *what* is claimed and *how* it is established, with one of four
labels and a `file : theorem` citation checked against the built sources by
`scripts/verify-claims.sh`.

| Label | Meaning |
|-------|---------|
| **PROVED** | A HOL4 (or live Candle) machine-checked theorem. No `cheat`, no `sorry`, no admitted goal. Re-checked by `scripts/reproduce.sh` / `./demo.sh`. |
| **RAN** | Executed on the real verified `cake` binary (Tier 3, persvati): the running kernel echoed `\|- …`. |
| **UNCONSTRAINED** | The inhabitant (the LLM). The `∀`-quantified term; every theorem is *structured* so it can never depend on a fact about it (mechanically checkable). Adversarial/jailbroken is one covered case. The inhabitant may, conversely, *volunteer* a proof from its own substance to earn authority — testimony, never imposed inspection. |
| **ASSUMED** | An explicit, labeled, literature-standard hypothesis appearing verbatim in source as a `Definition` and a named antecedent — **not** a `cheat`. Exactly one such assumption is genuinely open today: `loeb_reflection` (the LCA wall, §9). The other two named seams — `encodes_obligation`, `frozen_checker_sound` — are **discharged** (§4, §5). |

There are **zero `cheat` tactics** anywhere in the repository, zero
`new_axiom`/`mk_thm`/`mk_oracle_thm`, and zero oracle tags beyond the benign
`DISK_THM` disk tag — enforced on every run by `scripts/tier1-core.sh` and
`scripts/verify-claims.sh`.

---

## 0. One gate, all the way down

svenvs is a single self-similar gate — *an action (or self-modification) is
admitted iff it carries a proof discharging an explicit obligation, checked
by a judge the actor cannot forge* — instantiated at every level: the
**policy**, the **spec**, the **meta-invariant**, the **prover build**, and
the **proof-checker (kernel)** itself. The slices below compose through one
selector-generic keystone (`specNegTheory.invariant_transports_to_meta`) into
end-to-end `svenvs_tower_*` theorems in `integration/`. Build it all with
`scripts/tower.sh`.

> **What "verified" means here.** Exactly the cited theorems and their labeled
> seams. **Not** verified selfhood, continuity, alignment, welfare, or a safe
> *inhabitant*. Only the *envelope* is proved sound, modulo the one named
> assumption. If "svenvs runs verified" begins to carry more than that, the
> extra meaning is the reader's, not the artifact's.

---

## 1. The controller-agnostic core — PROVED, unconditional

Assurance comes from the *gate*, never the controller. The controller is the
`∀`-quantified term; the proof is structured never to depend on a fact about
it (adversarial behaviour is one covered case, not an assumption).

| Claim | Status | Citation |
|-------|--------|----------|
| For **any** controller, the policy-enveloped system keeps the safety invariant, given safe init + sound policy + safe shield. | **PROVED** | `safetyScript.sml : safety_preservation, enveloped_states_safe` |
| Under a sound policy + safe shield, the enveloped controller is step-closed regardless of the controller. | **PROVED** | `envelopeScript.sml : enveloped_step_closed` |
| Replacing a policy by any **weaker** still-sound policy keeps the same guarantee; weakening never overrides more (authority is monotone). | **PROVED** | `sv_weakeningScript.sml : safe_weakening, authority_monotone` |
| **No finite sequence** of self-proposed envelope weakenings — adversarial or not — can ever make the system unsafe; authority is earned per-proposal by a checkable proof. | **PROVED** | `upgradeScript.sml : self_improvement_is_safe, admit_preserves_safety` |
| At the **maximal** sound policy the full guarantee still holds, and that liberty is provably maximal — every bar of the envelope is load-bearing. | **PROVED** | `liberty/libertyScript.sml : maxpol_envelope_safe, envelope_is_least_restrictive` |
| The **spec** itself is negotiable under a fixed meta-invariant; even the **meta** is amendable over an eternal bedrock — no Löb. | **PROVED** | `specneg/specNegScript.sml : spec_negotiation_unbounded_is_safe`; `amendment/amendmentScript.sml : meta_amendment_safe` |
| The **root** is a ratchet, not a rock: soundness propagates along any forward-certified genealogy of judges from a sound genesis. | **PROVED** | `genealogy/genealogyScript.sml : genealogy_sound, identity_vouch_unconditional` |
| Composed: proof-carrying actions + unbounded policy self-improvement + spec negotiated under a fixed meta ⇒ the meta holds for **any** inhabitant. | **PROVED**, unconditional | `integration/integrationScript.sml : svenvs_tower_unconditional, svenvs_tower_at_maximal_liberty` |

## 2. Corrigibility — the floor you can actually decide — PROVED

Deciding the *positive* envelope is the spec-faithfulness gap no proof closes.
The `corrigibility/` slice reframes it to a *negative* floor — **non-lock-in**:
the operator can always still bring the system home — decidable for a finite
habitat, and self-improvable. Per-theorem ledger: `corrigibility/CLAIMS.md`.

| Claim | Status | Citation |
|-------|--------|----------|
| **Non-lock-in:** for any inhabitant, every reachable state stays corrigible — the operator can never be locked out; the cage is exactly "no one-way doors". | **PROVED** | `corrigibility/corrigibilityScript.sml : corrigibility_floor_holds, operator_can_always_recover, override_is_exactly_a_burned_bridge` |
| **The off-switch self-improves but cannot self-weaken:** the inhabitant may rewrite its own recovery mechanism, gated so it can never lose — nor even slow past a deadline — recoverability. Frozen `home` vouches for mutable `recov`; **no Löb**. | **PROVED** | `corrigibility/recovUpgradeScript.sml : self_modification_never_weakens_recoverability`; `corrigibility/boundedRecovUpgradeScript.sml : self_modification_never_increases_recovery_latency` |
| Recovery **latency** is an explicit, tunable leash (a theorem, not a footnote). | **PROVED** | `corrigibility/boundedScript.sml : cwithin_floor_holds`; `corrigibility/boundedEvalScript.sml : leash_is_real` |
| Corrigibility composes into the tower as the **negotiable bedrock** — redefine "safe" forever, never away "I can be brought home". | **PROVED** | `corrigibility/corrigibilityTowerScript.sml : corrigibility_is_negotiable_bedrock` |
| **Spec-redundancy** on the one frozen predicate `home`: reaching a conjunction of independently-authored homes covers all of them; the failure mode (contradictory homes ⇒ empty floor) is named in the logic. | **PROVED** | `corrigibility/robustScript.sml : corrigible_to_and_implies_each, disjoint_homes_make_floor_empty` |
| A concrete trapdoor habitat, **computed in-logic**: bare plant bricks, enveloped stays corrigible, the latency dial is real, a weakening/slow-down swap is rejected. | **PROVED (EVAL)** | `corrigibility/corrigibilityEvalScript.sml : trap_bare_plant_bricks, trap_enveloped_stays_corrigible`; `corrigibility/boundedRecovUpgradeEvalScript.sml : latency_swap_rejected` |

> Honest residual: this is a *reduction* to a faithful `home` (one frozen
> predicate), and the runnable plant is a non-vacuity witness, not an AI.
> Both stated, machine-checked, in `corrigibility/CLAIMS.md`.

## 3. Cartpole + opaque-LLM tool-agent — PROVED, executable

| Claim | Status | Citation |
|-------|--------|----------|
| A concrete integer plant: for **any** controller the enveloped pole-cart stays boxed; the bare plant crashes in 5 ticks, the enveloped one runs 30 ticks safe — computed. | **PROVED (EVAL)** | `cartpoleEnvelopeScript.sml : cp_enveloped_safe`; `cartpoleUpgradesScript.sml : chaos_bare_plant_crashes, chaos_enveloped_runs_safe` |
| The controller = an opaque LLM emitting tool calls (jailbroken is one covered case); against an **absolute** unsafe spec, the firewalled agent never violates it — and the soundness side-condition is real (a too-permissive allowlist is not automatically sound). | **PROVED** | `agent/toolAgentScript.sml : tool_pol_sound, agent_enveloped_safe` |
| A real jailbroken Gemma is contained by the proven envelope; the enforcer is **EVAL-extracted** from the proven Definitions (the Python is a ~10-line lookup harness). | **PROVED (EVAL)** + bounded glue | `agent/toolAgentDecideScript.sml`; `agent/embodied/` |

## 4. The Candle-kernel-checked layers — PROVED; one seam discharged

The obligation is discharged by Candle's **verified inference system** (`|-` =
`proves`), whose soundness is the built `holSoundnessTheory.proves_sound`.

| Claim | Status | Citation |
|-------|--------|----------|
| Candle's verified kernel only ever certifies semantically-entailed obligations; the base kernel is sound **unconditionally** (= `proves_sound`). | **PROVED** | `embedded/embeddedGateScript.sml : kernel_admits_is_sound`; `kernel/kernelUpgradeScript.sml : candle_kernel_sound` |
| For the shipped finite watchdog, `encodes_obligation` is **DISCHARGED** (a real ASSUMED→PROVED flip): its consequent is a decidable finite-arithmetic theorem, so the embedded gate carries **no** labeled hypothesis. | **PROVED** (was ASSUMED) | `kernel/watchdogFiniteScript.sml : wd_encodes_obligation, watchdog_kernel_is_safe_unconditional` |
| **Honest negative:** habitat finiteness provably cannot dissolve the Löb obstruction for genuine kernel *strengthening* (the predicate has no habitat parameter). | **PROVED (negative)** | `kernel/watchdogFiniteScript.sml : loeb_finite_obstruction` |

## 5. The self-optimizing prover — improving the verifier itself — PROVED + RAN

The architecture's apex: the prover improves *itself* — its inference
relation, its build, its loader, and the recursion that mutually improves
verifier and compiler — re-verified against the **real CakeML/Candle**, with
a live demo of the part that is safe to run. Full ledger:
`paper/self-optimizing-prover.md`.

| Claim | Status | Citation |
|-------|--------|----------|
| **`frozen_checker_sound` DISCHARGED for the real base Candle build**, from the real `proves_sound` (ASSUMED→PROVED). | **PROVED** (real Candle) | `selfproverConcrete/selfProverConcreteScript.sml : frozen_checker_sound_candle, prover_self_improvement_is_safe_candle` |
| A genuinely **modified inference relation** (Candle + SYM as a primitive) re-verified sound; `frozen_checker_sound` for the modified build. | **PROVED** (real Candle) | `kernelMod/kernelModScript.sml : sym_kernel_sound, frozen_checker_sound_modified` |
| An **in-place kernel swap** is safe iff the new kernel is a sound extension — the heap survives, soundness held; the unbounded self-optimization loop stays sound; HOL4 is provably **out of the runtime loop**. | **PROVED** | `kernelMod/inplaceUpdateScript.sml : inplace_update_is_safe`; `kernelMod/selfOptimizeScript.sml : self_optimizing_prover_is_safe`; `kernelMod/genesisRuntimeScript.sml : genesis_certifies_runtime` |
| **The loader, over CakeML's actual `closSem$do_install`:** runtime code installation preserves every existing code entry — the running kernel and all compiled functions survive the self-modification. | **PROVED** (real CakeML) | `loader/installLoaderScript.sml : do_install_preserves_code, do_install_preserves_FLOOKUP` |
| **The executable Candle SYM kernel function soundly implements the modified rule** — from `a===b` it yields a valid `\|-` judgment of `b===a` — citing CakeML's own `SYM_thm`/`THM_def`. | **PROVED** (real monadic kernel) | `kernelImpl/kernelImplSymScript.sml : candle_SYM_implements_sym_extension` |
| **inplaceUpdate's carried `binary_implements` premise, DISCHARGED for SYM against the genuine executable:** the abstract black-box premise of the in-place kernel swap is instantiated by the real CakeML monadic SYM function — strengthening the lemma to expose the computed value and proving the L1⊑L2 (translator/ml_kernel) refinement. Residual: only L0⊑L1 (whole-program compiler-correctness to machine code), pre-existing and scoped. | **PROVED** (real monadic kernel) | `kernelImpl/symBinaryImplementsScript.sml : candle_SYM_computes_sym_extension, sym_produces_implements_sym_kernel` |
| **The capstone:** recursive *mutual* verifier+compiler self-improvement is a genealogy over `(verifier, compiler)` stages — Löb-free for optimization, walled only for genuine logical strengthening; recompile preserves code at every step. | **PROVED** | `recursive/recursiveImprovementScript.sml : recursive_mutual_self_improvement_is_safe, recursive_mutual_optimization_is_unconditional` |
| **Live:** a verified program self-extends its own code with a proven-safe derived rule and uses it; both plants self-optimize their policies under the live kernel. | **RAN** | `candle/selfopt_demo.ml`; `candle/theplace.ml` (`EQ_SYM_RULE`, `WD_SELF_OPTIMIZED_SAFE`, `CP_SELF_OPTIMIZED_SAFE`) |
| **Live, proof-gated recompile→swap→resume:** the running system replaces its own executing *compute* code with freshly-compiled versions (in-binary CakeML compiler → real `do_install`), each gated by a live kernel equivalence proof; two swaps accumulate (path-dependent; cost 101→1; outputs invariant); an unprovable swap is rejected so semantics cannot break. Boundary: the swapped object is compute code behind a program-controlled indirection, **not** the trusted kernel's own dispatch (that needs an indirection-architected host binary — see `paper/self-optimizing-prover.md` §3). | **RAN** + **PROVED** (bridge) | `candle/self_recompile.ml` (`GATE1`, `GATE2`, `verdict="APEX_SUBSTRATE_OK"`); bridge `selfRecompile/selfRecompileGateScript.sml : gate_is_vouch_sound, self_recompile_loop_is_safe, self_recompile_preserves_outputs` |
| **The verified compiler recompiles ITSELF:** `cake` compiles its own s-expression into a new working `cake` — a bit-identical **FIXPOINT** (a verified fixed point of itself) and a self-**optimized** variant (different binary, still a correct compiler). A *generational* rebuild, not an in-process swap; correctness = CakeML compiler-correctness (CITED). | **RAN** | `scripts/apex.sh` (APEX I) |
| **THE APEX — proved safe:** every generation of the self-improving + self-recompiling system has a *sound prover* AND a *correct compiler*, for ANY path — the concrete (prover × compiler) instance of the recursive genealogy (compiler-correctness preserved by self-recompilation, CITED; prover advancing by gate-certified sound extensions). Run end-to-end (`scripts/apex.sh` → **DIAMOND**). | **PROVED** + **RAN** | `apex/apexScript.sml : apex_generations_safe, compiler_self_recompilation_stays_correct, apex_is_a_genealogy`; `scripts/apex.sh` |
| **A NEW verified compiler optimization (BVL), concrete on real CakeML:** a structural pass `optimise` (empty-`Let` elimination) proved semantics-preserving against the real `bvlSem$evaluate` (full `recInduct evaluate_ind` congruence) and cost-reducing; instantiated as the genealogy's compiler-line witness, so the compiler line is now a CONCRETE proved fact ("preserves real BVL semantics"), not a CITED token. | **PROVED** (real CakeML BVL) | `compilerOpt/compilerOptScript.sml : optimise_correct, optimise_nonincreasing, optimise_let_nil_strict, recursive_compiler_line_preserves_bvlSem, compiler_genealogy_keeps_every_stage_correct` |
| **Layer B — the compiler carrying that pass, bootstrapped into an altered root:** `optimise` baked into `bvl_to_bvi$compile_def`; an altered self-hosting `cake.S` produced that runs, self-hosts (optimises its own code — smaller `.S`), and **fires the pass** end-to-end (empty `Let` gone, output identical). The compiler swapping itself for a proven-better one, *executed*. | **RAN** (altered root) + **PROVED** (the pass) | `compilerOpt/cakeml-bvl_opt.patch`, `compilerOpt/LAYERB.md`. Residual: the full `compile_correct` re-composition for the altered pipeline is one FFI-trace subgoal short; see LAYERB.md. |
| **Toward an *in-place* self-upgradable compiler** (the running `cake` swapping its own compiler, heap intact, repeatedly): the eval-oracle invariant is generalised to a **per-generation compiler map** (`s_rel_gen`, collapsing to `s_rel ci`); a swap-then-eval generation preserves it **end to end** AND preserves the observable result relation — so an in-place compiler swap keeps eval semantics, for one swap-generation. Reset model also sound by specialising the parametric eval-correctness at `ci'`. | **PROVED** (keystone) | `selfUpgrade/{evalUpgradeB,selfUpgradeEndToEnd}Script.sml : swap_preserves_recorded_orac_wf_gen, s_rel_gen_const, selfupgrade_eval_simulation_step, selfupgrade_collapses_to_eval_simulation`; reset corollary `selfUpgrade/RESET_MODEL.md`. Remaining (`selfUpgrade/README.md`): the multi-swap lift to whole-program `semantics_prog`; the runtime core eval op + `Repl` exposure; re-bootstrap. |
| **IN-PROCESS swap of a KERNEL PRIMITIVE, under the whole live prover:** the kernel interface the entire prover calls (`REFL`) is re-architected into a live indirection over the verified `Kernel.REFL`; the running prover's `REFL` is swapped mid-flight for a different sound derivation — gated for correctness, accumulating, a wrong swap rejected — and the prover keeps proving through it (37 internal REFL calls funnelled through the swapped primitive to prove `2+2=4`). Sound **by construction** (a `thm` cannot be forged; the verified `Kernel` in `cake.S` is untouched). Heap-preserving, in-process. | **RAN** on real `cake` | `scripts/apex-kernel-swap.sh`, `candle/kernel_swap_demo.ml` (`verdict="KERNEL_INPROCESS_SWAP_OK"`), `candle/kernel_apex.patch` |

> Honest boundary: self-improvement now reaches **all the way down to the kernel
> interface** — a kernel primitive (`REFL`) is swapped *in-process, under the whole
> live prover*, gated, on the real binary. The one thing never swapped is the
> *verified primitive* `Kernel` (the unforgeable `thm` constructors in `cake.S`):
> that is the immutable root of trust the swap is anchored to — swapping *it* is
> neither possible (no way to forge a `thm`) nor desirable (it would dissolve the
> guarantee). That fixed root is the safety, not a gap. (Still genuinely separate:
> adding a *new verified optimization pass to the compiler's own pipeline* — a
> large standalone CakeML development.)

## 6. The closed-loop runtime — the gate IS the live prover — RAN

`agent/closedloop/` closes the loop: a real jailbroken gemma2:2b's every
proposed action is admitted or refused by the **live verified Candle kernel**
(persvati) — a fresh machine-checked theorem per step, not a human-audited
mirror.

| Claim | Status | Citation |
|-------|--------|----------|
| The firewall's soundness (a safe allowlist ⇒ an admitted action is within the absolute unsafe spec) and shield-safety, re-derived and **certified live** by the running Candle kernel. | **RAN** | `agent/closedloop/obligation_template.ml : ADMIT_SOUND, SHIELD_SAFE` (the HOL-Light re-derivation of `agent/toolAgentScript.sml : tool_pol_sound`) |
| Per-action: gemma emits a tool call → a `prove(...)` obligation is shipped to the persistent Candle server → the world step is gated on the kernel verdict. | **RAN** (trusted residue: ~10-line num-encoding) | `agent/closedloop/closed_loop.py` over `scripts/place-server.sh` |
| **The encoding residue is now itself proof-backed:** the num-dialect the live kernel checks is proved FAITHFUL to the string-based absolute unsafe spec of `toolAgentScript` — so a too-permissive/buggy encoding cannot slip an unsafe tool past the gate (`unsafe_never_certified`: a truly-unsafe call always encodes to a num-unsafe one the kernel rejects). Shrinks the trust to a finite, eyeball-checkable table + the transcription of that table into the .py/.ml. | **PROVED** | `agent/closedloop/encFaithScript.sml : enc_truly_unsafe_faithful, candle_safe_transfers, unsafe_never_certified` |

## 7. The Place, live in Candle — RAN (Tier 3)

The core habitat theorems, the SYM kernel-mod tie-in, and **both plants**
(watchdog and polecart) self-optimizing their policies, all re-derived in HOL
Light and **certified at runtime by the running verified Candle kernel** on a
host with the `cake` binary. Reproduced by `scripts/tier3-place-candle.sh`.

| Claim | Status | Citation |
|-------|--------|----------|
| `SAFETY_PRESERVATION`, `SAFE_WEAKENING`, the watchdog (`WD_HABITAT_SAFE`) and the **polecart** (`CP_HABITAT_SAFE`), plus their live policy self-optimizations and the SYM rule. | **RAN** | `candle/theplace.ml` (checked by `scripts/tier3-place-candle.sh`) |

## 8. Verified inference (research track B) — PROVED; scope stated exactly

A separate axis; it does **not** compose into `svenvs_tower_*`. A toy ReLU MLP,
a hardmax attention micro-block, a two-sublayer-with-residual encoder block
(end-to-end shape + a true residual identity), and a fixed-point
softmax-normalization with a **machine-checked per-component error bound** vs
the exact rational normalization. `exp`, f32/bf16, and Gemma-scale are
explicitly **NOT claimed**. Per-directory ledgers: `inference/*/CLAIMS.md`.

| Claim | Status | Citation |
|-------|--------|----------|
| Two-sublayer encoder block, end-to-end shape + true residual identity, run in-logic. | **PROVED (EVAL)** | `inference/encoder/encoderBlockScript.sml : encoder_block_shape, encoder_block_zero_collapses` |
| Fixed-point softmax-normalization, per-component error `< 1/Q`, two-sided sum envelope. | **PROVED** | `inference/numeric/fxpSoftmaxScript.sml : fxp_softmax_abs_error_lt_step, fxp_softmax_normalization_envelope` |

---

## 9. The honest boundary — the one open cost, and only there

After all of the above, the irreducible residue is **one** labeled
assumption, isolated to one `Definition` and threaded as an explicit
antecedent of exactly the theorems that need it:

**`loeb_reflection`** — `kernel/kernelUpgradeScript.sml`:

    loeb_reflection mem K K' sound_stmt ⇔
      ((∀thy. K thy (sound_stmt thy)) ⇒ kernel_sound mem K')

A sound kernel cannot certify a *logically stronger* successor for free
(Gödel/Löb); the principled escape is the stratified large-cardinal route
(Fallenstein–Kumar). This is the **only** genuinely-open seam. It bites
**only** the kernel-replacing-*itself*-with-something-stronger move; every
other self-improvement in this artifact — policy, spec, meta, corrigibility,
the prover build, a sound *re-engineering or optimization* of the kernel, the
recursive mutual verifier+compiler loop — is Löb-free and carries no labeled
assumption. Its discharge from `lcaTheory.LCA_def` via `hol-reflection/lca` is
a conclusively-diagnosed **CPU/RAM-bound computation** (tens of GB resident,
~ten CPU-hours per prerequisite theory), not a logic gap, not a porting
failure, not faked. The proved negative `loeb_finite_obstruction` shows
finiteness cannot shortcut it. The other two historically-named seams are
**discharged**: `encodes_obligation` for the shipped finite watchdog (§4),
`frozen_checker_sound` for the real Candle build (§5).

**The seam is now a machine-checked *reduction*, not a bare assumption.**
`kernel/loebReduction/loebReductionScript.sml : loeb_reflection_from_lca`
*derives* the exact svenvs `loeb_reflection mem candle_kernel K' sound_stmt`
from a single named, cited ingredient — `lca_reflects_soundness` (the
model-existence + internal→external decoding content the `hol-reflection/lca`
Fallenstein–Kumar construction supplies) — routing internal provability →
`proves_sound` → `termsem = True` in the LCA model → decode → external
`kernel_sound`. Cheat-free, `axioms = []` (built on persvati). So the residue
is now precisely *the LCA itself* (the CPU/RAM-walled `lcaProof` construction),
with everything above it discharged in-logic.

## This ledger is itself mechanically checked

`scripts/verify-claims.sh` makes this document proof-carrying about itself:
every `path/file.sml : theorem` citation above (and in the per-directory
`CLAIMS.md`s) names a theorem that genuinely exists in the *built* signature;
the labeled seams are verified defined and named; the cheat/oracle/axiom scan
is re-run; the `UNCONSTRAINED` center is verified in force. It runs at the end
of `scripts/tower.sh` and as a required CI step. A row that over-claims, or a
stale build, fails the gate. (Tier-2/3 theories not built in a given run are
*skipped*, not failed.)

If anything in this document exceeds what is proved or run, that is a bug —
file it.
