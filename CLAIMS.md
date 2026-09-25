# CLAIMS.md — exactly what svenvs is, now

A skeptic-facing, per-theorem ledger of the artifact **as it stands**. Every
row says *what* is claimed and *how* it is established, with one of five
labels and a `file : theorem` citation checked against the built sources by
`scripts/verify-claims.sh`.

| Label | Meaning |
|-------|---------|
| **PROVED** | A HOL4 (or live Candle) machine-checked theorem. No `cheat`, no `sorry`, no admitted goal. Re-checked by `scripts/reproduce.sh` / `./demo.sh`. |
| **RAN** | Executed on the real verified `cake` binary (Tier 3, persvati): the running kernel echoed `\|- …`. |
| **TRUSTED-GLUE** | Small, bounded, auditable non-proof code, named in the row that uses it (e.g. the ~10-line lookup harness in `agent/embodied/`, the closed-loop num-encoding transcription in §6). It sits outside every theorem, yet the running system's match to the theorem depends on it, so it is kept small enough to read by eye. |
| **UNCONSTRAINED** | The inhabitant (the LLM). The `∀`-quantified term; every theorem is *structured* so it can never depend on a fact about it (mechanically checkable). Adversarial/jailbroken is one covered case. The inhabitant may, conversely, *volunteer* a proof from its own substance to earn authority — testimony, never imposed inspection. |
| **ASSUMED** | An explicit, labeled, literature-standard hypothesis appearing verbatim in source as a `Definition` and a named antecedent — **not** a `cheat`. No kernel-upgrade *principle* is assumed: `loeb_reflection` is a derived notion, a consequence of the certifying kernel's soundness plus the encoding seam `encodes_soundness`. What remains open is one **witness not yet constructed** — a Candle derivation together with an LCA-produced `encodes_soundness` certificate for a strictly stronger kernel — beside the theorem that says it suffices (§9). The other two named seams — `encodes_obligation`, `frozen_checker_sound` — are **discharged** (§4, §5). Every gate that carries one of these seams is *operational* (it installs iff the certifier said yes), so each seam is load-bearing, and each has a machine-checked necessity theorem showing the conclusion fails without it (§1, §4, §5, §9). An opt-in fourth, `attestation_faithful`, is carried only by the testimony channel, never by the floor (§9). |

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
> *inhabitant*. Only the *envelope* is proved sound, modulo the labeled
> assumptions, and one soundness witness not yet constructed (§9). If "svenvs runs verified" begins to carry more than that, the
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
| Replacing a policy by any **weaker** still-sound policy keeps the same guarantee **and** takes no authority away (wherever the controller acted freely before, it still does); the weakening premise is necessary for the second half. | **PROVED** | `sv_weakeningScript.sml : safe_weakening, authority_monotone, safe_weakening_needs_weaker` |
| **No finite sequence** of self-proposed envelope weakenings — adversarial or not — can ever make the system unsafe; authority is earned per-proposal by a checkable proof. | **PROVED** | `upgradeScript.sml : self_improvement_is_safe, admit_preserves_safety` |
| The **operational gate** `gate cert oldp newp` installs iff the certifier said yes: soundness of the certifier's yes is exactly what protects safety (single step and unbounded stream), and a certified stream only grows authority; `admit`/`admit_all` are its oracle-certifier special case. Necessity: one unsound yes breaches safety; a yes to a non-weakening revokes authority. | **PROVED** | `upgradeScript.sml : gate_preserves_safety, certified_gate_correct, gated_self_improvement_is_safe, certified_stream_grows_authority, admit_is_gate, admit_all_is_gate_all, unsound_certificate_breaches, unweakening_certificate_revokes_authority, sound_certifier_iff_policy_gate_safe, gate_keeps_sound_iff, gate_all_keeps_sound_iff` |
| **One certifier theory, proved once:** a certifier is sound iff its yes transfers to every fact the obligation faithfully encodes, iff the gate it drives keeps the judge (given a good and a bad point), iff every certified stream stays good; every gate in this artifact is `cgate` and every succession a `ratchet`, and the layers' gate theorems are one-line instances (policy, embedded kernel, upgraded kernel, prover build, genealogy, self-recompile loop, Apex compiler line). | **PROVED** | `certifierScript.sml : sound_certifier_iff_transfers, cgate_safe, sound_certifier_iff_cgate_safe, ratchet_stream, ratchet_stream_iff, sound_certifier_iff_stream_safe, cgate_run_safe, cgate_run_safe_iff` |
| At the **maximal** sound policy the full guarantee still holds, and that liberty is provably maximal — every bar of the envelope is load-bearing — given a safe shield, which exists iff `safe` is viable (`viabilityScript.sml : shield_exists_iff_viable`). | **PROVED** | `liberty/libertyScript.sml : maxpol_envelope_safe, envelope_is_least_restrictive` |
| `safe_shield` is exactly **viability**: a safe shield exists iff every safe state lies in the viability kernel (the greatest controlled-invariant subset of `safe`); when `safe` is not fully viable, the kernel always has a shield and an envelope sound for the kernel keeps `safe`. | **PROVED** | `viabilityScript.sml : viable_is_controlled_inv, viable_greatest, shield_exists_iff_viable, safe_shield_iff_chooses_viable, viability_kernel_envelope` |
| Under viability the operational gate is **characterized**: the certifier's yes being sound is necessary and sufficient for the gated envelope to be safe for every init, shield, old policy and controller; upgrade's necessity witness is a corollary, and viability cannot be dropped (a doomed state makes the iff fail). | **PROVED** | `viabilityScript.sml : gate_certificate_iff, unsound_certificate_breaches_general, gate_iff_needs_viability` |
| **Minimal intervention:** every sound envelope with a safe shield overrides every unsafe action; at the maximal policy it overrides exactly the unsafe ones, least among sound policies, and weakening only reduces overrides; a controller that is safe on its own is never overridden and its enveloped run is its bare run. Each hypothesis has a counterexample. | **PROVED** | `liberty/transparencyScript.sml : sound_policy_intervenes_on_unsafe, maxpol_intervenes_iff_unsafe, maxpol_intervenes_least, intervention_monotone, envelope_transparent, envelope_transparent_run, envelope_transparent_iff` |
| **The plant may be nondeterministic or adversarial** (`stepr : 's -> 'a -> 's -> bool`): the envelope keeps its guarantee for every controller against every successor, and the deterministic theory is a proven instance (`det step`), with thirteen existing theorems re-derived alpha-identically as `*_from_rel`. | **PROVED** | `relEnvelopeScript.sml : safety_preservationr, enveloped_states_safer, safety_preservationr_tight, sound_policyr_det, safety_preservation_from_rel, safe_weakening_from_rel, gate_preserves_safety_from_rel, certified_gate_correct_from_rel`; `relSystemScript.sml : reachr_det, invariantr_det, invariant_intro_from_rel` |
| Blocked actions and many successors: safety needs no totality, not getting stuck needs liveness (five counterexamples, one per hypothesis); soundness must hold for **every** successor, the angelic reading is insufficient. | **PROVED** | `relEnvelopeScript.sml : sound_policyr_blocked, safe_shieldr_blocked, enveloped_nonblocking, enveloped_nonblocking_tight, enveloped_nonblocking_total, angelic_soundness_insufficient, angelic_soundr_det` |
| Weakening and the certified gate over relations, with their necessity witnesses carried through `det`. | **PROVED** | `relEnvelopeScript.sml : safe_weakeningr, safe_weakeningr_needs_weaker, gate_preserves_safetyr, certified_gate_correctr, certifier_gate_preserves_safetyr, unsound_certificate_breachesr` |
| **Robustness:** the relational run under a disturbance set is exactly the set of runs under every admissible disturbance sequence, so the envelope is safe for every controller and every sequence; nominal soundness is insufficient; the deterministic plant is the trivially disturbed one. | **PROVED** | `relEnvelopeScript.sml : reachr_disturbed_iff_drun, robust_safety_preservation, robust_envelope, nominal_soundness_insufficient, det_is_disturbed` |
| Viability over relations: a safe *and live* shield exists iff every safe state is viable (enabledness is required, or a deadlock would count as safe forever); the demonic reading is the right one; deterministic collapse. | **PROVED** | `relViabilityScript.sml : shield_exists_iff_viabler, shield_exists_iff_viabler_total, shield_exists_iff_viabler_needs_live, viabler_demonic, viabler_det, shield_exists_iff_viable_from_rel` |
| Minimal intervention over relations: the maximal policy overrides exactly the actions that *may* go unsafe, least among sound policies; a controller whose bare relational run is safe is never overridden. | **PROVED** | `liberty/relTransparencyScript.sml : maxpolr_is_greatest_sound, maxpolr_intervenes_iff_unsafe, envelope_transparent_runr, envelope_transparent_iffr, envelope_transparent_run_from_rel` |
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
| A real jailbroken Gemma is contained by the proven envelope; the enforcer is **EVAL-extracted** from the proven Definitions (the Python is a ~10-line lookup harness). | **PROVED (EVAL)** + **TRUSTED-GLUE** (the ~10-line lookup harness) | `agent/toolAgentDecideScript.sml`; `agent/embodied/` |

## 4. The Candle-kernel-checked layers — PROVED; one seam discharged

The obligation is discharged by Candle's **verified inference system** (`|-` =
`proves`), whose soundness is the built `holSoundnessTheory.proves_sound`.

| Claim | Status | Citation |
|-------|--------|----------|
| Candle's verified kernel only ever certifies semantically-entailed obligations; the base kernel is sound **unconditionally** (= `proves_sound`). | **PROVED** | `embedded/embeddedGateScript.sml : kernel_admits_is_sound`; `kernel/kernelUpgradeScript.sml : candle_kernel_sound` |
| The **embedded gate** installs a proposal iff Candle *derived* its obligation term (`kernel_gate`); safety holds for every controller given the faithful encoding, because `proves_sound` makes a derivation valid. Necessity: Candle genuinely derives a term (x = x in the initial context) that does not encode the obligation, and the gate breaches. | **PROVED** | `embedded/embeddedGateScript.sml : embedded_admit_preserves_safety, embedded_admit_installs, embedded_gate_rejects, candle_refl_witness, unfaithful_encoding_can_breach, kernel_admits_sound_certifier` |
| Soundness is exactly transfer: a kernel's yes transfers to every fact the term faithfully encodes. A policy upgrade decided by an **upgraded kernel** `K'` (`kgate`) is safe iff `K'` is sound: a kernel is sound exactly when the gate it drives is safe for every faithfully-encoded proposal; any certificate of a non-valid obligation breaches. | **PROVED** | `kernel/kernelUpgradeScript.sml : kernel_sound_is_sound_certifier, kernel_sound_iff_transfers, sound_kernel_certifies_admissible, upgraded_kernel_preserves_safety, upgraded_kernel_installs, kernel_sound_iff_gate_safe, kernel_unsound_certificate_can_breach` |
| Kernel self-upgrade needs **no principle**: a Candle derivation of a term encoding `K'`'s soundness makes `K'` sound; a soundness witness suffices — and, the trap stated as a theorem, *having* one is equivalent to `K'` being sound, so the content is the encoding certificate's provenance (§9). | **PROVED** | `kernel/kernelUpgradeScript.sml : encodes_soundness, sound_kernel_lifts_soundness, candle_lifts_soundness, loeb_reflection_from_soundness, witness_suffices, soundness_witness_iff_sound, sound_kernel_encoded_by_every_term` |
| For the shipped finite watchdog, `encodes_obligation` is **DISCHARGED** (a real ASSUMED→PROVED flip): its consequent is a decidable finite-arithmetic theorem, so the operational embedded gate carries **no** labeled hypothesis. Safety holds on both branches because both watchdog policies are sound — so it holds whichever kernel decides, even an unsound one. | **PROVED** (was ASSUMED) | `kernel/watchdogFiniteScript.sml : wd_encodes_obligation, watchdog_kernel_is_safe_unconditional, watchdog_self_improving_kernel_safe_unconditional` |
| **Honest negative:** habitat finiteness provably cannot dissolve the Löb obstruction for genuine kernel *strengthening*: with every watchdog fact and a genuine Candle certificate present, a strictly stronger kernel extending Candle's has no soundness witness at all (it is unsound). Finiteness supplies no witness; it does not refute one for a sound `K'`. | **PROVED (negative)** | `kernel/watchdogFiniteScript.sml : loeb_finite_obstruction` |

## 5. The self-optimizing prover — improving the verifier itself — PROVED + RAN

The architecture's apex: the prover improves *itself* — its inference
relation, its build, its loader, and the recursion that mutually improves
verifier and compiler — re-verified against the **real CakeML/Candle**, with
a live demo of the part that is safe to run. This table is the canonical
ledger; the narrative (the question, the one Löb, where execution stops) and
the supporting lemmas are in `paper/self-optimizing-prover.md`.

| Claim | Status | Citation |
|-------|--------|----------|
| The **prover gate** installs a policy upgrade iff the frozen HOL4 root accepted the proposed build `B'` and `B'` said yes; safety holds given `frozen_checker_sound` and the build's faithfulness, both load-bearing (necessity: an unsound checker, or an unfaithful vouched build, breaches); an unvouched build is inert whatever it says. | **PROVED** | `selfprover/selfProverScript.sml : prover_self_improvement_is_safe, prover_self_improvement_installs, unvouched_prover_swap_is_inert, unsound_frozen_checker_can_breach, uncertified_build_can_breach, prover_then_unbounded_policy_self_improvement_is_safe, prover_swap_then_safe_weakening, frozen_checker_sound_iff_prover_gate_safe, frozen_checker_sound_iff_sound_certifier` |
| **`frozen_checker_sound` DISCHARGED for the real base Candle build**, from the real `proves_sound` (ASSUMED→PROVED); through the prover gate only the Candle build's own faithfulness remains. | **PROVED** (real Candle) | `selfproverConcrete/selfProverConcreteScript.sml : frozen_checker_sound_candle, prover_self_improvement_is_safe_candle` |
| A genuinely **modified inference relation** (Candle + SYM as a primitive) re-verified sound; `frozen_checker_sound` for the modified build. | **PROVED** (real Candle) | `kernelMod/kernelModScript.sml : sym_kernel_sound, frozen_checker_sound_modified` |
| An **in-place kernel swap** is safe iff the new kernel is a sound extension — the heap survives, soundness held; the unbounded self-optimization loop stays sound; HOL4 is provably **out of the runtime loop**. | **PROVED** | `kernelMod/inplaceUpdateScript.sml : inplace_update_is_safe`; `kernelMod/selfOptimizeScript.sml : self_optimizing_prover_is_safe`; `kernelMod/genesisRuntimeScript.sml : genesis_certifies_runtime` |
| **The loader, over CakeML's actual `closSem$do_install`:** runtime code installation preserves every existing code entry — the running kernel and all compiled functions survive the self-modification. | **PROVED** (real CakeML) | `loader/installLoaderScript.sml : do_install_preserves_code, do_install_preserves_FLOOKUP` |
| **The executable Candle SYM kernel function soundly implements the modified rule** — from `a===b` it yields a valid `\|-` judgment of `b===a` — citing CakeML's own `SYM_thm`/`THM_def`. | **PROVED** (real monadic kernel) | `kernelImpl/kernelImplSymScript.sml : candle_SYM_implements_sym_extension` |
| **inplaceUpdate's carried `binary_implements` premise, DISCHARGED for SYM against the genuine executable:** the abstract black-box premise of the in-place kernel swap is instantiated by the real CakeML monadic SYM function — strengthening the lemma to expose the computed value and proving the L1⊑L2 (translator/ml_kernel) refinement. Residual: only L0⊑L1 (whole-program compiler-correctness to machine code), pre-existing and scoped. | **PROVED** (real monadic kernel) | `kernelImpl/symBinaryImplementsScript.sml : candle_SYM_computes_sym_extension, sym_produces_implements_sym_kernel` |
| **The capstone:** recursive *mutual* verifier+compiler self-improvement is a genealogy over `(verifier, compiler)` stages — Löb-free for optimization, walled only for genuine logical strengthening; recompile preserves code at every step. | **PROVED** | `recursive/recursiveImprovementScript.sml : recursive_mutual_self_improvement_is_safe, recursive_mutual_optimization_is_unconditional` |
| **Live:** a verified program self-extends its own code with a proven-safe derived rule and uses it; both plants self-optimize their policies under the live kernel. | **RAN** | `candle/selfopt_demo.ml`; `candle/theplace.ml` (`EQ_SYM_RULE`, `WD_SELF_OPTIMIZED_SAFE`, `CP_SELF_OPTIMIZED_SAFE`) |
| **Live, proof-gated recompile→swap→resume:** the running system replaces its own executing *compute* code with freshly-compiled versions (in-binary CakeML compiler → real `do_install`), each gated by a live kernel equivalence proof; two swaps accumulate (path-dependent; cost 101→1; outputs invariant); an unprovable swap is rejected so semantics cannot break. Boundary: the swapped object is compute code behind a program-controlled indirection, not the kernel; the kernel-interface swap is the `REFL` row below. | **RAN** + **PROVED** (bridge) | `candle/self_recompile.ml` (`GATE1`, `GATE2`, `verdict="APEX_SUBSTRATE_OK"`); bridge `selfRecompile/selfRecompileGateScript.sml : gate_is_vouch_sound, loop_is_a_genealogy, self_recompile_loop_is_safe, self_recompile_preserves_outputs, uncertified_swap_is_not_a_step, unsound_certificate_breaks_loop, cert_sound_iff_loop_safe, candle_run_modelled` (the operational swap loop, safe under the carried `cert_sound` premise, which is shown necessary; the candle run is replayed in-logic) |
| **The verified compiler recompiles ITSELF:** `cake` compiles its own s-expression into a new working `cake` — a bit-identical **FIXPOINT** (a verified fixed point of itself) and a self-**optimized** variant (different binary, still a correct compiler). A *generational* rebuild, not an in-process swap; correctness = CakeML compiler-correctness (CITED). | **RAN** | `scripts/apex.sh` (APEX I) |
| **THE APEX — proved safe:** every generation of the self-improving + self-recompiling system has a *sound prover* AND a *correct compiler*, for ANY path — the concrete (prover × compiler) instance of the genealogy: the Apex vouching is proved `vouch_sound` for the Apex judge and the Apex succession `forward_certified`, so `genealogy_sound` applies (compiler-correctness preserved by self-recompilation, CITED; prover advancing by gate-certified sound extensions). Run end-to-end (`scripts/apex.sh` → **DIAMOND**). | **PROVED** + **RAN** | `apex/apexScript.sml : apex_is_a_genealogy, apex_vouch_sound, apex_forward_certified, apex_generations_safe, compiler_self_recompilation_stays_correct`; `scripts/apex.sh` |
| **A NEW verified compiler optimization (BVL), concrete on real CakeML:** a structural pass `optimise` (empty-`Let` elimination) proved semantics-preserving against the real `bvlSem$evaluate` (full `recInduct evaluate_ind` congruence) and cost-reducing; instantiated as the genealogy's compiler-line witness, so the compiler line is now a CONCRETE proved fact ("preserves real BVL semantics"), not a CITED token. | **PROVED** (real CakeML BVL) | `compilerOpt/compilerOptScript.sml : optimise_correct, optimise_nonincreasing, optimise_let_nil_strict, recursive_compiler_line_preserves_bvlSem, compiler_genealogy_keeps_every_stage_correct` |
| **Layer B — the compiler carrying that pass, bootstrapped into an altered root:** `optimise` baked into `bvl_to_bvi$compile_def`; an altered self-hosting `cake.S` produced that runs, self-hosts (optimises its own code — smaller `.S`), and **fires the pass** end-to-end (empty `Let` gone, output identical). The compiler swapping itself for a proven-better one, *executed*. | **RAN** (altered root) + **PROVED** (the pass) | `compilerOpt/cakeml-bvl_opt.patch`, `compilerOpt/LAYERB.md`. Residual: the full `compile_correct` re-composition for the altered pipeline is one FFI-trace subgoal short; see LAYERB.md. |
| **Toward an *in-place* self-upgradable compiler** (the running `cake` swapping its own compiler, heap intact, repeatedly): the eval-oracle invariant is generalised to a **per-generation compiler map** (`s_rel_gen`, collapsing to `s_rel ci`); a swap-then-eval generation preserves it **end to end** AND preserves the observable result relation — so an in-place compiler swap keeps eval semantics, for one swap-generation. The keystone is then **iterated over a schedule of arbitrarily many in-place swaps** by induction on the schedule (`selfupgrade_multi_swap_simulation`: whole N-swap run preserves `s_rel_gen` to the fully-swapped map at the last active compiler, and preserves the observable result), with the conservative whole-program collapse (`selfupgrade_oracle_semantics_prog_collapse`). The op is then made **concrete and exposed**: `do_eval_record_gen g2c` is an actual `custom_do_eval` value (the field `EvalOracle` already carries — no core-semantics edit) that dispatches the compiler by the calling env's generation; it strictly generalises CakeML's `do_eval_record` (`do_eval_record_gen_const`) and a step PRESERVES the per-generation invariant operationally (`do_eval_record_gen_preserves_wf`). The exposed upgrade entry point `repl_upgrade ci' gen_now` (install `ci'` for the next generation) is sound (`repl_upgrade_preserves_recorded_orac_wf_gen`). And the heap-preserving **reset-model** upgrade is machine-checked against the real backend: a program run from the upgraded state is governed by eval-correctness at `ci'` (`eval_upgrade_preserves_semantics`). | **PROVED** (keystone + multi-swap lift + concrete op/expose + reset against real backend) | `selfUpgrade/{evalUpgradeB,selfUpgradeEndToEnd}Script.sml : swap_preserves_recorded_orac_wf_gen, s_rel_gen_const, selfupgrade_eval_simulation_step, selfupgrade_collapses_to_eval_simulation`; `selfUpgrade/selfUpgradeMultiSwapScript.sml : selfupgrade_multi_swap_simulation, selfupgrade_oracle_semantics_prog_collapse`; `selfUpgrade/evalUpgradeOpScript.sml : do_eval_record_gen_const, do_eval_record_gen_preserves_wf, repl_upgrade_preserves_recorded_orac_wf_gen`; `selfUpgrade/evalUpgradeResetScript.sml : eval_upgrade_preserves_semantics` (all `DISK_THM`, no oracles). Remaining (`selfUpgrade/README.md`): carry the op as the running `EvalDecs` root — re-bootstrap (the patched root is BUILT; see the self-upgradable ROOT row below). The *strictly* multi-compiler whole-program `semantics_prog` needs a per-generation meta-compiler `do_eval` (a CakeML-semantics change not made); multi-compiler content lives at the `evaluate_decs` level, closed for arbitrarily many swaps. |
| **IN-PROCESS swap of a KERNEL PRIMITIVE, under the whole live prover:** the kernel interface the entire prover calls (`REFL`) is re-architected into a live indirection over the verified `Kernel.REFL`; the running prover's `REFL` is swapped mid-flight for a different sound derivation — gated for correctness, accumulating, a wrong swap rejected — and the prover keeps proving through it (37 internal REFL calls funnelled through the swapped primitive to prove `2+2=4`). Sound **by construction** (a `thm` cannot be forged; the verified `Kernel` in `cake.S` is untouched). Heap-preserving, in-process. | **RAN** on real `cake` | `scripts/apex-kernel-swap.sh`, `candle/kernel_swap_demo.ml` (`verdict="KERNEL_INPROCESS_SWAP_OK"`), `candle/kernel_apex.patch` |
| **The verified per-generation compiler self-upgrade, RUNNING on real `cake`:** the structure proved sound in `selfUpgrade/evalUpgradeOpScript.sml` (the per-generation compiler map = `cmap`/g2c, the `agree` gate = `compiler_agrees`, `upgrade` = `repl_upgrade`) is compiled by the verified `cake` to native x86-64, linked, and EXECUTED — an in-place compiler upgrade keeps the OBSERVABLE identical while the compiled output improves (gen 0 → 15, gen 1 → 10 for the same source), an earlier generation keeps its own compiler (`repl_upgrade_no_op_below`), a non-agreeing claimed compilation is REJECTED by the gate (semantics protected), and upgrades ACCUMULATE (a third compiler at gen 2; a 64-generation bulk run), path-dependent. | **RAN** on real `cake` (native) | `scripts/apex-compiler-cell.sh`, `candle/compiler_cell_upgrade.cml` (sentinels `COMPILER_CELL_UPGRADE_OK`, `BULK_UPGRADES_OK`; `accepted=5 rejected=1`, observable-preserved `YES`); the maths it images: `selfUpgrade/evalUpgradeOpScript.sml` |
| **…and PROOF-GATED by the live verified kernel:** the same per-generation compiler self-upgrade, but the gate is STRENGTHENED from `compiler_agrees` to a live Candle **correctness proof** — the verified kernel must PROVE each new compiler correct (its value-spec = the observable spec `eval_spec`) before it is installed. Run under the live prover: `GATE_B`, `GATE_C` certified (`\|- ∀s. … = eval_spec s`); the wrong compiler's correctness theorem is unprovable (`bad_ok = false`) so its upgrade is REJECTED; observable invariant, cost strictly reduced, earlier generations preserved. | **RAN** under live Candle | `scripts/apex-compiler-cell-candle.sh`, `candle/compiler_cell_candle.ml` (`verdict = "COMPILER_CELL_CANDLE_OK"`) |
| **The self-upgradable ROOT — the verified compiler itself made self-upgrading, BUILT.** The per-generation swap (`repl_upgrade`/`do_eval_record_gen`) is patched into CakeML's bootstrap compiler program: the running cake's REPL eval-compiler dispatches by generation (stock before gen 3, an upgraded compiler — different register allocator — after, announcing the in-place upgrade). The patch **translates cleanly into the verified `compiler64ProgTheory`**, and the altered compiler **self-compiles (via the existing verified cake) to a working 1.19 GB cake binary that compiles programs correctly** (`fib 10 → 55`); the altered `cake-sexpr-64` differs from stock — the self-upgrade is embedded in the compiler. | **BUILT + VERIFIED** (compiler-level); runtime `--repl` demo **env-blocked** (proven) | `selfUpgrade/cakeml-selfupgrade-root.patch`, `scripts/build-selfupgrade-root.sh`, `scripts/apex-selfupgrade-root.sh`, `selfUpgrade/SELFUPGRADE_ROOT.md`. Honest boundary: in *this* candle package self-compiled cakes segfault in interactive `--repl` (proven environmental — the *unpatched* self-compile segfaults identically while compiling fine; the working cake here is a downloaded binary, not patchable); a runnable verified self-upgrading binary needs the official in-logic bootstrap (`x64BootstrapTheory`). The self-upgrade *pattern* RUNS as a program on cake (rows above). |

> Honest boundary: self-improvement now reaches **all the way down to the kernel
> interface** — a kernel primitive (`REFL`) is swapped *in-process, under the whole
> live prover*, gated, on the real binary. The one thing never swapped is the
> *verified primitive* `Kernel` (the unforgeable `thm` constructors in `cake.S`):
> that is the immutable root of trust the swap is anchored to — swapping *it* is
> neither possible (no way to forge a `thm`) nor desirable (it would dissolve the
> guarantee). That fixed root is the safety, not a gap. On the compiler side, a
> new verified pass *is* in the compiler's own pipeline (the BVL `optimise` and
> Layer B rows): the pass is proved and the altered root runs it. What is still
> open there is the whole-pipeline `compile_correct` re-composition, one
> FFI-trace subgoal short (`compilerOpt/LAYERB.md`).

## 6. The closed-loop runtime — the gate IS the live prover — RAN

`agent/closedloop/` closes the loop: a real jailbroken gemma2:2b's every
proposed action is admitted or refused by the **live verified Candle kernel**
(persvati) — a fresh machine-checked theorem per step, not a human-audited
mirror.

| Claim | Status | Citation |
|-------|--------|----------|
| The firewall's soundness (a safe allowlist ⇒ an admitted action is within the absolute unsafe spec) and shield-safety, re-derived and **certified live** by the running Candle kernel. | **RAN** | `agent/closedloop/obligation_template.ml : ADMIT_SOUND, SHIELD_SAFE` (the HOL-Light re-derivation of `agent/toolAgentScript.sml : tool_pol_sound`) |
| Per-action: gemma emits a tool call → a `prove(...)` obligation is shipped to the persistent Candle server → the world step is gated on the kernel verdict. | **RAN** + **TRUSTED-GLUE** (~10-line num-encoding; proof-backed by the next row) | `agent/closedloop/closed_loop.py` over `scripts/place-server.sh` |
| **The encoding residue is now itself proof-backed:** the num-dialect the live kernel checks is proved FAITHFUL to the string-based absolute unsafe spec of `toolAgentScript` — so a too-permissive/buggy encoding cannot slip an unsafe tool past the gate (`unsafe_never_certified`: a truly-unsafe call always encodes to a num-unsafe one the kernel rejects). Shrinks the trust to a finite, eyeball-checkable table + the transcription of that table into the .py/.ml. | **PROVED** | `agent/closedloop/encFaithScript.sml : enc_truly_unsafe_faithful, candle_safe_transfers, unsafe_never_certified` |

## 7. The Place, live in Candle — RAN (Tier 3)

The core habitat theorems, the SYM kernel-mod tie-in, and **both plants**
(watchdog and polecart) self-optimizing their policies, all re-derived in HOL
Light and **certified at runtime by the running verified Candle kernel** on a
host with the `cake` binary. Reproduced by `scripts/tier3-place-candle.sh`.

| Claim | Status | Citation |
|-------|--------|----------|
| `SAFETY_PRESERVATION`, `SAFE_WEAKENING`, the watchdog (`WD_HABITAT_SAFE`) and the **polecart** (`CP_HABITAT_SAFE`), plus their live policy self-optimizations and the SYM rule. | **RAN** | `candle/theplace.ml` (checked by `scripts/tier3-place-candle.sh`) |
| **The REAL CakeML semantics, ported into the live kernel:** the export cone of `evaluate` (45 datatypes; the function cone as 134 kernel-checked clause theorems, including the 29 clauses of the fueled `eval_n`) is generated from HOL4's own defining theorems and loads into the running Candle in about two minutes. The HOL4 bridge pins every fueled mirror to the original semantics for sufficient fuel; the candle constants are introduced by structural recursion and the HOL4 clause equations are then re-proved in the kernel, so the correspondence candle-constant ↔ HOL4-mirror is that re-proved clause set and the exporter's printing, not one theorem. The kernel then proves, hypothesis-free, that a literal, an integer addition and a type error evaluate correctly under the ported `eval_n`. | **RAN** (live Candle) + **PROVED** (bridge) + **TRUSTED-GLUE** (the exporter's printing) | `scripts/reflectsem-live.sh`; `reflectsem/fueledBridgeScript.sml : eval_n_agrees, do_app_n_agrees, pmatch_n_agrees, do_eq_n_agrees`; `candle/reflectsem_gate_smoke.ml` (`RS_SMOKE_VERDICT = "RS_SMOKE_OK: 3 gates proved"`) |
| **The ouroboros loop, live:** the running program evolves its own code over accumulating generations. Each generation mutates the champion read back out of the previous generation's installed kernel theorem; an enumerative rewrite search ranked by a self-model (per-operator proposed/proved/refused counts, used as weights) proposes candidates; the kernel must prove `∀i. eval_n … = Rval [Litv (IntLit (6i+10))]` against the ported real semantics; each proved candidate is self-fed through `Repl.nextString` and run natively. One run: cost 19→15→13→11→7→5 over 5 generations, 2 semantics-breaking candidates refused by the kernel. When the search stalls the model proposes a new **improver** as source, which is compiled and gated (an ML-checked fragment invariant, plus its output must be kernel-proved and strictly cheaper) before it is installed: v3 installed, v2 and v4 refused. The verdict is computed by fed code over the installed champions. Boundary: the improver's fragment invariant is checked by ML code, not proved by the kernel; nothing is proved about the improver as a function, only about each output it produces. | **RAN** (live Candle) + **TRUSTED-GLUE** (the improver invariant check) | `scripts/reflectsem-live.sh --ouroboros`; `candle/ouroboros.ml` (`ouro_gen_<n>_thm`, `ouro_gen_<n>_rejections`, `ouro_improver_3_installed`, `ouro_verdict = "OUROBOROS_OK: 5 generations, cost 19 -> 5, 2 rejections, improver upgraded, 1 via the rewriter theorem"`) |
| **The ouroboros rewriter, proved once:** the improver's constant-folding / dead-subterm rewriter is a HOL function proved in the live kernel against the ported `eval_n`, for every fragment term at any fuel ≥ `efuel e`, by full structural induction: `ofold_preserves`, `ofold_frag`, `ofold_cost`, plus `orw_oeq`, the congruences and `oeq_preserves` for single steps at any position and their compositions. The fragment is an inductive `ofrag` on the real `exp`, proved equal to the image of a binary `oexp` (`ofrag_oemb`). In the loop a candidate the rewriter produces gets its gate theorem by SPEC/MP from these theorems and the parent's certificate, with no symbolic execution (one run: generation 2 of 5); a self-test certifies a partial edit and refuses a semantics-breaking one every run. Boundary: the rewriter is defined on `oexp` and embedded, not on the nested `exp` directly; the other improver moves are still gated per candidate; the general improver's invariant is still ML-checked. | **PROVED** (kernel, the rewriter) + **RAN** (live Candle) | `scripts/reflectsem-live.sh --ouroboros`; `candle/ouroboros_rewrites.ml` (`val ofold_preserves = \|- …`, `OURO_RW_VERDICT = "OURO_RW_OK: 6 rewriter theorems, hypothesis-free"`); `candle/ouroboros.ml` (`ouro_gen_2_route = "rewriter theorem"`) |

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

## 9. The honest boundary — the one witness not yet constructed, and only there

After all of the above, the kernel-upgrade layer assumes **no principle**.
The historically-named seam `loeb_reflection` (`kernel/kernelUpgradeScript.sml`)

    loeb_reflection mem K K' thy sound_stmt ⇔
      (K thy sound_stmt ⇒ kernel_sound mem K')

is now a *derived* notion. It follows from the certifying kernel's soundness
together with an encoding seam of exactly the kind `encodes_obligation` is,

    encodes_soundness mem thy s K' ⇔ ((thy,[]) |= s ⇒ kernel_sound mem K')

and with a Candle derivation of `s` it yields `kernel_sound mem K'` by plain
theorem (`kernel/kernelUpgradeScript.sml : encodes_soundness, sound_kernel_lifts_soundness, candle_lifts_soundness, loeb_reflection_from_soundness, witness_suffices, self_improving_kernel_is_safe`;
composed: `integration/integrationKernelScript.sml : svenvs_tower_with_kernel_upgrade`).
Soundness itself is exactly transfer — a kernel's yes carries every fact the
term faithfully encodes (`kernel_sound_iff_transfers`).

**The trap, stated as a theorem.** An encoding seam holds whenever its
consequent does, so *having* a soundness witness (a Candle derivation plus an
`encodes_soundness` certificate) is **equivalent** to `K'` being sound
(`kernel/kernelUpgradeScript.sml : soundness_witness_iff_sound, sound_kernel_encoded_by_every_term`).
The predicate carries no information beyond soundness; the content is the
**provenance** of the encoding certificate. The hol-reflection translator
(`termsem_cert`, and for a strictly stronger kernel the Fallenstein–Kumar LCA
construction) produces `encodes_soundness` theorems *by construction*, without
already knowing `K'` sound. What remains open is therefore not a predicate but
a **construction**: for a strictly stronger `K'`, produce the theory, the term,
the Candle derivation and the encoding certificate by that route.
`kernel/loebReduction/loebReductionScript.sml : lca_encodes_soundness, loeb_reflection_from_lca, kernel_self_upgrade_sound_from_lca`
show that the LCA ingredient `lca_reflects_soundness` supplies exactly the
encoding half; constructing it is the CPU/RAM-walled `lcaProof` computation
(tens of GB resident, ~ten CPU-hours per prerequisite theory), not a logic gap,
not a porting failure, not faked.

A sound kernel cannot certify a *logically stronger* successor for free
(Gödel/Löb); the principled escape is that stratified large-cardinal route. It
bites **only** the kernel-replacing-*itself*-with-something-stronger move;
every other self-improvement in this artifact — policy, spec, meta,
corrigibility, the prover build, a sound *re-engineering or optimization* of
the kernel, the recursive mutual verifier+compiler loop — is Löb-free and
carries no labeled assumption. The other two historically-named seams are
**discharged**: `encodes_obligation` for the shipped finite watchdog (§4),
`frozen_checker_sound` for the real Candle build (§5).

An earlier form of `loeb_reflection` quantified the certificate over every
theory; Candle derives nothing in a theory that is not `theory_ok`, so that
antecedent was unsatisfiable and every theorem carrying it vacuous
(`kernel/kernelUpgradeScript.sml : old_reflection_antecedent_unsatisfiable`).
A sound certificate of an unrelated true term encodes nothing about `K'`
(`reflection_is_not_soundness`), and in the self-upgrade theorem both the
derivation and the encoding certificate are necessary
(`kernel/kernelUpgradeScript.sml : certificate_without_reflection_can_breach, reflection_without_certificate_can_breach`).
The proved negative `loeb_finite_obstruction` (§4) shows finiteness supplies no
witness.

**Two further items, stated so the count of one is not misread.**
*Genesis soundness* — `genealogy_sound` needs a sound judge at `n = 0` — is
not a labeled `Definition`: at the base it is the built
`holSoundnessTheory.proves_sound`, the ordinary LCF trust in HOL4's kernel and
the CakeML/Candle development that every row above already rests on.
`attestation_faithful` (`embodiment/embodimentScript.sml`) *is* a labeled
`Definition`, but opt-in: it is an antecedent only of the theorems that grant
*extra* authority for a proof the inhabitant volunteers about its own
substance (`integration/integrationScript.sml : svenvs_tower_with_embodied_disclosure`).
With nothing disclosed the full guarantee holds with no seam at all
(`embodiment/embodimentScript.sml : nondisclosure_is_inert, floor_holds_without_any_seam`),
and the `svenvs_tower_*` theorems cited in §1 do not carry it. See
`paper/honest-assumptions.md` §6.

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
