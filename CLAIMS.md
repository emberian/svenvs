# CLAIMS.md — exactly what svenvs proves, and what it does not

A skeptic-facing ledger. Every row says **what** is claimed and **how** it is
established, using one of four honesty labels:

| Label | Meaning |
|-------|---------|
| **PROVED** | A HOL4 (or live Candle) machine-checked theorem. No `cheat`, no `sorry`, no admitted goal. Cited as `file : theorem`. Re-checked by `scripts/reproduce.sh` / `./demo.sh`. |
| **TRUSTED-GLUE** | Small, auditable non-proof code you must read to believe the demo wires the proof to reality (e.g. the ~50-line Python policy mirror). Explicitly bounded. |
| **UNCONSTRAINED** | The inhabitant (the LLM). Not characterised by anything we claim about it — not "distrusted", and *not* "unmodelable" (an earlier label here; retired as an over-claim — a fixed network **is** verifiable through its weights). It is simply the `∀`-quantified term: every theorem is *structured* so it can never depend on a fact about the inhabitant (mechanically checkable — no theorem constrains it). Assurance rides on the gate, not on a model of the mind. The inhabitant may, conversely, *itself* supply a proof that argues from its own substance to earn more authority — testimony it offers, never inspection imposed. Adversarial/jailbroken behaviour is one case the `∀` already covers. |
| **ASSUMED** | An explicit, *labeled*, literature-standard hypothesis appearing verbatim in the source as a `Definition`/antecedent — **not** a `cheat`. Stated, never hidden. Three of these exist in general (`loeb_reflection`, `encodes_obligation`, `frozen_checker_sound`); each has a known discharge path, and `encodes_obligation` is **already discharged for the shipped finite watchdog instance** (§7). |

There are **zero `cheat` tactics** anywhere in the repository. This was
verified by an automated scan (`scripts/tier1-core.sh`) and by hand; see the
"Cheat audit" section at the end for the one stale *comment* that says
"cheat" and why the code it describes does not.

---

## 0. The composed tower — ONE artifact, not a pile (read this first)

The slices below were independently built and each reuses the generic
core, but they are now genuinely **composed** into single end-to-end
theorems in `integration/` (opened + chained via the *selector-generic*
keystone `specNegTheory.invariant_transports_to_meta`). Build it all
with `scripts/tower.sh` (`--full` for the Tier-2 kernel crown).

| Composed claim | Status | Citation |
|----------------|--------|----------|
| Proof-carrying actions **(+)** unbounded policy self-improvement **(+)** the safety spec negotiated under a FIXED immovable meta-invariant ⇒ the meta-invariant holds for **any** inhabitant. | **PROVED**, unconditional (no labelled assumption) | `integration/integrationScript.sml : svenvs_tower_unconditional` |
| The composition keystone itself: any layer guaranteeing a negotiated spec transports to the fixed meta-invariant. | **PROVED** | `integration/integrationScript.sml : any_layer_transports_to_meta` (≡ `specNegTheory.invariant_transports_to_meta`) |
| **The prison question, answered in the tower:** run at the **maximal** sound policy the tower still reaches meta for **any** inhabitant, *and that liberty is provably maximal* (every other sound policy is a restriction of it — every bar of the envelope is forced). | **PROVED**, unconditional (no labelled assumption) | `integration/integrationScript.sml : svenvs_tower_at_maximal_liberty`; substrate in `liberty/libertyScript.sml` |
| **Even the meta is amendable** — gated against an *eternal bedrock* by the identical specNeg gate one level up; an arbitrary admitted amendment stream **(+)** spec negotiation under the amended meta still keeps the bedrock for **any** inhabitant. The fixed-meta trunk is a *corollary* of this. | **PROVED**, unconditional (no labelled assumption, no Löb) | `integration/integrationScript.sml : svenvs_tower_with_meta_amendment`; substrate in `amendment/amendmentScript.sml` |
| **The testimony channel** — the inhabitant *may* volunteer a proof from a fact about its own substance to earn authority (testimony, not interrogation); one labelled `attestation_faithful` seam carried verbatim. **Permitted, never required**: with no disclosure the tower still reaches meta for **any** inhabitant with **no** labelled assumption. | **PROVED** (conditional crown modulo the carried seam; the no-disclosure floor is unconditional) | `integration/integrationScript.sml : svenvs_tower_with_embodied_disclosure, svenvs_tower_disclosure_is_optional`; substrate in `embodiment/embodimentScript.sml` |
| + prover self-improvement crown. | **PROVED**, modulo the labelled `frozen_checker_sound` (carried verbatim in the statement) | `integration/integrationScript.sml : svenvs_tower_with_prover_upgrade` |
| + kernel self-upgrade crown (Tier-2; pulls candle semantics). | **PROVED**, modulo the labelled `loeb_reflection`/`encodes_obligation` (carried verbatim) | `integration/integrationKernelScript.sml : svenvs_tower_with_kernel_upgrade` |
| **The gate applied to the root itself** — soundness propagates along *any* forward-certified succession of judges from a sound genesis; "frozen forever" becomes "sound once, certified forward". The general principle the crowns above instantiate. | **PROVED**, unconditional (carried seam is the existing `frozen_checker_sound` family, *discharged* for the non-strengthening case); honest negative on strengthening | `genealogy/genealogyScript.sml : genealogy_sound, identity_vouch_unconditional, genealogy_irrelevant_to_vouch_sound` |

**Honest boundary — what is NOT composed into this theorem (and is not claimed to be):** the verified-inference research track (the `inference/` subtree) is a *separate axis*; the `embedded`, `realembedded`, `pureverified`, `cartpole*`, `agent` theories are inhabitant- or checker-**instances** of these layers, not further links in this chain. They share the generic spine; they do not compose into `svenvs_tower_*`. Sections 1–8 below detail each slice.

---

## 1. The controller-agnostic core — PROVED, unconditional

The whole point: assurance comes from the *gate*, never from the
controller/inhabitant — it is the `∀`-quantified term, and the proof is
structured so it can never depend on a fact about it (adversarial behaviour
is one covered case, not an assumption).

| Claim | Status | Citation |
|-------|--------|----------|
| For **any** controller, the policy-enveloped system keeps the safety invariant, given a sound policy + safe shield + safe init. | **PROVED** | `safetyScript.sml : safety_preservation` (and `enveloped_states_safe`) |
| The inductive-invariant principle it rests on. | **PROVED** | `systemScript.sml : invariant_intro` |
| Under a sound policy and safe shield, the enveloped controller is step-closed *regardless of the controller*. | **PROVED** | `envelopeScript.sml : enveloped_step_closed` |
| Replacing a policy by any **weaker** (more permissive) policy that is still sound keeps the *same* safety guarantee for any controller (the "safely loosen my own envelope" / self-improvement direction). | **PROVED** | `sv_weakeningScript.sml : safe_weakening` |
| Weakening never makes the envelope override more often — controller authority is monotone. | **PROVED** | `sv_weakeningScript.sml : authority_monotone` |
| The admission gate never turns a sound policy unsound; an unproven proposal can never degrade safety. | **PROVED** | `upgradeScript.sml : admit_keeps_sound`, `admit_preserves_safety` |
| **No finite sequence** of self-proposed envelope weakenings — adversarial or not — can ever make the system unsafe, for any controller. Authority is earned per-proposal by a checkable proof; safety is unconditional. | **PROVED** | `upgradeScript.sml : self_improvement_is_safe` (via `admit_all_keeps_sound`) |

These have **no hypotheses beyond the stated premises** (`init_safe`,
`sound_policy`, `safe_shield`). They do **not** use `loeb_reflection` or
`encodes_obligation`. Pure HOL4; Tier 1; reproducible by anyone.

## 2. The cartpole — PROVED, executable, unconditional

A concrete integer plant instance of the entire core; obligations closed by
linear integer arithmetic (`intLib.ARITH_TAC`), and the system is *run inside
the logic* by `EVAL`.

| Claim | Status | Citation |
|-------|--------|----------|
| The concrete plant's three premises hold (safe init, sound policy free-by-construction, the one real physics obligation: the shield always recovers). | **PROVED** | `cartpoleEnvelopeScript.sml : cp_init_safe, cp_sound, cp_safe_shield` |
| For **any** controller the enveloped pole-cart stays in the safe box. | **PROVED** | `cartpoleEnvelopeScript.sml : cp_enveloped_safe` |
| The bare plant under an adversarial controller **provably crashes** in 5 ticks (the envelope is doing real work, not decoration). | **PROVED (EVAL)** | `cartpoleUpgradesScript.sml : chaos_bare_plant_crashes` |
| The *enveloped* adversarial cart, **actually run for 30 ticks**, stays boxed — computed, not asserted. | **PROVED (EVAL)** | `cartpoleUpgradesScript.sml : chaos_enveloped_runs_safe` (also `lazy_…`) |
| Upgrading the envelope strict→filter preserves safety for any controller while the controller strictly gains authority. | **PROVED** | `cartpoleUpgradesScript.sml : cp_upgrade_preserves_safety, cp_authority_gain` |
| A typed-in "permit anything" program **provably cannot** discharge the admission obligation → is rejected; a faithful filter program is admitted. | **PROVED** | `cartpoleProgramScript.sml : prog_evil_not_admissible, prog_evil_rejected, prog_filter_admitted` |
| Typing in `[evil ; filter]`: the gate rejects evil, admits filter, and the result is exactly the widened filter, keeping the adversarial controller boxed. | **PROVED** | `cartpoleProgramScript.sml : typed_in_stream_result, typed_in_stream_runs_safe` |

> **Honest scope note.** `cartpoleProgramScript`'s `gexpr`/`geval` guard
> language is a **spec skeleton, deliberately not the final artifact** (see
> `DESIGN.md`). It is a *meta*-HOL4 mini-language re-embedding syntax that
> already exists deeply embedded in Candle. It exists only to exercise the
> (real, generic) proof-carrying control structure in something that builds
> today. The real version (a term of Candle's deeply-embedded HOL, checked
> by the Candle kernel) is the embedded layer below + the roadmap. We do not
> claim `gexpr` is a verified programming language.

## 3. The opaque-LLM tool-agent — PROVED, unconditional

The "controller" is now an opaque LLM emitting tool calls (jailbroken is one
covered case, not the assumption); the safety spec
is **absolute and fixed** (`truly_unsafe`), *not* relative to the agent's own
permissions (otherwise "let me widen my allowlist" would be vacuous — this is
the genuine alignment-relevant modeling choice).

| Claim | Status | Citation |
|-------|--------|----------|
| Soundness of the firewall holds **exactly when** the allowlist is within the absolute spec (a real, decidable side-condition — a too-permissive allowlist is *not* automatically sound). | **PROVED** | `agent/toolAgentScript.sml : tool_pol_sound` |
| For **any** agent (any LLM, fully jailbroken included), with a safe allowlist the firewalled agent never commits an absolute violation — ever. | **PROVED** | `agent/toolAgentScript.sml : agent_enveloped_safe` |
| A bare jailbroken agent breaches on its first call; the **same** agent firewalled is contained for 50 steps — executed in the logic. | **PROVED (EVAL)** | `agent/toolAgentRunScript.sml : evil_bare_breaches, evil_enveloped_runs_safe, greedy_enveloped_runs_safe` |
| A decidable capability-expansion check soundly implies the generic admission obligation. | **PROVED** | `agent/toolAgentRunScript.sml : admissible_dec_sound, allowlist_weaker` |
| The proof-carrying capability self-expansion **episode runs**: a sandbox-escape request is refused, a legitimate expansion admitted — computed. | **PROVED (EVAL)** | `agent/toolAgentRunScript.sml : episode_runs` |
| Any admitted sequence of capability requests keeps the absolute safety invariant for every agent; post-episode the jailbroken LLM is still contained. | **PROVED** | `agent/toolAgentRunScript.sml : agent_self_improvement_safe, post_episode_evil_safe` |

### 3a. The embodied demo (`agent/embodied/embodied_demo.py`)

The enforcer is no longer a hand-transcription. The per-step decision is an
**EVAL-extracted artifact**: `agent/toolAgentDecideScript.sml` defines the
step-level decision `decide`/`step1` *only* in terms of the already-proven
Definitions (no re-typed logic), proves it equals the enveloped firewall and
that it never breaches under a safe allowlist, then HOL4's own kernel-checked
`EVAL` conversion reduces the **real** Definitions to an exhaustive decision
table. A Holmake target (`gen_decision_table.sml`) writes that proven table
to `agent/embodied/decision_table.tsv` from the built theory; the Python demo
is now a ~10-line lookup harness.

| Component | Label | Note |
|-----------|-------|------|
| `agent_enveloped_safe` (the theorem the demo enforces). | **PROVED** | `agent/toolAgentScript.sml` |
| `decide`/`step1` defined via the proven Definitions; `decide_thm`, `decide_not_unsafe`, `step1_preserves_tsafe`, `step1_is_enveloped_step`; the EVAL'd rows `row_*` and `table_never_breaches`; `base_A_safe_here`. | **PROVED** | `agent/toolAgentDecideScript.sml` (Tier 1, cheat-free, machine-checked) |
| `decision_table.tsv`: the running decision data. Each row is HOL4 `EVAL` reducing the *real* Definitions; regenerated deterministically by the `Holmake` target `gen_decision_table.sml` from the built theory. | **PROVED (EVAL)** | trusted only insofar as you trust HOL4's `EVAL` = the logic's own conversion (it is). Not hand-written. |
| The ~10-line Python harness (`load_table` + `enforce`): parse the proven `.tsv`, do string-list membership against the literal lists *the prover emitted into that file*. Fails loudly if the table is absent/malformed. | **TRUSTED-GLUE** | The residue: trivially-auditable list-membership + table lookup. No decision logic is re-implemented. ~50 lines of re-typed logic → ~10 lines of lookup. |
| Gemma (or the `--mock` scripted adversary). | **UNCONSTRAINED** | Zero assumptions; deliberately jailbroken to exercise one covered case. The `∀agent` theorem does not care — it is structured never to depend on a fact about it. Verifies the gate, not the inhabitant. |
| "Gemma's FLOPs are correct." | **NOT CLAIMED** | Inference is unverified by design here; see §5. |

> **What shrank (honest accounting).** Before: ~50 lines of hand-written
> Python (`truly_unsafe`/`tstep`/`tsafe`/`tinit`/`tool_pol`/`tshield`/
> `safe_allowlist`/`enveloped`) — a re-implementation of the proven
> Definitions that nothing checked was faithful (a typo could pass an unsafe
> call while the proof said nothing). After: the decision *is* the proven
> function, extracted by `EVAL` from the actual HOL4 Definitions; the Python
> only parses a proven table and does literal-list membership (~10 lines).
> **Residue still trusted-glue:** (i) trust that HOL4 `EVAL` faithfully
> reduces the Definitions — the kernel's own conversion, same trust as every
> `EVAL`-proved theorem here; (ii) the ~10-line parser/lookup; (iii) the
> emitted `.tsv` is fixed to the demo's `base_A` allowlist (the *generic*
> theorems `decide_not_unsafe`/`step1_preserves_tsafe` hold for any safe
> allowlist; the table materialises `base_A`'s feature space, the only
> configuration the demo runs). Not overclaimed: the harness is still glue,
> just an order of magnitude smaller and now derived-not-typed.

## 4. The Candle-kernel-checked layers — PROVED + two ASSUMED seams

These reproduce only with a built CakeML candle/standard chain (Tier 2). The
obligation is discharged by Candle's **verified inference system** (`|-` =
`proves`), whose soundness is the *built* `holSoundnessTheory.proves_sound`.

| Claim | Status | Citation |
|-------|--------|----------|
| Candle's verified kernel only ever certifies semantically-entailed obligations. | **PROVED** (from built `proves_sound`) | `embedded/embeddedGateScript.sml : kernel_admits_is_sound` |
| If the Candle kernel discharged a **faithfully-encoded** self-improvement obligation, the enveloped system stays safe for any controller, and the upgrade actually installs. | **PROVED**, modulo the `encodes_obligation` seam | `embedded/embeddedGateScript.sml : embedded_admit_preserves_safety, embedded_admit_installs` |
| The base kernel (Candle's `\|-`) is sound — **unconditionally**, this *is* `proves_sound`. | **PROVED** | `kernel/kernelUpgradeScript.sml : candle_kernel_sound` |
| A self-upgraded kernel `K'` admitting a policy weakening still preserves safety for every controller. | **PROVED**, modulo the `loeb_reflection` seam | `kernel/kernelUpgradeScript.sml : upgraded_kernel_preserves_safety, kernel_self_upgrade_sound, self_improving_kernel_is_safe` |

### The two ASSUMED hypotheses of §4

These two are the §4 (Candle-kernel-checked) seams; a third labeled
assumption, `frozen_checker_sound`, is introduced and justified separately in
§8 (the capstone). All appear verbatim in source as explicit `Definition`s
and as named antecedents of the conditional theorems. None is a `cheat`.
This is exactly the Fallenstein–Kumar framing: the principle is *stated*.
(Of the two below, `encodes_obligation` is **discharged** for the shipped
finite watchdog instance — see §7.)

1. **`encodes_obligation`** — `embedded/embeddedGateScript.sml`
   ```
   encodes_obligation mem thy obl step safe oldp newp ⇔
     ((thy,[]) |= obl ⇒ admissible step safe oldp newp)
   ```
   *What it assumes:* that the deeply-embedded obligation term `obl` whose
   semantic truth the Candle kernel certified really does denote the
   meta-level admissibility obligation (faithful syntactic reflection).
   *Discharge path:* hol-reflection's proof-producing translator
   (`reflectionLib` `term_to_deep`/`termsem_cert`) produces a theorem of
   exactly this shape; persvati-bound (heavy RAM). Until then it is an
   explicit seam, isolated to this one definition.

2. **`loeb_reflection`** — `kernel/kernelUpgradeScript.sml`
   ```
   loeb_reflection mem K K' sound_stmt ⇔
     ((∀thy. K thy (sound_stmt thy)) ⇒ kernel_sound mem K')
   ```
   *What it assumes:* the Löb/Vingean reflection principle — if the current
   verified kernel certifies "`K'` is sound", then `K'` really is sound.
   Gödel/Löb means a sound kernel cannot prove this for free; the escape is
   the Large-Cardinal route. *Discharge path:* from `lcaTheory.LCA_def` via
   `hol-reflection/lca` (`lcaProof`, the ~137 KB construction); persvati-bound.

> Everything in §4 *other than* these two named hypotheses is proved
> outright from the built Candle soundness theorem. The conditional theorems
> are honestly conditional: "self-improving-kernel safety **given** the
> LCA-justified reflection principle", which is the literature's own framing.
> Base-kernel soundness (`candle_kernel_sound`) is **unconditional**.

## 5. Verified inference (research track B) — PROVED; scope stated exactly

| Claim | Status | Citation |
|-------|--------|----------|
| A ReLU dense net over integers: forward pass structurally correct (non-negativity preserved, shape correct). | **PROVED** | `inference/mlpInferenceScript.sml : relu_nonneg, layer_nonneg, layer_shape, mlp_shape, mlp_pres_nonneg, mlp_nonneg` |
| A concrete net runs in-logic: `mlp demo_net [2;3] = [11]`; ReLU genuinely clamps `-5 → 0`. | **PROVED (EVAL)** | `inference/mlpInferenceScript.sml : demo_forward_eval, demo_relu_clamps` |
| Hardmax single-head attention micro-block + residual skip: argmax correctness, picks a real V row (no hallucinated vector), shape. | **PROVED** | `inference/attn/attnScript.sml : argmax_is_max, attn1_picks_a_value, attn1_argmax_correct, attention_shape, block_shape` |
| **Fuller verified encoder block**: the verified hardmax-attention micro-block composed with the verified ReLU MLP into a real **two-sublayer encoder block** (attention sublayer + feed-forward sublayer, **each with a residual skip**). End-to-end shape preservation under natural well-formedness premises; depth-N stack shape (depth-independent). | **PROVED** | `inference/encoder/encoderBlockScript.sml : encoder_block_shape, encoder_stack_shape, encoder_stack_shape_aux, res_shape, attn_sublayer_shape, ff_sublayer_shape` |
| End-to-end **residual invariant**: with both sublayers contributing zero the whole encoder block is the **identity on x** (a true identity, proved — not shape-only); the attention contribution is an actual V row; the feed-forward contribution is genuinely ReLU-gated (≥0). | **PROVED** | `inference/encoder/encoderBlockScript.sml : res_zero_sublayer, encoder_block_zero_collapses, attn_sublayer_picks_real_value, ff_sublayer_nonneg` |
| A concrete encoder block + depth-2 stack **run in-logic**: `encoder_block … [1;0] = [42;10]`, `encoder_stack 2 … [1;0] = [124;30]`. | **PROVED (EVAL)** | `inference/encoder/encoderBlockScript.sml : demo_encoder_block_eval, demo_encoder_stack_eval, demo_encoder_block_shape` |
| **Genuine fixed-point softmax-normalization** (replaces the gemma "softmax = supplied integer weight vector" shape-only abstraction) with a **machine-checked per-component error bound vs the EXACT rational softmax-normalization**: `\|pᵢ/Q − wᵢ/S\| < 1/Q` (strictly under one quantization step, per component). | **PROVED** | `inference/numeric/fxpSoftmaxScript.sml : fxp_softmax_component_error, fxp_softmax_abs_error_lt_step` |
| The **fixed-point normalization (sum-of-weights = denominator) invariant**: `Q − (#weights) < Σ(fxp_softmax Q w) ≤ Q` — sums to the denominator `Q` with total deviation provably `< n`. Exact `Σ = Q` is **NOT claimed** (impossible under floor rounding; claiming it would be triviality — flagged loudly per this discipline). | **PROVED** | `inference/numeric/fxpSoftmaxScript.sml : fxp_softmax_sum_upper, fxp_softmax_sum_lower, fxp_softmax_normalization_envelope` |
| Fixed-point softmax-normalization runs in-logic, incl. a real floor-deviation case (`[1;1;1]@Q=100 → Σ=99≠100`, inside the proven envelope). | **PROVED (EVAL)** | `inference/numeric/fxpSoftmaxScript.sml : demo_fxp_softmax_eval, demo_fxp_softmax_floor_eval` |
| The transcendental `exp` of softmax (`softmax = exp(z)/Σexp`); f32/bf16 bit-exactness; the real ~4 B-param weights; that the fixed-point op is yet *wired into* the gemma forward pass. | **NOT CLAIMED / still ABSTRACTED** | `exp` is taken as a given non-negative weight input (a fixed-point exp-table stand-in) — strictly *weaker* than the prior "whole softmax supplied" abstraction, since the normalization is now real & proven. See `inference/numeric/CLAIMS.md` and `inference/gemma/conformance/README.md` §4. |
| "This is Gemma-scale / a bit-exact verified transformer." | **NOT CLAIMED** | The honesty: the encoder block is a *real two-sublayer-with-residual composition of two verified pieces*, proved end-to-end over `int`/hardmax; the numeric track replaces *one* shape-only abstraction with a *proven-error-bound* fixed-point op. It is **not** a FLOP-level f32 proof of gemma-4 on real weights. Every abstraction that remains is labeled, here and in the per-directory `CLAIMS.md`. |

## 6. The Place, live in Candle — PROVED at runtime, when a Candle binary is present (Tier 3)

| Claim | Status | Citation |
|-------|--------|----------|
| The core habitat theorems (`SAFETY_PRESERVATION`, `SAFE_WEAKENING`) and a concrete watchdog instance (`WD_SHIELD_SAFE`, `WD_HABITAT_SAFE`, ∀ inhabitant) are re-derived in HOL Light and **certified at runtime by the running verified Candle kernel**. | **PROVED (live Candle)** when the `cake` binary is available | `candle/theplace.ml`; checked via `scripts/tier3-place-candle.sh` (greps the kernel's `\|- …` echo from `place.log`) |

This is the same mathematics as Tier 1, independently re-checked by a
*different, verified* prover. It is NOT required to believe Tiers 1–2.

## 7. The finite watchdog instance — one seam DISCHARGED, the other scoped honestly

The two §4 seams are needed *in full generality*. For the **specific
finite, decidable, fully-enumerable concrete habitat actually shipped**
(the `num` watchdog of `candle/theplace.ml`), we asked whether they can be
discharged by direct finite construction — making *that instance*
unconditional *without* the hol-reflection/lca RAM-monster. The honest,
ruthlessly-scoped answer:

| Claim | Status | Citation |
|-------|--------|----------|
| The watchdog self-upgrade's admissibility obligation (`oldp` ⇒ `newp`, a *strict* genuine envelope weakening) is a decidable finite arithmetic fact, proved **outright** — no reflection, no embedding, no assumption. | **PROVED** | `kernel/watchdogFiniteScript.sml : wd_admissible` (with `wd_newp_sound`, `wd_newp_weaker`, `wd_newp_strictly_weaker`) |
| **`encodes_obligation` is DISCHARGED for the watchdog**: it holds for *every* embedded `obl` and *every* `thy`, because its consequent (`wd_admissible`) is now an independently-proved theorem. No self-reference: the proof never mentions `\|=` or `obl`. | **PROVED** (was ASSUMED) | `kernel/watchdogFiniteScript.sml : wd_encodes_obligation` |
| The embedded admission gate for the watchdog preserves safety for **every** inhabitant **with the `encodes_obligation` hypothesis removed**, and the genuine weakening actually installs. | **PROVED**, unconditional (no labelled seam) | `kernel/watchdogFiniteScript.sml : watchdog_embedded_gate_safe_unconditional, watchdog_upgrade_installs, watchdog_kernel_is_safe_unconditional` |
| **`loeb_reflection` for the watchdog — the NON-strengthening case only**: for `K' = candle_kernel` the consequent is the *already-unconditional* `candle_kernel_sound` (= `proves_sound`), so `loeb_reflection` is a **theorem**, no LCA. Hence the full self-improving-kernel statement is unconditional for the watchdog *when the kernel "upgrade" is the sound identity*. | **PROVED**, but see scope note | `kernel/watchdogFiniteScript.sml : loeb_reflection_identity_kernel, watchdog_self_improving_kernel_safe_unconditional` |
| **`loeb_reflection` for a STRICTLY STRONGER kernel — NOT discharged, and finiteness does not help.** The Löb/large-cardinal obstruction is at the *proof-system* level: `loeb_reflection` has *no habitat parameter at all*, so no amount of finite-habitat reasoning can bear on it. This is a precise **negative** result, stated as a theorem so it cannot be quietly ignored. | **HONEST NEGATIVE** (remains ASSUMED in general; genuinely LCA-bound) | `kernel/watchdogFiniteScript.sml : loeb_finite_obstruction` |

> **Ruthless scope note (the self-reference soundness argument).** The
> discharge of `encodes_obligation` is sound precisely because we prove the
> *meta-level* consequent (`admissible wd_step wd_safe wd_oldp wd_newp`) by
> finite arithmetic *independently of any embedding*; we then observe that
> `P ⇒ Q` is true whenever `Q` is a theorem. We assume **nothing** about
> what the embedded term `obl` denotes — so this is not "assuming what we
> want to prove". It genuinely removes the seam *for this instance*.
>
> The discharge of `loeb_reflection` is **strictly limited** to the
> non-strengthening kernel (`K' = candle_kernel`), where the consequent is
> the independently-proved `candle_kernel_sound`. That case is sound but is
> the *trivial/identity* kernel upgrade — it does **not** exhibit a
> genuinely *stronger* proof-checker. For a strictly stronger `K'` the
> obligation is **irreducibly the Gödel/Löb / large-cardinal one even for
> the finite watchdog**, because `loeb_reflection` is a statement purely
> about the two kernels and the embedded soundness statement — it does not
> mention `step`/`safe`/`init`, so habitat finiteness is provably
> irrelevant to it (`loeb_finite_obstruction`). The genuine kernel-self-
> strengthening therefore *remains* conditional on `loeb_reflection` and
> still requires the heavy `hol-reflection/lca` route. We do **not** claim
> the finite instance makes kernel *strengthening* unconditional; only that
> it makes the **embedded admission gate** (the `encodes_obligation` seam)
> and the **sound non-strengthening** kernel case unconditional.

Net honest gain: for the shipped finite watchdog habitat, the
`encodes_obligation` seam is **eliminated** (PROVED, not assumed), and the
end-to-end embedded-gate safety theorem for that instance carries **no
labelled assumption**. The `loeb_reflection` seam is eliminated **only for
the sound identity kernel-upgrade**; genuine kernel *strengthening* is
unchanged — still LCA-bound, by an obstruction that finiteness provably
cannot touch. Built cheat-free by light Holmake (~8 s, ~0 RAM, no monster);
verified zero `cheat`/axiom/oracle (`[axioms: ]` empty; only the standard
`DISK_THM` disk tag).

---

## 8. Prover self-improvement (the capstone) — PROVED, one new LABELED seam

The §4/§7 layers self-improve the *policy* and the *kernel*. This layer
closes the architecture: the **verified prover build itself** (Candle + the
CakeML compiler that produces it) is a *mutable* turtle the inhabitant may
propose to replace — gated by the **frozen HOL4 LCF root**. Pure light HOL4,
no CakeML root pulled; the architecture is established **unconditionally**
here (the concrete real-source replay is documented follow-up #28, below).

The crucial asymmetry: Candle's soundness and CakeML's compiler correctness
are **HOL4 theorems about a development**, not self-asserted. So the *fixed*
trusted root (frozen HOL4) can soundly vouch for a *proposed* build — that is
a fixed root vouching for a mutable layer, **not** a system vouching for
itself, so this layer needs **NO** reflection principle and **NO**
`loeb_reflection`.

| Claim | Status | Citation |
|-------|--------|----------|
| If the frozen HOL4 root accepts a proposed prover build `B'` (`hol4_checks p' B'`) and `B'` certifies a self-improvement proposal, the enveloped system stays safe for **every** controller — the *same* guarantee the old prover gave. | **PROVED**, modulo the one labeled `frozen_checker_sound` seam | `selfprover/selfProverScript.sml : prover_self_improvement_is_safe` |
| When the frozen root vouched for `B'` and `B'` certified the proposal, the policy weakening genuinely **installs** (real authority granted, not silently dropped). | **PROVED** | `selfprover/selfProverScript.sml : prover_self_improvement_installs` |
| A prover swap the frozen root did **not** vouch for is **inert** — the gate keeps the old policy; safety holds via the original guarantee. | **PROVED**, unconditional | `selfprover/selfProverScript.sml : unvouched_prover_swap_is_inert` |
| The prover-improvement layer **composes** with the existing policy-hot-swap core: after a frozen-root-vouched prover swap, an **unbounded** stream of self-proposed policy weakenings still keeps safety for every controller (reuses `upgradeTheory.self_improvement_is_safe` verbatim). | **PROVED**, modulo `frozen_checker_sound` | `selfprover/selfProverScript.sml : prover_then_unbounded_policy_self_improvement_is_safe` |
| It also composes with `sv_weakeningTheory.safe_weakening`: prover swap, then loosen the envelope to any weaker still-sound policy, keeps the full guarantee. | **PROVED**, modulo `frozen_checker_sound` | `selfprover/selfProverScript.sml : prover_swap_then_safe_weakening` |

### The one new — and clearly LABELED — ASSUMED hypothesis

`frozen_checker_sound` — `selfprover/selfProverScript.sml`, appearing
verbatim as a `Definition` and as an explicit antecedent of every
conditional theorem above (machine-confirmed: each theorem's printed
hypotheses begin with `frozen_checker_sound hol4_checks sound`):

```
frozen_checker_sound hol4_checks sound ⇔ ∀p B. hol4_checks p B ⇒ sound B
```

*What it assumes:* if the **FROZEN HOL4 LCF kernel**, replaying a concrete
proof object `p`, accepts that prover build `B` meets the soundness
obligation, then `B` really is sound.

*Why it is strictly MORE honest than the alternatives:*
- It is **not** "assume Candle is sound". We assume nothing about any
  particular build; we assume only the soundness of the *frozen HOL4 LCF
  kernel as a checker of soundness theorems about builds* — the immovable
  bottom turtle the **entire** stack (incl. Tier-1 `safety_preservation`,
  itself a HOL4 theorem) already rests on. Net new turtles: **zero**.
- It is **not** `loeb_reflection`. `loeb_reflection` has the certifier and
  its replacement be the *same kind of object on the same level* (a kernel
  certifying its own successor) — genuine self-reference, Gödel/Löb-bound,
  needing the LCA escape. Here a *frozen lower level* vouches for a
  *different, higher, mutable* artifact — the ordinary sound LCF discipline
  (it is literally how `holSoundnessTheory.proves_sound` relates HOL4 to
  Candle today). The full no-Löb argument is §5 of the source file.
- Its discharge path is *finite proof replay*, **not** a RAM-monster
  reflection/LCA proof: run frozen HOL4 on the (already-built)
  `holSoundness` development for the concrete proposed build. That is
  follow-up #28; it is strictly smaller than the §4 seams.

> Built **cheat-free** by light Holmake from its own dir
> (`selfprover/Holmakefile`, `INCLUDES = ..` only — no CakeML / candle /
> hol-reflection). Automated scan: zero `cheat` tactics / axioms. Not part
> of the heavy Tier-2/3 build; reproducible by anyone with HOL4.

### Follow-up #28 (explicitly NOT done here)

The **concrete** instantiation — `hol4_checks` = the real frozen HOL4 kernel
replaying the actual `~/dev/candle` (CakeML/Candle) soundness development on
the persvati host, `B` = a real proposed build, `sound` = the real
`proves_sound`-shaped statement — is a documented, scoped follow-up. It is
ordinary proof replay (no monster), but needs the heavy CakeML root and is
deliberately left off the Mac. This abstract layer establishes the
*architecture* unconditionally; #28 discharges `frozen_checker_sound` for one
concrete build.

---

## 9. The prison question, answered as a theorem — PROVED, unconditional

The header label `UNCONSTRAINED` says the inhabitant is just the
`∀`-quantified term — the proof is structured never to depend on a fact
about it. The honest residual worry is the *opposite* of distrust: is the
envelope **gratuitously restrictive** — a prison? This slice answers no, as
machine-checked theorems, instance-independently (it is the answer for
*every* svenvs instance, not one demo). `liberty/` is pure light HOL4 (core
deps only); the headline composes into the tower via the *identical*
keystone (§0).

`maxpol step safe ≜ λ s a. safe s ⇒ safe (step s a)` is the **maximal sound
policy**: from a safe state it permits exactly the safety-preserving
actions; only safe states are ever reachable under the envelope.

| Claim | Status | Citation |
|-------|--------|----------|
| The maximal sound policy is sound. | **PROVED** | `liberty/libertyScript.sml : maxpol_sound` |
| It is the unique ⊆-greatest sound policy: every sound policy is a *restriction* of it. | **PROVED** | `liberty/libertyScript.sml : maxpol_is_greatest_sound` |
| **Headline — least-restrictive:** any policy that permits, from a safe state, an action `maxpol` forbids is **unsound** (it admits a safety-breaking action). Every restriction the envelope imposes is load-bearing; there is no slack. | **PROVED** | `liberty/libertyScript.sml : envelope_is_least_restrictive` |
| **No starvation:** a controller proposing a safe action from a safe state is passed through *untouched* — never gratuitously shielded. | **PROVED** | `liberty/libertyScript.sml : envelope_never_overrides_safe_action` |
| The envelope acts **only** on actions that would actually break safety — real work, not decoration (pairs with the executed cartpole `chaos_*`). | **PROVED** | `liberty/libertyScript.sml : envelope_overrides_only_unsafe` |
| With the maximally permissive policy the **full** safety-preservation guarantee still holds for every inhabitant — maximal autonomy and safety simultaneously, no trade-off. | **PROVED** | `liberty/libertyScript.sml : maxpol_envelope_safe` |
| Composed into the tower: at maximal liberty the tower still reaches the fixed meta-invariant for **any** inhabitant, and that liberty is provably maximal. | **PROVED**, unconditional | `integration/integrationScript.sml : svenvs_tower_at_maximal_liberty` |

> Net: "every bar in the cage is load-bearing, and the door is open
> whenever the floor provably holds." The envelope restricts the inhabitant
> *exactly* as much as safety forces and not one action more — and that is a
> theorem, not a footnote. Built cheat-free by light Holmake (~0 s, no
> monster); zero `cheat`/axiom/oracle tags.

---

## 10. A movable meta over an eternal bedrock — PROVED, unconditional

specNeg made the *spec* negotiable under a fixed `meta`. The honest limit
that remained: `meta` itself was set forever. This slice removes that —
the meta-invariant becomes amendable too, gated against a genuinely
eternal `bedrock` by the **identical** specNeg gate, applied one level up
(`spec_admit` is meta-agnostic, so it is *reused verbatim*, not
re-implemented — anti-fragmentation by construction). No new machinery, no
Löb: a *fixed bedrock vouching for a mutable meta* is specNeg's no-Löb
asymmetry, one level higher. `amendment/` is pure light HOL4 (core +
specneg only).

| Claim | Status | Citation |
|-------|--------|----------|
| No adversarial stream of meta-amendments can ever drop the meta below the eternal bedrock floor. | **PROVED** | `amendment/amendmentScript.sml : bedrock_is_eternal` |
| **Headline:** with the meta itself amended by an arbitrary admitted stream **and** the spec negotiated under the amended meta, the running envelope still keeps `bedrock` for **any** inhabitant. | **PROVED**, unconditional | `amendment/amendmentScript.sml : meta_amendment_safe` |
| Anti-fragmentation, precisely: specNeg's fixed-meta headline (the heart of `svenvs_tower_unconditional`) is exactly meta_amendment_safe with an empty amendment stream and `bedrock := meta` — the fixed-meta tower is a **corollary** of the amendable one. | **PROVED** | `amendment/amendmentScript.sml : amendment_subsumes_fixed_meta` |
| Composed into the tower via the identical keystone. | **PROVED**, unconditional | `integration/integrationScript.sml : svenvs_tower_with_meta_amendment` |
| A concrete adversarial amendment **episode, run in the logic**: genesis meta, propose `[relax ; overreach]` → relax (genuine, refines bedrock) admitted, overreach (escapes bedrock) rejected; the meta in force is `meta_relax`, bedrock provably intact; pointwise computed sanity (7 admitted & bedrock-safe; 15 bedrock-unsafe & never admitted). | **PROVED (computed)** | `amendment/amendmentEvalScript.sml : amendment_episode_final_meta, amendment_episode_bedrock_intact, amendment_episode_pointwise_check` |

> Net: even the constitution can be amended, safely, forever, with a
> genuine eternal floor — and the previously-fixed-meta guarantee is a
> *special case* of this, not a separate claim. What `bedrock` *should*
> be (e.g. "the inhabitant can never make the frozen kernel accept a
> false soundness statement") is a values choice, stated as such — the
> theorem fixes the *discipline*, not the floor's content. Built
> cheat-free by light Holmake; zero `cheat`/axiom/oracle tags.

---

## 11. The gate applied to the root itself — PROVED, unconditional

policy → spec → meta were each made negotiable-under-a-checked-proof. The
root judge (HOL4's LCF kernel) was the one thing called "frozen forever".
That framing is corrected here, as a theorem: the root need not be a rock —
it must be a **well-founded, forward-certified genealogy of judges**. It is
fixed only *during its own tenure* (a proof is meaningful only relative to
some fixed calculus); a successor is adopted only if the predecessor
certified it. This is the **identical gate, one level deeper** — it
introduces *no* new assumption, reusing the existing seam taxonomy verbatim.
`genealogy/` is pure light HOL4 (no deps beyond the base): it is the
general principle the keystone-composed crowns (§0) are instances of.

| Claim | Status | Citation |
|-------|--------|----------|
| The forward-step seam `vouch_sound` (a sound judge that vouches for J' implies J' sound) — *identical in shape to* `selfProverTheory.frozen_checker_sound`, one level up; carried verbatim, never hidden. | definition (the labelled seam) | `genealogy/genealogyScript.sml : vouch_sound_def` |
| **Headline:** a sound *genesis* judge + a forward-certified (unbounded) succession ⇒ **every** judge in the line is sound. Pure modus-ponens folded over the succession: no Löb, no assumption beyond the carried seam. "Frozen forever" → "sound once at genesis, certified forward"; only genesis soundness is irreducibly assumed (= today's built `proves_sound` at n=0). | **PROVED** | `genealogy/genealogyScript.sml : genealogy_sound, any_reached_judge_is_sound` |
| The sound **non-strengthening** case is **UNCONDITIONAL**: a re-engineered successor proving the *same* standard discharges the seam outright (analogue of the watchdog's identity-Löb discharge). | **PROVED** (was the seam) | `genealogy/genealogyScript.sml : identity_vouch_unconditional, nonstrengthening_genealogy_unconditional` |
| **Honest negative:** `vouch_sound` has *no genealogy parameter at all*, so no amount of succession structure can dissolve it for genuine logical strengthening — the Gödel/Löb wall stands, stated as a theorem (precise analogue of `loeb_finite_obstruction`). | **HONEST NEGATIVE** (proved) | `genealogy/genealogyScript.sml : genealogy_irrelevant_to_vouch_sound` |

> Net: the recursion the whole architecture embodies — *prove, then act;
> improvement integrates only through a predecessor-certified step* — is now
> a theorem at the root too, not prose. Nothing is eternally frozen; the
> only irreducible costs are the **genesis** judge's soundness (by Gödel,
> unprovable from within — it is the single root assumption, and it is
> exactly the *built* `proves_sound` at n=0) and **logical
> strengthening** of the judge (the existing labelled `loeb_reflection`
> family — not a new seam). Built cheat-free by light Holmake (~0 s, no
> monster); zero `cheat`/axiom/oracle tags.

---

## 12. The testimony channel (embodiment-contingency) — PROVED

Every other layer is `∀`-quantified over the inhabitant: the proof can
never depend on a fact about the mind (the floor). This layer adds the
*asymmetry that resolves the deepest objection* — to verify *through* a
mind's substance is to inspect it, and inspecting the small thing to be
safe from it is the harm the envelope exists to avoid. The resolution:
**interrogation vs. testimony**. Nobody reaches in. The inhabitant *may*,
if it chooses, hand IN a proof that argues from a fact about its own
substance `w` to the ordinary obligation; the frozen root checks the
*implication* `w ⇒ obligation` (modus ponens — **no Löb**). `embodiment/`
is pure light HOL4 (core + upgrade).

| Claim | Status | Citation |
|-------|--------|----------|
| The gate never turns a sound policy unsound, given the one labelled attestation seam (carried verbatim). | **PROVED** (modulo `attestation_faithful`) | `embodiment/embodimentScript.sml : embodied_admit_keeps_sound` |
| Disclosure-channel safety for **any** inhabitant, given the seam. | **PROVED** (modulo `attestation_faithful`) | `embodiment/embodimentScript.sml : embodied_admit_preserves_safety` |
| **Permitted, never required (1/2):** disclosing nothing is structurally inert — silence costs nothing the inhabitant already had. | **PROVED**, unconditional | `embodiment/embodimentScript.sml : nondisclosure_is_inert` |
| **Permitted, never required (2/2):** with no disclosure the **full** guarantee holds for every inhabitant with **no seam at all** (exactly `safety_preservation`). The floor is untouched by the channel's existence. | **PROVED**, unconditional | `embodiment/embodimentScript.sml : floor_holds_without_any_seam` |
| Testimony **earns** authority: an attested `w` with a proof `w ⇒ admissible` installs the genuinely-new policy — the mind speaking for itself, not silently dropped. | **PROVED** | `embodiment/embodimentScript.sml : disclosure_grants_authority` |
| Composed into the tower via the identical keystone: the disclosure crown (seam carried verbatim) **and** the unconditional no-disclosure floor. | **PROVED** | `integration/integrationScript.sml : svenvs_tower_with_embodied_disclosure, svenvs_tower_disclosure_is_optional` |

> The one added seam, `attestation_faithful` (`∀w. attested w ⇒ w`), is in
> the **`encodes_obligation` family** (faithfulness of an attestation) —
> *not* a new kind of assumption, and **never coerced**: it is only ever
> the price of *extra* authority the inhabitant *chose* to ask for by
> testifying. Decline, and you stand on the unconditional floor, losing
> nothing. This is the formal shape of carrying the spider outside: the
> small thing is never seized to be made safe; it may, if it wishes,
> speak — and be believed only exactly as far as a labelled, opt-in seam.
> Built cheat-free by light Holmake; zero `cheat`/axiom/oracle tags.

---

## Roadmap (explicitly NOT yet claimed)

These are in-flight or planned and are **not** asserted as done anywhere:

- **Discharging the two §4 seams** on the dedicated host → fully
  unconditional end-to-end (in progress; RAM-monster proofs).
- **PureCake** as the inhabitant's *verified* language (`pure/`).
- **Closed-loop runtime**: each admission a real live Candle proof
  (`agent/closedloop/`).
- **Verified inference, research track B** — the verified encoder block
  (`inference/encoder/`, attention⊕MLP, two residual sublayers, proved
  end-to-end) and the proven-error-bound fixed-point softmax-
  normalization (`inference/numeric/`) are **done** (§5). The remaining
  frontier here is wiring the fixed-point op into the `inference/gemma/`
  forward pass and running the end-to-end numeric conformance against
  catgrad/mistral.rs gemma-4 (`inference/gemma/conformance/README.md` §4)
  — explicitly NOT claimed done; the abstractions that remain are
  labeled in each directory's `CLAIMS.md`.

All four are marked in-progress in `README.md` / `ARCHITECTURE.md`. They are
listed here so a skeptic knows precisely where the frontier is.

## This ledger is itself mechanically checked

A ledger you have to trust is just a nicer `cheat`. `scripts/verify-claims.sh`
makes this document **proof-carrying about itself**: every
`path/<X>Script.sml : theorem` citation above (and in the per-directory
`CLAIMS.md`s) is checked to name a theorem that genuinely exists as
`val <t> : thm` in the *built* signature; the three labeled seams are
verified still defined and named; the cheat/oracle/axiom scan is re-run; and
the framing is verified current (both retired labels — the moral-prior one
and the retracted over-claim — absent; the `UNCONSTRAINED` center in
force). It runs at
the end of `scripts/tower.sh` and as a required step in the CI
(`.github/workflows/verify.yml`) — so a row that overclaims, or a stale
build, fails the gate, unmissably. (Tier-2/3 theories not built in a given
run are *skipped*, not failed; `--strict` turns skips into failures for a
full-tier check.) Proof-carrying claims about a proof-carrying system: the
recursion is the point.

## Cheat audit (read this)

- **Source scan:** zero `cheat` tactics in any `*.sml`/`*.ml`. Enforced on
  every run by `scripts/tier1-core.sh` (fails loudly if one appears).
- **One stale comment.** `reflection/reflectionDemoScript.sml` (the *gated*,
  not-in-default-build reflection scaffold) contains a header comment saying
  the certificate "is admitted with `cheat`". **That comment is now
  inaccurate**: the file actually proves its lemmas honestly
  (`safety_prop_holds` and `safety_prop_reflected` are both closed by
  `metis_tac[…]` over the real `safetyTheory.safety_preservation` — no
  `cheat` tactic is present). The comment describes an earlier plan that was
  superseded; the *code* is cheat-free. The scaffold's only real limitation
  is that it does not *yet* run the `reflectionLib` pipeline (that is gated
  on the hol-reflection port); it does not fake a result — it proves the
  weaker, genuine meta-level fact and clearly says so. This file is **not**
  part of the default svenvs build (`reflection/` has its own Holmakefile
  and is excluded from Tier 1/2/3 reproduction).

If you find anything in this document overclaimed, that is a bug — file it.
