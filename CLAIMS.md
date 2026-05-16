# CLAIMS.md — exactly what svenvs proves, and what it does not

A skeptic-facing ledger. Every row says **what** is claimed and **how** it is
established, using one of four honesty labels:

| Label | Meaning |
|-------|---------|
| **PROVED** | A HOL4 (or live Candle) machine-checked theorem. No `cheat`, no `sorry`, no admitted goal. Cited as `file : theorem`. Re-checked by `scripts/reproduce.sh` / `./demo.sh`. |
| **TRUSTED-GLUE** | Small, auditable non-proof code you must read to believe the demo wires the proof to reality (e.g. the ~50-line Python policy mirror). Explicitly bounded. |
| **UNTRUSTED** | Deliberately not relied upon (the LLM). The theorems are `∀`-quantified over it; nothing about it is assumed. |
| **ASSUMED** | An explicit, *labeled*, literature-standard hypothesis appearing verbatim in the source as a `Definition`/antecedent — **not** a `cheat`. Stated, never hidden. Three of these exist in general (`loeb_reflection`, `encodes_obligation`, `frozen_checker_sound`); each has a known discharge path, and `encodes_obligation` is **already discharged for the shipped finite watchdog instance** (§7). |

There are **zero `cheat` tactics** anywhere in the repository. This was
verified by an automated scan (`scripts/tier1-core.sh`) and by hand; see the
"Cheat audit" section at the end for the one stale *comment* that says
"cheat" and why the code it describes does not.

---

## 1. The controller-agnostic core — PROVED, unconditional

The whole point: assurance comes from the *envelope*, never from the
(untrusted, possibly adversarial, never-inspected) controller/inhabitant.

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

## 3. The adversarial-LLM tool-agent — PROVED, unconditional

The "controller" is now an opaque LLM emitting tool calls; the safety spec
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
| Gemma (or the `--mock` scripted adversary). | **UNTRUSTED** | Zero assumptions; deliberately jailbroken. The `∀agent` theorem does not care. Verifies the cage, not the animal. |
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

## 5. Verified inference (research track B) — PROVED, but TOY

| Claim | Status | Citation |
|-------|--------|----------|
| A ReLU dense net over integers: forward pass structurally correct (non-negativity preserved, shape correct). | **PROVED** | `inference/mlpInferenceScript.sml : relu_nonneg, layer_nonneg, layer_shape, mlp_shape, mlp_pres_nonneg, mlp_nonneg` |
| A concrete net runs in-logic: `mlp demo_net [2;3] = [11]`; ReLU genuinely clamps `-5 → 0`. | **PROVED (EVAL)** | `inference/mlpInferenceScript.sml : demo_forward_eval, demo_relu_clamps` |
| "This is Gemma-scale / a verified transformer." | **NOT CLAIMED** | Explicitly TOY — the *seed* of verified inference, not the thing. |

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

## Roadmap (explicitly NOT yet claimed)

These are in-flight or planned and are **not** asserted as done anywhere:

- **Discharging the two §4 seams** on the dedicated host → fully
  unconditional end-to-end (in progress; RAM-monster proofs).
- **PureCake** as the inhabitant's *verified* language (`pure/`).
- **Closed-loop runtime**: each admission a real live Candle proof
  (`agent/closedloop/`).
- **Verified tensor acceleration / attention** (`inference/accel/`,
  `inference/attn/`) — climbing from the toy MLP toward a verified block.

All four are marked in-progress in `README.md` / `ARCHITECTURE.md`. They are
listed here so a skeptic knows precisely where the frontier is.

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
