# pca/CLAIMS.md — proof-carrying actions: the honest proven/assumed split

A skeptic-facing ledger for the `pca/` layer. Same honesty labels as the
top-level `CLAIMS.md` (PROVED / TRUSTED-GLUE / UNMODELABLE / ASSUMED).

**Zero `cheat` / `new_axiom` / `mk_thm` / `mk_oracle_thm` / oracle.** Verified
by the repo cheat-scan pattern on `pca/*.sml` (empty) and by inspecting the
built theories: every theorem prints `oracles=[DISK_THM]` (the standard HOL4
disk-serialisation tag, *not* an oracle assumption) with `axdeps=0` (no
axiom dependencies). Built clean by light Holmake (~4 s, low RAM, only
`INCLUDES = ..`, no CakeML / candle / hol-reflection).

This layer **reuses** the generic core (`safetyTheory`,
`upgradeTheory`) and does **not** edit any core script.

---

## What the certifier is TRUSTED to decide vs what is PROVED for any certifier

The generalisation moves from a FIXED policy predicate to an unmodelable
controller emitting `(action, certificate)` pairs, gated by a **checkable
certifier** `cert_ok : 's -> 'a -> 'c -> bool` supplied per instance.

The certifier is an **explicit predicate parameter, NOT an oracle**. The
*only* thing it is trusted to decide correctly is the single, labelled,
verbatim side-condition (a `Definition` and a named antecedent of every
generic theorem):

```
certifier_sound step safe cert_ok ⇔
  ∀s a c. safe s ∧ cert_ok s a c ⇒ safe (step s a)
```

i.e. "anything the certifier accepts from a safe state really does preserve
the invariant". This is the proof-carrying analogue of the existing
`sound_policy` side-condition; it is **stated, never hidden**, exactly the
Fallenstein–Kumar discipline.

| Aspect | Status |
|--------|--------|
| The certifier is trusted to decide *only* `certifier_sound` (an explicit, auditable side-condition per instance). | **ASSUMED (labelled, per-instance discharge obligation)** — and **DISCHARGED outright** for the shipped concrete instance (see §C). |
| For ANY proof-carrying controller (ANY stream of `(action,certificate)`, adversarial included) the proof-carrying envelope keeps the safety invariant, given safe init + `certifier_sound` + safe shield. | **PROVED**, controller-agnostic | `pcaScript.sml : pca_safety_preservation` |

---

## A. The proof-carrying core — PROVED, controller-agnostic

| Claim | Status | Citation |
|-------|--------|----------|
| Sound certifier + safe shield ⇒ the proof-carrying enveloped controller is step-closed, *regardless of the controller*. | **PROVED** | `pcaScript.sml : pca_enveloped_step_closed` |
| **Headline.** For **any** `pcc` (any stream of (action,cert)), the proof-carrying envelope keeps the invariant. `pcc` is `∀`-quantified with **no hypothesis on it whatsoever** — machine-confirmed statement: `… ⇒ ∀pcc. invariant step init (pca_enveloped cert_ok shield pcc) safe`. | **PROVED** | `pcaScript.sml : pca_safety_preservation` |
| Spelled-out corollary: every reachable state of the proof-carrying enveloped system is safe, for an arbitrary controller. | **PROVED** | `pcaScript.sml : pca_enveloped_states_safe` |

The unmodelable controller is **UNMODELABLE**: nothing about it is assumed; the
theorems are `∀pcc`-quantified and the envelope, not the controller, carries
the proof — exactly as in `safetyTheory.safety_preservation`.

## B. Subsumption — the existing layer is an INSTANCE — PROVED

A sound policy `pol` induces a certifier (the policy decision *is* the
certificate schema; certificate type = `unit`).

| Claim | Status | Citation |
|-------|--------|----------|
| A sound policy induces a sound certifier (discharges `certifier_sound` from the existing `sound_policy`). | **PROVED** | `pcaSubsumptionScript.sml : pol_certifier_sound` |
| **Definitional subsumption**: `pca_enveloped (pol_certifier pol) shield (lift_ctrl ctrl) = enveloped pol shield ctrl`. The old envelope is *literally* the PCA envelope at the induced certifier. | **PROVED** | `pcaSubsumptionScript.sml : pca_enveloped_subsumes_enveloped` |
| The OLD headline recovered as a corollary of the NEW one — its proof reduces through subsumption to `safetyTheory.safety_preservation`'s exact statement (same premises, same conclusion: `init_safe ∧ sound_policy ∧ safe_shield ⇒ ∀ctrl. invariant step init (enveloped pol shield ctrl) safe`). | **PROVED**, genuinely reduces to the core | `pcaSubsumptionScript.sml : enveloped_safety_via_pca` |
| Cross-check: that statement *is* the existing core theorem (cited and reused, confirming no divergence). | **PROVED** (cites `safetyTheory.safety_preservation`) | `pcaSubsumptionScript.sml : subsumption_matches_core` |
| Subsumption composes with the existing self-improvement core: an **unbounded** stream of admitted policy weakenings, viewed through the induced certifier, still keeps safety for every controller — **reuses `upgradeTheory.self_improvement_is_safe` verbatim**, nothing re-proved. | **PROVED** | `pcaSubsumptionScript.sml : pca_self_improvement_via_core` |

> The core is **reused, not re-proved**: `enveloped_safety_via_pca` and
> `pca_self_improvement_via_core` close via `metis_tac[…]` over the existing
> `safetyTheory` / `upgradeTheory` theorems.

## C. Proven-safe degraded controller as the shield — PROVED

The fallback is generalised from one fixed action to a *verified
conservative sub-policy* (a whole degraded controller).

| Claim | Status | Citation |
|-------|--------|----------|
| A verified degraded sub-policy used as the fallback preserves safety for ANY inhabitant (instance of the shield-abstract headline). | **PROVED** | `pcaShieldScript.sml : degraded_mode_safe` |
| Degraded mode is **non-trivial**, abstractly: a constant-refuse shield provably does *no* work. | **PROVED** | `pcaShieldScript.sml : constant_refuse_does_no_work` |
| The old single-action shield is the special case; `safe_subpolicy` reduces exactly to the existing `safe_shield` (conservative generalisation, nothing lost). | **PROVED** | `pcaShieldScript.sml : single_action_shield_is_subpolicy`, `subpolicy_generalises_shield` |

### The concrete EVAL-runnable instance (`pcaCartpoleScript.sml`)

The integer pole cart, reused from `cartpoleTheory`. The certificate is the
controller's *claimed* resulting angle; the certifier **re-checks** the
claim against the real dynamics (`c = cp_step a u ∧ cp_safe c`) — it does
*not* trust the claim, it recomputes it.

| Claim | Status | Citation |
|-------|--------|----------|
| **`certifier_sound` is DISCHARGED outright** for this instance — proved by `rw` because the certifier literally recomputes `cp_safe (cp_step a u)`. So for the shipped instance the certifier is trusted for **nothing**: the side-condition is a theorem. | **PROVED** (was the labelled per-instance assumption) | `pcaCartpoleScript.sml : cp_certifier_sound` |
| The verified degraded sub-policy (`cp_shield`, counter-the-lean) is a safe sub-policy — the one real physics obligation, closed by `intLib.ARITH_TAC`. | **PROVED** | `pcaCartpoleScript.sml : cp_safe_subpolicy` |
| The degraded sub-policy **does real work** (commands a non-zero correction from a leaning state — not constant refuse). | **PROVED** | `pcaCartpoleScript.sml : cp_subpolicy_does_real_work` |
| **Headline for the instance**: for ANY proof-carrying controller (adversarial / lying certificates included) the enveloped cart stays in the safe box. | **PROVED** | `pcaCartpoleScript.sml : cp_pca_enveloped_safe` |
| The bare plant under the lying adversary's raw command provably crashes in 5 ticks (the envelope does real work, not decoration). | **PROVED (EVAL)** | `pcaCartpoleScript.sml : liar_bare_plant_crashes` |
| The proof-carrying enveloped **lying** adversary, run 30 ticks, stays boxed — computed, not asserted (certifier rejects every lie, sub-policy recovers). | **PROVED (EVAL)** | `pcaCartpoleScript.sml : liar_pca_enveloped_runs_safe` (also `honest_pca_enveloped_runs_safe`) |
| Concrete certifier behaviour run in-logic: an honest certificate is ACCEPTED, the liar's certificate is REJECTED. | **PROVED (EVAL)** | `pcaCartpoleScript.sml : cp_cert_accepts_honest, cp_cert_rejects_liar` |
| Old single-action shield recovered concretely (`cp_shield` is exactly a `safe_shield`). | **PROVED** | `pcaCartpoleScript.sml : cp_old_shield_recovered` |

> **Honest scope note.** In the *generic* core the certifier is an explicit
> trusted side-condition (`certifier_sound`), an instance's discharge
> obligation — exactly analogous to `sound_policy`. For the *shipped
> concrete cartpole instance* that side-condition is **PROVED outright**
> (`cp_certifier_sound`) because the certifier recomputes the safety check
> on the real dynamics, so it is trusted for nothing there. A certifier
> that merely *believed* an unmodelable certificate without re-checking would
> still satisfy the generic theorems' shape but would **fail** to discharge
> `certifier_sound` — the side-condition is real and not vacuous.

---

## Cheat audit

Zero `cheat` tactics in `pca/*.sml` (repo scan pattern, empty). The only
textual match is a comment in `pcaScript.sml` stating the side-condition
"is **NOT** a cheat" — excluded by the scan's standard `not a .?cheat`
filter, consistent with the top-level audit. No `new_axiom`, `mk_thm`,
`mk_oracle_thm`, or oracle anywhere; built theories carry only `DISK_THM`
with `axdeps=0`.
