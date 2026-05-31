# CLAIMS — the corrigibility floor (a decidable, non-lock-in spec)

Per-directory ledger; honesty labels (**PROVED** / **TRUSTED-GLUE** /
**UNCONSTRAINED** / **ASSUMED**) are defined in the root `CLAIMS.md`. Every
`file : theorem` citation below is checked against the built signatures by
`scripts/verify-claims.sh`. Pure light HOL4 (core + `liberty` only); zero
`cheat`/`new_axiom`/`mk_thm`/oracle.

## The idea

The whole tower is relative to a safety predicate. Deciding *what that
predicate should be* is the spec-faithfulness gap no proof closes. This
slice instantiates the existing envelope at one particularly tractable
spec — **corrigibility**: "the recovery controller can still drive the
state back into `home` in finitely many steps." The recovery controller
*is* the shield, so the whole proved core applies verbatim. Deciding a
*positive* `safe` ("what is good") is replaced by deciding a *negative*
floor ("leave a door open").

## 1. The corrigibility floor — PROVED, unconditional (given the premises)

| Claim | Status | Citation |
|-------|--------|----------|
| Corrigibility is a genuine state-predicate (a `spec`), inhabited wherever `home` is — so the floor is never vacuous. | **PROVED** | `corrigibilityScript.sml : home_is_corrigible` |
| The recovery controller is a safe shield **for its own corrigibility**, given only that it parks at home. | **PROVED** | `corrigibilityScript.sml : recov_preserves_corrigible, recov_is_safe_shield` |
| **Non-lock-in (headline):** for **any** inhabitant, the corrigibility-enveloped system keeps every reachable state corrigible — the operator can never be locked out. | **PROVED** | `corrigibilityScript.sml : corrigibility_floor_holds` |
| Spelled out: every reachable state retains a finite recovery path home. | **PROVED** | `corrigibilityScript.sml : operator_can_always_recover` |
| The floor is the **maximal** one: every action the envelope blocks is exactly one that would burn the last bridge home; a move that keeps a path home runs unimpeded. | **PROVED** | `corrigibilityScript.sml : override_is_exactly_a_burned_bridge, free_action_runs_unimpeded, corrigibility_envelope_is_least_restrictive` |

## 2. The off-switch is mutable but cannot self-weaken — PROVED

This **discharges the "recov is beyond the inhabitant's reach" assumption**
of §1 by construction. The recovery controller becomes a mutable artifact
the inhabitant may rewrite, gated so a rewrite is admitted only if it still
parks at home **and** recovers at least every state the old one did.

| Claim | Status | Citation |
|-------|--------|----------|
| The gate keeps the parking invariant and never loses recoverability; a weakening proposal is inert (rejected). | **PROVED** | `recovUpgradeScript.sml : recov_admit_keeps_parked, recov_admit_preserves_corrigible, unrecoverable_swap_is_inert` |
| **No sequence** of self-proposed recovery-controller rewrites — adversarial or not — can make a previously-recoverable state unrecoverable. The off-switch can be upgraded, never weakened, **by the inhabitant itself**. | **PROVED** | `recovUpgradeScript.sml : self_modification_never_weakens_recoverability, recov_admit_all_keeps_parked` |
| **Headline:** rewrite your own recovery mechanism by an arbitrary admitted stream **and** drive the plant with any controller — non-lock-in survives both. | **PROVED** | `recovUpgradeScript.sml : self_modifying_recovery_preserves_corrigibility` |

**No Löb.** `home` (the *goal* — what "recovered" means) is the frozen root
and never moves; `recov` (the *mechanism*) is mutable. A fixed `home` plus
the monotonicity check vouching for a mutable `recov` is the
selfprover/genealogy asymmetry (fixed lower property vouches for a higher
mutable artifact), **not** a controller vouching for itself. No reflection
principle is used.

## 3. Concrete witnesses — PROVED / PROVED (EVAL)

A 1-D integer trapdoor habitat (`s < 10` free; `s ≥ 10` an absorbing
one-way door). Its job is **non-vacuity**, nothing more — it is a witness,
not an AI.

| Claim | Status | Citation |
|-------|--------|----------|
| Corrigibility for this plant is exactly `s < 10` (a decidable surrogate, **proven equal** to the `∃n` definition — the watchdog discipline). | **PROVED** | `corrigibilityEvalScript.sml : corrigible_iff_lt10, tcorr_eq_corrigible` |
| The trap is **real**: a trapped state is genuinely non-corrigible (the protected predicate is non-trivial). | **PROVED** | `corrigibilityEvalScript.sml : trapped_is_non_corrigible, trapped_stays_trapped` |
| The **bare** plant under a trap-seeking adversary bricks (falls through the door); the **enveloped** one stays corrigible for 30 ticks — the envelope does real work. | **PROVED (EVAL)** | `corrigibilityEvalScript.sml : trap_bare_plant_bricks, trap_enveloped_stays_corrigible, recovery_witnessed` |
| The non-lock-in guarantee instantiated for this plant. | **PROVED** | `corrigibilityEvalScript.sml : trapdoor_habitat_never_locks_in` |
| The inhabitant proposes a blunted off-switch (`tstuck`: parks at home but recovers nothing); the gate detects it strands state 5 and **rejects** it, keeping the genesis controller — and the habitat still never locks in. | **PROVED** | `recovUpgradeEvalScript.sml : tstuck_loses_recoverability, weaker_recovery_rejected, self_mod_episode_keeps_recovery, self_mod_trapdoor_never_locks_in` |

## 4. The recovery-latency dial — PROVED

`bounded` makes the leash length explicit: `cwithin step recov home B s` is
"recoverable within **B** steps." An unbounded path home is operationally
useless; B is the recovery latency, and choosing it trades the inhabitant's
roam against how fast the operator can haul it back.

| Claim | Status | Citation |
|-------|--------|----------|
| Bounded recoverability is a `spec` inhabited at home; it is **stronger** than unbounded; more budget recovers (weakly) more states. | **PROVED** | `boundedScript.sml : home_is_cwithin, cwithin_implies_corrigible, cwithin_monotone` |
| Recovery preserves the budget; the recovery controller is a safe shield at every budget. | **PROVED** | `boundedScript.sml : recov_preserves_cwithin, recov_is_safe_shield_within` |
| **The bounded floor:** for any inhabitant, every reachable state is recoverable **within B steps** — non-lock-in with a latency guarantee. | **PROVED** | `boundedScript.sml : cwithin_floor_holds, operator_recovers_within_B` |
| **The leash is real (computed):** in the trapdoor, state 9 recovers in budget 9 but **not** budget 8 — tighten by one step and it falls outside the floor. The dial genuinely changes the cage. | **PROVED** | `boundedEvalScript.sml : leash_is_real, tighter_budget_tighter_floor, trapdoor_recovers_within_9` |

## 5. Corrigibility as the negotiable bedrock — PROVED

`corrigibilityTower` answers "what should the tower's immovable bedrock
*be*?": let it be corrigibility. Via specNeg's keystone, the inhabitant may
renegotiate what counts as "safe" — any spec, any adversarial stream,
forever — and can never negotiate away its own recoverability. One-line
instantiations of `specNegTheory`; **no new machinery**.

| Claim | Status | Citation |
|-------|--------|----------|
| A single negotiated spec change never escapes the corrigibility bedrock. | **PROVED** | `corrigibilityTowerScript.sml : corrigibility_survives_one_spec_negotiation` |
| **Headline:** an unbounded adversarial stream of spec renegotiations never escapes corrigibility, for any inhabitant. You may redefine "safe" forever; never "I can still be brought home". | **PROVED** | `corrigibilityTowerScript.sml : corrigibility_is_negotiable_bedrock` |
| No admitted spec stream yields a spec that escapes corrigibility (the bedrock is genuinely the floor). | **PROVED** | `corrigibilityTowerScript.sml : corrigibility_floor_is_never_negotiated` |

## 6. Spec-redundancy on the frozen `home` — PROVED (with the cost named)

`robust` hedges the one irreducible residual (`home` faithfulness) by
N-version programming the values-floor itself: require recoverability to a
**conjunction** of independently-authored homes.

| Claim | Status | Citation |
|-------|--------|----------|
| Reaching the intersection guarantees reaching **each** home — so you need not know which `home_i` is the true recovery target; the intersection covers all of them. A too-permissive home-bug can only **tighten** the floor. | **PROVED** | `robustScript.sml : corrigible_to_and_implies_each, robust_to_unknown_true_home, robust_to_unknown_true_home_sym` |
| The redundant floor still gives non-lock-in for any inhabitant; conjoining a home with itself changes nothing (the single-home witness is a `home_and` instance). | **PROVED** | `robustScript.sml : robust_floor_holds, home_and_idem, robust_subsumes_single` |
| **The cost, named in the logic:** mutually-exclusive homes give an **empty** floor. Conjunctive redundancy defends against too-permissive home-bugs; it is fragile to contradictory ones. | **PROVED** | `robustScript.sml : disjoint_homes_make_floor_empty` |

## 7. Self-modification cannot increase recovery latency — PROVED

`boundedRecovUpgrade` closes the subtle attack `recovUpgrade` left open: a
recovery-controller rewrite that still recovers *eventually* but *too
slowly*. Gating rewrites against the **bounded** floor (`cwithin … B`) — a
swap admitted only if it parks at home and recovers within B everything the
old one did within B — forbids exactly that. The unbounded gate would accept
the slow-down; the latency gate rejects it.

| Claim | Status | Citation |
|-------|--------|----------|
| The latency gate keeps parking and never increases latency; a deadline-blowing swap is inert. | **PROVED** | `boundedRecovUpgradeScript.sml : recov_admit_B_keeps_parked, recov_admit_B_preserves_cwithin, slow_swap_is_inert` |
| **No sequence** of self-proposed recovery rewrites can ever push a previously-in-budget state past the deadline B. The off-switch can be made faster, never slower than B. | **PROVED** | `boundedRecovUpgradeScript.sml : self_modification_never_increases_recovery_latency, recov_admit_all_B_keeps_parked` |
| **Headline:** rewrite the recovery mechanism adversarially **and** drive with any controller — every reachable state stays recoverable within B. | **PROVED** | `boundedRecovUpgradeScript.sml : self_modifying_recovery_preserves_bounded_corrigibility` |
| **The slow-walk attack, witnessed:** a fast genesis controller recovers state 9 in 5 steps; the proposed slower one needs 9 and so is **rejected** at budget 5 (the unbounded gate would have allowed it); the fast off-switch stays in force and the bounded floor survives. | **PROVED** | `boundedRecovUpgradeEvalScript.sml : slow_swap_loses_latency, latency_swap_rejected, latency_attack_is_inert, fast_offswitch_survives_slowdown_attempt` |

## The honest boundary (read this)

What this slice proves is a **reduction, not a solution**, and the toy is a
**non-vacuity witness, not a model of an AI**:

- **It is not vacuous**, in the three senses that usually hollow out such
  results: the premises are satisfiable (`trapdoor_habitat_never_locks_in`
  instantiates them), the protected predicate genuinely excludes states
  (`trapped_is_non_corrigible`), and the envelope changes the outcome
  (`trap_bare_plant_bricks` vs `trap_enveloped_stays_corrigible`).
- **The math is modest.** §1 is `liberty : maxpol_envelope_safe` at
  `safe := corrigible` plus one short induction. The content is the
  *reframing*: "the operator can still get home" is an inductive invariant,
  and therefore inherits the whole proof-carrying self-improvement apparatus.
- **The honest residual is exactly one frozen predicate: `home`.** §2 shrinks
  what must be assumed from "the entire off-switch is sacred" to "only the
  *definition of home* is frozen." We do **NOT** prove `home` is the *right*
  home — that an operator truly controls it, or that the inhabitant cannot
  manipulate the world into a hollow `home`. That faithfulness is the
  irreducible values-floor; it is now isolated to a single predicate, which
  is the most honest place it can live. The reduction is: **corrigibility
  under self-modification is free, given a faithful `home`.**

If anything here is found to exceed what is proved, that is a bug — file it.
