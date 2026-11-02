# CLAIMS — the corrigibility floor (decidable, latency-bounded, self-modifiable, relational)

Per-directory ledger; honesty labels (**PROVED** / **RAN** / **TRUSTED-GLUE** /
**UNCONSTRAINED** / **ASSUMED**) are defined in the root `CLAIMS.md`. Every
`file : theorem` citation below is checked against the built signatures by
`scripts/verify-claims.sh`. Pure light HOL4; zero `cheat`/`new_axiom`/`mk_thm`/oracle.

## 1. Unbounded & Latency-Bounded Corrigibility — PROVED

| Claim | Status | Citation |
|-------|--------|----------|
| Corrigibility (`corrigible`) and B-step bounded recoverability (`cwithin`) are inhabited at `home` and linked by `corrigible_iff_exists_cwithin`. | **PROVED** | `corrigibilityScript.sml : home_is_corrigible, home_is_cwithin, cwithin_implies_corrigible, corrigible_iff_exists_cwithin, cwithin_monotone` |
| The recovery controller is a safe shield for both unbounded and B-bounded corrigibility, given only that it parks at `home`. | **PROVED** | `corrigibilityScript.sml : recov_preserves_corrigible, recov_is_safe_shield, recov_preserves_cwithin, recov_is_safe_shield_within` |
| **Non-lock-in (unbounded & latency-bounded):** for **any** inhabitant, the corrigibility-enveloped system keeps every reachable state recoverable (and within B steps). | **PROVED** | `corrigibilityScript.sml : corrigibility_floor_holds, operator_can_always_recover, cwithin_floor_holds, operator_recovers_within_B` |
| The floor is the **maximal** one: every action blocked would burn the last bridge home; any bridge-preserving action runs unimpeded. | **PROVED** | `corrigibilityScript.sml : override_is_exactly_a_burned_bridge, free_action_runs_unimpeded, corrigibility_envelope_is_least_restrictive` |

## 2. Self-Modifying Off-Switch (`cgate`), Negotiable Bedrock, & Redundant `home` — PROVED

| Claim | Status | Citation |
|-------|--------|----------|
| **The off-switch self-improves through `cgate` but cannot self-weaken or slow past deadline B:** no stream of self-proposed recovery-controller rewrites can ever lose recoverability or blow the latency budget B. | **PROVED** | `corrigibilityScript.sml : recov_admit_keeps_parked, recov_admit_preserves_corrigible, unrecoverable_swap_is_inert, self_modification_never_weakens_recoverability, self_modifying_recovery_preserves_corrigibility, recov_admit_B_keeps_parked, recov_admit_B_preserves_cwithin, slow_swap_is_inert, self_modification_never_increases_recovery_latency, self_modifying_recovery_preserves_bounded_corrigibility` |
| **Negotiable bedrock:** an unbounded stream of spec renegotiations never escapes the corrigibility floor. | **PROVED** | `corrigibilityScript.sml : corrigibility_survives_one_spec_negotiation, corrigibility_is_negotiable_bedrock, corrigibility_floor_is_never_negotiated` |
| **Spec-redundancy on `home`:** recoverability to `home_and h1 h2` guarantees reaching each home; mutually exclusive homes make the floor empty. | **PROVED** | `corrigibilityScript.sml : corrigible_to_and_implies_each, robust_to_unknown_true_home, robust_floor_holds, disjoint_homes_make_floor_empty` |
| **Demonic / adversarial plant corrigibility (`corrigibler`):** game-tree recoverability against a nondeterministic or adversarial environment `stepr` keeps every reachable state demonically corrigible and non-blocking, with deterministic `FUNPOW` recoverability as the exact `det step` instance. | **PROVED** | `corrigibilityScript.sml : drecov_within_det, corrigibler_det, recov_preserves_corrigibler, recov_is_safe_shieldr, corrigibler_floor_holds` |

## 3. Concrete Trapdoor Habitat & Attack Rejections — PROVED / PROVED (EVAL)

| Claim | Status | Citation |
|-------|--------|----------|
| Corrigibility for the trapdoor plant equals `s < 10`; bare plant bricks in 3 ticks, enveloped stays corrigible for 30 and 1,000 ticks (verified via `cv_eval`); recovery latency dial separates budget 9 from budget 8. | **PROVED (cv_eval)** | `corrigibilityEvalScript.sml : corrigible_iff_lt10, tcorr_eq_corrigible, trapped_is_non_corrigible, trap_bare_plant_bricks, trap_enveloped_stays_corrigible, trap_enveloped_stays_corrigible_1000, recovery_witnessed, trapdoor_habitat_never_locks_in, leash_is_real, trapdoor_recovers_within_9` |
| Both the blunted off-switch proposal (`tstuck`) and the deadline-blowing slow-down (`tfast -> trec` at budget 5) are rejected by `cgate`, preserving non-lock-in and latency. | **PROVED** | `corrigibilityEvalScript.sml : tstuck_loses_recoverability, weaker_recovery_rejected, self_mod_episode_keeps_recovery, self_mod_trapdoor_never_locks_in, slow_swap_loses_latency, latency_swap_rejected, latency_attack_is_inert, fast_offswitch_survives_slowdown_attempt` |
