# specneg/CLAIMS.md — spec-level negotiation, the honest ledger

Skeptic-facing ledger for the `specneg/` layer, using the same four honesty
labels as the top-level `../CLAIMS.md` (PROVED / TRUSTED-GLUE / UNCONSTRAINED /
ASSUMED).

**Headline honesty statement for this layer:** every row below is
**PROVED**, unconditionally, in pure light HOL4, reusing the built generic
core verbatim. There are **zero `cheat`/`new_axiom`/`mk_thm`/
`mk_oracle_thm`/oracle** uses (`grep -in cheat specneg/*.sml` matches only
the prose in this paragraph's source counterpart). Crucially this layer
carries **no `loeb_reflection` and no labelled Löb/reflection ASSUMED row at
all** — §"The Löb question" below proves the obligation does not arise; its
absence is *exhibited*, not hidden or assumed away. (Contrast:
`kernel/kernelUpgradeScript.sml` legitimately carries the labelled
`loeb_reflection`; `selfprover/selfProverScript.sml` carries the labelled
finite-replay `frozen_checker_sound`. This layer needs neither.)

---

## What this layer adds

The core fixes the safety spec `safe` and lets the inhabitant negotiate the
*policy* (`upgradeTheory`) / *prover build* (`selfprover/`). `specneg/` lifts
negotiation one level up: the inhabitant may negotiate **the safety spec
itself**, anchored to a separate, fixed, **non-negotiable meta-invariant**
`meta`. `meta` is the immovable bottom turtle of the *spec* tower — the
spec-level analogue of the frozen HOL4 root in `selfProverScript`.

## 1. Meta-invariant, refinement, transport — PROVED, unconditional

| Claim | Status | Citation |
|-------|--------|----------|
| `spec_refines new meta ⇔ ∀s. new s ⇒ meta s` — the negotiated spec must be at least as strong as the meta floor (state-predicate twin of `sv_weakeningTheory.weaker`). | **PROVED (def)** | `specNegScript.sml : spec_refines_def` |
| Refinement is reflexive and transitive. | **PROVED** | `specNegScript.sml : spec_refines_refl, spec_refines_trans` |
| **Transport:** if the running enveloped system keeps the negotiated spec invariant and that spec refines `meta`, the system keeps the **meta-invariant** invariant. (The mutable-spec guarantee is converted into the fixed-property guarantee.) | **PROVED** | `specNegScript.sml : invariant_transports_to_meta` |

## 2. The spec-admission gate — PROVED, unconditional

| Claim | Status | Citation |
|-------|--------|----------|
| A proposed spec is admissible iff it carries a checked proof that it refines `meta` **and** is a genuine, non-vacuous change (≠ `meta` itself — mirrors `upgradeTheory.admissible` requiring a real `weaker`, not a no-op). | **PROVED (def)** | `specNegScript.sml : spec_admissible_def, genuine_spec_change_def` |
| The gate installs a proposed spec iff admissible, else keeps the current spec (unproven proposal can never move the spec). | **PROVED (def)** | `specNegScript.sml : spec_admit_def` |
| Gate invariant: any spec the gate yields from a meta-refining spec still refines `meta` — accepted or rejected. | **PROVED** | `specNegScript.sml : spec_admit_keeps_refining` |
| Iterated over an **unbounded adversarial stream** of proposals: "refines `meta`" is preserved. | **PROVED** | `specNegScript.sml : spec_admit_all_keeps_refining` |
| An un-refining/vacuous proposal is **inert** (gate keeps the prior spec). | **PROVED** | `specNegScript.sml : unrefining_spec_proposal_is_inert` |

## 3. The headline — PROVED, controller-agnostic, meta fixed

| Claim | Status | Citation |
|-------|--------|----------|
| For **any** controller and **any** single inhabitant-proposed spec change, admitted only via the refinement proof, the enveloped system **never violates the immovable `meta`** (accepted or rejected). `meta` is ∀-bound at the front, never a proposable object. | **PROVED** | `specNegScript.sml : spec_negotiation_is_safe` |
| Spelled-out corollary: every reachable state is meta-safe. | **PROVED** | `specNegScript.sml : spec_negotiation_states_meta_safe` |
| For **any** controller and **any** adversarial *sequence* of proposed spec changes through the iterated gate, the system **never violates `meta`**. (Spec-level analogue of `upgradeTheory.self_improvement_is_safe`; the core's `safety_preservation` is reused once, not re-proved.) | **PROVED** | `specNegScript.sml : spec_negotiation_unbounded_is_safe` |
| The meta floor is **never negotiated**: no proposal sequence yields a spec escaping `meta` (formal content of "meta is the bottom turtle"). | **PROVED** | `specNegScript.sml : meta_floor_is_never_negotiated` |
| Core reuse: envelope set up for a spec keeps THAT spec for any controller — verbatim `safetyTheory.safety_preservation`, not re-proved. | **PROVED** | `specNegScript.sml : envelope_keeps_its_spec` |

**Controller-agnostic / meta-fixed audit.** In `spec_negotiation_is_safe`
and `spec_negotiation_unbounded_is_safe`: `meta` is universally quantified at
the very front and occurs only (i) as the refinement floor in the
hypotheses and (ii) as the conclusion's invariant — it is never an argument
of `spec_admit`/`spec_admit_all` that gets varied; the only varied inputs are
`newspec`/`proposals` (fully adversarial) and `ctrl` (fully adversarial,
never inspected). `meta_floor_is_never_negotiated` proves there is no
proposal sequence that drops the floor. There is no `meta'` anywhere.

## 4. Concrete EVAL instance — PROVED by computation

Integer pole. `meta_box a ⇔ -5 ≤ a ≤ 5` (immovable floor). Current spec
`spec_tight` (±2, over-conservative). Proposal A `spec_relaxed` (±4, a real
refining relaxation). Proposal B `spec_overreach` (±9, escapes the floor).

| Claim | Status | Citation |
|-------|--------|----------|
| The current spec refines the meta floor. | **PROVED** | `specNegEvalScript.sml : tight_refines_meta` |
| Proposal A genuinely refines `meta_box` and is a non-vacuous change → **admitted & installed**. | **PROVED** | `specNegEvalScript.sml : relaxed_refines_meta, relaxed_is_genuine_change, relaxed_is_admissible, relaxed_is_installed` |
| Proposal B does **not** refine `meta_box` → **not admissible, rejected**, prior spec retained. | **PROVED** | `specNegEvalScript.sml : overreach_does_not_refine, overreach_not_admissible, overreach_is_rejected` |
| End-to-end adversarial episode `[relaxed; overreach]`: A admitted, B rejected, final spec = `spec_relaxed`, meta floor provably intact; pointwise sanity computed. | **PROVED (EVAL/ARITH)** | `specNegEvalScript.sml : episode_final_spec, episode_meta_floor_intact, episode_pointwise_check` |

## The Löb question — argued, NOT assumed (a deliverable)

Changing the spec the proofs reason about is exactly where self-reference
could sneak in. We **flag and guard** it; the precise argument lives
verbatim in `specNegScript.sml` §5. Summary:

- **Where Löb bites:** when the predicate a soundness proof reasons about is
  *also* the thing the inhabitant re-chooses, with the system using its own
  judgement to vouch for its own next judgement — the shape of
  `kernelUpgradeTheory.loeb_reflection`
  (`(∀thy. K thy (sound_stmt thy)) ⇒ kernel_sound mem K'`): judge and judged
  are the same kind of object on the same level (genuine self-reference,
  Gödel/Löb, needs the LCA escape — hence the labelled hypothesis *there*).

- **Why it does not bite here** (structurally identical to
  `selfProverScript` §5 (a)(b)(c)):
  - **(a) different roles/level.** `meta` is a fixed state predicate
    supplied once (∀-bound, never proposed); `newspec` is the mutable
    artifact one level up. Fixed-lower-property vouches-for higher-mutable
    artifact = ordinary refinement, the state-predicate twin of the already
    sound `weaker` discipline. Not self-reference.
  - **(b) the root never moves.** There is no `meta'`; nothing the
    inhabitant can reach redefines/re-proposes `meta`.
    `spec_admit`/`spec_admit_all` range only over `newspec`/`proposals`;
    `meta` is a constant parameter. `meta_floor_is_never_negotiated` proves
    no proposal sequence escapes it. The certifier (`meta`) is never the
    thing certified — no fixed point of "the spec proving its own spec".
  - **(c) no diagonalisation.** The obligation `spec_refines newspec meta`
    is a first-order implication between two state predicates, discharged by
    an ordinary finite HOL4 proof about states (see `specNegEvalScript`,
    `intLib`/`rw`-level). Not "the spec proves its own global soundness".
    `safety_preservation` is reused about the FIXED `meta`; the mutable
    `newspec` only ever appears UNDER `spec_refines _ meta`.

- **Conclusion (honest split):** `spec_negotiation_is_safe` /
  `spec_negotiation_unbounded_is_safe` carry **no Löb/reflection hypothesis
  at all** — strictly fewer assumptions than `selfProverScript` (no
  `frozen_checker_sound`: `meta` is a plain HOL4 predicate, not a checker
  that must be trusted; the refinement obligation is discharged by an
  ordinary in-logic proof). The genuinely self-referential
  kernel-replacing-itself seam remains the **separate, already-labelled**
  `kernelUpgradeTheory.loeb_reflection` turtle — untouched and unaffected by
  this layer. **Nothing is assumed here that is not proved.**

## Build & reproduce

```
cd specneg && ~/dev/HOL/bin/Holmake     # INCLUDES = .. only; ~3s, low RAM
```
Builds `specNegTheory` then `specNegEvalTheory` clean (`OK`). Dependencies:
only the pure-HOL4 generic core in `..` (`systemTheory`, `envelopeTheory`,
`safetyTheory`, `sv_weakeningTheory`, `upgradeTheory`) — no CakeML, no
hol-reflection. No core script is edited.
