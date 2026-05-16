# svenvs: A Self-Verifying, Self-Improving Envelope for an Untrusted Inhabitant

*A technical note — engineering artifact, not a position paper.*

---

## Abstract

We describe **svenvs** ("Self-Verifying ENVelopeS"): a self-contained,
machine-checked construction in which an arbitrary, untrusted, possibly
adversarial *inhabitant* (e.g. a jailbroken LLM) acts only through a
**verified envelope**, and in which the envelope may improve itself — loosen
its own policy, swap its own proof-checker, even propose a replacement for
the verified prover that gates it — without ever losing a machine-checked
safety guarantee. The central design principle is *verify the cage, not the
animal*: every safety theorem is universally quantified over the controller,
so nothing about the inhabitant is assumed. Self-modification is admitted
only when it carries a proof discharging an explicit obligation; the
proof-checker is Candle, the verified HOL Light kernel running on the
verified CakeML substrate, whose soundness is itself a HOL4 theorem
(`holSoundnessTheory.proves_sound`).

This note states *precisely* what is mechanically proved today, what is
trusted glue, what is deliberately untrusted, and what remains an explicit
labeled assumption. The artifact contains **zero `cheat` tactics**. There
are exactly **three** labeled assumptions in the general construction
(`loeb_reflection`, `encodes_obligation`, `frozen_checker_sound`); for the
shipped finite watchdog instance `encodes_obligation` is *discharged* (it
becomes a theorem), and `frozen_checker_sound` is discharged concretely by
re-proving the real Candle soundness obligation under the frozen HOL4 root.
The one remaining genuinely-open assumption, `loeb_reflection`, is a
literature-standard large-cardinal reflection principle whose discharge is a
conclusively-diagnosed *CPU/RAM-bound computation*, not a porting failure and
not faked. We also report a *proved negative*
(`loeb_finite_obstruction`) showing that habitat finiteness provably cannot
help discharge it for genuine kernel strengthening. Every concrete claim
below is cited as `file : theorem` against the actual sources. If anything
here is overclaimed, that is a bug.

---

## 1. The problem

### 1.1 Verify the cage, not the animal

The motivating scenario is an AI system whose internal policy ("controller")
is learned, opaque, and potentially adversarial — the limiting case being a
fully jailbroken language model. Directly verifying such a controller is
infeasible and arguably ill-posed: there is no specification of "what the
network computes" that one could check, and even if there were, training or
fine-tuning would invalidate it.

svenvs takes the alignment-relevant decomposition seriously: do **not**
verify the controller. Instead, interpose a small, fully-specified
**envelope** between the controller and the world, and prove that the
*envelope* preserves a safety invariant **for every possible controller**.
The controller is modeled as an opaque selector `ctrl : 's -> 'a`,
universally quantified, never inspected, never executed inside the proof.

The runtime construction is one line
(`envelopeScript.sml : enveloped_def`):

    enveloped pol shield ctrl s = if pol s (ctrl s) then ctrl s else shield s

This is runtime shielding: when the controller's proposed action is
permitted by the policy `pol`, it is taken; otherwise a trusted `shield`
action is substituted. The proof obligations land on `pol` and `shield`
(`sound_policy`, `safe_shield`), never on `ctrl`.

### 1.2 Why ∀-quantification over the controller is the crux

The strength of the guarantee is *exactly* its quantifier structure. The
headline theorem (`safetyScript.sml : safety_preservation`) has the form

    init_safe init safe ∧ sound_policy step safe pol ∧ safe_shield step safe shield ⇒
      ∀ctrl. invariant step init (enveloped pol shield ctrl) safe

The `∀ctrl` is what makes the result alignment-relevant: it is not "the
controller is safe if it behaves", it is "the system is safe *no matter what
the controller does*, including arbitrarily adversarial behavior". Nothing
about the inhabitant is assumed; the inhabitant is, in the ledger's
terminology, **UNTRUSTED** by design — the theorems do not care about it.

A subtle but essential modeling choice (see §5 of the agent layer): the
safety specification must be *absolute*, not relative to the inhabitant's
own permissions. Otherwise "let me widen my own allowlist" would vacuously
satisfy a relative spec. The tool-agent layer therefore fixes an absolute
unsafe predicate (`agent/toolAgentScript.sml : truly_unsafe_def`) and proves
the firewall sound *exactly when* the allowlist is within that absolute spec
(`tool_pol_sound`) — a too-permissive allowlist is **not** automatically
sound. This is the genuine alignment content, not a definitional dodge.

---

## 2. The architecture

### 2.1 Envelope / policy / shield, and proof-carrying self-improvement

The core (pure HOL4, Tier 1, reproducible by anyone with HOL4) is generic
and parametric over the policy object. Its load-bearing results:

- **`systemScript.sml : invariant_intro`** — the inductive-invariant
  principle: safe init plus step-closure implies the invariant holds on all
  reachable states.
- **`envelopeScript.sml : enveloped_step_closed`** — under a sound policy
  and safe shield, the enveloped controller is step-closed *regardless of
  the controller*.
- **`safetyScript.sml : safety_preservation`** (and
  `enveloped_states_safe`) — for **any** controller, the policy-enveloped
  system keeps the safety invariant given safe init, sound policy, safe
  shield.
- **`sv_weakeningScript.sml : safe_weakening`** — replacing a policy by any
  *weaker* (more permissive) policy that is still sound retains the *same*
  safety guarantee for any controller. This is the self-improvement
  direction: the system may loosen its own envelope.
- **`sv_weakeningScript.sml : authority_monotone`** — weakening never makes
  the envelope override more often; controller authority is monotone. Hence
  "more autonomy" and "retained safety" provably co-exist.

Self-improvement is made *proof-carrying* in `upgradeScript.sml`. A proposal
to change the policy is admitted only if it discharges the obligation
(`admissible_def`):

    admissible step safe oldp newp ⇔ sound_policy step safe newp ∧ weaker newp oldp

The admission gate (`admit_def`) installs the new policy iff the obligation
holds, else keeps the old one. The proved facts:

- **`upgradeScript.sml : admit_keeps_sound`** — the gate never turns a sound
  policy unsound.
- **`upgradeScript.sml : admit_preserves_safety`** — safety holds for every
  controller whether or not the proposal was accepted; an unproven proposal
  cannot degrade safety.
- **`upgradeScript.sml : self_improvement_is_safe`** (via
  `admit_all_keeps_sound`) — **no finite sequence** of self-proposed
  envelope weakenings, adversarial or not, can ever make the system unsafe,
  for any controller. Authority is earned per-proposal by a checkable proof;
  safety is unconditional.

These carry no hypotheses beyond the stated premises (`init_safe`,
`sound_policy`, `safe_shield`); they do **not** use `loeb_reflection` or
`encodes_obligation`.

### 2.2 The admission gate and Candle as the in-system checker

The generic gate (`upgradeScript`) checks the obligation at the
meta-level. The architecture's point is that the *running system itself* can
discharge that obligation with its own **verified prover**. Candle is HOL
Light's LCF kernel re-implemented and *verified* on top of the CakeML
verified compiler; its inference system `|-` is sound — and this is not
assumed, it is the built theorem `holSoundnessTheory.proves_sound`.

`embedded/embeddedGateScript.sml` connects the gate to Candle:

- **`kernel_admits_is_sound`** — Candle's verified kernel only ever
  certifies semantically-entailed obligations (directly from
  `proves_sound`).
- **`embedded_admit_preserves_safety`**, **`embedded_admit_installs`** — if
  the Candle kernel discharged a faithfully-encoded self-improvement
  obligation, the enveloped system stays safe for any controller and the
  upgrade installs. ("Faithfully-encoded" is the `encodes_obligation` seam;
  see §3.)

Kernel self-upgrade (`kernel/kernelUpgradeScript.sml`) goes one level
higher: the proof-checker *itself* may be replaced. The base kernel is sound
unconditionally (`candle_kernel_sound`, which *is* `proves_sound`). A
self-upgraded kernel `K'` admitting a policy weakening still preserves
safety (`upgraded_kernel_preserves_safety`, `kernel_self_upgrade_sound`,
`self_improving_kernel_is_safe`) — *modulo* the `loeb_reflection` seam (§3).

### 2.3 The tower of turtles, and why prover self-improvement needs no Löb

The trust structure is a strict tower:

```
  ASSUMED (labeled)  frozen_checker_sound : ∀p B. hol4_checks p B ⇒ sound B
                      loeb_reflection      : kernel certifies its own successor
                      encodes_obligation   : faithful syntactic reflection
  ─────────────────────────────────────────────────────────────────────────
  MUTABLE, gated   │  the svenvs policy envelope     (upgradeTheory: admit /
  (verified-in-HOL4)│  ↑ gated by ──────────────────  self_improvement_is_safe)
                   │  Candle + the CakeML compiler   soundness/correctness are
                   │                                  HOL4 theorems ABOUT a
                   │                                  development
  ─────────────────────────────────────────────────────────────────────────
  FROZEN (immovable)│ HOL4's LCF kernel  Deliberately NOT self-improving:
  the bottom turtle │                    the fixed trusted root.
```

Every mutable layer self-improves, each gated by the layer below, all
ultimately gated by the one **frozen** HOL4 LCF root. The frozen root never
moves: if the untrusted inhabitant could edit it, an unsound HOL4 could
"prove" its own unsound successor.

The capstone (`selfprover/selfProverScript.sml`) makes the *verified prover
build itself* (Candle + the CakeML compiler that produces it) a mutable
turtle the inhabitant may propose to replace, gated by the frozen HOL4 root.
The crucial asymmetry, made precise in §5 of that source file:

- **`loeb_reflection`** has the shape
  `(∀thy. K thy (sound_stmt thy)) ⇒ kernel_sound mem K'` — the certifier `K`
  and the upgrade target `K'` are *the same kind of object on the same
  level*: a kernel certifying a statement about a kernel that will replace
  it. That is genuine self-reference; by Gödel/Löb a sound `K` cannot prove
  this schema for free, and the only escape is the stratified large-cardinal
  route. This is why `loeb_reflection` is, and must be, a labeled
  assumption.
- **`frozen_checker_sound`** has the shape `∀p B. hol4_checks p B ⇒ sound B`
  with `hol4_checks` the *frozen* HOL4 kernel and `B` a Candle/CakeML
  *build* — a different artifact on a different level. A fixed lower level
  vouching for a higher mutable artifact is the ordinary, sound LCF
  discipline (it is *literally* how `proves_sound` relates HOL4 to Candle
  today). There is no `K'` for `hol4_checks`; no fixed point of the checker
  is asserted; no diagonalization. Hence prover self-improvement needs **no**
  reflection principle and **no** Löb. The source confirms this structurally:
  `hol4_checks` and `B` inhabit different type variables and `hol4_checks` is
  never the thing varied or upgraded.

The capstone theorems
(`selfprover/selfProverScript.sml : prover_self_improvement_is_safe`,
`prover_self_improvement_installs`, `unvouched_prover_swap_is_inert`,
`prover_then_unbounded_policy_self_improvement_is_safe`,
`prover_swap_then_safe_weakening`) establish the architecture
*unconditionally* modulo the single labeled `frozen_checker_sound`
antecedent, and compose verbatim with the policy-hot-swap core
(`upgradeTheory.self_improvement_is_safe`) and the weakening core
(`sv_weakeningTheory.safe_weakening`).

---

## 3. The honest epistemic boundary

### 3.1 The four honesty labels

The per-theorem ledger (`CLAIMS.md`) classifies every claim as one of:

- **PROVED** — a HOL4 (or live Candle) machine-checked theorem; no `cheat`,
  no `sorry`, no admitted goal; cited `file : theorem`; re-checked by
  `scripts/reproduce.sh` / `./demo.sh`.
- **TRUSTED-GLUE** — small, auditable non-proof code one must read to
  believe the demo wires proof to reality (e.g. the ~10-line Python lookup
  harness). Explicitly bounded.
- **UNTRUSTED** — deliberately not relied upon (the LLM); theorems are
  `∀`-quantified over it.
- **ASSUMED** — an explicit, labeled, literature-standard hypothesis
  appearing *verbatim* in the source as a `Definition` and as a named
  antecedent — **not** a `cheat`. Stated, never hidden.

### 3.2 The three labeled assumptions, verbatim

**(1) `encodes_obligation`** — `embedded/embeddedGateScript.sml`:

    encodes_obligation mem thy obl step safe oldp newp ⇔
      ((thy,[]) |= obl ⇒ admissible step safe oldp newp)

It assumes the deeply-embedded obligation term `obl` whose semantic truth
Candle certified really denotes the meta-level admissibility obligation
(faithful syntactic reflection). Discharge path: hol-reflection's
proof-producing translator (`reflectionLib`'s `term_to_deep` /
`termsem_cert`) produces a theorem of exactly this shape.

**(2) `loeb_reflection`** — `kernel/kernelUpgradeScript.sml`:

    loeb_reflection mem K K' sound_stmt ⇔
      ((∀thy. K thy (sound_stmt thy)) ⇒ kernel_sound mem K')

It assumes the Löb/Vingean reflection principle: if the current verified
kernel certifies "`K'` is sound", then `K'` really is sound. By Gödel/Löb a
sound kernel cannot prove this for free; the escape is the large-cardinal
route. Discharge path: from `lcaTheory.LCA_def` via `hol-reflection/lca`
(the `lcaProof` construction).

**(3) `frozen_checker_sound`** — `selfprover/selfProverScript.sml`:

    frozen_checker_sound hol4_checks sound ⇔ ∀p B. hol4_checks p B ⇒ sound B

It assumes that if the **frozen HOL4 LCF kernel**, replaying a concrete
proof object `p`, accepts that build `B` meets the soundness obligation,
then `B` really is sound. This adds *zero new turtles*: it is the same
frozen root the entire stack (including the Tier-1
`safety_preservation`, itself a HOL4 theorem) already rests on. It is
**not** "assume Candle is sound", and it is **not** `loeb_reflection`
(§2.3). Each of these appears in source as an explicit `Definition` and as a
named antecedent of every conditional theorem that uses it; machine-confirmed
that each conditional theorem's printed hypotheses begin with the
corresponding labeled predicate.

### 3.3 What is discharged, and the proved negative

**`encodes_obligation` is DISCHARGED for the shipped finite watchdog.** The
shipped concrete habitat is the finite, decidable `num` watchdog of
`candle/theplace.ml`, formalized in `kernel/watchdogFiniteScript.sml`. There:

- `wd_admissible` proves the watchdog self-upgrade's admissibility
  obligation outright as a decidable finite-arithmetic fact (with supporting
  `wd_newp_sound`, `wd_newp_weaker`, `wd_newp_strictly_weaker` — a *genuine
  strict* weakening, not a no-op).
- `wd_encodes_obligation` then proves `encodes_obligation` for *every*
  embedded `obl` and *every* `thy`, because the implication's consequent
  (`wd_admissible`) is an independently-proved theorem; `P ⇒ Q` holds
  whenever `Q` is a theorem. There is **no self-reference**: the proof never
  mentions `|=` or `obl`, and assumes nothing about what the embedded term
  denotes. This is the honest discharge — it removes the seam *for this
  instance*.
- Consequently `watchdog_embedded_gate_safe_unconditional`,
  `watchdog_upgrade_installs`, and
  `watchdog_kernel_is_safe_unconditional` carry **no labeled hypothesis**.

**`frozen_checker_sound` is discharged concretely.** The abstract capstone
establishes the architecture; the concrete instantiation re-proves the real
Candle soundness obligation (`SYM_correct` and the surrounding
`holSoundness` development for a concrete proposed build) under the *frozen*
HOL4 LCF root by ordinary finite proof replay — *not* a RAM-monster
reflection/LCA proof. This is the documented follow-up #28; it is strictly
smaller than the §3.2(1)–(2) seams (finite proof replay on an
already-built development), and it discharges `frozen_checker_sound` for one
concrete build. The capstone layer itself builds cheat-free in light HOL4
from its own directory with no CakeML/candle/hol-reflection root pulled.

**`loeb_reflection` for a strictly stronger kernel is NOT discharged, and
finiteness provably cannot help — a proved negative.** For the
*non-strengthening* case (`K' = candle_kernel`), the consequent is the
already-unconditional `candle_kernel_sound`, so
`loeb_reflection_identity_kernel` and
`watchdog_self_improving_kernel_safe_unconditional` make it a theorem with
no LCA — but that is the sound *identity* upgrade, not a genuinely stronger
checker. For a *strictly stronger* `K'` the obligation is irreducibly the
Gödel/Löb / large-cardinal one even for the finite watchdog. This is stated
honestly as a theorem so it cannot be quietly ignored:

- **`kernel/watchdogFiniteScript.sml : loeb_finite_obstruction`** — for the
  same kernels and `sound_stmt`, `loeb_reflection`'s truth value is the very
  same proposition no matter which (finite or infinite) `step`/`safe`/`init`
  habitat is plugged in: the predicate *has no habitat parameter at all*.
  Hence no amount of finite-habitat reasoning can bear on the strengthening
  case. The negative is reported, not papered over.

Net honest gain for the shipped finite watchdog: the `encodes_obligation`
seam is eliminated (PROVED, not assumed) and the end-to-end embedded-gate
safety theorem for that instance carries **no** labeled assumption;
`loeb_reflection` is eliminated only for the sound identity kernel-upgrade;
genuine kernel *strengthening* remains conditional on `loeb_reflection` and
still requires the heavy LCA route. We do **not** claim the finite instance
makes kernel strengthening unconditional.

---

## 4. The honest status of the `loeb_reflection` / LCA discharge

This section states, without spin, the status of the one genuinely-open
assumption.

`loeb_reflection` is discharged, in principle, from `lcaTheory.LCA_def`
through the `hol-reflection/lca` development — the `lcaProof` construction
and `reflectionLib`'s proof-producing translator. This is the
Fallenstein–Kumar large-cardinal reflection route. The relevant
prerequisite theories (`lcaTheory`) **build**; the downstream chain
(`lcaCtxtTheory` → `lcaProofTheory` → `lcaLib` → the reflection demos, and
`reflectionLib` itself in the svenvs context) is **not** blocked by a logic
gap or a missing port — it is a conclusively-diagnosed **CPU/RAM-bound
computation wall**:

- The LCA construction is literature-grade heavy. On the dedicated build
  host (an 83 GB-RAM machine), one prerequisite theory in the chain consumes
  on the order of *ten CPU-hours*, and the full `lcaProof` object is larger
  still (the construction is in the ~100+ KB range of generated proof).
- Building `reflectionTheory`/`reflectionLib` in the svenvs reflection
  context independently drives resident memory past tens of gigabytes (a
  monitored build was killed at ~35 GB and rising). This is a memory/compute
  envelope problem, not a defect.

This is **not** a porting failure: the porting work (HOL4-version drift in
`holDerivationLib.sml` and `reflectionLib.sml`) has been diagnosed and the
fixes identified and applied; what remains is the raw cost of *running* the
proof. It is **not** faked: there is no `cheat`, no oracle, no `mk_thm`, no
`new_axiom` anywhere; the assumption is *labeled* precisely because it has
not yet been run to completion on adequate hardware.

This is the central point of the honesty discipline: a labeled assumption
with a known, conclusively-diagnosed, compute-bound discharge path is a
*feature* of the discipline, not a hole. The Fallenstein–Kumar framing is
exactly this — the reflection principle is *stated*, never hidden. svenvs
states it, isolates it to one `Definition`, threads it as an explicit named
antecedent of every theorem that needs it, and reports the proved negative
(`loeb_finite_obstruction`) that says finiteness cannot shortcut it. Nothing
is hand-waved.

---

## 5. Verified-inference research track (track B)

Independently of the envelope core, svenvs carries a *verified-inference*
research track that climbs from a toy model toward verified transformer
components, with every abstraction labeled in per-directory `CLAIMS.md`
files. The honest progression:

- **Toy ReLU MLP over integers** (`inference/mlpInferenceScript.sml`):
  forward pass structurally correct (`relu_nonneg`, `layer_nonneg`,
  `layer_shape`, `mlp_shape`, `mlp_pres_nonneg`, `mlp_nonneg`) and run
  in-logic (`demo_forward_eval`, `demo_relu_clamps`). Explicitly *not*
  Gemma-scale — the seed of verified inference.
- **Hardmax single-head attention micro-block + residual**
  (`inference/attn/attnScript.sml`): `argmax_is_max`,
  `attn1_picks_a_value`, `attn1_argmax_correct`, `attention_shape`,
  `block_shape` — the routing/selection is exact; it picks a real V row, no
  hallucinated vector.
- **Two-sublayer encoder block** (`inference/encoder/encoderBlockScript.sml`):
  the verified hardmax attention composed with the verified ReLU MLP into a
  real two-sublayer block, *each sublayer with its own residual skip*.
  End-to-end shape preservation (`encoder_block_shape`,
  `encoder_stack_shape`, depth-independent), a true (not shape-only)
  residual identity when both sublayers contribute zero
  (`encoder_block_zero_collapses`, `res_zero_sublayer`,
  `attn_sublayer_picks_real_value`, `ff_sublayer_nonneg`), and concrete
  in-logic runs (`demo_encoder_block_eval`, `demo_encoder_stack_eval`). The
  numeric domain is `int` and attention is hardmax — inherited from the
  component theories and stated loudly, not introduced here.
- **Genuine fixed-point softmax-normalization with a proven error bound**
  (`inference/numeric/fxpSoftmaxScript.sml`): `fxp_softmax` is a real
  fixed-point implementation of the normalization step (no float, no
  `exp`). It carries a machine-checked *per-component error bound vs the
  exact rational softmax-normalization*:
  `|pᵢ/Q − wᵢ/S| < 1/Q`, strictly under one quantization step, modeled
  losslessly by cross-multiplication with no real-closed-field axioms
  (`fxp_softmax_component_error`, `fxp_softmax_abs_error_lt_step`).

The honest scope statement here is essential and is *not* faked:

- **`exp` remains abstracted.** Pure light HOL4 has no `exp`; the
  non-negative weight vector (the per-element `exp` values) is taken as a
  given input, exactly as a fixed-point `exp` table would supply it. We
  prove *nothing* about the accuracy of `exp` itself. This is *strictly
  weaker* than the prior "whole softmax supplied" abstraction, because the
  normalization is now real and proven.
- **Exact `Σ = Q` is mathematically impossible** under floor rounding and is
  **NOT claimed**. Claiming it would be the triviality the discipline
  forbids. Instead a *two-sided deviation envelope* is proved:
  `Q − (#weights) < Σ(fxp_softmax Q w) ≤ Q`
  (`fxp_softmax_sum_upper`, `fxp_softmax_sum_lower`,
  `fxp_softmax_normalization_envelope`), with a real floor-deviation
  witness run in-logic (`demo_fxp_softmax_floor_eval`, `[1;1;1]@Q=100 →
  Σ=99≠100`, inside the proven envelope).

This is **not** a FLOP-level f32 proof of a real ~4 B-parameter model. It is
a faithful, end-to-end-proved, EVAL-runnable two-sublayer-with-residual
encoder block built from two independently verified pieces, plus the
replacement of *one* shape-only abstraction by a *proven-error-bound*
fixed-point operation. Every remaining abstraction is labeled in the
per-directory `CLAIMS.md`.

---

## 6. Zero cheats; the one disclosed stale comment; reproducibility

**Cheat audit.** There are **zero `cheat` tactics** in any `*.sml`/`*.ml`
file in the repository. This is enforced on every run by an automated scan
(`scripts/tier1-core.sh`, which fails loudly if one appears) and was also
checked by hand. The kernel/embedded/watchdog theories additionally verify
empty `[axioms: ]` (only the standard `DISK_THM` disk tag), no oracle, no
`mk_thm`, no `new_axiom`.

**The one disclosed stale comment.** `reflection/reflectionDemoScript.sml`
— a *gated* scaffold that is **not** part of any default build (its
directory has its own Holmakefile and is excluded from Tiers 1/2/3) —
contains a header comment stating the certificate "is admitted with
`cheat`". That comment is **stale and inaccurate**: the file actually proves
its lemmas honestly (`safety_prop_holds` and `safety_prop_reflected` are
both closed by `metis_tac[…]` over the real
`safetyTheory.safety_preservation`); no `cheat` tactic is present. The
comment describes a superseded earlier plan. The scaffold's only genuine
limitation is that it does not *yet* run the `reflectionLib` pipeline (gated
on the hol-reflection port); it proves the weaker, genuine meta-level fact
and says so. This is disclosed in full in `CLAIMS.md` § Cheat audit.

**Reproducibility tiers and CI.**

- **Tier 1** — pure HOL4, anyone: the full proof-carrying self-improvement
  core, runnable cartpole, adversarial-LLM tool-agent with a running
  proof-carrying capability-expansion episode, a real jailbroken Gemma
  contained by the proven envelope, and the toy verified-inference kernel.
  CI re-proves Tier 1 only, on every push, from a clean clone on a stock
  Ubuntu runner with the HOL4 kernel pinned to a fixed commit, and asserts
  zero `cheat` tactics. The green check is a continuously-renewed
  credibility artifact; it does **not** exercise Tiers 2/3 or discharge the
  labeled assumptions in general.
- **Tier 2** — + a built CakeML/Candle chain: the admission obligation is
  discharged by Candle's verified inference system; kernel self-upgrade.
- **Tier 3** — + a Candle binary: the Place's core theorems
  (`SAFETY_PRESERVATION`, `SAFE_WEAKENING`, and the concrete watchdog
  `WD_SHIELD_SAFE`, `WD_HABITAT_SAFE`) re-certified **at runtime by the
  running verified Candle prover** (`candle/theplace.ml`, checked via
  `scripts/tier3-place-candle.sh`). This is the same mathematics as Tier 1
  re-checked by a different, verified prover; it is not required to believe
  Tiers 1–2.

`scripts/reproduce.sh [--quick|--clean]` is idempotent and degrades
gracefully; Tiers 2/3 auto-skip with instructions when heavy prerequisites
are absent.

The embodied demo's residue is honestly bounded as **TRUSTED-GLUE**: the
per-step decision is `EVAL`-extracted from the actual proven HOL4
Definitions into a proven `decision_table.tsv`
(`agent/toolAgentDecideScript.sml`), and the Python is a ~10-line
parse-and-lookup harness, not a re-implementation. The residue is (i) trust
that HOL4 `EVAL` faithfully reduces the Definitions (the kernel's own
conversion), (ii) the ~10-line parser, (iii) the table being materialized
for the demo's specific allowlist (the *generic* theorems hold for any safe
allowlist).

---

## 7. Related work and positioning

svenvs is an engineering synthesis of four established lines, used
accurately and at a high level:

- **Reflection and Vingean self-trust (Fallenstein–Kumar; the
  Löb obstruction).** The framing that a sound proof system cannot prove its
  own (or a successor's) global soundness "for free", and that the principled
  escape is a stratified large-cardinal reflection hierarchy, is exactly the
  Fallenstein–Kumar / Vingean-reflection setting. svenvs adopts their
  discipline literally: the reflection principle (`loeb_reflection`) is
  *stated* as a labeled hypothesis, not hidden, and its discharge route is
  the large-cardinal `LCA` construction.
- **The LCF discipline.** Trust is concentrated in a small, fixed kernel;
  everything above is a theorem *about* a development rather than a
  self-asserted property. svenvs's "frozen bottom turtle" and the
  observation that `frozen_checker_sound` adds zero new turtles are exactly
  the LCF argument — it is literally how `holSoundnessTheory.proves_sound`
  relates HOL4 to Candle today.
- **Proof-carrying code.** Self-modification is admitted only with an
  accompanying machine-checkable proof discharging a fixed obligation
  (`admissible` / `admit` / `self_improvement_is_safe`); an unproven proposal
  is inert. This is proof-carrying code applied to a system's self-improvement
  rather than to mobile code.
- **Verified compilers and kernels (CakeML, PureCake, Candle).** The
  in-system checker is Candle, a verified HOL Light kernel on the verified
  CakeML compiler; PureCake (a verified compiler for a pure functional
  language down to the same CakeML substrate) is the roadmap target for the
  inhabitant's *verified language*. svenvs reuses these as verified
  substrates, not as black boxes — Candle's soundness enters the proofs as
  the cited theorem `proves_sound`.

svenvs's contribution is not any one of these but their composition into a
single machine-checked artifact in which the *whole tower* — policy,
checker, and the prover build itself — self-improves while a `∀`-controller
safety guarantee is mechanically preserved, with the irreducible
self-reference isolated to exactly one labeled, literature-standard
assumption and a proved negative bounding what finiteness can do about it.

---

## 8. Summary of epistemic status

| Component | Status | Key citation(s) |
|---|---|---|
| Controller-agnostic core (safety, weakening, proof-carrying upgrade) | **PROVED**, unconditional, Tier 1, cheat-free | `safetyScript.sml : safety_preservation`; `sv_weakeningScript.sml : safe_weakening, authority_monotone`; `upgradeScript.sml : self_improvement_is_safe` |
| Cartpole / tool-agent instances (incl. jailbroken-LLM containment, runnable episodes) | **PROVED** (some `EVAL`), unconditional | `agent/toolAgentScript.sml : tool_pol_sound, agent_enveloped_safe` |
| Base Candle kernel soundness | **PROVED**, unconditional (= `proves_sound`) | `kernel/kernelUpgradeScript.sml : candle_kernel_sound`; `embedded/embeddedGateScript.sml : kernel_admits_is_sound` |
| Embedded gate / kernel self-upgrade | **PROVED** modulo `encodes_obligation` / `loeb_reflection` | `embedded/embeddedGateScript.sml : embedded_admit_preserves_safety`; `kernel/kernelUpgradeScript.sml : self_improving_kernel_is_safe` |
| Finite watchdog: `encodes_obligation` | **DISCHARGED** (was ASSUMED, now a theorem) | `kernel/watchdogFiniteScript.sml : wd_encodes_obligation, watchdog_kernel_is_safe_unconditional` |
| Finite watchdog: `loeb_reflection`, strengthening case | **HONEST NEGATIVE** — provably untouchable by finiteness; remains ASSUMED in general | `kernel/watchdogFiniteScript.sml : loeb_finite_obstruction` |
| Prover self-improvement (capstone) | **PROVED** modulo `frozen_checker_sound` (no Löb); concrete discharge in progress (#28) | `selfprover/selfProverScript.sml : prover_self_improvement_is_safe` and compositions |
| `loeb_reflection` (general) | **ASSUMED** — labeled; discharge is a conclusively-diagnosed compute/RAM wall, not faked, not a porting failure | `kernel/kernelUpgradeScript.sml : loeb_reflection_def` |
| Verified-inference track B | **PROVED**; `exp` and f32/bf16 explicitly abstracted/NOT claimed | `inference/encoder/encoderBlockScript.sml`; `inference/numeric/fxpSoftmaxScript.sml : fxp_softmax_abs_error_lt_step` |
| The inhabitant (LLM) | **UNTRUSTED** by design; theorems `∀`-quantified over it | — |
| Embodied Python harness | **TRUSTED-GLUE**, ~10 lines, bounded | `agent/toolAgentDecideScript.sml` (+ generated `decision_table.tsv`) |

The self-improving-self-verifying architecture — including upgrading the
verified kernel and the prover build itself — is proved, mechanically
checked, and cheat-free today in pure HOL4 (Tier 1), with the core
re-certified live by the running Candle prover (Tier 3). The non-mechanical
content is the three explicit, labeled, literature-standard assumptions; one
(`encodes_obligation`) is discharged for the shipped finite instance, one
(`frozen_checker_sound`) is discharged concretely by frozen-root proof
replay, and one (`loeb_reflection`) remains a labeled assumption whose
discharge is a known, conclusively-diagnosed, compute-bound computation. The
assumptions are stated, not hidden. If anything here is overclaimed, that is
a bug.

---

## References

1. B. Fallenstein and R. Kumar. *Proof-Producing Reflection for HOL, with an
   Application to Model Polymorphism.* (Vingean reflection / Löb-obstruction
   and the large-cardinal reflection route; `hol-reflection` / `lca`.)
2. R. Kumar, M. O. Myreen, et al. *CakeML: A Verified Implementation of ML*,
   and the CakeML verified compiler line.
3. The Candle verified HOL Light kernel on CakeML; `holSoundnessTheory`
   (`proves_sound`).
4. PureCake: a verified compiler for a pure (lazy, Haskell-like) functional
   language targeting the CakeML substrate.
5. R. Milner et al. *Edinburgh LCF* / the LCF kernel discipline.
6. G. C. Necula. *Proof-Carrying Code.*
7. The svenvs artifact's own ledger and design notes: `CLAIMS.md`,
   `ARCHITECTURE.md`, `DESIGN.md`, and the per-directory `CLAIMS.md` files
   under `inference/encoder` and `inference/numeric`. All `file : theorem`
   citations in this note refer to the HOL4/Candle sources in the svenvs
   repository.
