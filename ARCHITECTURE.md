# svenvs — architecture & epistemic status

**svenvs** ("Self-Verifying ENVelopeS") is a self-contained, self-verifying,
self-improving *Place* for an AI to live within: an untrusted inhabitant acts
through a verified envelope; the envelope's own verified prover (Candle)
gates every self-modification — including upgrades to the proof-checker
itself — with a machine-checked guarantee that safety is never lost.

## The layers (bottom → top)

| Layer | Files | What it proves |
|-------|-------|----------------|
| **Core** | `system`,`envelope`,`safety`,`sv_weakening`,`upgrade` | `safety_preservation` (∀ inhabitant, the envelope keeps the invariant); `safe_weakening` + `authority_monotone` (self-improvement that loosens the envelope keeps safety); `self_improvement_is_safe` (no unbounded sequence of self-proposed upgrades ever loses safety; unproven proposals rejected) |
| **Cartpole** | `cartpole*` | A concrete, *EVAL-runnable* integer plant instance of the whole core; adversarial controller provably contained |
| **LLM tool-agent** | `agent/toolAgent*` | The inhabitant = an opaque LLM emitting tool calls; firewall vs an *absolute fixed* safety spec; `agent_enveloped_safe` (∀ agent, jailbroken included); runnable adversarial episodes + decidable proof-carrying capability self-expansion (`episode_runs`) |
| **Embodied (real LLM)** | `agent/embodied/`, `agent/toolAgentDecide*` | A *real* jailbroken `gemma2:2b` (or `--mock` adversary) dropped into the proven envelope. The enforcer is **EVAL-extracted from the proven Definitions** (`toolAgentDecideScript.sml` → proven `decision_table.tsv`); the Python is now a ~10-line lookup harness, not a ~50-line re-implementation. "Verify the cage, not the animal." |
| **Verified inference (B)** | `inference/mlpInference` | Research track B: a TOY ReLU MLP over ints, forward pass proved correct + EVAL-run. Explicitly *not* Gemma-scale — the seed of verified inference |
| **Embedded** | `embedded/embeddedGate` | The admission obligation is discharged by **Candle's verified inference system** (`holSoundnessTheory.proves_sound`), not HOL4 metis |
| **Kernel self-upgrade** | `kernel/kernelUpgrade` | Replace the proof-checker itself; `self_improving_kernel_is_safe` from real Candle soundness + one labeled Löb/LCA hypothesis |
| **Prover self-improvement (capstone)** | `selfprover/selfProverProver` | The verified *prover build itself* (Candle+CakeML) is a mutable turtle the inhabitant may replace, gated by the FROZEN HOL4 root; `prover_self_improvement_is_safe` + composition with the policy/kernel core. Pure light HOL4; one new labeled `frozen_checker_sound` seam; NO Löb (fixed root vouches for mutable layer ≠ self-reference). Abstract here; concrete real-source replay = follow-up #28 |
| **The Place (live)** | `candle/theplace.ml` | Core habitat theorems re-derived and certified **at runtime by a running Candle prover** |
| **Reflection** | `reflection/` (gated) | `reflectionLib` path: HOL4 proofs → OpenTheory → embedded `\|-` → `proves_sound`. Not in any default build |

### The tower of turtles (what is frozen vs verified-in-HOL4-hence-mutable vs assumed)

```
  assumed (labeled) ─ frozen_checker_sound : hol4_checks p B ⇒ sound B
                       loeb_reflection      : (kernel certifies own successor)  [§4/§7 seam]
                       encodes_obligation   : faithful syntactic reflection     [§4 seam, §7 watchdog: DISCHARGED]
  ────────────────────────────────────────────────────────────────────────────
  MUTABLE, gated     │  the svenvs policy envelope        upgradeTheory: admit / self_improvement_is_safe
  (verified-in-HOL4) │  ↑ gated by ─────────────────────  the running prover build
                     │  Candle + the CakeML compiler      soundness/correctness are HOL4 *theorems about a
                     │                                     development* → inhabitant may propose B'; adopt iff
                     │                                     FROZEN HOL4 still proves sound(B')   ← selfprover
  ────────────────────────────────────────────────────────────────────────────
  FROZEN (immovable) │  HOL4's LCF kernel    Deliberately NOT self-improving. If the untrusted inhabitant
  the bottom turtle  │                        could edit it, an unsound HOL4 could 'prove' its own unsound
                     │                        successor. So it never moves. It is the fixed trusted root.
```

Every mutable layer self-improves, each gated by the layer below, all
ultimately gated by the one frozen root. The asymmetry that makes prover
self-improvement sound: the frozen root vouches for a *different, mutable*
artifact (its soundness is a HOL4 theorem about that artifact) — that is
**not** a system vouching for itself, so it needs **no** reflection
principle. Löb bites **only** the kernel-replacing-*itself* seam (the
separate, already-labeled `loeb_reflection`), not this one.

## Epistemic status (the honest boundary)

- **Unconditional, mechanically checked, cheat-free:** the entire Core,
  Cartpole, LLM-agent (Tier 1); base Candle-kernel soundness; the Place's
  core theorems certified by the live verified prover (Tier 3).
- **Conditional on two explicit, labeled assumptions** (literature-standard,
  each isolated to one definition, each with a known discharge path):
  - `loeb_reflection` — the Löb/Vingean reflection principle (the
    irreducible large-cardinal assumption; discharged from `lcaTheory.LCA_def`
    by `hol-reflection/lca` — the heavy `lcaProof`, persvati-bound);
  - `encodes_obligation` — faithful syntactic reflection (discharged by
    `reflectionLib`'s proof-producing translator — persvati-bound).
- **Discharged for the shipped finite watchdog instance** (no monster, light
  HOL4, cheat-free — `kernel/watchdogFiniteScript.sml`, see `CLAIMS.md` §7):
  - `encodes_obligation` is **eliminated** for the `num` watchdog: its
    consequent (`wd_admissible`) is a decidable finite-arithmetic theorem,
    so the seam holds for *any* embedded term — no assumption, no
    self-reference (`watchdog_kernel_is_safe_unconditional` carries no
    labelled hypothesis);
  - `loeb_reflection` is eliminated **only for the sound non-strengthening
    kernel** (`K' = candle_kernel`, consequent = the unconditional
    `candle_kernel_sound`). Genuine kernel *strengthening* remains
    LCA-bound — the Löb obstruction is at the proof-system level and is
    provably independent of habitat finiteness (`loeb_finite_obstruction`).
    This negative is reported honestly, not papered over.
- **Not a `cheat`:** zero `cheat` tactics anywhere in any `*.sml`/`*.ml`
  (enforced on every run by `scripts/tier1-core.sh`); the assumptions are
  *stated* and *labeled*, exactly as Fallenstein–Kumar frame it. What remains
  is *discharging* these two seams (the genuine RAM-monster proofs), which is
  what the dedicated build host is for. One header *comment* in the gated,
  not-in-default-build `reflection/reflectionDemoScript.sml` still says the
  scaffold "is admitted with `cheat`" — that comment is **stale**; the file
  actually proves its lemmas honestly from `safety_preservation` (no `cheat`
  tactic present). See `CLAIMS.md` § Cheat audit for the full disclosure.

## Roadmap axes (IN PROGRESS — concurrently developed, NOT yet claimed done)

These are active frontiers. Their dirs may exist with skeleton/partial
content while sibling agents build them; nothing here is asserted complete.
See `CLAIMS.md` § Roadmap for the precise un-overclaimed status of each.

- **Discharge the two labeled seams** (`encodes_obligation`,
  `loeb_reflection`) on the dedicated build host → unconditional
  end-to-end. (RAM-monster proofs: `reflectionLib`, `hol-reflection/lca`.)
- **PureCake** (`pure/`) as the inhabitant's *verified language*: PureLang
  programs (formal HOL4 semantics) verified-compiled to the same CakeML
  substrate Candle runs on — upgrades "typed-in program" from skeleton to a
  real verified language. End-to-end verified Place = Pure ⊕ Candle ⊕ CakeML.
- **Closed-loop runtime** (`agent/closedloop/`): each admission a real,
  live Candle proof via the persistent verification server
  (`scripts/place-server.sh`).
- **Verified tensor acceleration / attention** (`inference/accel/`,
  `inference/attn/`): climbing from the toy MLP toward a verified
  transformer block (still toy scale, integer domain).

## Reproduce / verify

- `./demo.sh` — the 2-minute guided showcase (Tier 1, prints the proofs).
- `scripts/reproduce.sh [--quick|--clean]` — tiered, degrades gracefully,
  idempotent. See `scripts/INSTALL.md`.
- `CLAIMS.md` — the per-theorem skeptic ledger (PROVED / TRUSTED-GLUE /
  UNTRUSTED / ASSUMED, with `file : theorem` citations).
