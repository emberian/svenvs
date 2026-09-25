# svenvs — architecture

**svenvs** ("Self-Verifying ENVelopeS") is a self-contained, self-verifying,
self-improving *Place* for an AI to live within: an inhabitant (the
`∀`-quantified term, never reasoned about by the proof) acts
through a verified envelope; the envelope's own verified prover (Candle)
gates every self-modification — including upgrades to the proof-checker
itself — with a machine-checked guarantee that safety is never lost.

This file is the map: the layers, the tower of turtles, and the design
reasoning behind the shape. What is proved, run, or assumed, row by row, is
the canonical ledger [`CLAIMS.md`](CLAIMS.md); this file does not restate it.

## The layers (bottom → top)

| Layer | Files | What it proves |
|-------|-------|----------------|
| **Core** | `system`,`envelope`,`safety`,`sv_weakening`,`upgrade` | `safety_preservation` (∀ inhabitant, the envelope keeps the invariant); `safe_weakening` (loosening the envelope keeps safety *and* takes no authority away; `safe_weakening_needs_weaker` shows the weakening premise is necessary); the operational `gate` (installs iff the certifier said yes; `unsound_certificate_breaches` shows an unsound yes breaches); `self_improvement_is_safe` (no unbounded sequence of self-proposed upgrades ever loses safety; unproven proposals rejected) |
| **Cartpole** | `cartpole*` | A concrete, *EVAL-runnable* integer plant instance of the whole core; adversarial controller provably contained |
| **LLM tool-agent** | `agent/toolAgent*` | The inhabitant = an opaque LLM emitting tool calls; firewall vs an *absolute fixed* safety spec; `agent_enveloped_safe` (∀ agent, jailbroken included); runnable adversarial episodes + decidable proof-carrying capability self-expansion (`episode_runs`) |
| **Embodied (real LLM)** | `agent/embodied/`, `agent/toolAgentDecide*` | A *real* jailbroken `gemma2:2b` (or `--mock` adversary) dropped into the proven envelope. The enforcer is **EVAL-extracted from the proven Definitions** (`toolAgentDecideScript.sml` → proven `decision_table.tsv`); the Python is now a ~10-line lookup harness, not a ~50-line re-implementation. "Verify the cage, not the animal." |
| **Verified inference (B)** | `inference/mlpInference` | Research track B: a TOY ReLU MLP over ints, forward pass proved correct + EVAL-run. Explicitly *not* Gemma-scale — the seed of verified inference |
| **Embedded** | `embedded/embeddedGate` | The admission obligation is discharged by **Candle's verified inference system** (`holSoundnessTheory.proves_sound`), not HOL4 metis |
| **Kernel self-upgrade** | `kernel/kernelUpgrade` | Replace the proof-checker itself; the upgraded kernel drives the gate (`kgate`), so a kernel is sound exactly when its gate is safe (`kernel_sound_iff_gate_safe`); `self_improving_kernel_is_safe` from real Candle soundness + one labeled Löb/LCA hypothesis, both proved necessary |
| **Prover self-improvement** | `selfprover/selfProver`, `selfproverConcrete/` | The verified *prover build itself* (Candle+CakeML) is a mutable turtle the inhabitant may replace, gated by the FROZEN HOL4 root: the prover gate installs only what a root-vouched build certified; `prover_self_improvement_is_safe` + composition with the policy/kernel core, with necessity theorems for the checker and the build. Pure light HOL4; the labeled `frozen_checker_sound` seam, NO Löb (fixed root vouches for mutable layer ≠ self-reference). The seam is discharged for the real Candle build in `selfproverConcrete/` |
| **Spec / meta / root** | `pca/`, `specneg/`, `amendment/`, `genealogy/`, `liberty/`, `integration/` | Proof-carrying actions; the spec negotiable under a fixed meta, the meta amendable over a bedrock, the root a forward-certified genealogy of judges, the least-restrictive envelope; all composed through `invariant_transports_to_meta` into the `svenvs_tower_*` theorems |
| **Corrigibility** | `corrigibility/` | The non-lock-in floor: decidable, self-improvable, latency-bounded, the tower's negotiable bedrock (own ledger `corrigibility/CLAIMS.md`) |
| **Testimony** | `embodiment/` | The inhabitant *may* volunteer a proof about its own substance to earn authority; permitted, never required |
| **Self-optimizing prover** | `kernelMod/`, `loader/`, `kernelImpl/`, `recursive/`, `selfRecompile/`, `apex/` | Modified inference relation re-verified sound; in-place kernel swap; the loader over the real `do_install`; the executable SYM refinement; recursive mutual verifier+compiler improvement; the Apex |
| **Compiler self-improvement** | `compilerOpt/`, `selfUpgrade/` | A new BVL pass proved against real `bvlSem` and baked into an altered root (Layer B); the per-generation in-place compiler self-upgrade at CakeML's eval semantics |
| **Closed loop** | `agent/closedloop/` | Every action of a real jailbroken model admitted or refused by the live Candle kernel; the num-encoding proved faithful |
| **The Place (live)** | `candle/theplace.ml` | Core habitat theorems re-derived and certified **at runtime by a running Candle prover** |
| **Reflection** | `reflection/` (gated) | `reflectionLib` path: HOL4 proofs → OpenTheory → embedded `\|-` → `proves_sound`. Not in any default build |

### The tower of turtles (what is frozen vs verified-in-HOL4-hence-mutable vs assumed)

```
  labeled seams ───── encodes_soundness    : faithful encoding of "K' is sound"   [WITNESS NOT YET CONSTRUCTED — CLAIMS §9]
                       loeb_reflection      : derived from soundness + that seam   [no longer assumed — CLAIMS §9]
                       frozen_checker_sound : hol4_checks p B ⇒ sound B          [DISCHARGED, real Candle — CLAIMS §5]
                       encodes_obligation   : faithful syntactic reflection     [DISCHARGED, finite watchdog — CLAIMS §4]
  ────────────────────────────────────────────────────────────────────────────
  MUTABLE, gated     │  the svenvs policy envelope        upgradeTheory: admit / self_improvement_is_safe
  (verified-in-HOL4) │  ↑ gated by ─────────────────────  the running prover build
                     │  Candle + the CakeML compiler      soundness/correctness are HOL4 *theorems about a
                     │                                     development* → inhabitant may propose B'; adopt iff
                     │                                     FROZEN HOL4 still proves sound(B')   ← selfprover
  ────────────────────────────────────────────────────────────────────────────
  ROOT (per tenure)  │  HOL4's LCF kernel    The current judge. Fixed *while it judges* (a proof is
  the current judge  │                        meaningful only vs. some fixed calculus); a successor is
                     │                        adopted only if THIS root certified it. The one move no
                     │                        sound root can make for free — certify a logically
                     │                        stronger successor — needs an LCA-built encoding
                     │                        certificate, by Gödel (CLAIMS §9).
```

Every mutable layer self-improves, each gated by the layer below, all
ultimately gated by the current root. The root is *not* eternally frozen:
it is the current term of a **forward-certified genealogy of judges** —
soundness propagates from a sound genesis along any certified succession
(`genealogy/genealogyScript.sml : genealogy_sound`), so "frozen forever"
is replaced by "sound once at genesis, certified forward". The asymmetry that makes prover
self-improvement sound: the frozen root vouches for a *different, mutable*
artifact (its soundness is a HOL4 theorem about that artifact) — that is
**not** a system vouching for itself, so it needs **no** reflection
principle. Löb bites **only** the kernel-replacing-*itself* move (the
soundness witness of CLAIMS §9), not this one.

## Design reasoning

### Why this shape

The thread claim: *syntactic consistency (Candle's self-verification) + a
proof-producing reflective translator (hol-reflection) is enough to build a
self-verifying / self-improving artifact* — and the concrete, falsifiable
demo is "a policy envelope around a controller with a policy-weakening
theorem and safety preservation."

We deliberately keep the controller **opaque**. It is a `:'s -> 'a`
selector, universally quantified, never inspected or executed. All assurance
comes from the *envelope*:

    enveloped pol shield ctrl s = if pol s (ctrl s) then ctrl s else shield s

This is runtime shielding. The proof obligations are on the *policy*
(`sound_policy`) and *shield* (`safe_shield`), not on the controller — which
is exactly the alignment-relevant decomposition: you don't need to verify the
(possibly learned, possibly adversarial) controller, only the envelope.

### The three theorems

- `safetyTheory.safety_preservation` — `∀ctrl. invariant … safe`. Pure
  inductive invariant; the controller is free.
- `sv_weakeningTheory.safe_weakening` — replacing a policy by any *weaker*
  (more permissive) policy that remains `sound_policy` keeps the **same**
  safety guarantee and takes no authority away. This is "the system may loosen
  its own envelope" — the self-improvement direction, made safe by the
  soundness side-condition; `safe_weakening_needs_weaker` shows the weakening
  premise is what the authority half rests on.
- `sv_weakeningTheory.authority_monotone` — weakening never increases
  overrides; the controller strictly gains authority. Together with
  `safe_weakening` this is the precise sense in which self-improvement (more
  autonomy) and self-verification (retained safety) co-exist.

### Reflection / Candle tie-in

`reflection/reflectionDemoScript.sml` (gated, not in any default build; a
cheat-free scaffold) is where `safety_prop` is to be reflected into Candle's
deeply-embedded HOL via `reflectionLib` (`term_to_deep`, `termsem_cert`,
`prop_to_loeb_hyp`). The endgame is a certificate that the safety
proposition is `True` under the set-theoretic semantics Candle's soundness
theorem connects to the running kernel — i.e. the envelope theorem is
checkable *by the verified prover about itself*. No large-cardinal axiom is
needed for this fragment (that is only required for the stronger
self-trust / reflection-of-provability results in hol-reflection/lca).

### What is the artifact vs. what is a spec skeleton

- `system`/`envelope`/`safety`/`sv_weakening`/`upgrade` — **real and
  final**. Generic, parametric over the *policy object*; the proof-carrying
  self-improvement theorems (`admit`, `self_improvement_is_safe`) do not
  depend on how a policy is represented.
- `cartpoleProgramScript`'s `gexpr`/`geval` — **a spec skeleton, not the
  artifact.** A bespoke mini-language in *meta* HOL4, a parallel embedding of
  syntax Candle already embeds deeply; it exists only to exercise the control
  structure and is not to be extended. The real version is built: the
  obligation is embedded provability checked by the Candle kernel, sound by
  the built `holSoundness` (`embedded/`), and kernel self-upgrade is
  `kernel/` — with genuine logical *strengthening* of the kernel resting on
  an LCA-constructed soundness witness (the `hol-reflection/lca` route,
  CLAIMS §9); `loeb_reflection` itself is derived, not assumed. The
  inhabitant's real language is PureLang (`pure/DESIGN.md`, `pureverified/`).

## Reproduce / verify

- `./demo.sh` — the 2-minute guided showcase (Tier 1, prints the proofs).
- `scripts/reproduce.sh [--quick|--clean]` — tiered, degrades gracefully,
  idempotent. See `scripts/INSTALL.md`.
- `CLAIMS.md` — the per-theorem skeptic ledger (PROVED / RAN / TRUSTED-GLUE /
  UNCONSTRAINED / ASSUMED, with `file : theorem` citations), including what
  is open.
