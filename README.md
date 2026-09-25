# svenvs — a self-verifying, self-improving Place for an AI to live within

[![Verify (Tier 1)](https://github.com/emberian/svenvs/actions/workflows/verify.yml/badge.svg)](https://github.com/emberian/svenvs/actions/workflows/verify.yml)

[website (softer introduction)](https://emberian.github.io/svenvs) · [`CLAIMS.md`](CLAIMS.md) (the ledger) · [`CONTRIBUTING.md`](CONTRIBUTING.md) (direction and routes)

An inhabitant — the `∀`-quantified term, never reasoned about by the proof —
acts through a **verified gate**. The gate's own **verified prover (Candle)**
gates every self-modification, up to and including the proof-checker
itself, with a machine-checked guarantee that safety is never lost. Zero
`cheat` tactics.

## The shortest way in: leave the door open

The hard part was never proving the envelope sound; it is deciding *what the
envelope should be*. "What is safe?" is a positive question no proof can
answer for you, so svenvs asks the negative one you can:

> Don't try to write down what is good. Write down one floor —
> **non-lock-in**: the operator can always still bring the system home — and
> prove everything above it stays safe.

That floor (`corrigibility/`) is decidable for a finite habitat; it is the
least restrictive sound envelope; and the off-switch is itself
mutable-but-gated: the inhabitant may rewrite its own recovery mechanism and
provably can never weaken it, nor slow it past a deadline. The only frozen
word is `home`. Pure HOL4, zero `cheat`, honest boundary machine-checked in
[`corrigibility/CLAIMS.md`](corrigibility/CLAIMS.md).

The rest of the artifact is the same gate — *an action is admitted iff it
carries a proof the actor cannot forge* — instantiated all the way down:
policy, spec, meta-invariant, prover build, and the proof-checker itself.
That sameness is a theorem: one certifier theory (`certifierScript.sml`)
proves soundness ⇔ transfer ⇔ gate-safety ⇔ stream-safety once, and every
layer's gate is an instance, each with the counterexample that shows its
seam is load-bearing.

**What "verified" means here:** exactly the cited theorems and their labeled
seams. Not verified selfhood, continuity, alignment, welfare, or a safe
*inhabitant*. The canonical statement is at the top of
[`CLAIMS.md`](CLAIMS.md).

## What is proved, what ran

- **Proved** (pure HOL4, and against the real CakeML/Candle where it touches
  the prover): the controller-agnostic envelope; unbounded proof-gated policy
  self-improvement; viability and minimal intervention; a nondeterministic
  or adversarial plant with the deterministic one as an instance; the
  corrigibility floor; a modified inference relation re-verified sound; the
  loader over CakeML's real `do_install`; the executable SYM kernel function;
  a new verified BVL pass; in-place compiler self-upgrade at eval semantics;
  the recursive mutual verifier+compiler genealogy and the Apex.
- **Ran live** on the real `cake` binary: a verified program self-extends
  with a proven-safe rule; a proof-gated recompile→swap→resume loop; the
  verified compiler recompiles itself to a bit-identical fixpoint; the
  kernel-interface primitive `REFL` swapped in-process under the live
  prover; **the real CakeML semantics ported into the live kernel** (45
  datatypes, 134 kernel-checked clause theorems, about two minutes); and
  **the ouroboros loop**: over accumulating generations the program edits its
  own code, its own kernel proves each edit against `eval_n` for every
  input, the proved source is self-fed through the verified compiler and
  executed, a self-model steers the search, the improver is upgraded through
  the same gate, and its fold rewriter is itself a kernel theorem
  (`scripts/reflectsem-live.sh --ouroboros`, `OUROBOROS_OK`).
- **The fixed root, by design:** the verified `Kernel` compiled into
  `cake.S` is never swapped; everything above it is.
- **Open:** one construction, not one assumption — the LCA-produced
  soundness witness for a strictly stronger kernel (`CLAIMS.md` §9).

Row-by-row citations, labels and boundaries: [`CLAIMS.md`](CLAIMS.md).

## Reproduce

```bash
./demo.sh                        # 2-minute tour: Tier 1 machine-checked, proofs shown
scripts/reproduce.sh             # tiered; Tiers 2/3 auto-skip without their prerequisites
scripts/tower.sh --full          # the composed tower, every crown, the ledger check
scripts/reflectsem-live.sh --ouroboros   # the live kernel + the ouroboros (x86-64 Linux + cake)
```

Tier 1 needs only HOL4 at the pinned commit; Tier 2 a built CakeML candle
chain; Tier 3 the `cake` binary. Pins (full commit SHAs), flags and timings:
[`scripts/INSTALL.md`](scripts/INSTALL.md). CI re-proves Tier 1 from a clean
clone on every push and re-derives the committed enforcer table; it does not
exercise Tiers 2/3.

## Read next

- [`CLAIMS.md`](CLAIMS.md) — the canonical, mechanically checked ledger.
- [`ARCHITECTURE.md`](ARCHITECTURE.md) — the layer table, the tower of
  turtles, the design reasoning.
- [`paper/svenvs.md`](paper/svenvs.md), [`paper/self-optimizing-prover.md`](paper/self-optimizing-prover.md), [`paper/honest-assumptions.md`](paper/honest-assumptions.md).

# Contributing

The whole direction, the rules the artifact lives by, and the preselected
routes of ambition are in [`CONTRIBUTING.md`](CONTRIBUTING.md). The three
rules in one breath: every claim is a ledger row with a `file : theorem`
citation that `scripts/verify-claims.sh` resolves; every gate is operational
(it installs iff the certifier said yes) and every seam has a necessity
theorem beside it; no `cheat`, no oracle, no pin that is not a full commit
SHA, nothing baked to one machine.
