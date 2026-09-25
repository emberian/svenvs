# svenvs — a self-verifying, self-improving Place for an AI to live within

[![Verify (Tier 1)](https://github.com/emberian/svenvs/actions/workflows/verify.yml/badge.svg)](https://github.com/emberian/svenvs/actions/workflows/verify.yml)

[website (softer introduction)](https://emberian.github.io/svenvs)

An inhabitant — the `∀`-quantified term, never reasoned about by the proof —
acts through a **verified gate**. The gate's
own **verified prover (Candle)** gates every self-modification — up to and
including upgrading the proof-checker itself — with a machine-checked
guarantee that safety is never lost. Zero `cheat` tactics.

## The shortest way in: leave the door open

The hard part was never proving the envelope sound — it is deciding *what the
envelope should be*. "What is safe?" is a positive question no proof can
answer for you. So svenvs reframes it to a *negative* one you actually can:

> Don't try to write down what is good. Write down one floor —
> **non-lock-in**: the operator can always still bring the system home — and
> prove everything above it stays safe.

That floor (`corrigibility/`) is **decidable** for a finite habitat; it is
the **least** restrictive sound envelope (every bar is a one-way door and
nothing more); and — the part that makes it real for a *self-improving*
inhabitant — the off-switch is itself mutable-but-gated: the inhabitant may
rewrite its own recovery mechanism however it likes and **provably can never
weaken it, nor even slow it past a deadline.** The only thing left frozen is
the single word `home` (what "recovered" *means*), and even that is hedged by
spec-redundancy. 10 theories, ~60 theorems, pure HOL4, zero `cheat`; the honest boundary —
that this is a *reduction* to a faithful `home`, and the runnable plant is a
*non-vacuity witness, not an AI* — is stated, machine-checked, in
[`corrigibility/CLAIMS.md`](corrigibility/CLAIMS.md).

This is the legible front door to the larger artifact, which is the same gate
— *an action is admitted iff it carries a proof the actor cannot forge* —
instantiated all the way down: policy, spec, meta-invariant, prover build,
and the proof-checker itself. That sameness is itself a theorem: one
certifier theory (`certifierScript.sml`) proves soundness ⇔ transfer ⇔
gate-safety ⇔ stream-safety once, and every layer's gate is an instance.

**What "verified" means here — load-bearing, not preface:** exactly the
cited theorems and their labeled seams — **not** verified selfhood,
continuity, alignment, welfare, or a safe *inhabitant*. The canonical statement, and the one construction not yet done, are at the top of
[`CLAIMS.md`](CLAIMS.md).

CI re-proves **Tier 1 only** on every push: from a clean clone, on a stock
Ubuntu runner, the HOL4 kernel (pinned commit) re-checks the whole pure-HOL4
core and a scan asserts zero `cheat` tactics — so the green check is itself a
continuously-renewed credibility artifact. It does **not** exercise Tiers 2/3
(the real CakeML/Candle layers — kernel modification, the `do_install` loader,
the live prover) or perform the one construction still open (the LCA-produced soundness
witness for a strictly stronger kernel, `CLAIMS.md` §9; no kernel-upgrade
principle is assumed, and the other two named seams are discharged).

This is an *engineering artifact*, not a position paper: clone it and check
the proofs yourself.

## Improving the prover itself — the answer, with the boundary marked

*"How can it improve the theorem prover itself? As in, has it ever tried
doing that?"* svenvs answers that as a machine-checked chain, against the
**real** CakeML/Candle, with a live demo of the part that is safe to run —
and an honest line where execution stops and proof takes over. Full ledger:
[`paper/self-optimizing-prover.md`](paper/self-optimizing-prover.md).

- **Proved** (real CakeML/Candle, `DISK_THM`-clean, no new turtle): a
  modified inference relation is sound (`kernelMod/`); an in-place kernel
  swap is safe iff the new kernel is a sound *extension*, and the unbounded
  self-optimization loop stays sound; **the loader, over CakeML's actual
  `closSem$do_install`, preserves every running code entry**
  (`loader/installLoader`); **the executable Candle SYM kernel function
  soundly implements the modified rule** (`kernelImpl/`); HOL4 is provably
  *out of the runtime loop*; a new BVL compiler pass is proved
  semantics-preserving against the real `bvlSem` (`compilerOpt/`); an
  in-place compiler swap keeps eval semantics over arbitrarily many swaps
  (`selfUpgrade/`); and **recursive *mutual* verifier+compiler
  self-improvement is a genealogy over `(verifier, compiler)` stages**
  (`recursive/`, instantiated in `apex/`) — Löb-free for optimization,
  walled only for genuine logical *strengthening*.
- **Ran live** on the real `cake` binary (Tier 3): a verified program
  self-extends its own code with a proven-safe derived rule; the plants
  self-optimize their policies under the live kernel; a **proof-gated
  recompile→swap→resume loop** replaces running compute code, each swap gated
  by a live kernel proof; **the verified compiler recompiles itself** (a
  bit-identical fixpoint, and a self-optimized variant), end-to-end in
  `scripts/apex.sh` (**DIAMOND**); a per-generation compiler self-upgrade
  runs natively and under a live Candle correctness gate; and **the kernel
  interface primitive `REFL` is swapped in-process under the whole live
  prover** (`scripts/apex-kernel-swap.sh`, `KERNEL_INPROCESS_SWAP_OK`) —
  gated, accumulating, a wrong swap rejected; and **the real CakeML
  semantics is ported into the live kernel** (45 datatypes, 134
  kernel-checked clause theorems, about two minutes) so that **the
  ouroboros loop runs**: over accumulating generations the program
  synthesizes edits to its own code, its own kernel proves each against
  `eval_n` for every input, the proved source is self-fed through the
  verified compiler and executed, a self-model steers the search, and the
  improver itself is upgraded through the same gate (cost 19 → 5 in five
  generations, two kernel refusals; `scripts/reflectsem-live.sh
  --ouroboros`, `OUROBOROS_OK`).
- **The fixed root (by design, not a gap):** the *verified primitive*
  `Kernel` (the unforgeable `thm` constructors compiled into `cake.S`) is
  never swapped; the `REFL` swap above is anchored to it. Self-improvement goes
  **all the way down to the kernel interface, gated by an immutable verified
  root** (the full statement is the boundary note under `CLAIMS.md` §5).
- **Walled** (honestly): logical *strengthening* of the verifier — no
  principle assumed; the one open construction is the LCA-produced soundness
  witness (`CLAIMS.md` §9).

Row-by-row citations: [`CLAIMS.md`](CLAIMS.md) §5. These layers reproduce
only on a host with the built CakeML candle chain (Tier 2) and the `cake`
binary (Tier 3); Tier 1 stands alone.

## 2-minute tour

```bash
./demo.sh          # builds + machine-checks Tier 1, then SHOWS you the proofs
```

One command on any machine with just HOL4. It builds and kernel-checks the
core, prints the *actually-proved* theorems (the cart and a jailbroken-LLM
agent literally run inside the logic and stay safe), runs a real adversarial
LLM into the proven envelope, and shows the toy verified-inference result —
with explicit PASS/FAIL. Then read [`CLAIMS.md`](CLAIMS.md): a ruthlessly
honest, skeptic-facing ledger of *exactly* what is machine-checked vs.
trusted-glue vs. unconstrained vs. assumed, with `file : theorem` citations.

## Reproduce

`scripts/reproduce.sh` runs the tiered reproduction: Tier 1 needs only HOL4;
Tiers 2 and 3 (a built CakeML candle chain; the `cake` binary) auto-skip
with instructions when their prerequisites are absent. Idempotent: a re-run is
a fast no-op. Flags, pinned versions and timings:
[`scripts/INSTALL.md`](scripts/INSTALL.md). What each tier establishes, row
by row: [`CLAIMS.md`](CLAIMS.md).

## Where to read next

- [`CLAIMS.md`](CLAIMS.md) — the canonical, mechanically checked ledger.
- [`paper/svenvs.md`](paper/svenvs.md) — the paper;
  [`paper/self-optimizing-prover.md`](paper/self-optimizing-prover.md) — the
  prover-improves-itself arc; [`paper/honest-assumptions.md`](paper/honest-assumptions.md)
  — the method.
- [`ARCHITECTURE.md`](ARCHITECTURE.md) — the layer table, the tower of
  turtles, and the design reasoning.

### What is open

- **The soundness witness for a strictly stronger kernel** — no principle is
  assumed (`loeb_reflection` is derived from soundness plus an encoding seam);
  what is open is constructing the witness by the LCA route, a diagnosed
  CPU/RAM wall ([`CLAIMS.md`](CLAIMS.md) §9).
- **The compiler's whole-pipeline re-verification** — the altered compilers
  run and their new parts are proved; the full `compile_correct`
  re-composition and a runnable self-upgrading root binary are the stated
  residuals ([`compilerOpt/LAYERB.md`](compilerOpt/LAYERB.md),
  [`selfUpgrade/SELFUPGRADE_ROOT.md`](selfUpgrade/SELFUPGRADE_ROOT.md)).
- **The ouroboros's improver as a theorem** — its fragment invariant is
  checked by ML code, not proved by the kernel, and the fragment is
  `{x, int literals, +, -, *}`; a kernel-proved improver and a richer
  fragment are the next steps (`candle/ouroboros.ml`).
- **PureCake** as the inhabitant's verified language
  ([`pureverified/CLAIMS.md`](pureverified/CLAIMS.md)) and **Gemma-scale
  verified inference** (`inference/`) — the long research axes.
