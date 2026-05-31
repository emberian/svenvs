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
spec-redundancy. 10 theories, pure HOL4, zero `cheat`; the honest boundary —
that this is a *reduction* to a faithful `home`, and the runnable plant is a
*non-vacuity witness, not an AI* — is stated, machine-checked, in
[`corrigibility/CLAIMS.md`](corrigibility/CLAIMS.md).

This is the legible front door to the larger artifact, which is the same gate
— *an action is admitted iff it carries a proof the actor cannot forge* —
instantiated all the way down: policy, spec, meta-invariant, prover build,
and the proof-checker itself.

**What "verified" means here — load-bearing, not preface.** Exactly the
cited theorems and their labeled seams. **Not** verified selfhood,
continuity, alignment, welfare, or a safe *inhabitant*. Only the
*envelope* is proved sound, modulo the named assumptions. If "svenvs runs
verified" starts carrying more than that, the extra meaning is the
reader's, not the artifact's.

CI re-proves **Tier 1 only** on every push: from a clean clone, on a stock
Ubuntu runner, the HOL4 kernel (pinned commit) re-checks the whole pure-HOL4
core and a scan asserts zero `cheat` tactics — so the green check is itself a
continuously-renewed credibility artifact. It does **not** exercise Tiers 2/3
or discharge the labeled assumptions in general (three; one already
discharged for the shipped finite instance — those need heavy/dedicated
infra; see `CLAIMS.md`).

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
  swap is safe iff the new kernel is a sound *extension*, so the heap
  survives (`kernelMod/inplaceUpdate`); the unbounded self-optimization loop
  stays sound (`kernelMod/selfOptimize`); **the loader, over CakeML's actual
  `closSem$do_install`, preserves every running code entry**
  (`loader/installLoader`); **the executable Candle SYM kernel function
  soundly implements the modified rule** (`kernelImpl/` — citing CakeML's own
  `SYM_thm`/`THM_def`); HOL4 is provably *out of the runtime loop*
  (`kernelMod/genesisRuntime`); and **recursive *mutual* verifier+compiler
  self-improvement is a genealogy over `(verifier, compiler)` stages**
  (`recursive/`) — Löb-free for optimization, walled only for genuine
  logical *strengthening*.
- **Ran live** on the real `cake` binary (Tier 3): a verified program
  self-extends its own code with a proven-safe derived rule and uses it
  (`candle/selfopt_demo.ml`), and the polecart + watchdog self-optimize their
  own policies under the live kernel (`candle/theplace.ml`).
- **Proved, not run:** a live edit of the *trusted kernel or compiler*.
  Candle *proves* (`candle_prover`) that REPL code cannot touch the kernel —
  so the live self-edit is of the *toolkit*, never the verifier; executing a
  real kernel swap needs a host program driving the recompile-relocate-resume
  loop, every link of which is already a theorem.
- **Walled** (honestly): logical *strengthening* of the verifier — the one
  Gödel/Löb seam (`loeb_reflection`, LCA), isolated and labeled.

These layers reproduce only on a host with the built CakeML candle chain
(Tier 2) and the `cake` binary (Tier 3); Tier 1 stands alone.

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

```bash
scripts/reproduce.sh            # full tiered reproduction
scripts/reproduce.sh --quick    # skip optional/slow extras
scripts/reproduce.sh --clean    # force a from-scratch rebuild
```

Idempotent: re-running is a fast no-op (Holmake caches); Tier 2/3 auto-skip
with instructions if their (heavy) prerequisites are absent.

Tiered, degrades gracefully to your toolchain:

- **Tier 1** — pure HOL4 (anyone): the full proof-carrying self-improvement
  core + the **corrigibility floor** (`corrigibility/`: non-lock-in as a
  decidable, self-improving, latency-tunable envelope, composed into the
  tower as bedrock, with spec-redundancy on its one frozen predicate) + a
  runnable cartpole + an adversarial-LLM tool-agent with a *running*
  proof-carrying capability-expansion episode + a real jailbroken Gemma
  contained by the proven envelope (`agent/embodied/`) + a toy
  *verified-inference* kernel (`inference/`, research track B).
- **Tier 2** — + a built CakeML candle chain: the admission obligation is
  discharged by Candle's *verified inference system*; kernel-self-upgrade.
- **Tier 3** — + a Candle binary: the Place's core theorems re-certified
  **at runtime by the running verified Candle prover**.

Prerequisites & pinned versions: [`scripts/INSTALL.md`](scripts/INSTALL.md).
What each layer proves and its **honest epistemic status** (what is
unconditional vs. the three explicit labeled assumptions, one already
discharged for the shipped finite instance):
[`ARCHITECTURE.md`](ARCHITECTURE.md) and the per-theorem ledger
[`CLAIMS.md`](CLAIMS.md). Design rationale: [`DESIGN.md`](DESIGN.md).

### Roadmap axes (in progress — explicitly NOT yet claimed as done)

- **PureCake** (`pure/`) as the inhabitant's *verified* language.
- **Closed-loop runtime** (`agent/closedloop/`): each admission a real,
  live Candle proof.
- **Verified tensor acceleration / attention** (`inference/accel/`,
  `inference/attn/`): climbing from the toy MLP toward a verified block.
- **Discharging the labeled assumptions** (`loeb_reflection`,
  `encodes_obligation`, `frozen_checker_sound`; the second already
  discharged for the finite watchdog) on the dedicated host →
  fully unconditional end-to-end.

These are concurrently-developed frontiers; see `CLAIMS.md` § Roadmap for
their exact (un-overclaimed) status.

## Status in one paragraph

The self-improving-self-verifying architecture — including upgrading the
verified kernel — is **proved, mechanically checked, cheat-free**, today, in
pure HOL4 (Tier 1), with the core re-certified live by the running Candle
prover (Tier 3). The only non-mechanical content is **three explicit,
labeled, literature-standard assumptions** (`loeb_reflection`,
`encodes_obligation`, `frozen_checker_sound`), each isolated to one line,
each with a known discharge path. Of these, `encodes_obligation` is
**already discharged** for the shipped finite watchdog instance (a real
ASSUMED→PROVED flip, with the precise honest negative `loeb_finite_obstruction`
about why the general case is not cheaply dodged), and `frozen_checker_sound`
is discharged concretely for a real modified Candle build (the frozen HOL4
root re-proving a genuine `holSoundness` source diff). `loeb_reflection`'s
general discharge is the heavy `hol-reflection/lca` + `reflectionLib` proof —
a conclusively-diagnosed compute wall, not a porting failure and not faked;
that it is *labeled* rather than hand-waved is exactly the point. See
[`CLAIMS.md`](CLAIMS.md) for the line-by-line ledger and the full cheat
audit (including one stale comment, disclosed in full).

Separately, the **corrigibility** neighborhood (`corrigibility/`, 10
theories, ~60 theorems, pure HOL4, zero `cheat`, its own proof-carrying
[`corrigibility/CLAIMS.md`](corrigibility/CLAIMS.md)) proves the
non-lock-in floor and its self-improvement, latency, tower-bedrock, and
spec-redundancy facts — the legible front door above — entirely within
Tier 1, with every honest boundary stated in the logic rather than the
prose. It is the answer to the question the rest of the artifact assumes
away: *what should the envelope be?* — leave the door open, and prove the
rest.
