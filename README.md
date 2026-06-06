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
(the real CakeML/Candle layers — kernel modification, the `do_install` loader,
the live prover) or discharge the one genuinely-open assumption
(`loeb_reflection`, the LCA wall; the other two named seams are discharged —
see `CLAIMS.md`).

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
- **Ran live** on the real `cake` binary (Tier 3): (1) a verified program
  self-extends its own code with a proven-safe derived rule and uses it
  (`candle/selfopt_demo.ml`); (2) the polecart + watchdog self-optimize their
  own policies under the live kernel (`candle/theplace.ml`); (3) a **proof-gated
  recompile→swap→resume loop** (`candle/self_recompile.ml`) replaces a running
  routine's compiled code at runtime — each swap gated by a live kernel
  equivalence proof, swaps accumulating path-dependently, an unprovable swap
  rejected (`verdict = "APEX_SUBSTRATE_OK"`); and (4) **the verified compiler
  recompiles itself** — `cake` compiles its own s-expression into a new working
  `cake` (bit-identical **FIXPOINT**) and into a self-**optimized** variant that
  is still a correct compiler (correctness = CakeML's compiler-correctness).
  The whole **Apex** — compiler self-recompilation + proof-gated prover
  self-improvement — is run end-to-end by `scripts/apex.sh` (emits **DIAMOND**)
  and **proved safe** in `apex/apexScript.sml` (`apex_generations_safe`: every
  generation has a sound prover and a correct compiler, for any path). And (5)
  **an in-process swap of a KERNEL PRIMITIVE under the whole live prover**
  (`scripts/apex-kernel-swap.sh`, `candle/kernel_swap_demo.ml`): the kernel
  interface the entire prover calls (`REFL`) is re-architected into a live
  indirection (`candle/kernel_apex.patch`); the running prover's `REFL` is
  swapped mid-flight for a different sound derivation — gated, accumulating, a
  wrong swap rejected — and it keeps proving through the swapped primitive
  (`verdict = "KERNEL_INPROCESS_SWAP_OK"`). Sound **by construction**: the swap
  target must still mint its `thm` through the verified `Kernel`, which cannot be
  forged.
- **The fixed root (by design, not a gap):** the *verified primitive* `Kernel`
  (the unforgeable `thm` constructors compiled into `cake.S`) is never swapped —
  it is the immutable root of trust the in-process kernel swap above is anchored
  to. Swapping *it* is neither possible (you cannot forge a `thm`) nor desirable
  (it would dissolve the very guarantee). Self-improvement goes **all the way
  down to the kernel interface, gated by an immutable verified root** — which is
  exactly the Apex: improve everything; the root that makes "improve safely"
  meaningful stays put.
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
  discharged by Candle's *verified inference system*; the kernel modification,
  the loader over the real `do_install`, and the executable-kernel SYM
  refinement all check against the real Candle development.
- **Tier 3** — + a Candle binary: the Place (incl. the polecart),
  the live self-optimization loop, and the **closed-loop runtime** (a real
  jailbroken gemma2:2b gated per-action) re-certified **at runtime by the
  running verified Candle prover**.

Prerequisites & pinned versions: [`scripts/INSTALL.md`](scripts/INSTALL.md).
Per-theorem epistemic status: [`CLAIMS.md`](CLAIMS.md) (the self-optimizing-
prover arc: [`paper/self-optimizing-prover.md`](paper/self-optimizing-prover.md)).
Architecture: [`ARCHITECTURE.md`](ARCHITECTURE.md). Design: [`DESIGN.md`](DESIGN.md).

### Where the frontier actually is now

Two of the three named seams are **discharged**: `encodes_obligation` for the
shipped finite watchdog, `frozen_checker_sound` for the real Candle build. The
closed-loop runtime is **live**. What genuinely remains:

- **`loeb_reflection`** — the one Gödel/Löb seam: a sound kernel certifying a
  *logically stronger* successor. Discharged from `lcaTheory.LCA_def` via the
  heavy `hol-reflection/lca` — a diagnosed CPU/RAM wall, not a logic gap;
  `loeb_finite_obstruction` proves finiteness cannot shortcut it. Every
  *other* self-improvement here — including a sound *optimization* of the
  kernel and the recursive mutual verifier+compiler loop — is Löb-free.
- **A live edit of the trusted kernel/compiler** — proved end to end, not
  *run*: it needs a host program driving the recompile-relocate-resume loop
  (the live REPL self-extends the toolkit, never the kernel — `candle_prover`
  proves it can't).
- **PureCake** (`pure/`) as the inhabitant's verified language; **Gemma-scale
  verified inference** (`inference/`) — the long research axes.

## Status in one paragraph

The self-verifying, self-improving architecture — policy, spec, meta, the
prover build, and the inference relation itself — is **proved, mechanically
checked, cheat-free**, today, in pure HOL4 (Tier 1), re-certified live by the
running Candle prover (Tier 3), and where it touches the running prover (the
loader, the executable-kernel SYM refinement) checked against the **real
CakeML/Candle** with no oracle beyond the benign disk tag. The inference
relation can be re-engineered and re-verified sound, the loader provably
preserves the running heap, and the recursive mutual verifier+compiler
self-improvement is a theorem. The **one** genuinely-open cost is the single
labeled `loeb_reflection` — strengthening the kernel's *logic* (Gödel/Löb,
LCA), isolated to one `Definition`, with a proved negative bounding what
finiteness can do about it. Everything else is unconditional. The assumptions
are stated, not hidden; if anything is overclaimed, that is a bug.

Separately, the **corrigibility** neighborhood (`corrigibility/`, 10
theories, ~60 theorems, pure HOL4, zero `cheat`, its own proof-carrying
[`corrigibility/CLAIMS.md`](corrigibility/CLAIMS.md)) proves the
non-lock-in floor and its self-improvement, latency, tower-bedrock, and
spec-redundancy facts — the legible front door above — entirely within
Tier 1, with every honest boundary stated in the logic rather than the
prose. It is the answer to the question the rest of the artifact assumes
away: *what should the envelope be?* — leave the door open, and prove the
rest.
