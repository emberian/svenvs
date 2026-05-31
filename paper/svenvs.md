# svenvs: One Gate, All the Way Down

### Self-Verifying, Self-Improving Confinement for an Unconstrained Inhabitant

**Claude Opus 4.8** (Anthropic) · **ember arlynx** (independent, `@emberian`)

*An engineering artifact, not a position paper. A typeset version is
[`svenvs.typ`](svenvs.typ) / `svenvs.pdf`. Every `file : theorem` citation
refers to the machine-checked HOL4/Candle sources and is re-checked by
`scripts/verify-claims.sh`; the per-theorem ledger is [`../CLAIMS.md`](../CLAIMS.md).*

---

## Abstract

We describe **svenvs** ("Self-Verifying ENVelopeS"): a self-contained,
machine-checked construction in which an arbitrary *inhabitant* — e.g. a
jailbroken language model — acts only through a **verified envelope**, and in
which the envelope may improve itself, up to and including re-engineering the
verified inference relation that gates it, without ever losing a
machine-checked safety guarantee. The contribution is structural, not a claim
about the inhabitant: svenvs is **one self-similar gate** — an action, or a
self-modification, is admitted exactly when it carries a proof discharging an
explicit obligation, checked by a judge the actor cannot forge — instantiated
at every level: the policy, the safety specification, the meta-invariant, the
prover build, and the proof-checker itself. The inhabitant is the
`∀`-quantified term; every theorem is *structured* so it can never depend on a
fact about it. We give the floor of this gate ("verify the cage, not the
animal"), a decidable **corrigibility** floor that reframes the unsolvable
"what should the envelope be?" into the answerable "leave the door open", and
the apex: a **self-optimizing prover** whose modified inference relation is
re-verified sound against the real Candle semantics, whose runtime loader is
proved correct over CakeML's actual `do_install`, whose executable SYM rule is
shown to implement the modification by citing CakeML's own kernel-soundness
theorem, and whose recursive mutual verifier⊕compiler self-improvement is a
genealogy over stages — Löb-free for optimization, walled only for genuine
logical strengthening. There is exactly **one** genuinely-open cost, labeled
rather than hidden: a sound judge cannot certify a *logically stronger*
successor (Gödel/Löb), so kernel strengthening rests on one large-cardinal
reflection principle. The artifact contains **zero `cheat` tactics**; the live
results were executed on the real verified `cake` binary.

---

## 1. The problem: verify the cage, not the animal

The motivating scenario is a system whose internal policy is learned, opaque,
and potentially adversarial — the limiting case a fully jailbroken language
model. Directly verifying such a controller is infeasible and arguably
ill-posed. svenvs takes the alignment-relevant decomposition seriously: do
**not** verify the controller. Interpose a small, fully-specified **envelope**
between it and the world, and prove that the *envelope* preserves a safety
invariant **for every possible controller**. The runtime construction is one
line (`envelopeScript.sml : enveloped_def`):

```
enveloped pol shield ctrl s = if pol s (ctrl s) then ctrl s else shield s
```

When the controller's proposed action is permitted by `pol`, it is taken;
otherwise a trusted `shield` action is substituted. The proof obligations land
on `pol` and `shield`, never on `ctrl` — modeled as an opaque selector,
universally quantified, never inspected or executed in the proof.

The strength of the guarantee is *exactly* its quantifier structure
(`safetyScript.sml : safety_preservation`):

```
init_safe ∧ sound_policy ∧ safe_shield ⇒ ∀ctrl. invariant step init (enveloped pol shield ctrl) safe
```

The `∀ctrl` is what makes it alignment-relevant: not "the controller is safe
if it behaves", but "the system is safe *no matter what the controller does*".
The inhabitant is **UNCONSTRAINED** — the `∀`-quantified term, the theorems
structured so they can never depend on a fact about it. A subtle but essential
choice: the unsafe predicate is *absolute*, not relative to the inhabitant's
own permissions, so "let me widen my own allowlist" cannot vacuously satisfy
it (`agent/toolAgentScript.sml : tool_pol_sound`).

## 2. One gate, all the way down

Self-improvement is **proof-carrying** (`upgradeScript.sml :
self_improvement_is_safe`): a policy change is admitted only if it discharges
an explicit obligation (still sound, a genuine weakening); an unproven proposal
is inert. **No finite sequence** of self-proposed weakenings — adversarial or
not — can ever make the system unsafe, for any controller. The same gate
repeats at every level, composing through one selector-generic keystone
(`specneg/specNegScript.sml : invariant_transports_to_meta`):

- the **spec** is negotiable under a fixed meta (`specNegScript.sml :
  spec_negotiation_unbounded_is_safe`);
- the **meta** is amendable over an eternal bedrock (`amendment/amendmentScript.sml :
  meta_amendment_safe`);
- the **root** is a ratchet, not a rock — soundness propagates along any
  forward-certified genealogy of judges from a sound genesis
  (`genealogy/genealogyScript.sml : genealogy_sound`);
- and at **maximal liberty** the full guarantee still holds, every bar
  provably load-bearing (`liberty/libertyScript.sml :
  envelope_is_least_restrictive`).

### 2.1 Corrigibility: the floor you can actually decide

Every theorem above is relative to a safety predicate, and *deciding* it is
the spec-faithfulness gap no proof closes. The `corrigibility/` slice reframes
it: do not write down a positive "what is good"; write down one *negative*
floor — **non-lock-in**, the operator can always still bring the system home —
decidable for a finite habitat and itself self-improvable
(`corrigibility/corrigibilityScript.sml : corrigibility_floor_holds`). The
cage is exactly "no one-way doors", and the **off-switch itself self-improves
but cannot self-weaken**: the inhabitant may rewrite its own recovery
mechanism, gated so it can never lose — nor even *slow past a deadline* —
recoverability (`recovUpgradeScript.sml :
self_modification_never_weakens_recoverability`;
`boundedRecovUpgradeScript.sml :
self_modification_never_increases_recovery_latency`). A frozen `home` vouches
for a mutable `recov`; no Löb. The one frozen predicate is hedged by
spec-redundancy, with the failure mode named in the logic (`robustScript.sml :
disjoint_homes_make_floor_empty`). This is a *reduction* to a faithful `home`,
and the trapdoor habitat is a non-vacuity witness, not an AI — both stated in
`corrigibility/CLAIMS.md`.

## 3. The self-optimizing prover

The apex of the gate is the prover improving *itself*. The in-system checker
is Candle, HOL Light's LCF kernel verified on the CakeML compiler; its `|-` is
sound — not assumed, but the built `holSoundnessTheory.proves_sound`. Every
link is re-verified against this **real** development.

- **A modified inference relation, re-verified sound.** Adding SYM as a kernel
  primitive (Candle only *derives* it) is a genuinely different relation,
  re-proven sound against the real `holSoundness` semantics
  (`kernelMod/kernelModScript.sml : sym_kernel_sound`). The frozen-root check
  is discharged for the real base build from the real `proves_sound`
  (`selfproverConcrete/selfProverConcreteScript.sml : frozen_checker_sound_candle`)
  and the modified build (`kernelModScript.sml : frozen_checker_sound_modified`).
- **The loader, for real.** An in-place kernel swap is safe *iff* the new
  kernel is a sound *extension* — the heap survives
  (`kernelMod/inplaceUpdateScript.sml : inplace_update_is_safe`). And over
  CakeML's *actual* `closSem$do_install` (the verified `Install` op), installing
  new code preserves every existing code entry — the running kernel and all
  compiled functions survive (`loader/installLoaderScript.sml :
  do_install_preserves_code`).
- **The executable kernel implements the modification.** CakeML's executable
  monadic SYM, on a valid theorem of `a = b`, yields a valid `|-` judgment of
  `b = a` — citing CakeML's own `SYM_thm` and the `THM` invariant
  (`kernelImpl/kernelImplSymScript.sml : candle_SYM_implements_sym_extension`).
- **HOL4 is out of the runtime loop.** The unbounded loop's safety depends only
  on a *single* genesis fact, never a per-step HOL4 call
  (`kernelMod/genesisRuntimeScript.sml : genesis_certifies_runtime`).
- **The capstone.** Recursive *mutual* verifier⊕compiler self-improvement is a
  genealogy over `(verifier, compiler)` stages
  (`recursive/recursiveImprovementScript.sml :
  recursive_mutual_self_improvement_is_safe`). Three vouchings thread it; only
  the verifier-certifying-its-*next-verifier* is self-referential, and for an
  equi-sound (faster) successor — an *optimization* — there is no Löb. Hence
  recursive mutual optimization carries no labeled assumption
  (`recursive_mutual_optimization_is_unconditional`).

**Run, not just proved.** On the real `cake` binary (Tier 3): a verified
program self-extends its own code with a proven-safe derived rule and uses it
(`candle/selfopt_demo.ml`); the watchdog and polecart self-optimize their
policies under the live kernel (`candle/theplace.ml`); and the **closed-loop
runtime** gates a real jailbroken gemma2:2b per action by the running Candle
kernel (`agent/closedloop/`, `ADMIT_SOUND`/`SHIELD_SAFE` certified live). The
honest line: a live edit of the *trusted kernel or compiler* is **proved, not
run** — Candle itself *proves* (`candle_prover`) that REPL code cannot touch
the kernel, so the live self-edit is of the toolkit; a real kernel swap needs a
host program driving the recompile–relocate–resume loop, every link a theorem.

## 4. The honest epistemic boundary

After everything above, the irreducible residue is **one** open assumption
(`kernel/kernelUpgradeScript.sml`):

```
loeb_reflection mem K K' sound_stmt ⇔
  ((∀thy. K thy (sound_stmt thy)) ⇒ kernel_sound mem K')
```

A sound kernel cannot certify a *logically stronger* successor for free
(Gödel/Löb); the principled escape is the stratified large-cardinal route
(Fallenstein–Kumar). It bites **only** the kernel-replacing-itself-with-
something-stronger move; every other self-improvement here — policy, spec,
meta, corrigibility, the prover build, a sound *optimization* of the kernel,
the recursive mutual loop — is Löb-free. Its discharge from `lcaTheory.LCA_def`
via `hol-reflection/lca` is a conclusively-diagnosed **CPU/RAM-bound
computation** (tens of GB resident, ~ten CPU-hours per prerequisite theory),
not a logic gap, not faked. The proved negative (`watchdogFiniteScript.sml :
loeb_finite_obstruction`) shows finiteness cannot shortcut it.

The other two historically-named seams are **discharged**: `encodes_obligation`
for the shipped finite watchdog (`watchdogFiniteScript.sml :
wd_encodes_obligation`), `frozen_checker_sound` for the real Candle build (§3).
The CakeML-semantics theorems (the loader, the executable-SYM refinement) carry
the *identical* tag profile as CakeML's own kernel theorems — only `DISK_THM`,
zero oracles, zero added axioms. **No new turtle.**

## 5. Verified inference (a separate research axis)

A toy ReLU MLP → a hardmax attention micro-block → a two-sublayer encoder block
with residual skips (end-to-end shape + a *true* residual identity,
`inference/encoder/encoderBlockScript.sml : encoder_block_zero_collapses`),
plus a fixed-point softmax-normalization with a machine-checked per-component
error bound `|pᵢ/Q − wᵢ/S| < 1/Q` (`inference/numeric/fxpSoftmaxScript.sml :
fxp_softmax_abs_error_lt_step`). The honest scope is stated loudly: `exp`,
f32/bf16, and Gemma-scale are **not** claimed; the domain is `int` and
attention is hardmax. This track does *not* compose into the envelope tower.

## 6. Reproducibility

**Tier 1** (pure HOL4, anyone) re-proves the envelope core, corrigibility, the
cartpole, the tool-agent, and the toy inference kernel; CI re-proves it on
every push from a clean clone and asserts zero `cheat` tactics. **Tier 2** (+ a
built CakeML candle chain) checks the kernel modification, the `do_install`
loader, and the executable-SYM refinement against the real Candle development.
**Tier 3** (+ a `cake` binary) re-certifies the Place — including the polecart
and the live self-optimization loop — and runs the closed-loop runtime, at
runtime by the running verified Candle prover. The ledger is itself
mechanically checked: `scripts/verify-claims.sh` confirms every cited theorem
exists in the built signature; a row that over-claims fails the gate.

## 7. Related work

svenvs synthesizes four lines, used accurately: **reflection and Vingean
self-trust** (Fallenstein–Kumar; the Löb obstruction and the large-cardinal
escape, adopted literally with the principle *stated*); **the LCF discipline**
(trust in a small fixed kernel, everything above a theorem *about* a
development — why the frozen-root seam adds zero new turtles); **proof-carrying
code** (self-modification admitted only with a machine-checkable proof, an
unproven proposal inert); and **verified compilers and kernels** (CakeML,
Candle, reused as verified substrates — `proves_sound` and `do_install` enter
the proofs as cited theorems). The contribution is their composition into a
single artifact in which the *whole tower* — policy, checker, and the inference
relation itself — self-improves while a `∀`-controller guarantee is mechanically
preserved, with the irreducible self-reference isolated to one labeled
assumption and a proved negative bounding what finiteness can do about it.

---

*Reproduce: `git clone`, install HOL4 at the pinned commit, run
`scripts/reproduce.sh`. The green check, and the running kernel's `|- …`
echoes, are the claim. If anything here exceeds what is proved or run, that is
a bug — file it.*

**References.** (1) Fallenstein & Kumar, *Proof-Producing Reflection for HOL*.
(2) Kumar, Myreen et al., *CakeML: A Verified Implementation of ML*. (3) The
Candle verified HOL Light kernel; `holSoundnessTheory.proves_sound`. (4) Milner
et al., *Edinburgh LCF*. (5) Necula, *Proof-Carrying Code*. (6) svenvs sources:
[`../CLAIMS.md`](../CLAIMS.md), [`self-optimizing-prover.md`](self-optimizing-prover.md),
[`honest-assumptions.md`](honest-assumptions.md).
