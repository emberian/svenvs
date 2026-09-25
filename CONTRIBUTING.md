# Contributing to svenvs

This file is the handoff: what the project is for, the rules it lives by,
how to work on it without breaking those rules, the end-state it is
steering toward, and the routes of ambition we picked, ranked. The
maintainers may be away for a while; everything you need to pick a route
and finish it is meant to be here or one link away.

## 1. What this is for

A verified gate that an unconstrained inhabitant acts through, applied to
every layer that could be self-modified: the policy, the spec, the
meta-invariant, the prover build, the proof-checker, and now the running
program's own code. The claim is never "the inhabitant is safe"; it is
"safety is never lost through this gate, and here is the theorem". The
bar set by the maintainer is: **the whole real CakeML**, no toy fragments,
no side languages, no baked-in swaps. The gate is a *schema*
(semantics-preservation over the real semantics held in the nested
kernel); novel edits arrive at runtime with proofs; the kernel checks
them; then the real install happens. Offline theorems justify the gate
discipline for every future edit; the runtime justifies each instance.

## 2. The rules (non-negotiable)

1. **The ledger is the truth.** `CLAIMS.md` (and the per-directory
   `CLAIMS.md` files) carry every claim as a row with a label (PROVED, RAN,
   TRUSTED-GLUE, UNCONSTRAINED, ASSUMED) and a `path/XScript.sml : thm1, thm2`
   citation. `scripts/verify-claims.sh` resolves every citation against the
   built signatures, checks the carried seams are `Definition`s, scans for
   `cheat` / `new_axiom` / `mk_thm` / `mk_oracle_thm` with comments stripped,
   and enforces the framing (the retired labels never return). If a doc
   says more than the ledger, the doc is wrong.
2. **No `cheat`, no oracle, ever.** Not as a placeholder, not "to be filled
   in". A theorem that cannot be proved is stated as a labeled seam
   (`Definition` + antecedent) or as an open construction in §9, never
   admitted.
3. **Gates are operational.** A gate installs iff its certifier said yes.
   Never let a theorem branch on the semantic predicate the certificate is
   supposed to establish (that was the vacuity this artifact once had:
   hypotheses that did no work). Beside every seam stands a necessity
   theorem, ideally an iff (`certifierScript.sml : sound_certifier_iff_cgate_safe`
   is the pattern); a bare ∃-witness only where an iff needs a side
   condition.
4. **Nothing baked to a machine.** Hosts, keys, temp paths and toolchain
   locations come from the environment (`scripts/env.sh`, `SVENVS_CANDLE_*`,
   `PLACE_DIR`, `REFLECTSEM_OUT_DIR`). Upstream pins are full commit SHAs
   (`scripts/env.sh`, `scripts/INSTALL.md`, `.github/workflows/verify.yml`,
   all in lockstep). Scripts that must edit an upstream checkout are opt-in
   (`SVENVS_ALLOW_INPLACE=1`) and refuse a dirty tree.
5. **Green plus a summary is not verification.** A claim lands when the
   gate that refutes it was run and its decisive lines are quoted: the
   kernel's `val … = |- …` echoes, the verdict strings, the tier scripts'
   final lines, the ledger check's `CLAIMS LEDGER VERIFIED`.

## 3. How to work

**Tiers.** Tier 1 is pure HOL4 at the pinned commit (`scripts/tier1-core.sh`,
the composed tower `scripts/tower.sh`, and `corrigibility/`). Tier 2 needs
CakeML's `candle/standard/semantics` built (`scripts/tier2-candle-layers.sh`,
`scripts/tower.sh --full`). Tier 2.5 needs the deeper CakeML theories
(`scripts/tier2.5-cited-layers.sh`). Tier 3 needs the `cake` binary
(`scripts/tier3-place-candle.sh`, `scripts/apex*.sh`,
`scripts/reflectsem-live.sh`). `scripts/reproduce.sh` runs what your
toolchain allows and skips the rest loudly.

**The Place.** `scripts/place-server.sh` starts a Candle with `hol.ml`
preloaded under a per-user `PLACE_DIR`; `place-submit.sh <file> <SENTINEL>`
feeds a file and prints the kernel's output for that submission;
`place-stop.sh` stops exactly that server. The closed-loop demos reach a
server on any host through `SVENVS_CANDLE_HOST` (see
`agent/closedloop/README.md`).

**Build boxes.** Anything heavy runs on a Linux box, never a laptop. Mirror
the working tree with rsync (exclude `.git`, `.hol`, `*Theory.*`, `*.ui`,
`*.uo`), build inside the mirror, always `--no-cache` (parallel Holmake
deadlocks against its theory cache otherwise). A proof that prints nothing
for five minutes at high memory is a non-terminating `metis_tac`, not
progress. Before believing any hang or failure reported from a shared
mirror, wipe the affected `.hol` directories and rebuild clean; stale
objects have produced false hangs. Never rebuild inside the pinned HOL4 or
CakeML checkouts; `realembedded/` is unbuildable in practice (its
hol-reflection certificate step does not terminate) and is cited nowhere.

**Working in parallel (humans or agents).** Disjoint file ownership per
lane; one mirror per lane; commit by explicit path, never `git add -A`;
never `git stash`; keep every cited theorem name, and when a statement must
change, change the ledger row in the same commit. After a lane touches a
shared definition, build the whole tree, not just the changed files.

**Proof-engineering conventions.** Necessity theorems: prefer an iff; an
∃-over-num witness where the iff needs a side condition. Instances: when a
layer's theorem is an instance of the certifier theory, its proof is the
instantiation, not a re-run of the argument. Every new theorem: no unused
hypothesis (add the counterexample or drop the hypothesis). History lives
in commit messages, not theorems.

## 4. The attractor

The end-state the development is steering toward, so that a session
mid-work makes the right choice:

- **One gate**: `cgate` is the only if-then-else gate (`gate`, `swap`,
  `vouch_sound`, `forward_certified` are already overloads of the certifier
  theory's constants); the wrappers `kernel_gate`, `kgate`, `prover_gate`
  are one-line definitions over it.
- **One ratchet, one transfer lemma**: every soundness notion is
  `sound_certifier` at its meaning, so transfer / gate-safety /
  stream-safety are instantiated, not restated.
- **One iff per seam**, one naming convention for the residual witnesses.
- **Seams are read from the ledger**, never hardcoded.
- **A ledger row cites at most about five names**: definition, safety
  instance, iff, install/reject.

Accretion to watch: "a witness theorem per hypothesis"; "keep the old name
for citation stability" (rename in the ledger instead); per-layer
install/reject/agrees trios; environment knobs.

## 5. Routes of ambition (preselected, ranked)

Each route says why, what "done" means (a theorem or a verdict string the
kernel echoes), the first step, and the size.

### R1. The ouroboros as a theorem, on the whole real language

*Why.* This is the point of the project: a running binary that edits its
own code, proves each edit with its own kernel against the real semantics,
installs it, and improves its improver. Today it runs (five generations,
cost 19→5, improver upgraded) on the fragment `{x, int literals, +, -, *}`
of the real `ast$exp`, and its fold/dead rewriter is a kernel theorem.
*Done.* `OUROBOROS_OK` with every accepted generation installed via a
rewriter theorem (zero per-candidate symbolic executions), on a fragment
that includes `Let`, `If`, `Fn`/`App` and `Letrec`, with the improver's
invariant a kernel theorem rather than an ML check, and the improver
improving its own improver through the same gate.
*First step.* Prove `collect` and `double` in `candle/ouroboros_rewrites.ml`
the way `ofold` is proved (a binary `oexp` embedded into the real `exp`,
`ofrag_oemb` fixing the image), then widen `oexp` one constructor at a time
with `OEVAL`-style step lemmas over the exported `eval_n_def`. The driver
is `scripts/reflectsem-live.sh --ouroboros`; a run is about five minutes
cold. *Size.* Weeks; each constructor is a lane.

### R2. Continuous verification of the whole tower

*Why.* CI re-proves Tier 1 only. The composed tower (pca, specneg,
selfprover, liberty, amendment, embodiment, genealogy, integration) and
corrigibility are pure HOL4 and cheap, yet verified only by hand; the
ledger check runs non-strict, skipping what is not built.
*Done.* `verify.yml` runs `scripts/tower.sh` and `corrigibility/` after
Tier 1 and `verify-claims.sh --strict` over everything pure HOL4; then a
second job with a cached CakeML candle chain runs Tier 2 and Tier 2.5 so
`kernel/`, `embedded/`, `kernelMod/`, `loader/`, `compilerOpt/`,
`selfUpgrade/` and the Löb reduction are re-proved on every push.
*First step.* Add `tower.sh` and the corrigibility build to the Tier-1 job
(minutes). The candle chain cache is the only hard part of the second job.
*Size.* A day for the first, a few days for Tier 2 in CI.

### R3. Attractor step two

*Why.* Half the remaining witnesses and every tie theorem exist because
each layer defines its own soundness notion.
*Done.* `kernel_sound`, `frozen_checker_sound`, `cert_sound` defined as
`sound_certifier` at their meaning; the transfer ladder gone; one naming
convention for witnesses; every ledger row under five citations; the
statement diff over all built theories shows only deletions.
*First step.* `kernel_sound` (its consumers rewrite with `kernel_sound_def`,
so keep that name as the derived equation). *Size.* Two days, quiet tree
required.

### R4. The relational tower

*Why.* The plant is now a relation (`relSystem`, `relEnvelope`,
`relViability`, `liberty/relTransparency`) with the deterministic theory an
instance, but the composed crowns (`integration/`), spec negotiation,
amendment and corrigibility are still stated deterministically.
*Done.* `svenvs_tower_*` crowns over `stepr`, with the deterministic crowns
as `_from_rel` corollaries; a disturbance-robust cartpole that still
EVALs; corrigibility's non-lock-in under an adversarial environment.
*First step.* `specneg` over relations (its keystone
`invariant_transports_to_meta` is plant-generic; check). *Size.* A week.

### R5. The witness construction

*Why.* The one open item. No principle is assumed any more: a Candle
derivation of a term that faithfully encodes "K′ is sound" makes K′ sound
by theorem (`kernel/kernelUpgradeScript.sml : witness_suffices`), and
having such a witness is equivalent to soundness
(`soundness_witness_iff_sound`), so the content is the certificate's
provenance: for a strictly stronger K′ it must come from the
hol-reflection/LCA construction, not from already knowing K′ sound.
*Done.* `soundness_witness mem K'` exhibited for a K′ ≠ `candle_kernel`,
with the `encodes_soundness` certificate produced by the reflection
translator over the LCA model (`kernel/loebReduction/loebReductionScript.sml :
lca_encodes_soundness` is the shape) and the derivation echoed by the kernel.
*First step.* Build `hol-reflection/lca` on a box with a memory cap and an
overnight budget (the `lcaProof` construction is tens of GB and about ten
CPU-hours per prerequisite theory); then instantiate `lca_reflects_soundness`.
*Size.* Unknown; it is the diagnosed wall. Do not start it on a shared box.

### R6. Closing Layer B and the self-upgradable root

*Why.* The altered compiler with the new BVL pass runs and self-hosts, and
the self-upgradable root builds and compiles programs, but the
whole-pipeline `compile_correct` re-composition is one FFI-trace subgoal
short (`compilerOpt/LAYERB.md`) and the root's interactive `--repl` is
blocked by the candle package's Eval runtime (`selfUpgrade/SELFUPGRADE_ROOT.md`).
*Done.* `compile_correct` for the altered pipeline, and a `cake` binary that
upgrades its own eval-compiler interactively.
*First step.* The FFI-trace subgoal; it is stated precisely in LAYERB.md.
*Size.* Weeks; CakeML backend expertise.

### R7. Generated obligations for the closed loop

*Why.* `agent/closedloop/obligation_template.ml` and `hotswap_template.ml`
are hand-mirrored HOL Light of the HOL4 definitions (TRUSTED-GLUE). The
reflectsem exporter now prints HOL Light from HOL4 defining theorems.
*Done.* The templates generated by `reflectsem/exportLib.sml` from
`agent/toolAgentScript.sml`, and `encFaithScript.sml`'s faithfulness
theorem covering the generated text, so the transcription seam disappears.
*First step.* Run the exporter on `tool_pol_def` and diff against the
template. *Size.* Days.

### R8. The long axes

PureCake as the inhabitant's verified language (`pure/`, `pureverified/`,
currently not buildable in the standard setup) and verified inference at
scale (`inference/`, explicitly toy). Research, not engineering; state
scope exactly, as `CLAIMS.md` §8 does.

**Our ranking.** R2 first: cheap, and it protects everything else. Then R1,
because it is the point. R3 whenever the tree is quiet. R4 when someone
wants the adversarial story in the crowns. R5 only with a dedicated box and
patience. R6 and R7 are self-contained and can be taken independently.

## 6. Repository hygiene (the audit, systematized)

This project was audited once from the outside; the findings were real and
none were malicious. The principles below are what they generalized to, and
`scripts/hygiene-audit.sh [repo]` is the mechanical first pass (it only
reads; HARD findings exit non-zero, soft ones are for judgment). Run it on
any repository before trusting a green badge.

1. **Pin by content, verify at use.** Every upstream, including each GitHub
   Action, each toolchain checkout and each downloaded artifact, is pinned by
   a full commit SHA or a content hash, never a tag or a short id; the pin is
   compared verbatim where it is used (`git rev-parse HEAD`, `sha256sum -c`).
2. **PR code is adversarial input to CI.** No `pull_request_target`; explicit
   least-privilege `permissions:`; caches restored on any event but saved
   only from trusted refs; no secrets reachable from a pull-request run.
3. **A committed artifact is re-derived, or it is not committed.** Never
   tracked and ignored at once; if the build regenerates it, CI regenerates
   it and `git diff --exit-code`s it.
4. **Nothing baked to a machine.** Hosts, users, key paths and home layouts
   come from documented environment variables, with a loud degraded path
   when unset. Anything that must edit a checkout outside the repo is
   opt-in, refuses a dirty tree, restores on exit and offers undo.
5. **Own your processes and your scratch.** Never `pkill -f <pattern>`
   (it kills other users' processes and your own ssh session); track what
   you start by pid or process group and stop only that. No fixed
   world-shared `/tmp` names; one per-user directory under `TMPDIR`.
6. **Docs that carry claims are code.** If a checker reads a document, CI
   must not `paths-ignore` it.
7. **Gates scan code, not prose.** Strip comments before matching; an
   allow-list of phrasings is a bug waiting for the next phrasing.
8. **State reproducibility honestly.** Say which bytes are deterministic
   (a verified compiler's output) and which depend on the host toolchain (a
   linked ELF), and hash the former.
9. **No secrets, no clutter.** Scan for key material; keep drafts, papers
   and scratch out of the tree or ignore them deliberately.
10. **The commit says which gate ran.** A change that could not be verified
    says so in its message.

## 7. Housekeeping

- `candle/ouroboros_logic.ml` is a superseded side-embedding draft and can
  be deleted.
- `realembedded/` should be retired or its certificate step made to
  terminate; it is cited nowhere and built by no script.
- Keep `scripts/INSTALL.md`, `scripts/env.sh` and `verify.yml` pins in
  lockstep; bumping any pin invalidates the CI cache by design.
