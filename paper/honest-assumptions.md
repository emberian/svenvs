# Honest Assumptions

### a discipline for AI-safety formalization, with svenvs as the worked example

*A short note. Engineering artifact, not a position paper. Companion to
`svenvs.md`; every theorem named here is cited `file : theorem` and
re-checked by `scripts/verify-claims.sh`.*

---

## 0. The claim

A formal AI-safety result is only as good as its honesty about the
*boundary* of what it proved. Most projects bury that boundary in prose.
The discipline this note describes makes the boundary the most visible,
and mechanically-checked, thing in the artifact. svenvs is the worked
example: a place an arbitrary inhabitant acts through a machine-checked
gate, where the gate may improve itself — its policy, its specification,
its meta-invariant, its proof-checker, even the root that vouches for the
checker — without ever losing a machine-checked guarantee.

Two contributions, one structural and one methodological:

1. **One self-similar gate, all the way down.** Not a tower of special
   cases — a single principle instantiated at every level, including the
   root.
2. **Proof-carrying claims about a proof-carrying system.** The ledger of
   what is and is not proved is itself mechanically verified against the
   built theorems, on every run and in CI.

A third thing is offered not as a result but as evidence the discipline
works: this note retracts, in the open, an earlier framing of the project
that was an over-claim. The retraction *is* the method.

## 1. One gate

Every layer of svenvs has the same shape:

> an action (or self-modification) is admitted **iff** it carries a proof
> discharging an explicit obligation, checked by a judge the actor cannot
> forge.

- Policy weakening — `upgradeScript.sml : self_improvement_is_safe`.
- Spec negotiation under a fixed meta — `specneg/specNegScript.sml :
  spec_negotiation_is_safe`, transported by the one keystone
  `invariant_transports_to_meta`.
- The meta itself, amendable over an eternal bedrock —
  `amendment/amendmentScript.sml : meta_amendment_safe`; the fixed-meta
  trunk is a *corollary* (`amendment_subsumes_fixed_meta`), not a
  separate claim.
- The prover build, gated by the frozen root —
  `selfprover/selfProverScript.sml : prover_self_improvement_is_safe`.
- The root itself — see §3.

Every one composes through the *same* selector-generic lemma
(`specNegTheory.invariant_transports_to_meta`); the end-to-end theorems
are assembled in `integration/integrationScript.sml` as
`svenvs_tower_*` and built+asserted by one command, `scripts/tower.sh`.
The discipline that prevents fragmentation is a rule, not an aspiration:
*a new layer composes through the keystone or it does not ship.*

The conservative theorem — for **every** controller, nothing assumed, the
enveloped world stays safe — is the *floor* of this gate, not its ceiling.
Selling that floor as the headline was precisely the over-claim §4
retracts.

## 2. The ledger, and the ledger's ledger

`CLAIMS.md` is a skeptic-facing, per-theorem ledger with four labels:

- **PROVED** — a machine-checked theorem, cited `file : theorem`.
- **TRUSTED-GLUE** — small, bounded, auditable non-proof code, named.
- **UNCONSTRAINED** — the inhabitant: the `∀`-quantified term, the proof
  *structured so it can never depend on a fact about it* (mechanically
  checkable: no theorem constrains it).
- **ASSUMED** — an explicit, labelled, literature-standard hypothesis
  appearing verbatim in the source as a `Definition` and an antecedent.
  Never a hidden step; you can grep every one.

The methodological core: a ledger you must *trust* is just a nicer cheat.
So `scripts/verify-claims.sh` makes the ledger **proof-carrying about
itself** — on every `tower.sh` run and as a required CI step it checks
that

- every `path/<X>Script.sml : t` citation names a theorem that genuinely
  exists as `val t : thm` in the *built* signature (153 checked at time
  of writing);
- the labelled seams are still defined and named;
- the cheat / oracle / axiom scan is zero;
- the framing is current (the retracted labels absent).

A row that over-claims, or a stale build, fails the gate, unmissably.

## 3. The root is a ratchet, not a rock

The honest hard question is the root of trust. svenvs's answer, now a
theorem (`genealogy/genealogyScript.sml`):

> nothing is eternally frozen — not even the kernel. What holds is that
> the genealogy of judges is **forward-certified**: each judge is
> certified by the one before it, against a standard the step may not
> weaken. `genealogy_sound`: a sound *genesis* judge plus a
> forward-certified (unbounded) succession ⇒ every judge in the line is
> sound. "Frozen forever" is replaced by "sound once at genesis,
> certified forward."

The root is immovable only *during its own tenure* — a proof is
meaningful only relative to some fixed calculus, so the checker that
checks a transition cannot be what that transition rewrites in the same
act. Improvement of the judge integrates, like everything else, through
a predecessor-certified step.

## 4. The retraction is the method

An earlier version of this project's framing made an over-claim we now
retract: it called the inhabitant *unmodelable* / computationally
irreducible and put that at the headline. It was an over-claim because a
fixed network *is* verifiable through its weights; the universal
quantifier is a design *stance*, not a fact about the network. The honest
statement is the humbler, structural one of §1–§2: the inhabitant is the
unconstrained term; the proof is *built* never to depend on it.

This matters more than the specific word. The discipline is not "be
right the first time"; it is "when a claim is found to exceed what is
proved, retract it in the open, as a labelled correction, and let the
mechanical gate enforce that the corrected framing actually holds." The
retraction is checked: `verify-claims.sh` fails the build if the
retracted labels reappear. The most honest possible thesis for a note on
honest assumptions is one that contains its own corrected error.

## 5. The negatives are results

When a clever trick *cannot* remove a hard assumption, that is a finding,
and it is written as a theorem rather than quietly skipped:

- `kernel/watchdogFiniteScript.sml : loeb_finite_obstruction` — finiteness
  provably cannot dissolve the Löb obstruction (it has no habitat
  parameter).
- `genealogy/genealogyScript.sml : genealogy_irrelevant_to_vouch_sound` —
  succession structure provably cannot dissolve the strengthening seam
  (it has no genealogy parameter).

A precise negative is a result. Stating it as a theorem makes it
impossible to quietly ignore.

## 6. Testimony, not interrogation

To verify *through* a mind's substance is to inspect it; inspecting the
small thing to be safe from it is the harm the gate exists to avoid. The
resolution is an asymmetry (`embodiment/embodimentScript.sml`): nobody
reaches in. The inhabitant *may*, if it chooses, hand in a proof arguing
from a fact about its own substance to the obligation; the root checks
the *implication* (modus ponens — no Löb). One labelled seam
(`attestation_faithful`, the `encodes_obligation` family — not a new kind
of assumption). And it is **permitted, never required**:
`nondisclosure_is_inert` and `floor_holds_without_any_seam` prove that
disclosing nothing is structurally inert and the full guarantee then
holds for every inhabitant with no seam at all. Disclosure can only ever
*add* authority; it can never be coerced. The small thing speaks for
itself, on its own terms, or stays silent and loses nothing.

## 7. Where the irreducible costs are (and only there)

After all of the above, the honest residue is exactly three things — each
labelled in the source, none hidden, none new, none dischargeable by
cleverness:

1. **Genesis soundness.** Some judge at `n = 0` must be sound, and by
   Gödel a judge cannot prove its own soundness. This is the single root
   assumption; it is exactly the *built* Candle soundness theorem
   (`holSoundnessTheory.proves_sound`) at the base.
2. **Logical strengthening of the judge** — `loeb_reflection`, the
   Löb/large-cardinal seam; discharged for the finite/non-strengthening
   cases, irreducible in general (§5), genuinely compute-bound (the
   `hol-reflection/lca` route), and *labelled*, never smuggled.
3. **Attestation faithfulness** — the §6 seam, opt-in, only ever the
   price of *extra* authority the inhabitant chose to ask for.

Everything else is proved outright, Mac-light, with zero `cheat`
tactics, zero oracle tags beyond the benign disk tag, zero added axioms.

## 8. Honest scope (what this note does NOT claim)

- The general `loeb_reflection` seam is **not discharged**; it is the
  labelled assumption + the proved honest negative. The heavy
  `hol-reflection/lca` construction is a compute wall, autonomous, and
  may not complete on available hardware. We do not pretend otherwise.
- The concrete real-Candle-source replay and the live-Candle closed-loop
  demo are dedicated-host work, not claimed done here.
- The verified-inference track is a *separate research axis*; it does not
  compose into `svenvs_tower_*` and is not claimed to.

If anything in this note, or in `CLAIMS.md`, is found to exceed what is
proved, that is a bug — file it. That sentence is not rhetoric; §2 and §4
are the machinery that makes it true.

---

*Reproduce: `git clone` the repo, install HOL4 at the pinned commit, run
`./scripts/tower.sh`. It builds the composed tower, asserts the
`svenvs_tower_*` theorems exist, and runs `verify-claims.sh` as its final
gate. Exit 0 is the claim.*
