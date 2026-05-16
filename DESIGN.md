# Design notes

## Why this shape

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

## The three theorems

- `safety/safety_preservation` — `∀ctrl. invariant … safe`. Pure inductive
  invariant; the controller is free.
- `weakening/safe_weakening` — replacing a policy by any *weaker* (more
  permissive) policy that remains `sound_policy` keeps the **same** safety
  guarantee. This is "the system may loosen its own envelope" — the
  self-improvement direction, made safe by the soundness side-condition.
- `weakening/authority_monotone` — weakening never increases overrides; the
  controller strictly gains authority. Together with `safe_weakening` this is
  the precise sense in which self-improvement (more autonomy) and
  self-verification (retained safety) co-exist.

## Reflection / Candle tie-in

`reflection/reflectionDemoScript.sml` reflects `safety_prop` into Candle's
deeply-embedded HOL via `reflectionLib` (`term_to_deep`, `termsem_cert`,
`prop_to_loeb_hyp`). The endgame is a certificate that the safety
proposition is `True` under the set-theoretic semantics Candle's soundness
theorem connects to the running kernel — i.e. the envelope theorem is
checkable *by the verified prover about itself*. No large-cardinal axiom is
needed for this fragment (that is only required for the stronger
self-trust / reflection-of-provability results in hol-reflection/lca).

## What is the artifact vs. what is a spec skeleton

DELIBERATE LAYERING (decided 2026-05-15):

- `system`/`envelope`/`safety`/`weakening`/`upgrade` — **real and final**.
  Generic, parametric over the *policy object*; the proof-carrying
  self-improvement theorems (`admit`, `self_improvement_is_safe`) do not
  depend on how a policy is represented. These survive everything below.

- `cartpole*` incl. `cartpoleProgramScript` (`gexpr`/`geval`) — **a spec
  skeleton, NOT the artifact.** `gexpr` is a bespoke mini-language living in
  *meta* HOL4; it is a parallel embedding and re-implements syntax we
  already have deeply embedded in Candle. It exists only to exercise the
  control structure in something that builds today. It will be *replaced*
  (not extended) by the real version.

- THE REAL VERSION (pending): the typed-in program is a term of the
  *already deeply-embedded* HOL (`holSyntax` `Term` from
  `~/dev/CakeML/candle`); "eval" is `termsem` / the embedded proof system;
  the obligation is *embedded provability checked by the Candle kernel*
  (soundness: built `holSoundness` + `candle/prover`); reflection is
  `reflectionLib` (`term_to_deep`/`termsem_cert`). Gated on the
  hol-reflection L1 port for ergonomic automation.

- KERNEL SELF-UPGRADE (the top): replacing the guard-checker / proof kernel
  itself is admissible iff the current kernel checks a proof the new one is
  sound. Gödel/Löb ⇒ this needs the stratified reflection hierarchy =
  `hol-reflection/lca` (LCA / Vingean reflection). Layer 3; depends on L1.

Do NOT invest further in `gexpr`. Next real work is the embedded version
once L1 lands.

## Dependency status

`system/envelope/safety/weakening/upgrade` + `cartpole*`: plain HOL4,
proved, build standalone today (no `cheat`). `reflection/` and the real
embedded version: gated on the hol-reflection L1 port (in progress, agent).
Kernel self-upgrade: gated on hol-reflection/lca (Layer 3). See `~/.claude`
memory `hol-reflection-build-chain`, `svenvs-demo`,
`svenvs-real-embedding-plan` for state.
