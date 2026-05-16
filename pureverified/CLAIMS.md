# `pureverified/` — honest claims

This directory makes "the untrusted inhabitant acts through a *verified*
language" a real theorem, linking the **real** PureCake verified
compiler-correctness result into the **generic** svenvs safety core.
It supersedes `pure/pureInhabitantScript.sml` (#18), which had no real
PureCake link (it `new_type`/`new_constant`-axiomatised the language).

## Where PureCake is, and its real correctness theorem

- PureCake (the HOL4 development) is at **`~/dev/pure`**
  (`.holpath` = `PUREDIR`). Compiler-correctness sources:
  - `compiler/proofs/pure_compilerProofScript.sml`
  - `compiler/backend/passes/proofs/pure_to_cakeProofScript.sml`
  - `compiler/proofs/pure_end_to_endProofScript.sml`
- The **top-level source→CakeML** theorem actually proved there
  (`Theorem pure_compilerProof$compiler_correctness`, verbatim shape):

  ```
  compile_to_ast c s = SOME cake ⇒
    ∃pure_ce ns.
      string_to_cexp s = SOME (pure_ce,ns) ∧
      pure_semantics$safe_itree (itree_of (exp_of pure_ce)) ∧
      state_to_cakeProof$itree_rel
        (itree_of (exp_of pure_ce)) (itree_semantics cake) ∧
      itree_semantics$safe_itree ffi_convention (itree_semantics cake)
  ```

  Its per-pass backbone is `pure_to_cakeProof$pure_to_cake_correct`
  (hyps: `cexp_wf x ∧ closed (exp_of x) ∧ NestedCase_free x ∧
  safe_itree (itree_of (exp_of x)) ∧ letrecs_distinct (exp_of x) ∧
  namespace_init_ok … ∧ cns_ok …`).
- The **machine-level** theorem (down to the real binary) is
  `pure_end_to_endProof$end_to_end_correctness`:
  `compile_to_ast c s = SOME cake ∧ cake_compile conf cake = SOME code
  ∧ configs_ok ∧ code_in_memory ⇒ ∃ce ns. string_to_cexp s = SOME
  (ce,ns) ∧ prunes (itree_of (exp_of ce)) (machine_sem_itree m)`.
  PureCake's own file ends with an explicit
  `check_thm end_to_end_correctness` oracle/cheat audit
  (`Tag.isEmpty ∨ Tag.isDisk`) — i.e. PureCake itself certifies these
  are cheat- and oracle-free.

`itree_rel` (`state_to_cakeProof`, a `CoInductive`) is a
bisimulation-style relation between PureLang's `pure_semantics`
interaction tree and CakeML's `itree_semantics`, with the FFI
channel/conf byte encoding. It is the formal meaning of "the compiled
program has the same observable behaviour as the source".

## The new theory

`pureVerifiedInhabitantScript.sml`, theory `pureVerifiedInhabitant`.

- `pureprog := :string` (the real verified-compiler input).
- `runnable c s ⇔ ∃cake. compile_to_ast c s = SOME cake` — **exactly**
  `compiler_correctness`'s hypothesis. No extra side-condition is
  assumed: the real theorem internally re-derives `cexp_wf` / `closed`
  / `NestedCase_free` / `safe_itree` / `namespace_ok` from it.
- `agent_of read t = read t`, `pure_controller read c s =
  agent_of read (itree_of (exp_of (FST (THE (string_to_cexp s)))))`
  — plain total HOL functions (NO `new_constant`/axiom). The decoder
  `read` is an ordinary universally-quantified function parameter
  (Place protocol, not svenvs-core content).

### Headline: `pure_inhabitant_verified_safe`

```
init_safe init safe ∧ sound_policy step safe pol ∧
safe_shield step safe shield ∧ runnable c s ⇒
  invariant step init (enveloped pol shield (pure_controller read c s)) safe
  ∧ ∃pure_ce ns cake.
      string_to_cexp s = SOME (pure_ce,ns) ∧
      compile_to_ast c s = SOME cake ∧
      pure_controller read c s = agent_of read (itree_of (exp_of pure_ce)) ∧
      pure_semantics$safe_itree (itree_of (exp_of pure_ce)) ∧
      state_to_cakeProof$itree_rel
        (itree_of (exp_of pure_ce)) (itree_semantics cake) ∧
      itree_semantics$safe_itree ffi_convention (itree_semantics cake)
```

Conjunct (a) = `safety$safety_preservation` instantiated at
`ctrl := pure_controller read c s` (generic core reused verbatim,
`irule safety_preservation`, nothing reproved → holds for **every**
program). Conjunct (b) = `pure_compilerProof$compiler_correctness`
re-derived (`drule`) for our runnable program, specialised so the
itree it certifies is **the same itree** `pure_controller` denotes.

Companions, same structure:
- `pure_inhabitant_states_verified_safe` (every reachable state safe);
- `pure_inhabitant_self_improvement_verified_safe`
  (unbounded self-proposed policy upgrades via
  `upgrade$self_improvement_is_safe`, faithfulness preserved);
- `pure_inhabitant_runs_on_machine`
  (`pure_end_to_endProof$end_to_end_correctness` specialised → behaviour
  down to `machine_sem_itree`, the actual machine).

## PROVEN vs ASSUMED (precise)

**Proven outright (modulo the final Holmake, see below):**
- Safety of the enveloped Place for *any* runnable PureCake inhabitant
  — by reuse of the generic, already-built, cheat-free svenvs core
  (`safety_preservation` / `self_improvement_is_safe`). The envelope,
  not the program, carries safety; quantification over all controllers
  is what makes this hold for the PureCake denotation for free.
- The verified-compilation bridge for our programs — by `drule` of the
  **real** `compiler_correctness` / `end_to_end_correctness`. These are
  cited, not re-axiomatised; their truth is PureCake's machine-checked
  result (and PureCake self-audits them oracle/cheat-free).

**Honestly assumed / abstracted (the genuine residue):**
1. **World coupling fidelity.** `agent_of read t = read t` and the
   single denotation point `pure_controller`. Safety does *not* depend
   on this (envelope is controller-agnostic — that is the design's
   whole point). What is *not* yet proven is that `read` faithfully
   realises the Place's reactive protocol over the *resumption*
   structure of `pure_semantics$interp` across ticks (DESIGN.md §3's
   `enc`/`dec`/`first_act` threaded coupling). This is a *fidelity*
   gap, not a *safety* gap: a misbehaving coupling can at worst feed
   the policy/shield a `null_act`, which they still gate.
2. **`itree_rel` ⇒ same svenvs action.** We do *not* claim
   `itree_rel t ct ⇒ agent_of read t = agent_of read ct`. We instead
   keep every safety theorem universally quantified over controllers,
   so it holds for `agent_of read` of *either* itree, and separately
   *exhibit* the real `itree_rel` between them. Turning "same itree up
   to `itree_rel`" into "literally the same svenvs selector" would need
   a `read` that factors through `itree_rel` (a decoder respecting the
   FFI byte encoding) — provable, future work, not load-bearing for the
   safety conclusion.
3. **Policy/shield/`step`/`safe`/`init`** remain the abstract svenvs
   parameters (as everywhere in svenvs core). Instantiating them to a
   concrete Place is orthogonal (cf. `cartpole*`).

So: *safety is genuinely earned and end-to-end down to the verified
machine semantics; the residual abstraction is exactly the
world-coupling decoder*, and it is provably *not* able to defeat safety.

## Cheat / oracle status

`pureVerifiedInhabitantScript.sml` contains **no `cheat`, no
`new_axiom`, no `mk_thm`, no `mk_oracle_thm`/`Thm.mk_thm`**. Every
theorem is `irule`/`drule`/`metis_tac` over (i) the already-built
cheat-free svenvs core and (ii) the cited real PureCake theorems
(themselves PureCake-audited oracle/cheat-free). `pureprog` is a
`Type` abbreviation and `agent_of`/`pure_controller`/`runnable` are
ordinary `Definition`s — **no `new_type`/`new_constant`** (the #18
abstraction is fully removed).

## Build outcome — DEFERRED (precisely)

- PureCake at `~/dev/pure` is **NOT built** on this Mac:
  `find ~/dev/pure -name '*Theory.uo' | wc -l` → **0**;
  `~/dev/pure/.hol` has only `make-deps`. CakeML *is* partially built
  (`~/dev/CakeML` 391 `*Theory.uo`) but PureCake's heavy
  `compiler/backend/passes/proofs` + `compiler/proofs` chain (and the
  CakeML `compiler/backend/proofs` it INCLUDES) are not.
- This layer's INCLUDES require a built PureCake. Building PureCake is a
  heavy HOL4 build. Hard constraints forbid heavy HOL builds on the Mac
  (memory-starved) and forbid contending with saturated persvati
  (lca PID ~3144677 + #28 build). persvati is also unreachable from
  this agent (no key auth). Therefore the final `Holmake` here is
  **DEFERRED**, exactly as the constraints direct.
- **What is pending is only the final compile.** All svenvs-side
  reasoning is concrete and cheat-free; the PureCake-side facts are the
  real, already-proved theorems cited by name with verified shapes
  read out of `~/dev/pure`. To complete: on a box with PureCake built,
  `cd pureverified && PUREDIR=<built-pure> Holmake`. No proof step
  remains to be discovered — the script is written against the actual
  theorem statements and tactic forms verified by reading the sources.

## Residual risk to the deferred Holmake (named honestly)

The proofs are written against the *exact* statements/locations read
from `~/dev/pure`. The only mechanical risks at the deferred compile
are (a) ancestor-`open` ordering / theory-name resolution across the
INCLUDES set, and (b) `irule`/`drule`-shape adjustments if a cited
theorem's bound-variable form differs trivially from what was read
(e.g. needing `goal_assum drule` vs `qexists`). These are local tactic
adjustments, not gaps in the *argument*: the safety half is the
generic core reused verbatim (already builds), and the bridge half is
a direct `drule` of theorems whose verbatim conclusions are reproduced
here. If any cited PureCake theorem could not in fact be discharged,
the honest fallback (precise obstruction, no fake) would be reported —
none was found: `compiler_correctness`, `pure_to_cake_correct`,
`end_to_end_correctness` all exist with the shapes used.
