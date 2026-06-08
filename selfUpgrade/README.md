# selfUpgrade — toward a self-upgradable CakeML compiler

Goal: the compiler the *running* `cake` uses is a gated, swappable cell, so the
system upgrades its own compiler **in place** (heap intact), repeatedly, each
upgrade carrying a proof — not a one-time source patch + re-bootstrap.

CakeML's eval mechanism is parametric over a compiler instance `ci`
(`source_evalProof`: `mk_compiler_fun_from_ci ci`, `mk_init_eval_state ci`;
`backendProof.source_eval_to_flat_semantics` is parametric over the eval-config
`SOME ci`). The obstacle to *in-place* upgrade: `s_rel`/`recorded_orac_wf` pin
**one** `ci` across the whole oracle history, so a mid-run swap mixes
`ci`/`ci'` entries and no single `ci` is well-formed.

## B — built here (`evalUpgradeBScript.sml`)

Generalises the oracle wellformedness invariant from one global compiler to a
**per-generation compiler map** and proves the swap is sound at that invariant:

- `recorded_orac_wf_gen g2c gen orac` — each recorded oracle entry wf for *its
  generation's* compiler `g2c (gen j)`.
- `recorded_orac_wf_gen_const` — collapses to the original `recorded_orac_wf`
  when the map is constant (so this strictly generalises the existing invariant).
- `gen_set_from` — the in-place swap on the generation→compiler map.
- **`swap_preserves_recorded_orac_wf_gen`** — the load-bearing fact: from the
  generalised invariant before the swap, it holds after installing a new
  compiler for generations ≥ n; prior generations keep their own compiler
  (`gen_set_from_below`), the new generation uses the new one
  (`new_generation_uses_newc`).

Builds against the prebuilt `source_evalProof` (no backendProof dependency), so
it isolates the genuinely-new content. (Tier-2; needs the CakeML candle/backend
chain — built on persvati.)

## A — reset model (corollary; statement in `RESET_MODEL.md`)

`eval_upgrade ci' s = add_eval_state (SOME ci') s` — re-init the eval state to
`mk_init_eval_state ci'` (refs/ffi preserved, eval-env history reset).
`eval_upgrade_preserves_semantics` is then a specialisation of
`backendProof.source_eval_to_flat_semantics` at `ev := SOME ci'` (proof:
`rw[eval_upgrade_def] \\ irule source_eval_to_flat_semantics \\ …`). It builds
against a built `backendProof`; it is not in `selfUpgrade`'s default build to
keep this dir dependency-light. Meaning: upgrading to any well-formed `ci'`
keeps eval sound — for the *reset* (checkpoint-restart) model, for free from
parametricity.

## End-to-end (`selfUpgradeEndToEndScript.sml`)

Generalises `s_rel` to `s_rel_gen` (a per-generation compiler map) and composes
the step + swap into the keystone:

- `s_rel_gen` / `s_rel_gen_const` — the per-generation generalisation of `s_rel`,
  collapsing to `s_rel ci` when the map is constant (strict generalisation).
- `s_rel_gen_step` — within a generation, `evaluate_decs` simulates and
  re-establishes `s_rel_gen` (reduces to the existing `eval_simulation`).
- `s_rel_gen_swap` — installing a new compiler for a fresh generation keeps
  `s_rel_gen` (via `swap_preserves_recorded_orac_wf_gen`).
- **`selfupgrade_eval_simulation_step`** — the keystone: a swap to `ci'` at a
  fresh generation followed by `evaluate_decs` preserves `s_rel_gen` end to end
  and preserves the observable result relation.
- `selfupgrade_collapses_to_eval_simulation` — conservativity (no-swap recovers
  the original guarantee); `selfupgrade_no_new_typeerror` — no new type error.

Structural finding: in real `EvalDecs`, `dec_s.compiler` is one fixed function and
`add_decs_generation` bumps the generation without touching it — so a swap lives
at the level of the oracle *history* invariant (`recorded_orac_wf_gen`), exactly
the altitude these theorems work at.

## Multi-swap lift (`selfUpgradeMultiSwapScript.sml`)

Iterates the one-generation keystone into a run over **arbitrarily many**
in-place compiler swaps, by induction on a swap *schedule* (a list of steps,
each `(n, ci', gen, decs, env, env')`).

- `multi_run_src` / `multi_run_tgt` thread `evaluate_decs` through the segments
  on the source and oracle sides (short-circuiting on a non-`Rval`, as
  `evaluate_decs` itself does).
- `multi_swap_chain` is the per-step gate proposition asserted at every *live*
  state reached: `keystone_pre` (post-swap `s_rel ci'`, shared history wf for
  the old running map, swap point past all recorded generations, fresh
  generation governed by `ci'`), the segment env-relation, and no segment
  type-errors.
- **`selfupgrade_multi_swap_simulation`** — from `s_rel_gen` in and a valid
  `multi_swap_chain`, the whole N-swap run preserves `s_rel_gen` to the
  fully-swapped compiler map (`apply_full_swaps`) at the last active compiler
  (`last_ci`) on the success spine, and preserves the observable `result_rel`
  of the final segment (a runtime exception just short-circuits, result still
  related). Proved by induction on the schedule, applying the keystone
  (`selfupgrade_chain_step`) at each step.
- **`selfupgrade_oracle_semantics_prog_collapse`** — the conservative
  whole-program lift: when the per-generation map is pinned to one `ci` (the
  only thing the *unmodified* `EvalDecs` semantics can carry, since it has one
  `s.compiler`), the generalised invariant collapses to `s_rel ci`, so
  `oracle_semantics_prog` applies verbatim. The PART 2 NOTE records the exact
  remaining goal for a *strictly* multi-compiler `semantics_prog` — it needs a
  per-generation meta-compiler `do_eval`, a change to CakeML semantics we do
  not make; the genuinely multi-compiler content lives at the `evaluate_decs`
  level, where the simulation closes it for arbitrarily many swaps.

Constant-map conservativity is the `g2c := K (mk_compiler_fun_from_ci ci)`
instance of the simulation (no separate lemma — see the file comment).
All `DISK_THM`, no oracles/axioms. (Tier-2; built on persvati.)

## Remaining for the full running self-upgrade

1. **Implement+expose:** the running binary's eval is `EvalDecs` with the
   compiler pinned and the `Install` op handled *inside* `cake.S` (no FFI seam).
   A real in-place swap needs a new core eval op (`do_eval_upgrade`, replacing
   `eval_state.compiler`) whose correctness is the keystone above — a core
   semantics change that re-proves the compiler, exposed via the `Repl` module.
2. **Re-bootstrap** a root that carries the op.
