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

## Remaining for full in-place upgrade

Generalise `s_rel` to carry the per-generation compiler map (instead of one
pinned `ci`) and re-derive the `do_eval`/`evaluate_decs` simulation lemmas in
`source_evalProof` against it (reusing `es_forward`/`es_stack_forward`), then
discharge the swap's side-condition (recorded entries predate the bumped
generation) from the generation-counter monotonicity in `es_forward`. The
preservation lemma above is the new fact that work threads through; plus the
runtime: exposing the swap in the verified `Repl` and re-bootstrapping a root
that has it.
