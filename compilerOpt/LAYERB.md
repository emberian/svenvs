# Layer B — the compiler swaps itself for a proven-better one (executed)

`compilerOpt/` proves a new BVL optimization (`optimise`) semantics-preserving
against the real `bvlSem$evaluate`. **Layer B bakes that pass into CakeML's own
compiler and bootstraps an altered root `cake.S` that carries it** — so the
verified compiler, recompiled by itself, now contains a new verified
optimization, and reproduces its own successor.

## What is executed (verified on persvati)

`compilerOpt/cakeml-bvl_opt.patch` (against CakeML pin `ac654a0a3`) adds:
- `compiler/backend/bvl_optScript.sml` — `optimise_one`/`optimise_list`
  (empty-`Let` elimination, cv-translator-friendly mutual recursion);
- `compiler/backend/proofs/bvl_optProofScript.sml` — **`optimise_correct`**
  (full `recInduct evaluate_ind` congruence vs real `bvlSem$evaluate`),
  `let_nil_correct`, the install-oracle simulation `evaluate_optimise`,
  `optimise_prog_names`/`MAP_FST_optimise_prog`. All `DISK_THM`-clean
  (`oracles=DISK_THM, naxioms=0`; no `cheat`/`mk_thm`/`new_axiom`);
- the integration edits: `bvl_to_bvi$compile_def` applies `optimise_prog` as a
  pre-pass; `backend_passes` mirrors it (`number_of_passes` 39→40);
  `to_data_cv` registers it for cv-translation.

Then the bootstrap is re-run (translate → sexpr → `cake`):
- **`cake-altered`** — the new compiler, compiled by the existing verified `cake`;
- it **runs** (compiles + links + executes a program), **self-hosts** (compiles
  its own sexpr; the self-compiled `.S` is *smaller* — the altered compiler
  optimises its own code), and **the pass demonstrably fires**:
  `EVAL ⊢ optimise_one (Let [] (Var 3)) = Var 3`, and a program whose
  compilation yields an empty `Let` builds to a *smaller* `.S` with *identical*
  output under altered-vs-stock `cake`.

So the apex-worthy move — *the compiler carrying a new verified pass, bootstrapped
into a self-reproducing altered root* — is **executed**.

## Whole-program FFI-trace & Install-oracle preservation (100% closed)

Both in `compilerOpt/compilerOptScript.sml` (checked on every Tier-2.5 `Holmake`
run without needing to patch `$CAKEMLDIR` in place) and in
`compilerOpt/cakeml-bvl_opt.patch` (`bvl_optProofScript.sml`), the whole-program
observational semantics theorems are **100% proved in HOL4 with zero `cheat`s**:
- `evaluate_optimise` — code-table and `Install` compile-oracle forward
  simulation (`opt_state_rel`), preserving clocks (`t2.clock = s.clock`) and FFI
  state (`t2.ffi = s.ffi`);
- `opt_evaluate_Call` and `opt_evaluate_Call_no_Fail` — per-`Call` lifting under
  `initial_state` at identical clock `k`, yielding exact result and FFI-state
  equality at every fuel value `k`;
- **`semantics_optimise`** and **`optimise_prog_semantics`** — full
  whole-program `bvlSem$semantics` preservation (`Terminate outcome io_events`
  and `Diverge (build_lprefix_lub ...)`), proved cleanly via extensional
  equality of the per-clock `evaluate` outcomes (`AP_TERM_TAC` on `some res. ...`
  and `IMAGE`).

## Reproduce
On a host with the CakeML backend proofs + bootstrap translation built (heavy):
`patch -p1 < compilerOpt/cakeml-bvl_opt.patch` inside `$CAKEMLDIR`, rebuild
`compiler/backend` + `bootstrap/translation` (`--no-cache -j4` — `-j24` OOMs),
regenerate the sexpr, and `cake --sexp=true --skip_type_inference=true …` it to a
new `cake.S`.
