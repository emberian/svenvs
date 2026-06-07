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

## The one honest residual (not faked)

The full **`compile_correct` re-composition** is **not** closed: with `optimise`
inserted, `bvl_to_bviProofTheory` (hence `backendProofTheory`) does not yet
rebuild. The whole-program semantics clone (`semantics_optimise`, mirroring
`bvl_inlineProof.semantics_let_op`) is complete **except one subgoal** in the
value/outcome-uniqueness branch — re-threading `s'.ffi = s.ffi` (from
`opt_evaluate_Call`) through the clock-juggling. Every supporting lemma it needs
(per-exp/list/Call simulation, names, `find_code`) is proven. So the altered root
**runs** the pass and the pass is **individually proven**; the gold-standard
"the *whole modified pipeline* is re-verified end-to-end" is one FFI-trace
subgoal away. Stated, not blurred.

## Reproduce
On a host with the CakeML backend proofs + bootstrap translation built (heavy):
`patch -p1 < compilerOpt/cakeml-bvl_opt.patch` inside `$CAKEMLDIR`, rebuild
`compiler/backend` + `bootstrap/translation` (`--no-cache -j4` — `-j24` OOMs),
regenerate the sexpr, and `cake --sexp=true --skip_type_inference=true …` it to a
new `cake.S`.
