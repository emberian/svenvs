# PureLang as the svenvs inhabitant's verified language

> Scope: design + a *light* abstract HOL4 sketch (`pureInhabitantScript.sml`).
> No PureCake / CakeML / hol-reflection is built here. We cite real
> definitions from `~/dev/pure` and state the integration as an
> axiomatised abstract signature so the build is seconds-fast and
> cheat-free, while pinning down *exactly* where the heavy verified
> artifacts attach.

## 0. The question

svenvs proves a generic `safety/safety_preservation`:

```
init_safe init safe ∧ sound_policy step safe pol ∧ safe_shield step safe shield ⇒
  ∀ctrl. invariant step init (enveloped pol shield ctrl) safe
```

The controller `ctrl : 's -> 'a` is an *opaque, universally quantified*
selector — never inspected, never executed. The thesis of this note:
**the inhabitant — the AI living in the Place — should be a PureLang
program, and "the controller" is the denotation of that program under
PureCake's formal semantics.** Because `safety_preservation` quantifies
over *all* `ctrl`, *any* PureLang program is automatically enveloped-safe;
the verified-compiler chain then carries that guarantee down to the CakeML
runtime that Candle itself executes on. The integration is therefore not a
new proof — it is an *instantiation* of the generic core, plus an argument
that the realisation path is end-to-end verified.

## 1. Why PureLang (not gexpr, not bare HOL)

`cartpoleProgramScript`'s `gexpr`/`geval` is, per the project's own
`DESIGN.md` and the `svenvs-real-embedding-plan` memory, a **spec
skeleton**: a bespoke mini-language in *meta* HOL4 with a hand-written
evaluator. It exercises the proof-carrying control structure but is *not*
the artifact and must not be extended.

PureLang is the natural real inhabitant language because:

- It is a **real, Haskell-like, lazy functional language** with a
  **formal HOL4 semantics** already developed (`~/dev/pure/language/`),
  not a re-embedding we maintain.
- It has a **verified compiler to CakeML** (`~/dev/pure/compiler/`,
  `pure_to_cake_correct`), and CakeML is the verified runtime the Candle
  prover executes on (see memory `hol-reflection-build-chain`,
  `candle-arm64-macos-feasible`). So a PureLang inhabitant has a
  *machine-checked* path from source to the very machine running the
  self-verifying kernel.
- Its observable behaviour is an **interaction tree** over FFI/`Act`
  effects (`pure_semantics$itree_of`), which is exactly the right shape
  for "a reactive agent that reads state and emits actions" — i.e. an
  svenvs `selector`.

## 2. Real PureLang definitions this design rests on

All from `~/dev/pure/language/` unless noted.

- **Syntax** — `pure_expScript.sml`:
  - `Type vname = “:string”`
  - `Datatype: exp = Var vname | Prim op (exp list) | App exp exp |
    Lam vname exp | Letrec ((vname # exp) list) exp`
  - `Datatype: op = If | Cons string | IsEq string num bool |
    Proj string num | AtomOp atom_op | Seq`
  - `Definition closed_def: closed e ⇔ freevars e = {}`
  - `Definition letrecs_distinct_def` (a well-formedness side-condition
    used by the compiler-correctness theorem).
- **Semantics** — `pure_semanticsScript.sml`:
  - `Type state[pp] = “:(exp list) list”` (the *PureLang* heap/store —
    distinct from the svenvs abstract `'s`).
  - `Datatype: cont = Done | BC exp cont | HC exp cont`
  - `Datatype: result = Termination | Error | FinalFFI (string#string) final_ffi`
  - `Definition next_def` / `Definition next_action_def` — the small-step
    driver producing `next_res = Act 'e cont state | Ret | Div | Err`.
  - `Definition interp` / `Theorem interp_def` — unfolds `next_action`
    into a coinductive **interaction tree** (`Vis`/`Ret`/`Div`) whose
    `Vis` nodes are exactly the program's FFI *actions*, each resumed by
    an environment-supplied response string.
  - `Definition semantics_def: semantics e stack state = interp (eval_wh e) stack state`
  - `Definition itree_of_def: itree_of e = semantics e Done []` — the
    canonical denotation of a closed program: its full I/O itree.
  - `CoInductive safe_itree` — the "this program never goes wrong"
    predicate (`Ret Termination` / `Ret (FinalFFI …)` / `Div` / well-fed
    `Vis`); it is the precondition of compiler correctness.
- **Verified compilation** — `~/dev/pure/compiler/`:
  - `pure_compilerScript.sml`: `Definition compile_def` (concrete syntax
    → CakeML AST string), `compile_to_ast`.
  - `compiler/backend/passes/proofs/pure_to_cakeProofScript.sml`:
    `Theorem pure_to_cake_correct` — given `cexp_wf x`,
    `closed (exp_of x)`, `NestedCase_free x`,
    `safe_itree (itree_of (exp_of x))`, `letrecs_distinct (exp_of x)`
    and namespace side-conditions,
    `itree_rel (itree_of (exp_of x))
       (itree_semantics$itree_semantics (pure_to_cake c ns x))` and the
    target itree is itself `safe_itree`. **This is the verified arc's
    backbone**: PureLang `itree_of` semantics is preserved by compilation
    into CakeML's itree semantics.

## 3. From a PureLang program to an svenvs `ctrl`

svenvs is parametric over opaque `'s` (world state) and `'a` (action).
The Place fixes a *protocol*: at each tick the inhabitant is handed an
encoding of the world state and must emit an action. PureLang's effectful
behaviour is exactly an itree of `Act` nodes, so the denotation is:

> **`agent_of (p : exp) : 's -> 'a`** — the selector that, at world
> state `s`, drives `itree_of p` (the program's `pure_semantics`
> interaction tree) under a deterministic *world coupling*: the encoding
> `enc s : string` is supplied as the FFI response to the program's
> first observable `Act`, and the string the program emits there is
> decoded `dec : string -> 'a` into the svenvs action. Concretely
> `agent_of p s = dec (first_act (itree_of p) (enc s))`, total by
> defaulting a divergent/erroring/silent itree to a fixed `null_act`.

Three honest remarks, all reflected in the sketch's abstract signature:

1. `agent_of` is a *total* `'s -> 'a` because svenvs selectors are total.
   Non-termination / `Error` / a program that never does an `Act` all
   collapse to `null_act`. This is sound: the envelope treats `ctrl s`
   as a black-box proposal and the *policy* gates it. A misbehaving
   inhabitant can at worst propose `null_act`, which the shield/policy
   still filters.
2. The interesting agents are *stateful/reactive*; the single-shot
   `first_act` reading is the minimal faithful slice for the integration
   theorem. The full design threads the itree across ticks (the world
   coupling is a relation between the `(state, cont)` resumption of
   `interp` and the next svenvs `step`); the abstract `denote` in the
   sketch is exactly the place that full coupling slots into without
   changing any safety proof, because safety quantifies over *all* `ctrl`.
3. Nothing about safety depends on *how* `agent_of` is defined. That is
   the whole point of the opaque-controller decomposition: the integration
   theorem is `safety_preservation` instantiated at
   `ctrl := agent_of p`, for an arbitrary `p`.

## 4. The admission obligation, stated over `pure_semantics`

svenvs self-improvement (`upgradeScript`) gates *policy* proposals, not
controllers. A PureLang inhabitant participates in self-improvement by
*emitting a proposed policy* (the same `'s -> 'a -> bool` object the core
already reasons about) and a machine-checkable proof obligation. Stated
over real PureLang semantics, the obligation a self-proposed PureLang
policy program `q : exp` must discharge is:

```
admissible step safe oldp (pol_of q)
  ⇔  sound_policy step safe (pol_of q) ∧ weaker (pol_of q) oldp
```

where `pol_of q` is the policy denoted by running `q` as a *pure decision
procedure*: `pol_of q s a ⇔ itree_of (q applied to enc(s,a))` converges to
the constructor `True`. The *well-behavedness* premise that makes this a
legitimate denotation — and the same premise the verified compiler needs —
is precisely `safe_itree (itree_of (exp_of q)) ∧ letrecs_distinct …
∧ closed …`. So the PureLang admission obligation is:

- **safety-soundness** of `pol_of q` (`sound_policy`, an svenvs-core
  predicate) — the *semantic* content, identical to today's gate; plus
- **`safe_itree`/`closed`/`letrecs_distinct` well-formedness of `q`** —
  the *syntactic/operational* content, which is *exactly* the hypothesis
  set of `pure_to_cakeProof$pure_to_cake_correct`.

This is the key alignment: the proof a self-improving inhabitant must pay
to widen its own envelope is *the same proof obligation that licenses
compiling its policy code to the trusted CakeML runtime*. Discharging it
once buys both "still safe" (`admit_keeps_sound`,
`self_improvement_is_safe`) and "faithfully runnable on the Candle
machine" (`pure_to_cake_correct`).

## 5. End-to-end verified arc

```
 PureLang source  ── pure_compiler$compile ──▶  CakeML AST/string
   (exp / cexp)                                       │
       │  pure_semantics$itree_of                      │ CakeML
       │  (denotation = the agent's I/O itree)         │ semantics
       ▼                                               ▼
  agent_of p : 's -> 'a  ───────────▶  itree_semantics$itree_semantics
       │  (svenvs ctrl)        pure_to_cake_correct:        │
       │                       itree_rel preserves it       │
       ▼                                                     ▼
  safety_preservation @ ctrl:=agent_of p          CakeML → (verified
  ⇒ ∀p. invariant step init                        backend, not built
        (enveloped pol shield (agent_of p)) safe    here) → machine
                                                     Candle runs on
```

Reading the arc:

1. **Source → denotation.** A PureLang inhabitant `p` denotes
   `itree_of (exp_of p)` (real `pure_semantics`), abstracted to an svenvs
   selector `agent_of p` (§3).
2. **Safety, free.** `safety_preservation` instantiated at
   `ctrl := agent_of p` gives, *for every well-formed `p`*, that the
   enveloped Place keeps `safe` invariant — no per-program proof. Safe
   self-improvement of the *policy* (with the §4 obligation) is the
   existing `upgrade$self_improvement_is_safe`, unchanged.
3. **Denotation → CakeML.** `pure_to_cake_correct` says the *same* itree
   (`itree_rel`) is produced by the compiled CakeML, and stays
   `safe_itree`. So the behaviour the safety argument talks about is the
   behaviour the verified compiler emits.
4. **CakeML → metal.** The CakeML verified backend (not built here; see
   memory `candle-arm64-macos-feasible`) carries the CakeML itree
   semantics to the actual machine — the same machine the Candle prover
   (which checks the inhabitant's self-improvement proofs) runs on.

Hence: a PureLang program is the inhabitant; its formal denotation is the
opaque svenvs controller; the envelope (proved, generic) keeps the Place
safe for *any* such program; and the verified PureCake → CakeML chain
makes "the program we proved about" be "the program that runs".

## 6. What is built here vs. what is gated

- **Built (this dir, light, cheat-free, seconds):**
  `pure/pureInhabitantScript.sml` — an *abstract signature* for PureLang:
  a type `pureprog`, an abstract denotation `denote : pureprog -> ('s,'a)
  selector`, an abstract `safe_program` well-formedness predicate
  (standing in for `safe_itree ∧ closed ∧ letrecs_distinct`), and the
  integration theorem `pure_inhabitant_safe` — **`safety_preservation`
  instantiated at `ctrl := denote p`, reusing the generic core verbatim
  (not reproved)**, plus `pure_inhabitant_self_improvement_safe`
  (analogously reusing `upgrade$self_improvement_is_safe`). These witness
  the integration *point* with no heavy dependency.
- **Gated (NOT built here, by hard rule):** replacing the abstract
  signature with the concrete `~/dev/pure` definitions
  (`exp`, `itree_of`, `safe_itree`, `pure_to_cake_correct`) — that is a
  heavy `INCLUDES` onto built PureCake + CakeML. The abstract theorem is
  designed so this swap changes *no svenvs proof*: only `denote`/
  `safe_program` get concrete definitions and `pure_to_cake_correct`
  is cited for step 5.3.

## 7. Feasibility verdict & next steps

**Verdict: feasible, and structurally clean.** The opaque-controller
decomposition means PureLang integration needs *zero* new safety
reasoning — it is one `irule safety_preservation`. The genuine work is
(a) PureCake/CakeML being built, and (b) defining the world-coupling
`agent_of` / `pol_of` and proving the *bridge* lemmas (single-shot, then
reactive). None of (a)/(b) touches the svenvs core.

Concrete next steps (in order):
1. Build PureCake (`~/dev/pure`) + CakeML once (heavy; out of scope here).
2. New dir with heavy `INCLUDES`: instantiate `pureprog := pure_exp$exp`,
   `safe_program p := closed (exp_of p) ∧ letrecs_distinct (exp_of p) ∧
   safe_itree (itree_of (exp_of p)) ∧ cexp_wf p ∧ NestedCase_free p`.
3. Define the world coupling `enc/dec/first_act`, define `agent_of`,
   discharge `pure_inhabitant_safe`'s concrete instance (still just
   `safety_preservation`).
4. Define `pol_of q` and prove the §4 obligation equivalence; connect to
   `upgrade$admissible` exactly as `cartpoleProgram` does for `gexpr`.
5. Cite `pure_to_cakeProof$pure_to_cake_correct` for the §5.3 leg; write
   the reactive (multi-tick) world-coupling and its bridge lemma.
6. (Layer 3, gated on hol-reflection/lca) tie the §4 proof obligation to
   *Candle-kernel-checked* provability so the inhabitant's self-upgrade
   proofs are validated by the verified prover running on the CakeML the
   PureLang inhabitant also compiles to — closing self-verification.
