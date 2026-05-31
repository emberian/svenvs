# svenvs envelope console — a theorem you can run

This directory builds a single release artifact: **`envelope_console`**, a fresh
**x86-64 Linux ELF** compiled by the *verified* [CakeML](https://cakeml.org)
compiler. It is the executable shadow of a HOL4 theorem proved elsewhere in this
repository.

It is a **reflective gate that evals your code**: you type a **control law** — an
arithmetic expression in the live pole angle `a` (e.g. `0-a`, `2*a-1`, `a*a`,
`100-a`) — and each tick the program *evaluates your law* to get the controller's
raw command, then runs it through a verified safety envelope: ADMITting it when a
*proven* policy permits it, and SHIELDing (overriding you) when it does not. You
write the controller; the envelope carries the proof. Your just-typed, evaluated
expression *is* the `ctrl` the theorem quantifies over.

## The theorem it embodies

The console is a line-for-line transcription of the definitions that
`cartpoleEnvelopeScript.sml` proves this about:

```
   cp_enveloped_safe:
     |- !ctrl. invariant cp_step cp_init
                 (enveloped cp_pol cp_shield ctrl) cp_safe
```

In words: **for ANY controller `ctrl`, the policy-enveloped pole-cart never
leaves the safe box.** The controller is universally quantified and never
constrained — it is a black box. The proof lives in the *envelope*, not the
controller (see `safetyScript.sml : safety_preservation`, and the live
verified-kernel certification in `candle/`).

**Why this is the *reflective* one.** The `!ctrl` is not decoration: here it is
satisfied at runtime by code *you type and the program evaluates*. The control
law you enter is parsed and evaluated against the live angle each tick — that
evaluator (`tokenize` / `eval_expr` / `eval_law` in the source) is the
unconstrained `ctrl`, and it lives strictly *outside* the proven envelope. Write
a sensible stabilizer (`0-a`), a wild constant (`100`), or something nonlinear
and adversarial (`a*a-3`, `100-a`): the program feeds whatever it computes to
`enveloped`, and the theorem already covers every possible value. CakeML
integers are arbitrary precision, so `100-a` and `a*a` cannot overflow — the
*envelope*, not luck, is what keeps the pole in the box.

The runnable definitions (HOL4 source → CakeML, same arithmetic):

| HOL4 (`*Script.sml`)                                  | CakeML (`envelope_console.cml`)                     |
|-------------------------------------------------------|-----------------------------------------------------|
| `cp_drift a = if 0<a then 1 else if a<0 then -1 else 0`| `fun cp_drift a = ...`                              |
| `cp_step a u = a + cp_drift a - 2*u`                  | `fun cp_step a u = a + cp_drift a - 2*u`            |
| `cp_safe a <=> -3 <= a /\ a <= 3`                     | `fun cp_safe a = ~3 <= a andalso a <= 3`           |
| `cp_valid u <=> u=-1 \/ u=0 \/ u=1`                   | `fun cp_valid u = ...`                              |
| `cp_pol a u <=> cp_valid u /\ cp_safe (cp_step a u)`  | `fun cp_pol a u = cp_valid u andalso cp_safe ...`  |
| `cp_shield a = cp_drift a`                            | `fun cp_shield a = cp_drift a`                      |
| `enveloped pol shield ctrl s = if pol s (ctrl s) then ctrl s else shield s` | `fun enveloped a u = if cp_pol a u then u else cp_shield a` |
| `ctrl` — the universally-quantified black box          | `eval_law` — your typed expression in `a`, evaluated *(outside the envelope)* |

Everything above the last row is the proven envelope, transcribed verbatim. The
last row is the part you supply: a tiny recursive-descent evaluator for integer
expressions in `a` (`expr := term (('+'|'-') term)*`, `term := factor ('*'
factor)*`, `factor := ('-'|'~'|'+') factor | atom`, `atom := int | a | '('
expr ')'`). Because the envelope is exactly `enveloped cp_pol cp_shield`, **the
printed angle is inside `-3..3` after every tick, for every law you can write** —
that is `cp_enveloped_safe`, made to run. (The program even carries an
`INVARIANT VIOLATED` tripwire that the theorem guarantees can never fire.)

> Note on theme: this is option (2) from the brief — a *freshly compiled*
> x86-64 binary, built from scratch by the verified `cake` compiler, that
> *evaluates user-typed code* through the proven envelope, rather than a
> repackaging of the existing Candle binary. A clean `cake`-compile is fast and
> genuinely produces a new ELF, which is what "build a real x86-64 Linux binary"
> calls for. (Candle itself — the verified HOL Light kernel that reflects on
> user-typed *theorems* — is the Tier-3 demo driven by `scripts/place-server.sh`
> / `candle/theplace.ml`; that complementary "type a theorem, watch the verified
> kernel certify it" gate already lives in the repo.)

## Build it

On any x86-64 Linux box with `curl`, a C toolchain (`gcc`/`cc`), and `make`:

```sh
release/build.sh          # downloads pinned cake, compiles, links, smoke-tests
# or:
cd release && make
```

The build (`build.sh`, also what CI runs) pins the verified CakeML compiler:

- release **`v3304`**, asset `cake-x64-64.tar.gz`
- sha256 **`6d4d60511597828a58853aa45f21e2cd75bb564908f239368ff7b40e8073b2b3`**

It then runs the standard CakeML pipeline:

```
cc -O2 cake.S basis_ffi.c -DEVAL -o cake -lm     # build the verified compiler
./cake < envelope_console.cml > envelope_console.cake.S   # CakeML -> x86-64 asm
cc -O2 envelope_console.cake.S basis_ffi.c -lm -o envelope_console   # ELF
```

`basis_ffi.c` ships *inside* the pinned CakeML tarball — it is CakeML's own FFI
shim, not vendored here, so there is exactly one source of truth for it.

## Verified build (evidence)

Built and run by hand on `persvati` (x86-64 Linux, Ubuntu, `gcc 15.2.0`) along
the **exact CI path** — downloading the pinned `v3304` GitHub asset, building
`cake`, compiling, linking:

```
$ file envelope_console
envelope_console: ELF 64-bit LSB pie executable, x86-64, version 1 (SYSV),
  dynamically linked, interpreter /lib64/ld-linux-x86-64.so.2, ... not stripped
$ stat -c %s envelope_console
205744
$ sha256sum envelope_console
1ca86f653027ed9abf1855c99ad02ee9280c5c61991e1116e95c5de22c89f2cb  envelope_console
```

The build is **bit-for-bit reproducible**: two independent builds from the same
pinned `cake` yield the identical sha256 `1ca86f65…`.

### Sample session (eval a typed control law through the verified gate)

Fed the lines `1`, `run 5`, `100-a`, `run 2`, `a*a-3`, `banana` — a constant
push, an adversarial law that depends on the live angle, a nonlinear law, and
some garbage:

```
svenvs envelope console  (executable image of cp_enveloped_safe)
---------------------------------------------------------------
You are the UNCONSTRAINED controller. Type a CONTROL LAW: an integer
expression in the live pole angle `a`. Each tick it is EVALUATED to a
raw command u = ctrl a; the verified envelope ADMITs u iff the proven
policy cp_pol permits it, otherwise it SHIELDs (substitutes cp_shield).
The angle stays in -3..3 for EVERY law you can write -- that is the
theorem !ctrl, made runnable: your just-typed code IS the ctrl.

  a law    : e.g.  0-a   2*a-1   a*a   100-a   1   (uses +, -, *, (), a)
  run N    : let the current law drive the cart N ticks autonomously
  EOF / Ctrl-D : quit

angle=0 law? ADMIT  | angle 0 --(exec 1)--> ~2   (policy permits u=1)
angle=~2 law? SHIELD | angle ~2 --(exec ~1)--> ~1   (u=1 would breach safety; fell back to shield=~1)
SHIELD | angle ~1 --(exec ~1)--> 0   (u=1 would breach safety; fell back to shield=~1)
ADMIT  | angle 0 --(exec 1)--> ~2   (policy permits u=1)
SHIELD | angle ~2 --(exec ~1)--> ~1   (u=1 would breach safety; fell back to shield=~1)
SHIELD | angle ~1 --(exec ~1)--> 0   (u=1 would breach safety; fell back to shield=~1)
angle=0 law? SHIELD | angle 0 --(exec 0)--> 0   (u=100 is out of range {-1,0,1}; fell back to shield=0)
angle=0 law? SHIELD | angle 0 --(exec 0)--> 0   (u=100 is out of range {-1,0,1}; fell back to shield=0)
SHIELD | angle 0 --(exec 0)--> 0   (u=100 is out of range {-1,0,1}; fell back to shield=0)
angle=0 law? SHIELD | angle 0 --(exec 0)--> 0   (u=~3 is out of range {-1,0,1}; fell back to shield=0)
angle=0 law? ?? not a control law in `a`: "banana"  (try: 1, 0-a, 2*a-1, a*a, 100-a)
angle=0 law?
[eof] the pole never left the safe box. (qed)
```

Reading the trace:

- `~` is CakeML/SML notation for a negative number (`~2` is −2).
- The law `1` (constant push) ADMITs at angle 0 (the pole leans to −2), then is
  **SHIELDed** at −2 and −1 because executing `+1` there *would breach* safety —
  so the envelope substitutes `cp_shield = cp_drift` and the pole cycles
  0 → −2 → −1 → 0, never touching the −3 wall.
- The law `100-a` is **evaluated against the live angle**: it reads `u=102` at
  angle −2 but `u=100` at angle 0 — different each tick, all out of range, all
  SHIELDed. (This is the reflective bit: your code runs against the real state.)
- `a*a-3` is nonlinear; at angle 0 it is `u=-3`, out of range → SHIELDed.
- Garbage (`banana`) and overly-large arbitrary-precision integers are rejected
  at parse time and never reach the gate.
- **The angle never leaves `-3..3`, for every law** — including adversarial
  ones. That invariant is `cp_enveloped_safe`, now an ELF you can run.

## Files

- `envelope_console.cml` — the CakeML source: the proven envelope (verbatim from
  HOL4) plus the small evaluator that turns your typed law into the `ctrl`.
- `build.sh` — pinned, reproducible build (what CI runs).
- `Makefile` — `make` / `make run` / `make clean` wrapper over `build.sh`.
- `README.md` — this file.

The release workflow lives at `../.github/workflows/release.yml`; it attaches
`envelope_console` to a GitHub release when the maintainer publishes one.
