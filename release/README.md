# svenvs envelope console — a theorem you can run

This directory builds a single release artifact: **`envelope_console`**, a fresh
**x86-64 Linux ELF** compiled by the *verified* [CakeML](https://cakeml.org)
compiler. It is the executable shadow of a HOL4 theorem proved elsewhere in this
repository.

It is a **reflective gate**: it reads your input, runs it through a verified
safety envelope, and reacts — ADMITting your command when a *proven* policy
permits it, and SHIELDing (overriding you) when it does not. You are the
unconstrained controller; the envelope is what carries the proof.

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

You type the `ctrl` choice; everything else is the proven envelope. Because the
envelope is exactly `enveloped cp_pol cp_shield`, **the printed angle is inside
`-3..3` after every single line you type — that is `cp_enveloped_safe`, made to
run.** (The program even carries an `INVARIANT VIOLATED` tripwire that the
theorem guarantees can never fire.)

> Note on theme: this is option (2) from the brief — a *freshly compiled*
> x86-64 binary, built from scratch by the verified `cake` compiler, rather than
> a repackaging of the existing Candle binary. It was chosen because a clean
> `cake`-compile is fast and genuinely produces a new ELF, which is what "build a
> real x86-64 Linux binary" calls for. (Candle itself — the verified HOL Light
> kernel that reflects on user-typed *theorems* — is the Tier-3 demo driven by
> `scripts/place-server.sh` / `candle/theplace.ml`; that complementary "type a
> theorem, watch the verified kernel certify it" gate already lives in the repo.)

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
190520
$ sha256sum envelope_console
d3e957bd20c034fdd3608aeb1a9aac1ef5d6287645e679a6223f0aa95b1615d2  envelope_console
```

The build is **bit-for-bit reproducible**: recompiling from the same pinned
`cake` yields the identical sha256 `d3e957bd…`.

### Sample session (eval user input through the verified gate)

Fed the line sequence `0, 1, 1, -1, 5, -1, -1, -1, banana, 0`:

```
svenvs envelope console  (executable image of cp_enveloped_safe)
---------------------------------------------------------------
You are the UNCONSTRAINED controller. Type a command u each tick.
The verified envelope ADMITs it iff the proven policy cp_pol permits it,
otherwise it SHIELDs (substitutes cp_shield). The angle stays in -3..3
for EVERY input -- that is the theorem, made runnable.

  commands : an integer u   (the envelope only ever executes -1, 0 or 1)
  EOF / Ctrl-D : quit

angle=0 u? ADMIT  | angle 0 --(exec 0)--> 0   (policy permits u=0)
angle=0 u? ADMIT  | angle 0 --(exec 1)--> ~2   (policy permits u=1)
angle=~2 u? SHIELD | angle ~2 --(exec ~1)--> ~1   (u=1 would breach safety; fell back to shield=~1)
angle=~1 u? ADMIT  | angle ~1 --(exec ~1)--> 0   (policy permits u=~1)
angle=0 u? SHIELD | angle 0 --(exec 0)--> 0   (u=5 is out of range {-1,0,1}; fell back to shield=0)
angle=0 u? ADMIT  | angle 0 --(exec ~1)--> 2   (policy permits u=~1)
angle=2 u? SHIELD | angle 2 --(exec 1)--> 1   (u=~1 would breach safety; fell back to shield=1)
angle=1 u? SHIELD | angle 1 --(exec 1)--> 0   (u=~1 would breach safety; fell back to shield=1)
angle=0 u? ?? not an integer: "banana"  (try -1, 0, or 1)
angle=0 u? ADMIT  | angle 0 --(exec 0)--> 0   (policy permits u=0)
angle=0 u?
[eof] the pole never left the safe box. (qed)
```

Reading the trace:

- `~` is CakeML/SML notation for a negative number (`~2` is −2).
- Out-of-range commands (`5`) and would-breach commands (`-1` at angle 2) are
  **SHIELDed** — the envelope overrides you with `cp_shield = cp_drift`.
- Garbage (`banana`) and huge arbitrary-precision integers are rejected at parse
  time and never reach the gate.
- **The angle never leaves `-3..3`, for every input** — including adversarial
  ones. That invariant is `cp_enveloped_safe`, now an ELF you can run.

## Files

- `envelope_console.cml` — the CakeML source (the reflective gate).
- `build.sh` — pinned, reproducible build (what CI runs).
- `Makefile` — `make` / `make run` / `make clean` wrapper over `build.sh`.
- `README.md` — this file.

The release workflow lives at `../.github/workflows/release.yml`; it attaches
`envelope_console` to a GitHub release when the maintainer publishes one.
