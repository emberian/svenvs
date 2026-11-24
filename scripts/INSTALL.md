# Prerequisites (pinned)

svenvs proofs were checked against exact upstream versions. Mismatches may
still work but are unsupported. Every pin is a **full commit SHA** (a tag can
be moved, a short id can collide); `scripts/env.sh` is the machine-readable
copy and CI compares the checked-out toolchain against it verbatim.

| Component | Pin | Needed for |
|-----------|-----|------------|
| PolyML | tag `v5.9.2` = commit `4557554077078decce4ce5f90da00a713cfc32e4` | HOL4 runtime |
| HOL4 (`HOL-Theorem-Prover/HOL`) | `2faefbd579453cb5d41f840debaa106d431bcd63` | **Tier 1** (everything) |
| CakeML (`CakeML/cakeml`) | `ac654a0a33de8eef7b85de46d951b9df344d8076`, with `candle/standard/semantics` built | **Tier 2** |
| Candle (`CakeML/candle`) `cake` binary | x86_64 Linux, via `build-instructions.sh` | **Tier 3** |
| Obend checkout in `$OBEND_ROOT` and an x86-64 `cake` with `--pancake` in `$CAKE` | Obend `43ebd791f1b82292107d9f8faca4e0012fee2e5f` and CakeML `ccfc23cbadf4fadf8c82a7ac60e813ea5906218a` ([native compiler release v3400](https://github.com/CakeML/cakeml/releases/tag/v3400)) | **full verification** (`scripts/verify-all-tiers.sh` parses Obend's Pancake kernels, which takes hours) |

## Minimum (Tier 1 — anyone)

```bash
# PolyML
git clone https://github.com/polyml/polyml && cd polyml \
  && git checkout 4557554077078decce4ce5f90da00a713cfc32e4 `# tag v5.9.2` \
  && ./configure --prefix=$HOME/poly \
  && make && make install && export PATH=$HOME/poly/bin:$PATH
# HOL4
git clone https://github.com/HOL-Theorem-Prover/HOL ~/dev/HOL && cd ~/dev/HOL \
  && git checkout 2faefbd579453cb5d41f840debaa106d431bcd63 \
  && poly < tools/smart-configure.sml && bin/build
export HOLDIR=~/dev/HOL
```
Then, from the svenvs clone:

```bash
./demo.sh                       # 2-minute guided showcase (Tier 1)
scripts/reproduce.sh            # full tiered reproduction
scripts/reproduce.sh --quick    # skip optional/slow extras
scripts/reproduce.sh --clean    # force a from-scratch rebuild
```

Tier 1 runs for anyone; Tiers 2–3 auto-skip with instructions if their
prerequisites are absent. All scripts are idempotent (re-running is a fast
Holmake-cached no-op) and exit non-zero with a clear message on any failure.
`demo.sh` additionally needs `python3` (for the embodied-LLM segment;
`--mock` needs no model). What is proven vs. assumed: `../CLAIMS.md`.

### If a build hangs at 0% CPU (many-core machines)

HOL4's **parallel** Holmake can deadlock against its own prebuilt-theory
cache (`~/.cache/HOL`): the build wedges indefinitely, futex-blocked, at 0%
CPU. It bites reliably on many-core boxes (small core counts sometimes slip
through — which is why it can look like "it just never finishes" rather than
an error). svenvs's scripts therefore pass `--no-cache` by default
(`SVENVS_HM_FLAGS` in `scripts/env.sh`), which keeps full parallelism without
the deadlock and only disables the *cross-clone* cache, not local incremental
rebuilds. To restore caching (e.g. on a 1–2 core box), run with
`SVENVS_HM_FLAGS= scripts/reproduce.sh`. Running a bare `Holmake` by hand on a
many-core machine? Add `--no-cache`, or `-j1`.

Reference timings (24-core box, prebuilt PolyML/HOL4, `--no-cache`): Tier 1
~16s cold / <1s warm; the CakeML candle/standard/semantics chain ~2m30s cold;
Tier 2 ~108s cold; Tier 3 (live Candle) ~55s. `scripts/reproduce.sh` takes roughly 5 minutes with the toolchain installed.
Building HOL4 itself takes another 30–60 minutes. The strict all-tier run
also builds and checks the five Pancake kernels on x86-64 Linux, which adds
about three hours on a cold build.

## Tier 2 (Candle-kernel-checked layers)

```bash
git clone https://github.com/CakeML/cakeml ~/dev/CakeML && cd ~/dev/CakeML \
  && git checkout ac654a0a33de8eef7b85de46d951b9df344d8076
cd ~/dev/CakeML/candle/standard/semantics && CAKEMLDIR=~/dev/CakeML Holmake  # heavy
export CAKEMLDIR=~/dev/CakeML
```

## Tier 3 (the Place, live in Candle — x86_64 Linux)

```bash
git clone https://github.com/CakeML/candle ~/dev/candle && cd ~/dev/candle \
  && ./build-instructions.sh        # downloads verified cake-x64-64; ~15 min
export CANDLE_ROOT=~/dev/candle
```

To align `candle/compute.ml` with the `cake-x64-64` binary's `compute_thms_def`
(CakeML commit `1af98e502b4d13fe06c561012f002b7e3c15d609`) for interactive
`Kernel.compute` sessions, apply `candle/compute_if.patch` in `$CANDLE_ROOT`
(`scripts/place-server.sh` also stages this automatically on `Cakeml.loadPath`
when starting the Place server).
