# Prerequisites (pinned)

svenvs proofs were checked against exact upstream versions. Mismatches may
still work but are unsupported.

| Component | Pin | Needed for |
|-----------|-----|------------|
| PolyML | `v5.9.2` | HOL4 runtime |
| HOL4 (`HOL-Theorem-Prover/HOL`) | `2faefbd57` | **Tier 1** (everything) |
| CakeML (`CakeML/cakeml`) | `ac654a0a3`, with `candle/standard/semantics` built | **Tier 2** |
| Candle (`CakeML/candle`) `cake` binary | x86_64 Linux, via `build-instructions.sh` | **Tier 3** |

## Minimum (Tier 1 — anyone)

```bash
# PolyML
git clone https://github.com/polyml/polyml && cd polyml \
  && git checkout v5.9.2 && ./configure --prefix=$HOME/poly \
  && make && make install && export PATH=$HOME/poly/bin:$PATH
# HOL4
git clone https://github.com/HOL-Theorem-Prover/HOL ~/dev/HOL && cd ~/dev/HOL \
  && git checkout 2faefbd57 && poly < tools/smart-configure.sml && bin/build
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
Tier 2 ~108s cold; Tier 3 (live Candle) ~55s. End-to-end cold from a built
toolchain is roughly 5 minutes; the one large one-time cost is building HOL4
itself (`bin/build`, ~30–60 min).

## Tier 2 (Candle-kernel-checked layers)

```bash
git clone https://github.com/CakeML/cakeml ~/dev/CakeML && cd ~/dev/CakeML \
  && git checkout ac654a0a3
cd ~/dev/CakeML/candle/standard/semantics && CAKEMLDIR=~/dev/CakeML Holmake  # heavy
export CAKEMLDIR=~/dev/CakeML
```

## Tier 3 (the Place, live in Candle — x86_64 Linux)

```bash
git clone https://github.com/CakeML/candle ~/dev/candle && cd ~/dev/candle \
  && ./build-instructions.sh        # downloads verified cake-x64-64; ~15 min
export CANDLE_ROOT=~/dev/candle
```
