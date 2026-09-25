#!/usr/bin/env bash
# PROOF-GATED per-generation compiler self-upgrade, RUNNING under the live
# verified Candle kernel.
#
# Submits candle/compiler_cell_candle.ml to a running Candle prover: the
# per-generation compiler map (= g2c) is upgraded in place (= repl_upgrade),
# but the GATE is STRONGER than the verified compiler_agrees — the live kernel
# must PROVE each new compiler CORRECT (its value-spec = the observable spec)
# before it is installed.  Across every gated upgrade the observable is
# invariant while the compiler's cost strictly drops; earlier generations keep
# their own compiler; a wrong compiler is REFUSED by the kernel.
#
# This is the kernel-proof-gated runtime image of selfUpgrade/evalUpgradeOp.
# Auto-SKIPs (exit 0) if no Candle binary is present.
. "$(dirname "$0")/env.sh"
for a in "$@"; do case "$a" in --clean|--quick) : ;; *) die "apex-compiler-cell-candle: unknown arg '$a'";; esac; done

LOG="$PLACE_LOG"

if [ ! -x "$CANDLE_ROOT/candle/build/cake" ]; then
  warn "SKIP apex-compiler-cell-candle: no Candle binary at $CANDLE_ROOT/candle/build/cake.
  Build/fetch it (x86_64 Linux): cd \$CANDLE_ROOT && ./build-instructions.sh.
  The proof side (selfUpgrade/evalUpgradeOpScript.sml) and the native runtime
  image (scripts/apex-compiler-cell.sh) need no live prover."
  exit 0
fi

# reuse the persistent server under $PLACE_DIR, or start it (loads hol.ml once)
place_ensure_server

say "submitting the proof-gated compiler-cell upgrade to the live verified kernel"
"$(dirname "$0")/place-submit.sh" "$SVENVS_ROOT/candle/compiler_cell_candle.ml" _CCC_DONE >/dev/null

# the live kernel must have PROVED each accepted compiler correct, REFUSED the
# wrong one, and the whole property must hold.
for thm in GATE_B GATE_C; do
  grep -aE "val $thm = " "$LOG" | tail -1 | grep -q '|-' \
    && ok "live kernel certified compiler-correctness $thm" \
    || die "$thm not certified by live Candle"
done
grep -aE 'val bad_ok = false' "$LOG" >/dev/null \
  && ok "live kernel REFUSED to certify the wrong compiler (bad_ok = false)" \
  || die "the bad compiler was not refused"
grep -aE 'val upBad = "REJECTED"' "$LOG" >/dev/null \
  && ok "the wrong compiler upgrade was REJECTED (observable protected)" \
  || die "the bad upgrade was not rejected"
if grep -aqE 'val verdict = "COMPILER_CELL_CANDLE_OK"' "$LOG"; then
  ok "verdict COMPILER_CELL_CANDLE_OK — observable invariant, cost reduced, earlier generations preserved, wrong compiler refused"
else
  die "compiler-cell upgrade did not reach COMPILER_CELL_CANDLE_OK"
fi

say "APEX COMPILER-CELL (CANDLE) RAN — the verified per-generation compiler self-upgrade runs live, each in-place upgrade gated by a real Candle kernel CORRECTNESS proof; the observable can never break"
