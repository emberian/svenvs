#!/usr/bin/env bash
# TIER 3 — "the Place" verified LIVE by a running Candle prover. Re-derives
# the core habitat theorems (same maths as Tier 1, in HOL Light) and a
# concrete watchdog-habitat instance, certified at runtime by Candle's
# verified kernel.
. "$(dirname "$0")/env.sh"
for a in "$@"; do case "$a" in --clean|--quick) : ;; *) die "tier3: unknown arg '$a'";; esac; done
FIFO="${PLACE_FIFO:-/tmp/place.fifo}"; LOG="${PLACE_LOG:-/tmp/place.log}"
export PLACE_FIFO="$FIFO" PLACE_LOG="$LOG"

if [ ! -x "$CANDLE_ROOT/candle/build/cake" ]; then
  warn "SKIP Tier 3: no Candle binary at $CANDLE_ROOT/candle/build/cake.
  Build it (x86_64 Linux): cd \$CANDLE_ROOT && ./build-instructions.sh
  (downloads the official verified cake-x64-64; ~15 min, no HOL needed).
  Tiers 1-2 fully reproduce the proofs without a running prover."
  exit 0
fi

# (re)start the persistent server if not alive
if ! { [ -f "${FIFO}.candle.pid" ] && kill -0 "$(cat "${FIFO}.candle.pid")" 2>/dev/null; }; then
  say "Tier 3: starting Candle server (loads hol.ml once)"
  CANDLE_ROOT="$CANDLE_ROOT" "$(dirname "$0")/place-server.sh"
  say "waiting for HOL Light to finish loading"
  for _ in $(seq 1 600); do grep -q "val _READY = 1" "$LOG" 2>/dev/null && break; sleep 2; done
  grep -q "val _READY = 1" "$LOG" || die "Candle server did not become ready"
fi
ok "Candle verification server live (hol.ml loaded)"

say "Tier 3: submitting the Place to the live verified kernel"
"$(dirname "$0")/place-submit.sh" "$SVENVS_ROOT/candle/theplace.ml" _SVENVS_PLACE_OK
for thm in SAFETY_PRESERVATION SAFE_WEAKENING WD_SHIELD_SAFE WD_HABITAT_SAFE; do
  grep -aE "val $thm = " "$LOG" | tail -1 | grep -q '|-' \
    && ok "Candle kernel certified $thm" \
    || die "$thm not certified by live Candle"
done
say "TIER 3 REPRODUCED — the Place certified at runtime by the verified Candle prover"
