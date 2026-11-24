#!/usr/bin/env bash
# TIER 3 — "the Place" verified LIVE by a running Candle prover. Re-derives
# the core habitat theorems (same maths as Tier 1, in HOL Light) and a
# concrete watchdog-habitat instance, certified at runtime by Candle's
# verified kernel.
. "$(dirname "$0")/env.sh"
for a in "$@"; do case "$a" in --clean|--quick) : ;; *) die "tier3: unknown arg '$a'";; esac; done

if [ ! -x "$CANDLE_ROOT/candle/build/cake" ]; then
  warn "SKIP Tier 3: no Candle binary at $CANDLE_ROOT/candle/build/cake.
  Build it (x86_64 Linux): cd \$CANDLE_ROOT && ./build-instructions.sh
  (downloads the official verified cake-x64-64; ~15 min, no HOL needed).
  Tiers 1-2 fully reproduce the proofs without a running prover."
  exit 0
fi

# reuse the persistent server under $PLACE_DIR, or start it (loads hol.ml once)
place_ensure_server

say "Tier 3: submitting the fused Place + self-optimization + proof-gated compiler cell to the live verified kernel"
here="$SVENVS_ROOT/scripts"
"$here/place-submit.sh" "$SVENVS_ROOT/candle/theplace.ml" _SVENVS_PLACE_OK > "$PLACE_LOG.theplace"
"$here/place-submit.sh" "$SVENVS_ROOT/agent/closedloop/obligation_template.ml" _SVENVS_CLOSEDLOOP_OK > "$PLACE_LOG.closedloop"
bash "$here/verify-claims.sh" --tier 3 --strict

say "TIER 3 REPRODUCED — the Place + live self-optimization + live proof-gated compiler cell, certified at runtime by the verified Candle prover"
