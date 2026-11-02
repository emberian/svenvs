#!/usr/bin/env bash
# TIER 3 — "the Place" verified LIVE by a running Candle prover. Re-derives
# the core habitat theorems (same maths as Tier 1, in HOL Light) and a
# concrete watchdog-habitat instance, certified at runtime by Candle's
# verified kernel.
. "$(dirname "$0")/env.sh"
for a in "$@"; do case "$a" in --clean|--quick) : ;; *) die "tier3: unknown arg '$a'";; esac; done
LOG="$PLACE_LOG"

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
"$(dirname "$0")/place-submit.sh" "$SVENVS_ROOT/candle/theplace.ml" _SVENVS_PLACE_OK >/dev/null
# core habitat + the SYM kernel-mod tie-in + the live policy self-optimizations
# (watchdog and polecart), all certified at runtime by the verified kernel.
for thm in SAFETY_PRESERVATION SAFE_WEAKENING WD_SHIELD_SAFE WD_HABITAT_SAFE \
           EQ_SYM_RULE WD_SELF_OPTIMIZED_SAFE CP_HABITAT_SAFE CP_SELF_OPTIMIZED_SAFE; do
  grep -aE "val $thm = " "$LOG" | tail -1 | grep -q '|-' \
    && ok "Candle kernel certified $thm" \
    || die "$thm not certified by live Candle"
done

for thm in SYM_LEMMA FACT1_SYM FACT1_ROUNDTRIP; do
  grep -aE "val $thm = " "$LOG" | tail -1 | grep -q '|-' \
    && ok "Candle kernel certified $thm (self-extended)" \
    || die "$thm not certified by live Candle"
done

for thm in GATE1 GATE2 GATE_B GATE_C THEPLACE_COMPUTE_THM; do
  grep -aE "val $thm = " "$LOG" | tail -1 | grep -q '|-' \
    && ok "Candle kernel certified swap/compiler/compute gate $thm" \
    || die "$thm not certified by live Candle"
done
grep -aqE 'val compiler_cell_verdict = "COMPILER_CELL_CANDLE_OK"' "$LOG" \
  && ok "live proof-gated compiler cell: COMPILER_CELL_CANDLE_OK" \
  || die "theplace.ml did not reach COMPILER_CELL_CANDLE_OK"
grep -aqE 'val verdict = "APEX_SUBSTRATE_OK"' "$LOG" \
  && ok "live recompile-swap-resume: outputs invariant across accumulated swaps, bad swaps REJECTED (APEX_SUBSTRATE_OK)" \
  || die "theplace.ml did not reach APEX_SUBSTRATE_OK"

say "TIER 3 REPRODUCED — the Place + live self-optimization + live proof-gated compiler cell, certified at runtime by the verified Candle prover"
