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
# core habitat + the SYM kernel-mod tie-in + the live policy self-optimizations
# (watchdog and polecart), all certified at runtime by the verified kernel.
for thm in SAFETY_PRESERVATION SAFE_WEAKENING WD_SHIELD_SAFE WD_HABITAT_SAFE \
           EQ_SYM_RULE WD_SELF_OPTIMIZED_SAFE CP_HABITAT_SAFE CP_SELF_OPTIMIZED_SAFE; do
  grep -aE "val $thm = " "$LOG" | tail -1 | grep -q '|-' \
    && ok "Candle kernel certified $thm" \
    || die "$thm not certified by live Candle"
done

# the live self-optimization loop: the prover proves a rule sound, ADOPTS it
# as a reusable derived rule, and uses it to prove more (LCF self-extension).
say "Tier 3: submitting the live self-optimization loop"
"$(dirname "$0")/place-submit.sh" "$SVENVS_ROOT/candle/selfopt_demo.ml" _SVENVS_SELFOPT_OK
for thm in SYM_LEMMA FACT1_SYM FACT1_ROUNDTRIP; do
  grep -aE "val $thm = " "$LOG" | tail -1 | grep -q '|-' \
    && ok "Candle kernel certified $thm (self-extended)" \
    || die "$thm not certified by live Candle"
done
# the live PROOF-GATED RECOMPILE -> SWAP -> RESUME loop: the running system
# replaces its own executing compute code with freshly-compiled versions (in-
# binary compiler + real do_install), each gated by a live kernel equivalence
# proof; swaps accumulate (path-dependent); an unprovable swap is REJECTED so
# semantics can never break. The Apex substrate, running.
say "Tier 3: submitting the live proof-gated recompile->swap->resume loop"
"$(dirname "$0")/place-submit.sh" "$SVENVS_ROOT/candle/self_recompile.ml" _SVENVS_RECOMPILE_OK
for thm in GATE1 GATE2; do
  grep -aE "val $thm = " "$LOG" | tail -1 | grep -q '|-' \
    && ok "Candle kernel certified swap gate $thm" \
    || die "$thm not certified by live Candle"
done
grep -aqE 'val verdict = "APEX_SUBSTRATE_OK"' "$LOG" \
  && ok "live recompile-swap-resume: outputs invariant across 2 accumulated swaps, cost 101->1, bad swap REJECTED (APEX_SUBSTRATE_OK)" \
  || die "self_recompile loop did not reach APEX_SUBSTRATE_OK"

say "TIER 3 REPRODUCED — the Place + live self-optimization + live proof-gated recompile-swap-resume, certified at runtime by the verified Candle prover"
