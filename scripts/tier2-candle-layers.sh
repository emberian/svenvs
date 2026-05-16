#!/usr/bin/env bash
# TIER 2 — needs a CakeML checkout with the candle/standard chain built
# (holSyntax/holSemantics/holSoundness). Builds the layers where the
# self-improvement obligation is checked by Candle's *verified inference
# system* (proves_sound), and the kernel-self-upgrade layer.
#
# Idempotent; auto-SKIPs (exit 0) with instructions if the candle chain is
# absent — Tier 1 is unaffected. Pass --clean to force a rebuild.
. "$(dirname "$0")/env.sh"
require_hol4

CLEAN=0
for a in "$@"; do
  case "$a" in
    --clean) CLEAN=1 ;;
    --quick) : ;;                       # accepted, no effect at this tier
    *) die "tier2: unknown arg '$a'" ;;
  esac
done

CANDLE_SEM="$CAKEMLDIR/candle/standard/semantics/.hol/objs/holSoundnessTheory.uo"
if [ ! -f "$CANDLE_SEM" ]; then
  warn "SKIP Tier 2: CakeML candle chain not built at
       $CANDLE_SEM
  Need CakeML @ $SVENVS_CAKEML_COMMIT with candle/standard/semantics built:
      cd \$CAKEMLDIR/candle/standard/semantics && CAKEMLDIR=\$CAKEMLDIR Holmake
  (heavy; see scripts/INSTALL.md). Tier 1 fully reproduces the
  proof-carrying self-improvement architecture without this."
  exit 0
fi

for d in embedded kernel; do
  say "Tier 2: $d (obligation checked by Candle's verified kernel)"
  cd "$SVENVS_ROOT/$d" || die "missing $SVENVS_ROOT/$d"
  if [ "$CLEAN" = 1 ]; then
    CAKEMLDIR="$CAKEMLDIR" "$HOLMAKE" cleanAll >/dev/null 2>&1 || true
    rm -rf .hol
  fi
  if ! CAKEMLDIR="$CAKEMLDIR" "$HOLMAKE" 2>&1 \
        | tee "/tmp/svenvs-t2-$d.log" | tail -n 6; then
    die "Holmake failed in $d — full log: /tmp/svenvs-t2-$d.log"
  fi
done

built "$SVENVS_ROOT/embedded" embeddedGate \
  || die "embeddedGateTheory not built (see /tmp/svenvs-t2-embedded.log)"
built "$SVENVS_ROOT/kernel" kernelUpgrade \
  || die "kernelUpgradeTheory not built (see /tmp/svenvs-t2-kernel.log)"
ok "embeddedGate + kernelUpgrade machine-checked (Candle-soundness-backed)"
say "TIER 2 REPRODUCED — obligation discharged by Candle's verified inference system"
