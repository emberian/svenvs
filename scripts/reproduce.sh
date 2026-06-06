#!/usr/bin/env bash
# One command to reproduce svenvs from a clone, as far as your toolchain
# allows. Each tier degrades gracefully:
#   Tier 1 — only HOL4 (anyone).
#   Tier 2 — + a built CakeML candle chain (auto-skips if absent).
#   Tier 3 — + a Candle binary (auto-skips if absent).
#
#   git clone <svenvs> && cd svenvs && scripts/reproduce.sh
#
# Options (forwarded to every tier):
#   --quick   skip optional/slow extras (toy verified-inference track)
#   --clean   force a from-scratch rebuild (default: incremental, cached)
#
# Re-running is safe and fast: Holmake only rebuilds what changed.
set -euo pipefail
here="$(cd "$(dirname "$0")" && pwd)"
. "$here/env.sh"

ARGS=("$@")
for a in "${ARGS[@]:-}"; do
  case "$a" in
    --quick|--clean) : ;;
    -h|--help) sed -n '2,16p' "$0"; exit 0 ;;
    *) die "reproduce.sh: unknown option '$a' (see --help)" ;;
  esac
done

say "svenvs reproduction  (pins: HOL4 $SVENVS_HOL4_COMMIT, CakeML $SVENVS_CAKEML_COMMIT, PolyML $SVENVS_POLYML_VERSION)"

bash "$here/tier1-core.sh"          "${ARGS[@]:-}"
bash "$here/tier2-candle-layers.sh" "${ARGS[@]:-}" || true
bash "$here/tier2.5-cited-layers.sh" "${ARGS[@]:-}" || true
bash "$here/tier3-place-candle.sh"  "${ARGS[@]:-}" || true

say "REPRODUCTION SUMMARY"
yn(){ "$@" >/dev/null 2>&1 && printf yes || printf 'no (skipped — prereq absent)'; }
t1=$(yn built "$SVENVS_ROOT" upgrade)
t1b=$(yn built "$SVENVS_ROOT/agent" toolAgentRun)
t2=$(yn built "$SVENVS_ROOT/kernel" kernelUpgrade)
t25=$(yn built "$SVENVS_ROOT/loader" installLoader)
t3=no
grep -aqE 'val WD_HABITAT_SAFE = .*\|-' "${PLACE_LOG:-/tmp/place.log}" 2>/dev/null && t3=yes

printf '  Tier 1   core + cartpole + proof-carrying self-improvement : %s\n' "$t1"
printf '  Tier 1   adversarial-LLM tool-agent (running episodes)     : %s\n' "$t1b"
printf '  Tier 2   Candle-kernel-checked + kernel-self-upgrade       : %s\n' "$t2"
printf '  Tier 2.5 cited self-improvement layers (loader/kernelMod/  : %s\n' "$t25"
printf '           kernelImpl/selfproverConcrete)\n'
printf '  Tier 3   the Place, live in the running Candle prover      : %s\n' "$t3"

[ "$t1" = yes ] && [ "$t1b" = yes ] \
  || die "Tier 1 MUST reproduce on any machine with HOL4 — see /tmp/svenvs-t1-*.log"

ok "Tier 1 reproduced. Higher tiers reproduce when their (heavy) prereqs are present."
echo
echo "  Next: ./demo.sh                 — the 2-minute guided showcase"
echo "        less CLAIMS.md            — exactly what is proven vs assumed"
echo "        less ARCHITECTURE.md      — layers + honest epistemic status"
