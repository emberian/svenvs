#!/usr/bin/env bash
# Shared environment + pinned versions for reproducing svenvs.
# Source this: . scripts/env.sh
set -euo pipefail

# --- pinned upstream versions (the svenvs proofs were checked against these) -
export SVENVS_HOL4_COMMIT="2faefbd57"     # HOL-Theorem-Prover/HOL
export SVENVS_CAKEML_COMMIT="ac654a0a3"   # CakeML/cakeml
export SVENVS_POLYML_VERSION="v5.9.2"     # polyml/polyml

# --- locations (override by exporting before sourcing) ----------------------
SVENVS_ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
export SVENVS_ROOT
export HOLDIR="${HOLDIR:-$HOME/dev/HOL}"
export CAKEMLDIR="${CAKEMLDIR:-$HOME/dev/CakeML}"
export HOLREFLDIR="${HOLREFLDIR:-$HOME/dev/hol-reflection}"
export CANDLE_ROOT="${CANDLE_ROOT:-$HOME/dev/candle}"
export HOLMAKE="${HOLMAKE:-$HOLDIR/bin/Holmake}"

# HOL4's *parallel* Holmake deadlocks against its own prebuilt-theory cache
# (~/.cache/HOL) on many-core machines: futex hang, 0% CPU, indefinitely.
# --no-cache keeps full parallelism without the deadlock; it only disables the
# cross-clone theory cache, NOT local incremental .uo checks, so re-running
# stays a fast no-op. Set SVENVS_HM_FLAGS= (empty) to restore caching, e.g.
# on a 1-2 core box where the deadlock does not bite and cross-clone replay helps.
export SVENVS_HM_FLAGS="${SVENVS_HM_FLAGS---no-cache}"

# colour only on a tty (logs/pipes stay clean)
if [ -t 1 ]; then C_HD=$'\033[1;36m'; C_OK=$'\033[1;32m'; C_NO=$'\033[1;31m'
                 C_WN=$'\033[1;33m'; C_Z=$'\033[0m'
else C_HD=; C_OK=; C_NO=; C_WN=; C_Z=; fi
say(){  printf '\n%s=== %s ===%s\n'  "$C_HD" "$*" "$C_Z"; }
ok(){   printf '%s  OK  %s%s\n'      "$C_OK" "$*" "$C_Z"; }
warn(){ printf '%s  WARN %s%s\n'     "$C_WN" "$*" "$C_Z" >&2; }
die(){  printf '%s  FAIL %s%s\n'     "$C_NO" "$*" "$C_Z" >&2; exit 1; }
have(){ command -v "$1" >/dev/null 2>&1; }

# HOL4's hol binary (for printing proved theorems in demo.sh)
export HOL="${HOL:-$HOLDIR/bin/hol}"

require_hol4(){
  [ -x "$HOLMAKE" ] || die "HOL4 Holmake not found at $HOLMAKE.
  Install HOL4 (PolyML $SVENVS_POLYML_VERSION) and build it at commit $SVENVS_HOL4_COMMIT,
  or set HOLDIR. See scripts/INSTALL.md."
  local got; got="$(git -C "$HOLDIR" rev-parse --short HEAD 2>/dev/null || echo '?')"
  [ "$got" = "$SVENVS_HOL4_COMMIT" ] || \
    warn "HOL4 at $got, pinned $SVENVS_HOL4_COMMIT (proofs checked against the pin)"
}

# A theory is "built" iff Holmake produced its .uo object.
built(){ [ -f "$1/.hol/objs/${2}Theory.uo" ]; }
