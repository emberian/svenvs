#!/usr/bin/env bash
# Shared environment + pinned versions for reproducing svenvs.
# Source this: . scripts/env.sh
set -euo pipefail

# --- pinned upstream versions (the svenvs proofs were checked against these) -
# Full commit SHAs, never a tag or a short id: a tag can be moved and a short
# id can collide, so these are what every script and the CI workflow compare
# against verbatim. Keep .github/workflows/verify.yml and scripts/INSTALL.md
# in lockstep with this block.
export SVENVS_HOL4_COMMIT="2faefbd579453cb5d41f840debaa106d431bcd63"    # HOL-Theorem-Prover/HOL
export SVENVS_CAKEML_COMMIT="ac654a0a33de8eef7b85de46d951b9df344d8076"  # CakeML/cakeml
export SVENVS_POLYML_VERSION="v5.9.2"                                    # polyml/polyml: the tag ...
export SVENVS_POLYML_COMMIT="4557554077078decce4ce5f90da00a713cfc32e4"  # ... and the commit it named

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

# --- scratch ------------------------------------------------------------------
# Everything svenvs writes outside the repo (build logs, apex work dirs, the
# Place) lives under ONE per-user directory. Nothing at a fixed, shared /tmp
# name, so two users or two concurrent runs on the same box never collide.
export SVENVS_WORK="${SVENVS_WORK:-${TMPDIR:-/tmp}/svenvs-$(id -un)}"
export SVENVS_LOGS="${SVENVS_LOGS:-$SVENVS_WORK/logs}"
mkdir -p "$SVENVS_LOGS"

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
  local got; got="$(git -C "$HOLDIR" rev-parse HEAD 2>/dev/null || echo '?')"
  [ "$got" = "$SVENVS_HOL4_COMMIT" ] || \
    warn "HOL4 at $got, pinned $SVENVS_HOL4_COMMIT (proofs checked against the pin)"
}

# A theory is "built" iff Holmake produced its .uo object.
built(){ [ -f "$1/.hol/objs/${2}Theory.uo" ]; }

# The code of an SML/HOL Light file with every (* ... *) comment blanked out
# (newlines kept, so line numbers survive). The cheat/oracle gates scan this,
# so prose about cheats can never trip them.
code_only(){ perl -0777 -pe 's/\(\*.*?\*\)/ my $m = $&; $m =~ s#[^\n]# #g; $m /gse' "$1"; }

# --- the Place: a persistent Candle server fed over a FIFO -------------------
# scripts/place-server.sh starts it under $PLACE_DIR and records its process
# group; scripts/place-submit.sh feeds it; scripts/place-stop.sh stops it by
# that recorded group and nothing else. Scripts that need their own private
# server call place_use_dir first.
place_use_dir(){
  export PLACE_DIR="$1"
  export PLACE_FIFO="$PLACE_DIR/place.fifo"
  export PLACE_LOG="$PLACE_DIR/place.log"
  export PLACE_PGID_FILE="$PLACE_DIR/server.pgid"
}
export PLACE_DIR="${PLACE_DIR:-$SVENVS_WORK/place}"
export PLACE_FIFO="${PLACE_FIFO:-$PLACE_DIR/place.fifo}"
export PLACE_LOG="${PLACE_LOG:-$PLACE_DIR/place.log}"
export PLACE_PGID_FILE="${PLACE_PGID_FILE:-$PLACE_DIR/server.pgid}"

# alive iff the process group place-server.sh recorded still has a member
place_alive(){
  local pg
  [ -f "$PLACE_PGID_FILE" ] || return 1
  pg="$(cat "$PLACE_PGID_FILE")"
  [ -n "$pg" ] && kill -0 -- "-$pg" 2>/dev/null
}
# block until hol.ml is loaded (the server echoes _READY), or the server dies
place_wait_ready(){
  local _i
  for _i in $(seq 1 "${PLACE_READY_TRIES:-600}"); do
    grep -qa "val _READY = 1" "$PLACE_LOG" 2>/dev/null && return 0
    place_alive || die "the Candle server died while loading hol.ml (see $PLACE_LOG)"
    sleep 2
  done
  die "Candle server did not become ready (see $PLACE_LOG)"
}
# reuse a live server under $PLACE_DIR, else start one and wait for it
place_ensure_server(){
  if place_alive; then ok "Candle verification server live under $PLACE_DIR"; return 0; fi
  say "starting the Candle server under $PLACE_DIR (loads hol.ml once, ~minutes)"
  "$SVENVS_ROOT/scripts/place-server.sh"
  place_wait_ready
  ok "Candle verification server live (hol.ml loaded)"
}

# --- guard for scripts that must edit a file inside an UPSTREAM checkout -----
# (your CakeML or Candle tree). Opt-in only, and refused if any of the files
# already carries local modifications, so a restore can never clobber your
# own edits. Prefer a throwaway checkout for these scripts.
#   svenvs_confirm_inplace <repo-dir> "<path> [<path>...]" "<why>"
svenvs_confirm_inplace(){
  local repo="$1" paths="$2" why="$3" p dirty=""
  [ "${SVENVS_ALLOW_INPLACE:-0}" = 1 ] || die "this script edits files inside $repo in place ($why):
    $paths
  It is opt-in: re-run with SVENVS_ALLOW_INPLACE=1, ideally against a throwaway checkout."
  if git -C "$repo" rev-parse --is-inside-work-tree >/dev/null 2>&1; then
    for p in $paths; do
      [ -z "$(git -C "$repo" status --porcelain -- "$p")" ] || dirty="$dirty $p"
    done
    [ -z "$dirty" ] || die "these files in $repo already have local modifications:$dirty
  Commit or restore them first, so nothing of yours can be clobbered."
  else
    warn "$repo is not a git checkout; cannot verify its files are pristine before editing them"
  fi
}
