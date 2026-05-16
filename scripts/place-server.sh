#!/usr/bin/env bash
# Start a persistent Candle verification server: HOL Light loaded ONCE,
# fed proof scripts via a FIFO. This is both the fast-iteration loop and
# the closed-loop runtime substrate for "the Place".
#
#   CANDLE_ROOT=~/dev/candle scripts/place-server.sh
#
# Then submit with scripts/place-submit.sh <file> <SENTINEL>.
set -euo pipefail
: "${CANDLE_ROOT:=$HOME/dev/candle}"
FIFO="${PLACE_FIFO:-/tmp/place.fifo}"
LOG="${PLACE_LOG:-/tmp/place.log}"

[ -x "$CANDLE_ROOT/candle/build/cake" ] || {
  echo "No Candle binary at $CANDLE_ROOT/candle/build/cake — run build-instructions.sh" >&2
  exit 1; }

pkill -f "cake --candle" 2>/dev/null || true
sleep 1
rm -f "$FIFO" "$LOG"; mkfifo "$FIFO"
# holder keeps the FIFO write-end open so Candle never sees EOF
( exec 3>"$FIFO"; while sleep 3600; do :; done ) &
echo $! > "${PLACE_FIFO}.holder.pid"
( cd "$CANDLE_ROOT" && ./candle.sh < "$FIFO" > "$LOG" 2>&1 ) &
echo $! > "${PLACE_FIFO}.candle.pid"
# preload HOL Light (slow, exactly once)
printf '#use "hol.ml";;\nlet _READY = 1;;\n' > "$FIFO"
echo "place-server: loading hol.ml (~minutes). Watch: grep _READY $LOG"
