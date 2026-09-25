#!/usr/bin/env bash
# Start (or query) the persistent Candle verification server of the Place:
# HOL Light loaded ONCE into the verified cake, then fed proof scripts over a
# FIFO. This is both the fast-iteration loop and the closed-loop runtime
# substrate.
#
#   scripts/place-server.sh            start (no-op if one is already running here)
#   scripts/place-server.sh --status   exit 0 iff a server is alive under $PLACE_DIR
#   scripts/place-server.sh --restart  stop the one under $PLACE_DIR, start fresh
#   scripts/place-stop.sh              stop it
#   scripts/place-submit.sh f.ml SENT  feed it
#
# Everything lives under PLACE_DIR (default $SVENVS_WORK/place, per user; see
# scripts/env.sh): the FIFO, the log, and the server's process-group id. The
# server runs in its own process group and is only ever stopped by that id,
# never by matching process names, so nothing else on the machine is touched.
. "$(dirname "$0")/env.sh"

case "${1:-}" in
  --status)
    place_alive && { echo "place-server: alive under $PLACE_DIR"; exit 0; }
    echo "place-server: not running under $PLACE_DIR" >&2; exit 1 ;;
  --restart) "$SVENVS_ROOT/scripts/place-stop.sh" ;;
  "") place_alive && { echo "place-server: already running under $PLACE_DIR (--restart for a fresh one)"; exit 0; } ;;
  *) die "place-server.sh: unknown arg '$1' (--status | --restart)" ;;
esac

[ -x "$CANDLE_ROOT/candle/build/cake" ] || die "no Candle binary at $CANDLE_ROOT/candle/build/cake (run its build-instructions.sh)"
[ -x "$CANDLE_ROOT/candle.sh" ] || die "no candle.sh in $CANDLE_ROOT"

mkdir -p "$PLACE_DIR"
rm -f "$PLACE_FIFO" "$PLACE_LOG" "$PLACE_PGID_FILE"
mkfifo "$PLACE_FIFO"
: > "$PLACE_LOG"

# One process group holds both the FIFO write-end holder (so Candle never sees
# EOF between submissions) and Candle itself; its id is what place-stop.sh
# kills. Job control gives the background job its own group.
set -m
(
  trap '' HUP
  ( exec 3>"$PLACE_FIFO"; while sleep 3600; do :; done ) &
  cd "$CANDLE_ROOT" && exec ./candle.sh < "$PLACE_FIFO" >> "$PLACE_LOG" 2>&1
) </dev/null >/dev/null 2>&1 &
echo $! > "$PLACE_PGID_FILE"
set +m

# preload HOL Light (slow, exactly once)
printf '#use "hol.ml";;\nlet _READY = 1;;\n' > "$PLACE_FIFO"
echo "place-server: loading hol.ml under $PLACE_DIR (~minutes). Watch: grep _READY $PLACE_LOG"
