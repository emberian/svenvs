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

mkdir -p "$PLACE_DIR/ovl/candle"
rm -f "$PLACE_FIFO" "$PLACE_LOG" "$PLACE_PGID_FILE"
mkfifo "$PLACE_FIFO"
: > "$PLACE_LOG"

# Ensure candle/compute.ml matches the cake binary's compute_thms_def
# (CakeML commit 1af98e502b4d13fe06c561012f002b7e3c15d609) even on a fresh
# unpatched CANDLE_ROOT checkout, without mutating CANDLE_ROOT in place.
cp "$CANDLE_ROOT/candle/compute.ml" "$PLACE_DIR/ovl/candle/compute.ml"
if grep -q 'Cexp_if (Cexp_pair p2 q2) p1 q1 = p1' "$PLACE_DIR/ovl/candle/compute.ml"; then
  patch -s "$PLACE_DIR/ovl/candle/compute.ml" < "$SVENVS_ROOT/candle/compute_if.patch" \
    || die "failed to apply candle/compute_if.patch to staged compute.ml"
fi

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

# preload HOL Light (slow, exactly once) with staged compute.ml on loadPath
printf 'let () = Cakeml.loadPath := "%s/ovl" :: !Cakeml.loadPath;;\n#use "hol.ml";;\nlet _READY = 1;;\n' "$PLACE_DIR" > "$PLACE_FIFO"
echo "place-server: loading hol.ml under $PLACE_DIR (~minutes). Watch: grep _READY $PLACE_LOG"
