#!/usr/bin/env bash
# Stop the Candle server that place-server.sh started under $PLACE_DIR, by its
# recorded process group only. Nothing else on the machine is touched.
. "$(dirname "$0")/env.sh"

if [ -f "$PLACE_PGID_FILE" ]; then
  pg="$(cat "$PLACE_PGID_FILE")"
  if [ -n "$pg" ] && kill -0 -- "-$pg" 2>/dev/null; then
    kill -TERM -- "-$pg" 2>/dev/null || true
    sleep 1
    kill -0 -- "-$pg" 2>/dev/null && { kill -KILL -- "-$pg" 2>/dev/null || true; }
    ok "stopped the Candle server (process group $pg) under $PLACE_DIR"
  else
    echo "place-stop: no live server under $PLACE_DIR"
  fi
  rm -f "$PLACE_PGID_FILE"
else
  echo "place-stop: no server recorded under $PLACE_DIR"
fi
rm -f "$PLACE_FIFO"
