#!/usr/bin/env bash
# Submit a HOL Light file to the running Candle verification server and
# block until its sentinel is echoed (i.e. the verified kernel finished).
#   scripts/place-submit.sh <file.ml> <SENTINEL_IDENT>
set -euo pipefail
FIFO="${PLACE_FIFO:-/tmp/place.fifo}"
LOG="${PLACE_LOG:-/tmp/place.log}"
f="$1"; s="$2"
[ -p "$FIFO" ] || { echo "no place-server FIFO at $FIFO (start place-server.sh)" >&2; exit 1; }
{ cat "$f"; printf '\nlet %s = 1;;\n' "$s"; } > "$FIFO"
for _ in $(seq 1 300); do
  grep -q "val $s = 1" "$LOG" 2>/dev/null && { echo "[$s] verified-kernel pass"; exit 0; }
  sleep 2
done
echo "[$s] TIMEOUT" >&2; exit 1
