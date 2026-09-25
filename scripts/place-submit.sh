#!/usr/bin/env bash
# Submit a HOL Light file to the running Candle server and block until the
# verified kernel echoes the sentinel. On success the kernel's own output for
# THIS submission (the log slice appended after the submit) is printed on
# stdout, so callers parse the kernel's echoes without grepping the whole log
# or trusting a sentinel left by an earlier run.
#   scripts/place-submit.sh <file.ml> <SENTINEL_IDENT>
. "$(dirname "$0")/env.sh"

[ $# = 2 ] || die "usage: place-submit.sh <file.ml> <SENTINEL_IDENT>"
f="$1"; s="$2"
[ -f "$f" ] || die "no such file: $f"
place_alive || die "no Candle server under $PLACE_DIR (start scripts/place-server.sh)"

start=$(wc -c < "$PLACE_LOG")
{ cat "$f"; printf '\nlet %s = 1;;\n' "$s"; } > "$PLACE_FIFO"
for _ in $(seq 1 "${PLACE_SUBMIT_TRIES:-300}"); do
  if tail -c +$((start + 1)) "$PLACE_LOG" | grep -qa "val $s = 1"; then
    tail -c +$((start + 1)) "$PLACE_LOG"
    echo "[$s] verified-kernel pass" >&2
    exit 0
  fi
  place_alive || die "[$s] the Candle server died (see $PLACE_LOG)"
  sleep 2
done
die "[$s] TIMEOUT"
