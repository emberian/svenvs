#!/usr/bin/env bash
# ======================================================================
#  APEX — in-process swap of a KERNEL PRIMITIVE under the whole live prover.
#
#  Re-architects the candle kernel INTERFACE (`candle/kernel.ml`) so the
#  prover's `REFL` is a live indirection over the verified `Kernel.REFL`
#  (which stays fixed in cake.S — the soundness, since `thm` is unforgeable),
#  loads the full HOL Light prover on top, then swaps that kernel primitive
#  AT RUNTIME for a different sound derivation — gated, accumulating, with a
#  wrong swap rejected — and keeps proving through the swapped primitive.
#
#  Reversible: applies `candle/kernel_apex.patch` to a backup, runs, restores.
#  Requires a built `cake` (CANDLE_ROOT). Reloads hol.ml (~minutes).
#
#  Usage:  CANDLE_ROOT=~/dev/candle scripts/apex-kernel-swap.sh
# ======================================================================
set -uo pipefail
here="$(cd "$(dirname "$0")" && pwd)"
. "$here/env.sh"

KSRC="$CANDLE_ROOT/candle/kernel.ml"
[ -f "$KSRC" ] || die "no candle kernel at $KSRC"
[ -x "$CANDLE_ROOT/candle/build/cake" ] || die "no cake binary under $CANDLE_ROOT"
FIFO="${PLACE_FIFO:-/tmp/place-apex.fifo}"; LOG="${PLACE_LOG:-/tmp/place-apex.log}"
export PLACE_FIFO="$FIFO" PLACE_LOG="$LOG"

restore(){ [ -f "$KSRC.apexbak" ] && { cp "$KSRC.apexbak" "$KSRC"; rm -f "$KSRC.apexbak"; ok "restored pristine $KSRC"; }; }
trap 'restore' EXIT

say "patching the candle kernel interface (REFL → live sound indirection)"
cp "$KSRC" "$KSRC.apexbak"
( cd "$CANDLE_ROOT" && patch -p1 < "$SVENVS_ROOT/candle/kernel_apex.patch" ) \
  || die "patch failed (kernel.ml moved upstream? regenerate candle/kernel_apex.patch)"

say "starting a fresh Candle server on the re-architected kernel (loads hol.ml)"
pkill -f "cake --candle" 2>/dev/null || true; sleep 1; rm -f "$FIFO"* "$LOG"
CANDLE_ROOT="$CANDLE_ROOT" "$here/place-server.sh"
for _ in $(seq 1 600); do grep -q "val _READY = 1" "$LOG" 2>/dev/null && break; sleep 2; done
grep -q "val _READY = 1" "$LOG" || die "Candle server did not become ready"
ok "full HOL Light prover loaded on the swappable kernel interface"

say "executing the in-process kernel-primitive swap (candle/kernel_swap_demo.ml)"
"$here/place-submit.sh" "$SVENVS_ROOT/candle/kernel_swap_demo.ml" _SVENVS_KSWAP_DONE
grep -aE 'val uses_genesis = ' "$LOG" | tail -1
grep -aE 'val swap_ok = |val bad_ok = ' "$LOG" | tail -2
if grep -aqE 'val verdict = "KERNEL_INPROCESS_SWAP_OK"' "$LOG"; then
  ok "KERNEL_INPROCESS_SWAP_OK — a kernel primitive was swapped under the live prover,"
  ok "gated, the prover kept proving through it, and a wrong swap was rejected."
else die "kernel swap demo did not reach KERNEL_INPROCESS_SWAP_OK"; fi

say "APEX kernel-swap COMPLETE — verified core fixed, kernel interface swapped live"
