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
#  What it touches, and how that is contained:
#   * candle/kernel.ml INSIDE YOUR CANDLE CHECKOUT is patched for the run and
#     restored on exit (any exit). Opt-in (SVENVS_ALLOW_INPLACE=1), and refused
#     if that file already has local edits, so nothing of yours is clobbered.
#     Prefer a throwaway CANDLE_ROOT.
#   * it runs its own private Place (a fresh prover on the patched kernel)
#     under $SVENVS_WORK/place-apex-kswap and stops it on exit; a server you
#     have running elsewhere is never touched.
#
#  Usage:  SVENVS_ALLOW_INPLACE=1 CANDLE_ROOT=~/dev/candle scripts/apex-kernel-swap.sh
# ======================================================================
here="$(cd "$(dirname "$0")" && pwd)"
. "$here/env.sh"
place_use_dir "$SVENVS_WORK/place-apex-kswap"
LOG="$PLACE_LOG"

KSRC="$CANDLE_ROOT/candle/kernel.ml"
[ -f "$KSRC" ] || die "no candle kernel at $KSRC"
[ -x "$CANDLE_ROOT/candle/build/cake" ] || die "no cake binary under $CANDLE_ROOT"
svenvs_confirm_inplace "$CANDLE_ROOT" "candle/kernel.ml" \
  "the prover must load on the re-architected kernel interface for the duration of the run"

restore(){
  "$here/place-stop.sh" >/dev/null 2>&1 || true
  [ -f "$KSRC.apexbak" ] && { cp "$KSRC.apexbak" "$KSRC"; rm -f "$KSRC.apexbak"; ok "restored pristine $KSRC"; }
  return 0
}
trap 'restore' EXIT

say "patching the candle kernel interface (REFL → live sound indirection)"
cp "$KSRC" "$KSRC.apexbak"
( cd "$CANDLE_ROOT" && patch -p1 < "$SVENVS_ROOT/candle/kernel_apex.patch" ) \
  || die "patch failed (kernel.ml moved upstream? regenerate candle/kernel_apex.patch)"

say "starting a fresh Candle server on the re-architected kernel (loads hol.ml)"
"$here/place-server.sh" --restart
place_wait_ready
ok "full HOL Light prover loaded on the swappable kernel interface"

say "executing the in-process kernel-primitive swap"
KSWAP_ML="$PLACE_DIR/kernel_swap_demo.ml"
cat > "$KSWAP_ML" <<'EOF'
let _ = (_apex_refl_uses := 0);;
let T1 = ARITH_RULE `2 + 2 = 4`;;
let uses_genesis = !_apex_refl_uses;;
let refl_alt tm = Kernel.TRANS (Kernel.REFL tm) (Kernel.REFL tm);;
let swap_ok = apex_swap_refl refl_alt [`x:num`; `2 + 2`; `T`; `p /\ q`];;
let swaps_after = !_apex_refl_swaps;;
let _ = (_apex_refl_uses := 0);;
let T2 = ARITH_RULE `40 + 2 = 42`;;
let uses_after_swap = !_apex_refl_uses;;
let refl_bad tm = Kernel.REFL `T`;;
let bad_ok = apex_swap_refl refl_bad [`x:num`; `2 + 2`];;
let T3 = ARITH_RULE `1 + 1 = 2`;;
let verdict =
  if uses_genesis > 0 && swap_ok && swaps_after = 1 && uses_after_swap > 0
     && not bad_ok && concl T2 = `40 + 2 = 42` && concl T3 = `1 + 1 = 2`
  then "KERNEL_INPROCESS_SWAP_OK" else "FAILED";;
EOF
"$here/place-submit.sh" "$KSWAP_ML" _SVENVS_KSWAP_DONE >/dev/null
grep -aE 'val uses_genesis = ' "$LOG" | tail -1 || true
grep -aE 'val swap_ok = |val bad_ok = ' "$LOG" | tail -2 || true
if grep -aqE 'val verdict = "KERNEL_INPROCESS_SWAP_OK"' "$LOG"; then
  ok "KERNEL_INPROCESS_SWAP_OK — a kernel primitive was swapped under the live prover,"
  ok "gated, the prover kept proving through it, and a wrong swap was rejected."
else die "kernel swap demo did not reach KERNEL_INPROCESS_SWAP_OK (see $LOG)"; fi

say "APEX kernel-swap COMPLETE — verified core fixed, kernel interface swapped live"
