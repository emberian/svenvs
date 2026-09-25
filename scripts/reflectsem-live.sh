#!/usr/bin/env bash
# reflectsem, end to end, into a live Candle kernel:
#   build fueledSem/fueledBridge -> check_fueled -> export datatypes +
#   functions (HOL4 -> HOL Light script) -> private place-server -> load the
#   45 datatypes -> load the function cone -> gate smoke test (and, with
#   --ouroboros, one gated self-fed ouroboros generation) -> print the
#   kernel's verdict lines -> stop the server.
#
#   scripts/reflectsem-live.sh [--ouroboros] [--keep-server]
#
# Needs HOL4 + a built CakeML (semantics, semantics/ffi, misc/cakeml-heap,
# basis/pure) and the Candle binary (scripts/env.sh locations). Every wait
# is bounded; every failure is loud and stops the run.
. "$(dirname "$0")/env.sh"

OURO=0; KEEP=0
for a in "$@"; do
  case "$a" in
    --ouroboros) OURO=1 ;;
    --keep-server) KEEP=1 ;;
    *) die "reflectsem-live.sh: unknown arg '$a' (--ouroboros | --keep-server)" ;;
  esac
done

require_hol4
RS="$SVENVS_ROOT/reflectsem"
export REFLECTSEM_OUT_DIR="${REFLECTSEM_OUT_DIR:-$SVENVS_WORK/reflectsem}"
mkdir -p "$REFLECTSEM_OUT_DIR"
LOG="$SVENVS_LOGS/reflectsem-live"; mkdir -p "$LOG"
tick(){ date +%s; }
T0=$(tick)

# ---- 1. build + check ------------------------------------------------------
say "building reflectsem (fueledSem + fueledBridge)"
build=( "$HOLMAKE" $SVENVS_HM_FLAGS )
have swarm-build && build=( swarm-build "${build[@]}" )
( cd "$RS" && CAKEMLDIR="$CAKEMLDIR" "${build[@]}" ) > "$LOG/build.log" 2>&1 \
  || { tail -30 "$LOG/build.log"; die "reflectsem build failed (see $LOG/build.log)"; }
ok "built ($(( $(tick) - T0 ))s)"

run_hol(){  # run_hol <script.sml> <log>: from CakeML semantics, so paths resolve
  ( cd "$CAKEMLDIR/semantics" && SVENVS_ROOT="$SVENVS_ROOT" CAKEMLDIR="$CAKEMLDIR" \
      "$HOL" < "$1" ) > "$2" 2>&1
}
run_hol "$RS/check_fueled.sml" "$LOG/check_fueled.log"
grep -q '^CHECK_FUELED_OK' "$LOG/check_fueled.log" || die "check_fueled did not print CHECK_FUELED_OK (see $LOG/check_fueled.log)"
ok "CHECK_FUELED_OK"

# ---- 2. export ---------------------------------------------------------------
say "exporting HOL Light script into $REFLECTSEM_OUT_DIR"
run_hol "$RS/export_datatypes.sml" "$LOG/export_datatypes.log" \
  || die "export_datatypes failed (see $LOG/export_datatypes.log)"
grep -a '^EXPORT_DATATYPES_OK' "$LOG/export_datatypes.log" || die "export_datatypes not OK (see $LOG/export_datatypes.log)"
run_hol "$RS/export_functions.sml" "$LOG/export_functions.log" \
  || { grep -a '^EXPORT_FAIL' "$LOG/export_functions.log"; die "export_functions failed (see $LOG/export_functions.log)"; }
grep -a '^EXPORT_FUNCTIONS_OK' "$LOG/export_functions.log" || die "export_functions not OK"
DT="$REFLECTSEM_OUT_DIR/reflectsem_datatypes.ml"; FN="$REFLECTSEM_OUT_DIR/reflectsem_functions.ml"
N_DT=$(grep -c 'define_type' "$DT" || true); N_FN=$(grep -c '^let [A-Za-z_0-9]*_def = ' "$FN" || true)
ok "exported $N_DT define_types, $N_FN clause theorems"

# ---- 3. private Candle server -------------------------------------------------
place_use_dir "${RS_PLACE_DIR:-$SVENVS_WORK/reflectsem-place}"
[ "$KEEP" = 1 ] || trap '"$SVENVS_ROOT/scripts/place-stop.sh" >/dev/null 2>&1 || true' EXIT
"$SVENVS_ROOT/scripts/place-stop.sh" >/dev/null 2>&1 || true
T=$(tick)
"$SVENVS_ROOT/scripts/place-server.sh" >/dev/null
place_wait_ready
ok "Candle server ready under $PLACE_DIR ($(( $(tick) - T ))s)"

# submit <file> <SENTINEL> <tries> <out>: bounded; the kernel's own output
# for the submission lands in <out>; any OCaml/HOL error in it is fatal
submit(){
  local f="$1" s="$2" tries="$3" out="$4"
  PLACE_SUBMIT_TRIES="$tries" "$SVENVS_ROOT/scripts/place-submit.sh" "$f" "$s" \
    | sed 's/\x1b\[[0-9;]*m//g' > "$out" || die "[$s] did not complete (see $out, $PLACE_LOG)"
  if grep -a -n 'EXCEPTION\|ERROR:\|Parsing failed' "$out" | head -5 | grep -q .; then
    { grep -a -n -A3 'EXCEPTION\|ERROR:\|Parsing failed' "$out" || true; } | head -20
    die "[$s] the kernel reported errors (see $out)"
  fi
}

# ---- 4. datatypes, functions ------------------------------------------------
T=$(tick); submit "$DT" RS_DT_LOADED 1800 "$LOG/datatypes.out"
got=$(grep -a -c '_DT = ' "$LOG/datatypes.out" || true)
[ "$got" = "$N_DT" ] || die "only $got of $N_DT datatypes echoed (see $LOG/datatypes.out)"
{ grep -a 'RS_CASE_FALLBACK' "$LOG/datatypes.out" || true; } | sed 's/^/  note: /'
ok "$got datatypes defined in the kernel ($(( $(tick) - T ))s)"

T=$(tick); submit "$FN" RS_FN_LOADED 1800 "$LOG/functions.out"
got=$(grep -a -c 'val [A-Za-z_0-9]*_def = ' "$LOG/functions.out" || true)
grep -a -q 'val eval_n_def = |-' "$LOG/functions.out" || die "eval_n_def was not proved (see $LOG/functions.out)"
ok "$got definitions/clause theorems in the kernel, eval_n_def included ($(( $(tick) - T ))s)"

# ---- 5. gate smoke test -----------------------------------------------------------
T=$(tick); submit "$SVENVS_ROOT/candle/reflectsem_gate_smoke.ml" RS_SMOKE_OK 300 "$LOG/smoke.out"
grep -a -q 'RS_SMOKE_VERDICT = "RS_SMOKE_OK' "$LOG/smoke.out" || die "smoke verdict missing (see $LOG/smoke.out)"
say "kernel verdict lines (smoke, $(( $(tick) - T ))s)"
awk '/val rs_thm[0-9]* = \|-/{p=1} p{print} /: thm$/{p=0}' "$LOG/smoke.out"
grep -a 'RS_SMOKE_VERDICT\|val RS_SMOKE_OK' "$LOG/smoke.out"

# ---- 6. optional: one ouroboros generation ---------------------------------------
if [ "$OURO" = 1 ]; then
  T=$(tick); start=$(wc -c < "$PLACE_LOG")
  PLACE_SUBMIT_TRIES=900 "$SVENVS_ROOT/scripts/place-submit.sh" "$SVENVS_ROOT/candle/ouroboros.ml" OURO_DONE \
    > /dev/null || die "ouroboros submission did not complete (see $PLACE_LOG)"
  # the self-fed declarations run when the REPL next reads: wait for them
  for _ in $(seq 1 300); do
    tail -c +$((start + 1)) "$PLACE_LOG" | grep -aq 'val ouro_verdict' && break
    place_alive || die "the Candle server died during the ouroboros run"
    sleep 2
  done
  tail -c +$((start + 1)) "$PLACE_LOG" | sed 's/\x1b\[[0-9;]*m//g' > "$LOG/ouroboros.out"
  { grep -a -n -A3 'EXCEPTION\|ERROR:\|Parsing failed' "$LOG/ouroboros.out" || true; } | head -20
  say "kernel verdict lines (ouroboros, $(( $(tick) - T ))s)"
  grep -a 'val ouro_cand_src\|val ouro_bad_src\|val ouro_gate_ok\|val ouro_reject_ok\|val ouro_native_out\|val ouro_verdict' "$LOG/ouroboros.out"
  grep -a -q 'val ouro_verdict = "OUROBOROS_ONE_GEN_OK' "$LOG/ouroboros.out" || die "no OUROBOROS_ONE_GEN_OK verdict (see $LOG/ouroboros.out)"
fi

ok "reflectsem live run complete ($(( $(tick) - T0 ))s total); logs in $LOG"
