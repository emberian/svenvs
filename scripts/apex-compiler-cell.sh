#!/usr/bin/env bash
# RUNTIME IMAGE of the verified per-generation compiler self-upgrade.
#
# Compiles candle/compiler_cell_upgrade.cml with the REAL verified `cake`
# compiler (to native x86-64), links it with basis_ffi.c, RUNS it, and asserts
# the evidence — so the structure proved in selfUpgrade/evalUpgradeOpScript.sml
# (the per-generation compiler map `cmap` = g2c, the `agree` gate =
# compiler_agrees, `upgrade` = repl_upgrade) is shown EXECUTING, not just proved:
#   - an in-place compiler upgrade keeps the OBSERVABLE identical while the
#     compiled output improves (gen 0: 15 -> gen 1: 10 for the same source);
#   - an earlier generation keeps its own compiler (repl_upgrade_no_op_below);
#   - a non-agreeing claimed compilation is REJECTED by the gate (semantics
#     protected) — the do_eval_record_gen / compiler_agrees discipline;
#   - upgrades ACCUMULATE (gen 2 gets a third compiler), path-dependent.
#
# Auto-SKIPs (exit 0) with instructions if the verified cake binary is absent.
. "$(dirname "$0")/env.sh"

for a in "$@"; do case "$a" in --clean|--quick) : ;; *) die "apex-compiler-cell: unknown arg '$a'";; esac; done

CAKE="${CAKE:-$CANDLE_ROOT/candle/build/cake}"
FFI="${CAKE_FFI:-$CANDLE_ROOT/candle/build/basis_ffi.c}"
SRC="$SVENVS_ROOT/candle/compiler_cell_upgrade.cml"
WORK="${TMPDIR:-/tmp}/svenvs-ccu"

if [ ! -x "$CAKE" ]; then
  warn "SKIP apex-compiler-cell: no verified cake binary at $CAKE.
  Build/fetch it (x86_64 Linux): cd \$CANDLE_ROOT && ./build-instructions.sh
  (downloads the official verified cake-x64-64). The proof side
  (selfUpgrade/evalUpgradeOpScript.sml) reproduces without a running cake."
  exit 0
fi
[ -f "$SRC" ] || die "missing $SRC"
[ -f "$FFI" ] || die "missing basis_ffi.c at $FFI (set CAKE_FFI)"
have cc || die "cc not found (need a C compiler to link the cake output)"

mkdir -p "$WORK"
say "apex-compiler-cell: compiling the upgrade demo with the verified cake"
if ! "$CAKE" < "$SRC" > "$WORK/ccu.S" 2> "$WORK/ccu.cerr"; then
  cat "$WORK/ccu.cerr" >&2; die "cake failed to compile $SRC"
fi
ok "cake compiled compiler_cell_upgrade.cml -> $(wc -l < "$WORK/ccu.S") lines of native asm"

say "apex-compiler-cell: linking with basis_ffi.c"
cc -o "$WORK/ccu" "$WORK/ccu.S" "$FFI" -lm 2> "$WORK/ccu.lerr" \
  || { cat "$WORK/ccu.lerr" >&2; die "link failed"; }

say "apex-compiler-cell: RUNNING the proof-gated upgrade loop on native cake output"
"$WORK/ccu" > "$WORK/ccu.out" 2>&1 || die "the demo exited nonzero — see $WORK/ccu.out"
cat "$WORK/ccu.out"

# --- assert the evidence -----------------------------------------------------
assert(){ grep -qaE "$1" "$WORK/ccu.out" || die "expected evidence missing: /$1/ (see $WORK/ccu.out)"; ok "$2"; }
assert 'gen=0 src=5 .* compiled=15 gate=ACCEPT'        "gen 0 dispatches compiler A, gate accepts"
assert 'UPGRADE: install compiler B'                   "in-place upgrade to B installed"
assert 'gen=1 src=5 .* compiled=10 gate=ACCEPT'        "gen 1 dispatches improved compiler B (cheaper), gate accepts"
assert 'gen=0 src=5 .* compiled=15 gate=ACCEPT'        "earlier generation 0 still dispatches A (history preserved)"
assert 'claim=999 gate=REJECT'                         "non-agreeing compilation REJECTED by the gate"
assert 'UPGRADE: install compiler C'                   "second upgrade accumulates (gen 2)"
assert 'observable preserved across upgrades.*: YES'   "OBSERVABLE preserved across every in-place upgrade"
assert 'accepted=5 rejected=1'                         "5 gated evals accepted, 1 rejected"
assert 'COMPILER_CELL_UPGRADE_OK'                      "sentinel: the running upgrade loop is sound"

say "APEX COMPILER-CELL RAN — the verified per-generation compiler self-upgrade (repl_upgrade / do_eval_record_gen / compiler_agrees) executes on the real cake binary, in place, gated, accumulating; observable preserved, bad swaps rejected"
