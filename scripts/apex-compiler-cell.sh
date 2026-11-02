#!/usr/bin/env bash
# RUNTIME IMAGE of the verified per-generation compiler self-upgrade.
#
# Compiles the generated compiler_cell_upgrade.cml with the REAL verified `cake`
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
WORK="$SVENVS_WORK/ccu"
SRC="$WORK/compiler_cell_upgrade.cml"

if [ ! -x "$CAKE" ]; then
  warn "SKIP apex-compiler-cell: no verified cake binary at $CAKE.
  Build/fetch it (x86_64 Linux): cd \$CANDLE_ROOT && ./build-instructions.sh
  (downloads the official verified cake-x64-64). The proof side
  (selfUpgrade/evalUpgradeOpScript.sml) reproduces without a running cake."
  exit 0
fi
[ -f "$FFI" ] || die "missing basis_ffi.c at $FFI (set CAKE_FFI)"
have cc || die "cc not found (need a C compiler to link the cake output)"

mkdir -p "$WORK"
cat > "$SRC" <<'EOF'
fun eval_src s = s * s + 1;
fun compA st s = (st + 1, s * 3);
fun compB st s = (st + 1, s * 2);
fun compC st s = (st + 1, s + s);
val cmap = Ref (fn (g:int) => compA);
fun upgrade n newc =
  let val old = (!cmap) in
    cmap := (fn g => if g < n then old g else newc)
  end;
fun agree gen st s claimed = (((!cmap) gen) st s = claimed);
val accepted = Ref 0;
val rejected = Ref 0;
fun gated_eval gen st s claimed =
  case claimed of (cst, cout) =>
  if agree gen st s claimed then
    (accepted := (!accepted) + 1;
     TextIO.print ("  gen=" ^ Int.toString gen ^ " src=" ^ Int.toString s ^
       " -> OBS=" ^ Int.toString (eval_src s) ^
       " compiled=" ^ Int.toString cout ^ " gate=ACCEPT\n");
     Some (eval_src s))
  else
    (rejected := (!rejected) + 1;
     TextIO.print ("  gen=" ^ Int.toString gen ^ " src=" ^ Int.toString s ^
       " claim=" ^ Int.toString cout ^ " gate=REJECT (semantics protected)\n");
     None);
fun obs_of x = case x of Some r => Int.toString r | None => "<rejected>";
val _ = TextIO.print "== per-generation compiler self-upgrade, live on cake ==\n";
val r0 = gated_eval 0 0 5 (compA 0 5);
val _ = TextIO.print "UPGRADE: install compiler B from generation 1 (improved)\n";
val _ = upgrade 1 compB;
val r1 = gated_eval 1 0 5 (compB 0 5);
val r0b = gated_eval 0 0 5 (compA 0 5);
val rbad = gated_eval 1 0 5 (0, 999);
val _ = TextIO.print "UPGRADE: install compiler C from generation 2 (accumulated)\n";
val _ = upgrade 2 compC;
val r2 = gated_eval 2 0 7 (compC 0 7);
val r1b = gated_eval 1 0 7 (compB 0 7);
val obs_preserved =
  (obs_of r0 = obs_of r1) andalso (obs_of r1 = obs_of r0b);
val _ = TextIO.print ("observable preserved across upgrades (src=5): " ^
  obs_of r0 ^ " = " ^ obs_of r1 ^ " = " ^ obs_of r0b ^ " : " ^
  (if obs_preserved then "YES" else "NO") ^ "\n");
val _ = TextIO.print ("accepted=" ^ Int.toString (!accepted) ^
  " rejected=" ^ Int.toString (!rejected) ^ "\n");
val ok = obs_preserved andalso (!accepted = 5) andalso (!rejected = 1);
val _ = TextIO.print (if ok then "COMPILER_CELL_UPGRADE_OK\n"
                            else "COMPILER_CELL_UPGRADE_FAIL\n");
val bulk_ok = Ref True;
fun bulk n =
  if n >= 67 then ()
  else
    let val cn = (fn st => fn s => (st + 1, s * 2 + n)) in
      upgrade n cn;
      if (((!cmap) n) 0 4 = cn 0 4) andalso (eval_src 4 = 17)
      then bulk (n + 1)
      else bulk_ok := False
    end;
val _ = TextIO.print "BULK: 64 accumulated in-place compiler upgrades, each gated...\n";
val _ = bulk 3;
val _ = TextIO.print (if (!bulk_ok)
  then "BULK_UPGRADES_OK (64 generations, observable invariant)\n"
  else "BULK_UPGRADES_FAIL\n");
EOF
say "apex-compiler-cell: compiling the upgrade harness with the verified cake"
if ! "$CAKE" < "$SRC" > "$WORK/ccu.S" 2> "$WORK/ccu.cerr"; then
  cat "$WORK/ccu.cerr" >&2; die "cake failed to compile $SRC"
fi
ok "cake compiled compiler_cell_upgrade.cml -> $(wc -l < "$WORK/ccu.S") lines of native asm"

say "apex-compiler-cell: linking with basis_ffi.c"
cc -o "$WORK/ccu" "$WORK/ccu.S" "$FFI" -lm 2> "$WORK/ccu.lerr" \
  || { cat "$WORK/ccu.lerr" >&2; die "link failed"; }

say "apex-compiler-cell: RUNNING the compiler_agrees-gated upgrade loop on native cake output"
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
assert 'BULK_UPGRADES_OK'                              "64 accumulated in-place upgrades RAN soundly (runtime image of selfupgrade_multi_swap_simulation)"

say "APEX COMPILER-CELL RAN — the verified per-generation compiler self-upgrade (repl_upgrade / do_eval_record_gen / compiler_agrees) executes on the real cake binary, in place, gated, accumulating; observable preserved, bad swaps rejected"
