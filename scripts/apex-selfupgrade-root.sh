#!/usr/bin/env bash
# THE SELF-UPGRADABLE ROOT cake.S, EXECUTED.
#
# Re-bootstraps an ALTERED cake whose REPL `eval` self-upgrades its OWN compiler
# IN PLACE at a generation boundary (selfUpgrade/cakeml-selfupgrade-root.patch:
# the per-generation dispatch realises repl_upgrade / do_eval_record_gen on the
# running binary — future generations compiled by an upgraded compiler with a
# different register allocator, semantics preserved). Then RUNS it and asserts.
#
# Build route (Layer-B-style, fast/binary path — the existing verified `cake`
# self-compiles the altered compiler's s-expression):
#   1. (done by build-selfupgrade-root.sh) re-translate compiler64ProgTheory
#      with the patch, regenerate cake-sexpr-64;
#   2. self-compile cake.S with the EXISTING verified cake; link -> cake-selfupgrade.
# This script does steps from the regenerated sexpr onward, caches the altered
# binary, runs the REPL demo, and asserts the in-place self-upgrade.
#
# Honest residual: the post-swap compilations leave the unmodified backendProof
# envelope (opt_eval_config_wf pins one compiler_fun); the generalised soundness
# is the svenvs selfUpgrade proofs (tier2.5), the concrete backendProof
# re-composition the documented residual (selfUpgrade/SELFUPGRADE_ROOT.md).
. "$(dirname "$0")/env.sh"
for a in "$@"; do case "$a" in --clean|--quick|--rebuild) : ;; *) die "apex-selfupgrade-root: unknown arg '$a'";; esac; done

CAKE="${CAKE:-$CANDLE_ROOT/candle/build/cake}"
FFI="${CAKE_FFI:-$CANDLE_ROOT/candle/build/basis_ffi.c}"
SEXPR="${SELFUP_SEXPR:-$CAKEMLDIR/compiler/bootstrap/compilation/x64/64/cake-sexpr-64}"
DEMO="$SVENVS_ROOT/candle/selfupgrade_root_demo.repl"
WORK="${TMPDIR:-/tmp}/svenvs-selfupgrade-root"
ALT="$WORK/cake-selfupgrade"

if [ ! -x "$CAKE" ]; then
  warn "SKIP apex-selfupgrade-root: no verified cake at $CAKE (build/fetch it).
  The proof side (selfUpgrade/evalUpgradeOp) and the in-cake demos
  (apex-compiler-cell*) reproduce without this re-bootstrap."
  exit 0
fi
[ -f "$DEMO" ] || die "missing demo $DEMO"
mkdir -p "$WORK"

rebuild=0
for a in "$@"; do [ "$a" = --rebuild ] && rebuild=1; done
if [ ! -x "$ALT" ] && [ "$rebuild" = 0 ]; then
  warn "SKIP apex-selfupgrade-root: the altered self-upgradable cake is not built.
  Build it (heavy, ~1-2h): scripts/build-selfupgrade-root.sh  (re-translate the
  patched compiler + regen sexpr), then re-run this with --rebuild. The proof
  side and the in-cake demos reproduce without the re-bootstrap."
  exit 0
fi
if [ ! -x "$ALT" ] || [ "$rebuild" = 1 ]; then
  [ -f "$SEXPR" ] || die "no altered cake-sexpr-64 at $SEXPR — run scripts/build-selfupgrade-root.sh first (re-translate compiler64ProgTheory with the patch + regen sexpr)"
  say "self-compiling the ALTERED compiler's s-expression with the existing verified cake (~5 min)"
  CML_STACK_SIZE=1000 CML_HEAP_SIZE=6000 "$CAKE" --sexp=true --exclude_prelude=true \
    --skip_type_inference=true --reg_alg=0 < "$SEXPR" > "$WORK/cake.S" 2>"$WORK/sc.err" \
    || { cat "$WORK/sc.err" >&2; die "self-compile failed"; }
  ok "altered cake.S produced ($(wc -l < "$WORK/cake.S") lines)"
  say "assembling + linking the self-upgradable root"
  cc -O2 "$WORK/cake.S" "$FFI" -lm -o "$ALT" 2>"$WORK/link.err" \
    || { cat "$WORK/link.err" >&2; die "link failed"; }
  ok "self-upgradable cake built: $ALT"
fi

say "RUNNING the self-upgradable root — feeding REPL declarations; the compiler upgrades ITSELF in place mid-session"
"$ALT" --repl < "$DEMO" > "$WORK/run.out" 2>&1 || true
sed -n '1,60p' "$WORK/run.out"

assert(){ grep -qaE "$1" "$WORK/run.out" || die "expected evidence missing: /$1/ (see $WORK/run.out)"; ok "$2"; }
assert 'self-upgraded its own compiler IN PLACE at generation' \
       "the running cake announced an IN-PLACE compiler self-upgrade"
assert 'reg_alg := 0' \
       "the upgrade is a genuine compiler change (register allocator switched)"
assert 'RESULT=99' \
       "semantics preserved across the in-place compiler self-upgrade (a=2,b=6,c=10,d=100,e=99)"

say "SELF-UPGRADABLE ROOT RAN — an altered cake.S whose REPL self-upgrades its OWN compiler in place at a generation boundary, executed on the real verified-cake-self-compiled binary; later declarations compiled by the upgraded compiler, output correct"
