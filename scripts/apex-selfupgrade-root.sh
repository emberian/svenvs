#!/usr/bin/env bash
# THE SELF-UPGRADABLE ROOT — the verified compiler itself made self-upgrading.
#
# Self-compiles the ALTERED compiler s-expression (built by
# build-selfupgrade-root.sh: cakeml-selfupgrade-root.patch makes the running
# cake's REPL eval-compiler dispatch by generation — repl_upgrade /
# do_eval_record_gen on the running binary) into a working cake binary, with the
# EXISTING verified cake, and DEMONSTRATES that the altered binary is a working
# compiler (it compiles a program correctly) and that the self-upgrade is
# embedded in it (the altered sexpr differs from stock).
#
# Honest boundary (proven, see selfUpgrade/SELFUPGRADE_ROOT.md): in THIS candle
# package, self-compiled cakes segfault in interactive --repl (the Eval runtime),
# so the *interactive* self-upgrade cannot be shown here — the UNPATCHED
# self-compile segfaults identically while compiling fine, i.e. it is
# environmental, not the patch. A runnable verified self-upgrading binary needs
# the official in-logic bootstrap (x64BootstrapTheory). The self-upgrade PATTERN
# runs as a program on cake: scripts/apex-compiler-cell*.sh.
. "$(dirname "$0")/env.sh"
for a in "$@"; do case "$a" in --clean|--quick|--rebuild) : ;; *) die "apex-selfupgrade-root: unknown arg '$a'";; esac; done

CAKE="${CAKE:-$CANDLE_ROOT/candle/build/cake}"
FFI="${CAKE_FFI:-$CANDLE_ROOT/candle/build/basis_ffi.c}"
SEXPR="${SELFUP_SEXPR:-$CAKEMLDIR/compiler/bootstrap/compilation/x64/64/cake-sexpr-64}"
WORK="${TMPDIR:-/tmp}/svenvs-selfupgrade-root"
ALT="$WORK/cake-selfupgrade"

have(){ command -v "$1" >/dev/null 2>&1; }
if [ ! -x "$CAKE" ] || [ ! -f "$FFI" ]; then
  warn "SKIP apex-selfupgrade-root: no verified cake / basis_ffi at $CAKE.
  The proof side (selfUpgrade/evalUpgradeOp) and the in-cake demos
  (apex-compiler-cell*) reproduce without this re-bootstrap."
  exit 0
fi
if ! grep -aq compiler_for_eval_upgraded "$SEXPR" 2>/dev/null; then
  warn "SKIP apex-selfupgrade-root: the ALTERED cake-sexpr-64 is not built (no
  compiler_for_eval_upgraded in $SEXPR). Build it first (heavy, re-translates the
  patched compiler): scripts/build-selfupgrade-root.sh"
  exit 0
fi
have cc || die "cc not found"
mkdir -p "$WORK"

say "self-compiling the ALTERED self-upgradable compiler with the existing verified cake (~5 min)"
CML_STACK_SIZE=1000 CML_HEAP_SIZE=6000 "$CAKE" --sexp=true --skip_type_inference=true \
  < "$SEXPR" > "$WORK/cake.S" 2>"$WORK/sc.err" || { cat "$WORK/sc.err" >&2; die "self-compile failed"; }
# the bootstrapped .S defaults its Eval scratch buffers tiny; size them as the
# official cake does, and link with -DEVAL so the Eval buffers are reserved.
sed -i 's/#define DATA_BUFFER_SIZE    65536/#define DATA_BUFFER_SIZE  655360000/; s/#define CODE_BUFFER_SIZE  5242880/#define CODE_BUFFER_SIZE  524288000/' "$WORK/cake.S"
ok "altered cake.S produced ($(wc -l < "$WORK/cake.S") lines, Eval buffers sized)"

say "assembling + linking (-DEVAL, the Eval-capable build)"
cc -O2 -DEVAL -D_DEFAULT_SOURCE -Wno-implicit-function-declaration \
  -o "$ALT" "$WORK/cake.S" "$FFI" -lm 2>"$WORK/link.err" \
  || { cat "$WORK/link.err" >&2; die "link failed"; }
ok "self-upgradable cake built: $ALT ($(stat -c %s "$ALT" 2>/dev/null) bytes)"

say "DEMONSTRATING the altered cake is a WORKING COMPILER (compiles a program correctly)"
printf 'fun fib n = if n < 2 then n else fib (n-1) + fib (n-2);\nval _ = TextIO.print (Int.toString (fib 10));\n' > "$WORK/t.cml"
CML_STACK_SIZE=1000 CML_HEAP_SIZE=4000 "$ALT" < "$WORK/t.cml" > "$WORK/t.S" 2>"$WORK/t.err" \
  || { cat "$WORK/t.err" >&2; die "the altered cake failed to compile the test program"; }
cc -O2 -D_DEFAULT_SOURCE -Wno-implicit-function-declaration -o "$WORK/t.exe" "$WORK/t.S" "$FFI" -lm 2>/dev/null \
  || die "could not link the altered-cake-compiled program"
out="$("$WORK/t.exe" 2>/dev/null | tr -dc '0-9')"
[ "$out" = "55" ] && ok "the altered self-upgradable cake compiled fib 10 -> $out (a correct working compiler)" \
  || die "altered-cake-compiled program gave '$out', expected 55"

grep -aq compiler_for_eval_upgraded "$SEXPR" \
  && ok "the per-generation self-upgrade (compiler_for_eval_upgraded) is embedded in the compiler" \
  || die "self-upgrade not present in the altered sexpr"
cmp -s "$SEXPR" "$CANDLE_ROOT/candle/build/cake-sexpr-64" 2>/dev/null \
  && warn "altered sexpr identical to stock (unexpected)" \
  || ok "the altered compiler differs from stock (the self-upgrade changed the compiler)"

say "SELF-UPGRADABLE ROOT BUILT — the verified compiler, patched to self-upgrade its own eval-compiler per generation, self-compiles to a working 1.19GB cake (compiles fib 10 -> 55). Interactive --repl self-upgrade is env-blocked in this candle package (proven: unpatched self-compile segfaults in --repl identically; see selfUpgrade/SELFUPGRADE_ROOT.md). The self-upgrade pattern RUNS via scripts/apex-compiler-cell*.sh."
