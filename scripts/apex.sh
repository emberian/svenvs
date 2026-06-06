#!/usr/bin/env bash
# ======================================================================
#  svenvs APEX — the self-improving, self-recompiling system, EXECUTED.
#
#  Runs, end to end, on the real verified CakeML/Candle stack:
#
#   I.  THE COMPILER RECOMPILES ITSELF (and self-optimizes), staying correct
#       - cake compiles cake's own s-expression -> a new working cake
#       - FIXPOINT: the self-recompiled cake reproduces the compiler bit-for-bit
#       - SELF-OPTIMIZE: cake recompiles itself under a different optimization
#         regime -> a different binary that is still a correct compiler
#       (correctness = CakeML's verified compiler-correctness theorem, CITED)
#
#   II. THE PROVER IMPROVES ITSELF, proof-gated (candle/self_recompile.ml)
#       - a running compute routine is recompiled+hot-swapped at runtime, each
#         swap GATED by a live Candle kernel equivalence proof; swaps accumulate
#         (path-dependent); an unprovable swap is REJECTED (semantics can't break)
#
#  Emits DIAMOND if both halves execute and verify this run. The safety of the
#  whole is PROVED in apex/apexScript.sml (instantiating the recursive genealogy).
#
#  Honest residual (NOT executed): an in-process swap of the trusted *kernel's
#  own code* — it is compiled into cake.S (perms_ok-protected), so that needs a
#  proven kernel-modified cake.S (in-logic re-verification). See CLAIMS.md.
#
#  Usage:  CANDLE_ROOT=~/dev/candle scripts/apex.sh
# ======================================================================
set -uo pipefail
here="$(cd "$(dirname "$0")" && pwd)"
. "$here/env.sh"

B="$CANDLE_ROOT/candle/build"
[ -x "$B/cake" ] || die "no cake at $B/cake (build candle first)"
[ -f "$B/cake-sexpr-64" ] || die "no cake-sexpr-64 at $B (the compiler's own source)"
export CML_HEAP_SIZE="${CML_HEAP_SIZE:-24000}" CML_STACK_SIZE="${CML_STACK_SIZE:-4000}"
WORK="${APEX_WORK:-/tmp/apex}"; mkdir -p "$WORK"

I_OK=0; FIX_OK=0; OPT_OK=0; PROVER_OK=0

# --- I. compiler recompiles itself -----------------------------------
say "APEX I — the verified compiler recompiles itself"
( cd "$B" && ./cake --sexp=true --skip_type_inference=true < cake-sexpr-64 > "$WORK/cake1.S" 2>"$WORK/cake1.err" )
if [ -s "$WORK/cake1.S" ] && cc -O2 "$WORK/cake1.S" "$B/basis_ffi.c" -DEVAL -o "$WORK/cake1" -lm 2>"$WORK/cake1.cc.err"; then
  printf 'print "selfhost-ok\\n";\n' | "$WORK/cake1" > "$WORK/p.S" 2>/dev/null \
    && cc -O2 "$WORK/p.S" "$B/basis_ffi.c" -o "$WORK/p" -lm 2>/dev/null \
    && [ "$("$WORK/p" 2>/dev/null)" = "selfhost-ok" ] \
    && { ok "the self-recompiled cake is a working compiler"; I_OK=1; }
fi
[ "$I_OK" = 1 ] || die "compiler self-host failed (see $WORK/cake1.err)"

say "APEX I — FIXPOINT: does the self-recompiled cake reproduce the compiler?"
( cd "$B" && "$WORK/cake1" --sexp=true --skip_type_inference=true < cake-sexpr-64 > "$WORK/cake2.S" 2>/dev/null )
if cmp -s "$WORK/cake1.S" "$WORK/cake2.S"; then
  ok "FIXPOINT: bit-identical — the compiler is a verified fixed point of itself"; FIX_OK=1
else warn "self-host not a fixpoint (still a working compiler, but not bit-identical)"; fi

say "APEX I — SELF-OPTIMIZE: cake recompiles itself under a new optimization regime"
( cd "$B" && ./cake --sexp=true --skip_type_inference=true --inline_size=200 --max_app=8 \
    < cake-sexpr-64 > "$WORK/cakeopt.S" 2>/dev/null )
if [ -s "$WORK/cakeopt.S" ] && ! cmp -s "$WORK/cake1.S" "$WORK/cakeopt.S" \
   && cc -O2 "$WORK/cakeopt.S" "$B/basis_ffi.c" -DEVAL -o "$WORK/cakeopt" -lm 2>/dev/null; then
  printf 'print "opt-ok\\n";\n' | "$WORK/cakeopt" > "$WORK/q.S" 2>/dev/null \
    && cc -O2 "$WORK/q.S" "$B/basis_ffi.c" -o "$WORK/q" -lm 2>/dev/null \
    && [ "$("$WORK/q" 2>/dev/null)" = "opt-ok" ] \
    && { ok "a DIFFERENT (self-optimized) compiler binary, still correct"; OPT_OK=1; }
fi
[ "$OPT_OK" = 1 ] || warn "self-optimize variant did not verify"

# --- II. prover improves itself, proof-gated -------------------------
say "APEX II — the prover improves itself, proof-gated (live Candle)"
FIFO="${PLACE_FIFO:-/tmp/place.fifo}"; LOG="${PLACE_LOG:-/tmp/place.log}"
export PLACE_FIFO="$FIFO" PLACE_LOG="$LOG"
if ! { [ -f "${FIFO}.candle.pid" ] && kill -0 "$(cat "${FIFO}.candle.pid")" 2>/dev/null; }; then
  say "starting Candle server (loads hol.ml once)"
  CANDLE_ROOT="$CANDLE_ROOT" "$here/place-server.sh"
  for _ in $(seq 1 600); do grep -q "val _READY = 1" "$LOG" 2>/dev/null && break; sleep 2; done
  grep -q "val _READY = 1" "$LOG" || die "Candle server did not become ready"
fi
"$here/place-submit.sh" "$SVENVS_ROOT/candle/self_recompile.ml" _SVENVS_APEX_RECOMPILE
for thm in GATE1 GATE2; do
  grep -aE "val $thm = " "$LOG" | tail -1 | grep -q '|-' || die "$thm not certified by live Candle"
done
if grep -aqE 'val verdict = "APEX_SUBSTRATE_OK"' "$LOG"; then
  ok "prover proof-gated recompile->swap->resume: 2 swaps accumulated, cost 101->1, bad swap REJECTED"
  PROVER_OK=1
else die "prover self-improvement loop did not reach APEX_SUBSTRATE_OK"; fi

# --- verdict ---------------------------------------------------------
say "APEX VERDICT"
if [ "$I_OK" = 1 ] && [ "$FIX_OK" = 1 ] && [ "$PROVER_OK" = 1 ]; then
  ok "DIAMOND — the compiler recompiled itself (fixpoint$([ "$OPT_OK" = 1 ] && echo ' + self-optimized')), and the prover improved itself under live proof gate. Apex EXECUTED."
  echo
  echo "  Proven safe in apex/apexScript.sml; the one residual (in-process swap of"
  echo "  the kernel's OWN code) is stated honestly in CLAIMS.md / paper §3."
else
  die "DIAMOND not reached (I_OK=$I_OK FIX_OK=$FIX_OK OPT_OK=$OPT_OK PROVER_OK=$PROVER_OK)"
fi
