#!/usr/bin/env bash
# Build the ALTERED self-upgradable compiler s-expression (steps 1-2 of the
# re-bootstrap; see selfUpgrade/SELFUPGRADE_ROOT.md). Applies
# selfUpgrade/cakeml-selfupgrade-root.patch to $CAKEMLDIR, re-translates the
# patched compiler program, and regenerates cake-sexpr-64. Heavy: re-translating
# the bootstrap *Prog chain is ~1-2h on a many-core box; the sexpr regen a few
# minutes. Then run scripts/apex-selfupgrade-root.sh to self-compile + RUN it.
#
# Idempotent-ish: skips re-applying the patch if already present.
. "$(dirname "$0")/env.sh"

PATCH="$SVENVS_ROOT/selfUpgrade/cakeml-selfupgrade-root.patch"
PROG="$CAKEMLDIR/compiler/bootstrap/translation/compiler64ProgScript.sml"
[ -f "$PATCH" ] || die "missing $PATCH"
[ -f "$PROG" ]  || die "missing $PROG (is CAKEMLDIR=$CAKEMLDIR a CakeML checkout?)"

if grep -qa compiler_for_eval_upgraded "$PROG"; then
  ok "patch already present in $PROG"
else
  say "applying cakeml-selfupgrade-root.patch to \$CAKEMLDIR"
  ( cd "$CAKEMLDIR" && patch -p1 < "$PATCH" ) || die "patch failed — check pin (ac654a0a3)"
  ok "patch applied"
fi

say "re-translating the patched compiler program (chain tail; ~1-2h if backend timestamps moved)"
( cd "$CAKEMLDIR/compiler/bootstrap/translation" \
    && CAKEMLDIR="$CAKEMLDIR" "$HOLMAKE" $SVENVS_HM_FLAGS -j4 compiler64ProgTheory.uo ) \
  || die "re-translation failed (see the Holmake output)"
ok "compiler64ProgTheory re-translated"

say "regenerating the altered cake-sexpr-64"
( cd "$CAKEMLDIR/compiler/bootstrap/compilation/x64/64" \
    && rm -f cake-sexpr-64 \
    && CAKEMLDIR="$CAKEMLDIR" "$HOLMAKE" $SVENVS_HM_FLAGS -j4 cake-sexpr-64 ) \
  || die "sexpr regeneration failed"
[ -f "$CAKEMLDIR/compiler/bootstrap/compilation/x64/64/cake-sexpr-64" ] \
  || die "cake-sexpr-64 not produced"
ok "altered cake-sexpr-64 produced"

say "BUILT the altered compiler s-expression. Next: scripts/apex-selfupgrade-root.sh (self-compile with the existing verified cake, link, RUN the in-place self-upgrade demo)."
