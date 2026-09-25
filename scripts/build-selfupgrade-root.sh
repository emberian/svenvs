#!/usr/bin/env bash
# Build the ALTERED self-upgradable compiler s-expression (steps 1-2 of the
# re-bootstrap; see selfUpgrade/SELFUPGRADE_ROOT.md). Applies
# selfUpgrade/cakeml-selfupgrade-root.patch to $CAKEMLDIR, re-translates the
# patched compiler program, and regenerates cake-sexpr-64. Heavy: re-translating
# the bootstrap *Prog chain is ~1-2h on a many-core box; the sexpr regen a few
# minutes. Then run scripts/apex-selfupgrade-root.sh to self-compile + RUN it.
#
# This EDITS YOUR CAKEML CHECKOUT (the patch stays applied so the altered sexpr
# can be rebuilt incrementally). It is opt-in (SVENVS_ALLOW_INPLACE=1), refuses
# a checkout whose touched files already carry local edits, and is reversed by
#   scripts/build-selfupgrade-root.sh --undo
# Prefer a throwaway CAKEMLDIR. Idempotent: skips the patch if already present.
. "$(dirname "$0")/env.sh"

PATCH="$SVENVS_ROOT/selfUpgrade/cakeml-selfupgrade-root.patch"
PROG_REL="compiler/bootstrap/translation/compiler64ProgScript.sml"
PROG="$CAKEMLDIR/$PROG_REL"
SEXDIR_REL="compiler/bootstrap/compilation/x64/64"
SEXDIR="$CAKEMLDIR/$SEXDIR_REL"
[ -f "$PATCH" ] || die "missing $PATCH"
[ -f "$PROG" ]  || die "missing $PROG (is CAKEMLDIR=$CAKEMLDIR a CakeML checkout?)"

case "${1:-}" in
  --undo)
    grep -qa compiler_for_eval_upgraded "$PROG" || { ok "patch not present in $PROG; nothing to undo"; exit 0; }
    svenvs_confirm_inplace "$CAKEMLDIR" "$SEXDIR_REL/Holmakefile" "reversing the self-upgrade patch"
    ( cd "$CAKEMLDIR" && patch -R -p1 --dry-run < "$PATCH" >/dev/null && patch -R -p1 < "$PATCH" ) \
      || die "could not reverse the patch cleanly (the file drifted?); inspect $PROG by hand"
    ok "reversed cakeml-selfupgrade-root.patch in $CAKEMLDIR (the altered cake-sexpr-64, if built, is now stale)"
    exit 0 ;;
  "") ;;
  *) die "build-selfupgrade-root.sh: unknown arg '$1' (--undo)" ;;
esac

if grep -qa compiler_for_eval_upgraded "$PROG"; then
  ok "patch already present in $PROG (scripts/build-selfupgrade-root.sh --undo reverses it)"
  svenvs_confirm_inplace "$CAKEMLDIR" "$SEXDIR_REL/Holmakefile" "regenerating the altered sexpr"
else
  svenvs_confirm_inplace "$CAKEMLDIR" "$PROG_REL $SEXDIR_REL/Holmakefile" \
    "the self-upgrade patch must be applied to the compiler's translation source"
  say "applying cakeml-selfupgrade-root.patch to \$CAKEMLDIR"
  ( cd "$CAKEMLDIR" && patch -p1 < "$PATCH" ) || die "patch failed — check pin ($SVENVS_CAKEML_COMMIT)"
  ok "patch applied (reverse with: scripts/build-selfupgrade-root.sh --undo)"
fi

say "re-translating the patched compiler program (chain tail; ~1-2h if backend timestamps moved)"
( cd "$CAKEMLDIR/compiler/bootstrap/translation" \
    && CAKEMLDIR="$CAKEMLDIR" "$HOLMAKE" $SVENVS_HM_FLAGS -j4 compiler64ProgTheory.uo ) \
  || die "re-translation failed (see the Holmake output)"
ok "compiler64ProgTheory re-translated"

say "regenerating the altered cake-sexpr-64"
# The x64/64 dir's HOLHEAP (cake_compile_heap) pulls the heavy in-logic
# eval_cake_compile machinery, which has a latent broken HOL trace here; the
# sexpr only needs compiler64Prog printed, so build it against the base heap.
# The Holmakefile edit is temporary and restored whatever happens.
cp "$SEXDIR/Holmakefile" "$SEXDIR/Holmakefile.svenvs.bak"
trap 'mv -f "$SEXDIR/Holmakefile.svenvs.bak" "$SEXDIR/Holmakefile" 2>/dev/null || true' EXIT
sed -i 's@^HOLHEAP = .*cake_compile_heap@# HOLHEAP disabled by build-selfupgrade-root.sh (broken trace in cake_compile_heap)@' "$SEXDIR/Holmakefile"
rc=0
( cd "$SEXDIR" && rm -f cake-sexpr-64 \
    && CAKEMLDIR="$CAKEMLDIR" "$HOLMAKE" $SVENVS_HM_FLAGS -j1 cake-sexpr-64 ) || rc=$?
mv -f "$SEXDIR/Holmakefile.svenvs.bak" "$SEXDIR/Holmakefile"   # always restore
trap - EXIT
[ "$rc" = 0 ] || die "sexpr regeneration failed"
[ -f "$SEXDIR/cake-sexpr-64" ] || die "cake-sexpr-64 not produced"
ok "altered cake-sexpr-64 produced"

say "BUILT the altered compiler s-expression. Next: scripts/apex-selfupgrade-root.sh (self-compile with the existing verified cake, link, RUN the in-place self-upgrade demo)."
