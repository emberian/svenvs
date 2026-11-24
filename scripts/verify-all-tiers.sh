#!/usr/bin/env bash
# Build every tier, then check the ledger with zero skips.
#
# Needs HOL4, CakeML with the candle chain and backend proofs built, and a
# Candle binary (scripts/INSTALL.md).
#
# SVENVS_UPPER_HM_FLAGS overrides the Holmake flags for Tiers 2 and up. Set it
# to "--no-cache --no_prereqs" to keep a shared, prebuilt CakeML tree read-only.
. "$(dirname "$0")/env.sh"
require_hol4

got="$(git -C "$CAKEMLDIR" rev-parse HEAD 2>/dev/null || echo '?')"
[ "$got" = "$SVENVS_CAKEML_COMMIT" ] ||
  die "CakeML at $got, pinned $SVENVS_CAKEML_COMMIT"
[ "$(git -C "$HOLDIR" rev-parse HEAD)" = "$SVENVS_HOL4_COMMIT" ] ||
  die "full verification requires HOL4 at $SVENVS_HOL4_COMMIT"
[ -s "$CAKEMLDIR/candle/standard/semantics/.hol/objs/holSoundnessTheory.uo" ] ||
  die "build CakeML's Candle theories before full verification"
[ -s "$CAKEMLDIR/compiler/backend/proofs/.hol/objs/backendProofTheory.uo" ] ||
  die "build CakeML's backend proofs before full verification"
[ -x "$CANDLE_ROOT/candle/build/cake" ] || die "full verification requires the Candle binary"
dirty="$(git -C "$CAKEMLDIR" status --porcelain --untracked-files=no)"
[ -z "$dirty" ] || warn "CakeML has local edits, so any theory depending on them is not at the pin:
$dirty"

here="$SVENVS_ROOT/scripts"
upper="${SVENVS_UPPER_HM_FLAGS-$SVENVS_HM_FLAGS}"

bash "$here/tier1-core.sh"
SVENVS_HM_FLAGS="$upper" bash "$here/tier2-candle-layers.sh"
SVENVS_HM_FLAGS="$upper" bash "$here/tier2.5-cited-layers.sh"

say "Tier 2: composed kernel crown (integrationKernelTheory)"
( cd "$SVENVS_ROOT/integration" &&
  WITH_KERNEL=1 CAKEMLDIR="$CAKEMLDIR" "$HOLMAKE" $upper ) ||
  die "integrationKernelTheory failed to build"

# A private server, so the log holds only this run's kernel output.
place_use_dir "$(mktemp -d "$SVENVS_WORK/verify-all-place.XXXXXX")"
trap '"$here/place-stop.sh" >/dev/null 2>&1 || true' EXIT
bash "$here/tier3-place-candle.sh"

bash "$here/verify-claims.sh" --tier all --strict
say "To re-check this run: PLACE_DIR=$PLACE_DIR scripts/verify-claims.sh --tier all --strict"
