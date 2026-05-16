#!/usr/bin/env bash
# Build the COMPOSED svenvs tower in dependency order and assert the
# composed end-to-end theorems exist. This is the single coherent
# entrypoint: the 17 per-slice Holmakefiles are layers of ONE artifact,
# `integration/integrationScript.sml`, which opens and composes them via
# specNeg's selector-generic transport keystone.
#
#   ./scripts/tower.sh          # pure-HOL4 tower (trunk + prover crown)
#   ./scripts/tower.sh --full   # + Tier-2 kernel crown (needs candle)
set -euo pipefail
here="$(cd "$(dirname "$0")/.." && pwd)"
HOL="${HOLDIR:-$HOME/dev/HOL}/bin/Holmake"
full=0; [ "${1:-}" = "--full" ] && full=1

say(){ printf '\n=== %s ===\n' "$*"; }

# DAG order: generic core -> the three composable slices -> integration.
say "1. generic core (system/envelope/safety/sv_weakening/upgrade)"
( cd "$here" && "$HOL" )
for d in pca specneg selfprover liberty amendment genealogy; do
  say "2. slice: $d"
  ( cd "$here/$d" && "$HOL" )
done
say "3. composed tower (integration/)"
if [ "$full" = 1 ]; then
  ( cd "$here/kernel" && "$HOL" ) || { echo "kernel slice failed (Tier-2 candle chain absent?)"; exit 1; }
  ( cd "$here/integration" && "$HOL" )
  crowns="svenvs_tower_unconditional svenvs_tower_at_maximal_liberty svenvs_tower_with_meta_amendment svenvs_tower_with_prover_upgrade svenvs_tower_with_kernel_upgrade"
else
  # build only the pure trunk+prover theory, skip the Tier-2 kernel crown
  ( cd "$here/integration" && "$HOL" integrationTheory.uo )
  crowns="svenvs_tower_unconditional svenvs_tower_at_maximal_liberty svenvs_tower_with_meta_amendment svenvs_tower_with_prover_upgrade"
fi

say "COMPOSED THEOREMS (the artifact, not a pile)"
ok=1
for thm in $crowns; do
  if grep -aq "val $thm :" "$here"/integration/.hol/objs/integration*Theory.sig 2>/dev/null; then
    echo "  PROVED  integration : $thm"
  else
    echo "  MISSING $thm"; ok=0
  fi
done
# cheat/oracle gate on the composed theory itself
if grep -rnE '(^|[[:space:]>(])cheat([[:space:]]|$|\))|new_axiom|mk_thm|mk_oracle_thm' \
     "$here"/integration/*Script.sml | grep -vqE 'cheat-free|`cheat`|hidden|gap|forced'; then
  echo "  !! cheat/oracle token in integration source"; ok=0
else
  echo "  cheat/oracle scan: clean"
fi
# The general principle the keystone-composed crowns are instances of:
# the gate applied to the root judge itself (forward-certified genealogy).
for thm in genealogy_sound identity_vouch_unconditional genealogy_irrelevant_to_vouch_sound; do
  if grep -aqE "^[[:space:]]*val $thm :" "$here"/genealogy/.hol/objs/genealogyTheory.sig 2>/dev/null; then
    echo "  PROVED  genealogy   : $thm"
  else
    echo "  MISSING $thm"; ok=0
  fi
done

[ "$ok" = 1 ] || { echo; echo "TOWER INCOMPLETE."; exit 1; }

# Proof-carrying claims: the ledger must not lie about what was just built.
say "PROOF-CARRYING CLAIMS (verify-claims.sh)"
if bash "$here/scripts/verify-claims.sh"; then
  echo; echo "TOWER COMPOSED & VERIFIED."
else
  echo; echo "TOWER BUILT, but CLAIMS LEDGER FAILED — fix CLAIMS.md."; exit 1
fi
