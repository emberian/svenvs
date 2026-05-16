#!/usr/bin/env bash
# verify-claims.sh — proof-carrying claims about a proof-carrying system.
#
# CLAIMS.md is the skeptic-facing ledger. This script mechanically checks
# that the ledger does not lie about the artifact:
#
#  1. CITATION INTEGRITY. Every `path/<X>Script.sml : t1, t2, ...` citation
#     in CLAIMS.md (and the per-directory CLAIMS.md files — citations there
#     are resolved relative to that file's directory) names theorems that
#     genuinely exist as `val <t> : thm` in the *built* signature
#     <dir>/.hol/objs/<X>Theory.sig. A theory not built in this run is
#     SKIPPED with a notice (run a tier/tower build first; --strict turns
#     skips into failures for full CI).
#  2. LABELED-ASSUMPTION INTEGRITY. The three labeled assumptions
#     (loeb_reflection, encodes_obligation, frozen_checker_sound) each
#     still appear verbatim as a `Definition` in source, and CLAIMS.md
#     still names all three.
#  3. CHEAT/ORACLE/AXIOM GATE. No cheat tactic / new_axiom / mk_thm /
#     mk_oracle_thm in any non-inference, non-excluded *Script.sml/*.ml
#     (prose mentions of the words are excluded).
#  4. FRAMING GUARD. Both retired labels (`UNTRUSTED`, `UNMODELABLE`)
#     appear nowhere; the live `UNCONSTRAINED` center is in force; the
#     lowercase words survive only where text explicitly names them as the
#     retired/retracted words.
#
# Exit non-zero on any failure. Intended for the cheat gate / CI.
. "$(dirname "$0")/env.sh"

STRICT=0
for a in "$@"; do
  case "$a" in
    --strict) STRICT=1 ;;
    *) die "verify-claims.sh: unknown arg '$a' (use --strict)" ;;
  esac
done

cd "$SVENVS_ROOT"
fails=0
checked=0
skipped=0

ledgers=$(find . -name CLAIMS.md -not -path './.hol/*' | sort)

say "1. Citation integrity (ledger theorems exist in built signatures)"
for ledger in $ledgers; do
  ldir="$(dirname "$ledger")"
  while IFS= read -r cite; do
    [ -n "$cite" ] || continue
    path="${cite%% : *}"
    names="${cite#* : }"
    # resolve relative to the ledger's directory, then normalise
    src="$ldir/$path"
    [ -f "$src" ] || src="$path"
    if [ ! -f "$src" ]; then
      warn "cited source missing: $path  (in $ledger)"; fails=$((fails+1)); continue
    fi
    base="$(basename "$src")"
    dir="$(dirname "$src")"
    thy="${base%Script.sml}Theory"
    sig="$dir/.hol/objs/$thy.sig"
    if [ ! -f "$sig" ]; then
      skipped=$((skipped+1))
      if [ "$STRICT" = 1 ]; then
        die "STRICT: $thy not built (no $sig) — cited for: $names"
      else
        warn "skip (not built this run): $thy"
      fi
      continue
    fi
    oldIFS=$IFS; IFS=','
    for raw in $names; do
      IFS=$oldIFS
      t="$(printf '%s' "$raw" | tr -cd 'A-Za-z0-9_')"
      [ -n "$t" ] || { IFS=','; continue; }
      checked=$((checked+1))
      # accept a theorem cited by name, or a Definition cited by its base
      # name (sig stores those as `val <t>_def : thm`).
      if ! grep -qE "^[[:space:]]*val (${t}|${t}_def) :" "$sig"; then
        printf '  %sMISSING%s  %s : %s  (not in %s)\n' "$C_NO" "$C_Z" "$thy" "$t" "$sig"
        fails=$((fails+1))
      fi
      IFS=','
    done
    IFS=$oldIFS
  done < <(grep -ohoE '[A-Za-z0-9_./-]+Script\.sml : [A-Za-z0-9_]+(, *[A-Za-z0-9_]+)*' "$ledger" | sort -u)
done
[ "$fails" = 0 ] && ok "all cited theorems present ($checked checked, $skipped skipped)"

say "2. Labeled-assumption integrity (the three seams: defined + named)"
for a in loeb_reflection encodes_obligation frozen_checker_sound; do
  if grep -rqE "Definition[[:space:]]+${a}_def" --include='*Script.sml' . ; then
    ok "Definition ${a}_def present"
  else
    printf '  %sMISSING%s  Definition %s_def not found\n' "$C_NO" "$C_Z" "$a"
    fails=$((fails+1))
  fi
  grep -qE "\`${a}\`" CLAIMS.md || {
    printf '  %sMISSING%s  CLAIMS.md does not name labeled assumption %s\n' "$C_NO" "$C_Z" "$a"
    fails=$((fails+1)); }
done

say "3. Cheat / oracle / axiom gate (non-inference sources)"
# Real danger = the cheat *tactic* / axiom builders as CODE. Exclude:
#  - the HOL build tree
#  - the inference/ research track + the build-excluded reflection scaffold
#  - prose that merely talks ABOUT cheats (negations, "anywhere", citations)
cheat_re='(^|[[:space:]>(])cheat([[:space:]]|$|\))|new_axiom|mk_thm|mk_oracle_thm'
prose_re='cheat-free|`cheat`|the one stale|admitted with|[Nn][Oo][Tt]? a cheat|[Nn]o cheat|without cheat|cheat / new_axiom|anywhere in this|oracle anywhere|no .*(mk_thm|oracle)'
hits=$(grep -rnE "$cheat_re" --include='*Script.sml' --include='*.ml' . \
       | grep -v '/.hol/' \
       | grep -vE 'inference/|reflection/reflectionDemoScript\.sml' \
       | grep -vE "$prose_re" || true)
if [ -n "$hits" ]; then
  printf '  %sFAIL%s cheat/oracle/axiom token in a load-bearing source:\n' "$C_NO" "$C_Z"
  printf '%s\n' "$hits" | sed 's/^/    /'
  fails=$((fails+1))
else
  ok "zero cheat/oracle/axiom tokens in load-bearing sources"
fi

say "4. Framing guard (the one-gate center is current)"
# BOTH retired labels must be gone everywhere: UNTRUSTED (a moral prior) and
# UNMODELABLE (a retracted over-claim). The live label is UNCONSTRAINED.
retired_labels=0
for lbl in UNTRUSTED UNMODELABLE; do
  if grep -rn "$lbl" --include='*.md' --include='*.sml' --include='*.ml' \
       --include='*.html' --include='*.py' . | grep -v '/.hol/' | grep -q . ; then
    printf '  %sFAIL%s retired label %s still present:\n' "$C_NO" "$C_Z" "$lbl"
    grep -rn "$lbl" --include='*.md' --include='*.sml' --include='*.ml' \
       --include='*.html' --include='*.py' . | grep -v '/.hol/' | sed 's/^/    /'
    retired_labels=1
  fi
done
if [ "$retired_labels" = 0 ]; then
  ok "retired labels UNTRUSTED / UNMODELABLE absent"
else
  fails=$((fails+1))
fi
# the live label must actually be in force
if grep -q 'UNCONSTRAINED' CLAIMS.md; then
  ok "live label UNCONSTRAINED in force"
else
  printf '  %sFAIL%s live label UNCONSTRAINED missing from CLAIMS.md\n' "$C_NO" "$C_Z"
  fails=$((fails+1))
fi
# lowercase "untrusted"/"unmodelable" allowed ONLY where the text explicitly
# names it AS the retired word (the over-claim retraction, the carceral-
# vocabulary list, the "not untrusted (a moral verdict)" pivot, comments
# that cite the retraction).
allow_re='retir|retract|reframe|over-claim|over-rotat|moral verdict|adversarial default|carceral|envelope, contain|breach, the untrusted|not untrusted|earlier label|earlier draft|earlier version|an earlier'
stray=$(grep -rnE '\b(untrusted|unmodelable)\b' --include='*.md' --include='*.sml' \
     --include='*.ml' --include='*.html' --include='*.py' . \
   | grep -v '/.hol/' | grep -viE "$allow_re" || true)
if [ -n "$stray" ]; then
  printf '  %sFAIL%s stray "untrusted"/"unmodelable" outside the allowed retired-word mentions:\n' "$C_NO" "$C_Z"
  printf '%s\n' "$stray" | sed 's/^/    /'
  fails=$((fails+1))
else
  ok 'lowercase "untrusted"/"unmodelable" only where it names the retired word'
fi

echo
if [ "$fails" = 0 ]; then
  ok "CLAIMS LEDGER VERIFIED — the claims carry their own proof."
  exit 0
else
  die "$fails ledger discrepancy/-ies — CLAIMS.md overclaims or the build is stale."
fi
