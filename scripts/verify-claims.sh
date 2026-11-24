#!/usr/bin/env bash
# verify-claims.sh — proof-carrying claims about a proof-carrying system.
#
# CLAIMS.md is the skeptic-facing ledger. This script mechanically checks
# that the ledger does not lie about the artifact:
#
#  1. CITATION INTEGRITY. Every `path/<X>Script.sml : t1, t2, ...` citation
#     in CLAIMS.md (and the per-directory CLAIMS.md files — citations there
#     are resolved relative to that file's directory; `dir/{A,B}Script.sml`
#     means the theorem is in either theory) names theorems that genuinely
#     exist as `val <t> : thm` in the *built* signature
#     <dir>/.hol/objs/<X>Theory.sig. Each citation belongs to one tier:
#       tier 1  pure HOL4 (scripts/tier1-core.sh)
#       tier 2  HOL4 over CakeML/Candle (scripts/tier2-candle-layers.sh,
#               scripts/tier2.5-cited-layers.sh, integrationKernelTheory)
#       tier 3  theorems the live Candle kernel echoed into the Place log
#               (scripts/tier3-place-candle.sh)
#     A theory with no signature or object, or whose source is newer than
#     its signature, is SKIPPED. --strict turns every skip in the requested
#     tiers into a failure and also fails a requested tier with no citations.
#  2. LABELED-SEAM INTEGRITY. Every seam the ledger carries
#     (encodes_obligation, encodes_soundness, frozen_checker_sound,
#     attestation_faithful) still appears verbatim as a `Definition` in
#     source, and CLAIMS.md still names each one.
#  3. CHEAT/ORACLE/AXIOM GATE. No cheat tactic / new_axiom / mk_thm /
#     mk_oracle_thm in any project *.sml or *.ml file
#     (prose mentions of the words are excluded).
#  4. FRAMING GUARD. Both retired labels (`UNTRUSTED`, `UNMODELABLE`)
#     appear nowhere; the live `UNCONSTRAINED` center is in force; the
#     lowercase words survive only where text explicitly names them as the
#     retired/retracted words.
#
# Usage:
#   verify-claims.sh                       every tier; unbuilt citations skip
#   verify-claims.sh --tier 1 --strict     Tier 1, zero skips (push/PR CI)
#   verify-claims.sh --tier all --strict   every tier, zero skips (full run)
#
# Exit non-zero on any failure. Intended for the cheat gate / CI.
. "$(dirname "$0")/env.sh"

STRICT=0
TIER=all
while [ $# -gt 0 ]; do
  case "$1" in
    --strict) STRICT=1 ;;
    --tier)
      [ $# -ge 2 ] || die "verify-claims.sh: --tier needs a value (1|2|3|all)"
      shift; TIER="$1" ;;
    --tier=*) TIER="${1#--tier=}" ;;
    *) die "verify-claims.sh: unknown arg '$1' (use --tier 1|2|3|all, --strict)" ;;
  esac
  shift
done
case "$TIER" in
  1|2|3|all) ;;
  *) die "verify-claims.sh: unknown tier '$TIER' (use 1|2|3|all)" ;;
esac
cd "$SVENVS_ROOT" || die "cannot cd to $SVENVS_ROOT"
fails=0
work="$(mktemp -d "$SVENVS_WORK/verify-claims.XXXXXX")"
trap 'rm -f "$work/code" "$work/sources"; rmdir "$work"' EXIT

say "1. Citation integrity (tier $TIER)"
if ! manifest=$(python3 -I scripts/check-claim-signatures.py "$TIER" "$STRICT"); then
  fails=1
fi
printf '%s\n' "$manifest"

say "2. Labeled-seam integrity (every seam the ledger carries: defined + named)"
for a in encodes_obligation encodes_soundness frozen_checker_sound attestation_faithful; do
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

say "3. Cheat / oracle / axiom gate (all sources, zero exclusions)"
# Real danger = the cheat *tactic* / axiom builders as CODE. Comments are
# stripped before scanning (every `(* ... *)` block becomes blanks, newlines
# kept so line numbers stay right), so prose ABOUT cheats can never trip the
# gate and needs no allow-list. Excluded: only the HOL build tree (.hol/).
cheat_re="(^|[^[:alnum:]_'])(cheat|new_axiom|mk_thm|mk_oracle_thm)([^[:alnum:]_']|$)"
find -L . -type d \( -name .hol -o -name .git \) -prune -o \
  -type f \( -name '*.sml' -o -name '*.ml' \) -print0 > "$work/sources"
hits=""
while IFS= read -r -d '' f; do
  code_only "$f" > "$work/code"
  if matches=$(grep -nE "$cheat_re" "$work/code"); then
    printf '%s\n%s\n' "$f" "$matches"
    hits=1
  elif [ "$?" != 1 ]; then
    die "cannot scan $f"
  fi
done < "$work/sources"
if [ -n "$hits" ]; then
  printf '  %sFAIL%s cheat/oracle/axiom token in a load-bearing source\n' "$C_NO" "$C_Z"
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
retire_ctx_re='retir|retract|reframe|over-claim|over-rotat|moral verdict|adversarial default|carceral|envelope, contain|breach, the untrusted|not untrusted|earlier label|earlier draft|earlier version|an earlier'
stray=$(grep -rnE '\b(untrusted|unmodelable)\b' --include='*.md' --include='*.sml' \
     --include='*.ml' --include='*.html' --include='*.py' . \
   | grep -v '/.hol/' | grep -viE "$retire_ctx_re" || true)
if [ -n "$stray" ]; then
  printf '  %sFAIL%s stray "untrusted"/"unmodelable" outside the allowed retired-word mentions:\n' "$C_NO" "$C_Z"
  printf '%s\n' "$stray" | sed 's/^/    /'
  fails=$((fails+1))
else
  ok 'lowercase "untrusted"/"unmodelable" only where it names the retired word'
fi

echo
if [ "$fails" = 0 ] && [[ "$manifest" != *", skipped: 0" ]]; then
  warn "CLAIMS LEDGER PARTIAL — $manifest"
  exit 0
elif [ "$fails" = 0 ]; then
  ok "CLAIMS LEDGER VERIFIED — the claims carry their own proof. $manifest"
  exit 0
else
  die "Claims verification failed. See the diagnostics above."
fi
