#!/usr/bin/env bash
# TIER 1 — pure HOL4, no CakeML. Anyone with HOL4 can reproduce this.
# Builds, and machine-checks, the generic self-improving-envelope core, the
# cartpole instance, the adversarial-LLM tool-agent (incl. the EVAL'd
# running episodes), and the toy verified-inference kernel.
#
# Idempotent: re-running is a fast no-op (Holmake caches). It does NOT
# clean by default — pass --clean to force a from-scratch rebuild, or
# --quick to skip the optional inference track.
. "$(dirname "$0")/env.sh"
require_hol4

CLEAN=0; QUICK=0
for a in "$@"; do
  case "$a" in
    --clean) CLEAN=1 ;;
    --quick) QUICK=1 ;;
    *) die "tier1-core.sh: unknown arg '$a' (use --clean / --quick)" ;;
  esac
done

# build <label> <dir> <logtag> <theory...>
build_dir(){
  local label="$1" dir="$2" tag="$3"; shift 3
  say "Tier 1: $label"
  cd "$dir" || die "missing directory $dir"
  [ "$CLEAN" = 1 ] && { "$HOLMAKE" cleanAll >/dev/null 2>&1 || true; rm -rf .hol; }
  if ! "$HOLMAKE" $SVENVS_HM_FLAGS 2>&1 | tee "$SVENVS_LOGS/t1-$tag.log" | tail -n 6; then
    die "Holmake failed in $dir — full log: $SVENVS_LOGS/t1-$tag.log"
  fi
  local t
  for t in "$@"; do
    built "$dir" "$t" || die "$label: ${t}Theory not built (see $SVENVS_LOGS/t1-$tag.log)"
  done
  ok "$label: $# theories machine-checked"
}

build_dir "core + cartpole (pure HOL4)" "$SVENVS_ROOT" core \
  system envelope safety sv_weakening upgrade certifier viability \
  cartpole cartpoleEnvelope cartpoleUpgrades cartpoleProgram

build_dir "adversarial-LLM tool-agent" "$SVENVS_ROOT/agent" agent \
  toolAgent toolAgentRun toolAgentDecide

build_dir "recursive self-improvement capstone (pure HOL4)" "$SVENVS_ROOT/recursive" recursive \
  recursiveImprovement

build_dir "self-recompile gate — runtime loop <-> proved spine bridge" "$SVENVS_ROOT/selfRecompile" selfrec \
  selfRecompileGate

build_dir "APEX — self-improving+self-recompiling system, proved safe" "$SVENVS_ROOT/apex" apex \
  apex

build_dir "closed-loop num-encoding faithfulness (gate can't be fooled)" "$SVENVS_ROOT/agent/closedloop" encfaith \
  encFaith

if [ "$QUICK" = 0 ]; then
  build_dir "toy verified-inference kernel" "$SVENVS_ROOT/inference" inf \
    mlpInference
else
  warn "skipping optional verified-inference track (--quick)"
fi

# integrity: a real 'cheat' tactic must appear nowhere in Tier 1 sources
# (scope = every directory built above). Comments are stripped first (a
# `(* ... *)` block becomes blanks, newlines kept), so prose about cheats
# cannot trip the gate; only a bare `cheat` tactic in CODE does.
code_only(){ perl -0777 -pe 's/\(\*.*?\*\)/ my $m = $&; $m =~ s#[^\n]# #g; $m /gse' "$1"; }
cheats="$(for f in "$SVENVS_ROOT"/*.sml "$SVENVS_ROOT"/agent/*.sml \
            "$SVENVS_ROOT"/agent/closedloop/*.sml "$SVENVS_ROOT"/recursive/*.sml \
            "$SVENVS_ROOT"/selfRecompile/*.sml "$SVENVS_ROOT"/apex/*.sml \
            "$SVENVS_ROOT"/inference/mlpInferenceScript.sml; do
            [ -f "$f" ] || continue
            { code_only "$f" | grep -nE '(^|[^[:alnum:]_])cheat([^[:alnum:]_]|$)' | sed "s|^|$f:|"; } || true
          done)"
if [ -n "$cheats" ]; then
  printf '%s\n' "$cheats" >&2
  die "a real 'cheat' tactic appears in a Tier-1 source (above) — STOP"
fi
ok "Tier 1 sources are cheat-free (verified by scan)"

say "TIER 1 REPRODUCED — proof-carrying self-improving envelope + adversarial-LLM agent + toy verified inference, all machine-checked, pure HOL4"
