#!/usr/bin/env bash
# TIER 2.5 — the deeper self-improvement layers that CLAIMS.md / README cite but
# that no other build script was checking: the concrete frozen-root discharge,
# the kernel-modification + in-place-swap + self-optimization-loop + genesis-
# runtime proofs, the executable monadic SYM kernel tie-in, and the loader over
# CakeML's real closSem$do_install. Needs the built CakeML candle chain (Tier 2).
#
# Idempotent; auto-SKIPs (exit 0) with instructions if the candle chain is
# absent. Pass --clean to force a rebuild.
. "$(dirname "$0")/env.sh"
require_hol4

CLEAN=0
for a in "$@"; do
  case "$a" in
    --clean) CLEAN=1 ;;
    --quick) : ;;
    *) die "tier2.5: unknown arg '$a'" ;;
  esac
done

CANDLE_SEM="$CAKEMLDIR/candle/standard/semantics/.hol/objs/holSoundnessTheory.uo"
if [ ! -f "$CANDLE_SEM" ]; then
  warn "SKIP Tier 2.5: CakeML candle chain not built at
       $CANDLE_SEM
  (same prerequisite as Tier 2 — see scripts/INSTALL.md). Tiers 1-2 unaffected."
  exit 0
fi

# dir : "Theory:theorem ..." assertions (the headline cited theorems)
build_and_assert(){
  local d="$1"; shift
  local tag="${d//\//_}"   # sanitize nested dirs (kernel/loebReduction) for the log path
  say "Tier 2.5: $d"
  cd "$SVENVS_ROOT/$d" || die "missing $SVENVS_ROOT/$d"
  if [ "$CLEAN" = 1 ]; then
    CAKEMLDIR="$CAKEMLDIR" "$HOLMAKE" cleanAll >/dev/null 2>&1 || true; rm -rf .hol
  fi
  if ! CAKEMLDIR="$CAKEMLDIR" "$HOLMAKE" $SVENVS_HM_FLAGS 2>&1 \
        | tee "/tmp/svenvs-t25-$tag.log" | tail -n 6; then
    die "Holmake failed in $d — full log: /tmp/svenvs-t25-$tag.log"
  fi
  local spec th nm
  for spec in "$@"; do
    th="${spec%%:*}"; nm="${spec#*:}"
    grep -aqE "val $nm" "$SVENVS_ROOT/$d/.hol/objs/${th}Theory.sig" 2>/dev/null \
      || die "$d: cited theorem $nm not found in ${th}Theory (see /tmp/svenvs-t25-$d.log)"
    ok "$d : $th.$nm"
  done
}

build_and_assert selfproverConcrete \
  "selfProverConcrete:frozen_checker_sound_candle" \
  "selfProverConcrete:prover_self_improvement_is_safe_candle"
build_and_assert kernelMod \
  "kernelMod:sym_kernel_sound" \
  "inplaceUpdate:inplace_update_is_safe" \
  "selfOptimize:self_optimizing_prover_is_safe" \
  "genesisRuntime:genesis_certifies_runtime"
build_and_assert kernelImpl \
  "kernelImplSym:candle_SYM_implements_sym_extension" \
  "symBinaryImplements:sym_produces_implements_sym_kernel" \
  "symBinaryImplements:candle_SYM_computes_sym_extension"
build_and_assert loader \
  "installLoader:do_install_preserves_code" \
  "installLoader:do_install_preserves_FLOOKUP"

# A genuinely NEW verified compiler optimization (BVL), proven semantics-
# preserving against the real bvlSem$evaluate and wired as a CONCRETE proved
# witness into the recursive genealogy's compiler line (CITED -> PROVED).
build_and_assert compilerOpt \
  "compilerOpt:optimise_correct" \
  "compilerOpt:optimise_let_nil_strict" \
  "compilerOpt:recursive_compiler_line_preserves_bvlSem"

# The open assumption loeb_reflection, REDUCED in-logic to the cited LCA
# (Fallenstein-Kumar via hol-reflection) — no longer a bare assumption.
build_and_assert kernel/loebReduction \
  "loebReduction:loeb_reflection_from_lca" \
  "loebReduction:kernel_proves_satisfied"

# Toward a self-upgradable compiler: the per-generation eval-oracle invariant +
# the swap-preservation lemma (a mid-run compiler swap keeps the invariant),
# the single-swap end-to-end keystone, and the multi-swap lift (the keystone
# iterated over a schedule of arbitrarily many in-place compiler swaps).
build_and_assert selfUpgrade \
  "evalUpgradeB:swap_preserves_recorded_orac_wf_gen" \
  "evalUpgradeB:recorded_orac_wf_gen_const" \
  "selfUpgradeEndToEnd:selfupgrade_eval_simulation_step" \
  "selfUpgradeEndToEnd:s_rel_gen_const" \
  "selfUpgradeEndToEnd:selfupgrade_collapses_to_eval_simulation" \
  "selfUpgradeMultiSwap:selfupgrade_multi_swap_simulation" \
  "selfUpgradeMultiSwap:selfupgrade_oracle_semantics_prog_collapse"

say "TIER 2.5 REPRODUCED — every cited self-improvement-layer theorem re-proved against real CakeML/Candle, plus a new verified BVL optimization pass, the SYM binary-implements discharge, and the loeb_reflection->LCA reduction"
