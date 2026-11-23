#!/usr/bin/env bash
# Execute on the Linux build host. Bound each compiler or prover invocation.
set -euo pipefail
here=$(cd "$(dirname "$0")" && pwd)
. "$here/../../scripts/env.sh"
obend=$(cd "${1:?expected the Obend checkout}" && pwd)
basis=${2:-}
export SWARM_MEM_MAX=${SWARM_MEM_MAX:-24G}
bounded() { timeout --kill-after=10s 600s swarm-build "$@"; }
work=$(mktemp -d)
trap 'rm -rf "$work"' EXIT
export PANCAKE_CORPUS="$work/corpus"
(
  cd "$obend/lean"
  bounded lake build Obend.Lower.Pancake.PancakeKeccak Obend.Lower.Pancake.LcnfFun Obend.Tactic.Tooth
  bounded lake env lean --run tests/metasystem/PancakeKeccakSpineTest.lean "$PANCAKE_CORPUS"
)
cmp "$obend/lean/Obend/Lower/Pancake/keccakF1600.pnk" "$PANCAKE_CORPUS/keccakF1600.pnk"

# The script reads generated files at theory-build time. A fresh directory
# and --no-cache ensure that a changed fixture is evaluated.
mkdir "$work/hol"
cp "$here"/{Holmakefile,pancakeDifferentialScript.sml} "$work/hol/"
(cd "$work/hol" && bounded "$HOLMAKE" --no-cache -j1 --no_prereqs pancakeDifferentialTheory.uo)
if [[ -n "$basis" ]]; then
  bounded python3 "$here/native.py" "$PANCAKE_CORPUS" "$basis"
fi
