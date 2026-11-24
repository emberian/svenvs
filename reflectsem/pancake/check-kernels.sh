#!/usr/bin/env bash
# Run the proved Pancake optimizer on Obend's emitted kernels, then compare the
# native binaries before and after it. Execute on the Linux build host, with
# compilerOpt built and `cake` on PATH or in $CAKE.
#
#   check-kernels.sh OBEND_CHECKOUT
#
# The verified parser runs in the logic, so the two large kernels take hours.
# The optimized sources and measurements stay in the printed run directory.
set -euo pipefail
here=$(cd "$(dirname "$0")" && pwd)
. "$here/../../scripts/env.sh"
obend=$(cd "${1:?expected the Obend checkout}" && pwd)
export SWARM_MEM_MAX=${SWARM_MEM_MAX:-40G}
bounded() { local limit="$1"; shift; timeout --kill-after=10s "$limit" swarm-build "$@"; }

run=$(mktemp -d "$SVENVS_WORK/pancake-kernels.XXXXXX")
src="$obend/lean/Obend/Lower/Pancake"
cp "$src"/{keccakF1600,cshake256,beltLatch}.pnk "$src"/{cshake256,beltLatch}.c "$run/"
mkdir "$run/hol"
cp "$here"/{Holmakefile,pancakeKernelOptScript.sml} "$run/hol/"
# Record the exact inputs and compiler alongside the measurements.
(cd "$run" && sha256sum ./*.pnk ./*.c) > "$run/inputs.sha256"
"${CAKE:-cake}" --version > "$run/cake-version.txt"
export PANCAKE_KERNELS="$run"
(cd "$run/hol" && bounded 14400s "$HOLMAKE" --no-cache -j1 --no_prereqs pancakeKernelOptTheory.uo)
bounded 3600s python3 -I "$here/kernel_native.py" "$run"
echo "kernel run directory: $run"
