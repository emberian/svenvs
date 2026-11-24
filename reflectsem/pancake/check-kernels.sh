#!/usr/bin/env bash
# Run the proved Pancake optimizer on Obend's five emitted kernels, evaluate
# them in HOL4, then compare the native binaries before and after it. Execute
# on the Linux build host, with compilerOpt built and `cake` on PATH or in $CAKE.
#
#   check-kernels.sh OBEND_CHECKOUT
#
# HOL4 parses each kernel twice in the logic, the source and the printed
# optimizer output, one theory per kernel; kmac256 alone takes over an hour.
# pancakeKernelOptTheory then evaluates the vectors. The theories are built in
# this directory so that verify-claims.sh can check their citations.
#
# The theories read the kernels while they build, so Holmake cannot see a
# changed input. They read a copy in .hol/kernels, and when the copied files
# differ from the last build's, their results are removed and built again.
# .hol/kernels also keeps the compiler version, the optimized sources, node
# counts and evaluation rows. KERNEL_JOBS and KERNEL_HEAP_MB bound how many
# builders run at once and the heap of each.
set -euo pipefail
here=$(cd "$(dirname "$0")" && pwd)
. "$here/../../scripts/env.sh"
obend=$(cd "${1:?expected the Obend checkout}" && pwd)
export SWARM_MEM_MAX=${SWARM_MEM_MAX:-40G}
jobs=${KERNEL_JOBS:-2}
heap=${KERNEL_HEAP_MB:-12000}
# swarm-build caps memory on the shared build hosts; elsewhere the timeout bounds the run.
bounded() {
  local limit="$1"; shift
  if have swarm-build; then timeout --kill-after=10s "$limit" swarm-build "$@"
  else timeout --kill-after=10s "$limit" "$@"; fi
}

src="$obend/lean/Obend/Lower/Pancake"
kernels="$here/.hol/kernels"
mkdir -p "$kernels"
# Holmake locks its objects, but the input files and native run share this directory too.
exec 9>"$kernels/build.lock"
flock 9
staged=$(mktemp -d "$SVENVS_WORK/pancake-kernels.XXXXXX")
trap 'rm -r "$staged"' EXIT
cp "$src"/{keccakF1600,cshake256,beltLatch,macaroonVerify,kmac256}.pnk \
   "$src"/{cshake256,beltLatch,macaroonVerify,kmac256}.c "$staged/"
for input in "$staged"/*.pnk; do
  name=$(basename "$input" .pnk)
  if ! cmp -s "$input" "$kernels/$name.pnk" ||
     [[ ! -s "$kernels/opt/$name.pnk" || ! -s "$kernels/opt/$name.stats" ]]; then
    rm -f "$here/.hol/objs/obend${name^}Theory".* "$here/.hol/objs/pancakeKernelOptTheory".*
    cp -f "$input" "$kernels/$name.pnk"
  fi
done
if [[ ! -s "$kernels/opt/eval.tsv" ]]; then
  rm -f "$here/.hol/objs/pancakeKernelOptTheory".*
fi
cp -f "$staged"/*.c "$kernels/"
(cd "$kernels" && sha256sum ./{keccakF1600,cshake256,beltLatch,macaroonVerify,kmac256}.pnk \
                           ./{cshake256,beltLatch,macaroonVerify,kmac256}.c) > "$kernels/inputs.sha256"
"${CAKE:-cake}" --version > "$kernels/cake-version.txt"
export PANCAKE_KERNELS="$kernels"
# kmac256 first: it is the longest build.
(cd "$here" && bounded 21600s "$HOLMAKE" --no-cache "-j$jobs" --heap-size "$heap" --no_prereqs \
   obendKmac256Theory.uo obendKeccakF1600Theory.uo obendCshake256Theory.uo \
   obendMacaroonVerifyTheory.uo obendBeltLatchTheory.uo pancakeKernelOptTheory.uo) ||
  { tail -n 40 "$here"/.hol/logs/obend*Theory "$here"/.hol/logs/pancakeKernelOptTheory 2>/dev/null
    exit 1; }
(cd "$here" && bounded 600s "$HOL" --maxheap "$heap" run \
   --holstate="$CAKEMLDIR/misc/cakeml-heap" checkKernelProofs.sml)
bounded 3600s env -u PANCAKE_KERNEL_NAMES python3 -I "$here/kernel_native.py" "$kernels"
echo "kernel results: $kernels"
