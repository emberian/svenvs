#!/usr/bin/env bash
# ---------------------------------------------------------------------------
# build.sh — reproduce the svenvs envelope console x86-64 ELF from scratch.
#
# This is exactly what .github/workflows/release.yml runs in CI, factored out
# so you can run it by hand on any x86-64 Linux box with a C toolchain.
#
# It:
#   1. downloads the *verified* CakeML compiler distribution (pinned release
#      + pinned sha256),
#   2. builds the `cake` compiler binary from its bootstrapped assembly,
#   3. compiles release/envelope_console.cml -> x86-64 assembly with `cake`,
#   4. assembles + links it (with CakeML's basis_ffi.c) into an ELF.
#
# Output: ./envelope_console  (a fresh x86-64 ELF, the release artifact).
#
# Usage:   release/build.sh [OUTDIR]      (default OUTDIR = ./_build)
# ---------------------------------------------------------------------------
set -euo pipefail

# --- pinned toolchain (CakeML verified compiler, x86-64 build) --------------
CAKE_RELEASE="v3304"
CAKE_TARBALL="cake-x64-64.tar.gz"
CAKE_URL="https://github.com/CakeML/cakeml/releases/download/${CAKE_RELEASE}/${CAKE_TARBALL}"
# sha256 of the v3304 cake-x64-64.tar.gz GitHub release asset (verified to
# produce a bit-identical envelope_console ELF; see release/README.md).
CAKE_SHA256="6d4d60511597828a58853aa45f21e2cd75bb564908f239368ff7b40e8073b2b3"

HERE="$(cd "$(dirname "$0")" && pwd)"
SRC="${HERE}/envelope_console.cml"
OUTDIR="${1:-${HERE}/_build}"
CC="${CC:-cc}"

mkdir -p "${OUTDIR}"
cd "${OUTDIR}"

echo ">> downloading verified CakeML compiler ${CAKE_RELEASE} (${CAKE_TARBALL})"
curl -fsSL -o "${CAKE_TARBALL}" "${CAKE_URL}"

echo ">> verifying sha256 of ${CAKE_TARBALL}"
echo "${CAKE_SHA256}  ${CAKE_TARBALL}" | sha256sum -c -

echo ">> unpacking"
tar xzf "${CAKE_TARBALL}"
cd cake-x64-64

echo ">> building the cake compiler (cake.S + basis_ffi.c)"
"${CC}" -O2 cake.S basis_ffi.c -DEVAL -o cake -lm

echo ">> compiling envelope_console.cml -> assembly with cake"
./cake < "${SRC}" > envelope_console.cake.S

echo ">> assembling + linking the ELF (with basis_ffi.c)"
"${CC}" -O2 envelope_console.cake.S basis_ffi.c -lm -o envelope_console

cp envelope_console "${OUTDIR}/envelope_console"
cd "${OUTDIR}"

echo
echo ">> built: ${OUTDIR}/envelope_console"
file envelope_console || true
sha256sum envelope_console || true
echo
echo ">> smoke test (feed: 1, 1, -1, 5):"
printf '1\n1\n-1\n5\n' | ./envelope_console
