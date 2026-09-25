#!/usr/bin/env bash
# hygiene-audit.sh — mechanical first pass of the repository-hygiene checklist
# (CONTRIBUTING.md § Repository hygiene). Greps for the patterns that turned
# out to matter in a real audit; prints findings by principle with file:line.
# HARD findings exit non-zero; SOFT ones are for judgment.
#
#   scripts/hygiene-audit.sh [repo-dir]        (default: the current repo)
#
# It only reads. Tune the SKIP regex for paths that are data, not code.
set -uo pipefail
repo="${1:-$(git rev-parse --show-toplevel 2>/dev/null || pwd)}"
cd "$repo" || { echo "no such dir: $repo" >&2; exit 2; }
SKIP='(^|/)(\.git|node_modules|target|_build|\.hol|dist|vendor)(/|$)|\.(pdf|png|jpg|jpeg|gif|svg|ico|woff2?|ttf|pdf|dat|uo|ui)$'
hard=0; soft=0
files(){ if git rev-parse --is-inside-work-tree >/dev/null 2>&1; then git ls-files; else find . -type f | sed 's|^\./||'; fi | grep -vE "$SKIP"; }
list(){ files > "${TMPDIR:-/tmp}/hyg.$$"; }
list
F="${TMPDIR:-/tmp}/hyg.$$"
g(){ # g <regex> [extra grep args] ; greps the tracked file list (portable xargs)
  local re="$1"; shift
  tr '\n' '\0' < "$F" | xargs -0 grep -nIE "$@" -e "$re" 2>/dev/null | grep -v '^Binary'
}
section(){ printf '\n== %s ==\n' "$*"; }
code(){ grep -vE '^[^:]+:[0-9]+:[[:space:]]*(#|\(\*|//|\*)'; }   # drop comment-only lines
hardf(){ hard=$((hard+1)); printf '  HARD %s\n' "$*"; }
softf(){ soft=$((soft+1)); printf '  soft %s\n' "$*"; }
report(){ # report <kind> <label> <lines>
  local kind="$1" label="$2" lines="$3"
  [ -z "$lines" ] && return 0
  printf '  %s %s\n' "$kind" "$label"; printf '%s\n' "$lines" | sed 's/^/        /' | head -25
  local n; n=$(printf '%s\n' "$lines" | wc -l | tr -d ' '); [ "$n" -gt 25 ] && printf '        … %s more\n' $((n-25))
  if [ "$kind" = HARD ]; then hard=$((hard+n)); else soft=$((soft+n)); fi
}

section "1. Pins: every upstream by full commit SHA or content hash"
report HARD "GitHub Actions not pinned to a 40-hex SHA" "$(g '^[[:space:]]*-?[[:space:]]*uses:[[:space:]]*[A-Za-z0-9_./-]+@' | grep -vE '@[0-9a-f]{40}([[:space:]]|#|$)' | grep -E '\.github/workflows/')"
report soft "short git SHAs (7-12 hex) used as pins in scripts/docs/config" "$(g '(commit|checkout|pin|rev|sha)[^\n]{0,40}\b[0-9a-f]{7,12}\b' -i | grep -vE '[0-9a-f]{40}' | grep -E '\.(sh|md|yml|yaml|toml|cfg|env|txt)$|Makefile|Holmakefile' )"
report soft "downloads without a checksum nearby (curl/wget of a tarball or binary)" "$(g '(curl|wget)[^|]*\.(tar\.gz|tgz|zip|deb|bin|sh|run)\b' | grep -viE 'sha256|sha512|checksum')"
report soft "toolchain pinned by tag/branch only (checkout <tag> without a SHA)" "$(g 'git checkout (v[0-9][^ ]*|main|master|develop)\b' | grep -vE '[0-9a-f]{40}')"

section "2. CI trust boundaries"
report HARD "pull_request_target used" "$(g 'pull_request_target' | grep -E '\.github/workflows/')"
report soft "workflow without an explicit permissions: block" "$(for w in $(grep -E '\.github/workflows/.*\.ya?ml$' "$F"); do grep -q '^permissions:' "$w" || echo "$w: no top-level permissions:"; done)"
report soft "cache written on pull_request events (actions/cache without a save guard)" "$(for w in $(grep -E '\.github/workflows/.*\.ya?ml$' "$F"); do if grep -qE 'pull_request' "$w" && grep -qE 'uses:[[:space:]]*actions/cache@' "$w" && ! grep -qE 'actions/cache/(restore|save)@' "$w"; then echo "$w: actions/cache on a pull_request-triggered workflow (split restore/save, save only on push)"; fi; done)"
report soft "secrets referenced in a pull_request-triggered workflow" "$(for w in $(grep -E '\.github/workflows/.*\.ya?ml$' "$F"); do grep -qE 'pull_request' "$w" && grep -nE 'secrets\.' "$w" | sed "s|^|$w:|"; done)"
report soft "load-bearing docs skipped by paths-ignore (a checker reads *.md?)" "$(g "paths-ignore" -A6 | grep -E "'\*\*/\*\.md'|'\*\.md'" )"

section "3. Generated and committed artifacts"
report HARD "tracked files that are also gitignored (stale by construction)" "$(git rev-parse --is-inside-work-tree >/dev/null 2>&1 && git ls-files -ci --exclude-standard 2>/dev/null)"
report soft "committed generated-looking files (check CI re-derives and diffs them)" "$(grep -iE '(generated|\.tsv$|\.lock$|\.sig$|_pb2\.py$|\.min\.js$)' "$F" | grep -viE 'package-lock|Cargo.lock|yarn.lock|uv.lock|poetry.lock|flake.lock' | head -20)"

section "4. Nothing baked to a machine"
report HARD "private key paths or ssh identities in code" "$(g '~/\.ssh/|\.ssh/id_[a-z0-9]+|-i \$?\{?HOME' | code | grep -vE 'README|\.md:|\.html:' )"
report soft "hostnames, IPs, users or home paths in code (should come from env)" "$(g '\b(192\.168\.[0-9]+\.[0-9]+|10\.[0-9]+\.[0-9]+\.[0-9]+|100\.64\.[0-9]+\.[0-9]+)\b|/Users/[a-z]+/|/home/[a-z]+/|[a-z]+@[a-z]+\.(local|lan)\b' | grep -vE '\.md:|example|placeholder')"
report soft "ssh/scp calls with a literal host" "$(g '\b(ssh|scp|rsync)\b[^|]*\b[a-z][a-z0-9.-]{2,}:[/~A-Za-z]' | code | grep -vE '\$\{?[A-Z_]+|\.md:|@\{' )"

section "5. Process and filesystem hygiene in scripts"
report HARD "pkill -f / killall by pattern (kills other users' processes, and your own ssh)" "$(g 'pkill -f|killall\b' | code | grep -vE '\.md:')"
report soft "fixed world-shared /tmp names (use a per-user dir under TMPDIR)" "$(g '(^|[^A-Za-z_$])/tmp/[A-Za-z0-9_.-]+' | grep -vE 'TMPDIR|mktemp|\.md:|/tmp/svenvs-\$|\$\(id -un\)')"
report soft "in-place edits of files outside the repo (sed -i / patch on \$SOME_DIR)" "$(g '(sed -i|patch -p[0-9]).*\$[A-Z_]*(DIR|ROOT|HOME)' | grep -vE 'ALLOW_INPLACE|confirm_inplace')"
report soft "rm -rf on a variable path" "$(g 'rm -rf? +"?\$' )"
report soft "curl | sh style installs" "$(g '(curl|wget)[^|]*\|[[:space:]]*(sudo )?(ba)?sh\b' | code)"
report soft "sudo in repo scripts (fine in CI steps, suspicious in user-run scripts)" "$(g '\bsudo\b' | code | grep -vE '\.github/|\.md:')"

section "6. Secrets and clutter"
report HARD "secret-looking literals" "$(g '(AKIA[0-9A-Z]{16}|ghp_[A-Za-z0-9]{20,}|xox[baprs]-[A-Za-z0-9-]{10,}|sk-[A-Za-z0-9]{20,}|-----BEGIN (RSA|OPENSSH|EC) PRIVATE KEY-----)')"
report soft "env files or credentials tracked" "$(grep -E '(^|/)(\.env|\.env\..*|credentials(\.json)?|.*\.pem|.*\.p12|id_rsa|id_ed25519)$' "$F")"
report soft "untracked large or odd files in the tree (pdf/zip/tarballs/scratch)" "$(git rev-parse --is-inside-work-tree >/dev/null 2>&1 && git ls-files --others --exclude-standard | grep -iE '\.(pdf|zip|tgz|tar\.gz|log|tmp)$|(^|/)(dbg|scratch|tmp)[^/]*$' )"

section "7. Gates that scan prose"
report soft "grep-based gates with allow-lists of phrasings (strip comments instead)" "$(g 'grep -v.*(no cheat|cheat-free|not a cheat|allow|prose)' | grep -E '\.(sh|yml|yaml)$')"

rm -f "$F"
printf '\n%s: %d hard, %d soft finding(s)\n' "$repo" "$hard" "$soft"
[ "$hard" -eq 0 ]
