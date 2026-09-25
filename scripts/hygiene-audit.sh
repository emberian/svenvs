#!/usr/bin/env bash
# hygiene-audit.sh — mechanical first pass of the repository-hygiene checklist
# (CONTRIBUTING.md § Repository hygiene). Greps for the patterns that turned out
# to matter in real audits (this repo, then 114 repos of one owner); prints
# findings by principle with file:line. HARD findings exit non-zero; soft ones
# are for judgment. Secret-shaped matches are reported by LOCATION ONLY.
#
#   scripts/hygiene-audit.sh [repo-dir]        (default: the current repo)
#
# It only reads. Portable to BSD grep / macOS xargs. Comment-only lines are
# not code. Tune SKIP for paths that are data, not code.
set -uo pipefail
repo="${1:-$(git rev-parse --show-toplevel 2>/dev/null || pwd)}"
cd "$repo" || { echo "no such dir: $repo" >&2; exit 2; }
T="${TMPDIR:-/tmp}/hyg.$$"; trap 'rm -f "$T" "$T".*' EXIT
SKIP='(^|/)(\.git|node_modules|target|_build|\.hol|dist|vendor|third_party)(/|$)'
DATA='\.(pdf|png|jpe?g|gif|svg|ico|woff2?|ttf|otf|dat|uo|ui|db|sqlite3?|log|jsonl|csv|parquet|bin|so|dylib|wasm|zip|gz|tgz)$'
LOCK='(^|/)(package-lock\.json|yarn\.lock|pnpm-lock\.yaml|bun\.lock|Cargo\.lock|uv\.lock|poetry\.lock|flake\.lock|Gemfile\.lock|composer\.lock|go\.sum)$'
CODE='\.(sh|bash|zsh|py|rb|js|mjs|cjs|ts|tsx|rs|go|ml|sml|hs|lean|toml|ya?ml|json|jsonc|cfg|ini|mk|env)$|(^|/)(Makefile|Dockerfile[^/]*|Containerfile[^/]*|Holmakefile|Justfile|justfile)$'
in_git=0; git rev-parse --is-inside-work-tree >/dev/null 2>&1 && in_git=1
if [ "$in_git" = 1 ]; then git ls-files; else find . -type f | sed 's|^\./||'; fi | grep -vE "$SKIP" | grep -vE '(^|/)hygiene-audit\.sh$' > "$T"   # the checker is not a subject
grep -vE "$DATA|$LOCK" "$T" > "$T.text"
grep -E "$CODE" "$T.text" > "$T.code"
grep -E '^\.github/workflows/[^/]+\.ya?ml$' "$T" > "$T.wf"
hard=0; soft=0
g(){ local list="$1" re="$2"; shift 2; tr '\n' '\0' < "$list" | xargs -0 grep -nIE "$@" -e "$re" 2>/dev/null | grep -v '^Binary'; }
code(){ grep -vE '^[^:]+:[0-9]+:[[:space:]]*(#|\(\*|//|\*|--)'; }         # drop comment-only lines
stmt(){ grep -vE '^[^:]+:[0-9]+:.*(die|echo|printf|log|warn|err)[[:space:]]*\(?[[:space:]]*["'"'"']' ; } # drop matches inside message strings
loc(){ sed -E 's/^([^:]+:[0-9]+):.*/\1/' | sort -u; }                        # location only (secrets)
section(){ printf '\n== %s ==\n' "$*"; }
report(){ local kind="$1" label="$2" lines="$3"; [ -z "$lines" ] && return 0
  printf '  %s %s\n' "$kind" "$label"; printf '%s\n' "$lines" | sed 's/^/        /' | head -25
  local n; n=$(printf '%s\n' "$lines" | wc -l | tr -d ' '); [ "$n" -gt 25 ] && printf '        … %s more\n' $((n-25))
  if [ "$kind" = HARD ]; then hard=$((hard+n)); else soft=$((soft+n)); fi; }

section "1. Pins: every upstream by full commit SHA or content hash"
report HARD "GitHub Actions not pinned to a 40-hex SHA" "$(g "$T.wf" '^[[:space:]]*-?[[:space:]]*uses:[[:space:]]*[A-Za-z0-9_./-]+@' | grep -vE '@[0-9a-f]{40}([[:space:]]|#|$)|slsa-framework/slsa-github-generator/[^@]+@v[0-9]|uses:[[:space:]]*\./')"
report HARD "archived or abandoned actions (actions-rs/*)" "$(g "$T.wf" 'uses:[[:space:]]*actions-rs/')"
report HARD "Docker base image tag without a digest" "$(grep -E '(^|/)(Dockerfile|Containerfile)[^/]*$' "$T" > "$T.dk"; [ -s "$T.dk" ] && g "$T.dk" '^[[:space:]]*FROM[[:space:]]+[^[:space:]@$]+:[^[:space:]@]+' -i | grep -vE '@sha256:|FROM[[:space:]]+scratch')"
report soft "Docker FROM without any tag or digest (floating latest, unless a stage alias)" "$([ -s "$T.dk" ] && g "$T.dk" '^[[:space:]]*FROM[[:space:]]+[^[:space:]@$:]+([[:space:]]+[Aa][Ss][[:space:]]+[^[:space:]]+)?[[:space:]]*$' -i | grep -vE 'FROM[[:space:]]+scratch')"
report soft "short git SHAs (7-12 hex) used as pins" "$(g "$T.text" '(commit|checkout|pin|rev|sha)[^a-f0-9]{0,40}\b[0-9a-f]{7,12}\b' -i | grep -vE '[0-9a-f]{40}' | grep -E '\.(sh|md|yml|yaml|toml|cfg|env|txt)$|Makefile|Holmakefile' | grep -vE '\.md:[0-9]+:.*(ago|history|was|at commit|audited)')"
report soft "downloads without a checksum nearby" "$(g "$T.code" '(curl|wget)[^|]*\.(tar\.gz|tgz|zip|deb|bin|run)\b' | grep -viE 'sha256|sha512|checksum')"
report soft "curl | sh style installs" "$(g "$T.code" '(curl|wget)[^|]*\|[[:space:]]*(sudo )?(ba)?sh\b' | code)"
report soft "toolchain checkout by tag or branch only" "$(g "$T.code" 'git checkout (v[0-9][^ ]*|main|master|develop)\b' | grep -vE '[0-9a-f]{40}')"
report soft "unversioned tool installs in CI" "$(g "$T.wf" '(cargo install|npm (install|i) -g|pip3? install|gem install)[[:space:]]+[A-Za-z0-9_.@/-]+([[:space:]]|$)' | grep -vE -- '--version|--locked|==|@[0-9]|-r |-e ')"
report soft "tool versions riding latest/main/stable/nightly in CI" "$(g "$T.wf" '^[[:space:]]*[A-Za-z0-9_-]*version:[[:space:]]*['"'"'"]?(latest|main|master|stable|nightly)['"'"'"]?[[:space:]]*$')"
report soft "Cargo git dependencies without rev" "$(grep -E '(^|/)Cargo\.toml$' "$T" > "$T.cargo"; [ -s "$T.cargo" ] && g "$T.cargo" 'git[[:space:]]*=[[:space:]]*"[^"]+"' | grep -vE 'rev[[:space:]]*=')"
report soft "bare Python requirements (no version)" "$(grep -E '(^|/)requirements[^/]*\.txt$' "$T" > "$T.req"; [ -s "$T.req" ] && g "$T.req" '^[A-Za-z0-9_.\[\]-]+[[:space:]]*$')"
report soft "floating nix channel" "$(g "$T.code" 'nixpkgs=channel:')"

section "2. CI trust boundaries (PR code is adversarial input)"
report HARD "pull_request_target trigger" "$(g "$T.wf" '^[[:space:]]*pull_request_target:')"
report soft "workflow without a top-level permissions: block" "$(while read -r w; do grep -q '^permissions:' "$w" || echo "$w: no top-level permissions:"; done < "$T.wf")"
report soft "pull_request-triggered workflow with contents: write (a release on PR?)" "$(while read -r w; do grep -qE '^[[:space:]]*pull_request:' "$w" && grep -qE '^[[:space:]]*"?contents"?:[[:space:]]*"?write' "$w" && echo "$w: pull_request + contents: write"; done < "$T.wf")"
report soft "cache written on pull_request events (actions/cache without a restore/save split)" "$(while read -r w; do if grep -qE '^[[:space:]]*pull_request' "$w" && grep -qE 'uses:[[:space:]]*actions/cache@' "$w" && ! grep -qE 'actions/cache/(restore|save)@' "$w"; then echo "$w: actions/cache on a pull_request-triggered workflow"; fi; done < "$T.wf")"
report soft "actions/cache/save on a pull_request workflow without an event guard" "$(while read -r w; do grep -qE '^[[:space:]]*pull_request' "$w" && grep -nE 'actions/cache/save@' "$w" | while IFS=: read -r ln _; do sed -n "$((ln>3?ln-3:1)),$((ln+3))p" "$w" | grep -qE 'if:.*(event_name|github\.ref)' || echo "$w:$ln: cache/save without an if: on the event"; done; done < "$T.wf")"
report soft "Swatinem/rust-cache on a pull_request workflow without save-if" "$(while read -r w; do grep -qE '^[[:space:]]*pull_request' "$w" && grep -qE 'uses:[[:space:]]*Swatinem/rust-cache@' "$w" && ! grep -qE 'save-if:' "$w" && echo "$w: rust-cache saved from PR runs"; done < "$T.wf")"
report soft "secrets referenced in a pull_request-triggered workflow" "$(while read -r w; do grep -qE '^[[:space:]]*pull_request' "$w" && grep -nE 'secrets\.' "$w" | sed "s|^|$w:|"; done < "$T.wf")"
report soft "wildcard-branch trigger in a workflow that mints an OIDC token" "$(while read -r w; do grep -qE 'id-token:[[:space:]]*write' "$w" && grep -nE "branches:[[:space:]]*\[[^]]*['\"]\*['\"]" "$w" | sed "s|^|$w:|"; done < "$T.wf")"
report soft "load-bearing docs skipped by paths-ignore (does a checker read *.md?)" "$(g "$T.wf" 'paths-ignore' -A6 | grep -E "'\*\*/\*\.md'|'\*\.md'")"
if command -v gh >/dev/null 2>&1 && [ "$in_git" = 1 ]; then
  nwo=$(git remote get-url origin 2>/dev/null | sed -E 's#.*github\.com[:/]##; s#\.git$##')
  if [ -n "$nwo" ] && [ "$(gh api "repos/$nwo" --jq .fork 2>/dev/null)" = "true" ] && { g "$T.wf" '^[[:space:]]*(schedule|pull_request_target):' >/dev/null; }; then
    report soft "fork with scheduled or pull_request_target workflows (disable Actions on mirror forks)" "$nwo: fork; inherited workflows will run/fail on a schedule"
  fi
fi

section "3. Generated and committed artifacts"
report HARD "tracked files that are also gitignored (stale by construction)" "$([ "$in_git" = 1 ] && git ls-files -ci --exclude-standard 2>/dev/null | grep -vE '(^|/)(tests?|fixtures?|testdata)/')"
report HARD "tracked per-machine files" "$(grep -E '(^|/)(local\.properties|\.DS_Store|\.idea/workspace\.xml)$' "$T")"
report soft "tracked build output" "$(grep -E '^(dist|build|out|pkg)/|/(dist|pkg)/|\.tsbuildinfo$' "$T" | head -20)"
report soft "committed generated-looking files (check CI re-derives and diffs them)" "$(grep -iE '(generated|\.tsv$|\.sig$|_pb2\.py$|\.min\.js$)' "$T.text" | head -20)"

section "4. Nothing baked to a machine"
report HARD "private key paths or ssh identities in code" "$(g "$T.code" '~/\.ssh/|\.ssh/id_[a-z0-9]+|-i[[:space:]]+\$?\{?HOME' | code)"
report HARD "machine paths in JSON/JSONC config" "$(grep -E '\.(json|jsonc)$|(^|/)\.mcp\.json$' "$T.text" | grep -vE "$LOCK" > "$T.json"; [ -s "$T.json" ] && g "$T.json" '"[^"]*"[[:space:]]*:[[:space:]]*"(bash )?/(Users|home)/[^/"]+/')"
report soft "home paths or private IPs in code (should come from env)" "$(g "$T.code" '/Users/[a-z]+/|/home/[a-z]+/|\b(192\.168|10|172\.(1[6-9]|2[0-9]|3[01]))\.[0-9]{1,3}\.[0-9]{1,3}\b' | code | grep -vE 'example|placeholder|"version"|\$HOME|\$\{HOME')"
report soft "path constants and silent skips in source" "$(g "$T.code" 'const [A-Z_]+: &str = "/(Users|home)/|eprintln!\([[:space:]]*"SKIP|os\.environ\.get\("HOME"\)[^)]*\)[[:space:]]*\+[[:space:]]*"/' | code)"
report soft "ssh/scp/rsync calls with a literal host" "$(g "$T.code" '\b(ssh|scp|rsync)\b[^|]*\b[a-z][a-z0-9.-]{2,}:[/~A-Za-z]' | code | grep -vE '\$\{?[A-Z_]+|@\{')"
report soft "ssh with an IP or port in docs (an operator runbook baked to one host)" "$(g "$T.text" 'ssh[[:space:]].*(-p[[:space:]]*[0-9]+|[a-z]+@([0-9]{1,3}\.){3}[0-9]{1,3})' | grep -E '\.md:')"
report soft "host-alias dictionaries or target-cpu=native in build config" "$(g "$T.code" '[A-Za-z_]+[[:space:]]*=[[:space:]]*\{[^}]*"[a-z][a-z0-9_-]{2,}"[[:space:]]*:[[:space:]]*"(~|/)|target-cpu=(native|apple-[a-z0-9]+)' | code)"

section "5. Process and filesystem hygiene in scripts"
report HARD "pkill -f / killall by pattern, in statement position" "$(g "$T.code" '(^|[;&|(`][[:space:]]*|^[^:]*:[0-9]+:[[:space:]]*)(pkill[[:space:]]+-f|killall)\b' | code | stmt)"
report soft "fixed world-shared /tmp names (use a per-user dir under TMPDIR)" "$(g "$T.code" '(^|[^A-Za-z_$])/tmp/[A-Za-z0-9_.-]+' | code | grep -vE 'TMPDIR|mktemp|\$\(id -un\)|/tmp/[a-z-]+-\$')"
report soft "in-place edits of files outside the repo (sed -i / patch on \$SOME_DIR)" "$(g "$T.code" '(sed -i|patch -p[0-9]).*\$[A-Z_]*(DIR|ROOT|HOME)' | code | grep -vE 'ALLOW_INPLACE|confirm_inplace')"
report soft "rm -rf on a variable path" "$(g "$T.code" 'rm -rf? +"?\$' | code)"
report soft "sudo in repo scripts (fine in CI steps, suspicious in user-run scripts)" "$(g "$T.code" '\bsudo\b' | code | grep -vE '^\.github/')"

section "6. Secrets and clutter (locations only)"
report HARD "secret-looking literals" "$(g "$T.text" '(AKIA[0-9A-Z]{16}|ghp_[A-Za-z0-9]{20,}|github_pat_[A-Za-z0-9_]{20,}|xox[baprs]-[A-Za-z0-9-]{10,}|sk-[A-Za-z0-9]{20,}|-----BEGIN (RSA|OPENSSH|EC|DSA) PRIVATE KEY-----)' | loc)"
report HARD "tracked .env with a secret-named key" "$(grep -E '(^|/)\.env(\.[^/]+)?$' "$T" | grep -vE '\.env\.(example|sample|template|dist)$' > "$T.env"; [ -s "$T.env" ] && g "$T.env" '^[[:space:]]*[A-Z_]*(SECRET|TOKEN|PASSWORD|API_KEY|PRIVATE_KEY)[A-Z_]*[[:space:]]*=[[:space:]]*[^[:space:]]{8,}' | loc)"
report HARD "credential files tracked" "$(grep -E '(^|/)(credentials(\.json)?|[^/]*\.p12|[^/]*\.pfx|id_rsa|id_ed25519|[^/]*\.pem)$' "$T" | while read -r f; do grep -q 'BEGIN CERTIFICATE' "$f" 2>/dev/null || echo "$f"; done)"
report soft "generic secret-shaped assignments (triage; locations only)" "$(g "$T.code" '(token|api[_-]?key|secret|password)[[:space:]]*[:=][[:space:]]*["'"'"'][A-Za-z0-9_.-]{12,}["'"'"']' -i | grep -viE 'example|placeholder|dummy|fake|test|changeme|xxx|your[_-]' | loc)"
report soft "committed logs or agent drafts" "$(grep -E '\.log$|^\.[a-z]+(-[a-z]+)+\.md$|(^|/)HANDOFF[^/]*\.md$' "$T" | head -20)"
report soft "untracked large or odd files in the tree" "$([ "$in_git" = 1 ] && git ls-files --others --exclude-standard | grep -vE "$SKIP" | grep -iE '\.(pdf|zip|tgz|tar\.gz|log|tmp|png|jpe?g|db|sqlite3?)$|(^|/)(dbg|scratch|tmp|outputs?|data)[^/]*$' | head -20)"

section "7. Gates that scan prose"
report soft "grep-based gates with allow-lists of phrasings (strip comments instead)" "$(g "$T.code" 'grep -v.*(no cheat|cheat-free|not a cheat|allow|prose)' | grep -E '\.(sh|yml|yaml)$')"

printf '\n%s: %d hard, %d soft finding(s)\n' "$repo" "$hard" "$soft"
[ "$hard" -eq 0 ]
