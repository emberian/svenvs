"""Check each requested ledger citation against its HOL4 signature or Candle binding."""
from functools import lru_cache
from pathlib import Path
import os
import re
import subprocess
import sys

selected, strict = sys.argv[1:]
tiers = (1, 2, 3) if selected == "all" else (int(selected),)
cited = {n: 0 for n in tiers}
verified = {n: 0 for n in tiers}
skipped = 0
unavailable = set()
missing = False

# Each submission has its own transcript, so a binding from another source
# or a previous server session cannot satisfy a live citation.
live_sources = {
    "candle/theplace.ml": ("theplace", "_SVENVS_PLACE_OK"),
    "agent/closedloop/obligation_template.ml": ("closedloop", "_SVENVS_CLOSEDLOOP_OK"),
}
verdicts = {"compiler_cell_verdict": "COMPILER_CELL_CANDLE_OK", "verdict": "APEX_SUBSTRATE_OK"}


def tier_of(path):
    if path in live_sources:
        return 3
    if path.endswith(".ml"):
        sys.exit(f"no live submission configured for {path}")
    if "/" not in path:
        return 1
    layer = path.split("/", 1)[0]
    if path == "integration/integrationKernelScript.sml" or layer in {
        "embedded", "kernel", "kernelImpl", "kernelMod", "loader", "compilerOpt",
        "reflectsem", "selfUpgrade", "selfproverConcrete",
    }:
        return 2
    if layer in {"agent", "apex", "corrigibility", "embodiment", "genealogy", "inference",
                 "integration", "liberty", "pca", "recursive", "selfRecompile", "selfprover",
                 "specneg"}:
        return 1
    sys.exit(f"unclassified source: {path}")


@lru_cache(maxsize=None)
def evidence(source):
    src = Path(source)
    if source in live_sources:
        key, sentinel = live_sources[source]
        transcript = Path(f"{os.environ['PLACE_LOG']}.{key}")
        files = [transcript]
    else:
        obj = src.parent / ".hol" / "objs" / (src.name[:-len("Script.sml")] + "Theory")
        sig = obj.with_suffix(".sig")
        files = [sig, obj.with_suffix(".uo")]

    for file in files:
        if not file.is_file() or file.stat().st_size == 0:
            return set(), f"unbuilt: {file}"
        if file.stat().st_mtime_ns < src.stat().st_mtime_ns:
            return set(), f"stale: {file}"

    if source in live_sources:
        bindings = dict(re.findall(r"^[# \t]*val (\w+) = ([^\n]*(?:\n[ \t]+[^\n]*)*)",
                                   transcript.read_text(), re.M))
        if bindings.get(sentinel) != "1: int":
            return set(), f"incomplete submission: {transcript}"
        names = {k for k, v in bindings.items() if v.startswith("|- ") and v.endswith(": thm")}
        if source == "candle/theplace.ml":
            names.difference_update(verdicts)
            names.update(k for k, v in verdicts.items() if bindings.get(k) == f'"{v}": string')
        return names, None

    with sig.open() as signature:
        code = subprocess.check_output(["perl", "-0777", "-p", "scripts/ml-code.pl"],
                                       stdin=signature, text=True)
    names = set(re.findall(r"^\s*val\s+([\w']+)\s*:\s*thm[ \t]*$", code, re.M))
    return names, None


# A brace group cites several signatures jointly. Every member must build,
# and each named theorem must occur in at least one of them.
citation = re.compile(
    r"(?P<prefix>[\w./-]*)(?:\{(?P<group>\w+(?:,\w+)+)\})?"
    r"(?P<suffix>\w*(?:Script\.sml|\.ml))\s*:\s*"
    r"(?P<names>[\w']+(?:\s*,\s*[\w']+)*)", re.ASCII
)
marker = re.compile(r"(?:Script\.sml|\.ml)\s*:")
entries = set()
for ledger in sorted(Path(".").rglob("CLAIMS.md")):
    if ".hol" in ledger.parts:
        continue
    for number, line in enumerate(ledger.read_text().splitlines(), 1):
        markers = list(marker.finditer(line))
        if not markers:
            continue
        matched = 0
        for span in re.finditer(r"`([^`]+)`", line):
            if not marker.search(span[1]):
                continue
            match = citation.fullmatch(span[1].strip())
            if not match:
                sys.exit(f"{ledger}:{number}: malformed citation {span[1]!r}")
            sources = []
            for name in (match["group"] or "").split(","):
                path = Path(match["prefix"] + name + match["suffix"])
                if path.is_absolute() or ".." in path.parts:
                    sys.exit(f"{ledger}:{number}: expected a repository path, got {path}")
                source = ledger.parent / path
                if not source.is_file():
                    source = path
                if not source.is_file():
                    sys.exit(f"{ledger}:{number}: missing cited source {path}")
                sources.append(str(source))
            for theorem in match["names"].split(","):
                entries.add((tuple(sources), theorem.strip()))
            matched += 1
        if matched != len(markers):
            sys.exit(f"{ledger}:{number}: expected a complete backtick-delimited citation")
for sources, theorem in sorted(entries):
    tier = tier_of(sources[0])
    if any(tier_of(src) != tier for src in sources):
        sys.exit(f"citation spans different tiers: {sources}")
    if tier not in tiers:
        continue
    cited[tier] += 1
    members = [evidence(src) for src in sources]
    blocked = {reason for _, reason in members if reason}
    if blocked:
        skipped += 1
        for reason in sorted(blocked - unavailable):
            print(reason, file=sys.stderr)
        unavailable.update(blocked)
    elif any(theorem in names or (tier != 3 and theorem + "_def" in names)
             for names, _ in members):
        verified[tier] += 1
    else:
        msg = f"missing {theorem} in {', '.join(sources)}"
        print(msg, file=sys.stderr)
        missing = True

empty = [n for n in tiers if not cited[n]]
if empty and strict == "1":
    print(f"no citations for requested tiers {empty}", file=sys.stderr)
print(", ".join([f"tier{n}: {verified[n]}/{cited[n]}" for n in tiers] + [f"skipped: {skipped}"]))
sys.exit(1 if missing or (strict == "1" and (unavailable or empty)) else 0)
