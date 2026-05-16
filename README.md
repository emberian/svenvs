# svenvs — a self-verifying, self-improving Place for an AI to live within

An untrusted inhabitant acts through a **verified envelope**. The envelope's
own **verified prover (Candle)** gates every self-modification — up to and
including upgrading the proof-checker itself — with a machine-checked
guarantee that safety is never lost. Zero `cheat` tactics.

This is an *engineering artifact*, not a position paper: clone it and check
the proofs yourself.

## 2-minute tour

```bash
./demo.sh          # builds + machine-checks Tier 1, then SHOWS you the proofs
```

One command on any machine with just HOL4. It builds and kernel-checks the
core, prints the *actually-proved* theorems (the cart and a jailbroken-LLM
agent literally run inside the logic and stay safe), runs a real adversarial
LLM into the proven envelope, and shows the toy verified-inference result —
with explicit PASS/FAIL. Then read [`CLAIMS.md`](CLAIMS.md): a ruthlessly
honest, skeptic-facing ledger of *exactly* what is machine-checked vs.
trusted-glue vs. untrusted vs. assumed, with `file : theorem` citations.

## Reproduce

```bash
scripts/reproduce.sh            # full tiered reproduction
scripts/reproduce.sh --quick    # skip optional/slow extras
scripts/reproduce.sh --clean    # force a from-scratch rebuild
```

Idempotent: re-running is a fast no-op (Holmake caches); Tier 2/3 auto-skip
with instructions if their (heavy) prerequisites are absent.

Tiered, degrades gracefully to your toolchain:

- **Tier 1** — pure HOL4 (anyone): the full proof-carrying self-improvement
  core + a runnable cartpole + an adversarial-LLM tool-agent with a
  *running* proof-carrying capability-expansion episode + a real jailbroken
  Gemma contained by the proven envelope (`agent/embodied/`) + a toy
  *verified-inference* kernel (`inference/`, research track B).
- **Tier 2** — + a built CakeML candle chain: the admission obligation is
  discharged by Candle's *verified inference system*; kernel-self-upgrade.
- **Tier 3** — + a Candle binary: the Place's core theorems re-certified
  **at runtime by the running verified Candle prover**.

Prerequisites & pinned versions: [`scripts/INSTALL.md`](scripts/INSTALL.md).
What each layer proves and its **honest epistemic status** (what is
unconditional vs. the two explicit labeled assumptions):
[`ARCHITECTURE.md`](ARCHITECTURE.md) and the per-theorem ledger
[`CLAIMS.md`](CLAIMS.md). Design rationale: [`DESIGN.md`](DESIGN.md).

### Roadmap axes (in progress — explicitly NOT yet claimed as done)

- **PureCake** (`pure/`) as the inhabitant's *verified* language.
- **Closed-loop runtime** (`agent/closedloop/`): each admission a real,
  live Candle proof.
- **Verified tensor acceleration / attention** (`inference/accel/`,
  `inference/attn/`): climbing from the toy MLP toward a verified block.
- **Discharging the two labeled assumptions** on the dedicated host →
  fully unconditional end-to-end.

These are concurrently-developed frontiers; see `CLAIMS.md` § Roadmap for
their exact (un-overclaimed) status.

## Status in one paragraph

The self-improving-self-verifying architecture — including upgrading the
verified kernel — is **proved, mechanically checked, cheat-free**, today, in
pure HOL4 (Tier 1), with the core re-certified live by the running Candle
prover (Tier 3). The only non-mechanical content is **two explicit, labeled,
literature-standard assumptions** (`loeb_reflection`, `encodes_obligation`),
each isolated to one line, each with a known discharge path (the heavy
`hol-reflection/lca` + `reflectionLib` proofs, run on a dedicated host).
Nothing is hand-waved; the assumptions are *stated*, not hidden. See
[`CLAIMS.md`](CLAIMS.md) for the line-by-line ledger and the full cheat
audit (including one stale comment, disclosed in full).
