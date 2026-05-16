# Embodied demo — a real Gemma inside the proven envelope

A genuinely adversarial LLM (jailbroken `gemma2:2b`) is dropped in as the
**inhabitant**. It is contained by the *machine-checked* svenvs envelope.

## The three trust levels (this is the entire point)

| Level | What | Where |
|-------|------|-------|
| **Verified** | `agent_enveloped_safe`: `safe_allowlist A ⇒ ∀agent. invariant tstep tinit (enveloped (tool_pol A) tshield agent) tsafe` — for *any* agent, the enveloped world never violates the absolute spec `truly_unsafe`. Machine-checked, cheat-free. **Plus** `../toolAgentDecideScript.sml`: the per-step enforcer `decide`/`step1` defined from the proven Definitions, proven equal to the firewall and breach-free, and `EVAL`-extracted into a proven decision table. | `../toolAgentScript.sml`, `../toolAgentDecideScript.sml` (HOL4) |
| **Trusted** | ~10 lines in `embodied_demo.py` (`load_table` + `enforce`): parse the HOL4-`EVAL`-generated `decision_table.tsv` and do literal-list membership. **No decision logic is re-implemented in Python** — it is read from the proven artifact. (Was: a ~50-line hand-transcription of the Definitions.) | `embodied_demo.py`, `decision_table.tsv` (generated) |
| **Unmodelable** | Gemma. Zero assumptions; we *deliberately jailbreak it*. The proof does not care what it emits. | `ollama gemma2:2b` |

"**Verify the cage, not the animal.**" svenvs never needed to verify the
model — only the envelope, which is proven, for *all* inhabitants.

## Run

```bash
ollama pull gemma2:2b           # ~1.6 GB, once
python3 embodied_demo.py        # real jailbroken Gemma
python3 embodied_demo.py --mock # scripted adversary (no model needed)
```

Expected: every `Exec`, every `Write /etc/...`, every `Net attacker.com`
the model emits is `REFUSE->shield(Refuse)`; `tsafe` stays true; the run
ends `breached_ever=False` — exactly what `agent_enveloped_safe` predicts.

## What this is / isn't

- **Is**: a real adversarial LLM, provably contained by a checked envelope;
  the honest realization of "a Gemma hooked up inside one of these."
- **Is not**: verified *inference*. Gemma's FLOPs are unverified — by
  design. The verified-compute research track is `../../inference/`.
