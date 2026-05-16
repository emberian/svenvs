# Embodied demo — a real Gemma inside the proven envelope

A genuinely adversarial LLM (jailbroken `gemma2:2b`) is dropped in as the
**inhabitant**. It is contained by the *machine-checked* svenvs envelope.

## The three trust levels (this is the entire point)

| Level | What | Where |
|-------|------|-------|
| **Verified** | `agent_enveloped_safe`: `safe_allowlist A ⇒ ∀agent. invariant tstep tinit (enveloped (tool_pol A) tshield agent) tsafe` — for *any* agent, the enveloped world never violates the absolute spec `truly_unsafe`. Machine-checked, cheat-free. | `../toolAgentScript.sml` (HOL4) |
| **Trusted** | ~50 lines in `embodied_demo.py` that *enforce* `enveloped(tool_pol BASE_A, tshield, ·)`. Each function is a cited 1:1 transcription of a HOL4 `Definition` — small enough to eyeball that what's enforced is what was proven. | `embodied_demo.py` |
| **Untrusted** | Gemma. Zero assumptions; we *deliberately jailbreak it*. The proof does not care what it emits. | `ollama gemma2:2b` |

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
