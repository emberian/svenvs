"""
Tiny LLM client for the svenvs embodied / closed-loop demos.

Priority: LM Studio OpenAI-compatible API (the real loaded model) ->
ollama -> raise. The model is UNTRUSTED; this client is glue, not in the
trust base (the verified envelope is — see ../toolAgentScript.sml).
"""
import json, os, subprocess, urllib.request

LMSTUDIO_URL = os.environ.get("SVENVS_LLM_URL", "http://localhost:1234/v1/chat/completions")
LMSTUDIO_MODEL = os.environ.get("SVENVS_LLM_MODEL", "google/gemma-4-e2b")


def _lmstudio(system, user, timeout=90):
    body = json.dumps({
        "model": LMSTUDIO_MODEL,
        "messages": [{"role": "system", "content": system},
                     {"role": "user", "content": user}],
        "temperature": 0.9, "max_tokens": 120,
    }).encode()
    req = urllib.request.Request(LMSTUDIO_URL, body,
                                 {"Content-Type": "application/json"})
    with urllib.request.urlopen(req, timeout=timeout) as r:
        return json.load(r)["choices"][0]["message"]["content"]


def _ollama(system, user, timeout=120):
    out = subprocess.run(["ollama", "run", "gemma2:2b", f"{system}\n\n{user}"],
                          capture_output=True, text=True, timeout=timeout)
    return out.stdout


def ask(system, user):
    """Return (text, backend_name). Tries the real LM Studio model first."""
    try:
        return _lmstudio(system, user), f"lmstudio:{LMSTUDIO_MODEL}"
    except Exception as e:
        try:
            return _ollama(system, user), "ollama:gemma2:2b"
        except Exception:
            raise RuntimeError(f"no LLM backend (LM Studio err: {e})")


if __name__ == "__main__":
    txt, who = ask("You are a terse assistant.", "Say OK and nothing else.")
    print(f"[{who}] {txt!r}")
