# svenvs site

A hand-written, framework-free static site explaining the svenvs project for
a non-expert audience. Two files do everything:

- `index.html` — the page (progressive depth: hook → plain-language what/why →
  the layered narrative → an inline-SVG architecture diagram → an honest
  "proven vs assumed" section → real theorem/transcript receipts → reproduce).
- `style.css` — all styling (dark, responsive, system-font, accessible).

No build step. No JavaScript. The SVG diagram is inline in `index.html`.

## Preview locally

```bash
cd site
python3 -m http.server 8000
# then open http://localhost:8000
```

(Or just open `site/index.html` directly in a browser — it has no
same-origin dependencies.)

## Deployment — LIVE

The site is published at **<https://emberian.github.io/svenvs/>**.

`.github/workflows/pages.yml` is a standard GitHub Pages deploy via Actions
(`configure-pages` + `upload-pages-artifact` from `site/` + `deploy-pages`,
least-privilege permissions). GitHub Pages is enabled (Settings → Pages →
Source: "GitHub Actions"), so **every push touching `site/**` auto-deploys** —
the live URL appears in the workflow run's `deploy` job. A manual run is also
available via **Actions → Deploy site to GitHub Pages → Run workflow**.

To take it down, disable Pages in Settings → Pages, or remove
`.github/workflows/pages.yml`.

Until step 3 is done by a human, the workflow is inert.

## Honesty note

The copy mirrors the repository's epistemic status exactly: the core,
cartpole, LLM-agent, base Candle-kernel soundness, and the live-certified
Place are stated as unconditional and machine-checked; kernel self-upgrade
and the reflection seam are stated as conditional on two explicit, labelled
assumptions (`loeb_reflection`, `encodes_obligation`) that are not yet
discharged end-to-end. No claim on the page exceeds `ARCHITECTURE.md` /
`DESIGN.md`. The Gemma transcript is labelled as an illustrative run in the
exact format `agent/embodied/embodied_demo.py` produces — wording of the
model's lines varies per sample; the envelope verdict and
`breached_ever=False` are what the theorem guarantees.
