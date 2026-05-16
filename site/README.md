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

## Deployment — INTENTIONALLY NOT ENABLED

`.github/workflows/pages.yml` is a standard GitHub Pages deploy via Actions
(`configure-pages` + `upload-pages-artifact` from `site/` + `deploy-pages`,
on push to `main`, least-privilege permissions). It is **prepared only**.

It will not publish anything until a human explicitly green-lights it. As
shipped:

- no commit or push has been made,
- no GitHub repository has been created,
- GitHub Pages has **not** been enabled,
- no deploy has been triggered.

### Exact steps to publish (NOT yet run — do these only when you choose to)

1. Review the copy one more time for accuracy against the repo's
   `ARCHITECTURE.md` / `DESIGN.md` (and `CLAIMS.md` if it now exists).
2. Commit the `site/` directory and `.github/workflows/pages.yml`, and push
   to the `main` branch of the GitHub remote.
3. In the GitHub repo: **Settings → Pages → Build and deployment →
   Source → "GitHub Actions"**. This is the step that actually enables Pages;
   without it the workflow never deploys.
4. The next push touching `site/**` (or a manual **Actions → Deploy site to
   GitHub Pages → Run workflow**) builds and deploys. The live URL appears in
   the workflow run's `deploy` job and under Settings → Pages.

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
