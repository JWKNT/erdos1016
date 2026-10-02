# Erdős 1016 interactive proof guide

Dependency-free static guide, published from this `site/` directory through GitHub Pages.

- Open via any static HTTP server (for example `python3 -m http.server 8000 --directory site`). ES modules require HTTP.
- Run `node --test site/tests/*.mjs` from the repository root.
- Source mathematical revision: `d1bf348d5cbf6a7e4ecfbff58c47344debb3c771`.
- Source Lean certificate: https://github.com/JWKNT/erdos1016/actions/runs/36203783167
- Shared-theme files are vendored from jehlp.net site-theme v2 at commit `09fa096` for self-contained rendering; update them together, preserving the theme contract.
- All diagrams are local vector geometry or PNG symbols. No analytics, tracking, external font or runtime library is needed.
- All enumerations are exact and deliberately bounded. The asymptotic demonstrations are identified as illustrations, not graph evidence.

The publication workflow tests the examples and uploads only `site/`. It does not modify the Lean source, pinned dependencies, or verification workflow.
