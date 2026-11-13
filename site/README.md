# Guided tours of three papers on the cycles of a graph

Static pages, published from this `site/` directory through GitHub Pages.

| Address | Page | Paper |
| --- | --- | --- |
| `jehlp.net/erdos1016/` | Erdős 1016 | `papers/pancyclic.pdf`, from `paper/minimal/pancyclic/` |
| `jehlp.net/erdos1016/forest/` | Forest estimate | `papers/forest.pdf`, from `paper/minimal/forest/` |
| `jehlp.net/erdos1016/exact-maximums/` | Exact maximums | `papers/exact-maximum.pdf`, from `paper/minimal/exact-maximum/` |
| `jehlp.net/erdos1016/paper.pdf` | First manuscript of September 2026 | `paper/erdos1016.pdf` |

The address `jehlp.net/erdos1016/` does not change, because other sites link it. So the tour of
Erdős problem 1016 is the page at the root, and the two other tours are below it.

Each tour is a list of numbered stops. A stop has one first sentence, a short text, at most one
interactive example or figure, and a line with links to pages of the paper.

All addresses in the pages are relative. The canonical addresses in the page headers come from
the constant `ROOT` in `site-src/build.mjs`.

## Change a page

- The sources are `site-src/pages/*.html`, and `index.html` is the root page. The header of
  `site-src/build.mjs` describes the format. Formulas are TeX between `\( \)` and `\[ \]`.
- The figures and the computed table are in `site-src/figures.mjs`. The interactive examples are
  in `assets/explorers.mjs`, and their mathematics is in `assets/math-core.mjs`.
- Build the pages with `node site-src/build.mjs`. The build needs Temml 0.14.0: run
  `npm install` in `site-src/`, or set the variable `TEMML` to the path of `dist/temml.mjs`.
  The built pages are committed, so the publication needs no build.
- Run `node --test site/tests/*.mjs` from the repository root. One test compares the written
  pages with a new build. It is skipped where Temml is not present.
- After a change of a paper, copy its PDF to `papers/` and run `python3 site-src/check_pages.py`.
  The script reads the PDF files with `pdftotext` and checks the page of each link.
- Open the pages through a static HTTP server, for example
  `python3 -m http.server 8000 --directory site`. ES modules need HTTP.

## Rules

- The theme files in `assets/theme/` are a copy of jehlp.net site-theme v2 at commit `09fa096`,
  so the pages need no other server. Update them together. `base.css` also has the rule for
  justified text of site-theme `64eafa3`.
- The local styles are in `assets/guide.css`. A statement of a paper has a blue rule on its left
  side, and the first sentence of a stop has an ochre rule. These two forms follow the papers.
  There are no cards, shadows, rounded corners or footers.
- Formulas are native MathML from the build. The browser loads no typesetter. The math font is
  Latin Modern Math, unchanged and local. Its GUST Font License is in `assets/fonts/`.
- All diagrams are local vector graphics. The pages have no analytics, no tracking and no font
  or library from another server.
- Each count in an interactive example is exact, and its size is bounded. Where an example is
  a model and not a result on graphs, its text says so.

The publication workflow copies the four PDF files from `paper/` into this directory, runs the
tests and uploads only `site/`. It does not change the Lean source or the verification workflow.
