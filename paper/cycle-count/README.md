# The number of cycles in a graph: draft manuscript

This folder contains a draft manuscript and its supporting material.
The authors are KNT, Astra, and Fable 5.2.
The manuscript is not the paper in `paper/erdos1016.tex`.

- `sharp-cycle-paper.pdf` and `sharp-cycle-paper.tex` are the current draft. The files in `sharp/` are its sections.
- `pancyclic-paper.pdf` and `pancyclic-paper.tex` are the previous draft, of 10 November 2026. It does not contain the sharp bound.
- `paper-checks/` contains tests of the statements on small graphs. See its `README.md`.
- `research/` contains the research reports and notes of November 2026. The current draft cites some of them as its supplement.
- `drafts/` contains three earlier drafts. They are kept for reference only.
- `notes/erdos1016-book-notes.md` contains research notes from the search for a shorter proof.

The current draft has three parts.

1. A graph of cyclomatic number `r` has at most `2^(r-1) + K r 2^(r/2)` cycles. This result is not formalised. Its proof is written, and two language models checked it. A part of the proof is in the supplement.
2. A graph of large cyclomatic number `r` has at most `(1/2 + o(1)) 2^r` cycles. This result is formalised in Lean.
3. A pancyclic graph on `n` vertices has at least `n + log2 n + log* n - O(1)` edges, and this is best possible up to the constant. This result is formalised in Lean.

Section 1.5 of the draft states which results are formalised.
Appendix A prints the Lean statements, names the commit of the Lean code, and gives the commands that repeat the check.
Table 3 in Appendix A lists the steps of the first result that are formalised.

Build the PDF with a LaTeX engine such as `tectonic sharp-cycle-paper.tex`.
