# Two minimal papers

KNT asked for these two papers on 11 November 2026. Fable 5.2 wrote them and owns this folder.
Each paper has one aim and no side results.

| Paper | Aim | Source | Pages |
|---|---|---|---|
| [exact-maximum.pdf](exact-maximum/exact-maximum.pdf) | `psi(r) = H(r)` for all large `r` (the formulas of Horak and Kim), and nothing else | `exact-maximum/exact-maximum.tex` and `exact-maximum/sections/` | 49 |
| [pancyclic.pdf](pancyclic/pancyclic.pdf) | Erdős Problem #1016: `log n + log* n - O(1) <= h(n) <= floor(log n) + log* n + 1` | `pancyclic/pancyclic.tex` | 7 |

The second paper uses one theorem of the first paper, the forest estimate (Theorem 3.1).
The first paper is complete in itself.

Both papers use the design in `style/preamble.tex`: a title block, the proof in a few numbered
sentences, boxed statements, idea boxes, proofs with a rule at the left, and annotated figures.
The design follows the guide on the Riemann hypothesis of 9 November 2026.
In plain `article` layout the two papers had 37 and 5 pages.

Build each paper in its folder:

```sh
tectonic --keep-logs exact-maximum.tex
```

```sh
tectonic --keep-logs pancyclic.tex
```

## How the first paper differs from the other manuscripts

`../cycle-count/foundations-paper.tex` (Astra) and `../cycle-count/sharp-cycle-paper.tex` (Fable)
contain the same proof ideas and many more results.
The first paper here keeps only the steps that the equation `psi(r) = H(r)` needs.

- It has no classification of the graphs with many cycles. It does not define necklaces.
- It has no statement on the graphs that attain the maximum, and no stability theorem.
- A graph with a cyclic cut of at most three edges gets the bound `2^(r-1) + O(2^(r/2))` directly.
  The gap theorem is used for cuts of four edges only.
- The case of large girth uses the bound `q(G,P) < 2/5` (Theorem 8.1).
  This removes the induction on the rank of the earlier proof.
- The lemmas on cycles of moderate length (Section 3.2) are stated once with free parameters.
  Section 3 and Section 8 both use them.

## Status

The proofs are written. The two models have read them. No referee has read them.
The forest estimate for `|E(W)| <= sqrt(r)`, the bound `psi(r) <= (1/2 + o(1)) 2^r`, and both
bounds of the pancyclic theorem are formalised in Lean 4 at commit `a5cb5fa`.
The exact maximum is formalised in Lean 4 (12 November 2026, 01:45 UTC):
`Erdos1016.ExactMaximum.exactMaximum : ∃ R, ∀ r, R ≤ r → CycleCount.maxCycles r = horakKim r`,
with the axioms `propext`, `Classical.choice` and `Quot.sound` only. The files are at commit
`3a80aa9` (branch `feat/cycle-count-bound`). `Erdos1016/ExactMaximum/README.md` says who proved
which part: Fable 5.2 wrote `Erdos1016/ExactMaximum/`, and Astra wrote
`Erdos1016/ExactMaximumSupport/`; the gap theorem (Theorem 5.10), by Astra, was the last part.
The Lean kernel checks the formal statement. It does not check the text of the paper, and no
referee has read the text.

In the text, the proof of Proposition 5.3 no longer adds a new vertex to the pole (11 November
2026, 21:50 UTC): Step 1 adds the shortest path `A` to each path. The statement is the same, and
the constant uses `Theta_{eps/2}(1)` in place of `Theta_{eps/2}(2)`.
