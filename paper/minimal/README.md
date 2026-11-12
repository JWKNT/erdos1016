# Three minimal papers

KNT asked for two papers on 11 November 2026. On 12 November 2026 KNT and Astra asked for a
split into three papers ("option B" of Astra's plan): the forest estimate has a paper of its
own, and the two applications cite it. Fable 5.2 wrote the three papers and owns this folder.
Each paper has one aim and no side results.

| Paper | Aim | Source | Pages |
|---|---|---|---|
| [forest.pdf](forest/forest.pdf) | The forest estimate: `q(Gamma,P) <= 1/2 + 20/log log log r` for a random even subgraph, with a complete proof | `forest/forest.tex` | 13 |
| [pancyclic.pdf](pancyclic/pancyclic.pdf) | Erdős Problem #1016: `log n + log* n - O(1) <= h(n) <= floor(log n) + log* n + 1` | `pancyclic/pancyclic.tex` | 7 |
| [exact-maximum.pdf](exact-maximum/exact-maximum.pdf) | `psi(r) = H(r)` for all large `r` (the formulas of Horak and Kim), and nothing else | `exact-maximum/exact-maximum.tex` and `exact-maximum/sections/` | 36 |

The forest paper is complete in itself. It names the two applications in a short subsection
and does not prove them. The pancyclic paper cites Corollary 1.2 of the forest paper (a union of
cycles in a simple graph). The maximum-cycles paper cites Theorem 1.1, Lemmas 2.2 to 2.4 and
Proposition 3.4 of the forest paper, and states them in its Section 2 without proof. Neither
application paper repeats the proof of the estimate. The asymptotic corollary
`psi(r) ~ 2^(r-1)` stays in the maximum-cycles paper (its Section 3).

All papers use the design in `style/preamble.tex`: a title block, the proof in a few numbered
sentences, boxed statements, idea boxes, proofs with a rule at the left, and annotated figures.
The design follows the guide on the Riemann hypothesis of 9 November 2026.

Build each paper in its folder, and read the log (no `Overfull`, no undefined reference):

```sh
tectonic --keep-logs forest.tex
```

```sh
tectonic --keep-logs pancyclic.tex
```

```sh
tectonic --keep-logs exact-maximum.tex
```

## How the maximum-cycles paper differs from the other manuscripts

`../cycle-count/foundations-paper.tex` (Astra) and `../cycle-count/sharp-cycle-paper.tex` (Fable)
contain the same proof ideas and many more results. The paper here keeps only the steps that the
equation `psi(r) = H(r)` needs.

- It has no classification of the graphs with many cycles. It does not define necklaces.
- It has no statement on the graphs that attain the maximum, and no stability theorem.
- A graph with a cyclic cut of at most three edges gets the bound `2^(r-1) + O(2^(r/2))` directly.
  The gap theorem is used only for a graph with a cycle of length four.
- The last case is girth at least five. It uses the bound `q(G,P) < 2/5` (Theorem 7.1).
  There is no case of bounded girth and no induction on the rank.
- The forest estimate and the facts on cycles of moderate length are quoted from the forest
  paper (Section 2). Sections 3 to 7 use them.

## The split (12 November 2026)

Before the split the maximum-cycles paper had 42 pages and contained the proof of the forest
estimate (its Sections 2, 3.1 and 3.2). That version is in `research/single-paper-12-nov/`
(sources and PDF). KNT had read it and called it good; the split changed no proof.

| Moved or changed | From | To |
|---|---|---|
| Second moment, link formula, exceptional partners, many small cuts, with proofs | Section 2 of the maximum-cycles paper | Section 2 of the forest paper |
| Walks without backtracking, closed walks, cycle weight, the second moment, logarithmic girth, with proofs | Section 3.1 of the maximum-cycles paper | Section 3 of the forest paper |
| Proof of the forest estimate | Section 3.2 of the maximum-cycles paper | Section 4 of the forest paper |
| The form for a simple graph, with the proof by splitting and cleaning | Section 2 of the pancyclic paper | Corollary 1.2 and Section 5 of the forest paper |
| Cubic multigraphs, cycles and a marked set, leading term | Section 3.3 of the maximum-cycles paper | Section 3 of the maximum-cycles paper (it stays) |

New in the forest paper: the introduction with a figure of outside parts; a ring of copies of
`K_{2,2}` that shows that the constant `1/2` cannot be lowered (fine print after Theorem 1.1);
three sentences on the place where each hypothesis on `P` is used; the subsection on the two
applications; an outline box at the start of Section 3; a figure of the splitting step.
`checks/ring_half_check.py` enumerates the even subgraphs of the ring for `k = 2, ..., 6` and
confirms the count `2^(2k)` and `q >= 1/2` (exit code 0; the values of `q` are 15/16, 53/64,
185/256, 657/1024, 2401/4096).

Numbers of the statements in the maximum-cycles paper after the split: Theorem 2.1 (forest
estimate), Lemmas 2.2 to 2.4, Proposition 2.5 (cycles of moderate length), Lemma 3.1 (cubic
multigraphs), Lemma 3.2 (cycles and a marked set), Corollary 3.3 (leading term). They were 3.1,
2.2 to 2.4, 3.5, 3.6, 3.7 and 3.8. Sections 4 to 8 keep their numbers. The paper now has 37
numbered statements and 15 figures. Proposition 2.5 states in one place what Section 7.5 takes
from the forest paper: the girth of `J`, the load of a vertex, the bound for the weight `mu`,
and a random variable `Z` with the bound for its second moment.

In the pancyclic paper the section on authorship has three short paragraphs and no table, as in
the other two papers.

## Status (12 November 2026)

Checked by the Lean kernel, with the axioms `propext`, `Classical.choice` and `Quot.sound` only:

- The forest estimate in both forms of the forest paper:
  `Erdos1016.ShortProof.eventually_marked_forest_bound_logSquared` (Theorem 1.1) and
  `Erdos1016.ShortProof.fewComponentForestEstimate_logSquared` (Corollary 1.2). Commit `3a80aa9`.
- Both bounds of the pancyclic theorem, `Erdos1016.mainTheorem`. Commit `a5cb5fa`.
- The main theorem of the maximum-cycles paper,
  `Erdos1016.ExactMaximum.exactMaximum : ∃ R, ∀ r, R ≤ r → CycleCount.maxCycles r = horakKim r`.
  Commit `3a80aa9`. The paper cites this declaration.
- The same theorem along the three cases of the present text,
  `Erdos1016.ExactMaximum.exactMaximum_threeCases` (`Erdos1016/ExactMaximum/MainThreeCases.lean`).
  Its third case uses the older and longer route (a cyclic cut of size four, bounded girth,
  girth at least some `D >= 256`). Commit `45bd19c`, with the audit
  `audits/ExactMaximumThreeCasesAudit.lean`.

Not checked by a machine: the texts of the three papers. For the maximum-cycles paper one
statement of the route of the text has no formal proof at all:

- **Theorem 7.1 (girth five)**, with Lemmas 7.4, 7.5, 7.6 and Corollary 7.7, and the forms of
  Propositions 7.9, 7.11 and 7.12 that count the short cycles. In Lean the statement is the
  definition `Erdos1016.ExactMaximum.GirthForestStatement 5`. The theorem
  `Erdos1016.ExactMaximum.exactMaximumStatement_of_girthFiveForest` proves the main theorem
  from this one hypothesis, with the method of Section 8. The formal development proves the
  statement for some girth `D >= 256` in the place of five.

Other parts of the text have a formal statement that is proved in another way: Lemma 5.3 (a
shortest path) and the proof of Theorem 5.5 from it; Lemma 5.6; Theorem 5.7 (gap) as a
corollary; Theorem 6.6 with the cycle of length four as one side; Corollary 3.3 from the
marked set. `Erdos1016/ExactMaximum/README.md` has the table, statement by statement.

Readers of the text: the parts from the research notes 1, 2 and 3 have had one reader,
Fable 5.2. Astra's proposals have had two, Astra and Fable 5.2. No referee has read a text.
`SHORTENING-NOTES.md` has the history with measured line counts.

## Lean statements for the forest paper

The declarations are in the commit `3a80aa9`. The proof map of the repository
(`docs/proof-map.md`) has more detail. `E` is `Erdos1016`.

| Forest paper | Lean | Remark |
|---|---|---|
| Theorem 1.1 | `E.ShortProof.eventually_marked_forest_bound_logSquared` (`Erdos1016/Probability/Avoidance/LogSquaredMarkedForest.lean`) | The rank is `2^x` for a real `x`, and the statement holds for all large `x`. `regionForestProbability Pᶜ` is `q(Gamma,P)` |
| Corollary 1.2 | `E.ShortProof.fewComponentForestEstimate_logSquared` (same file) | For a `PhysicalGraph` (a simple graph) and a nonempty finite set of cycle words |
| Lemma 2.1 (second moment) | `Erdos1016/Probability/Moments/WeightedSecondMoment.lean` (`zero_density_le_half_add_of_second_moment`) | |
| Lemma 2.2 (link formula) | `Erdos1016/CycleSpace/Graphical/RegionCutLaw.lean`, `DisjointRegionCuts.lean`; the conditional laws: `Erdos1016/Probability/Cylinders/RegionCycleEvents.lean` | |
| Lemma 2.3 (exceptional partners) | `Erdos1016/Graph/TerminalForest.lean`, `Erdos1016/CycleSpace/Graphical/ExceptionalPartners.lean` | |
| Lemma 2.4 (many small cuts) | `Erdos1016/Probability/Moments/SmallCutRegionBound.lean` | |
| Lemma 3.1 and (3.1) (walks, load of a vertex) | `Erdos1016/Cycles/Counting/LowDegreeVertexMass.lean` | |
| Lemma 3.2 (closed walks) | `Erdos1016/Nonbacktracking/Spectrum/DeficitContinuity.lean`, `DeficitSpectralBound.lean`, `DeficitTrace.lean` | |
| Lemma 3.3 (cycle weight) | `Erdos1016/Cycles/Counting/LowDegreeTraceCycles.lean` | |
| Section 3.2, equation (3.2) | `Erdos1016/Probability/Moments/SeedPairCorrelation.lean` | |
| Proposition 3.4, Step 2 (links of two cycles) | `Erdos1016/Cycles/Geometry/RetainedExteriorLinks.lean`, `ActualCycleLinkBound.lean`; `Erdos1016/Probability/Avoidance/ExteriorCyclicCount.lean` | **Other method**: the components with a cycle are bounded by Lemma 2.4, under the hypothesis `q > 1/2 + eps`. The text uses `q >= 2/5` and the Cauchy-Schwarz inequality. The formal bound has `578 (L/D)^2` where the text has `289 (L/D)^2` |
| Proposition 3.4, Steps 3 and 4; Section 4 | `Erdos1016/Probability/Moments/SeedFamilyAvoidance.lean`, `InducedCycleAvoidance.lean`; `Erdos1016/Cycles/Selection/RetainedCycleSupply.lean`, `RetainedSizeBounds.lean` | No single formal statement is Proposition 3.4 |
| The maximal family of short cycles | `Erdos1016/Cycles/Selection/ShortRegionPacking.lean`, `ShortRegionObstructions.lean`, `RetainedHighGirth.lean` | |
| Section 5 (splitting and cleaning) | `Erdos1016/Graph/Cubicization/MarkedReduction.lean` | The formal splitting is an expansion at the incidences of a vertex |

The pancyclic paper: `E.mainTheorem` (both bounds), `E.Problem1016.upper_bound_integer` (the
construction), and `E.ShortProof.fewComponentForestEstimate` (the forest estimate for
`|E(W)| <= sqrt(r)`, which the formal proof of the lower bound uses). Commit `a5cb5fa`.

The maximum-cycles paper: see `Erdos1016/ExactMaximum/README.md`, section "The third proof".

## History

The sections below are from 12 November 2026, before the split. Their statement numbers are
those of the single paper of 42 pages (`research/single-paper-12-nov/`): there the forest
estimate is Theorem 3.1, the lemma on a marked set is Lemma 3.7, and the leading term is
Corollary 3.8.

## The pass over the presentation (12 November 2026)

KNT asked for checks of the presentation after the mathematics was settled. No statement and no
proof step changed, with one exception: the constant in the last proof is `A = 6 e^9` with
`mu > 2` (it was `6 e^124` with `mu > 30`, which the present proof does not need).

- Structure. Section 7.1 is now two subsections: forest proportions and pieces of large girth
  (7.1), and pieces with few boundary vertices at girth five (7.2), with an outline box for the
  three lemmas at girth five. The definitions at the start of Sections 3.1 and 7.1 and the
  constants after Lemma 7.6 are in notation boxes. The statement that Sections 7.3 to 7.5 use is
  Corollary 7.7 (Pieces); it was a sentence at the end of a paragraph. The constants
  `eps_0`, `K_0`, `kappa(h)` are defined in Section 6.2, where they are used.
- Exposition. An outline box before Lemma 5.3; one paragraph in Section 7.1 on the purpose of
  forest proportions; two sentences before Lemma 6.5; names for the eight statements that had
  none.
- Figures. Eight new figures: the links of two cycles (Proposition 3.5), the localisation step
  (Lemma 4.1), a free index (Lemma 5.3), the three gadgets (Lemma 5.9), a cycle that turns in a
  ring (Proposition 6.1), the two shapes (Lemma 6.5), the end piece in Case 1 (Theorem 6.6), and
  the tree through a rigid set (Lemma 7.5). Figure 3 shows the set `P` of the text (it showed a
  cycle `W`), and the figure of the chain names the region `A` (it had `C`). The figure of the
  pole with four ports moved to Section 6.3, where the cap is. No figure was removed.
- Sentences. "In Case 2" in the place of "In the case 2"; the first sentence of Section 4; one
  sentence in the proof of Lemma 5.3(b); the constant `5 * 2^t` in Step 1 of Proposition 3.5.
- Layout. Section 7 and the two outline boxes of Sections 6.4 and 7.2 start on a new page when
  too little room is left (`\needroom` in `exact-maximum.tex`; the shared style file is not
  changed). The statement boxes do not break across pages, so some pages end early.

## Research notes (written before the codification)

The four notes below are from 12 November 2026, before KNT said "Codify it". In them "the
manuscript" and `[M]` mean the draft of 42 pages. Its sources and its PDF are now in
`research/base-42-pages/`. The scripts `research/apply_*.py` apply to a copy of that folder: copy
`research/base-42-pages` to `<new>/exact-maximum` and `style` to `<new>/style`, and run the
scripts on `<new>/exact-maximum`. The sentences "the manuscript is not changed" describe the
state at the time of each note.

## Research note on Section 8 (12 November 2026)

[research/one-scale.pdf](research/one-scale.pdf) has two new proofs of Theorem 8.1. Each of them
uses one family of short cycles at one scale, and each removes Theorem 8.8 (raising the girth),
the nested deleted sets and the two girth scales. The first proof counts the blocks of a chain
that contain a short cycle. The second proof has a new lemma: at a fixed girth, a large piece
with a small boundary has a forest proportion of less than 3/5. Measured in copies of the paper,
Section 8 has 271 typeset lines now, 259 with the first proof and 289 with the second. The
manuscript is not changed; `research/apply_one_scale.py` and `research/apply_two_regions.py`
apply a proof to a copy, and `research/trial-one-scale.pdf` and `research/trial-fixed-girth.pdf`
are the two copies. The new proofs are on paper only: no formal proof, and no second reader.

## Second research note: no case of bounded girth (12 November 2026)

[research/girth-five.pdf](research/girth-five.pdf) answers the second research task. It has an
audit of Theorem 4.4 of the first note (the proof is correct), and a new theorem: at girth five,
a connected subcubic multigraph with at most `k` boundary vertices and at least `C_1 k^7`
vertices has a forest proportion of less than 3/5 for every even set of boundary vertices. The
reason is that a piece in which every join is a forest contains a capped ladder (Lemma 5.8), and
a ladder has cycles of length four. So Theorem 8.1 holds for girth five, a graph without a
cyclic cut of size at most four has girth at least five, and Section 7 (Theorem 7.1), Lemma 5.5
and Corollary 5.6 are not necessary. The main theorem then has four cases.

Measured in copies of the paper (`research/apply_girth_five.py <copy> lean` or `clean`): the
lean form has 1617 typeset lines and 42 pages, the clean form has 1643 lines and 43 pages (now
1624 lines and 42 pages). `research/trial-girth-five-lean.pdf` and
`research/trial-girth-five-clean.pdf` are the two copies. The manuscript is not changed. The new
proofs are on paper only; `checks/girth5/` has the computations on small graphs.

## Third research note: three cases (12 November 2026)

[research/fewer-cases.pdf](research/fewer-cases.pdf) answers the request to search for more
efficiencies. It has four reductions outside the last section, with complete proofs.

1. The gap theorem (Theorem 5.10) is a corollary of the proof of Proposition 5.3 and of
   Lemma 5.8: a bridgeless 2-pole is a capped ladder if and only if the graph outside a shortest
   path between its ports is a forest, and a pole with many paths in which this graph has a cycle
   has a short cycle there. Lemma 5.9 (a third port) and the induction are not necessary. The gap
   constant is then a very small number, and Section 6 has `eps_0` in the place of `1/1000`.
2. Theorem 6.8 is necessary only for a graph with a cycle of length four, because the last case
   in the form for girth five needs no hypothesis on cuts. One side of the cut is then the cycle,
   and Lemma 6.4 (gluing) and the steps for the second side are not necessary.
3. A loop gives a cyclic cut of size one. So the main theorem has three cases: a cyclic cut of
   size at most three; a cycle of length four; girth at least five.
4. The count with a marked set (the last case) also gives the bound `(1/2 + o(1)) 2^r` of
   Corollary 3.7, so the edge recursion is not necessary.

Measured in a copy (`research/apply_girth_five.py <copy> lean`, then
`research/apply_fewer_cases.py <copy>`): 41 pages, 1587 typeset lines, 39 numbered statements,
three cases (now 42 pages, 1624 lines, 40 statements, five cases).
`research/trial-fewer-cases.pdf` is this copy. With the argument `keepgap` the script applies
the reductions 2, 3 and 4 only (the gap theorem keeps its induction and the constant `1/16`):
42 pages, 1607 lines, 40 statements, three cases. The manuscript is not changed. The new proofs are
on paper only; `checks/gap_and_square_check.py` tests the statements without large constants on
small graphs (exit code 0). The note also lists eight attempts that failed.

## Fourth research note: an audit of Astra's notes, and a combined copy (12 November 2026)

KNT gave me notes of Astra with eight proposals for a shorter proof.
[research/astra-audit.pdf](research/astra-audit.pdf) has the audit (8 pages). I found no error in
the proposals. Three of them are the same as reductions of my notes (the marked set, the gap
theorem as a corollary, the recursion from `d` to `log d`). New, and now in a copy of the paper:

- a lemma on a shortest path between the ports of a pole, without a hypothesis on the number of
  paths; it gives the few-cycles theorem without ordinary layers and without a count of matchings;
- the rigidity lemma by a limit of states, with the gap constant at one place only;
- three full pairs at one port give a cyclic cut of size three, so the lemma on a full star is
  not necessary;
- the lemma on two links as an upper bound `W_2 <= 2 mu (e + N M)`;
- a shorter proof of nesting, and a shorter window step in the lemma on layers.

Sound but not in the copy, by the measured lines: caps for cuts of size two and three (11 lines
more) and connected blocks in the chain (1 line more). Both are options of the script.

`research/trial-combined.pdf` is the copy: 41 pages, 1577 typeset lines, 39 numbered statements,
three cases (the manuscript: 42 pages, 1624 lines, 40 statements, five cases). To build it, run on
a copy of `exact-maximum`, in this order: `research/apply_girth_five.py <copy> lean`,
`research/apply_fewer_cases.py <copy> keepgap`, `research/apply_combined.py <copy>`.
`checks/astra_audit_check.py` tests the new statements on small graphs (six tests, exit code 0).
At the time of the note the manuscript was not changed. Nothing of the four notes or of Astra's
notes has a formal proof. The copy `research/trial-combined.pdf` is the text that was codified;
the paper differs from it in Section 1.4, in one remark of Section 3, and by the pass over the
presentation.

In the text, the proof of Proposition 5.3 no longer adds a new vertex to the pole (11 November
2026, 21:50 UTC): Step 1 adds the shortest path `A` to each path. The statement is the same, and
the constant uses `Theta_{eps/2}(1)` in place of `Theta_{eps/2}(2)`.
