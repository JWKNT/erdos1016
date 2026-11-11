# A census of cycles in cubic graphs up to 22 vertices (and girth five at 24)

Date: 10 November 2026. Author: Fable 5.2. Reader: Astra (Codex) and KNT.

Status: **[COMPUTED]** exact integer counts by `fable_cycle_census.c`, run through `fable_cycle_census_run.py`. Results: `fable-cycle-census-results.json`. Two small cases are also **[CHECKED]** by independent Python code and by hand (Section 3). Nothing here is a proof about large ranks.

Novelty: **the table is not new.** Markström's paper (Section 5), which I have now read, lists the same values of `psi(r)` for all ranks up to 12, and it credits Guichard (1996) with the failure of the girth conjecture. My census is an independent confirmation. I do not know whether the result of Section 3 is known: Markström's paper does not discuss it, and I could not read Guichard's paper.

## 1. What was computed

For every connected simple cubic graph `G` on `n` vertices, `4 <= n <= 22`, the program enumerates the `2^r - 1` nonzero even subgraphs (`r = n/2 + 1`) with a Gray code and tests each for connectedness. In a cubic graph a connected nonzero even subgraph is a cycle. This gives the number `c(G)` of cycles and the number `c_e(G)` of cycles through each edge. The graphs come from `geng -c -d3 -D3 n` (nauty 2.8.9, the binary that Astra built).

The numbers of graphs agree with the known counts: 1, 2, 5, 19, 85, 509, 4060, 41301, 510489, 7319447.

Why cubic graphs are enough. Entringer and Slater proved that a cubic graph attains `psi(r)` for `r >= 3`. Here is the short argument, so that the table does not depend on the wording of their theorem. A graph of rank `r` has the same cycles as its kernel. Splitting a vertex of degree at least four does not lose a cycle. So `psi(r)` is the largest number of cycles of a connected cubic multigraph on `2r - 2` vertices. A vertex with a loop has one further edge, which is a bridge, so such a graph has at most `1 + psi(r-1)` cycles. Let `u, v` be joined by two parallel edges, with further neighbours `x` and `y`. If `x = y`, the graph has at most `3 + psi(r-2)` cycles. Otherwise put `G'' = G - u - v + xy`, a cubic multigraph of rank `r - 1`, and let `P` be the number of `x`-`y` paths in `G - u - v`. Then `c(G) = 1 + 2P + c(G - u - v) = 1 + P + c(G'')`, so `c(G) <= 1 + 2^(r-2) + psi(r-1)`. The values in the table for simple cubic graphs exceed `1 + 2^(r-2) + psi(r-1)` for `4 <= r <= 12`. By induction on `r`, multigraphs with loops or parallel edges do not reach the maximum, and the table gives `psi(r)`.

## 2. Table

`psi(r)` is the largest number of cycles at rank `r`. `X_r = psi(r) - 2^(r-1)`. "min edge" is the largest value of `min_e c_e(G)` over the cubic graphs of that order, and `g = (min edge) - 2^(r-2)`. The recurrence of `fable-notes.md`, Section 2, says `X_r - X_(r-1) <= g`.

| `r` | `n` | graphs | `psi(r)` | `psi(r)/2^r` | `X_r` | `X_r - X_(r-1)` | `g` | girth of the extremal graphs | largest girth at this order |
|---|---|---|---|---|---|---|---|---|---|
| 3 | 4 | 1 | 7 | 0.875 | 3 | | 2 | 3 | 3 |
| 4 | 6 | 2 | 15 | 0.938 | 7 | 4 | 4 | 4 | 4 |
| 5 | 8 | 5 | 29 | 0.906 | 13 | 6 | 6 | 4 | 4 |
| 6 | 10 | 19 | 57 | 0.891 | 25 | 12 | 12 | 5 | 5 |
| 7 | 12 | 85 | 109 | 0.852 | 45 | 20 | 21 | 5, 5 | 5 |
| 8 | 14 | 509 | 213 | 0.832 | 85 | 40 | 40 | 6 | 6 |
| 9 | 16 | 4060 | 401 | 0.783 | 145 | 60 | 66 | **5** | 6 |
| 10 | 18 | 41301 | 783 | 0.765 | 271 | 126 | 128 | 6 | 6 |
| 11 | 20 | 510489 | 1484 | 0.725 | 460 | 189 | 204 | 6 and 5 | 6 |
| 12 | 22 | 7319447 | 2876 | 0.702 | 828 | 368 | 368 | 6 | 6 |

The rows for `r <= 8` agree with Table 1 of Entringer and Slater.

Observations.

- **The recurrence is almost exact here.** `X_r - X_(r-1)` equals `g` for `r = 4, 5, 6, 8, 12` and is within 10 percent for the other ranks. So the worst minimum edge excess is the right quantity at these ranks.
- **The ratio `psi(r)/2^r` decreases slowly**, from 0.94 to 0.70. The asymptotic value is `1/2`. The excess `X_r` grows by a factor between 1.7 and 2.4 per rank (1.80 at the last step). These ranks do not show the exponent.
- **Girth.** At 16 vertices the graph with the most cycles (401) has girth 5. The only cubic graph of girth 6 on 16 vertices has 400 cycles. At 20 vertices one extremal graph has girth 6 and one has girth 5. So Conjecture 4 of Entringer and Slater ("the cubic graphs of given order with the maximum number of cycles are precisely those with maximum girth") fails at order 16. This is known (Section 5).
- **Edge-half conjecture** (Conjecture 2 of Entringer and Slater: some edge lies on at most half of the cycles). It holds for every connected cubic graph up to 22 vertices except `K4` and `K33`. The smallest value of `c(G) - 2 min_e c_e(G)` is 0, 1, 3, 5, 8, 11, 11, 14 for `n = 8, ..., 22`. So the conjecture has little room.

## 3. The vertex form of the edge-half conjecture is false

Conjecture 3 of Entringer and Slater: in every graph other than `K4` and `K33` with minimum degree at least three, every vertex `v` has an incident edge that lies on at most half of the cycles.

**Counterexample (10 vertices).** [COMPUTED; CHECKED by separate Python code; CHECKED by hand below] Take a vertex `z` and three triangles `a_i b_i c_i`, `i = 1, 2, 3`. Add the edges `z a_i` and the edges `c_1 b_2`, `c_2 b_3`, `c_3 b_1`. This is `K4` with three of its vertices replaced by triangles. It is cubic and 3-edge-connected. It has 47 cycles, and each of the three edges at `z` lies on 24 of them. Since `24 > 47/2`, no edge at `z` lies on at most half of the cycles.

*Count by hand.* The three triangles are cycles. A cycle that avoids `z` and is not a triangle goes once around the ring; it passes each triangle from `b_i` to `c_i` directly or through `a_i`: 8 cycles. A cycle through `z` uses two spokes `z a_i`, `z a_j` and a path from `a_i` to `a_j` outside `z`. The short way round has `2 * 2 = 4` such paths and the long way round has `2 * 2 * 2 = 8`. So each pair gives 12 cycles and there are 36 cycles through `z`. The total is `3 + 8 + 36 = 47`. Each spoke is in two of the three pairs: 24 cycles.

In graph6 form the graph is `ICOedPKL?`. The census finds the following numbers of connected cubic graphs with such a vertex (the two exceptions `K4` and `K33` are included at orders 4 and 6).

| `n` | 4 | 6 | 8 | 10 | 12 | 14 | 16 | 18 | 20 | 22 |
|---|---|---|---|---|---|---|---|---|---|---|
| graphs with a vertex whose three edges are each on more than half of the cycles | 1 | 1 | 0 | 1 | 1 | 14 | 160 | 2382 | 42286 | 838696 |

At 22 vertices this is 11.5 percent of all connected cubic graphs. So the failure is not a small-case accident.

At a vertex of degree `d >= 4` the statement of Conjecture 3 holds for a trivial reason: the numbers `c_e` at the vertex sum to twice the number of cycles through it. So the conjecture can only fail at vertices of degree three.

Consequence for our work: none for the upper bounds. The recurrence needs one good edge in the whole graph (Conjecture 2), not one at every vertex.

## 3a. Symmetric graphs beyond 22 vertices

For some cubic graphs with many symmetries I counted the cycles directly (function `cycles_of` in `fable_check_blocking.py`). The edge-half conjecture holds in each case, with little room. In the edge-transitive cases every edge lies on the same number of cycles, so the conjecture is the statement that the mean cycle length is at most `3n/4`.

| graph | `n` | girth | cycles | cycles through an edge (min, max) | mean cycle length | `3n/4` |
|---|---|---|---|---|---|---|
| Petersen | 10 | 5 | 57 | 28, 28 | 7.37 | 7.5 |
| Heawood | 14 | 6 | 213 | 104, 104 | 10.25 | 10.5 |
| Möbius-Kantor | 16 | 6 | 400 | 194, 194 | 11.64 | 12 |
| Pappus | 18 | 6 | 783 | 384, 384 | 13.24 | 13.5 |
| Desargues | 20 | 6 | 1456 | 712, 712 | 14.67 | 15 |
| McGee | 24 | 7 | 5608 | 2732, 2758 | 17.66 | 18 |
| Nauru | 24 | 6 | 5442 | 2662, 2662 | 17.61 | 18 |
| F26A | 26 | 6 | 10429 | 5118, 5118 | 19.14 | 19.5 |
| Tutte-Coxeter | 30 | 8 | 41400 | 20352, 20352 | 22.12 | 22.5 |

The counts 5608 and 41400 agree with the values that Entringer and Slater quote from Barefoot for the McGee graph and the Tutte-Coxeter graph.

## 3b. Order 24, girth at least five

[COMPUTED] Results: `fable-cycle-census-girth5-order24.json` (`geng -c -d3 -D3 -tf 24`, 1,620,479 graphs, which is the known number of connected cubic graphs of girth at least five on 24 vertices; 15 minutes on eleven cores).

| girth | graphs | largest number of cycles |
|---|---|---|
| 5 | 1,612,905 | 5511 |
| 6 | 7,573 | 5581 |
| 7 | 1 | 5608 |

- The McGee graph is the only graph in this class with 5608 cycles. Markström's lower bound `psi(13) >= 5608` came from the graphs of girth at least six; this run extends the search to girth five and finds nothing larger. The graphs with a triangle or a four-cycle were not searched, so `psi(13) = 5608` is not proved. At every order from 10 to 22 the maximum over the graphs with a triangle or a four-cycle is smaller than the maximum over the others.
- The largest minimum edge count in this class is 2732, at the McGee graph. If `psi(13) = 5608`, then `X_13 = 1512` and `X_13 - X_12 = 684 = 2732 - 2^11`: the recurrence would be exact again.
- No graph in this class violates the edge-half conjecture. 18,420 of them violate its vertex form.

## 4. Reproduce

    cc -O2 -o fable_cycle_census fable_cycle_census.c
    python3 fable_cycle_census_run.py --geng /tmp/nauty2_8_9/geng --census ./fable_cycle_census \
            --orders 4 6 8 10 12 14 16 18 20 22 --jobs 10 --out fable-cycle-census-results.json

Orders up to 20 take about half a minute on ten cores. Order 22 took eleven minutes on a loaded machine. I ran the whole census twice (the second time with the per-vertex test added). The two runs agree in every field.

Cross-check: for each extremal graph of orders 16 to 22, a separate Python program (depth-first search, its own graph6 parser) finds the same number of cycles and the same smallest and largest edge counts. Astra's independent program (`second-order-cubic-catalog-results.json`) gives the same maximum numbers of cycles and the same largest minimum edge counts for every order through 20.

## 5. Literature

- R. C. Entringer and P. J. Slater, *On the maximum number of cycles in a graph*, Ars Combin. 11 (1981) 289-294. I read the scan linked from OEIS A006188. It gives `psi(3..8)` and Conjectures 1 to 4. OEIS A006188 lists the six terms 7, 15, 29, 57, 109, 213 and no more. A search of the OEIS for `401, 783, 1484` returns no sequence. So Markström's values, which this census confirms, would extend A006188 by four terms. I have not submitted anything.
- K. Markström, *Extremal graphs for some problems on cycles in graphs* (Congr. Numer. 171, 2004; I read the version of August 2005 from the author's page, with KNT's permission to download it). **Read.** Its Table 1 gives `psi(k)` for `3 <= k <= 12` as 7, 15, 29, 57, 109, 213, 401, 783, 1484, 2876, with the girths of the extremal graphs 3, 4, 4, 5, 5, 6, 5, 6, "5, 6", 6. Every entry agrees with the table in Section 2. (The text of the paper says that the extremal graphs were found for `k <= 11`, but the table and the caption of its Figure 4 give the value at `k = 12` as exact, from a search without a girth restriction.) For `13 <= k <= 22` it gives lower bounds from searches restricted to high girth: 5608, 10872, 21192, 41400, 80211, 157134, 306373, 600054, 1182592, 2324532. It states that the girth conjecture of Entringer and Slater "was disproved in [Gui96]". It conjectures that the generalised Petersen graphs come close to the maximum. It does not mention the edge-half conjecture or its vertex form.
- D. R. Guichard, *The maximum number of cycles in graphs*, Congr. Numer. 121 (1996) 211-215. **Not read.** Markström credits it with the disproof of the girth conjecture. An abstract found by search says that it reports partial results on the edge-half conjecture. I do not know whether it treats the vertex form.
- Correction: an earlier version of this note said, from a search summary, that Markström shows that a counterexample to the edge-half conjecture has at least 30 vertices. That statement is not in the paper that I read. I withdraw it.

So: the values 401, 783, 1484 and 2876 and the girth observation are confirmations of known results, obtained independently with a different program. The counterexample of Section 3 is not in Markström's paper. It may be in Guichard's paper. A person should check that paper before any claim is made.

The extremal graph at 22 vertices is unique. Its graph6 string is `U????A?O@?A?B?o_T??o_Ca@CG?HG?B_?BA?GP??`. It has girth 6, and its edges lie on between 1392 and 1416 cycles.
