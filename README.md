# Erdős problem 1016 — Lean verification

[![Verify Lean theorem](https://github.com/JWKNT/erdos1016/actions/workflows/verify.yml/badge.svg)](https://github.com/JWKNT/erdos1016/actions/workflows/verify.yml)

This Lean formalization proves the shorter argument with a union of few witness cycles. The main theorem is unconditional:

```lean
Erdos1016.mainTheorem : Erdos1016.Problem1016.MainTheorem
```

It proves

$$h(n)=\log_2 n+\log_* n+O(1),$$

where `h(n)` is the minimum excess of edges over vertices in a simple graph on `n` vertices containing every cycle length from 3 through `n`. The bounds hold uniformly for every `n ≥ 3`. Here `log* n` is the least `k` with `n ≤ T(k)`, where `T(0) = 1` and `T(k + 1) = 2 ^ T(k)`.

The public declarations are in [Main.lean](Erdos1016/Main.lean). `Erdos1016.mainTheorem_integer_excess` gives the equivalent statement using integer subtraction for the excess.

Read the [paper (PDF)](paper/erdos1016.pdf) or its [LaTeX source](paper/erdos1016.tex). The [`old/`](old/ARCHIVE.md) directory preserves the previous formalization, published paper, and earlier working draft. The active Lean build and current CI certificate exclude this archived material. The website has a separate archive.

## Cycle-count theorems

The same forest estimate bounds the number of cycles of a graph. Two further endpoints are unconditional:

```lean
Erdos1016.cycleCountTheorem : Erdos1016.CycleCount.CycleCountStatement
Erdos1016.cycleCountAsymptotic : Erdos1016.CycleCount.AsymptoticCycleCount
```

The first endpoint proves that a simple graph with large cyclomatic number `r` has at most

$$\Bigl(\tfrac12+\frac{21}{\log_2\log_2\log_2 r}\Bigr)2^{r}$$

cycles. The second endpoint proves that the largest number of cycles at cyclomatic number `r`, divided by `2^r`, tends to `1/2`. This is the asymptotic form of a question of Entringer and Slater.

Cycles are Mathlib `SimpleGraph.Walk.IsCycle` objects. The count uses their edge sets, so each cycle is counted once. The cyclomatic number is `edges - vertices + components`. The statements use graphs on `Fin n`. `Erdos1016.cycleCountTheorem_general` gives the same bound on every finite vertex type.

The bound is asymptotic and its threshold is not explicit. The bound is below the elementary bound `2^r` only if `log₂ log₂ log₂ r > 42`. See the [proof map](docs/proof-map.md#cycle-count-theorems) for the modules.

A draft manuscript gives the proof: [PDF](paper/cycle-count/sharp-cycle-paper.pdf) and [LaTeX source](paper/cycle-count/sharp-cycle-paper.tex). The folder [`paper/cycle-count`](paper/cycle-count/README.md) also contains tests on small graphs, earlier drafts, and research notes.

## The sharp cycle bound: a written proof with formalized steps

The same manuscript states a stronger result. A graph with cyclomatic number `r` has at most

$$2^{r-1}+K\,r\,2^{r/2}$$

cycles, for an absolute constant `K`. Examples of Horak and Kim show that the order of the second term is correct. This result is **not formalized**. Its proof is a written proof that two language models checked. No referee has read it. A part of the proof is in research reports in [`paper/cycle-count/research/2026-11-10`](paper/cycle-count/research/2026-11-10).

The modules in `Erdos1016/PolynomialBound/` formalize some steps of the proof: the parallel-link lemma, the link bound without a forest excess, the two-link moment inequality, the order of nested separators with its blocks, and the product lemma for two regions. They contain no endpoint theorem. See the [proof map](docs/proof-map.md#steps-towards-the-sharp-cycle-bound) for the modules, and the manuscript for the list of the steps that are not formalized.

## Exact-counting theorems

Two elementary theorems on paths and cycles are also unconditional. Their proofs do not use the forest estimate.

```lean
Erdos1016.twoTerminalTheorem : Erdos1016.ExactCounting.TwoTerminalStatement
Erdos1016.noWasteTheorem : Erdos1016.ExactCounting.NoWasteStatement
```

The first endpoint concerns a connected simple graph with cyclomatic number `r` and two of its vertices. The graph has at most `2^r` paths between them. If it has exactly `2^r`, then each of these paths has at least `r` edges. The graph without the edges of such a path is acyclic.

The second endpoint concerns a subgraph `W` of a connected simple graph `G`. Suppose that every even edge set of `G` agrees outside `W` with some cycle of `G`. Then the graph without the edges of `W` has no two edge-disjoint cycles. The cyclomatic numbers satisfy `β(G) ≤ β(W) + |V(W)| + 3`.

The second proof contains the lemma of Erdős and Pósa in the language of even edge sets. If any two nonempty even edge sets of a multigraph share an edge, then the multigraph has at most `n + 3` edges on `n` vertices. See the [proof map](docs/proof-map.md#exact-counting-theorems) for the modules.

## Proof structure

1. Extract a union of witness cycles using least missing lengths, with simultaneous edge, rank, and component budgets.
2. Expand the graph. Prune unmarked leaves. Suppress unmarked degree-two vertices. Preserve the cycle space and control the marked region during these operations.
3. Use the small-cut probability bound to delete a small packing of short cyclic regions.
4. Use the nonbacktracking trace and degree deficit of the retained graph to obtain enough weighted cycles.
5. Bound their actual pair correlations by the marked components and exterior links. Apply the weighted second moment to prove the forest estimate.
6. Derive the linear exponential recurrence. Iterate it to obtain the log-star lower bound. Combine this result with the reused constructive upper bound.

The complete forest estimate is `ShortProof.fewComponentForestEstimate`. The earlier conditional deduction remains a reusable lemma. The declaration `mainTheorem` supplies its proved premise. See the [proof map](docs/proof-map.md) for the corresponding modules.

## Verification

The project is pinned to Lean 4.19.0 and the Mathlib revision in `lake-manifest.json`. Mathlib is the only direct package dependency. The other locked packages are its transitive dependencies. Keep the committed lockfile unchanged.

Install [elan](https://github.com/leanprover/elan), Git, and Python 3. Then run:

```sh
git clone https://github.com/JWKNT/erdos1016.git
cd erdos1016
elan toolchain install leanprover/lean4:v4.19.0
lake exe cache get
python3 -m unittest discover -s scripts -p 'test_*.py'
python3 scripts/verify.py --fresh --jobs 2
```

The verifier rebuilds every active module with bounded parallelism. It checks the unconditional endpoint and expanded mathematical statements. It audits theorem axioms and records source hashes with the evidence. A successful run permits only `propext`, `Classical.choice`, and `Quot.sound`. The verifier rejects admissions and extra axioms. See [verification.md](docs/verification.md) for details.

The active library contains only the import closure of `Erdos1016.lean`. The verifier writes local records under `.verification/`. [GitHub Actions](https://github.com/JWKNT/erdos1016/actions/workflows/verify.yml) repeats fresh verification for each pushed revision. It uploads the report and logs. A passing run certifies its recorded commit. Before you share a verification link, inspect that commit.

No new license is granted for the project sources. Dependencies retain their upstream licenses; see [NOTICE.md](NOTICE.md).
