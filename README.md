# Erdős problem 1016 — Lean verification

[![Verify Lean theorem](https://github.com/JWKNT/erdos1016/actions/workflows/verify.yml/badge.svg)](https://github.com/JWKNT/erdos1016/actions/workflows/verify.yml)

A Lean formalization of the shorter proof based on a union of few witness cycles. The main theorem is unconditional:

```lean
Erdos1016.mainTheorem : Erdos1016.Problem1016.MainTheorem
```

It proves

$$h(n)=\log_2 n+\log_* n+O(1),$$

where `h(n)` is the minimum excess of edges over vertices in a simple graph on `n` vertices containing every cycle length from 3 through `n`. The bounds hold uniformly for every `n ≥ 3`. Here `log* n` is the least `k` with `n ≤ T(k)`, where `T(0) = 1` and `T(k + 1) = 2 ^ T(k)`.

The public declarations are in [Main.lean](Erdos1016/Main.lean). `Erdos1016.mainTheorem_integer_excess` gives the equivalent statement using integer subtraction for the excess.

Read the [paper (PDF)](paper/erdos1016.pdf) or its [LaTeX source](paper/erdos1016.tex). The previous formalization, published paper, and an earlier working draft are preserved under [`old/`](old/ARCHIVE.md). The archived material is excluded from the active Lean build and current CI certificate. The website is archived separately.

## Proof structure

1. Extract a union of witness cycles using least missing lengths, with simultaneous edge, rank, and component budgets.
2. Expand, prune, and suppress the graph while preserving its cycle space and controlling the marked region.
3. Apply the small-cut probability bound to delete a small packing of short cyclic regions.
4. Use the nonbacktracking trace and degree deficit of the retained graph to obtain enough weighted cycles.
5. Bound their actual pair correlations by the marked components and exterior links, and apply the weighted second moment to prove the forest estimate.
6. Deduce the linear exponential recurrence, iterate to the log-star lower bound, and combine it with the reused constructive upper bound.

The complete forest estimate is `ShortProof.fewComponentForestEstimate`. The earlier conditional deduction remains a reusable lemma; `mainTheorem` supplies its now-proved premise. See the [proof map](docs/proof-map.md) for the corresponding modules.

## Verification

The project is pinned to Lean 4.19.0 and the Mathlib revision in `lake-manifest.json`. Mathlib is the only direct package dependency; the other locked packages are its transitive dependencies. Keep the committed lockfile unchanged.

Install [elan](https://github.com/leanprover/elan), Git, and Python 3, then run:

```sh
git clone https://github.com/JWKNT/erdos1016.git
cd erdos1016
elan toolchain install leanprover/lean4:v4.19.0
lake exe cache get
python3 -m unittest discover -s scripts -p 'test_*.py'
python3 scripts/verify.py --fresh --jobs 2
```

The verifier rebuilds every active module with bounded parallelism, checks the unconditional endpoint and expanded mathematical statements, audits theorem axioms, and binds its evidence to source hashes. A successful run permits only `propext`, `Classical.choice`, and `Quot.sound`; it rejects admissions and extra axioms. Details are in [verification.md](docs/verification.md).

The active library contains only the import closure of `Erdos1016.lean`. Local verification records are written under `.verification/`. [GitHub Actions](https://github.com/JWKNT/erdos1016/actions/workflows/verify.yml) repeats the fresh verification for each pushed revision and uploads the report and logs. A passing run certifies its recorded commit; inspect that commit when sharing a verification link.

No new license is granted for the project sources. Dependencies retain their upstream licenses; see [NOTICE.md](NOTICE.md).
