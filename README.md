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
