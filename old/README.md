# Erdős problem 1016

[![Verify Lean proof](https://github.com/JWKNT/erdos1016/actions/workflows/verify.yml/badge.svg)](https://github.com/JWKNT/erdos1016/actions/workflows/verify.yml)

A Lean formalization of the minimum number of edges in a pancyclic simple graph. A graph on `n` vertices is **pancyclic** when it contains a cycle of every length from `3` through `n`.

Read the [paper (PDF)](paper/erdos1016.pdf) or its [LaTeX source](paper/erdos1016.tex).

Let `m(n)` be the minimum number of edges in such a graph and let `h(n) = m(n) − n`. The result is

$$h(n)=\log_2 n+\log^* n+O(1).$$

Precisely, there are real constants `Aminus` and `Aplus`, independent of `n`, such that for every integer `n ≥ 3`,

$$\log_2 n+\log^* n-A_{\mathrm{minus}}\le h(n)\le\log_2 n+\log^* n+A_{\mathrm{plus}}.$$

Here `log* n` is the least `k` with `n ≤ T(k)`, where `T(0) = 1` and `T(k + 1) = 2 ^ T(k)`.

The public declarations in [Main.lean](Erdos1016/Main.lean) are:

- `Erdos1016.mainTheorem`: the minimum of the natural-number excesses `|E| − n`.
- `Erdos1016.mainTheorem_integer_excess`: the equivalent minimum edge count minus `n`, computed in the integers.

Both declarations have no unproved mathematical hypotheses. The definitions and their equivalence are in [Statement.lean](Erdos1016/Extremal/Statement.lean) and [MinimumEdgesStatement.lean](Erdos1016/Extremal/MinimumEdgesStatement.lean).

## Verify locally

Install [elan](https://github.com/leanprover/elan), Git, and Python 3. The repository selects Lean **4.19.0** through `lean-toolchain`.

```sh
git clone https://github.com/JWKNT/erdos1016.git
cd erdos1016
elan toolchain install leanprover/lean4:v4.19.0
lake exe cache get
python3 -m unittest discover -s scripts -p 'test_*.py'
python3 scripts/verify.py --fresh --jobs 2
```

Keep the committed `lake-manifest.json`; do not run `lake update`. The cache command downloads the pinned dependencies and their compiled artifacts. Verification then rebuilds every project module from source with at most two concurrent builds, checks the expanded theorem statements and axiom dependencies, and writes `.verification/verification.json` and logs. See [the verification guide](docs/verification.md) for the checks and how to inspect CI evidence.

## Source guide

| Directory | Contents |
| --- | --- |
| [Graph](Erdos1016/Graph), [CycleSpace](Erdos1016/CycleSpace), [Boundary](Erdos1016/Boundary) | Graph models, parity and rank, boundary laws. |
| [Nonbacktracking](Erdos1016/Nonbacktracking) | Walks, entropy, spectrum, girth, and trace estimates. |
| [Cycles](Erdos1016/Cycles), [Probability](Erdos1016/Probability) | Cycle counting, filtering and selection; conditional laws, moments, and avoidance. |
| [Expansion](Erdos1016/Expansion), [Decomposition](Erdos1016/Decomposition), [Cleanup](Erdos1016/Cleanup) | Expanding regions, cores, graph cleanup, and descent. |
| [Extremal](Erdos1016/Extremal) | The statement, upper-bound construction, capacities, and log-star recurrence. |

The lower-bound assembly passes through [uniform core decay](Erdos1016/Probability/Avoidance/UniformCoreDecay.lean) and its [extremal reduction](Erdos1016/Extremal/Recurrence/UniformDecayReduction.lean). The upper bound is exposed in [UpperBound.lean](Erdos1016/Extremal/UpperBound.lean).

This repository contains the manuscript and the Lean verification source and tools. Lean file paths are organized by mathematical topic. Some proof comments refer to the manuscript's numbered sections.

No new license is granted for the project sources. Dependencies retain their upstream licenses; see [NOTICE.md](NOTICE.md).
