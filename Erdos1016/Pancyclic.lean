import Erdos1016.Main

/-!
# Entry module for the pancyclic problem (Erdős Problem #1016)

Text: "The minimum number of edges in a pancyclic graph" (`paper/minimal/pancyclic/`).

This module imports the formal proof of both bounds for the smallest excess `h(n)` of a
pancyclic graph on `n` vertices.

| Text | Declaration |
|---|---|
| The main theorem: `log₂ n + log* n - O(1) ≤ h(n) ≤ log₂ n + log* n + O(1)` | `Erdos1016.mainTheorem`, `Erdos1016.mainTheorem_integer_excess` |
| The construction for the upper bound | `Erdos1016.Problem1016.upper_bound_integer` |
| The forest estimate that the lower bound uses | `Erdos1016.ShortProof.fewComponentForestEstimate` |

`Erdos1016/README.md` has the folders that the proof uses. In addition to the folders of the
forest estimate these are mainly the modules of `Extremal/`.
-/
