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

The import closure has 264 modules of the library, and the proof uses 224 of them;
`Erdos1016/README.md` has the folders. In addition to the folders of the forest estimate these
are mainly the modules of `Extremal/`. The file `Erdos1016/Main.lean` also has the theorems on
the number of cycles that follow from the forest estimate, and two elementary theorems.
-/
