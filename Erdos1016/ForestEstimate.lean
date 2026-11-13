import Erdos1016.Probability.Avoidance.LogSquaredMarkedForest

/-!
# Entry module for the forest estimate

Text: "The forest proportion of a random even subgraph" (`paper/minimal/forest/`).

This module imports the formal proof of the forest estimate and nothing else.
`Erdos1016/README.md` has the folders that the proof uses.

| Text | Declaration |
|---|---|
| Theorem 1.1: `q(Γ,P) ≤ 1/2 + 20 / log log log r` for a connected cubic multigraph `Γ` of large rank `r` and a set `P` of at most `3 log r` vertices with `Γ[P]` connected | `Erdos1016.ShortProof.eventually_marked_forest_bound_logSquared` |
| Corollary 1.2: the same bound for a union of cycles in a simple graph | `Erdos1016.ShortProof.fewComponentForestEstimate_logSquared` |

`paper/minimal/README.md` has the table for the lemmas of the text.
-/
