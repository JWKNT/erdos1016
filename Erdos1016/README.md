# The Lean library `Erdos1016`

The library has the formal proofs for three texts of `paper/minimal/`. Each text has an entry
module. It imports the proof of the theorems of the text, and its header has a table of the
statements.

| Text | Entry module | Endpoint theorems | Modules imported / used |
|---|---|---|---|
| The forest proportion of a random even subgraph (`paper/minimal/forest/`) | `Erdos1016/ForestEstimate.lean` | `Erdos1016.ShortProof.eventually_marked_forest_bound_logSquared`, `Erdos1016.ShortProof.fewComponentForestEstimate_logSquared` | 246 / 190 |
| The minimum number of edges in a pancyclic graph (`paper/minimal/pancyclic/`) | `Erdos1016/Pancyclic.lean` | `Erdos1016.mainTheorem` | 264 / 224 |
| The maximum number of cycles in a graph of large rank (`paper/minimal/exact-maximum/`) | `Erdos1016/MaximumCycles.lean` | `Erdos1016.ExactMaximum.exactMaximum_threeCases`, `Erdos1016.ExactMaximum.maxCycles_formula_threeCases`, `Erdos1016.cycleCountAsymptotic` | 662 / 529 |

"Imported" is the number of modules of this library in the import closure of the entry module.
"Used" is the number of modules with a declaration that the endpoint theorems use (see below).
The two numbers differ because a file is imported as a whole. The third entry module does not
import `ExactMaximum/Main.lean` and `ExactMaximum/MainCaps.lean` (the proofs along five cases).
It does import files of Astra with other proofs of the theorem, because the parts that the
proof takes are in these files.

The root file `Erdos1016.lean` imports the three entry modules, then the other proofs of the
third theorem, and then the other modules, so that all 685 other modules are in its import closure.

## Which folder is used by which theorem

The table counts modules. A module is used by a theorem if the type or the proof term of the
theorem uses a declaration of the module, directly or through other declarations.
`audits/UsageMap.lean` computes the table from the compiled library:

```sh
lake env lean audits/UsageMap.lean
```

The columns:

- `F`: the forest estimate (the two endpoint theorems of the first text);
- `P`: the pancyclic theorem (`mainTheorem`);
- `T`: the maximum number of cycles along the three cases of the text (the three endpoint
  theorems of the third text);
- `M`: the same theorem along the five cases of the first text (`ExactMaximum.exactMaximum`);
- `C`: the same with caps (`ExactMaximum.exactMaximum_caps`).

State of 12 November 2026:

| Folder | Modules | F | P | T | M | C |
|---|---|---|---|---|---|---|
| `*.lean` (the files of this folder) | 4 | 0 | 1 | 1 | 1 | 1 |
| `Boundary/` | 5 | 3 | 3 | 3 | 3 | 3 |
| `Cleanup/` | 30 | 30 | 30 | 30 | 30 | 30 |
| `CycleCount/` | 9 | 0 | 0 | 8 | 8 | 8 |
| `CycleSpace/` | 17 | 11 | 12 | 12 | 12 | 12 |
| `Cycles/` | 44 | 40 | 42 | 42 | 42 | 42 |
| `Decomposition/` | 4 | 3 | 3 | 3 | 3 | 3 |
| `ExactCounting/` | 8 | 0 | 0 | 0 | 0 | 0 |
| `ExactMaximum/*.lean` | 70 | 0 | 0 | 56 | 63 | 63 |
| `ExactMaximum/GirthFive/` | 11 | 0 | 0 | 11 | 0 | 0 |
| `ExactMaximumSupport/*.lean` | 184 | 0 | 0 | 148 | 173 | 172 |
| `ExactMaximumSupport/CubicReduction/` | 7 | 0 | 0 | 7 | 7 | 7 |
| `ExactMaximumSupport/LargeGirth/` | 76 | 0 | 0 | 50 | 76 | 50 |
| `ExactMaximumSupport/Shortening/` | 53 | 0 | 0 | 30 | 0 | 17 |
| `Extremal/` | 36 | 4 | 27 | 11 | 11 | 11 |
| `Graph/` | 55 | 48 | 54 | 52 | 52 | 52 |
| `Linear/` | 1 | 1 | 1 | 1 | 1 | 1 |
| `Nonbacktracking/` | 29 | 28 | 28 | 28 | 28 | 28 |
| `PolynomialBound/` | 10 | 0 | 0 | 6 | 6 | 6 |
| `Probability/` | 32 | 22 | 23 | 30 | 30 | 30 |
| **all** | 685 | 190 | 224 | 529 | 546 | 536 |

How to read the table:

- The forest estimate uses 190 modules, in the folders `Cleanup/`, `Cycles/`, `CycleSpace/`,
  `Graph/`, `Nonbacktracking/`, `Probability/` and four smaller ones. The pancyclic theorem
  uses these and `Extremal/`.
- The theorem on the maximum number of cycles uses the forest estimate and the folders
  `CycleCount/`, `ExactMaximum/`, `ExactMaximumSupport/` and `PolynomialBound/`.
- `ExactMaximum/GirthFive/` (Theorem 7.1 of the third text at girth five) is used by the
  proof along the text only. That proof does not use 26 modules of
  `ExactMaximumSupport/LargeGirth/` (parts of the earlier proof for large girth) and 14
  modules of `ExactMaximum/` (the case of bounded girth, among others; the README of that
  folder has the list).
- `ExactCounting/` has two theorems of its own (`Erdos1016.twoTerminalTheorem`,
  `Erdos1016.noWasteTheorem`); none of the five groups uses it.
- A module that no column uses is a step that is proved and not used by an endpoint theorem,
  or a part of another proof of the third theorem (the files `*ExactMaximum.lean` of
  `ExactMaximumSupport/Shortening/`).

## The folders

| Folder | Content |
|---|---|
| `Graph/`, `CycleSpace/`, `Linear/` | Graphs and multigraphs with labelled edges, the cycle space over `F₂`, boundaries, cuts |
| `Cycles/`, `Nonbacktracking/` | Cycles and their geometry, walks without backtracking, the trace bound |
| `Probability/`, `Cleanup/`, `Decomposition/`, `Boundary/` | Random even subgraphs, second moments, the forest estimate and its localised forms |
| `Extremal/` | Pancyclic graphs: the construction and the lower bound |
| `CycleCount/` | The number of cycles of a graph, `maxCycles`, the leading term |
| `ExactCounting/` | Two elementary theorems on paths and cycles |
| `PolynomialBound/` | Separators, two-link moments, the product of two regions |
| `ExactMaximum/` (Fable 5.2) | The exact maximum: statements, networks, poles, the cases, the lower bound, the main theorems. Its README has a table file by file |
| `ExactMaximum/GirthFive/` (Fable 5.2) | Theorem 7.1 of the third text at girth five. Its README has the mathematics |
| `ExactMaximumSupport/` (Astra) | The proofs of the statements of `ExactMaximum/`: few cycles, the gap theorem, cuts of size four, large girth, and the shorter proofs in `Shortening/` |
