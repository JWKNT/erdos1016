# Proof map

The public endpoint is `Erdos1016.mainTheorem : Problem1016.MainTheorem`. It has no mathematical premise. `mainTheorem_integer_excess` checks the equivalent integer-excess formulation.

## Witness extraction and recurrence

- `Extremal/Witness/LeastMissing` constructs least-missing-length cycles and stops at the first rank crossing. If the rank jumps, skipped ranks receive no charge. The jump creates no extra selected cycles.
- `Graph/ConnectedCover` counts components on the witness's support vertices. It excludes isolated host vertices.
- `Extremal/Witness/WeightedExtraction` and `CapacityBudget` prove simultaneous edge, rank, component, and tail-weighted budgets for the same extracted union.
- `Extremal/Capacity/ActualRankTail` defines the tail supremum using each graph's actual cycle rank. `Graph/ConnectedCoverage` connects components by bridges. This preserves rank and covered lengths.
- `Graph/CycleRestrictionForest` and `Extremal/Capacity/WitnessOutsideBound` prove the outside forest requirement, uniform projection fibers, and resulting length-count inequality.
- `Extremal/Recurrence/WitnessReduction` checks the forest hypotheses at rank at least `2^(256R)` and derives the recurrence with its explicit error term.
- `LinearExponentialDecay` proves the recurrence's log-star decay. `ShortProofConclusion` transfers this result to the pancyclic lower bound. It combines this bound with the independently reused upper construction.

## Graph and probability reductions

- `Graph/TerminalForest` and `CycleSpace/Graphical/ExceptionalPartners` construct the terminal forest and actual link-to-branch map, including labelled parallel edges.
- `Graph/Multigraph/ConnectedContraction`, `CycleSpace/Graphical/RegionCutLaw`, and `DisjointRegionCuts` prove the exact cut laws for actual connected regions. `Probability/Cylinders/RegionCycleEvents` supplies the internal factors. `Probability/Moments/SmallCutRegionBound` proves the small-cut corollary.
- `Graph/Cubicization/MarkedReduction` constructs the incidence expansion, full two-core, and unmarked degree-two suppression. It preserves cycle rank. It bounds the marked size and component count. It transfers the forest probability in the required direction.
- `Cycles/Selection/ShortRegionPacking` constructs a maximal packing. `ShortRegionObstructions` and `RetainedHighGirth` remove loops, parallel labels, and all short cycles from the actual retained graph.
- `Graph/Multigraph/InducedDeletionBounds` and `Cycles/Selection/RetainedSizeBounds` prove the retained graph's order and full degree deficit. They do not require positive minimum degree.

## Cycle supply and correlations

- `Nonbacktracking/Spectrum/DeficitContinuity`, `DeficitSpectralBound`, and `DeficitTrace` prove the quadratic-pencil and even-trace estimates for graphs with degrees from zero to three.
- `Cycles/Counting/LowDegreeTraceCycles`, `LowDegreeVertexMass`, and `DeficitCutoffParameters` convert these traces to actual cycle weight and vertex loads. `Cycles/Selection/RetainedCycleSupply` assembles the packing, actual retained graph, girth, and mass bound `z/64` in a single construction.
- `Cycles/Geometry/RetainedExteriorLinks` classifies the original exterior components into marked, large-cut, small cyclic, and forest classes. The retained graph contains these actual forest components. Its girth bounds the number of short joining paths.
- `Probability/Avoidance/ExteriorCyclicCount` bounds the small cyclic class. `Probability/Moments/PairQuotientGeometry` and `PairLinkCount` connect the original labelled graph to the quotient links used by the correlation formula.
- `Cycles/Geometry/ActualCycleLinkBound` supplies the full link bound, including the explicit `578(L/D)^2` geometric error. `ForestCutoffParameters` and `ExceptionalLoadCutoffs` prove its uniform numerical estimates.
- `Graph/Multigraph/InducedCycleSeeds` lifts physical cycles of the retained graph into the ambient cycle space. `LengthIndexedFamily` proves exact weight and vertex-load identities. These identities count each physical cycle once, regardless of its root or orientation.
- `Probability/Moments/SeedPairCorrelation`, `SeedFamilyAvoidance`, and `InducedCycleAvoidance` prove the exact normalized pair law and exceptional packing bound. They then prove the actual forest bound `1/2 + 20/z`. Every probability uses the ambient multigraph cycle space.

## Final assembly

`Probability/Avoidance/FewComponentForest` selects uniform thresholds. It uses the same retained graph for mass and correlations. It proves the marked multigraph forest bound. `MarkedForestReduction` transfers this bound to the original simple graph and witness union. The result is the unconditional `ShortProof.fewComponentForestEstimate`.

`Main` applies the checked recurrence deduction to this theorem. It imports neither the archived main theorem nor the previous uniform core-decay argument. This proof reuses general graph, linear-algebra, counting, and upper-construction lemmas when it depends on them.
