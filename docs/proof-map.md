# Proof map

The public endpoint is `Erdos1016.mainTheorem : Problem1016.MainTheorem`. It has no mathematical premise. `mainTheorem_integer_excess` checks the equivalent integer-excess formulation.

## Witness extraction and recurrence

- `Extremal/Witness/LeastMissing` constructs least-missing-length cycles and stops at the first rank crossing. Rank jumps skip charges rather than create extra cycles.
- `Graph/ConnectedCover` counts components on the witness's support vertices, excluding isolated host vertices.
- `Extremal/Witness/WeightedExtraction` and `CapacityBudget` prove simultaneous edge, rank, component, and tail-weighted budgets for the same extracted union.
- `Extremal/Capacity/ActualRankTail` defines the tail supremum using each graph's actual cycle rank. `Graph/ConnectedCoverage` preserves rank and covered lengths when connecting components by bridges.
- `Graph/CycleRestrictionForest` and `Extremal/Capacity/WitnessOutsideBound` prove the outside forest requirement, uniform projection fibers, and resulting length-count inequality.
- `Extremal/Recurrence/WitnessReduction` checks the forest hypotheses at rank at least `2^(256R)` and derives the recurrence with its explicit error term.
- `LinearExponentialDecay` proves the recurrence's log-star decay; `ShortProofConclusion` transfers it to the pancyclic lower bound and combines the independently reused upper construction.

## Graph and probability reductions

- `Graph/TerminalForest` and `CycleSpace/Graphical/ExceptionalPartners` construct the terminal forest and actual link-to-branch map, including labelled parallel edges.
- `Graph/Multigraph/ConnectedContraction`, `CycleSpace/Graphical/RegionCutLaw`, and `DisjointRegionCuts` prove the exact cut laws for actual connected regions. `Probability/Cylinders/RegionCycleEvents` supplies the internal factors, and `Probability/Moments/SmallCutRegionBound` proves the small-cut corollary.
- `Graph/Cubicization/MarkedReduction` constructs the incidence expansion, full two-core, and unmarked degree-two suppression. It preserves cycle rank, bounds the marked size and component count, and transports the forest probability in the required direction.
- `Cycles/Selection/ShortRegionPacking` constructs a maximal packing. `ShortRegionObstructions` and `RetainedHighGirth` remove loops, parallel labels, and all short cycles from the actual retained graph.
- `Graph/Multigraph/InducedDeletionBounds` and `Cycles/Selection/RetainedSizeBounds` prove the retained graph's order and full degree deficit, without assuming positive minimum degree.

## Cycle supply and correlations

- `Nonbacktracking/Spectrum/DeficitContinuity`, `DeficitSpectralBound`, and `DeficitTrace` prove the quadratic-pencil and even-trace estimates for graphs with degrees from zero to three.
- `Cycles/Counting/LowDegreeTraceCycles`, `LowDegreeVertexMass`, and `DeficitCutoffParameters` convert these traces to actual cycle weight and vertex loads. `Cycles/Selection/RetainedCycleSupply` assembles the packing, actual retained graph, girth, and mass bound `z/64` in a single construction.
- `Cycles/Geometry/RetainedExteriorLinks` classifies the original exterior components into marked, large-cut, small cyclic, and forest classes. Actual forest components are retained, and short joining paths are bounded using girth.
- `Probability/Avoidance/ExteriorCyclicCount` bounds the small cyclic class. `Probability/Moments/PairQuotientGeometry` and `PairLinkCount` connect the original labelled graph to the quotient links used by the correlation formula.
- `Cycles/Geometry/ActualCycleLinkBound` supplies the full link bound, including the explicit `578(L/D)^2` geometric error. `ForestCutoffParameters` and `ExceptionalLoadCutoffs` discharge its uniform numerical estimates.
- `Graph/Multigraph/InducedCycleSeeds` lifts physical cycles of the retained graph into the ambient cycle space. `LengthIndexedFamily` proves exact weight and vertex-load identities without counting roots or orientations twice.
- `Probability/Moments/SeedPairCorrelation`, `SeedFamilyAvoidance`, and `InducedCycleAvoidance` prove the exact normalized pair law and exceptional packing bound, then the actual forest bound `1/2 + 20/z`. Every probability is taken in the ambient multigraph cycle space.

## Final assembly

`Probability/Avoidance/FewComponentForest` selects uniform thresholds, uses the same retained graph for mass and correlations, and proves the marked multigraph forest bound. `MarkedForestReduction` transfers it back to the original simple graph and witness union, yielding the unconditional `ShortProof.fewComponentForestEstimate`.

`Main` applies the checked recurrence deduction to this theorem. It imports neither the archived main theorem nor the previous uniform core-decay argument. General graph, linear-algebra, counting, and upper-construction lemmas are reused where they are dependencies of this route.
