import Erdos1016.Probability.Avoidance.LogSquaredMarkedForest
import Erdos1016.Probability.Avoidance.LocalizedForestBound
import Erdos1016.Probability.Avoidance.ThinMarkerLayers
import Erdos1016.Probability.Avoidance.PoleMarker
import Erdos1016.ExactMaximumSupport.CubicReduction.Statement
import Erdos1016.ExactMaximumSupport.PhysicalCycleCount
import Erdos1016.ExactMaximumSupport.SecondOrder
import Erdos1016.ExactMaximumSupport.SecondOrderLower
import Erdos1016.ExactMaximumSupport.Averaging
import Erdos1016.ExactMaximumSupport.Product
import Erdos1016.ExactMaximumSupport.LargeGirth.SimpleRealization
import Erdos1016.ExactMaximumSupport.LargeGirth.LinkBound
import Erdos1016.ExactMaximumSupport.LargeGirth.GoodRow
import Erdos1016.ExactMaximumSupport.LargeGirth.SeparatorWitness
import Erdos1016.ExactMaximumSupport.LargeGirth.ChainSelection
import Erdos1016.ExactMaximumSupport.LargeGirth.WeightedMoore
import Erdos1016.ExactMaximumSupport.LargeGirth.BlockGeometry
import Erdos1016.ExactMaximumSupport.LargeGirth.BallLayers
import Erdos1016.ExactMaximumSupport.LargeGirth.AffinePole
import Erdos1016.ExactMaximumSupport.LargeGirth.CycleSupply
import Erdos1016.ExactMaximumSupport.LargeGirth.RegionPackingSequence
import Erdos1016.ExactMaximumSupport.LargeGirth.PackingCycleSelection
import Erdos1016.ExactMaximumSupport.LargeGirth.SmallBoundaryPieces
import Erdos1016.ExactMaximumSupport.LargeGirth.Packing
import Erdos1016.ExactMaximumSupport.LargeGirth.RaisedGirth
import Erdos1016.ExactMaximumSupport.LargeGirth.ChainContradiction
import Erdos1016.ExactMaximumSupport.LargeGirth.Statement
import Erdos1016.ExactMaximumSupport.PoleLayerInput
import Erdos1016.ExactMaximumSupport.PoleCyclePacking
import Erdos1016.ExactMaximumSupport.FewCyclesSums
import Erdos1016.ExactMaximumSupport.VertexRankDeletion
import Erdos1016.ExactMaximumSupport.CycleLayerSpan
import Erdos1016.ExactMaximumSupport.ThinIntervalBoundary
import Erdos1016.ExactMaximumSupport.PoleOutsideRank
import Erdos1016.ExactMaximumSupport.PoleFourLayers
import Erdos1016.ExactMaximumSupport.ThinLayerShortCycle
import Erdos1016.ExactMaximumSupport.PoleThinLayers
import Erdos1016.ExactMaximumSupport.NetworkShortCycleCut
import Erdos1016.ExactMaximumSupport.InterfaceMatchings
import Erdos1016.ExactMaximumSupport.MatchingProduct
import Erdos1016.ExactMaximumSupport.PoleAvoidingShortCycle
import Erdos1016.ExactMaximumSupport.NatFewCyclesSums
import Erdos1016.ExactMaximumSupport.PoleFewCycles
import Erdos1016.ExactMaximumSupport.PoleMarginLayers
import Erdos1016.ExactMaximumSupport.RingUpperArithmetic
import Erdos1016.ExactMaximumSupport.LadderPermutation
import Erdos1016.ExactMaximumSupport.PolePortReduction
import Erdos1016.ExactMaximumSupport.PoleGapReduction
import Erdos1016.ExactMaximumSupport.PoleGapInduction
import Erdos1016.ExactMaximumSupport.PoleCyclicShore
import Erdos1016.ExactMaximumSupport.PoleTwoPaths
import Erdos1016.ExactMaximumSupport.NetworkIso
import Erdos1016.ExactMaximumSupport.MixedTilesRank
import Erdos1016.ExactMaximumSupport.LadderTileOrder
import Erdos1016.ExactMaximumSupport.NetworkPathInterior
import Erdos1016.ExactMaximumSupport.FullPairRailEquiv
import Erdos1016.ExactMaximumSupport.ThirdPortBridgeInduction
import Erdos1016.ExactMaximumSupport.ThirdPortMarkedCore
import Erdos1016.ExactMaximumSupport.MixedRingOdd
import Erdos1016.ExactMaximumSupport.MixedRingParity
import Erdos1016.ExactMaximumSupport.MixedRingLocalCycles
import Erdos1016.ExactMaximumSupport.MixedRingFibers
import Erdos1016.ExactMaximumSupport.NetworkPathSegment
import Erdos1016.ExactMaximumSupport.FullPairCappedLadder
import Erdos1016.ExactMaximumSupport.ThirdPortRestoredCore
import Erdos1016.ExactMaximumSupport.FourCutArithmeticProof
import Erdos1016.ExactMaximumSupport.MixedRingUpper
import Erdos1016.ExactMaximumSupport.RingCaseInput
import Erdos1016.ExactMaximumSupport.ThirdPortCappedReduction
import Erdos1016.ExactMaximumSupport.PoleExtendedShoreBase
import Erdos1016.ExactMaximumSupport.PoleMarginBridge
import Erdos1016.ExactMaximumSupport.CyclicShoreInput
import Erdos1016.ExactMaximumSupport.ShortCycleInput
import Erdos1016.ExactMaximumSupport.NetworkThreadPathCounts
import Erdos1016.ExactMaximumSupport.GapInput

/-!
# Checked support for the eventual exact maximum

The cubic-reduction statement is proved unconditionally. The other imports
provide exact agreement of the simple and physical cycle counts, the larger
marked-forest estimate, concrete region localization, the quadratic level-width
and affine-marker theorems, the weighted Moore bound, actual port-free balls,
both affine-pole bounds, the finite retained-cycle supply, nested maximal
region packings, and the separator-family and clean-block steps.
Actual core extraction and the two-piece product bound are also proved.
The fixed-probability packing bound and bounded nested high-girth packings
are proved for actual connected cubic multigraphs. The finite clean-chain
contradiction has explicit size and girth budgets.
The final numerical estimates discharge all budgets in the large-girth case.
`LargeGirth.largeGirthStatement` proves that case without extra hypotheses.
The sharp second-order lower bound follows from the proved ring construction.
The two-sided asymptotic still depends on eventual exactness.
Both pole forest inputs are proved on the original network model.
The rank outside an actual shortest path is uniformly bounded in path-rich poles.
Four consecutive thin distance layers contain an actual cycle with at most four edges.
The full thin-layer statement is proved, including its ordinary-layer counting bound.
Large path-rich bridgeless two-poles have a short cycle avoiding any bounded vertex set.
The matching product and natural floor-exponent sum estimates are also proved.
The few-cycles theorem and the case of cyclic cuts of size at most three are proved.
Thin layers and short-cycle avoidance also hold at every positive path-density margin.
The ring optimization and ladder permutation arguments are proved.
The gap theorem reduces to the explicit third-port theorem.
Its rank induction, terminal deletion, adjacent-port case, and rank-one base are proved.
Actual disjoint terminal paths and physical mixed-tile models are also available.
The full-pair complement is an actual matching between the ordered rails.
Third-port bridges reduce to a marked edge in a connected full core.
Every full bridgeless two-pole above rank one is an actual capped mixed ladder.
The isomorphism preserves physical labels, terminal vertices, and rank.
The restored third-port count transfers exactly to a marked concrete core.
All four physical ring sectors have proved bounds.
Concrete mixed rings of weight at least seven satisfy the Horak--Kim bound.
The exact scalar four-cut interface is proved without extra hypotheses.
The original full-cross four-cut graph is a concrete mixed ring.
`ringCaseStatement` proves that case unconditionally, with threshold eight.
The concrete capped marked-edge counts cover every physical label.
The arbitrary-margin cyclic-shore statement is unconditional.
Its proof includes all bridge configurations and tracked extra-port suppression.
The bounded-girth case is unconditional, with its cyclic-shore input discharged.
The full-pair gap is unconditional, including all bridge and suppression cases.
All inputs to the eventual exact maximum are now supplied.
The full mathematical endpoints have a separate expanded audit.
-/
