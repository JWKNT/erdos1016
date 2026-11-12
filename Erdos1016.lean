import Erdos1016.Main
import Erdos1016.PolynomialBound.Statement
import Erdos1016.PolynomialBound.LinkBound
import Erdos1016.PolynomialBound.TwoLinkMoment
import Erdos1016.PolynomialBound.Chain
import Erdos1016.PolynomialBound.Product
import Erdos1016.ExactMaximum.Cases
import Erdos1016.ExactMaximum.NetCutFour
import Erdos1016.ExactMaximum.NetCutRank
import Erdos1016.ExactMaximum.LooplessBridge
import Erdos1016.ExactMaximum.LowerBound
import Erdos1016.ExactMaximum.Remaining
import Erdos1016.ExactMaximum.PoleInputs
import Erdos1016.ExactMaximum.PoleReduce
import Erdos1016.ExactMaximum.PoleLayers
import Erdos1016.ExactMaximum.PoleMatchings
import Erdos1016.ExactMaximum.PoleCycleCount
import Erdos1016.ExactMaximum.FullPairs
import Erdos1016.ExactMaximum.Gadgets
import Erdos1016.ExactMaximum.NetEmbed
import Erdos1016.ExactMaximum.FourCutArithmetic
import Erdos1016.ExactMaximum.FourCutNumbering
import Erdos1016.ExactMaximum.FourCutStructure
import Erdos1016.ExactMaximum.FourPorts
import Erdos1016.ExactMaximum.FourCutSides
import Erdos1016.ExactMaximum.FourCut
import Erdos1016.ExactMaximum.CyclicShore
import Erdos1016.ExactMaximum.CycleBoundMargin
import Erdos1016.ExactMaximum.PathFirstEdge
import Erdos1016.ExactMaximum.ShortestCycle
import Erdos1016.ExactMaximum.ExitPole
import Erdos1016.ExactMaximum.ShortCycleExit
import Erdos1016.ExactMaximum.ShortCycleCount
import Erdos1016.ExactMaximum.ShortCycle
import Erdos1016.ExactMaximum.Corollaries
import Erdos1016.ExactMaximum.Main
import Erdos1016.ExactMaximum.CutCaps
import Erdos1016.ExactMaximum.SmallCutCaps
import Erdos1016.ExactMaximum.MainCaps
import Erdos1016.ExactMaximum.ThreeCases
import Erdos1016.ExactMaximum.GirthFive
import Erdos1016.ExactMaximum.MainThreeCases
import Erdos1016.ExactMaximumSupport.Stable
import Erdos1016.ExactMaximumSupport.Shortening.ExactMaximum
import Erdos1016.ExactMaximumSupport.Shortening.BoundedPortExactMaximum
import Erdos1016.ExactMaximumSupport.Shortening.CompactExactMaximum
import Erdos1016.ExactMaximumSupport.Shortening.SharedExactMaximum

/-!
# Erdős problem 1016

The few-component-witness proof, with unconditional endpoint
`Erdos1016.mainTheorem : Problem1016.MainTheorem` and the equivalent
integer-excess statement. The same forest estimate gives the cycle-count
endpoints `Erdos1016.cycleCountTheorem` and `Erdos1016.cycleCountAsymptotic`.
Two elementary theorems on paths and cycles, `Erdos1016.twoTerminalTheorem` and
`Erdos1016.noWasteTheorem`, do not use the forest estimate.
The modules under `Erdos1016/PolynomialBound/` prove steps of two results that
are not formalized as a whole: the bound `2^(r-1) + K r 2^(r/2)` for the number
of cycles, and the forest estimate with a polynomial error. They contain no
endpoint theorem.
The modules under `Erdos1016/ExactMaximum/` state the exact maximum
`ExactMaximum.ExactMaximumStatement` (the number of cycles is the number of Horak
and Kim for every large cyclomatic number) and reduce it to six named statements
(`ExactMaximum.exactMaximumStatement_of_parts`). The loop case, the cubic reduction and the lower
bound are proved. `ExactMaximumSupport.CubicReduction.cubicReductionStatement` closes the
reduction case and `ExactMaximum.lowerBoundStatement` the lower bound.
Of the other four case statements, the case of large girth
(`ExactMaximumSupport.LargeGirth.largeGirthStatement`) and the case of a cyclic cut of size at
most three (`ExactMaximum.threeCutStatement`) are proved, and so is the case of a short cycle
(`ExactMaximum.shortCycleStatement`). The case of a cyclic cut of size four is proved from the
gap theorem (`ExactMaximum.GapStatement`, Theorem 5.10 of the paper), and the gap theorem is
proved (`ExactMaximumSupport.gapStatement`). So the endpoint theorem holds without hypothesis:
`ExactMaximum.exactMaximum : ∃ R, ∀ r, R ≤ r → CycleCount.maxCycles r = horakKim r`
(file `ExactMaximum/Main.lean`).
`ExactMaximumSupport.Stable` also imports the larger marked-forest estimate and
checked graph-level steps of the large-girth argument.
`NetPaths`, `NetMinimal`, `NetSub`, `NetCircuits`, `NetTransfer` and `NetCut` formalize parts of
Sections 5 and 6 of that paper on `Network`: at most `2^b` paths between two vertices, Lemma 5.1,
cycles and paths as minimal words, and the number of cycles of a graph with a cut of one, two,
three or four edges (equation (6.1) and Lemma 6.4; files `NetGlue`, `NetPairs`, `NetCutFour`).
`NetCutRank` proves the rank relation `r + 1 = b₁ + b₂ + d` for a cut with connected sides, and
`LooplessBridge` identifies a `FiniteMultiGraph` without loops with its `Network` (cycles, rank,
degrees, connectedness, cut edges).
`Ring`, `RingChain`, `RingBounds`, `RingCount` and `RingRank` define the ring of squares as a
`Network` and prove that it has rank `r` and at least `H(r)` cycles, for both parities of `r`.
`NetRealization` turns a network without parallel edges into a `SimpleGraph (Fin n)` with the
same cyclomatic number and the same number of cycles. `LowerBound` proves
`ExactMaximum.lowerBoundStatement : LowerBoundStatement` and
`ExactMaximum.exactMaximumStatement_of_four`: the exact maximum follows from the four other
case statements (cuts of size at most three, cuts of size four, short cycles, large girth).
`NetBridge`, `NetSmallCut`, `Poles`, `TwoCut`, `ThirdPair`, `ThreeCut` and `SmallCutCase` prove
Proposition 6.3 from two statements about poles (`ExactMaximum.FewCyclesStatement`, Theorem 5.4
of the paper for one value of `ε`, and `ExactMaximum.PoleCycleBoundStatement`, Corollary 3.11 for
poles): a bridge gives at most `2^(r-1)` cycles, the sides of a smallest cyclic cut of a cubic
network are connected poles, and a cyclic cut of size at most three gives at most
`2^(r-1) + 4 K 2^(r/2)` cycles (`ExactMaximum.threeCutStatement_of_poles`).
`NetSubdivide` and `PoleCycleBound` prove the second statement
(`ExactMaximum.poleCycleBoundStatement`): the subdivision of a network has the same rank and the
same number of cycles and no parallel edges, so `cycleCountTheorem` applies to it. The first
statement is proved in the following files (`ExactMaximum.fewCyclesStatement`), so
Proposition 6.3 holds (`ExactMaximum.threeCutStatement`).
`NetSuppress` and `PoleReduce` prove Lemma 5.2 (a) of the paper: a port
other than the two given ports can be removed, so the first statement follows from its case for
poles with exactly two ports (`ExactMaximum.fewCyclesStatement_of_twoPole`). `NetBridgeCut`,
`PoleSides` and `PoleBridges` prove Lemma 5.2 (b): the two sides of a bridge of such a pole are
poles with two ports, and an induction along the bridges reduces the statement to connected
bridgeless poles (`ExactMaximum.twoPoleFewCyclesStatement_of_bridgeless`).
`CountTools` and `PoleCycleCount` prove the count of Theorem 5.4 for these poles from
Proposition 5.3 and two local statements about cycles
(`ExactMaximum.bridgelessFewCyclesStatement_of_layers`).
`Remaining` derives the exact maximum from the case statements for cuts of size four and for
short cycles (`ExactMaximum.exactMaximumStatement_of_remaining`), and then from the gap theorem
alone (`ExactMaximum.exactMaximumStatement_of_gap`). `FullPairs` states the gap theorem and the
ring case of Theorem 6.8 (`ExactMaximum.GapStatement`, `ExactMaximum.RingCaseStatement`); their
proofs are in `Erdos1016/ExactMaximumSupport/` (`ExactMaximumSupport.gapStatement`,
`ExactMaximumSupport.ringCaseStatement`). `NetAddVertex` adds a vertex of degree two to a
network, and `Gadgets` proves Lemma 5.7 (b), (c), (d) with it (`ExactMaximum.gadget_third_pair`,
`ExactMaximum.gadget_cross_pairs`, `ExactMaximum.gadget_opposite_pair`).
`FourCutStructure`, `FourPorts`, `FourCutNumbering`, `FourCutSides` and `FourCut` prove the rest
of Theorem 6.8: the two sides of a smallest cyclic cut of size four are poles with four ports,
`F ≤ 1`, Lemma 6.7, the side of rank one, and the count as an equation of real numbers. The
arithmetic of Lemmas 6.5 and 6.6 and of the four cases is the statement
`ExactMaximum.FourCutArithmeticStatement` of `FourCutArithmetic`; its proof is in
`Erdos1016/ExactMaximumSupport/`. So the case of a cyclic cut of size four follows from the gap
theorem and the ring case (`ExactMaximum.fourCutStatement_of_gap_ring`), and it is proved
(`ExactMaximum.fourCutStatement`).
`CyclicShore` states Corollary 5.6 for the pole alone (`ExactMaximum.CyclicShoreStatement`); its
proof is in `Erdos1016/ExactMaximumSupport/` (`ExactMaximumSupport.cyclicShoreStatement`).
`CycleBoundMargin`, `PathFirstEdge`, `ShortestCycle`, `ExitPole`, `ShortCycleExit`,
`ShortCycleCount` and `ShortCycle` prove Theorem 7.1 from it
(`ExactMaximum.shortCycleStatement_of_shore`): the cycle bound with a margin, the paths by their
first edge, a shortest cycle (no chord, one exit edge at each vertex), the component that is left
when vertices of the cycle are deleted, and the recursion along the cycle. So the case of a short
cycle is proved (`ExactMaximum.shortCycleStatement`).
`Corollaries` derives the printed forms from the exact maximum, and `Main` has the theorems
without hypothesis: `ExactMaximum.exactMaximum`, the upper bound
`ExactMaximum.upperBoundStatement`, the two parities of equation (1.1)
(`ExactMaximum.maxCycles_parity`, `ExactMaximum.maxCycles_formula`), and the second term
`ψ(r) - 2^(r-1) = Θ(r 2^(r/2))` (`ExactMaximum.maxCycles_secondOrder`,
`ExactMaximum.maxCycles_secondOrder_explicit`).
`MainCaps` proves the theorem a second time, from the parts that the text of the paper uses after
12 November 2026 (`ExactMaximum.exactMaximum_caps`). In the case of a cyclic cut of size four
the larger side of the cut is closed by a small tree, a cap, and Corollary 3.11 for the result
replaces the lemma on poles without a pair of ports with many paths
(`ExactMaximumSupport.Shortening.FourCutTreeCap.fourCutStatement`, with the cap
`ExactMaximumSupport.Shortening.TreeCapCycleBound.exists_thousandth_bound`). In the case of large
girth the marked set is a connected set of eight vertices
(`ExactMaximumSupport.Shortening.FixedMarkerLargeGirth.largeGirthStatement`). The other cases
are those of `Main`. `CutCaps` and `SmallCutCaps` prove Proposition 6.3 with caps in the place
of the bound `(9/16) 2^b` for a pole (`ExactMaximum.capStatement`,
`ExactMaximum.threeCutStatement_caps`); the text does not use this second proof, because it is
not shorter. `audits/ExactMaximumCapsAudit.lean` checks which declarations each proof uses.
`ThreeCases`, `GirthFive` and `MainThreeCases` follow the text of 12 November 2026 with three
cases: a loop or a cyclic cut of size at most three; a cycle of length at most four; girth at
least five. `ExactMaximum.exactMaximum_threeCases` proves the theorem along these cases. Its
third case is not proved in the way of the text: it uses the cases of a cyclic cut of size four,
of bounded girth and of large girth. `ExactMaximum.exactMaximumStatement_of_girthFiveForest`
proves the theorem from `ExactMaximum.GirthForestStatement 5`, which is Theorem 7.1 of the text
and has no formal proof; `ExactMaximum.numCycles_le_marked` is Lemma 3.2 of the text.
`audits/ExactMaximumThreeCasesAudit.lean` checks the axioms and the declarations that each of
the two proofs uses. The files `ExactMaximumSupport/Shortening/ExactMaximum`,
`BoundedPortExactMaximum`, `CompactExactMaximum`, `SharedExactMaximum` and `ChainExactMaximum`
(by Astra) have further proofs of the theorem from other choices of the parts.
`PoleInputs` states the two facts that the proof of `FewCyclesStatement` takes from the forest
estimate (`ExactMaximum.PoleLayerBoundStatement`, `ExactMaximum.PoleCyclePackingStatement`), and
their consequence `ExactMaximum.PoleOutsideRankStatement`. The proofs of these statements are in
`Erdos1016/ExactMaximumSupport/`. `PoleLayers` defines the distance layers of a pole and states
Proposition 5.3 (ii), (iii) and Lemma 5.5 (`ExactMaximum.ThinLayersStatement`,
`ExactMaximum.FourThinLayersStatement`); `PoleMatchings` states the two local facts of the count
of Theorem 5.4 (`ExactMaximum.TwoStrandsStatement`, `ExactMaximum.LayerMatchingStatement`). The
proofs of the statements of these two files are in `Erdos1016/ExactMaximumSupport/` too.
`NetEmbed` treats a side of a cut as a network of its own.
The previous formalization and its manuscript are preserved separately under
`old/` and are not imported.
-/
