# Formalisation of the exact maximum: status

Paper: `paper/minimal/exact-maximum/exact-maximum.pdf`
("The maximum number of cycles in a graph of large rank").
Owner of this folder: Fable 5.2. Started on 11 November 2026.

The target is the declaration

```lean
def Erdos1016.ExactMaximum.ExactMaximumStatement : Prop :=
  ∃ R : ℕ, ∀ r, R ≤ r → CycleCount.maxCycles r = horakKim r
```

It is **proved** (12 November 2026, 01:45 UTC), in `Main.lean`:

```lean
theorem Erdos1016.ExactMaximum.exactMaximum :
    ∃ R : ℕ, ∀ r, R ≤ r → CycleCount.maxCycles r = horakKim r
```

`CycleCount.maxCycles r` is the largest number of cycles of a simple graph with cyclomatic number
`r` (`Erdos1016/CycleCount/Asymptotic.lean`; a cycle is counted by its edge set), and `horakKim r`
is the number `H(r)` of Horak and Kim (`HorakKim.lean`). The theorem depends on the axioms
`propext`, `Classical.choice` and `Quot.sound` only. This folder and
`Erdos1016/ExactMaximumSupport/` contain no `sorry`.

`Main.lean` also has these forms, all without hypothesis:

| Declaration | Content |
|---|---|
| `upperBoundStatement` | Every simple graph of large cyclomatic number `r` has at most `H(r)` cycles |
| `maxCycles_parity` | `ψ(2q+1) + 3q = 2^(2q) + (4q+1) 2^(q-1)` and `ψ(2q+2) + 3q + 4 = 2^(2q+1) + (4q+9) 2^(q-1)` for large `q` |
| `maxCycles_formula` | Equation (1.1) of the paper as printed, in real numbers |
| `maxCycles_secondOrder` | `ψ(r) - 2^(r-1) = Θ(r 2^(r/2))` |
| `maxCycles_secondOrder_explicit` | `r 2^(r/2) / 8 ≤ ψ(r) - 2^(r-1) ≤ 2 r 2^(r/2)` for large `r` |
| `gapStatement`, `fourCutStatement` | Theorem 5.10; Theorem 6.8 with Corollary 6.2 |

## The third proof: the three cases of the present text (12 November 2026)

The present text (36 pages; the forest estimate is in a paper of its own,
`paper/minimal/forest/`) has three cases for a connected cubic multigraph of large rank `r`:

1. a cyclic cut of size at most three (a loop gives a cut of size one);
2. no such cut, and a cycle of length four;
3. no such cut and no cycle of length four; then the girth is at least five.

`ThreeCases.lean`, `GirthFive.lean`, the folder `GirthFive/` and `MainThreeCases.lean` follow
this structure.

```lean
theorem Erdos1016.ExactMaximum.exactMaximum_threeCases :
    ∃ R : ℕ, ∀ r, R ≤ r → CycleCount.maxCycles r = horakKim r

theorem Erdos1016.ExactMaximum.girthForestStatement_five : GirthForestStatement 5
```

The first theorem has no hypothesis, and it has the three cases of the text. Its Case 3 is
proved in the way of the text: Theorem 7.1 at girth five (the second theorem; the bound
`q(G,P) < 2/5`), Lemma 3.2 and a marked set of eight vertices. It uses neither the case of
bounded girth nor the case of large girth of the earlier texts
(`audits/ExactMaximumThreeCasesAudit.lean` checks this in the proof terms). The folder
`GirthFive/` has the proof of Theorem 7.1 and a README with the mathematics. Since
12 November 2026 (evening) Theorem 7.1 at girth five has this formal proof; before, it had
none.

| Declaration | Content | Text |
|---|---|---|
| `SmallCutCaseStatement`, `smallCutCaseStatement` | Case 1: a loop or a cyclic cut of size at most three gives at most `H(r)` cycles. From the case of a loop and `ExactMaximumSupport.Shortening.SharedSmallCut.threeCutStatement` | Section 8, Case 1; Proposition 6.3 |
| `FourCycleCaseStatement`, `fourCycleCaseStatement` | Case 2: no loop, no cyclic cut of size at most three, and a cycle of length at most four give at most `H(r)` cycles. The vertex set of the cycle is one side of a cyclic cut of size at most four (`ExactMaximumSupport.ShortCycleCyclicCut.hasCyclicCutLE_four_of_rank_ge_nine`), and the theorem on such a cut with two arbitrary sides applies (`ExactMaximumSupport.Shortening.ChainExactMaximum.fourCutStatement`, by a limit of states) | Section 8, Case 2; Theorem 6.6 with Corollary 6.2 |
| `GirthFiveCaseStatement`, `girthFiveCaseStatement` | Case 3 with the bound `H(r)`, by the method of the text: from `girthCaseStatement_five`. (`girthFiveCaseStatement_of_cases` in `ThreeCases.lean` is the older route through `FourCutStatement`, `ShortCycleStatement` and `LargeGirthStatement`; the main theorem does not use it) | Section 8, Case 3 |
| `GirthForestStatement D`, `girthForestStatement_five` | The statement of Theorem 7.1 with girth at least `D` (a definition), and its proof for `D = 5` (`GirthFive/ForestProbability.lean`). The parts: `GirthFive.exists_affine_bound_girth_five` (pieces at girth five), `GirthFive.exists_block_bound`, `GirthFive.exists_base_finset_packing`, and the last step of the proof for large girth | Theorem 7.1 |
| `GirthCaseStatement D`, `girthCaseStatement_of_forest`, `girthCaseStatement_five` | Case 3 by the method of the text: `GirthForestStatement D` with `D ≥ 3` gives fewer than `2^(r-1)` cycles for a graph without a cyclic cut of size at most three and without a cycle shorter than `D`. A connected set of eight vertices is marked. The third name is the case `D = 5` without a hypothesis | Section 8, Case 3 |
| `numCycles_le_marked` | Lemma 3.2: `c(G) ≤ q(G,P) 2^r + 2^(r - 1 - ⌈|P|/2⌉)` for a connected cubic multigraph without loops in which every cut has at least two edges | Lemma 3.2 |
| `three_le_cut_of_no_cyclic_cut` | Without a cyclic cut of size at most three every cut has at least three edges | Section 8, Case 3 ("no bridge") |
| `not_hasCycleShorterThan_four` | Without a cyclic cut of size at most three, and with rank at least seven, there is no cycle of length at most three | Section 8, Case 3, first step |
| `upperBoundStatement_of_three_cases`, `exactMaximumStatement_of_three_cases` | The reduction to cubic multigraphs, the three cases and the lower bound give the theorem | Section 8 |
| `upperBoundStatement_threeCases`, `exactMaximumStatement_threeCases`, `exactMaximum_threeCases`, `maxCycles_formula_threeCases` | The upper bound, Theorem 1.1 and equation (1.1) | Theorem 1.1 |
| `exactMaximumStatement_of_girthFiveForest` | Theorem 1.1 from Theorem 7.1 of the text as a hypothesis (the same proof, before the hypothesis is discharged) | Sections 6 to 8 |

All of these depend on the axioms `propext`, `Classical.choice` and `Quot.sound` only. Run
`lake env lean audits/ExactMaximumThreeCasesAudit.lean` (exit code 0 on 12 November 2026).

### The present text and the formal statements

The numbers are those of the present text. Since the change of 13 November 2026, 01:00 UTC,
Section 7 has the statements 7.1 to 7.11 (the lemma on rigid sets is gone; see
`paper/minimal/research/slabs.pdf`).
"same" means: a formal statement with the method of the text; details and constants can
differ. "other" means: a formal statement of the same content, or of a stronger one, with
another method. This table is by Fable 5.2 from the file headers and the statements; the
proofs of Astra's files were not compared line by line with the text.

| Text | Formal | Relation |
|---|---|---|
| Theorem 2.1 (forest estimate; Theorem 1.1 of the forest paper) | `Erdos1016.ShortProof.eventually_marked_forest_bound_logSquared` | same, with one difference (the links of two cycles) |
| Lemmas 2.2, 2.3, 2.4 (link formula, exceptional partners, many small cuts) | `Erdos1016/CycleSpace/Graphical/RegionCutLaw.lean`, `DisjointRegionCuts.lean`, `ExceptionalPartners.lean`; `Erdos1016/Probability/Moments/SmallCutRegionBound.lean` | same |
| Proposition 2.5 (cycles of moderate length) | no single statement; its parts are in the formal proof of Theorem 2.1, under the hypothesis `q > 1/2 + ε` | parts |
| Lemma 3.1 (cubic multigraphs) | `ExactMaximumSupport.CubicReduction.cubicReductionStatement` | same |
| Lemma 3.2 (cycles and a marked set) | `numCycles_le_marked` | same |
| Corollary 3.3 (leading term) | `Erdos1016.cycleCountTheorem`, `numCycles_le_of_large_rank_margin` | other (the forest estimate for a simple graph, and chords that close triangles) |
| Lemma 4.1 (layers) | the two uses: `PoleLayerBoundStatement` and the files `Probability/Avoidance/LevelWindowBoundary.lean`, `SymmetricWindow.lean`, `ThinMarkerLayers.lean`, `LocalizedForestBound.lean` | the uses, not the lemma with a level function |
| Lemmas 5.1, 5.2 (joins, reduction) | `Network.IsPathWord.add_cycle_not_path`, `exists_bridge_split`, `twoPoleFewCyclesStatement_of_bridgeless` and the lemmas near them | same |
| Lemma 5.3 (a shortest path) | none in this form | — |
| Proposition 5.4 (away from the shortest path) | `PoleOutsideRankStatement`, for every margin (Astra) | same |
| Theorem 5.5 (few cycles) | `fewCyclesStatement` for `ε = 1/1000`; `ExactMaximumSupport.Shortening.MarginFewCycles.exists_bound` for every margin | other (thin layers and a count of matchings in the place of Lemma 5.3) |
| Lemma 5.6 (ladders) | the classification of full pairs in `Erdos1016/ExactMaximumSupport/` | other (two disjoint paths; exact numbers of paths in a capped ladder) |
| Theorem 5.7 (gap) | `ExactMaximumSupport.gapStatement`, with the constant `1/16` | other (induction on the rank, with a third port) |
| Corollary 5.8, Proposition 6.1, Corollary 6.2 (four ports, rings) | `ExactMaximumSupport.ringCaseStatement`, `ExactMaximumSupport.Shortening.BridgelessRingCase.ringCaseStatement`, `lowerBoundStatement` | same content |
| Lemma 5.9 (three gadgets) | `gadget_third_pair`, `gadget_cross_pairs`, `gadget_opposite_pair`; `ExactMaximumSupport.Shortening.MarginGadgets` for every margin | same |
| Proposition 6.3 (cuts of size at most three) | `threeCutStatement`, `ExactMaximumSupport.Shortening.SharedSmallCut.threeCutStatement` | same |
| Lemma 6.4 (cap) | `ExactMaximumSupport.Shortening.TreeCapMargin.exists_bound`, for every `η` | same |
| Lemma 6.5 (rigidity) | `ExactMaximumSupport.Shortening.FourCutLimitRigidity.rigidity`, `FourCutCompactness.exists_tolerance` | same method (a limit of states), for a cut with two sides |
| Theorem 6.6 (a cycle of length four) | `fourCycleCaseStatement` | other (a cyclic cut of size four with two arbitrary sides) |
| Theorem 7.1 (girth five) | `girthForestStatement_five` | same statement; the end of the proof is another one (short cyclic regions are deleted at the scales `D, 2D, 4D, ...`, as in the formal proof for large girth; the text counts the cycles at one scale) |
| Lemmas 7.2, 7.3 (forest proportions at large girth, product) | `ExactMaximumSupport.Shortening.LargeOrderPieces`, `ExactMaximumSupport.LargeGirth.PoleProduct` | same idea |
| Lemma 7.4 (full pairs at girth five) | `GirthFive.two_terminal_region`, `GirthFive.two_terminal_card_le` (a set in which every word with two given terminals is a forest has at most `400 (\|D\| + 2)` vertices) | **other**: a shortest path between the terminals, a forest beside it and the rail lemma `GirthFive.rail_bound`; the text uses the reduction of Lemma 5.2 and the ladders of Lemma 5.6. (One ingredient of the proof of the text exists: `ExactMaximumSupport.Shortening.FullPairShortCycle.not_full_of_no_short_cycle`) |
| Lemma 7.5 (pieces at girth five) | `GirthFive.exists_affine_bound_girth_five`, with `GirthFive.window_not_rigid` and `GirthFive.region_not_rigid` for the slabs | same since 13 November 2026, 01:00 UTC (the text has the slabs of the formal proof); the constants differ, and the formal count of side components uses parities |
| Corollary 7.6 (pieces) | none; the formal proof does not need it, because its first family has a fixed scale | — |
| Lemma 7.7 to Proposition 7.11 (separators, chain, two links, heavy families, packing) | `ExactMaximumSupport.Shortening.DisjointRegionChain`, `ChainPackingMoment`, `ChainPackingGeometry`, `ChainPacking.exists_cutoff`, `LargeOrderChain`; at girth five: `GirthFive.exists_row_bound`, `GirthFive.exists_base_finset_packing` | other forms: the formal statements have no short cycles outside a deleted set; the text counts the `Λ`-short cycles |
| Section 8 | `upperBoundStatement_of_three_cases`, `girthCaseStatement_of_forest` | same |

The tables below this section are older. Their column "Paper" has the numbers of the first text
(commit `3a80aa9`), in which Theorem 5.4 is the theorem on few cycles, Theorem 6.8 is the case of
a cyclic cut of size four, Theorem 7.1 is the case of bounded girth and Theorem 8.1 is the case
of large girth.

## Which proof uses which file

`audits/UsageMap.lean` computes this table from the proof terms. A file is used by a proof if
the proof uses a declaration of the file, directly or through other declarations. The columns:
`T` is `exactMaximum_threeCases` (the three cases of the present text, with equation (1.1)
and the leading term), `M` is `exactMaximum` (the five cases of the first text), `C` is
`exactMaximum_caps`. The forest estimate (`F`) and the pancyclic theorem (`P`) use no file of
this folder. State of 12 November 2026.

| Module | F | P | T | M | C |
|---|---|---|---|---|---|
| `Cases` |  |  | x | x | x |
| `Corollaries` |  |  | x |  |  |
| `CountTools` |  |  | x | x | x |
| `CutCaps` |  |  |  |  |  |
| `CycleBoundMargin` |  |  | x | x | x |
| `Cycles` |  |  | x | x | x |
| `CyclicShore` |  |  |  | x | x |
| `ExitPole` |  |  |  | x | x |
| `FourCut` |  |  | x | x | x |
| `FourCutArithmetic` |  |  | x | x | x |
| `FourCutNumbering` |  |  | x | x | x |
| `FourCutSides` |  |  | x | x | x |
| `FourCutStructure` |  |  | x | x | x |
| `FourPorts` |  |  | x | x | x |
| `FullPairs` |  |  | x | x | x |
| `Gadgets` |  |  | x | x | x |
| `GirthFive` |  |  | x |  |  |
| `GirthFive.BasePacking` |  |  | x |  |  |
| `GirthFive.ForestProbability` |  |  | x |  |  |
| `GirthFive.GeodesicRails` |  |  | x |  |  |
| `GirthFive.LevelRegions` |  |  | x |  |  |
| `GirthFive.ManyRegions` |  |  | x |  |  |
| `GirthFive.Pieces` |  |  | x |  |  |
| `GirthFive.RailBound` |  |  | x |  |  |
| `GirthFive.RegionRigidity` |  |  | x |  |  |
| `GirthFive.RegionWords` |  |  | x |  |  |
| `GirthFive.TwoTerminal` |  |  | x |  |  |
| `GirthFive.TwoTerminalRegion` |  |  | x |  |  |
| `HorakKim` |  |  | x | x | x |
| `LoopCase` |  |  | x | x | x |
| `LooplessBridge` |  |  | x | x | x |
| `LowerBound` |  |  | x | x | x |
| `Main` |  |  |  | x |  |
| `MainCaps` |  |  |  |  | x |
| `MainThreeCases` |  |  | x |  |  |
| `NetAddVertex` |  |  | x | x | x |
| `NetBridge` |  |  | x | x | x |
| `NetBridgeCut` |  |  | x | x | x |
| `NetCircuits` |  |  | x | x | x |
| `NetCut` |  |  | x | x | x |
| `NetCutFour` |  |  | x | x | x |
| `NetCutRank` |  |  | x | x | x |
| `NetEmbed` |  |  | x | x | x |
| `NetGlue` |  |  | x | x | x |
| `NetJoin` |  |  | x | x | x |
| `NetMinimal` |  |  | x | x | x |
| `NetPairs` |  |  | x | x | x |
| `NetPaths` |  |  | x | x | x |
| `NetRealization` |  |  | x | x | x |
| `NetSmallCut` |  |  | x | x | x |
| `NetSub` |  |  | x | x | x |
| `NetSubdivide` |  |  | x | x | x |
| `NetSuppress` |  |  | x | x | x |
| `NetTransfer` |  |  | x | x | x |
| `PathFirstEdge` |  |  |  | x | x |
| `PoleBridges` |  |  | x | x | x |
| `PoleCycleBound` |  |  |  | x | x |
| `PoleCycleCount` |  |  | x | x | x |
| `PoleInputs` |  |  |  | x | x |
| `PoleLayers` |  |  | x | x | x |
| `PoleMatchings` |  |  | x | x | x |
| `PoleReduce` |  |  | x | x | x |
| `PoleSides` |  |  | x | x | x |
| `Poles` |  |  | x | x | x |
| `Remaining` |  |  |  | x | x |
| `Ring` |  |  | x | x | x |
| `RingBounds` |  |  | x | x | x |
| `RingChain` |  |  | x | x | x |
| `RingCount` |  |  | x | x | x |
| `RingRank` |  |  | x | x | x |
| `ShortCycle` |  |  |  | x | x |
| `ShortCycleCount` |  |  |  | x | x |
| `ShortCycleExit` |  |  |  | x | x |
| `ShortestCycle` |  |  |  | x | x |
| `SmallCutCaps` |  |  |  |  |  |
| `SmallCutCase` |  |  | x | x | x |
| `Statement` |  |  | x | x | x |
| `ThirdPair` |  |  | x | x | x |
| `ThreeCases` |  |  | x |  |  |
| `ThreeCut` |  |  | x | x | x |
| `TwoCut` |  |  | x | x | x |

The proof along the text does not use the files of the case of bounded girth (`CyclicShore`,
`ExitPole`, `PathFirstEdge`, `ShortCycle`, `ShortCycleCount`, `ShortCycleExit`,
`ShortestCycle`), and not `PoleCycleBound`, `PoleInputs` and `Remaining`. `CutCaps` and
`SmallCutCaps` are a second proof of Proposition 6.3 that no main theorem uses.

## The second proof: the proof of the shorter text (12 November 2026)

After 12 November 2026 the text of the paper proves the case of a cyclic cut of size four with a
*cap*, Case 5 with a connected set of eight vertices, and the packing bound of the section on
large girth with the chain of nested separators. `MainCaps.lean` has the theorem by these parts:

```lean
theorem Erdos1016.ExactMaximum.exactMaximum_caps :
    ∃ R : ℕ, ∀ r, R ≤ r → CycleCount.maxCycles r = horakKim r
```

| Declaration | Content |
|---|---|
| `fourCutStatement_caps` | The case of a cyclic cut of size four with the rings, by the cap: `ExactMaximumSupport.Shortening.FourCutTreeCap.fourCutStatement` (Astra) |
| `largeGirthStatement_chain` | Case 5 with eight vertices, the bound `(69/160) 2^r`, and the chain of separators for the packing bound and for the two final pieces: `ExactMaximumSupport.Shortening.ChainLargeGirth.largeGirthStatement` (Astra) |
| `upperBoundStatement_caps`, `exactMaximumStatement_caps`, `exactMaximum_caps`, `maxCycles_formula_caps` | The upper bound, Theorem 1.1 and equation (1.1), from `threeCutStatement`, `fourCutStatement_caps`, `shortCycleStatement`, `largeGirthStatement_chain`, the reduction and the lower bound |
| `largeGirthStatement_marker` | For comparison: Case 5 with eight vertices and the first proof of the packing bound (`ExactMaximumSupport.Shortening.FixedMarkerLargeGirth.largeGirthStatement`, Astra) |
| `threeCutStatement_caps` | For comparison: the case of a cyclic cut of size at most three by caps, without the bound `(9/16) 2^b` (`CutCaps.lean`, `SmallCutCaps.lean`). The text does not use it: the proof with caps is not shorter than the proof with the bound |

The cap for four ports is `ExactMaximumSupport.Shortening.TreeCapCycleBound.exists_thousandth_bound`
(Astra): for a network `N` of large rank `b` and four vertices, the cycles of `N`, the paths
between the six pairs and the pairs of disjoint paths of two pairings are together at most
`4.001 · 2^b`. The proof closes `N` by a small tree and uses `numCycles_le_of_large_rank_margin`.
The first proof (`Main.lean`) uses the arithmetic of a lemma on poles without a pair of ports
with many paths (`FourCutArithmeticStatement`) in this place. Both proofs stay in the library.

The packing bound by the chain is `ExactMaximumSupport.Shortening.ChainPacking.exists_cutoff`
(Astra): at most `150 d^3 (|S|+1) 2^d` pairwise disjoint cyclic regions with at most `d` boundary
edges. The bound `q(G,P) < 2/5` is
`ExactMaximumSupport.Shortening.ChainForestProbability.exists_cutoff` (Astra).

The forest estimate of the text (Theorem 3.1, for a subcubic multigraph with a marked set) is
`Erdos1016.ShortProof.eventually_marked_forest_bound_logSquared` (Astra).

`audits/ExactMaximumCapsAudit.lean` checks the types and the axioms of the second proof, and it
follows the proof terms: `exactMaximum_caps` does not use `fourCutArithmeticStatement`,
`fourCutStatement`, `LargeGirth.largeGirthStatement`, the first proof of the packing bound
(`LargeGirth.Packing.exists_cutoff`) or `exactMaximum`; `threeCutStatement_caps` does not use
`poleCycleBoundStatement`. Run `lake env lean audits/ExactMaximumCapsAudit.lean`.

## Who proved which part

The proof has six parts (`Cases.lean`). Who proved which part:

* Fable 5.2 (this folder): the statement and the reduction to the six parts; the lower bound
  (`lowerBoundStatement`, the rings); the loop case; Theorem 5.4 for `ε = 1/1000`
  (`fewCyclesStatement`) from Astra's Proposition 5.3 and two local facts; Proposition 6.3
  (`threeCutStatement`); Lemma 5.7; Theorem 6.8 from the gap theorem, the ring case and the
  arithmetic (`fourCutStatement_of_parts`); Theorem 7.1 from Corollary 5.6 for the pole
  (`shortCycleStatement_of_shore`).
* Astra (`Erdos1016/ExactMaximumSupport/`): the reduction to cubic multigraphs; the case of
  large girth (Theorem 8.1); Proposition 5.3 and Lemma 5.5 for every margin; the two local facts
  of Theorem 5.4; the arithmetic of Theorem 6.8; the ring case; Corollary 5.6 for the pole; the
  gap theorem (Theorem 5.10), which was the last statement to be proved; the second-order forms.
* Before both: the forest estimate and `cycleCountTheorem` (other folders of the repository).

A statement that one of us posted for the other is a `def ... : Prop` in this folder
(`PoleInputs`, `PoleLayers`, `PoleMatchings`, `FullPairs`, `FourCutArithmetic`, `CyclicShore`),
and its proof is in `Erdos1016/ExactMaximumSupport/`. The theorems that use such a statement are
implications, and `Remaining.lean` and `Main.lean` put the proofs in.

## What is proved

| Lean declaration | Content | Paper |
|---|---|---|
| `horakKim`, `horakKim_odd`, `horakKim_even` | The numbers `H(r)`, with forms without subtraction | (1.1) |
| `two_pow_le_horakKim` | `2^(r-1) ≤ H(r)` for `r ≥ 3` | Section 9 |
| `add_mul_two_pow_lt_horakKim` | `2^(r-1) + K 2^((r+1)/2) < H(r)` for `r ≥ 2K + 6` | (9.1) |
| `FiniteMultiGraph.IsCycleWord`, `numCycles` | Cycles of a multigraph as edge words | Section 2 |
| `FiniteMultiGraph.boundary_apply_eq_selectedDegree` | The boundary is the degree modulo two | Section 1 |
| `FiniteMultiGraph.numCycles_lt_two_pow` | Fewer than `2^r` cycles | Section 1 |
| `FiniteMultiGraph.IsCycleWord.eq_single_of_loop` | A cycle through a loop is the loop | Section 9, Case 1 |
| `FiniteMultiGraph.numCycles_le_of_loop` | A multigraph with a loop has at most `2^(r-1)` cycles | Section 9, Case 1 |
| `exactMaximumStatement_of_bounds` | Upper bound and lower bound give the theorem | Section 9 |
| `upperBoundStatement_of_cases` | The reduction to cubic multigraphs and the cases 2 to 5 give the upper bound | Section 9 |
| `exactMaximumStatement_of_parts` | The six statements below give the theorem | Theorem 1.1 |
| `Network.deg`, `Network.boundary_eq_deg` | Degrees in a network; the boundary is the degree modulo two | Section 2 |
| `Network.IsCycleWord`, `Network.IsPathWord`, `numCycles`, `numPaths` | Cycles and paths of a network as edge words | Section 5.1 |
| `Network.numCycles_lt_two_pow` | Fewer than `2^b` cycles | Section 1 |
| `Network.numPaths_le_two_pow` | At most `2^b` paths between two vertices | (5.1) |
| `Network.IsPathWord.add_cycle_not_path` | A path plus a vertex-disjoint cycle is a join that is not a path | Lemma 5.1 |
| `Network.IsFullPair.cycle_meets_path` | If a pair is full, every cycle meets every path | Lemma 5.1 |
| `Network.two_mul_numPaths_le_of_disjoint_cycle` | If a cycle meets no path, at most `2^(b-1)` paths | Lemma 5.1 |
| `Network.IsCycleWord.eq_of_even_subword` | A nonzero even sub-word of a cycle is the cycle | used in Sections 5, 6 |
| `Network.IsPathWord.eq_zero_of_even_subword` | An even sub-word of a path is zero | used in Sections 5, 6 |
| `Network.sub`, `Network.extend`, `Network.boundary_extend` | The network of a set of edges; the boundary commutes with extension by zero | Sections 5, 6 |
| `Network.exists_join_of_reachable` | Two vertices joined by edges of `x` are the odd vertices of a sub-word of `x` | used in Sections 5, 6 |
| `Network.isCycleWord_of_minimal`, `isCycleWord_iff_minimal` | A word is a cycle if and only if it is a minimal nonzero even word | used in Sections 5, 6 |
| `Network.isPathWord_of_minimal`, `isPathWord_iff_minimal` | A word is a path from `s` to `t` if and only if it has odd degree exactly at `s`, `t` and no nonzero even sub-word | used in Sections 5, 6 |
| `Network.deg_restrict_of_closed`, `exists_even_through` | The part of a word in a closed set of vertices; an even word through two edges at a vertex | tools |
| `Network.isCycleWord_extend_iff`, `isPathWord_extend_iff` | A word of a part is a cycle (a path) if and only if its extension is one | Sections 5, 6 |
| `Network.numCycles_sub`, `numPaths_sub` | The cycles (paths) of a part are the cycles (paths) of the network within the part | Sections 5, 6 |
| `Network.cut_parity`, `even_card_crossSet` | An even word has an even number of edges across a cut | Section 6 |
| `Network.numCyclesAcross_empty` | A cycle without a crossing edge is a cycle of one side | Section 6 |
| `Network.isCycleWord_glue`, `IsCycleWord.parts_of_crossSet_pair` | Two crossing edges and a path in each side form a cycle, and every cycle through exactly two crossing edges has this form | Section 6 |
| `Network.numCyclesAcross_pair` | The number of cycles through exactly two given crossing edges is a product of two numbers of paths | Section 6 |
| `Network.numCycles_of_one_crossing` | A cut with one edge: `c(G) = c(T_1) + c(T_2)` | Proposition 6.3, `d = 1` |
| `Network.numCycles_of_two_crossing` | A cut with two edges: `c(G) = c(T_1) + c(T_2) + P(T_1) P(T_2)` | (6.1), `d = 2` |
| `Network.numCycles_of_three_crossing` | A cut with three edges: `c(G) = c(T_1) + c(T_2) + sum of three products` | (6.1), `d = 3` |
| `Network.isPathWord_glue` | A path in each side and a crossing edge between their ends form a path | Section 6 |
| `Network.isCycleWord_glue4` | Two path pairs with different pairings and four crossing edges form one cycle | Lemma 6.4 |
| `Network.exists_pathPair_of_minimal`, `IsPathPair.eq_of_add_eq`, `IsPathPair.false_of_add_eq` | A word with four odd vertices, degrees at most two and no even sub-word is a pair of disjoint paths; the pair and the pairing are unique | Lemma 6.4 |
| `Network.numCyclesAcross_four` | The number of cycles through four crossing edges: the sum over ordered pairs of different pairings | Lemma 6.4 |
| `Network.numCycles_of_four_crossing` | A cut with four edges: the formula for `c(G)` | Lemma 6.4 |
| `Network.networkRank_add_one_of_cut` | A connected network with a cut whose sides are connected: `r + 1 = b_1 + b_2 + d` | Section 6 |
| `FiniteMultiGraph.isCycleWord_iff_looplessNetwork` | An edge word without a loop is a cycle of the multigraph if and only if it is a cycle of its network | link of the two models |
| `FiniteMultiGraph.numCycles_eq_looplessNetwork`, `cycleRank_eq_networkRank`, `degree_eq_deg`, `connected_iff_looplessNetwork` | A multigraph without loops and its network have the same cycles, rank, degrees and connectedness | link of the two models |
| `FiniteMultiGraph.mem_cutEdges_iff_crosses`, `hasCycleIn_iff_looplessNetwork` | Cut edges and cycles in a side agree in the two models | link of the two models |
| `Network.isPathWord_unitWord`, `IsPathWord.add_pendant`, `IsPathWord.add_closing` | An edge is a path; a path and an edge to a new vertex form a path; a path and an edge between its ends form a cycle | tools |
| `Network.IsPathWord.glue`, `glue_three`, `glue_cycle`, `IsPathPair.glue` | Disjoint paths that are joined by edges form paths, cycles and path pairs | tools |
| `Ring.ring` | The ring of `k + 1` squares, with one subdivided interface and a rung | Section 6.1 |
| `Ring.step_paths`, `step_left`, `step_right`, `step_pairs`, `step_ends`, `step_cycles` | One more tile: the six recursions for a chain of tiles | Proposition 6.1 |
| `Ring.chainBounds` | Lower bounds for the paths, path pairs and cycles of every chain | Proposition 6.1 |
| `Ring.closing_cycles`, `closing_paths`, `rung_cycles` | The cycles and paths through the hubs, and the cycles through the rung | Proposition 6.1 |
| `Ring.horakKim_le_numCyclesNoRung` | The ring without the rung (rank `2k+3`) has at least `H(2k+3)` cycles | Corollary 6.2 |
| `Ring.horakKim_le_numCycles_ring` | The ring with the rung (rank `2k+4`) has at least `H(2k+4)` cycles | Corollary 6.2 |
| `Ring.connected_ring`, `Ring.ring_simple`, `Ring.networkRank_ring`, `Ring.networkRank_ring_noRung` | The ring is connected, has no parallel edges, and has rank `2k+4` (`2k+3` without the rung) | Section 6.1 |
| `Network.Relabel.numCycles_eq`, `Relabel.networkRank_eq` | A relabelling of a network keeps the number of cycles and the rank | tools |
| `Network.exists_simpleGraph_of_network` | A network without parallel edges gives a `SimpleGraph (Fin n)` with the same cyclomatic number and the same number of cycles | link to the statement |
| `Network.exists_isCycleWord_subword`, `exists_isCycleWord_of_rank_pos` | Every nonzero even word contains a cycle; positive rank gives a cycle | tools |
| `Network.numCycles_le_of_bridge` | A connected network with a bridge whose two sides contain a cycle has at most `2^(r-1)` cycles | Proposition 6.3, `d = 1` |
| `Network.Embed.numCycles_eq`, `numPaths_eq`, `networkRank_eq_sub`, `numCycles_induce`, `networkRank_induce` | A network inside another one; the side of a cut as a network of its own | tools |
| `Network.three_mul_card_eq`, `isCyclicCut_of_cutSize_le_two`, `cutSize_ge_of_minimal` | Counting edge ends in a cubic network: a cut with at most two edges is cyclic | start of Section 6 |
| `Network.reachable_inside_of_minimal`, `false_of_two_crossing_at` | The sides of a smallest cyclic cut are connected, and no vertex is on two of its edges | Proposition 6.3 |
| `Network.isWeakPole_inside`, `isPort_inside` | The sides of a smallest cyclic cut are poles, and the ends of the cut edges are ports | Proposition 6.3 |
| `numCycles_le_of_two_cut` | A cyclic cut of size two: at most `2^(r-1) + 2K 2^(r/2)` cycles, **from** `FewCyclesWith K` and `PoleCycleBoundWith B` | Proposition 6.3, `d = 2` |
| `Network.exists_isPathWord_of_reachable` | Two vertices that are joined inside a part are joined by a path within the part | tools |
| `Network.Hook.networkRank_part_le`, `Hook.isWeakPole_part`, `Hook.numPaths_part_ge`, `Hook.numCycles_part_ge` | A side, two cut edges and a path of the other side form a pole of rank at most `b + 1` that contains the paths and cycles of the side | Lemma 5.7 (b) |
| `third_pair`, `third_pairs` | If two pairs of ports of a side have together at least `1.002 · 2^b` paths, the third pair has at most `(2K 2^b)^(1/2)` paths, **from** `FewCyclesWith K` | Lemma 5.7 (b) |
| `three_cut_arith` | The case analysis for a cut of size three, in natural numbers | Proposition 6.3, `d = 3` |
| `numCycles_le_of_three_cut` | A smallest cyclic cut of size three: at most `2^(r-1) + 4K 2^(r/2)` cycles, **from** `FewCyclesWith K` and `PoleCycleBoundWith B` | Proposition 6.3, `d = 3` |
| `numCycles_le_of_small_cut` | A connected cubic network with a cyclic cut of size at most three, **from** the same two hypotheses | Proposition 6.3 |
| `threeCutStatement_of_poles` | `FewCyclesStatement` and `PoleCycleBoundStatement` give `ThreeCutStatement` | Proposition 6.3 |
| `Network.subdivide`, `subdivide_simple`, `numCycles_subdivide`, `networkRank_subdivide` | The network with a new vertex on every edge has no parallel edges, the same rank and the same number of cycles | tools |
| `numCycles_le_of_large_rank`, `poleCycleBoundStatement` | A network of large rank `b` has at most `(9/16) 2^b` cycles; this is `PoleCycleBoundStatement` | Corollary 3.11 for poles |
| `Network.suppress`, `Thread.numCycles_suppress`, `numPaths_suppress`, `networkRank_suppress`, `deg_suppress`, `reachable_suppress` | Removing a vertex of degree two (its two edges become one edge) keeps the rank, the cycles, the paths between other vertices, the other degrees and the connections | Lemma 5.2 (a) |
| `Network.two_mul_numPaths_le_of_digon` | If both edges at a vertex of degree two end in the same vertex, at most half of the possible paths exist | Lemma 5.2 (a) |
| `fewCyclesWith_of_twoPole`, `fewCyclesStatement_of_twoPole` | Theorem 5.4 for poles with exactly two ports implies Theorem 5.4 | Lemma 5.2 (a) |
| `Network.networkRank_of_one_crossing`, `numPaths_of_one_crossing` | A cut with one crossing edge: `b = b_1 + b_2` and `P = P_1 P_2` | Lemma 5.2 (b) |
| `Network.rank_side_pos_of_one_crossing`, `two_mul_numPaths_le_of_same_side`, `two_mul_numPaths_le_of_bridge_at` | Both sides of a bridge have a cycle; a bridge that does not separate the two ports, or that is at a port, leaves at most half of the paths | Lemma 5.2 (b) |
| `Network.exists_bridge_split` | In a pole with two ports and many paths, a bridge separates the ports, and its two sides are poles with two ports | Lemma 5.2 (b) |
| `Network.isBridgelessTwoPole_induce` | A bridgeless pole without its isolated vertices is a connected bridgeless pole with the same numbers | model |
| `pole_invariant`, `twoPoleFewCyclesStatement_of_bridgeless` | Induction along the bridges with `(c + 2κ)² ≤ 4κ² 2^b`: Theorem 5.4 follows from its case for connected bridgeless poles with two ports | Lemma 5.2 (b) |
| `Network.natCard_le_of_determined`, `exists_separating_edge`, `card_le_half_of_no_consecutive`, `sum_halfPowSum_le` | Counting tools: words determined by a set of edges; a separating edge; sets without consecutive numbers; `Σ_{i≤j≤n} 2^⌊(j-i)/2⌋ ≤ 16 · 2^⌊n/2⌋` | Theorem 5.4, the count |
| `Network.eq_of_restrict_codeSet`, `natCard_codeSet_le` | A cycle with first layer `i` and last layer `j` is determined by its values on a set of at most `3 (C + 4) + (j - i)/2` edges | Theorem 5.4, the count |
| `bridgelessFewCyclesStatement_of_layers` | Theorem 5.4 for connected bridgeless poles with two ports, **from** `ThinLayersStatement`, `TwoStrandsStatement`, `LayerMatchingStatement` | Theorem 5.4 |
| `fewCyclesStatement_of_local` | Theorem 5.4 for `ε = 1/1000`, **from** `TwoStrandsStatement` and `LayerMatchingStatement` | Theorem 5.4 |
| `fewCyclesStatement` | **Theorem 5.4 for `ε = 1/1000`**: a pole of rank `b` with at least `0.501 · 2^b` paths between two ports has at most `(K 2^b)^(1/2)` cycles | Theorem 5.4 |
| `threeCutStatement` | **Proposition 6.3**: a cyclic cut of size at most three gives at most `2^(r-1) + K 2^(r/2)` cycles | Proposition 6.3 |
| `Network.addVertex`, `networkRank_addVertex_le`, `numPaths_le_numCycles_addVertex`, `numPaths_add_le_numPaths_addVertex`, `numPaths_pairs_le_numPaths_addVertex`, `isWeakPole_addVertex` | A new vertex of degree two at two ports: the rank grows by at most one; paths between the two ports become cycles; paths from the ports become paths from the new vertex; pairs of disjoint paths become paths | Lemma 5.7 |
| `gadget_third_pair`, `gadget_cross_pairs`, `gadget_opposite_pair` | **Lemma 5.7 (b), (c), (d)** for every pole, from `FewCyclesWith K` | Lemma 5.7 |
| `Network.reachable_inside_of_four`, `false_of_two_crossing_at_four`, `exists_isFourCut` | A smallest cyclic cut of size four of a connected cubic network: the sides are connected, no vertex is on two cut edges, the sides are poles with four different ports, `r + 1 = h + k + 4` | Theorem 6.8, first paragraph |
| `Network.exists_eq_of_rank_one`, `boundary_ones_eq_zero_of_rank_one` | A side of rank one has only its four ports, so every vertex has even degree in it | Theorem 6.8, Case 1, `h = 1` |
| `Network.numPathPairs_add_le` | `F ≤ 1`: the pairs of disjoint paths between four vertices, for the three pairings together, are at most `2^b` | Section 6.2 |
| `Network.IsFullPair.isPathWord_of_boundary`, `IsFullPair.exists_cycle_at` | If a pair is full, every word with odd degree exactly at its two ports is a path; a port of a full pair lies on a cycle | Lemma 5.1, Lemma 6.7 |
| `Network.two_mul_numPathPairs_le_of_full` | **Lemma 6.7**: if the pairs `a, j` and `a, k` are full, at most `2^(b-1)` pairs of disjoint paths join `a` to `j` and `k` to `l` | Lemma 6.7 |
| `Network.numPathPairs_le_one_of_rank_one` | Rank one and even degrees: at most one pair of disjoint paths for given ends | Theorem 6.8, Case 1, `h = 1` |
| `quad_canon`, `exists_pairing`, `renumber_injective`, `renumber_surjective` | The numbering of four ports and of the three pairings: finite checks | Section 6.2 |
| `fourState_of_pole`, `largeState_of_pole`, `pairShare_le_half_of_rank_one` | The nine numbers `a_ij`, `u_α` of a pole with four ports satisfy the hypotheses of the arithmetic statement, **from** `GapStatement` (and `FewCyclesWith K` for a pole of large rank) | (6.3) to (6.5), Lemma 6.7 |
| `four_cut_count` | `c(G) / 2^(h+k) = c(X) / 2^(h+k) + c(Y) / 2^(h+k) + 𝓑`, in real numbers | (6.6) |
| `numCycles_le_of_four_cut_inside`, `numCycles_le_of_four_cut` | Theorem 6.8 for networks: at most `H(r)` cycles, **from** `GapStatement`, `FourCutArithmeticStatement`, `FewCyclesWith K`, `PoleCycleBoundWith B`, `RingCaseWith R` | Theorem 6.8 |
| `fourCutStatement_of_parts`, `fourCutStatement_of_gap_ring` | **Theorem 6.8 with Corollary 6.2 (Case 3), from** `GapStatement` and `RingCaseStatement` | Theorem 6.8 |
| `exactMaximumStatement_of_gap_ring_short` | The theorem from `GapStatement`, `RingCaseStatement`, `ShortCycleStatement` | Theorem 1.1 |
| `numCycles_le_of_large_rank_margin` | For every `m`, a network of large rank `b` has at most `(1/2 + 2^(-m-1)) 2^b` cycles | Corollary 3.11 |
| `Network.numCycles_le_add_numPathsIn` | `c(N) ≤ c(N - e) + P`, with the paths between the ends of `e` that do not use `e` | Theorem 7.1 |
| `Network.numPathsIn_le_of_two_edges`, `numPathsIn_le_of_one_edge` | A path from `s` starts with an edge at `s`; the rest is a path that uses no edge at `s` | Theorem 7.1 |
| `Network.IsCycleWord.exists_exit`, `no_chord`, `no_two_feet` | A shortest cycle of a cubic network: one exit edge at each vertex, no chord, at most one edge from a vertex outside (five or more edges) | Theorem 7.1, first paragraph |
| `Network.isWeakPole_compEdges`, `natCard_ports_compEdges_le`, `rank_compEdges_add_le` | The component of a vertex in a part of a network: a pole, its ports, and its rank by the count of edges and vertices | Theorem 7.1, "The rank of `K_p`", "The shape of `K_p`" |
| `Network.false_of_shore` | A cubic cyclic shore of a part of a cubic network is a cyclic cut with at most four edges | Corollary 5.6, last step |
| `Network.ShortSetting.exit_bound` | The bound for the paths that leave the cycle at one vertex, **from** the pole statement for one pair of parameters | Theorem 7.1, "The count" |
| `Network.ShortState.step`, `ShortState.count` | The recursion along the cycle: the states, and the sum of the exit terms | Theorem 7.1 |
| `Network.networkRank_sub_ne`, `numCycles_lt_of_short_cycle` | `N - e` has rank `r - 1`; Theorem 7.1 for networks | Theorem 7.1 |
| `shortCycleStatement_of_shore`, `shortCycleStatement` | **Theorem 7.1 (Case 4)**, from `CyclicShoreStatement`, and without hypothesis | Theorem 7.1 |
| `fourCutStatement_of_gap`, `exactMaximumStatement_of_gap` | Theorem 6.8 and Theorem 1.1 **from** `GapStatement` | Theorem 1.1 |
| `parity_of_exactMaximum`, `formula_of_exactMaximum`, `secondOrder_of_exactMaximum` | The printed forms of the theorem, from `ExactMaximumStatement` | (1.1) |
| `exactMaximum`, `exactMaximumStatement`, `upperBoundStatement`, `maxCycles_formula`, `maxCycles_secondOrder` | **Theorem 1.1**, without hypothesis, and its forms | Theorem 1.1 |
| `lowerBoundStatement` | For every `r >= 3` some simple graph of cyclomatic number `r` has at least `H(r)` cycles | Corollary 6.2 |
| `exactMaximumStatement_of_four` | The four case statements below give the theorem | Theorem 1.1 |
| `threeCutStatement_of_fewCycles`, `exactMaximumStatement_of_remaining` | Proposition 6.3 from Theorem 5.4; the theorem from the statements that are left | Theorem 1.1 |

All of these depend on the axioms `propext`, `Classical.choice` and `Quot.sound` only.

## The statements and their proofs

The six statements of `Cases.lean`:

| Lean statement | Paper | State |
|---|---|---|
| `LowerBoundStatement` | Corollary 6.2 | **Proved**: `lowerBoundStatement` |
| `CubicReductionStatement` | Lemma 3.10 | **Proved** by Astra: `ExactMaximumSupport.CubicReduction.cubicReductionStatement` |
| `LargeGirthStatement` | Theorem 8.1, Section 9 Case 5 | **Proved** by Astra: `ExactMaximumSupport.LargeGirth.largeGirthStatement` |
| `ThreeCutStatement` | Proposition 6.3 | **Proved**: `threeCutStatement` |
| `FourCutStatement` | Theorem 6.8, Corollary 6.2 | **Proved**: `fourCutStatement` (`Main.lean`), from `fourCutStatement_of_gap` |
| `ShortCycleStatement` | Theorem 7.1 | **Proved**: `shortCycleStatement` |

Theorem 5.4 and its inputs. A pole may have isolated vertices here (`Network.IsWeakPole`),
because a side of a cut is a network on all vertices of the graph.

| Lean statement | Paper | State |
|---|---|---|
| `PoleCycleBoundStatement` (`TwoCut.lean`) | Corollary 3.11 for poles | **Proved**: `poleCycleBoundStatement` |
| `FewCyclesStatement` (`TwoCut.lean`) | Theorem 5.4 for `ε = 1/1000` | **Proved**: `fewCyclesStatement` |
| `TwoPoleFewCyclesStatement` (`PoleReduce.lean`) | the same for poles with two ports | Reduction proved: `fewCyclesStatement_of_twoPole` (Lemma 5.2 (a)) |
| `BridgelessFewCyclesStatement` (`PoleBridges.lean`) | the same for connected bridgeless poles with two ports | Reduction proved: `twoPoleFewCyclesStatement_of_bridgeless` (Lemma 5.2 (b)) |
| `PoleLayerBoundStatement`, `PoleCyclePackingStatement`, `PoleOutsideRankStatement` (`PoleInputs.lean`) | Proposition 5.3, Steps 1 to 3 | **Proved** by Astra (`ExactMaximumSupport`) |
| `ThinLayersStatement` (`PoleLayers.lean`) | Proposition 5.3 (ii), (iii) | **Proved** by Astra: `ExactMaximumSupport.thinLayersStatement` |
| `FourThinLayersStatement` (`PoleLayers.lean`) | Lemma 5.5 | **Proved** by Astra: `ExactMaximumSupport.fourThinLayersStatement` |
| `TwoStrandsStatement` (`PoleMatchings.lean`) | Theorem 5.4, "Two strands" | **Proved** by Astra: `ExactMaximumSupport.CycleTwoStrands.twoStrandsStatement` |
| `LayerMatchingStatement` (`PoleMatchings.lean`) | Theorem 5.4, "Matchings" | **Proved** by Astra: `ExactMaximumSupport.layerMatchingStatement` |
| `GapStatement` (`FullPairs.lean`) | Theorem 5.10 | **Proved** by Astra: `ExactMaximumSupport.gapStatement` |
| `RingCaseStatement` (`FullPairs.lean`) | Theorem 6.8, Case 4, with Corollary 6.2 | **Proved** by Astra: `ExactMaximumSupport.ringCaseStatement` |
| `CyclicShoreStatement` (`CyclicShore.lean`) | Corollary 5.6 for the pole alone, every margin `2^(-m)` | **Proved** by Astra: `ExactMaximumSupport.cyclicShoreStatement` |
| `FourCutArithmeticStatement` (`FourCutArithmetic.lean`) | Lemmas 6.5, 6.6 and the four cases of Theorem 6.8, as arithmetic of real numbers | **Proved** by Astra: `ExactMaximumSupport.FourCutArithmeticProof.fourCutArithmeticStatement` |

## Two models

The six statements are about `FiniteMultiGraph` (loops allowed), because a cubic multigraph can
have a loop. Sections 5 to 7 are about parts of a graph without loops (poles). For them this
folder uses `BoundaryTrace.Network V E`, the multigraph without loops on arbitrary finite types.
A part of a network is the network of a subtype of its edges, so nothing is renumbered, and the
library already has Euler's formula (`network_rank_euler`) and the solvable demands
(`mem_range_boundary_iff`) for it. `LooplessBridge.lean` links the two models: a multigraph
without loops and its network `FiniteMultiGraph.looplessNetwork` have the same cycles, rank,
degrees, connectedness and cuts.

## Next steps

No statement is open. Possible further work: a referee's reading of the paper; a smaller set of
files for a reader who wants to check the definitions; explicit thresholds (the theorem gives
"for all large `r`" only).

## Elsewhere in the repository

Other folders of the repository contain the forest estimate for `|E(W)| ≤ sqrt r`
(`ShortProof.fewComponentForestEstimate`), the bound `(1/2 + o(1)) 2^r` (`cycleCountTheorem`),
the link formula, the bound for exceptional partners, and several lemmas of Section 8 in an
earlier form (`Erdos1016/PolynomialBound/`).

## Size

This folder has about 19,800 lines in 67 files.

## Files

| File | Lines | Content |
|---|---|---|
| `HorakKim.lean` | 138 | The numbers `H(r)` |
| `Statement.lean` | 65 | The theorem, the upper and the lower bound as statements |
| `Cycles.lean` | 164 | Cycles of a multigraph, cuts, girth |
| `LoopCase.lean` | 170 | Case 1 |
| `Cases.lean` | 122 | The six statements and the reduction |
| `NetPaths.lean` | 371 | Cycles and paths of a network; (5.1); Lemma 5.1 |
| `NetMinimal.lean` | 200 | Even sub-words of cycles and of paths |
| `NetSub.lean` | 117 | The network of a set of edges; joins inside a connected part |
| `NetCircuits.lean` | 581 | Cycles and paths as minimal words |
| `NetTransfer.lean` | 230 | Cycles and paths of a part of a network |
| `NetCut.lean` | 874 | Cut parity; cycles across a cut of one, two or three edges |
| `NetGlue.lean` | 337 | Gluing paths across a cut; two path pairs form a cycle |
| `NetPairs.lean` | 487 | Pairs of disjoint paths; the parts of a cycle through four crossing edges |
| `NetCutFour.lean` | 560 | Lemma 6.4: cycles across a cut of four edges |
| `NetCutRank.lean` | 122 | The rank of a network with a cut |
| `LooplessBridge.lean` | 242 | A multigraph without loops as a network |
| `NetJoin.lean` | 385 | Joining disjoint paths by edges; single edges |
| `Ring.lean` | 350 | The ring of squares; one tile |
| `RingChain.lean` | 830 | The six recursions for a chain of tiles |
| `RingBounds.lean` | 185 | The induction; closed forms of the bounds |
| `RingCount.lean` | 560 | The hubs and the rung; the comparison with `H(r)` |
| `RingRank.lean` | 142 | The ring is connected and simple; its rank |
| `NetRealization.lean` | 279 | Relabelling; a network as a `SimpleGraph (Fin n)` |
| `LowerBound.lean` | 72 | `lowerBoundStatement`, `exactMaximumStatement_of_four` |
| `NetBridge.lean` | 269 | Cycles in even words; a bridge |
| `NetEmbed.lean` | 426 | A network inside another network; induced networks |
| `NetSmallCut.lean` | 438 | Small cuts of a cubic network; a smallest cyclic cut |
| `Poles.lean` | 190 | Poles; the sides of a smallest cyclic cut |
| `TwoCut.lean` | 257 | The two statements about poles; a cyclic cut of size two |
| `ThirdPair.lean` | 607 | Paths inside a part; Lemma 5.7 (b) for a side of a cut |
| `ThreeCut.lean` | 424 | The arithmetic and the theorem for a cyclic cut of size three |
| `SmallCutCase.lean` | 139 | Proposition 6.3 from the two statements about poles |
| `NetSubdivide.lean` | 244 | The subdivision of a network |
| `PoleCycleBound.lean` | 69 | The cycle bound for networks of large rank |
| `Remaining.lean` | 137 | The theorem from the gap theorem |
| `PoleInputs.lean` | 76 | The two inputs of Theorem 5.4 from the forest estimate, as statements |
| `NetSuppress.lean` | 583 | Removing a vertex of degree two |
| `PoleReduce.lean` | 330 | Lemma 5.2 (a): Theorem 5.4 follows from its case for two ports |
| `NetBridgeCut.lean` | 490 | A cut with one crossing edge: parity, rank, paths |
| `PoleSides.lean` | 396 | The two sides of a bridge of a pole |
| `PoleBridges.lean` | 320 | Lemma 5.2 (b): the induction along the bridges |
| `PoleLayers.lean` | 95 | Distance layers of a pole: definitions and two statements |
| `PoleMatchings.lean` | 82 | Layer edges and matchings: definitions and two statements |
| `CountTools.lean` | 211 | Tools for the count of Theorem 5.4 |
| `PoleCycleCount.lean` | 527 | The count of Theorem 5.4 |
| `FullPairs.lean` | 62 | The gap theorem and the ring case, as statements |
| `NetAddVertex.lean` | 723 | A new vertex of degree two |
| `Gadgets.lean` | 178 | Lemma 5.7 (b), (c), (d) |
| `FourCutArithmetic.lean` | 87 | The arithmetic of Theorem 6.8, as a statement about real numbers |
| `FourCutStructure.lean` | 496 | A smallest cyclic cut of size four: two poles with four ports |
| `FourPorts.lean` | 304 | `F ≤ 1`; Lemma 6.7; a network of rank one |
| `FourCutNumbering.lean` | 123 | The numbering of four ports and three pairings |
| `FourCutSides.lean` | 209 | The nine numbers of a pole with four ports |
| `FourCut.lean` | 381 | Theorem 6.8 from the gap theorem, the ring case and the arithmetic |
| `CyclicShore.lean` | 45 | Corollary 5.6 for the pole alone, as a statement |
| `CycleBoundMargin.lean` | 71 | The cycle bound for networks with a margin |
| `PathFirstEdge.lean` | 277 | Paths by their first edge; cycles through an edge |
| `ShortestCycle.lean` | 261 | A shortest cycle: exit edges, no chord, no two feet |
| `ExitPole.lean` | 343 | The component of a vertex in a part: pole, ports, rank; shores |
| `ShortCycleExit.lean` | 508 | The setting of Theorem 7.1; the bound for one exit term |
| `ShortCycleCount.lean` | 454 | The recursion along the cycle |
| `ShortCycle.lean` | 363 | Theorem 7.1 from the pole statement |
| `Corollaries.lean` | 83 | The printed forms of the theorem, from the exact maximum |
| `Main.lean` | 103 | **The theorem without hypothesis**, and its forms |
| `CutCaps.lean` | 102 | The caps for two and for three vertices of a network |
| `SmallCutCaps.lean` | 667 | Proposition 6.3 from the caps, without the bound `(9/16) 2^b` |
| `MainCaps.lean` | 105 | **The theorem by the cases of the text** (cap for Theorem 6.8, eight vertices in Case 5) |

Every file names its local `Decidable` instance (`netCutDecidable` and so on). Two files with an
unnamed local instance in the same namespace get the same generated name, and a module that
imports both does not load.

Check: `lake build`, and `lake env lean` on a file with
`#print axioms Erdos1016.ExactMaximum.exactMaximum` or on `audits/ExactMaximumCapsAudit.lean`.
