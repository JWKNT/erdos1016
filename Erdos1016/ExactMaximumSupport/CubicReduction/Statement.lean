import Erdos1016.ExactMaximumSupport.CubicReduction.CubicCore
import Erdos1016.ExactMaximumSupport.CubicReduction.IncidenceCycles
import Erdos1016.ExactMaximumSupport.CubicReduction.CorridorCycles
import Erdos1016.ExactMaximum.Cases

set_option autoImplicit false

/-!
# Reduction to a connected cubic multigraph

Connect the input by bridges, expand each incidence row to a path, prune
the full two-core, and suppress its degree-two corridors. Each step preserves
rank and has an explicit injection on individual cycles.
-/

noncomputable section

namespace Erdos1016.ExactMaximumSupport.CubicReduction

open ShortProof ShortProof.CycleCore PhysicalGraph

theorem core_nonempty_of_rank_pos (G : PhysicalGraph) (hr : 0 < G.cycleRank) :
    (core G).Nonempty := by
  obtain ⟨x, hx⟩ : ∃ x : G.CycleSpace, x ≠ 0 :=
    Module.finrank_pos_iff_exists_ne_zero.mp hr
  have hx0 : x.1 ≠ 0 := fun h => hx (Subtype.ext h)
  obtain ⟨e, he⟩ := Function.ne_iff.mp hx0
  exact ⟨G.src e, (nonzero_edge_in_core G x e he).1⟩

theorem exists_cubic_with_cycleCount (G : PhysicalGraph) (hconn : G.IsConnected)
    (hmin : ∀ v, 2 ≤ G.degree v) (hmax : ∀ v, G.degree v ≤ 3)
    (hr : 2 ≤ G.cycleRank) :
    ∃ M : FiniteMultiGraph, M.toSimpleGraph.Connected ∧ M.IsCubic ∧
      M.cycleRank = G.cycleRank ∧ Fintype.card G.CycleWord ≤ M.numCycles := by
  classical
  let P := cubicVertices G
  have hP : P.Nonempty := cubicVertices_nonempty G hconn hmin hmax hr
  have hd (v : G.Vertex) (_hv : v ∉ P) : G.degree v = 2 ∨ G.degree v = 3 := by
    have hlo := hmin v
    have hhi := hmax v
    omega
  let M := MarkedCorridors.graph G P hconn hP hd
  refine ⟨M, MarkedCorridors.connected G P hconn hP hd, ?_,
    MarkedCorridors.cycleRank_preserved G P hconn hP hd,
    cycleCount_le_corridor G P hconn hP hd hmax⟩
  intro v
  rw [MarkedCorridors.degree_preserved]
  have hv := MarkedCorridors.vertexMap_retained G P hconn hP hd v
  simpa only [Proof.PhysicalDegreeTwoCoreComponents.protectedOrBranch, P, cubicVertices,
    Finset.union_self, Finset.mem_filter, Finset.mem_univ, true_and] using hv

theorem physical_cubic_reduction (G : PhysicalGraph) (hr : 2 ≤ G.cycleRank) :
    ∃ M : FiniteMultiGraph, M.toSimpleGraph.Connected ∧ M.IsCubic ∧
      M.cycleRank = G.cycleRank ∧ Fintype.card G.CycleWord ≤ M.numCycles := by
  let H := connectByHub G
  have hH : H.IsConnected := connectByHub_connected G
  have hHr : H.cycleRank = G.cycleRank := cycleRank_connectByHub G
  let I := IncidencePaths.physical H ∅
  have hI : I.IsConnected := IncidencePaths.physical_connected H ∅ hH
  have hIr : I.cycleRank = G.cycleRank :=
    (IncidencePaths.physical_cycleRank H ∅).trans hHr
  have hImax : ∀ v, I.degree v ≤ 3 := IncidencePaths.physical_degree_le_three H ∅
  let K := corePhysical I
  have hcore : (core I).Nonempty := core_nonempty_of_rank_pos I (by rw [hIr]; omega)
  have hK : K.IsConnected := ShortProof.CycleCore.physical_connected I hI hcore
  have hKr : K.cycleRank = G.cycleRank :=
    (ShortProof.CycleCore.cycleRank_preserved I).trans hIr
  have hKmin : ∀ v, 2 ≤ K.degree v :=
    Nonbacktracking.FiniteTwoCore.maximalPhysicalCore_minDegree I
  have hKmax : ∀ v, K.degree v ≤ 3 :=
    Nonbacktracking.FiniteTwoCore.maximalPhysicalCore_degree_le_three I hImax
  obtain ⟨M, hMc, hMd, hMr, hcount⟩ :=
    exists_cubic_with_cycleCount K hK hKmin hKmax (by rw [hKr]; exact hr)
  refine ⟨M, hMc, hMd, hMr.trans hKr, ?_⟩
  calc
    Fintype.card G.CycleWord ≤ Fintype.card H.CycleWord :=
      CycleCount.cycleCount_le_connectByHub G
    _ ≤ Fintype.card I.CycleWord := cycleCount_le_incidence H ∅
    _ ≤ Fintype.card K.CycleWord := cycleCount_le_core I
    _ ≤ M.numCycles := hcount

/-- The exact A3 proposition from the case-reduction file, without hypotheses. -/
theorem cubicReductionStatement : ExactMaximum.CubicReductionStatement := by
  intro n G r hr htwo
  let P := Problem1016.physicalOfSimpleGraph G
  have hPr : P.cycleRank = r := by
    have heuler := CycleCount.physical_euler G
    change P.cycleRank + n = _ at heuler
    omega
  obtain ⟨M, hc, hd, hrank, hcount⟩ :=
    physical_cubic_reduction P (by rw [hPr]; exact htwo)
  refine ⟨M, hc, hd, hrank.trans hPr, ?_⟩
  exact (CycleCount.numCycles_le_cycleCount G).trans hcount

end Erdos1016.ExactMaximumSupport.CubicReduction
