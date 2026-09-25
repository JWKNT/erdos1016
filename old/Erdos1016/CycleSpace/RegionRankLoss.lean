import Erdos1016.CycleSpace.ForcedRegionCylinder
import Erdos1016.Decomposition.Regions.Cuts

set_option autoImplicit false

/-!
# Actual cubic-support rank loss

Only vertices in the selected region are assumed cubic. Vertices outside it,
including a boundary apex, may have arbitrary degree. Every complement is in
the unchanged owner. This proves the exponents in manuscript (4.3)--(4.4).
-/

noncomputable section
open scoped BigOperators
namespace Erdos1016.BoundaryDecay

open BoundaryTrace Network SafeCore
local instance originalRankLossDecidable (p : Prop) : Decidable p := Classical.propDecidable p

private theorem dyadic_congr {a b : ℤ} (h : a = b) : dyadic a = dyadic b := by
  cases h
  rfl

variable (G : PhysicalGraph)

local instance physicalOutsideVertexFintype (S : Finset G.Vertex) :
    Fintype (Shore.OutsideVertex S) :=
  Shore.outsideVertexFintype G.traceNetwork S

local instance physicalOutsideEdgeFintype (S : Finset G.Vertex) :
    Fintype (Shore.OutsideEdge G.traceNetwork S) :=
  Shore.outsideEdgeFintype G.traceNetwork S

@[simp] theorem rank_traceNetwork : networkRank G.traceNetwork = G.cycleRank := by
  change Module.finrank Bit (LinearMap.ker G.traceNetwork.boundary) =
    Module.finrank Bit (LinearMap.ker G.boundary)
  rw [G.traceNetwork_boundary]

@[simp] theorem inside_vertex_card (S : Finset G.Vertex) :
    Fintype.card (Shore.InsideVertex S) = S.card := by simp

@[simp] theorem inside_edge_card (S : Finset G.Vertex) :
    Fintype.card (Shore.InsideEdge G.traceNetwork S) = (internalEdges G S).card := by
  apply Fintype.card_of_subtype
  intro e
  simp [internalEdges, PhysicalGraph.traceNetwork]

@[simp] theorem cut_edge_card (S : Finset G.Vertex) :
    Fintype.card (Shore.CutEdge G.traceNetwork S) = cutSize G S := by
  unfold cutSize
  apply Fintype.card_of_subtype
  intro e
  simp [PhysicalGraph.traceNetwork]

/-- Includes original isolated vertices outside S. -/
theorem outside_vertex_card_int (S : Finset G.Vertex)
    [Fintype (Shore.OutsideVertex S)] :
    (Fintype.card (Shore.OutsideVertex S) : ℤ) =
      (G.vertexCount : ℤ) - S.card := by
  have h := Fintype.card_congr (Shore.verticesEquiv S)
  simp only [Fintype.card_sum, inside_vertex_card, Fintype.card_fin] at h
  omega

theorem outside_edge_card_int (S : Finset G.Vertex)
    [Fintype (Shore.OutsideVertex S)]
    [Fintype (Shore.OutsideEdge G.traceNetwork S)] :
    (Fintype.card (Shore.OutsideEdge G.traceNetwork S) : ℤ) =
      (G.edgeCount : ℤ) - (internalEdges G S).card - cutSize G S := by
  have h := Fintype.card_congr (Shore.edgesEquiv G.traceNetwork S)
  simp only [Fintype.card_sum, inside_edge_card, cut_edge_card, Fintype.card_fin] at h
  omega

theorem outside_component_card (S : Finset G.Vertex)
    [Fintype (Shore.OutsideVertex S)] :
    Fintype.card (Shore.outside G.traceNetwork S).Component =
      G.originalExteriorComponents S :=
  G.exteriorComponentCount_eq_original S

/-- General original-owner deletion identity, before using cubicity. -/
theorem original_rank_loss (hG : G.IsConnected) (S : Finset G.Vertex)
    [Fintype (Shore.OutsideVertex S)]
    [Fintype (Shore.OutsideEdge G.traceNetwork S)] :
    (networkRank (Shore.outside G.traceNetwork S) : ℤ) - G.cycleRank =
      (S.card : ℤ) - (internalEdges G S).card - cutSize G S +
        G.originalExteriorComponents S - 1 := by
  have hc : G.traceNetwork.graph.Connected := by
    simpa only [G.traceNetwork_graph] using hG
  have hin := connected_network_rank_int G.traceNetwork hc
  have hout := network_rank_int (Shore.outside G.traceNetwork S)
  rw [rank_traceNetwork, Fintype.card_fin, Fintype.card_fin] at hin
  rw [outside_vertex_card_int, outside_edge_card_int, outside_component_card] at hout
  omega

/-- All and only region vertices need degree three. The apex is not included. -/
theorem cubic_original_rank_loss (hG : G.IsConnected) (S : Finset G.Vertex)
    [Fintype (Shore.OutsideVertex S)]
    [Fintype (Shore.OutsideEdge G.traceNetwork S)]
    (hc : ∀ v ∈ S, G.degree v = 3) :
    (networkRank (Shore.outside G.traceNetwork S) : ℤ) - G.cycleRank =
      (internalEdges G S).card - 2 * (S.card : ℤ) +
        G.originalExteriorComponents S - 1 := by
  rw [original_rank_loss G hG]
  have hd := cubic_cut_identity G S hc
  omega

/-- Same homogeneous event law, expressed with the existing PhysicalGraph type. -/
def forcedProbability (S : Finset G.Vertex) (z : G.CycleSpace) : ℝ :=
  Finite.density (fun x : G.CycleSpace => ForcedRegion G.traceNetwork S z.1 x.1)

theorem forcedProbability_eq_network (S : Finset G.Vertex) (z : G.CycleSpace) :
    forcedProbability G S z =
      Finite.density (fun x : G.traceNetwork.CycleSpace =>
        ForcedRegion G.traceNetwork S (G.traceCycleEquiv z).1 x.1) := by
  apply Finite.density_equiv G.traceCycleEquiv
  intro x
  rfl

/-- The finite component-event formula with the ACTUAL induced-edge count. -/
theorem cubic_forcedProbability (hG : G.IsConnected) (S : Finset G.Vertex)
    (hc : ∀ v ∈ S, G.degree v = 3) (z : G.CycleSpace) :
    forcedProbability G S z = dyadic
      ((internalEdges G S).card - 2 * (S.card : ℤ) +
        G.originalExteriorComponents S - 1) := by
  letI : Fintype (Shore.OutsideVertex S) := physicalOutsideVertexFintype G S
  letI : Fintype (Shore.OutsideEdge G.traceNetwork S) := physicalOutsideEdgeFintype G S
  rw [forcedProbability_eq_network, forced_region_probability_dyadic]
  rw [rank_traceNetwork]
  apply dyadic_congr
  exact cubic_original_rank_loss G hG S hc

/-- No simple-cycle hypothesis is needed for this exact edge-union count. -/
theorem internalEdges_union_card (S T : Finset G.Vertex) (hST : Disjoint S T) :
    (internalEdges G (S ∪ T)).card =
      (internalEdges G S).card + (internalEdges G T).card + crossSize G S T := by
  have hd (v : G.Vertex) : ¬ (v ∈ S ∧ v ∈ T) := fun h =>
    Finset.disjoint_left.1 hST h.1 h.2
  have hp (e : G.Edge) :
      (if G.src e ∈ S ∪ T ∧ G.dst e ∈ S ∪ T then (1 : ℕ) else 0) =
        (if G.src e ∈ S ∧ G.dst e ∈ S then 1 else 0) +
        (if G.src e ∈ T ∧ G.dst e ∈ T then 1 else 0) +
        (if (G.src e ∈ S ∧ G.dst e ∈ T) ∨
          (G.src e ∈ T ∧ G.dst e ∈ S) then 1 else 0) := by
    simp only [Finset.mem_union]
    by_cases hs : G.src e ∈ S <;> by_cases ht : G.src e ∈ T <;>
      by_cases ds : G.dst e ∈ S <;> by_cases dt : G.dst e ∈ T <;>
      simp_all [hd]
  have h := congrArg (fun f : G.Edge → ℕ => ∑ e, f e) (funext hp)
  simpa only [internalEdges, crossSize, crossing, Finset.card_eq_sum_ones,
    Finset.sum_filter, Finset.sum_add_distrib] using h

theorem originalExteriorComponents_pos (S : Finset G.Vertex)
    (v₀ : G.Vertex) (hv₀ : v₀ ∉ S) :
    0 < G.originalExteriorComponents S := by
  let O := Shore.outside G.traceNetwork S
  haveI : Nonempty O.Component := ⟨O.component ⟨v₀, hv₀⟩⟩
  rw [← outside_component_card G S]
  exact Fintype.card_pos

end Erdos1016.BoundaryDecay
