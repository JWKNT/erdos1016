import Erdos1016.Graph.Basic
import Erdos1016.Boundary.Shore

set_option autoImplicit false

/-!
# Adapter to the existing `Erdos1016.PhysicalGraph`

The main theorem at the end has the ORIGINAL owner graph, its original edge
labels, and its original exterior component count in its statement. The
boundary-average term is the complete one-apex law, whose sector-average
normalization was proved in `BoundaryAverage.lean`.

This module adds declarations only. It does not overwrite the prior final
assembly or silently construct any of the other untranslated deep inputs.
-/

noncomputable section

namespace Erdos1016.PhysicalGraph

open BoundaryTrace
open scoped BigOperators

local instance (p : Prop) : Decidable p := Classical.propDecidable p

def traceNetwork (G : PhysicalGraph) : BoundaryTrace.Network G.Vertex G.Edge where
  src := G.src
  dst := G.dst
  noLoops := G.noLoops

@[simp] theorem traceNetwork_boundary (G : PhysicalGraph) :
    G.traceNetwork.boundary = G.boundary := by
  apply LinearMap.ext
  intro x
  funext v
  simp only [BoundaryTrace.Network.boundary_apply, PhysicalGraph.boundary,
    traceNetwork]
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro e _
  by_cases hs : G.src e = v <;> by_cases ht : G.dst e = v <;> simp [hs, ht]

@[simp] theorem traceNetwork_graph (G : PhysicalGraph) :
    G.traceNetwork.graph = G.toSimpleGraph := by
  ext u v
  constructor
  · rintro ⟨e, h⟩
    exact ⟨e, one_ne_zero, h⟩
  · rintro ⟨e, _, h⟩
    exact ⟨e, h⟩

def traceCycleEquiv (G : PhysicalGraph) : G.CycleSpace ≃ G.traceNetwork.CycleSpace where
  toFun x := ⟨x.1, by
    change G.traceNetwork.boundary x.1 = 0
    rw [G.traceNetwork_boundary]
    exact x.2⟩
  invFun x := ⟨x.1, by
    change G.boundary x.1 = 0
    rw [← G.traceNetwork_boundary]
    exact x.2⟩
  left_inv x := rfl
  right_inv x := rfl

/-- Equality of the actual induced selected graphs, including isolated
vertices on the shore. -/
theorem trace_inside_selectedGraph (G : PhysicalGraph) (S : Finset G.Vertex)
    (x : G.Word) :
    (Network.Shore.inside G.traceNetwork S).selectedGraph
        (Network.Shore.restrictInside G.traceNetwork S x) =
      (G.selectedGraph x).induce (↑S : Set G.Vertex) := by
  ext u v
  constructor
  · rintro ⟨e, hx, h | h⟩
    · exact ⟨e.1, hx, Or.inl ⟨congrArg Subtype.val h.1, congrArg Subtype.val h.2⟩⟩
    · exact ⟨e.1, hx, Or.inr ⟨congrArg Subtype.val h.1, congrArg Subtype.val h.2⟩⟩
  · rintro ⟨e, hx, h | h⟩
    · rcases h with ⟨hs, ht⟩
      change G.src e = u.1 at hs
      change G.dst e = v.1 at ht
      have hs' : G.traceNetwork.src e = u.1 := hs
      have ht' : G.traceNetwork.dst e = v.1 := ht
      refine ⟨⟨e, hs'.symm ▸ u.2, ht'.symm ▸ v.2⟩, hx, Or.inl ?_⟩
      exact ⟨Subtype.ext hs, Subtype.ext ht⟩
    · rcases h with ⟨hs, ht⟩
      change G.src e = v.1 at hs
      change G.dst e = u.1 at ht
      have hs' : G.traceNetwork.src e = v.1 := hs
      have ht' : G.traceNetwork.dst e = u.1 := ht
      refine ⟨⟨e, hs'.symm ▸ v.2, ht'.symm ▸ u.2⟩, hx, Or.inr ?_⟩
      exact ⟨Subtype.ext hs, Subtype.ext ht⟩

/-- The component count is taken in the full ORIGINAL complement H-S. -/
def originalExteriorComponents (G : PhysicalGraph) (S : Finset G.Vertex) : ℕ :=
  Nat.card (G.toSimpleGraph.induce {v | v ∉ S}).ConnectedComponent

theorem exteriorComponentCount_eq_original (G : PhysicalGraph)
    (S : Finset G.Vertex) :
    Network.Shore.exteriorComponentCount G.traceNetwork S =
      G.originalExteriorComponents S := by
  unfold Network.Shore.exteriorComponentCount originalExteriorComponents
  rw [← Nat.card_eq_fintype_card]
  change Nat.card ((Network.Shore.outside G.traceNetwork S).graph).ConnectedComponent = _
  rw [Network.Shore.outside_graph_eq_induce, G.traceNetwork_graph]

/-- Probability of forest restriction under the entire owner cycle space. -/
def originalForestFraction (G : PhysicalGraph) (S : Finset G.Vertex) : ℝ :=
  Finite.density (fun x : G.CycleSpace =>
    ((G.selectedGraph x.1).induce (↑S : Set G.Vertex)).IsAcyclic)

/-- Uniform even words in the one-apex completion, tested only for internal
foresthood. Never condition on a favorable boundary word or successful family. -/
def oneApexForestFraction (G : PhysicalGraph) (S : Finset G.Vertex) : ℝ :=
  Network.Shore.boundaryAverage G.traceNetwork S
    (Network.Shore.inside G.traceNetwork S).IsForest

theorem originalForestFraction_eq_network (G : PhysicalGraph)
    (S : Finset G.Vertex) :
    G.originalForestFraction S =
      Network.Shore.originalFraction G.traceNetwork S
        (Network.Shore.inside G.traceNetwork S).IsForest := by
  unfold originalForestFraction Network.Shore.originalFraction
  apply Finite.density_equiv G.traceCycleEquiv
  intro x
  change ((G.selectedGraph x.1).induce (↑S : Set G.Vertex)).IsAcyclic ↔ _
  rw [← G.trace_inside_selectedGraph S x.1]
  rfl

/-- The formerly untranslated ORIGINAL-EXTERIOR TRACE BOUND, in concrete
owner-and-shore form. Every ingredient of this theorem is proved in this
patch; the only hypotheses are an actual graph and an actual exterior vertex.

The forest average is the one-apex average, not an arbitrary local model.
For connected min-2/max-3 shores, `apexFraction_eq_normalized_even_average`
identifies it with the manuscript's complete even-boundary average. -/
theorem originalExteriorTraceBound (G : PhysicalGraph)
    (S : Finset G.Vertex) (v₀ : G.Vertex) (hv₀ : v₀ ∉ S) :
    G.originalForestFraction S ≤
      (2 : ℝ) ^ (G.originalExteriorComponents S - 1) * G.oneApexForestFraction S := by
  rw [G.originalForestFraction_eq_network,
    ← G.exteriorComponentCount_eq_original]
  exact Network.Shore.original_forest_fraction_le G.traceNetwork S ⟨v₀, hv₀⟩



end Erdos1016.PhysicalGraph
