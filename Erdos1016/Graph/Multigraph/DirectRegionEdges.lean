import Erdos1016.Graph.Multigraph.Forest

set_option autoImplicit false
noncomputable section
namespace Erdos1016.FiniteMultiGraph
local instance directRegionEdgesDecidable (p : Prop) : Decidable p := Classical.propDecidable p

/-- The original physical labels joining two vertex regions, counted once
regardless of their stored orientation. -/
def directLabels (G : FiniteMultiGraph) (A B : Finset G.Vertex) : Finset G.Edge :=
  Finset.univ.filter (fun e => (G.src e ∈ A ∧ G.dst e ∈ B) ∨
    (G.src e ∈ B ∧ G.dst e ∈ A))

@[simp] theorem mem_directLabels (G : FiniteMultiGraph) (A B : Finset G.Vertex)
    (e : G.Edge) : e ∈ G.directLabels A B ↔
      (G.src e ∈ A ∧ G.dst e ∈ B) ∨ (G.src e ∈ B ∧ G.dst e ∈ A) := by
  simp [directLabels]

theorem directLabels_internal (G : FiniteMultiGraph) (A B R : Finset G.Vertex)
    (hA : A ⊆ R) (hB : B ⊆ R) : G.directLabels A B ⊆ G.internalEdges R := by
  intro e he
  have h := (G.mem_directLabels A B e).mp he
  apply Finset.mem_filter.mpr
  refine ⟨Finset.mem_univ _, ?_⟩
  exact h.elim (fun h => ⟨hA h.1, hB h.2⟩) (fun h => ⟨hB h.1, hA h.2⟩)

end Erdos1016.FiniteMultiGraph
