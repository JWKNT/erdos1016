import Erdos1016.Graph.Multigraph.RegionDegrees

set_option autoImplicit false
noncomputable section
namespace Erdos1016.FiniteMultiGraph

local instance regionBoundaryDecidable (p : Prop) : Decidable p := Classical.propDecidable p

theorem cut_union_subset (G : FiniteMultiGraph) (A B : Finset G.Vertex) :
    G.cutEdges (A ∪ B) ⊆ G.cutEdges A ∪ G.cutEdges B := by
  intro e he
  simp only [cutEdges, Finset.mem_filter, Finset.mem_univ, true_and,
    Finset.mem_union] at he ⊢
  tauto

theorem cut_union_card_le (G : FiniteMultiGraph) (A B : Finset G.Vertex) :
    (G.cutEdges (A ∪ B)).card ≤ (G.cutEdges A).card + (G.cutEdges B).card :=
  (Finset.card_le_card (G.cut_union_subset A B)).trans (Finset.card_union_le _ _)

/-- The boundary of two two-regular regions costs at most their total size.
This includes chords and does not require the cycles to be induced. -/
theorem cut_two_regular_union_card_le (G : FiniteMultiGraph) (A B : Finset G.Vertex)
    (a b : G.EdgeWord)
    (ha : ∀ v ∈ A, G.selectedDegree a v = 2)
    (hb : ∀ v ∈ B, G.selectedDegree b v = 2)
    (hasupport : ∀ e, e ∉ G.internalEdges A → a e = 0)
    (hbsupport : ∀ e, e ∉ G.internalEdges B → b e = 0)
    (hmax : ∀ v, G.degree v ≤ 3) :
    (G.cutEdges (A ∪ B)).card ≤ A.card + B.card :=
  (G.cut_union_card_le A B).trans (Nat.add_le_add
    (G.cutEdges_card_le_of_two_regular A a ha hasupport (fun v _ => hmax v))
    (G.cutEdges_card_le_of_two_regular B b hb hbsupport (fun v _ => hmax v)))

end Erdos1016.FiniteMultiGraph
