import Erdos1016.Probability.Conditional.IsolatedCycleLaw

set_option autoImplicit false
noncomputable section
namespace Erdos1016.Proof.CycleProximity
open BoundaryDecay SafeCore

local instance (p : Prop) : Decidable p := Classical.propDecidable p

/-- Proximity in the ordinary induced region, including zero-length paths
and without imposing connectivity of the region. -/
def Near (G : PhysicalGraph) (J : Finset G.Vertex) (q : ℕ)
    (C D : G.CycleWord) : Prop :=
  ∃ (u v : J), u.1 ∈ Cycle.vertices C ∧ v.1 ∈ Cycle.vertices D ∧
    ∃ p : (G.toSimpleGraph.induce (↑J : Set G.Vertex)).Walk u v, p.length ≤ q



theorem near_of_overlap {G : PhysicalGraph} (J : Finset G.Vertex) (q : ℕ)
    (C D : G.CycleWord) (hCJ : Cycle.vertices C ⊆ J)
    (hoverlap : ¬ Disjoint (Cycle.vertices C) (Cycle.vertices D)) : Near G J q C D := by
  obtain ⟨v, hvC, hvD⟩ := Finset.not_disjoint_iff.mp hoverlap
  exact ⟨⟨v, hCJ hvC⟩, ⟨v, hCJ hvC⟩, hvC, hvD, .nil, Nat.zero_le q⟩

theorem near_self {G : PhysicalGraph} (J : Finset G.Vertex) (q : ℕ)
    (C : G.CycleWord) (hCJ : Cycle.vertices C ⊆ J) : Near G J q C C := by
  apply near_of_overlap J q C C hCJ
  intro h
  have hnonempty := BoundaryDecay.usedVertices_nonempty_of_ne_zero C.1 C.2.1
  obtain ⟨v, hv⟩ := hnonempty
  exact Finset.disjoint_left.mp h hv hv

def eligible (G : PhysicalGraph) (A F : Finset G.CycleWord) : Finset G.CycleWord :=
  A.filter (fun D => Disjoint (CycleExtensionProbability.tupleVertices F)
    (Cycle.vertices D))

end Erdos1016.Proof.CycleProximity
end
