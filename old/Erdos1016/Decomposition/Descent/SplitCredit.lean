import Erdos1016.Decomposition.Descent.ExteriorMerge

set_option autoImplicit false

/-!
# Graph-specific local signed-credit inequality

The abstract signed-credit induction assumes a local inequality at a fork.
For a split of a connected region, this module proves the both-children
inequality from the exact original-exterior update and the fact that every
old exterior component contacts the parent region.
-/

noncomputable section
namespace Erdos1016.Proof.SignedCredit
open Erdos1016.SafeCore

variable (G : PhysicalGraph)

/-- Every component of the old exterior contacts at least one child. -/
theorem oldExterior_subset_childContacts (hG : G.IsConnected)
    {J : Finset G.Vertex} (s : BondSplit G J) :
    components G Jᶜ ⊆
      touchingComponents G J s.left ∪ touchingComponents G J s.right := by
  intro C hC
  have hJ : J.Nonempty := s.left_connected.1.mono s.left_subset
  obtain ⟨u, hu, v, hv, huv⟩ :=
    (crossing_nonempty_iff G C J).1 (component_touches_removed G hG hJ hC)
  rw [← s.union_eq] at hv
  rcases Finset.mem_union.1 hv with hvL | hvR
  · exact Finset.mem_union_left _ ((mem_touchingComponents G J s.left C).2
      ⟨hC, (crossing_nonempty_iff G C s.left).2 ⟨u, hu, v, hvL, huv⟩⟩)
  · exact Finset.mem_union_right _ ((mem_touchingComponents G J s.right C).2
      ⟨hC, (crossing_nonempty_iff G C s.right).2 ⟨u, hu, v, hvR, huv⟩⟩)

/-- The total number of child contacts covers all old exterior components. -/
theorem oldExteriorCount_le_childContacts (hG : G.IsConnected)
    {J : Finset G.Vertex} (s : BondSplit G J) :
    (components G Jᶜ).card ≤
      (touchingComponents G J s.left).card +
        (touchingComponents G J s.right).card := by
  have hsub := oldExterior_subset_childContacts G hG s
  have hcard := Finset.card_le_card hsub
  have hsum := Finset.card_union_le
      (touchingComponents G J s.left) (touchingComponents G J s.right)
  omega







end Erdos1016.Proof.SignedCredit
end
