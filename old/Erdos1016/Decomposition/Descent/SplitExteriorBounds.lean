import Erdos1016.Decomposition.Descent.DecompositionCredit

set_option autoImplicit false

/-!
# Graph-specific §9 split facts

This module connects a connected physical graph's binary connected-shore split
with the exterior-count facts used by the finite §9 tree argument. The
no-contact case is recorded separately: the omitted no-contact child is
negative-potential, while its sibling's exterior count can increase by one.
-/

noncomputable section
namespace Erdos1016.Proof.SplitExteriorBounds

open Erdos1016.SafeCore
open Erdos1016.Proof.SignedCredit
open Erdos1016.Proof.GraphDecompositionCredit

variable (G : PhysicalGraph)

/-- For a connected ambient graph, the sum of the two child exterior counts
is at most the parent's exterior count plus two. The proof counts old exterior
components by their contacts with the shores, then uses the exact split
component updates. -/
theorem child_exterior_count_sum_le (hG : G.IsConnected)
    {J : Finset G.Vertex} (s : BondSplit G J) :
    G.originalExteriorComponents s.left + G.originalExteriorComponents s.right ≤
      G.originalExteriorComponents J + 2 := by
  have hleft := originalExteriorComponents_split_add G s
  have hright0 := originalExteriorComponents_split_add G s.symm
  have hright :
      G.originalExteriorComponents s.right +
          (touchingComponents G J s.left).card =
        G.originalExteriorComponents J + 1 := by
    simpa only [BondSplit.symm] using hright0
  have hold := oldExteriorCount_le_childContacts G hG s
  have hcontacts : G.originalExteriorComponents J ≤
      (touchingComponents G J s.left).card +
        (touchingComponents G J s.right).card := by
    simpa only [← exteriorCount_eq_original] using hold
  omega

/-- If the omitted right shore contacts the old exterior, retaining the left
shore cannot increase the exterior-component count. -/
theorem retained_left_exterior_le_of_right_contact
    {J : Finset G.Vertex} (s : BondSplit G J)
    (hcontact : (touchingComponents G J s.right).Nonempty) :
    G.originalExteriorComponents s.left ≤ G.originalExteriorComponents J := by
  have h := exteriorCount_left_le_of_touch G s hcontact
  simpa only [← exteriorCount_eq_original] using h

/-- Symmetric retained-child monotonicity under contact of the omitted left
shore with the old exterior. -/
theorem retained_right_exterior_le_of_left_contact
    {J : Finset G.Vertex} (s : BondSplit G J)
    (hcontact : (touchingComponents G J s.left).Nonempty) :
    G.originalExteriorComponents s.right ≤ G.originalExteriorComponents J := by
  have h := exteriorCount_left_le_of_touch G s.symm hcontact
  simpa only [BondSplit.symm, ← exteriorCount_eq_original] using h

/-- If a child is omitted because it has no negative-potential leaf, the
split hypotheses force it to contact the old exterior. Otherwise the
no-contact sibling lemma would make that child itself negative-potential.
This is the orientation needed to derive retained-child monotonicity in §9. -/
theorem right_contact_of_left_negative_and_right_nonnegative
    (P : CutParameters) (hG : G.IsConnected)
    {J : Finset G.Vertex} {s : BondSplit G J}
    (hcheap : Cheap G P s)
    (hRightNonnegative : 0 ≤ potential G P s.right) :
    (touchingComponents G J s.right).Nonempty := by
  by_contra hcontact
  have hnoContact : touchingComponents G J s.right = ∅ :=
    Finset.not_nonempty_iff_eq_empty.mp hcontact
  have hneg := no_contact_sibling_potential_neg G P hG hcheap hnoContact
  linarith

/-- The tree form used during pruning: if the omitted right subtree has no
negative-potential leaves, its root potential is nonnegative by the leaf
potential ledger, hence that shore must contact the old exterior. -/
theorem right_contact_of_no_negative_leaf_subtree
    (P : CutParameters) (hG : G.IsConnected)
    {J : Finset G.Vertex} {s : BondSplit G J}
    (hcheap : Cheap G P s)
    (rightTree : Decomposition G P s.right)
    (hRightLeaves : ∀ L ∈ rightTree.leaves, 0 ≤ potential G P L) :
    (touchingComponents G J s.right).Nonempty := by
  have hsum : 0 ≤ ∑ L ∈ rightTree.leaves, potential G P L := by
    apply Finset.sum_nonneg
    intro L hL
    exact hRightLeaves L hL
  have hroot : 0 ≤ potential G P s.right := le_trans hsum rightTree.potential_sum_le
  exact right_contact_of_left_negative_and_right_nonnegative G P hG hcheap hroot





/-- The tree-pruning form: a retained left subtree contains a negative leaf,
while the omitted right subtree contains none, so the right shore contacts
the old exterior and the retained exterior count does not grow. -/
theorem retained_left_exterior_le_of_leaf_subtrees
    (P : CutParameters) (hG : G.IsConnected)
    {J : Finset G.Vertex} {s : BondSplit G J}
    (hcheap : Cheap G P s)
    (leftTree : Decomposition G P s.left)
    (_hLeftNegative : ∃ L ∈ leftTree.leaves, potential G P L < 0)
    (rightTree : Decomposition G P s.right)
    (hRightNonnegative : ∀ L ∈ rightTree.leaves, 0 ≤ potential G P L) :
    G.originalExteriorComponents s.left ≤ G.originalExteriorComponents J := by
  exact retained_left_exterior_le_of_right_contact G s
    (right_contact_of_no_negative_leaf_subtree G P hG hcheap rightTree
      hRightNonnegative)



/-- Symmetric tree-pruning form. -/
theorem retained_right_exterior_le_of_leaf_subtrees
    (P : CutParameters) (hG : G.IsConnected)
    {J : Finset G.Vertex} {s : BondSplit G J}
    (hcheap : Cheap G P s)
    (rightTree : Decomposition G P s.right)
    (_hRightNegative : ∃ L ∈ rightTree.leaves, potential G P L < 0)
    (leftTree : Decomposition G P s.left)
    (hLeftNonnegative : ∀ L ∈ leftTree.leaves, 0 ≤ potential G P L) :
    G.originalExteriorComponents s.right ≤ G.originalExteriorComponents J := by
  have hcheap' : Cheap G P s.symm := cheap_symm G P hcheap
  have hcontact := right_contact_of_no_negative_leaf_subtree G P hG hcheap'
    (rightTree := leftTree) hLeftNonnegative
  exact retained_right_exterior_le_of_left_contact G s
    (by simpa only [BondSplit.symm] using hcontact)



end Erdos1016.Proof.SplitExteriorBounds
end
