import Erdos1016.Decomposition.Descent.PotentialDescent

set_option autoImplicit false

/-! # Finite actual bond-cut decompositions and their potential ledger -/
noncomputable section
open scoped BigOperators
namespace Erdos1016.SafeCore
local instance instSafeCoreDecompositionPropDecidable (p : Prop) : Decidable p := Classical.propDecidable p

inductive Decomposition (G : PhysicalGraph) (P : CutParameters) : Finset G.Vertex → Type
  | leaf (U : Finset G.Vertex) (conn : ConnectedRegion G U)
      (expanded : Expanded G P U) : Decomposition G P U
  | node {U : Finset G.Vertex} (conn : ConnectedRegion G U)
      (split : BondSplit G U) (cheap : Cheap G P split)
      (left : Decomposition G P split.left)
      (right : Decomposition G P split.right) : Decomposition G P U

namespace Decomposition
variable {G : PhysicalGraph} {P : CutParameters}

def leaves {U : Finset G.Vertex} : Decomposition G P U → Finset (Finset G.Vertex)
  | .leaf U _ _ => {U}
  | .node _ _ _ l r => l.leaves ∪ r.leaves



theorem leaf_subset {U : Finset G.Vertex} (t : Decomposition G P U) :
    ∀ L ∈ t.leaves, L ⊆ U := by
  induction t with
  | leaf U hc he =>
      intro L hL
      have heq : L = U := by simpa only [leaves, Finset.mem_singleton] using hL
      subst L
      exact Finset.Subset.refl _
  | node hc s hs l r ihl ihr =>
      intro L hL
      rcases Finset.mem_union.1 hL with hL | hL
      · exact (ihl L hL).trans s.left_subset
      · exact (ihr L hL).trans s.right_subset

theorem leaf_connected {U : Finset G.Vertex} (t : Decomposition G P U) :
    ∀ L ∈ t.leaves, ConnectedRegion G L := by
  induction t with
  | leaf U hc he =>
      intro L hL
      have heq : L = U := by simpa only [leaves, Finset.mem_singleton] using hL
      simpa only [heq] using hc
  | node hc s hs l r ihl ihr =>
      intro L hL
      rcases Finset.mem_union.1 hL with hL | hL
      · exact ihl L hL
      · exact ihr L hL

theorem leaf_expanded {U : Finset G.Vertex} (t : Decomposition G P U) :
    ∀ L ∈ t.leaves, Expanded G P L := by
  induction t with
  | leaf U hc he =>
      intro L hL
      have heq : L = U := by simpa only [leaves, Finset.mem_singleton] using hL
      simpa only [heq] using he
  | node hc s hs l r ihl ihr =>
      intro L hL
      rcases Finset.mem_union.1 hL with hL | hL
      · exact ihl L hL
      · exact ihr L hL

theorem separated_leaf_families {U : Finset G.Vertex} (s : BondSplit G U)
    (l : Decomposition G P s.left) (r : Decomposition G P s.right) :
    Disjoint l.leaves r.leaves := by
  apply Finset.disjoint_left.2
  intro A hA hB
  obtain ⟨v, hv⟩ := (l.leaf_connected A hA).1
  exact Finset.disjoint_left.1 s.disjoint (l.leaf_subset A hA hv) (r.leaf_subset A hB hv)

theorem leaves_pairwise {U : Finset G.Vertex} (t : Decomposition G P U) :
    Set.Pairwise (↑t.leaves : Set (Finset G.Vertex)) Disjoint := by
  induction t with
  | leaf U hc he => simp [leaves]
  | node hc s hs l r ihl ihr =>
      intro A hA B hB hne
      rcases Finset.mem_union.1 hA with hA | hA <;>
        rcases Finset.mem_union.1 hB with hB | hB
      · exact ihl hA hB hne
      · exact Finset.disjoint_left.2 fun v hvA hvB =>
          Finset.disjoint_left.1 s.disjoint (l.leaf_subset A hA hvA) (r.leaf_subset B hB hvB)
      · exact Finset.disjoint_left.2 fun v hvA hvB =>
          Finset.disjoint_left.1 s.disjoint (l.leaf_subset B hB hvB) (r.leaf_subset A hA hvA)
      · exact ihr hA hB hne



/-- No repeated vertex bag and no duplicate potential term is hidden here. -/
theorem potential_sum_le {U : Finset G.Vertex} (t : Decomposition G P U) :
    ∑ L ∈ t.leaves, potential G P L ≤ potential G P U := by
  induction t with
  | leaf U hc he => simp [leaves]
  | node hc s hs l r ihl ihr =>
      change (∑ L ∈ l.leaves ∪ r.leaves, potential G P L) ≤ _
      rw [Finset.sum_union (separated_leaf_families s l r)]
      exact (add_le_add ihl ihr).trans (potential_split_le G P hs)

end Decomposition

/-- Build the complete finite decomposition using only actual connected cuts. -/
theorem exists_decomposition (G : PhysicalGraph) (P : CutParameters)
    {H : Finset G.Vertex} (hH : ConnectedRegion G H) : Nonempty (Decomposition G P H) := by
  have aux : ∀ n : ℕ, ∀ U : Finset G.Vertex, U.card = n →
      ConnectedRegion G U → Nonempty (Decomposition G P U) := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro U hcard hU
      by_cases he : Expanded G P U
      · exact ⟨.leaf U hU he⟩
      · obtain ⟨s, hs⟩ := exists_cheap_bond G P hU he
        obtain ⟨l⟩ := ih s.left.card (hcard ▸ s.left_card_lt) s.left rfl s.left_connected
        obtain ⟨r⟩ := ih s.right.card (hcard ▸ s.right_card_lt) s.right rfl s.right_connected
        exact ⟨.node hU s hs l r⟩
  exact aux H.card H rfl hH

end Erdos1016.SafeCore
