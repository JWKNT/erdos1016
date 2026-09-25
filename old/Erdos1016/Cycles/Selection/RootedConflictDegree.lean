import Erdos1016.Decomposition.Regions.ConnectedSeparators
import Erdos1016.Cycles.Geometry.NonconflictingComplements

set_option autoImplicit false

/-!
# Polynomial conflict degree from connected-separator nesting

Manuscript Lemma 4.2. The finite rooted geometry recorded below is constructed
from expansion and a protector in ProtectedCycles. No conflict-degree bound
or pairwise-independence hypothesis is part of this structure.
-/

noncomputable section
open scoped BigOperators
namespace Erdos1016.CycleSupply
open SafeCore BoundaryDecay
local instance cycleSupplyConflictDegreeDecidable (p : Prop) : Decidable p := Classical.propDecidable p

/-- Actual disjoint connected supports and the complete off-root budgets. -/
structure RootedFamily (G : PhysicalGraph) (ι : Type*) [DecidableEq ι] where
  family : Finset ι
  region : ι → Finset G.Vertex
  root : G.Vertex
  cutBound : ℕ
  singleBudget : ℕ
  jointBudget : ℕ
  connected : ∀ i ∈ family, ConnectedRegion G (region i)
  disjoint : ∀ i ∈ family, ∀ j ∈ family, i ≠ j → Disjoint (region i) (region j)
  root_avoids : ∀ i ∈ family, root ∉ region i
  cut_le : ∀ i ∈ family, cutSize G (region i) ≤ cutBound
  single_le : ∀ i ∈ family,
    (offRootVertices G (region i)ᶜ root).card ≤ singleBudget
  joint_le : ∀ i ∈ family, ∀ j ∈ family, i ≠ j →
    (offRootVertices G (region i ∪ region j)ᶜ root).card ≤ jointBudget

namespace RootedFamily
variable {G : PhysicalGraph} {ι : Type*} [DecidableEq ι]
variable (P : RootedFamily G ι)

def Conflict (i j : ι) : Prop := i ≠ j ∧
  ((crossing G (P.region i) (P.region j)).Nonempty ∨
    ¬ P.region j ⊆ reachSet G (P.region i)ᶜ P.root ∨
    ¬ P.region i ⊆ reachSet G (P.region j)ᶜ P.root ∨
    MixedOffRoot G P.root (P.region i) (P.region j))

def degreeBound : ℕ :=
  P.cutBound * (P.jointBudget + 2) + 2 * P.singleBudget + 1

def adjacentPartners (i : ι) : Finset ι := P.family.filter fun j =>
  i ≠ j ∧ (crossing G (P.region i) (P.region j)).Nonempty

def belowPartners (i : ι) : Finset ι := P.family.filter fun j =>
  i ≠ j ∧ ¬ P.region j ⊆ reachSet G (P.region i)ᶜ P.root

def abovePartners (i : ι) : Finset ι := P.family.filter fun j =>
  i ≠ j ∧ ¬ P.region i ⊆ reachSet G (P.region j)ᶜ P.root

def mixedPartners (i : ι) : Finset ι := P.family.filter fun j =>
  i ≠ j ∧ P.region j ⊆ reachSet G (P.region i)ᶜ P.root ∧
    MixedOffRoot G P.root (P.region i) (P.region j)

theorem conflict_symmetric : Symmetric P.Conflict := by
  intro i j h
  obtain ⟨hne, h⟩ := h
  refine ⟨hne.symm, ?_⟩
  rcases h with ha | hb | hc | hd
  · left
    simpa only [crossing_comm] using ha
  · exact Or.inr (Or.inr (Or.inl hb))
  · exact Or.inr (Or.inl hc)
  · exact Or.inr (Or.inr (Or.inr ((mixedOffRoot_symm G P.root _ _).1 hd)))

theorem subset_complement {i j : ι} (hi : i ∈ P.family) (hj : j ∈ P.family)
    (hne : i ≠ j) : P.region j ⊆ (P.region i)ᶜ := by
  intro v hv
  exact Finset.mem_compl.2 fun hvi => Finset.disjoint_left.1 (P.disjoint i hi j hj hne) hvi hv

theorem below_is_offRoot {i j : ι} (hi : i ∈ P.family) (hj : j ∈ P.family)
    (hne : i ≠ j) (hbelow : ¬ P.region j ⊆ reachSet G (P.region i)ᶜ P.root) :
    P.region j ⊆ offRootVertices G (P.region i)ᶜ P.root := by
  rcases connected_subset_root_or_offRoot G
    (Finset.mem_compl.2 (P.root_avoids i hi)) (P.connected j hj)
    (P.subset_complement hi hj hne) with h | h
  · exact False.elim (hbelow h)
  · exact h

theorem adjacentPartners_card_le (i : ι) (hi : i ∈ P.family) :
    (P.adjacentPartners i).card ≤ P.cutBound := by
  apply le_trans (disjoint_meeting_card_le G (P.adjacentPartners i) P.region
    (outsideNeighbors G (P.region i)) ?_ ?_)
    ((outsideNeighbors_card_le G _).trans (P.cut_le i hi))
  · intro j hj k hk hne
    exact P.disjoint j (Finset.mem_filter.1 hj).1 k (Finset.mem_filter.1 hk).1 hne
  · intro j hj
    obtain ⟨hjF, hne, hedge⟩ := Finset.mem_filter.1 hj
    obtain ⟨u, hu, v, hv, huv⟩ := (crossing_nonempty_iff G _ _).1 hedge
    exact ⟨v, hv, (mem_outsideNeighbors G _ _).2
      ⟨fun hvi => Finset.disjoint_left.1 (P.disjoint i hi j hjF hne) hvi hv,
        u, hu, huv⟩⟩

theorem belowPartners_card_le (i : ι) (hi : i ∈ P.family) :
    (P.belowPartners i).card ≤ P.singleBudget := by
  apply le_trans (disjoint_meeting_card_le G (P.belowPartners i) P.region
    (offRootVertices G (P.region i)ᶜ P.root) ?_ ?_) (P.single_le i hi)
  · intro j hj k hk hne
    exact P.disjoint j (Finset.mem_filter.1 hj).1 k (Finset.mem_filter.1 hk).1 hne
  · intro j hj
    obtain ⟨hjF, hne, hbelow⟩ := Finset.mem_filter.1 hj
    obtain ⟨v, hv⟩ := (P.connected j hjF).1
    exact ⟨v, hv, P.below_is_offRoot hi hjF hne hbelow hv⟩

/-- A support left away from the root gives a real connected separator. -/
theorem above_separator {i j : ι} (hi : i ∈ P.family) (hj : j ∈ P.family)
    (hne : i ≠ j) (habove : ¬ P.region i ⊆ reachSet G (P.region j)ᶜ P.root)
    (x : G.Vertex) (hx : x ∈ P.region i) :
    SeparatingRegion G Finset.univ x P.root (P.region j) := by
  have haway := P.below_is_offRoot hj hi hne.symm habove
  have hxaway := haway hx
  rw [offRootVertices_eq_sdiff G (Finset.mem_compl.2 (P.root_avoids j hj))] at hxaway
  have hxnot : x ∉ P.region j := by
    exact Finset.mem_compl.1 ((Finset.mem_sdiff.1 hxaway).1)
  refine ⟨Finset.subset_univ _, P.connected j hj, by simp [hxnot],
    by simp [P.root_avoids j hj], ?_⟩
  intro hp
  have hp' : InReach G (P.region j)ᶜ x P.root := by
    simpa only [← Finset.compl_eq_univ_sdiff (P.region j)] using hp
  exact (Finset.mem_sdiff.1 hxaway).2
    ((mem_reachSet G (P.region j)ᶜ P.root x).2 ⟨hp'.source, hp'.symm⟩)

theorem abovePartners_card_le (hG : G.IsConnected) (i : ι) (hi : i ∈ P.family) :
    (P.abovePartners i).card ≤ P.singleBudget + 1 := by
  obtain ⟨x, hx⟩ := (P.connected i hi).1
  apply bounded_sides_bound_separators G Finset.univ (connected_univ G hG)
    x P.root (P.abovePartners i) P.region P.singleBudget
  · intro j hj
    obtain ⟨hjF, hne, habove⟩ := Finset.mem_filter.1 hj
    exact P.above_separator hi hjF hne habove x hx
  · intro j hj k hk hne
    exact P.disjoint j (Finset.mem_filter.1 hj).1 k (Finset.mem_filter.1 hk).1 hne
  · intro j hj
    obtain ⟨hjF, hne, habove⟩ := Finset.mem_filter.1 hj
    have hsep := P.above_separator hi hjF hne habove x hx
    have hsub := separatorSide_subset_offRoot G hsep
    have hc : (separatorSide G Finset.univ (P.region j) x).card ≤
        (offRootVertices G (P.region j)ᶜ P.root).card := by
      simpa only [← Finset.compl_eq_univ_sdiff (P.region j)] using Finset.card_le_card hsub
    exact hc.trans (P.single_le j hjF)

/-- A mixed small component gives a separator INSIDE the giant of G-C.
The witness x is an actual outside neighbor of C. This is where the source
replaces an exponentially large distance neighborhood by nested separators. -/
theorem mixed_separator_witness (i j : ι) (hi : i ∈ P.family)
    (hj : j ∈ P.mixedPartners i) :
    ∃ x ∈ outsideNeighbors G (P.region i),
      SeparatingRegion G (reachSet G (P.region i)ᶜ P.root) x P.root (P.region j) ∧
      (separatorSide G (reachSet G (P.region i)ᶜ P.root) (P.region j) x).card ≤
        P.jointBudget := by
  obtain ⟨hjF, hne, hjH, A, hA, hAi, hAj⟩ := Finset.mem_filter.1 hj
  obtain ⟨hAc, hwA⟩ := (mem_offRootComponents G _ _ _).1 hA
  let H := reachSet G (P.region i)ᶜ P.root
  have hwHi : P.root ∈ (P.region i)ᶜ := Finset.mem_compl.2 (P.root_avoids i hi)
  have hH : H ∈ components G (P.region i)ᶜ := root_component_mem G hwHi
  have hAsub : A ⊆ (P.region i)ᶜ := by
    intro v hv
    have ho := component_subset G hAc hv
    simp only [Finset.mem_compl, Finset.mem_union] at ho ⊢
    tauto
  obtain ⟨a, ha, d, hd, had⟩ := (crossing_nonempty_iff G A (P.region j)).1 hAj
  have haH : a ∈ H := component_closed G hH d (hjH hd) a (hAsub ha) had.symm
  have hAH : A ⊆ H := connected_subset_component G
    (component_connected G hAc) hAsub hH ha haH
  have hAjoint : A ⊆ H \ P.region j := by
    intro v hv
    refine Finset.mem_sdiff.2 ⟨hAH hv, ?_⟩
    have ho := component_subset G hAc hv
    simp only [Finset.mem_compl, Finset.mem_union] at ho
    tauto
  have hHsub : H \ P.region j ⊆ (P.region i ∪ P.region j)ᶜ := by
    intro v hv
    obtain ⟨hvH, hvj⟩ := Finset.mem_sdiff.1 hv
    have hvi := Finset.mem_compl.1 (component_subset G hH hvH)
    simp [hvi, hvj]
  have hAin := component_in_smaller_ambient G hAc hAjoint hHsub
  obtain ⟨x, hxA, c, hci, hxc⟩ := (crossing_nonempty_iff G A (P.region i)).1 hAi
  have hxN : x ∈ outsideNeighbors G (P.region i) :=
    (mem_outsideNeighbors G _ _).2
      ⟨Finset.mem_compl.1 (hAsub hxA), c, hci, hxc.symm⟩
  have hxeq : A = separatorSide G H (P.region j) x :=
    component_eq_reachSet G ((mem_components G _ A).1 hAin) hxA
  have hwV : P.root ∈ H \ P.region j := Finset.mem_sdiff.2
    ⟨self_mem_reachSet G hwHi, P.root_avoids j hjF⟩
  have hsep : SeparatingRegion G H x P.root (P.region j) := by
    refine ⟨hjH, P.connected j hjF, hAjoint hxA, hwV, ?_⟩
    intro hp
    have hwR : P.root ∈ separatorSide G H (P.region j) x :=
      (mem_reachSet G _ x P.root).2 ⟨hwV, hp⟩
    exact hwA (hxeq.symm ▸ hwR)
  have hAU : A ⊆ offRootVertices G (P.region i ∪ P.region j)ᶜ P.root := by
    intro v hv
    exact Finset.mem_biUnion.2 ⟨A, hA, hv⟩
  refine ⟨x, hxN, hsep, ?_⟩
  rw [← hxeq]
  exact (Finset.card_le_card hAU).trans (P.joint_le i hi j hjF hne)

def separatorsAt (i : ι) (x : G.Vertex) : Finset ι := P.family.filter fun j =>
  SeparatingRegion G (reachSet G (P.region i)ᶜ P.root) x P.root (P.region j) ∧
    (separatorSide G (reachSet G (P.region i)ᶜ P.root) (P.region j) x).card ≤
      P.jointBudget

theorem separatorsAt_card_le (i : ι) (hi : i ∈ P.family) (x : G.Vertex) :
    (P.separatorsAt i x).card ≤ P.jointBudget + 1 := by
  have hH := reachSet_connected G (Finset.mem_compl.2 (P.root_avoids i hi))
  apply bounded_sides_bound_separators G _ hH x P.root
    (P.separatorsAt i x) P.region P.jointBudget
  · intro j hj
    exact (Finset.mem_filter.1 hj).2.1
  · intro j hj k hk hne
    exact P.disjoint j (Finset.mem_filter.1 hj).1 k (Finset.mem_filter.1 hk).1 hne
  · intro j hj
    exact (Finset.mem_filter.1 hj).2.2

theorem mixedPartners_card_le (i : ι) (hi : i ∈ P.family) :
    (P.mixedPartners i).card ≤ P.cutBound * (P.jointBudget + 1) := by
  have hsub : P.mixedPartners i ⊆
      (outsideNeighbors G (P.region i)).biUnion (P.separatorsAt i) := by
    intro j hj
    obtain ⟨x, hx, hsep, hsize⟩ := P.mixed_separator_witness i j hi hj
    exact Finset.mem_biUnion.2 ⟨x, hx,
      Finset.mem_filter.2 ⟨(Finset.mem_filter.1 hj).1, hsep, hsize⟩⟩
  calc
    (P.mixedPartners i).card ≤
        ((outsideNeighbors G (P.region i)).biUnion (P.separatorsAt i)).card :=
      Finset.card_le_card hsub
    _ ≤ ∑ x ∈ outsideNeighbors G (P.region i), (P.separatorsAt i x).card :=
      Finset.card_biUnion_le
    _ ≤ ∑ _x ∈ outsideNeighbors G (P.region i), (P.jointBudget + 1) :=
      Finset.sum_le_sum (s := outsideNeighbors G (P.region i)) fun x _ =>
        P.separatorsAt_card_le i hi x
    _ = (outsideNeighbors G (P.region i)).card * (P.jointBudget + 1) := by
      simp
    _ ≤ P.cutBound * (P.jointBudget + 1) :=
      Nat.mul_le_mul_right _ ((outsideNeighbors_card_le G _).trans (P.cut_le i hi))

/-- Every conflict is charged to one of the four explicitly counted classes. -/
theorem conflict_neighbors_cover (i : ι) :
    P.family.filter (P.Conflict i) ⊆
      P.adjacentPartners i ∪ P.belowPartners i ∪ P.abovePartners i ∪ P.mixedPartners i := by
  intro j hj
  obtain ⟨hjF, hne, ha | hb | hc | hd⟩ := Finset.mem_filter.1 hj
  · exact Finset.mem_union_left _ (Finset.mem_union_left _
      (Finset.mem_union_left _ (Finset.mem_filter.2 ⟨hjF, hne, ha⟩)))
  · exact Finset.mem_union_left _ (Finset.mem_union_left _
      (Finset.mem_union_right _ (Finset.mem_filter.2 ⟨hjF, hne, hb⟩)))
  · exact Finset.mem_union_left _
      (Finset.mem_union_right _ (Finset.mem_filter.2 ⟨hjF, hne, hc⟩))
  · by_cases hr : P.region j ⊆ reachSet G (P.region i)ᶜ P.root
    · exact Finset.mem_union_right _ (Finset.mem_filter.2 ⟨hjF, hne, hr, hd⟩)
    · exact Finset.mem_union_left _ (Finset.mem_union_left _
        (Finset.mem_union_right _ (Finset.mem_filter.2 ⟨hjF, hne, hr⟩)))

/-- The exact source polynomial J = D(t+2)+2s+1. -/
theorem conflict_degree_le (hG : G.IsConnected) (i : ι) (hi : i ∈ P.family) :
    (P.family.filter (P.Conflict i)).card ≤ P.degreeBound := by
  have ha := P.adjacentPartners_card_le i hi
  have hb := P.belowPartners_card_le i hi
  have hc := P.abovePartners_card_le hG i hi
  have hd := P.mixedPartners_card_le i hi
  have h1 := Finset.card_union_le (P.adjacentPartners i) (P.belowPartners i)
  have h2 := Finset.card_union_le (P.adjacentPartners i ∪ P.belowPartners i) (P.abovePartners i)
  have h3 := Finset.card_union_le
    (P.adjacentPartners i ∪ P.belowPartners i ∪ P.abovePartners i) (P.mixedPartners i)
  have h4 := Finset.card_le_card (P.conflict_neighbors_cover i)
  calc
    (P.family.filter (P.Conflict i)).card ≤
        P.cutBound + P.singleBudget + (P.singleBudget + 1) +
          P.cutBound * (P.jointBudget + 1) := by omega
    _ = P.degreeBound := by unfold degreeBound; ring

/-- A nonconflicting pair has exactly the original component count needed
by the already formalized event-probability identity. -/
theorem nonconflict_component_identity (hG : G.IsConnected) (i j : ι)
    (hi : i ∈ P.family) (hj : j ∈ P.family) (hne : i ≠ j)
    (hn : ¬ P.Conflict i j) :
    Disjoint (P.region i) (P.region j) ∧
      crossSize G (P.region i) (P.region j) = 0 ∧
      G.originalExteriorComponents (P.region i ∪ P.region j) + 1 =
        G.originalExteriorComponents (P.region i) + G.originalExteriorComponents (P.region j) := by
  have ha : ¬ (crossing G (P.region i) (P.region j)).Nonempty :=
    fun h => hn ⟨hne, Or.inl h⟩
  have ht : P.region j ⊆ reachSet G (P.region i)ᶜ P.root := by
    by_contra h
    exact hn ⟨hne, Or.inr (Or.inl h)⟩
  have hs : P.region i ⊆ reachSet G (P.region j)ᶜ P.root := by
    by_contra h
    exact hn ⟨hne, Or.inr (Or.inr (Or.inl h))⟩
  have hm : ¬ MixedOffRoot G P.root (P.region i) (P.region j) :=
    fun h => hn ⟨hne, Or.inr (Or.inr (Or.inr h))⟩
  refine ⟨P.disjoint i hi j hj hne, ?_, ?_⟩
  · exact Finset.card_eq_zero.2 (Finset.not_nonempty_iff_eq_empty.1 ha)
  · exact original_components_nonconflict G hG (P.connected i hi).1
      (P.disjoint i hi j hj hne) P.root (P.root_avoids i hi) (P.root_avoids j hj)
      ht hs hm

end RootedFamily
end Erdos1016.CycleSupply
