import Erdos1016.Decomposition.Regions.ComponentPartition

set_option autoImplicit false

/-!
# Exact original complement identity for a nonconflicting pair

The component count is obtained from an equality of finite families of actual
component vertex sets. No independence assertion is used in the proof.
-/

noncomputable section
namespace Erdos1016.CycleSupply
open SafeCore BoundaryDecay
local instance cycleSupplyNonconflictPartitionDecidable (p : Prop) : Decidable p := Classical.propDecidable p
variable (G : PhysicalGraph)

/-- A component away from the root after the joint deletion contacts both
removed supports by actual edges. -/
def MixedOffRoot (w : G.Vertex) (S T : Finset G.Vertex) : Prop :=
  ∃ A ∈ offRootComponents G (S ∪ T)ᶜ w,
    (crossing G A S).Nonempty ∧ (crossing G A T).Nonempty

theorem mixedOffRoot_symm (w : G.Vertex) (S T : Finset G.Vertex) :
    MixedOffRoot G w S T ↔ MixedOffRoot G w T S := by
  unfold MixedOffRoot
  rw [Finset.union_comm S T]
  constructor <;> rintro ⟨A, hA, hS, hT⟩ <;> exact ⟨A, hA, hT, hS⟩

theorem single_offRoot_into_joint {S T A : Finset G.Vertex} {w : G.Vertex}
    (hw : w ∈ Sᶜ) (hT : T ⊆ reachSet G Sᶜ w)
    (hA : A ∈ offRootComponents G Sᶜ w) :
    A ∈ offRootComponents G (S ∪ T)ᶜ w := by
  obtain ⟨hAc, hwn⟩ := (mem_offRootComponents G Sᶜ A w).1 hA
  have hne : A ≠ reachSet G Sᶜ w := by
    intro h
    exact hwn ((component_root_iff G hAc hw).2 h)
  have hd := components_disjoint G hAc (root_component_mem G hw) hne
  have hAJ : A ⊆ (S ∪ T)ᶜ := by
    intro v hv
    apply Finset.mem_compl.2
    intro h
    rcases Finset.mem_union.1 h with hS | hT'
    · exact (Finset.mem_compl.1 (component_subset G hAc hv)) hS
    · exact Finset.disjoint_left.1 hd hv (hT hT')
  have hJU : (S ∪ T)ᶜ ⊆ Sᶜ := by
    intro v hv
    simp only [Finset.mem_compl, Finset.mem_union] at hv ⊢
    tauto
  exact (mem_offRootComponents G (S ∪ T)ᶜ A w).2
    ⟨component_in_smaller_ambient G hAc hAJ hJU, hwn⟩

/-- Restoring the second support does not affect a component with no edge
to it. This is an equality-of-components argument, not a rank heuristic. -/
theorem joint_offRoot_into_single {S T A : Finset G.Vertex} {w : G.Vertex}
    (hA : A ∈ offRootComponents G (S ∪ T)ᶜ w)
    (hno : crossing G A T = ∅) : A ∈ offRootComponents G Sᶜ w := by
  obtain ⟨hAc, hwn⟩ := (mem_offRootComponents G (S ∪ T)ᶜ A w).1 hA
  have hVU : (S ∪ T)ᶜ ⊆ Sᶜ := by
    intro v hv
    simp only [Finset.mem_compl, Finset.mem_union] at hv ⊢
    tauto
  have hnew : Sᶜ \ (S ∪ T)ᶜ ⊆ T := by
    intro v hv
    simp only [Finset.mem_sdiff, Finset.mem_compl, Finset.mem_union] at hv
    tauto
  have he : crossing G A (Sᶜ \ (S ∪ T)ᶜ) = ∅ := by
    apply Finset.eq_empty_iff_forall_not_mem.2
    intro e he
    have h := crossing_mono G (Finset.Subset.refl A) hnew he
    simpa only [hno, Finset.not_mem_empty] using h
  exact (mem_offRootComponents G Sᶜ A w).2
    ⟨component_in_larger_ambient G hAc hVU he, hwn⟩

theorem offRoot_families_disjoint (hG : G.IsConnected)
    {S T : Finset G.Vertex} (hSne : S.Nonempty) (hST : Disjoint S T)
    (w : G.Vertex) :
    Disjoint (offRootComponents G Sᶜ w) (offRootComponents G Tᶜ w) := by
  apply Finset.disjoint_left.2
  intro A hAS hAT
  have hS := ((mem_offRootComponents G Sᶜ A w).1 hAS).1
  have hT := ((mem_offRootComponents G Tᶜ A w).1 hAT).1
  obtain ⟨a, ha, s, hs, has⟩ := (crossing_nonempty_iff G A S).1
    (component_touches_removed G hG hSne hS)
  have hsT : s ∈ Tᶜ := Finset.mem_compl.2
    (fun ht => Finset.disjoint_left.1 hST hs ht)
  have hsA := component_closed G hT a ha s hsT has
  exact (Finset.mem_compl.1 (component_subset G hS hsA)) hs

/-- Every joint off-root component is exactly one old off-root component.
The root component may merge extensively; it is not counted as a small piece. -/
theorem offRoot_joint_partition {S T : Finset G.Vertex} {w : G.Vertex}
    (hwS : w ∈ Sᶜ) (hwT : w ∈ Tᶜ)
    (hT : T ⊆ reachSet G Sᶜ w) (hS : S ⊆ reachSet G Tᶜ w)
    (hn : ¬ MixedOffRoot G w S T) :
    offRootComponents G (S ∪ T)ᶜ w =
      offRootComponents G Sᶜ w ∪ offRootComponents G Tᶜ w := by
  apply Finset.Subset.antisymm
  · intro A hA
    by_cases ht : (crossing G A T).Nonempty
    · have hs : crossing G A S = ∅ := by
        apply Finset.not_nonempty_iff_eq_empty.1
        intro h
        exact hn ⟨A, hA, h, ht⟩
      have hA' : A ∈ offRootComponents G (T ∪ S)ᶜ w := by
        simpa only [Finset.union_comm] using hA
      exact Finset.mem_union_right _ (joint_offRoot_into_single G hA' hs)
    · exact Finset.mem_union_left _ (joint_offRoot_into_single G hA
        (Finset.not_nonempty_iff_eq_empty.1 ht))
  · intro A hA
    rcases Finset.mem_union.1 hA with hA | hA
    · exact single_offRoot_into_joint G hwS hT hA
    · simpa only [Finset.union_comm] using single_offRoot_into_joint G hwT hS hA

/-- Formula (4.2), before converting to exact event independence. -/
theorem original_components_nonconflict (hG : G.IsConnected)
    {S T : Finset G.Vertex} (hSne : S.Nonempty) (hST : Disjoint S T)
    (w : G.Vertex) (hwS : w ∉ S) (hwT : w ∉ T)
    (hT : T ⊆ reachSet G Sᶜ w) (hS : S ⊆ reachSet G Tᶜ w)
    (hn : ¬ MixedOffRoot G w S T) :
    G.originalExteriorComponents (S ∪ T) + 1 =
      G.originalExteriorComponents S + G.originalExteriorComponents T := by
  have hs := offRootComponents_card_add_one G (Finset.mem_compl.2 hwS)
  have ht := offRootComponents_card_add_one G (Finset.mem_compl.2 hwT)
  have hwJ : w ∈ (S ∪ T)ᶜ := by simp [hwS, hwT]
  have hj := offRootComponents_card_add_one G hwJ
  have hpart := congrArg Finset.card (offRoot_joint_partition G
    (Finset.mem_compl.2 hwS) (Finset.mem_compl.2 hwT) hT hS hn)
  rw [Finset.card_union_of_disjoint (offRoot_families_disjoint G hG hSne hST w)] at hpart
  have hcount : exteriorCount G (S ∪ T) + 1 = exteriorCount G S + exteriorCount G T := by
    change componentCount G (S ∪ T)ᶜ + 1 = componentCount G Sᶜ + componentCount G Tᶜ
    omega
  simpa only [exteriorCount_eq_original] using hcount

end Erdos1016.CycleSupply
