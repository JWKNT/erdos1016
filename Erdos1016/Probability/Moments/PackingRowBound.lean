import Erdos1016.Graph.PackingCover

set_option autoImplicit false
noncomputable section
open scoped BigOperators

namespace Erdos1016.BoundaryDecay
variable {Ω ι V : Type*} [Fintype Ω] [DecidableEq ι] [DecidableEq V]

/-- Turn the graph packing bound and vertex cycle-weight estimate into the
aggregate exceptional row estimate. `joint j` may be the actual mixed moment
of a fixed cycle and partner `j`; no independence is used. -/
theorem exceptional_row_le_of_packing (s : Finset ι) (U : ι → Finset V)
    (d L : ℕ) (a joint : ι → ℝ) (a₀ M b : ℝ)
    (ha₀ : 0 ≤ a₀) (hM : 0 ≤ M) (hb : 0 ≤ b)
    (ha : ∀ i ∈ s, 0 ≤ a i)
    (hne : ∀ i ∈ s, (U i).Nonempty)
    (hsize : ∀ i ∈ s, (U i).card ≤ L)
    (hpack : ∀ F ⊆ s, (∀ i ∈ F, ∀ j ∈ F, i ≠ j → Disjoint (U i) (U j)) → F.card ≤ d)
    (hload : ∀ v, (∑ i ∈ s, if v ∈ U i then a i else 0) ≤ b)
    (hjoint : ∀ i ∈ s, joint i ≤ a₀ * M * a i) :
    (∑ i ∈ s, joint i) ≤ a₀ * (M * d * L * b) := by
  have hmass := PackingCover.mass_le_of_packing s U d L hne hsize hpack a b hb ha hload
  calc
    _ ≤ ∑ i ∈ s, a₀ * M * a i := Finset.sum_le_sum hjoint
    _ = a₀ * M * (∑ i ∈ s, a i) := (Finset.mul_sum _ _ _).symm
    _ ≤ a₀ * M * ((d : ℝ) * L * b) := mul_le_mul_of_nonneg_left hmass (mul_nonneg ha₀ hM)
    _ = _ := by ring

end Erdos1016.BoundaryDecay
