import Erdos1016.Probability.Moments.SecondMoments
import Erdos1016.Probability.Moments.CycleEvents

set_option autoImplicit false

/-!
# The actual-edge load bound

Source: the ordered-pair charge preceding manuscript (12.5).

The family and supports may overlap. We sum over real nonnegative weights;
no independence is postulated. The maximum-degree hypothesis is required
only at vertices on a support. A high-degree apex outside every support is
therefore harmless.
-/

noncomputable section
open scoped BigOperators
namespace Erdos1016.BoundaryDecay

local instance weightedLoadsDecidable (p : Prop) : Decidable p := Classical.propDecidable p

section Abstract
variable {V ι : Type*} [Fintype V]

/-- Every physical adjacency is retained. -/
def neighbors (R : V → V → Prop) (u : V) : Finset V := Finset.univ.filter (R u)

def Touch (R : V → V → Prop) (S T : Finset V) : Prop :=
  ∃ u ∈ S, ∃ v ∈ T, R u v

def vertexLoad (s : Finset ι) (S : ι → Finset V) (w : ι → ℝ) (v : V) : ℝ :=
  ∑ i ∈ s, if v ∈ S i then w i else 0



/-- Charge one touching partner to at least one actual endpoint adjacency.
Multiple possible witnesses are retained only for an upper bound. -/
theorem touching_weight_le_endpoint_sum (R : V → V → Prop)
    (U W : Finset V) (a : ℝ) (ha : 0 ≤ a) :
    (if Touch R U W then a else 0) ≤
      ∑ u ∈ U, ∑ v ∈ neighbors R u, if v ∈ W then a else 0 := by
  by_cases ht : Touch R U W
  · rw [if_pos ht]
    obtain ⟨u, hu, v, hv, huv⟩ := ht
    have hm : v ∈ neighbors R u := Finset.mem_filter.2 ⟨Finset.mem_univ _, huv⟩
    have hin : a ≤ ∑ v' ∈ neighbors R u, if v' ∈ W then a else 0 := by
      have h := Finset.single_le_sum (s := neighbors R u)
        (f := fun v' => if v' ∈ W then a else 0)
        (fun v' _ => by
          by_cases hvw : v' ∈ W <;> simp [hvw, ha]) hm
      simpa only [if_pos hv] using h
    have hout : (∑ v' ∈ neighbors R u, if v' ∈ W then a else 0) ≤
        ∑ u' ∈ U, ∑ v' ∈ neighbors R u', if v' ∈ W then a else 0 := by
      exact Finset.single_le_sum
        (s := U)
        (f := fun u' => ∑ v' ∈ neighbors R u', if v' ∈ W then a else 0)
        (fun u' _ => Finset.sum_nonneg fun v' _ => by
          by_cases hvw : v' ∈ W <;> simp [hvw, ha]) hu
    exact hin.trans hout
  · rw [if_neg ht]
    apply Finset.sum_nonneg
    intro u _
    apply Finset.sum_nonneg
    intro v _
    by_cases hvw : v ∈ W <;> simp [hvw, ha]

/-- Bound the total weight of all partners touching one fixed support. -/
theorem touching_partner_mass_le (R : V → V → Prop)
    (s : Finset ι) (S : ι → Finset V) (w : ι → ℝ)
    (hw : ∀ i ∈ s, 0 ≤ w i) (A : ℝ) (hA : 0 ≤ A)
    (hload : ∀ v, vertexLoad s S w v ≤ A)
    (d L : ℕ) (U : Finset V)
    (hdegree : ∀ u ∈ U, (neighbors R u).card ≤ d) (hsize : U.card ≤ L) :
    (∑ j ∈ s, if Touch R U (S j) then w j else 0) ≤ (d : ℝ) * L * A := by
  calc
    (∑ j ∈ s, if Touch R U (S j) then w j else 0)
        ≤ ∑ j ∈ s, ∑ u ∈ U, ∑ v ∈ neighbors R u,
          if v ∈ S j then w j else 0 := by
      exact Finset.sum_le_sum fun j hj =>
        touching_weight_le_endpoint_sum R U (S j) (w j) (hw j hj)
    _ = ∑ u ∈ U, ∑ v ∈ neighbors R u, vertexLoad s S w v := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro u _
      rw [Finset.sum_comm]
      rfl
    _ ≤ ∑ u ∈ U, ∑ _v ∈ neighbors R u, A := by
      exact Finset.sum_le_sum fun u _ => Finset.sum_le_sum fun v _ => hload v
    _ ≤ ∑ _u ∈ U, (d : ℝ) * A := by
      apply Finset.sum_le_sum
      intro u hu
      simp only [Finset.sum_const, nsmul_eq_mul]
      apply mul_le_mul_of_nonneg_right _ hA
      exact_mod_cast hdegree u hu
    _ = (U.card : ℝ) * ((d : ℝ) * A) := by simp
    _ ≤ (L : ℝ) * ((d : ℝ) * A) := by
      apply mul_le_mul_of_nonneg_right _ (mul_nonneg (Nat.cast_nonneg _) hA)
      exact_mod_cast hsize
    _ = (d : ℝ) * L * A := by ring



end Abstract

section Physical
variable (G : PhysicalGraph)











end Physical
end Erdos1016.BoundaryDecay
