import Erdos1016.CycleSpace.EvenForestZero
import Erdos1016.Probability.Avoidance.PackingRate
import Erdos1016.Graph.PancyclicRank

set_option autoImplicit false
set_option maxHeartbeats 600000

noncomputable section
namespace Erdos1016.Proof.ClosedCubicDecay
open BoundaryDecay BoundaryTrace
open scoped BigOperators

local instance (p : Prop) : Decidable p := Classical.propDecidable p

/-- With no degree-two ports, the one-apex law is exactly the ordinary
cycle-space law; the added apex has no incident edges. -/
def localCycleEquiv (H : PhysicalGraph) [IsEmpty (CorePin H)] :
    (corePorts H).LocalSpace ≃ H.CycleSpace where
  toFun w := ⟨w.1.1, by
    have hw := w.2
    change H.traceNetwork.boundary w.1.1 + push (corePorts H).inside w.1.2 = 0 at hw
    have hp : push (corePorts H).inside w.1.2 = 0 := by
      ext v
      simp [push]
    simpa [hp] using hw⟩
  invFun x := ⟨(x.1, 0), by
    change H.traceNetwork.boundary x.1 + push (corePorts H).inside 0 = 0
    simp [x.2]⟩
  left_inv w := by
    apply Subtype.ext
    change (w.1.1, 0) = w.1
    exact Prod.ext rfl (Subsingleton.elim _ _)
  right_inv x := by apply Subtype.ext; rfl

theorem coreBoundaryAverage_eq_cycle_density (H : PhysicalGraph) [IsEmpty (CorePin H)] :
    coreBoundaryAverage H = Finite.density (fun x : H.CycleSpace => H.IsForest x.1) := by
  unfold coreBoundaryAverage
  rw [Ported.apexFraction_eq_local]
  apply Finite.density_equiv (localCycleEquiv H)
  intro x
  rfl

theorem coreBoundaryAverage_le_inverse_rank (H : PhysicalGraph) [IsEmpty (CorePin H)] :
    coreBoundaryAverage H ≤ 1 / (2 : ℝ) ^ H.cycleRank := by
  rw [coreBoundaryAverage_eq_cycle_density]
  have hc := Finite.count_mono (P := fun x : H.CycleSpace => H.IsForest x.1)
    (Q := fun x => x = 0) (fun x hx => by
      apply Subtype.ext
      exact CycleSpaceForestZero.word_eq_zero_of_boundary_zero_of_forest H x.1 x.2 hx)
  have hz : Finite.count (fun x : H.CycleSpace => x = 0) = 1 := by
    unfold Finite.count
    classical
    rw [Finset.sum_eq_single (0 : H.CycleSpace)]
    · simp
    · intro b _ hb
      simp [hb]
    · simp
  have hcard : (Fintype.card H.CycleSpace : ℝ) = (2 : ℝ) ^ H.cycleRank := by
    exact_mod_cast H.cycleSpace_card
  unfold Finite.density
  rw [hcard]
  exact div_le_div_of_nonneg_right (by simpa [hz] using hc) (by positivity)

/-- The closed cubic case has exponentially small forest probability.
This handles the missing-port branch independently of the protector proof. -/
theorem closed_cubic_bound (H : PhysicalGraph) [IsEmpty (CorePin H)]
    (hH : H.IsConnected) (hmin : ∀ v, 2 ≤ H.degree v) (hmax : ∀ v, H.degree v ≤ 3) :
    coreBoundaryAverage H ≤ (2 : ℝ) ^ (-(H.vertexCount : ℝ) / 2) := by
  have hb : Nonbacktracking.degreeTwoCount H = 0 := by
    unfold Nonbacktracking.degreeTwoCount
    apply Finset.card_eq_zero.mpr
    apply Finset.eq_empty_iff_forall_not_mem.mpr
    intro v hv
    exact isEmptyElim (⟨v, (Finset.mem_filter.mp hv).2⟩ : CorePin H)
  have hdegree := Nonbacktracking.min_two_max_three_degree_sum H hmin hmax
  rw [hb] at hdegree
  have hrank := congrArg (fun k : ℕ => (k : ℝ)) (Extremal.connected_rank_euler H hH)
  push_cast at hdegree hrank
  have hr : (H.vertexCount : ℝ) / 2 ≤ H.cycleRank := by linarith
  calc
    _ ≤ 1 / (2 : ℝ) ^ H.cycleRank := coreBoundaryAverage_le_inverse_rank H
    _ = (2 : ℝ) ^ (-(H.cycleRank : ℝ)) := by
      rw [Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 2), Real.rpow_natCast]
      simp only [one_div]
    _ ≤ _ := Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)

end Erdos1016.Proof.ClosedCubicDecay
