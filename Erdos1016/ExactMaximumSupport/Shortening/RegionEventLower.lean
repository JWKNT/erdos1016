import Erdos1016.Probability.Cylinders.RegionCycleEvents

set_option autoImplicit false

/-!
# The redundant coordinate on an actual region cut

An even word has even cut parity, so one cut label is determined by all the
others. A cyclic region with at most d cut labels therefore has nonzero
internal zero-cut event probability at least 2^(-d), for d positive. Loops,
parallel labels, disconnected regions and empty cuts are all retained.
-/
noncomputable section
open scoped BigOperators
namespace Erdos1016.ExactMaximumSupport.Shortening.RegionEventLower
open FiniteMultiGraph BoundaryTrace BoundaryDecay

/-- The actual cut coordinates of an even physical edge word sum to zero. -/
theorem cut_parity (G : FiniteMultiGraph) (U : Finset G.Vertex) (x : G.CycleSpace) :
    (∑ e ∈ G.cutEdges U, x.1 e)=0 := by
  classical
  have hsum : (∑ v ∈ U, G.boundary x.1 v)=∑ e ∈ G.cutEdges U,x.1 e := by
    change (∑ v ∈ U,∑ e,((if G.src e=v then x.1 e else 0)+
      (if G.dst e=v then x.1 e else 0)))= _
    rw [Finset.sum_comm]
    simp_rw [Finset.sum_add_distrib,Finset.sum_ite_eq]
    simp only [cutEdges,Finset.sum_filter]
    rw [←Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro e _
    by_cases hs : G.src e∈U <;> by_cases ht : G.dst e∈U <;>
      simp [hs,ht,bit_add_self]
  rw [←hsum]
  apply Finset.sum_eq_zero
  intro v _
  exact congrFun x.2 v

/-- Vanishing on all but one physical cut label is the exact zero-cut event. -/
theorem zeroCut_iff_erase (G : FiniteMultiGraph) (U : Finset G.Vertex)
    (e₀ : G.Edge) (he₀ : e₀∈G.cutEdges U) (x : G.CycleSpace) :
    x∈G.zeroCutSpace U ↔ ∀ e∈(G.cutEdges U).erase e₀,x.1 e=0 := by
  classical
  rw [G.mem_zeroCutSpace_iff]
  constructor
  · intro h e he
    exact h e (Finset.mem_of_mem_erase he)
  · intro h e he
    by_cases heq : e=e₀
    · subst e
      have hsingle : (∑ g∈G.cutEdges U,x.1 g)=x.1 e₀ := by
        apply Finset.sum_eq_single e₀
        · intro g hg hne
          exact h g (Finset.mem_erase.mpr ⟨hne,hg⟩)
        · exact fun hn => (hn he₀).elim
      exact hsingle.symm.trans (cut_parity G U x)
    · exact h e (Finset.mem_erase.mpr ⟨heq,he⟩)

/-- The parity saving gives the stronger actual cyclic-region event bound. -/
theorem regionCycleEvent_probability_ge (G : FiniteMultiGraph) (U : Finset G.Vertex)
    (hcyc : ∃x:G.internalCycleSpace U,x≠0) (d : ℕ) (hd : 1≤d)
    (hcut : (G.cutEdges U).card≤d) :
    1/(2:ℝ)^d ≤ Finite.density (G.RegionCycleEvent U) := by
  classical
  by_cases hne : (G.cutEdges U).Nonempty
  · obtain ⟨e,he⟩ := hne
    have hcard : ((G.cutEdges U).erase e).card+1≤d := by
      rw [Finset.card_erase_add_one he]
      exact hcut
    have hz : 1/(2:ℝ)^((G.cutEdges U).erase e).card ≤
        Finite.density (fun x:G.CycleSpace => x∈G.zeroCutSpace U) := by
      have hp : (fun x:G.CycleSpace => x∈G.zeroCutSpace U)=
          fun x => ∀g∈(G.cutEdges U).erase e,x.1 g=0 := by
        funext x
        exact propext (zeroCut_iff_erase G U e he x)
      rw [hp]
      exact G.zeroCoordinates_probability_ge _
    rw [G.regionCycleEvent_density]
    have hh := mul_le_mul (G.internalCycleFactor_ge_half U hcyc) hz
      (by positivity) (G.internalCycleFactor_nonneg U)
    calc
      _ ≤ 1/(2:ℝ)^(((G.cutEdges U).erase e).card+1) :=
        one_div_le_one_div_of_le (by positivity)
          (pow_le_pow_right₀ (by norm_num) hcard)
      _ = (1/2:ℝ)*(1/(2:ℝ)^((G.cutEdges U).erase e).card) := by rw [pow_succ]; ring
      _ ≤ _ := hh
  · have hempty : G.cutEdges U=∅ := Finset.not_nonempty_iff_eq_empty.mp hne
    exact (one_div_le_one_div_of_le (by positivity : (0:ℝ)<2^(0+1))
      (pow_le_pow_right₀ (by norm_num : (1:ℝ)≤2) hd)).trans
      (G.regionCycleEvent_probability_ge U hcyc 0 (by simp [hempty]))

end Erdos1016.ExactMaximumSupport.Shortening.RegionEventLower
