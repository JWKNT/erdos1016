import Erdos1016.PolynomialBound.TwoLinkMoment
import Erdos1016.ExactMaximumSupport.Averaging

set_option autoImplicit false

/-!
# Two-link weight at forest probability two fifths

The actual normalized seed moments give the coefficient two thirds.
The connected supports, degree conditions, and link envelope are graph
hypotheses. No abstract pair-moment estimate is assumed.
-/

noncomputable section
open scoped BigOperators
namespace Erdos1016.ExactMaximumSupport.LargeGirth

open FiniteMultiGraph BoundaryDecay BoundaryTrace
open FiniteMultiGraph.SeedPairCorrelation FiniteMultiGraph.SeedFamilyAvoidance
open PolynomialBound.TwoLinkMoment

variable {ι : Type*} [DecidableEq ι]
variable (G : FiniteMultiGraph) (U : ι → Finset G.Vertex)
  (seed : ∀ i, G.internalCycleSpace (U i))

omit [DecidableEq ι] in
/-- Every forest on a containing edge set avoids all nonzero even seeds.
The comparison holds on the ambient uniform cycle space. -/
theorem forest_density_le_seed_avoidance (s : Finset ι) (E : Finset G.Edge)
    (hne : ∀ i ∈ s, (seed i).1 ≠ 0)
    (hE : ∀ i ∈ s, G.internalEdges (U i) ⊆ E) :
    Finite.density (fun x : G.CycleSpace => G.IsForestWord (G.restrictEdges E x.1)) ≤
      Finite.density (fun x : G.CycleSpace => ∀ i ∈ s, ¬ G.SelectedSeed (seed i).1 x) := by
  classical
  rw [← average_indicator, ← average_indicator]
  apply average_mono
  intro x
  by_cases hx : G.IsForestWord (G.restrictEdges E x.1)
  · have havoid : ∀ i ∈ s, ¬ G.SelectedSeed (seed i).1 x := by
      intro i hi hsel
      apply G.not_isForestWord_of_even_support (seed i).1 _
        (G.restrictEdges E x.1) _ hx
      · exact fun hz => hne i hi (Subtype.ext hz)
      · intro e he
        have heU : e ∈ G.internalEdges (U i) := by
          by_contra hn
          exact he ((seed i).2 e hn)
        simpa only [restrictEdges, hE i hi heU, ↓reduceIte] using hsel e he
    simp only [indicator, if_pos hx, if_pos havoid]
    rfl
  · simp only [indicator, if_neg hx]
    split_ifs <;> norm_num

/-- Convert the actual seed avoidance probability into total two-link weight. -/
theorem twoLink_weight_ge_two_fifths (s : Finset ι) (L : ℕ) (M b : ℝ)
    (hG : G.toSimpleGraph.Connected)
    (hconn : ∀ i ∈ s,
      ((G.selectedGraph (seed i).1.1).induce (↑(U i) : Set G.Vertex)).Connected)
    (htwo : ∀ i ∈ s, ∀ v ∈ U i, G.selectedDegree (seed i).1.1 v = 2)
    (hdegree : ∀ i ∈ s, ∀ v ∈ U i, G.degree v ≤ 3)
    (hinj : ∀ i ∈ s, ∀ j ∈ s, (seed i).1 = (seed j).1 → i = j)
    (hlen : ∀ i ∈ s, (U i).card ≤ L)
    (hM : 0 ≤ M) (hb : 0 ≤ b)
    (hload : ∀ v, (∑ i ∈ s, if v ∈ U i then weight G U seed i else 0) ≤ b)
    (hlinks : ∀ i ∈ s, ∀ j ∈ s, i ≠ j → Exceptional G U i j →
      dyadic ((Nat.card (Links G (U i) (U j)) : ℤ) - 1) ≤ M)
    (hzero : (2 / 5 : ℝ) ≤ Finite.density (fun x : G.CycleSpace =>
      ∀ i ∈ s, ¬ G.SelectedSeed (seed i).1 x)) :
    (2 / 3 : ℝ) * (∑ i ∈ s, weight G U seed i) ^ 2 -
        (1 + M * L * L * b) * (∑ i ∈ s, weight G U seed i) ≤
      ∑ i ∈ s, ∑ j ∈ s, twoLink G U i j *
        (weight G U seed i * weight G U seed j) := by
  classical
  have hz : (fun x : G.CycleSpace => ∀ i ∈ s, ¬ G.SelectedSeed (seed i).1 x) =
      fun x => (∑ i ∈ s, G.normalizedSeedIndicator (seed i).1 x) = 0 := by
    funext x
    apply propext
    rw [Finset.sum_eq_zero_iff_of_nonneg
      (fun i hi => (G.normalizedSeedIndicator_bounds (seed i).1 x).1)]
    apply forall₂_congr
    intro i hi
    exact (normalizedIndicator_eq_zero_iff _ _ (by positivity)
      (lt_of_lt_of_le (by positivity) (G.selectedSeed_probability_ge (seed i).1)) x).symm
  rw [hz] at hzero
  apply ExactMaximumSupport.Averaging.kernel_weight_ge_two_fifths (fun x => ∑ i ∈ s, G.normalizedSeedIndicator (seed i).1 x)
    _ _ _ ?_ ?_ hzero
  · simp only [average_sum, G.average_normalizedSeedIndicator, weight]
  · exact PolynomialBound.TwoLinkMoment.second_moment_le G U seed s L M b hG hconn htwo hdegree hinj hlen hM hb hload hlinks

/-- The two-link weight bound from a forest event on a containing edge set. -/
theorem twoLink_weight_ge_of_forest (s : Finset ι) (L : ℕ) (M b : ℝ)
    (hG : G.toSimpleGraph.Connected)
    (hconn : ∀ i ∈ s,
      ((G.selectedGraph (seed i).1.1).induce (↑(U i) : Set G.Vertex)).Connected)
    (htwo : ∀ i ∈ s, ∀ v ∈ U i, G.selectedDegree (seed i).1.1 v = 2)
    (hdegree : ∀ i ∈ s, ∀ v ∈ U i, G.degree v ≤ 3)
    (hinj : ∀ i ∈ s, ∀ j ∈ s, (seed i).1 = (seed j).1 → i = j)
    (hlen : ∀ i ∈ s, (U i).card ≤ L)
    (hM : 0 ≤ M) (hb : 0 ≤ b)
    (hload : ∀ v, (∑ i ∈ s, if v ∈ U i then weight G U seed i else 0) ≤ b)
    (hlinks : ∀ i ∈ s, ∀ j ∈ s, i ≠ j → Exceptional G U i j →
      dyadic ((Nat.card (Links G (U i) (U j)) : ℤ) - 1) ≤ M)
    (E : Finset G.Edge) (hne : ∀ i ∈ s, (seed i).1 ≠ 0)
    (hE : ∀ i ∈ s, G.internalEdges (U i) ⊆ E)
    (hforest : (2 / 5 : ℝ) ≤
      Finite.density (fun x : G.CycleSpace => G.IsForestWord (G.restrictEdges E x.1))) :
    (2 / 3 : ℝ) * (∑ i ∈ s, weight G U seed i) ^ 2 -
        (1 + M * L * L * b) * (∑ i ∈ s, weight G U seed i) ≤
      ∑ i ∈ s, ∑ j ∈ s, twoLink G U i j *
        (weight G U seed i * weight G U seed j) := by
  exact twoLink_weight_ge_two_fifths G U seed s L M b hG hconn htwo hdegree
    hinj hlen hM hb hload hlinks
    (hforest.trans (forest_density_le_seed_avoidance G U seed s E hne hE))

end Erdos1016.ExactMaximumSupport.LargeGirth
