import Erdos1016.Extremal.Capacity.CompositionProbability
import Erdos1016.Probability.Cylinders.ActiveCoordinateUniformity
import Erdos1016.Probability.Moments.PaleyZygmund

set_option autoImplicit false

noncomputable section
open scoped BigOperators

namespace Erdos1016.Proof.ActiveDegreeMoment

open Erdos1016
open Erdos1016.PhysicalGraph
open Erdos1016.Proof.ActiveEdgeUniform

/-- The expected number of selected edges from a finite family is the sum of
the individual selection probabilities. -/
def expectedSelectedFamilySize (G : PhysicalGraph) (F : Finset G.Edge) : ℝ :=
  ∑ e ∈ F, selectedDensity G e

/-- Every active edge has marginal probability one half, so the expected
number of selected edges in any finite family of active edges is half its
cardinality. No independence assumption is needed. -/
theorem expectedSelectedFamilySize_eq_half (G : PhysicalGraph)
    (F : Finset G.Edge) (hactive : ∀ e ∈ F, ActiveEdge G e) :
    expectedSelectedFamilySize G F = (F.card : ℝ) / 2 := by
  unfold expectedSelectedFamilySize
  calc
    (∑ e ∈ F, selectedDensity G e) = ∑ e ∈ F, (1 / 2 : ℝ) := by
      apply Finset.sum_congr rfl
      intro e he
      rw [selectedDensity_eq_half_of_active G e (hactive e he)]
    _ = (F.card : ℝ) / 2 := by norm_num [div_eq_mul_inv]

/-- The number of selected members of a family, viewed as a real random
variable on the uniform cycle space. -/
def selectedFamilyCount (G : PhysicalGraph) (F : Finset G.Edge)
    (x : G.CycleSpace) : ℝ :=
  ∑ e ∈ F, if x.1 e = 1 then 1 else 0

/-- The statewise count has expectation equal to the sum of edge marginals. -/
theorem mean_selectedFamilyCount_eq_expectedSelectedFamilySize
    (G : PhysicalGraph) (F : Finset G.Edge) :
    (∑ x : G.CycleSpace, selectedFamilyCount G F x) /
        (Fintype.card G.CycleSpace : ℝ) =
      expectedSelectedFamilySize G F := by
  classical
  have hsum : (∑ x : G.CycleSpace, selectedFamilyCount G F x) =
      ∑ e ∈ F,
        (Fintype.card {x : G.CycleSpace // x.1 e = 1} : ℝ) := by
    simp only [selectedFamilyCount]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro e he
    rw [Finset.sum_boole]
    rw [Fintype.card_subtype]
  have htotal : (Fintype.card G.CycleSpace : ℝ) =
      (2 : ℝ) ^ G.cycleRank := by
    exact_mod_cast G.cycleSpace_card
  rw [hsum, htotal]
  unfold expectedSelectedFamilySize selectedDensity
  rw [Finset.sum_div]
  congr 1
  funext e
  congr 1
  exact htotal.symm

/-- A family of edges contained in the complement and incident to `v` can
never have more selected edges than the restricted degree at `v`. -/
theorem selectedFamilyCount_le_restrictedDegree
    (G : PhysicalGraph) (E F : Finset G.Edge) (v : G.Vertex)
    (x : G.CycleSpace)
    (hF : ∀ e ∈ F, e ∈ Eᶜ ∧ G.incident e v) :
    selectedFamilyCount G F x ≤
      (G.restrictedSelectedDegree Eᶜ (G.restrictWord Eᶜ x.1) v : ℝ) := by
  classical
  have hcount : selectedFamilyCount G F x =
      ((F.filter fun e => x.1 e = 1).card : ℝ) := by
    unfold selectedFamilyCount
    rw [Finset.sum_boole]
  have hcard : (F.filter fun e => x.1 e = 1).card ≤
      (Finset.univ.filter fun e : G.RestrictedEdge Eᶜ =>
        G.restrictWord Eᶜ x.1 e ≠ 0 ∧ G.incident e.1 v).card := by
    let S := F.filter fun e => x.1 e = 1
    let T := Finset.univ.filter fun e : G.RestrictedEdge Eᶜ =>
      G.restrictWord Eᶜ x.1 e ≠ 0 ∧ G.incident e.1 v
    let f : {e // e ∈ S} → G.RestrictedEdge Eᶜ := fun e =>
      ⟨e.1, (hF e.1 (Finset.mem_filter.mp e.2).1).1⟩
    have hf : ∀ e ∈ (Finset.univ : Finset {e // e ∈ S}), f e ∈ T := by
      intro e he
      rcases Finset.mem_filter.mp e.2 with ⟨heF, heSelected⟩
      simp only [T, Finset.mem_filter, Finset.mem_univ, true_and]
      constructor
      · simpa [f, PhysicalGraph.restrictWord] using (show x.1 e.1 ≠ 0 from by
          rw [heSelected]
          norm_num)
      · exact (hF e.1 heF).2
    have hinj : Set.InjOn f (Finset.univ : Finset {e // e ∈ S}) := by
      intro e he f' hf' hef
      exact Subtype.ext
        (congrArg (fun z : G.RestrictedEdge Eᶜ => z.1) hef)
    have haux := Finset.card_le_card_of_injOn f hf hinj
    calc
      S.card = (Finset.univ : Finset {e // e ∈ S}).card := by simp
      _ ≤ T.card := haux
      _ = _ := rfl
  rw [hcount]
  unfold restrictedSelectedDegree
  exact_mod_cast hcard

/-- The active edges outside `E` incident to a marked vertex. -/
def outsideActiveIncidentEdges (G : PhysicalGraph) (E : Finset G.Edge)
    (v : G.Vertex) : Finset G.Edge := by
  classical
  exact Finset.univ.filter fun e => e ∈ Eᶜ ∧ G.incident e v ∧ ActiveEdge G e

/-- A nonnegative count with mean `n / 2`, bounded by `n`, has probability
at most `n / (2 (n - 2))` of being at most two. This elementary tail bound
is the numerical step behind the active-degree argument. -/
theorem probability_le_of_mean_half_and_bounded
    {Ω : Type*} [Fintype Ω] [Nonempty Ω]
    (Z : Ω → ℝ) (n : ℝ) (hn : 2 < n)
    (hmean : Erdos1016.Proof.FinitePaleyZygmund.mean Z = n / 2)
    (hhi : ∀ x, Z x ≤ n) :
    Erdos1016.Proof.FinitePaleyZygmund.probability (fun x => Z x ≤ 2) ≤
      n / (2 * (n - 2)) := by
  classical
  let N : ℝ := Fintype.card Ω
  let low : Finset Ω := Finset.univ.filter (fun x => Z x ≤ 2)
  let high : Finset Ω := Finset.univ.filter (fun x => ¬ Z x ≤ 2)
  have hN : 0 < N := by
    dsimp [N]
    exact_mod_cast Fintype.card_pos_iff.mpr ‹Nonempty Ω›
  have hmean_sum : (∑ x, Z x) = (n / 2) * N := by
    have hm := hmean
    dsimp [Erdos1016.Proof.FinitePaleyZygmund.mean, N] at hm
    exact (div_eq_iff (by positivity : (Fintype.card Ω : ℝ) ≠ 0)).1 hm
  have hlow : (∑ x ∈ low, Z x) ≤ 2 * (low.card : ℝ) := by
    calc
      (∑ x ∈ low, Z x) ≤ ∑ x ∈ low, (2 : ℝ) := by
        apply Finset.sum_le_sum
        intro x hx
        exact (Finset.mem_filter.mp hx).2
      _ = 2 * (low.card : ℝ) := by simp [mul_comm]
  have hhigh : (∑ x ∈ high, Z x) ≤ n * (high.card : ℝ) := by
    calc
      (∑ x ∈ high, Z x) ≤ ∑ x ∈ high, n := by
        apply Finset.sum_le_sum
        intro x hx
        exact hhi x
      _ = n * (high.card : ℝ) := by simp [mul_comm]
  have hsplit : (∑ x ∈ low, Z x) + (∑ x ∈ high, Z x) = ∑ x, Z x := by
    simpa [low, high] using
      (Finset.sum_filter_add_sum_filter_not Finset.univ
        (fun x => Z x ≤ 2) Z)
  have hcard : (low.card : ℝ) + (high.card : ℝ) = N := by
    dsimp [N, low, high]
    rw [Finset.card_filter, Finset.card_filter]
    push_cast
    rw [← Finset.sum_add_distrib]
    calc
      (∑ x : Ω, ((if Z x ≤ 2 then (1 : ℝ) else 0) +
          (if ¬ Z x ≤ 2 then 1 else 0))) = ∑ _x : Ω, (1 : ℝ) := by
        apply Finset.sum_congr rfl
        intro x hx
        by_cases h : Z x ≤ 2 <;> simp [h]
      _ = (Fintype.card Ω : ℝ) := by simp
  have hmass : (n - 2) * (low.card : ℝ) ≤ (n / 2) * N := by
    nlinarith [hmean_sum, hlow, hhigh, hsplit, hcard]
  have hprob : Erdos1016.Proof.FinitePaleyZygmund.probability
      (fun x => Z x ≤ 2) = (low.card : ℝ) / N := by
    simp [Erdos1016.Proof.FinitePaleyZygmund.probability, low, N]
  rw [hprob]
  have hnm2 : 0 < n - 2 := by linarith
  apply (div_le_div_iff₀ hN (by positivity : 0 < 2 * (n - 2))).2
  nlinarith [hmass]

/-- If every state in an event selects at most two edges from an active
family, its probability is bounded by the half-mean tail estimate. -/
theorem activeFamily_event_probability_le (G : PhysicalGraph)
    (E : Finset G.Edge) (F : Finset G.Edge)
    (hactive : ∀ e ∈ F, ActiveEdge G e) (hcard : 2 < F.card)
    (hsmall : ∀ x ∈ G.outsideLinearForestStates E,
      selectedFamilyCount G F x ≤ 2) :
    G.outsideLinearForestProbability E ≤
      (F.card : ℝ) / (2 * ((F.card : ℝ) - 2)) := by
  classical
  have hmean : Erdos1016.Proof.FinitePaleyZygmund.mean
      (selectedFamilyCount G F) = (F.card : ℝ) / 2 := by
    unfold Erdos1016.Proof.FinitePaleyZygmund.mean
    rw [mean_selectedFamilyCount_eq_expectedSelectedFamilySize]
    rw [expectedSelectedFamilySize_eq_half G F hactive]
  have hbound : ∀ x : G.CycleSpace,
      selectedFamilyCount G F x ≤ (F.card : ℝ) := by
    intro x
    unfold selectedFamilyCount
    calc
      (∑ e ∈ F, if x.1 e = 1 then (1 : ℝ) else 0) ≤
          ∑ e ∈ F, (1 : ℝ) := by
            apply Finset.sum_le_sum
            intro e he
            split_ifs <;> norm_num
      _ = (F.card : ℝ) := by simp
  have htail := probability_le_of_mean_half_and_bounded
    (selectedFamilyCount G F) (F.card : ℝ)
    (by exact_mod_cast hcard) hmean hbound
  have hsubset : G.outsideLinearForestStates E ⊆
      Finset.univ.filter (fun x : G.CycleSpace =>
        selectedFamilyCount G F x ≤ 2) := by
    intro x hx
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hsmall x hx⟩
  have hprob : G.outsideLinearForestProbability E ≤
      Erdos1016.Proof.FinitePaleyZygmund.probability
        (fun x : G.CycleSpace => selectedFamilyCount G F x ≤ 2) := by
    unfold Erdos1016.PhysicalGraph.outsideLinearForestProbability
      Erdos1016.Proof.FinitePaleyZygmund.probability
    have hden : (2 : ℝ) ^ G.cycleRank =
        (Fintype.card G.CycleSpace : ℝ) := by
      exact_mod_cast G.cycleSpace_card.symm
    rw [hden]
    exact div_le_div_of_nonneg_right
      (by exact_mod_cast Finset.card_le_card hsubset) (by positivity)
  exact hprob.trans (by simpa using htail)

/-- If the outside linear-forest event has probability above `1/2 + 1/R`,
then any active family that has at most two selected members throughout that
event has size at most `R + 1`. -/
theorem activeFamily_card_le_of_outsideForest_probability_gt
    (G : PhysicalGraph) (E : Finset G.Edge) (F : Finset G.Edge)
    (R : ℕ) (hR : 0 < R)
    (hactive : ∀ e ∈ F, ActiveEdge G e)
    (hsmall : ∀ x ∈ G.outsideLinearForestStates E,
      selectedFamilyCount G F x ≤ 2)
    (hprob : (1 / 2 : ℝ) + 1 / (R : ℝ) <
      G.outsideLinearForestProbability E) :
    F.card ≤ R + 1 := by
  by_contra hnot
  have hlarge : R + 2 ≤ F.card := by omega
  have hcard : 2 < F.card := by omega
  have htail := activeFamily_event_probability_le G E F hactive hcard hsmall
  have hRpos : (0 : ℝ) < (R : ℝ) := by exact_mod_cast hR
  have hn : (2 : ℝ) < (F.card : ℝ) := by exact_mod_cast hcard
  have hRle : (R : ℝ) ≤ (F.card : ℝ) - 2 := by
    have hcast : ((R + 2 : ℕ) : ℝ) ≤ (F.card : ℝ) := by exact_mod_cast hlarge
    norm_num at hcast ⊢
    linarith
  have hrecip : 1 / ((F.card : ℝ) - 2) ≤ 1 / (R : ℝ) :=
    one_div_le_one_div_of_le hRpos hRle
  have hidentity : (F.card : ℝ) / (2 * ((F.card : ℝ) - 2)) =
      (1 / 2 : ℝ) + 1 / ((F.card : ℝ) - 2) := by
    have hnm2 : 0 < (F.card : ℝ) - 2 := by linarith
    field_simp [ne_of_gt hnm2]
  rw [hidentity] at htail
  linarith



end Erdos1016.Proof.ActiveDegreeMoment
