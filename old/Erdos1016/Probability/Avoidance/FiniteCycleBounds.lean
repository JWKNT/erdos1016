import Erdos1016.Probability.Conditional.VertexLoads

set_option autoImplicit false

/-!
# Finite MANY and FEW probability bounds for actual cycle families

The geometry appears as the manuscript's explicit original-complement and
inter-cycle-edge hypotheses. SINGLE and JOINT probabilities, incompatible
overlaps, covariance sums, and the zero-event estimate are all proved by the
imported modules, rather than entered as separate probability assumptions.

This is NOT the full boundary-average decay theorem: constructing suitable
cycle families from expansion and deficit remains the analytic supply step.
-/

noncomputable section
open scoped BigOperators
namespace Erdos1016.BoundaryDecay

open BoundaryTrace SafeCore
local instance finiteDecayDecidable (p : Prop) : Decidable p := Classical.propDecidable p

variable {G : PhysicalGraph}

/-- The law of this function is the full owner cycle space. -/
theorem forest_fraction_le_no_cycle_events (U : Finset G.Vertex)
    (F : Finset G.CycleWord) (hF : ∀ C ∈ F, Cycle.vertices C ⊆ U) :
    G.originalForestFraction U ≤
      Finite.density (fun x : G.CycleSpace => ∀ C ∈ F, ¬ Cycle.Event C x) := by
  unfold PhysicalGraph.originalForestFraction Finite.density
  apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
  apply Finite.count_mono
  intro x hx C hC hEvent
  exact Cycle.event_not_forest_restriction C x hEvent U (hF C hC) hx

/-- MANY, finite form (4.5), once the actual nonconflicting subfamily has
been chosen. No factor comes from selecting successful states. -/
theorem forest_fraction_le_many (hG : G.IsConnected)
    (U : Finset G.Vertex) (F : Finset G.CycleWord) (hFne : F.Nonempty)
    (hFU : ∀ C ∈ F, Cycle.vertices C ⊆ U)
    (D : ℕ) (hD : ∀ C ∈ F, Cycle.length C ≤ D)
    (hc : ∀ C ∈ F, ∀ v ∈ Cycle.vertices C, G.degree v = 3)
    (v₀ : G.Vertex) (hv₀ : ∀ C ∈ F, v₀ ∉ Cycle.vertices C)
    (hpair : ∀ C ∈ F, ∀ C' ∈ F, C ≠ C' →
      Disjoint (Cycle.vertices C) (Cycle.vertices C') ∧
      crossSize G (Cycle.vertices C) (Cycle.vertices C') = 0 ∧
      G.originalExteriorComponents (Cycle.vertices C ∪ Cycle.vertices C') + 1 =
        G.originalExteriorComponents (Cycle.vertices C) +
          G.originalExteriorComponents (Cycle.vertices C')) :
    G.originalForestFraction U ≤ (2 : ℝ) ^ D / F.card := by
  have hprob : ∀ C ∈ F, 1 / (2 : ℝ) ^ D ≤ Cycle.probability C := by
    intro C hC
    exact Cycle.probability_ge_inverse_pow hG C (hc C hC) v₀ (hv₀ C hC) D (hD C hC)
  have hmass : (F.card : ℝ) / (2 : ℝ) ^ D ≤ eventMass F Cycle.Event := by
    have h := Finset.sum_le_sum hprob
    simpa [eventMass, Cycle.probability, div_eq_mul_inv] using h
  have hcard : (0 : ℝ) < F.card := by exact_mod_cast Finset.card_pos.2 hFne
  have hpow : (0 : ℝ) < (2 : ℝ) ^ D := by positivity
  have hm : 0 < eventMass F Cycle.Event := (div_pos hcard hpow).trans_le hmass
  have hpairs : ∀ C ∈ F, ∀ C' ∈ F, C ≠ C' →
      Finite.density (fun x => Cycle.Event C x ∧ Cycle.Event C' x) ≤
        Finite.density (Cycle.Event C) * Finite.density (Cycle.Event C') := by
    intro C hC C' hC' hne
    obtain ⟨hd, he, hn⟩ := hpair C hC C' hC' hne
    exact (Cycle.pairwise_probability_of_nonconflict hG C C' hd
      (hc C hC) (hc C' hC') he hn).le
  calc
    G.originalForestFraction U ≤
        Finite.density (fun x : G.CycleSpace => ∀ C ∈ F, ¬ Cycle.Event C x) :=
      forest_fraction_le_no_cycle_events U F hFU
    _ ≤ 1 / eventMass F Cycle.Event :=
      no_events_density_le_inverse_mass F Cycle.Event hm hpairs
    _ ≤ 1 / ((F.card : ℝ) / (2 : ℝ) ^ D) :=
      one_div_le_one_div_of_le (div_pos hcard hpow) hmass
    _ = (2 : ℝ) ^ D / F.card := by field_simp [ne_of_gt hcard, ne_of_gt hpow]

/-- The covariance error is charged only when an ACTUAL edge joins supports.
Two supports both incident with a common apex are not automatically adjacent. -/
def cyclePairError (K : ℕ) (C D : G.CycleWord) : ℝ :=
  if Touch G.toSimpleGraph.Adj (Cycle.vertices C) (Cycle.vertices D) then
    (2 : ℝ) ^ K * Cycle.probability C * Cycle.probability D else 0







def cycleWeight (C : G.CycleWord) : ℝ := 1 / (2 : ℝ) ^ Cycle.length C

def cycleWeightSum (F : Finset G.CycleWord) : ℝ := ∑ C ∈ F, cycleWeight C









end Erdos1016.BoundaryDecay
