import Erdos1016.Extremal.Recurrence.QuarticDecay
import Erdos1016.Graph.PancyclicRank

set_option autoImplicit false

/-!
# Tail capacity for the extremal initial-coverage function

This file formalizes the tail supremum from §2. It proves its elementary
boundedness and monotonicity, and supplies those facts to the generic
quartic-recurrence theorem. The near-halving recurrence itself is deliberately
left as a hypothesis: its derivation from the graph argument is still open.
-/

noncomputable section
namespace Erdos1016.Extremal
open Filter
open scoped Topology

/-- The normalized excess of the initial coverage extremum. -/
def initialCapacityExcess (r : ℕ) : ℝ :=
  ((initialCapacity r : ℝ) - 2) / (2 : ℝ) ^ r

lemma initialCapacityExcess_nonneg (r : ℕ) : 0 ≤ initialCapacityExcess r := by
  have hI : 2 ≤ initialCapacity r := initialCapacity_two_le r
  have hden : 0 < (2 : ℝ) ^ r := by positivity
  unfold initialCapacityExcess
  exact div_nonneg (by exact_mod_cast (show (0 : ℕ) ≤ initialCapacity r - 2 by omega))
    (le_of_lt hden)

lemma initialCapacityExcess_le_one (r : ℕ) : initialCapacityExcess r ≤ 1 := by
  have hI : 2 ≤ initialCapacity r := initialCapacity_two_le r
  have hnumNat : initialCapacity r - 2 ≤ 2 ^ r := by
    have hb := initialCapacity_le r
    omega
  have hnumCast : ((initialCapacity r - 2 : ℕ) : ℝ) ≤ (2 : ℝ) ^ r := by
    exact_mod_cast hnumNat
  have hnum : ((initialCapacity r : ℝ) - 2) ≤ (2 : ℝ) ^ r := by
    simpa [Nat.cast_sub hI] using hnumCast
  have hden : 0 < (2 : ℝ) ^ r := by positivity
  unfold initialCapacityExcess
  exact (div_le_iff₀ hden).2 (by nlinarith)

/-- The tail capacity `sup_{r ≥ R} (I(r)-2)/2^r` from the paper. -/
def tailCapacity (R : ℕ) : ℝ :=
  sSup {x : ℝ | ∃ r : ℕ, R ≤ r ∧ x = initialCapacityExcess r}

private lemma tailCapacity_set_bddAbove (R : ℕ) :
    BddAbove {x : ℝ | ∃ r : ℕ, R ≤ r ∧ x = initialCapacityExcess r} := by
  refine ⟨1, ?_⟩
  rintro x ⟨r, _, rfl⟩
  exact initialCapacityExcess_le_one r

private lemma tailCapacity_set_nonempty (R : ℕ) :
    ({x : ℝ | ∃ r : ℕ, R ≤ r ∧ x = initialCapacityExcess r}).Nonempty := by
  exact ⟨initialCapacityExcess R, ⟨R, le_rfl, rfl⟩⟩

theorem tailCapacity_bounds (R : ℕ) : 0 ≤ tailCapacity R ∧ tailCapacity R ≤ 1 := by
  constructor
  · unfold tailCapacity
    calc
      0 ≤ initialCapacityExcess R := initialCapacityExcess_nonneg R
      _ ≤ sSup {x : ℝ | ∃ r : ℕ, R ≤ r ∧ x = initialCapacityExcess r} :=
        le_csSup (tailCapacity_set_bddAbove R) ⟨R, le_rfl, rfl⟩
  · unfold tailCapacity
    apply csSup_le (tailCapacity_set_nonempty R)
    rintro x ⟨r, _, rfl⟩
    exact initialCapacityExcess_le_one r

theorem tailCapacity_antitone {a b : ℕ} (hab : a ≤ b) :
    tailCapacity b ≤ tailCapacity a := by
  unfold tailCapacity
  apply csSup_le_csSup
  · exact tailCapacity_set_bddAbove a
  · exact tailCapacity_set_nonempty b
  · rintro x ⟨r, hbr, rfl⟩
    exact ⟨r, hab.trans hbr, rfl⟩





/-- If the paper's quartic near-halving recurrence is proved for this tail
capacity, the generic recurrence argument gives its log-star decay bound.
The recurrence premise is intentionally explicit rather than asserted here. -/
theorem initialCapacity_tail_logStar_bound
    (C Rmin : ℕ) (hC : 1 ≤ C)
    (hrec : ∀ R, Rmin ≤ R →
      tailCapacity (2 ^ (C * R ^ 4)) ≤
        ((1 / 2 : ℝ) + 1 / (R : ℝ)) * tailCapacity R +
          (2 : ℝ) ^ (2 - (R : ℝ))) :
    ∃ K : ℝ, 0 < K ∧ ∀ r : ℕ,
      tailCapacity r ≤ K / (2 : ℝ) ^ logStar r := by
  exact quartic_exponential_recurrence_logStar_bound C Rmin hC tailCapacity
    tailCapacity_bounds (by
      intro a b hab
      exact tailCapacity_antitone hab) hrec

end Erdos1016.Extremal
