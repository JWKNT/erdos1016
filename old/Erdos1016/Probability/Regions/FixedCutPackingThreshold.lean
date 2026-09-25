import Erdos1016.Probability.Regions.LogarithmicCutoff

set_option autoImplicit false

/-!
# Fixed-cut quadratic bound for the many-region threshold

The moving threshold in Section 8 becomes quadratic in `R` whenever the
outgoing-cut bound is fixed. This is the estimate used for the double-edge
protection count in the Section 10 cleanup.
-/

namespace Erdos1016.Proof.ManyRegionsLogCutoff

/-- Number of regions required by the paper's second-moment threshold. -/
def movingRegionThreshold (R d : ℕ) : ℕ :=
  8 * R * 2 ^ d * (1 + 2 ^ (2 * d) + cutoff R)

/-- The fixed-cut coefficient in the quadratic bound. -/
def fixedCutCoefficient (d : ℕ) : ℕ :=
  8 * 2 ^ d * (2 + 2 ^ (2 * d))

/-- For each fixed cut bound, the moving many-region threshold is at most a
fixed constant times `R^2`. -/
theorem movingRegionThreshold_le_quadratic (R d : ℕ) (hR : 5 ≤ R) :
    movingRegionThreshold R d ≤ fixedCutCoefficient d * R ^ 2 := by
  have hcut := cutoff_le R hR
  have hfactor : 1 + 2 ^ (2 * d) + cutoff R ≤
      (2 + 2 ^ (2 * d)) * R := by
    have hR1 : 1 ≤ R := by omega
    have h2R : 1 + R ≤ 2 * R := by omega
    have hpowR : 2 ^ (2 * d) ≤ 2 ^ (2 * d) * R := by
      calc
        2 ^ (2 * d) = 2 ^ (2 * d) * 1 := by simp
        _ ≤ 2 ^ (2 * d) * R := Nat.mul_le_mul_left _ hR1
    calc
      1 + 2 ^ (2 * d) + cutoff R ≤ 1 + 2 ^ (2 * d) + R := by
        exact Nat.add_le_add_left hcut _
      _ = (1 + R) + 2 ^ (2 * d) := by omega
      _ ≤ 2 * R + 2 ^ (2 * d) := Nat.add_le_add_right h2R _
      _ ≤ 2 * R + 2 ^ (2 * d) * R := Nat.add_le_add_left hpowR _
      _ = (2 + 2 ^ (2 * d)) * R := by ring
  unfold movingRegionThreshold fixedCutCoefficient
  calc
    8 * R * 2 ^ d * (1 + 2 ^ (2 * d) + cutoff R) ≤
        8 * R * 2 ^ d * ((2 + 2 ^ (2 * d)) * R) := by
          exact Nat.mul_le_mul_left (8 * R * 2 ^ d) hfactor
    _ = 8 * 2 ^ d * (2 + 2 ^ (2 * d)) * R ^ 2 := by ring



end Erdos1016.Proof.ManyRegionsLogCutoff
