import Erdos1016.Nonbacktracking.Entropy.EntropyGrowth

set_option autoImplicit false

/-!
# The finite entropy/counting side of the Moore bounds

These lemmas use the actual physical run set and its actual endpoint map.
Their injectivity hypothesis is EXPLICIT: the separate theorem deriving
short-walk injectivity from girth is not claimed here. Once it is supplied,
these are the logarithmic inequalities in source §§7.1--7.2.
-/
noncomputable section
namespace Erdos1016.Nonbacktracking
open scoped BigOperators
local instance entropyMooreDecidable (p : Prop) : Decidable p := Classical.propDecidable p

variable (G : PhysicalGraph)

/-- An injective actual endpoint map bounds walks by the square of the order. -/
theorem allRunCount_le_order_sq (k : ℕ)
    (hu : Function.Injective (endpoints G k)) :
    allRunCount G k ≤ G.vertexCount ^ 2 := by
  have h := Fintype.card_le_of_injective (endpoints G k) hu
  simpa [card_allRuns, Fintype.card_prod, pow_two] using h

/-- Finite stationary-entropy bound from uniqueness of short endpoint walks.
`k` transitions means `k+1` graph edges, so the exponent is exactly `k`. -/
theorem endpoint_injective_entropy_bound
    (hmin : ∀ v, 2 ≤ G.degree v) (hn : 0 < G.vertexCount)
    (k : ℕ) (hu : Function.Injective (endpoints G k)) :
    (k : ℝ) * meanLogBranching G ≤ Real.logb 2 ((G.vertexCount : ℝ) / 2) := by
  have hm := edgeCount_pos_of_min_two G hmin hn
  have hn' : (0 : ℝ) < G.vertexCount := by exact_mod_cast hn
  have hs : 2 * G.vertexCount ≤ ∑ v : G.Vertex, G.degree v := by
    calc
      _ = ∑ _v : G.Vertex, (2 : ℕ) := by simp [Nat.mul_comm]
      _ ≤ _ := Finset.sum_le_sum (fun v _ => hmin v)
  rw [physical_degree_sum] at hs
  have hmn : G.vertexCount ≤ G.edgeCount := by omega
  have hmn' : (G.vertexCount : ℝ) ≤ G.edgeCount := by exact_mod_cast hmn
  have hl := allRunCount_entropy_lower G hmin hm k
  have hu' : (allRunCount G k : ℝ) ≤ (G.vertexCount : ℝ) ^ 2 := by
    exact_mod_cast allRunCount_le_order_sq G k hu
  have hx : 0 < (2 : ℝ) ^ ((k : ℝ) * meanLogBranching G) :=
    Real.rpow_pos_of_pos (by norm_num) _
  have hmul : 2 * (G.vertexCount : ℝ) *
      (2 : ℝ) ^ ((k : ℝ) * meanLogBranching G) ≤
      2 * (G.edgeCount : ℝ) * (2 : ℝ) ^ ((k : ℝ) * meanLogBranching G) := by
    gcongr
  have hpow : (2 : ℝ) ^ ((k : ℝ) * meanLogBranching G) ≤
      (G.vertexCount : ℝ) / 2 := by
    have hh : (G.vertexCount : ℝ) *
        (2 * (2 : ℝ) ^ ((k : ℝ) * meanLogBranching G)) ≤
        (G.vertexCount : ℝ) * G.vertexCount := by
      nlinarith [hmul.trans (hl.trans hu')]
    have hc := (mul_le_mul_left hn').mp hh
    linarith
  exact (Real.le_logb_iff_rpow_le (by norm_num : (1 : ℝ) < 2)
    (div_pos hn' (by norm_num))).mpr hpow






/-- The elementary rearrangement behind the high-girth deficit estimate.
If the entropy loss from a deficit `k` is bounded after `u` steps, and the
logarithmic order term is strictly below `u`, then the order is bounded by
the deficit times the displayed amplification factor. -/
theorem order_le_deficit_factor {v k u ell : ℝ}
    (hkv : k < v) (hlu : ell < u)
    (hentropy : u * (1 - k / (v - k)) ≤ ell) :
    v ≤ k * (1 + u / (u - ell)) := by
  have hden : 0 < v - k := sub_pos.mpr hkv
  have hratio : 1 - k / (v - k) = (v - k - k) / (v - k) := by
    field_simp [ne_of_gt hden]
  rw [hratio] at hentropy
  have hquot : (u * (v - k - k)) / (v - k) ≤ ell := by
    convert hentropy using 1 <;> ring
  have hmul : u * (v - k - k) ≤ ell * (v - k) :=
    (div_le_iff₀ hden).1 hquot
  have hprod : (u - ell) * (v - k) ≤ u * k := by nlinarith [hmul]
  have hquot' : v - k ≤ (u * k) / (u - ell) :=
    (le_div_iff₀ (sub_pos.mpr hlu)).2 (by nlinarith [hprod])
  calc
    v = k + (v - k) := by ring
    _ ≤ k + (u * k) / (u - ell) := add_le_add_left hquot' k
    _ = k * (1 + u / (u - ell)) := by ring


end Erdos1016.Nonbacktracking
