import Erdos1016.Probability.Avoidance.CutoffAvoidance
import Erdos1016.Cycles.Selection.LogarithmicRetainedMass
import Erdos1016.Cycles.Selection.CollisionSurvivalLimits

set_option autoImplicit false
set_option maxHeartbeats 800000

/-!
# Exact manuscript cutoffs using only the proved even trace estimate

A smaller absolute selection target retains the same cutoff geometry and
conditional error bounds. This yields the universal coefficient `σ/128`
without needing the stronger paired spectral estimate.
-/

noncomputable section
open Filter
open scoped Topology
namespace Erdos1016.Proof.EvenTraceParameters
open CutoffAvoidance CutoffLimits
open ReturnSurvivalLimits
open CollisionSurvivalLimits

/-- Target supported by the existing even trace theorem and two half-survival
bounds. It is a deterministic function of the ambient graph order. -/
def evenTraceTarget (σ x : ℝ) : ℝ :=
  (1 / 64 : ℝ) * Real.log ((cutoffL σ x : ℝ) / (traceStart x : ℝ)) - 1

theorem evenTraceTarget_bounds {σ x : ℝ} (hσ : 0 < σ) (hx : 1 ≤ x)
    (hlarge : 4 ≤ (2 : ℝ) ^ (σ * Real.sqrt x)) :
    meanFloor (σ / 32) x ≤ evenTraceTarget σ x ∧
      evenTraceTarget σ x + 1 ≤ σ * Real.sqrt x := by
  have hb := selectionTarget_bounds hσ hx hlarge
  have hlogx := Real.log_nonneg hx
  have heq : evenTraceTarget σ x = selectionTarget σ x / 32 - 31 / 32 := by
    dsimp [evenTraceTarget, selectionTarget]
    ring
  rw [heq]
  constructor
  · dsimp [meanFloor] at hb ⊢
    nlinarith [hb.1]
  · have hσs : 0 ≤ σ * Real.sqrt x := by positivity
    linarith [hb.2]

theorem selected_mean_bounds {σ x lam : ℝ} (hσ : 0 < σ) (hx : 1 ≤ x)
    (hlarge : 4 ≤ (2 : ℝ) ^ (σ * Real.sqrt x))
    (hlow : evenTraceTarget σ x ≤ lam)
    (hhigh : lam ≤ evenTraceTarget σ x + 1 / (2 : ℝ) ^ (cutoffD x + 1)) :
    meanFloor (σ / 32) x ≤ lam ∧ lam ≤ σ * Real.sqrt x := by
  have hb := evenTraceTarget_bounds hσ hx hlarge
  have hover : 1 / (2 : ℝ) ^ (cutoffD x + 1) ≤ 1 := by
    apply (div_le_one (by positivity)).mpr
    exact one_le_pow₀ (by norm_num)
  exact ⟨hb.1.trans hlow, by linarith [hb.2]⟩

/-- Uniform probability decay for the actual paper cutoffs and the smaller
mean furnished by even trace. The threshold is independent of the graph. -/
theorem even_trace_cutoffs_avoidance_rate
    (σ : ℝ) (hσ : 0 < σ) (hσ20 : σ < 1 / 20)
    (x : ℕ → ℝ) (hx : Tendsto x atTop atTop) :
    ∀ᶠ j in atTop, ∀ (μ lam d : ℝ),
      evenTraceTarget σ (x j) ≤ lam →
      lam ≤ evenTraceTarget σ (x j) + 1 / (2 : ℝ) ^ (cutoffD (x j) + 1) →
      0 ≤ d → d ≤ cutoffLoad σ (x j) →
      μ ≤ Real.exp (-lam) + lam ^ (momentK σ (x j) + 1) /
          ((momentK σ (x j) + 1).factorial : ℝ) +
        d * lam * Real.exp (lam + (Nat.choose (momentK σ (x j)) 2 : ℝ) * d / lam) →
      μ ≤ (2 : ℝ) ^ (-(σ / 128) * Real.sqrt (x j)) := by
  let c : ℝ := Real.log 2 / 5
  have hc : 0 < c := by dsimp [c]; positivity
  have hsqrt := sqrt_tendsto_atTop x hx
  have hmean := meanFloor_tendsto_atTop (σ / 32) (by positivity) x hx
  have hload := cutoffLoad_le_exp_power_eventually σ hσ hσ20 x hx
  have habsorb := QuantitativeAvoidance.three_exp_neg_le_base_two_stretched
    x (fun j => meanFloor (σ / 32) (x j)) (σ / 32) 3 hx (by positivity)
    (Eventually.of_forall (fun j => le_refl _))
  filter_upwards [hx.eventually_ge_atTop 1, hsqrt.eventually_ge_atTop 4,
      hsqrt.eventually_ge_atTop (8 / c), hsqrt.eventually_ge_atTop (2 / σ),
      hmean.eventually_ge_atTop 1, hload, habsorb]
    with j hxj hs4 hsc hsσ hmeanj hloadj habsorbj
  intro μ lam d hlamLow hlamHigh hd hdUpper hfinite
  have hlarge : 4 ≤ (2 : ℝ) ^ (σ * Real.sqrt (x j)) := by
    have hσs : 2 ≤ σ * Real.sqrt (x j) := by
      have h := (div_le_iff₀ hσ).mp hsσ
      nlinarith
    have h := Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 2) hσs
    norm_num at h ⊢
    exact h
  have hlam := selected_mean_bounds hσ hxj hlarge hlamLow hlamHigh
  have hlamOne : 1 ≤ lam := hmeanj.trans hlam.1
  have hlamSqrt : lam ≤ Real.sqrt (x j) := by
    calc
      _ ≤ σ * Real.sqrt (x j) := hlam.2
      _ ≤ 1 * Real.sqrt (x j) :=
        mul_le_mul_of_nonneg_right (by linarith : σ ≤ 1) (Real.sqrt_nonneg _)
      _ = _ := one_mul _
  have hK := momentK_bounds hσ hσ20 hs4
  have hKMean : 8 * lam ≤ ((momentK σ (x j) + 1 : ℕ) : ℝ) := by
    push_cast
    have hσs0 : 0 ≤ σ * Real.sqrt (x j) := by positivity
    nlinarith [hlam.2, hK.1]
  have hcSqrt : 8 ≤ c * Real.sqrt (x j) := by
    have h := (div_le_iff₀ hc).mp hsc
    nlinarith
  have hrelative := QuantitativeAvoidance.relative_error_le_one_of_exp_decay
    (momentK σ (x j)) (by linarith : 0 ≤ x j) hc (by linarith) hcSqrt
    hlamOne hlamSqrt hK.2 hd (hdUpper.trans hloadj)
  have havoid := QuantitativeAvoidance.poisson_bound_le_three_exp_neg
    (momentK σ (x j)) (by linarith : 0 ≤ lam) hKMean hrelative hfinite
  calc
    μ ≤ 3 * Real.exp (-lam) := havoid
    _ ≤ 3 * Real.exp (-meanFloor (σ / 32) (x j)) := by
      gcongr
      exact hlam.1
    _ ≤ (2 : ℝ) ^ (-(σ / 128) * Real.sqrt (x j)) := by convert habsorbj using 1 <;> congr 2 <;> ring


/-- Numerical retained-family budgets hold simultaneously at one onset.
The proof uses the actual cutoff asymptotics, including the growing return
radius, rather than fixing any of these integer parameters. -/
theorem retained_cutoff_budgets
    (σ : ℝ) (hσ : 0 < σ) (hσ20 : σ < 1 / 20)
    (x : ℕ → ℝ) (hx : Tendsto x atTop atTop) :
    ∀ᶠ j in atTop,
      12 ≤ x j ∧ 0 ≤ evenTraceTarget σ (x j) ∧
      traceStart (x j) ≤ cutoffL σ (x j) ∧
      2 * cutoffS (x j) ≤ cutoffD (x j) ∧ 0 < cutoffS (x j) ∧
      cutoffQ σ (x j) ≤ cutoffL σ (x j) ∧
      (9 / 4 : ℝ) * (cutoffL σ (x j) : ℝ) ^ 2 *
        (1 / 2 : ℝ) ^ cutoffS (x j) ≤ 1 / 2 ∧
      (9 / 2 : ℝ) * (2 : ℝ) ^ cutoffQ σ (x j) *
        (cutoffL σ (x j) : ℝ) ^ 3 * (1 / 2 : ℝ) ^ cutoffS (x j) ≤ 1 / 2 := by
  have hcol := cutoff_collision_error_tendsto_zero σ hσ hσ20 x hx
  have hret := cutoff_return_error_tendsto_zero σ hσ hσ20 x hx
  have hq := cutoffQ_ratio_tendsto σ hσ x hx
  have hqcoeff : 20 * σ ^ 2 < 1 := by nlinarith
  have hsqrt := sqrt_tendsto_atTop x hx
  have hmean := meanFloor_tendsto_atTop (σ / 32) (by positivity) x hx
  filter_upwards [hx.eventually_ge_atTop 12, hsqrt.eventually_ge_atTop (2 / σ),
      hmean.eventually_ge_atTop 0, hq.eventually_lt_const hqcoeff,
      hcol.eventually_lt_const (by norm_num : (0 : ℝ) < 1 / 2),
      hret.eventually_lt_const (by norm_num : (0 : ℝ) < 1 / 2)]
    with j hxj hsσ hm hqj hc hr
  have hxpos : 0 < x j := by linarith
  have hxone : 1 ≤ x j := by linarith
  have hσs : 2 ≤ σ * Real.sqrt (x j) := by
    have h := (div_le_iff₀ hσ).mp hsσ
    nlinarith
  have hlarge : 4 ≤ (2 : ℝ) ^ (σ * Real.sqrt (x j)) := by
    have h := Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 2) hσs
    norm_num at h ⊢
    exact h
  have ht := hm.trans (evenTraceTarget_bounds hσ hxone hlarge).1
  have hM := traceStart_bounds hxone
  have hMpos : 0 < (traceStart (x j) : ℝ) := by linarith [hM.1]
  have hLpos : 0 < cutoffL σ (x j) := by dsimp [cutoffL, largestOddCutoff]; omega
  have hratio : 1 ≤ (cutoffL σ (x j) : ℝ) / (traceStart (x j) : ℝ) := by
    apply (Real.log_nonneg_iff (by positivity)).mp
    dsimp [evenTraceTarget] at ht
    linarith
  have hMLr : (traceStart (x j) : ℝ) ≤ cutoffL σ (x j) :=
    (one_le_div hMpos).mp hratio
  have hML : traceStart (x j) ≤ cutoffL σ (x j) := by exact_mod_cast hMLr
  have hqxr : (cutoffQ σ (x j) : ℝ) ≤ x j := (div_le_one hxpos).mp hqj.le
  have hqL : cutoffQ σ (x j) ≤ cutoffL σ (x j) := by
    exact_mod_cast (show (cutoffQ σ (x j) : ℝ) ≤ cutoffL σ (x j) by linarith [hM.1])
  have hD : 6 ≤ cutoffD (x j) := by
    apply Nat.le_floor
    linarith
  have hshort : 2 * cutoffS (x j) ≤ cutoffD (x j) := by dsimp [cutoffS]; omega
  have hs : 0 < cutoffS (x j) := by dsimp [cutoffS]; omega
  refine ⟨hxj, ht, hML, hshort, hs, hqL, hc.le, ?_⟩
  rw [exp_suffixErrorLogScale_eq _ _ _ hLpos] at hr
  exact hr.le

open Erdos1016.Nonbacktracking Erdos1016.BoundaryDecay
open Erdos1016.Proof.RejectedCycleEncoding
open Erdos1016.Proof.ExternalReturnFilter
open QuantitativeRetainedSupply InducedRetainedCycleFilter

local instance (p : Prop) : Decidable p := Classical.propDecidable p

/-- The even-trace spectral error is small uniformly over every core with
order at most the ambient order `2^x`. -/
theorem spectral_error_of_order_bound (G : PhysicalGraph) {x : ℝ} (hx : 3 ≤ x)
    (hmin : ∀ v : G.Vertex, 2 ≤ G.degree v)
    (hmax : ∀ v : G.Vertex, G.degree v ≤ 3)
    (horder : (G.vertexCount : ℝ) ≤ (2 : ℝ) ^ x) :
    2 * (G.edgeCount : ℝ) * (2 : ℝ) ^ (-(Nat.ceil (3 * x) : ℝ)) ≤ 1 / 4 := by
  have hedge := min_two_max_three_degree_sum G hmin hmax
  have hbound : 2 * (G.edgeCount : ℝ) ≤ 3 * (2 : ℝ) ^ x := by
    have hb : 0 ≤ (degreeTwoCount G : ℝ) := by positivity
    linarith
  have hM : 3 * x ≤ (Nat.ceil (3 * x) : ℝ) := Nat.le_ceil _
  have hpow : (2 : ℝ) ^ (-(Nat.ceil (3 * x) : ℝ)) ≤ (2 : ℝ) ^ (-3 * x) := by
    apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
    linarith
  calc
    _ ≤ (3 * (2 : ℝ) ^ x) * (2 : ℝ) ^ (-3 * x) :=
      mul_le_mul hbound hpow (by positivity) (by positivity)
    _ = 3 * (2 : ℝ) ^ (-2 * x) := by
      rw [mul_assoc, ← Real.rpow_add (by norm_num : (0 : ℝ) < 2)]
      congr 2
      ring
    _ ≤ 3 * (2 : ℝ) ^ (-6 : ℝ) := by
      apply mul_le_mul_of_nonneg_left _ (by norm_num)
      exact Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)
    _ ≤ 1 / 4 := by norm_num

/-- A uniform threshold for the actual retained-cycle selection on the exact
paper cutoffs. Apart from degree and girth, the only core-specific conditions
are its order bound and the numerical degree-two deficit `b₀ L / n₀ ≤ 1`.
All trace, collision, return, rounding and selection estimates are discharged
inside the theorem. -/
theorem eventually_exists_selected_retained_family
    (σ : ℝ) (hσ : 0 < σ) (hσ20 : σ < 1 / 20)
    (x : ℕ → ℝ) (hx : Tendsto x atTop atTop) :
    ∀ᶠ j in atTop, ∀ (G : PhysicalGraph) (V : Finset G.Vertex),
      (∀ v : G.Vertex, 2 ≤ G.degree v) →
      (∀ v : G.Vertex, G.degree v ≤ 3) →
      0 < G.vertexCount → (G.vertexCount : ℝ) ≤ (2 : ℝ) ^ (x j) →
      (degreeTwoCount G : ℝ) * (cutoffL σ (x j) : ℝ) / G.vertexCount ≤ 1 →
      ShortWalks.GirthGreater G.toSimpleGraph (cutoffD (x j)) →
      ∃ F ⊆ inducedAcceptedCycles G V (shortCycleWords G (cutoffL σ (x j)))
          (cutoffQ σ (x j)),
        evenTraceTarget σ (x j) ≤ cycleWeightSum F ∧
        cycleWeightSum F ≤ evenTraceTarget σ (x j) +
          1 / (2 : ℝ) ^ (cutoffD (x j) + 1) := by
  filter_upwards [retained_cutoff_budgets σ hσ hσ20 x hx] with j hj
  obtain ⟨hxj, hτ, hML, hshort, hs, hqL, hcol, hret⟩ := hj
  intro G V hmin hmax hn horder hdefect hg
  let M := Nat.ceil (3 * x j)
  let K := cutoffL σ (x j) / 2
  have hM : 0 < M := by
    apply Nat.ceil_pos.mpr
    linarith
  have hMpos : (0 : ℝ) < M := by exact_mod_cast hM
  have hMK : M ≤ K + 1 := by dsimp [traceStart] at hML; dsimp [M, K]; omega
  have hKL : 2 * K ≤ cutoffL σ (x j) := by dsimp [K]; omega
  have hnpos : (0 : ℝ) < G.vertexCount := by exact_mod_cast hn
  have hmain : (degreeTwoCount G : ℝ) * (2 * (K : ℝ)) / G.vertexCount ≤ 1 := by
    apply le_trans _ hdefect
    apply div_le_div_of_nonneg_right _ hnpos.le
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    exact_mod_cast hKL
  have herr := spectral_error_of_order_bound G (by linarith : 3 ≤ x j) hmin hmax horder
  have hLpos : (0 : ℝ) < cutoffL σ (x j) := by
    have h : 0 < cutoffL σ (x j) := by dsimp [cutoffL, largestOddCutoff]; omega
    exact_mod_cast h
  have hratio : (cutoffL σ (x j) : ℝ) / (traceStart (x j) : ℝ) ≤
      ((K + 1 : ℕ) : ℝ) / (M : ℝ) := by
    have hlarge : (cutoffL σ (x j) : ℝ) ≤ 2 * ((K + 1 : ℕ) : ℝ) := by
      exact_mod_cast (show cutoffL σ (x j) ≤ 2 * (K + 1) by dsimp [K]; omega)
    have hMcast : (traceStart (x j) : ℝ) = 2 * (M : ℝ) := by simp [traceStart, M]
    rw [hMcast]
    apply (div_le_div_iff₀ (by positivity) hMpos).mpr
    nlinarith [mul_le_mul_of_nonneg_right hlarge hMpos.le]
  have hlog := Real.log_le_log (by
      have h : (traceStart (x j) : ℝ) = 2 * (M : ℝ) := by simp [traceStart, M]
      rw [h]
      positivity) hratio
  have hτmax : evenTraceTarget σ (x j) ≤
      (1 / 64 : ℝ) * Real.log (((K + 1 : ℕ) : ℝ) / (M : ℝ)) := by
    dsimp [evenTraceTarget]
    linarith
  exact exists_selected_retained_family G M K (cutoffL σ (x j)) (cutoffS (x j))
    (cutoffD (x j)) (cutoffQ σ (x j)) V (evenTraceTarget σ (x j))
    hmin hmax hn hM hMK hKL hmain herr hg hshort hs (by dsimp [cutoffQ]; omega) hqL hcol hret hτ hτmax

end Erdos1016.Proof.EvenTraceParameters
