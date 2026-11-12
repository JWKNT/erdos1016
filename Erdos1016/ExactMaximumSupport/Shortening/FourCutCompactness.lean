import Erdos1016.ExactMaximumSupport.Shortening.FourCutLimits
import Erdos1016.ExactMaximumSupport.Shortening.FourCutLimitGluing

set_option autoImplicit false
set_option maxHeartbeats 3000000

/-! Finite-dimensional compactness gives one positive tolerance that forces
an exact common full cross. The tolerance is obtained by compactness, not
by numerical rigidity or a supplied stability assertion. -/
noncomputable section
namespace Erdos1016.ExactMaximumSupport.Shortening.FourCutCompactness
open ExactMaximum FourCutArithmeticProof Filter
open scoped Topology

private abbrev StateData :=
  ((Fin 4 → Fin 4 → ℝ) × (Fin 4 → Fin 4 → ℝ)) × ((Fin 3 → ℝ) × (Fin 3 → ℝ))

/-- A uniform positive error tolerance forces exact fullness on both shores. -/
theorem exists_tolerance : ∃ η : ℝ,0<η ∧ η≤1 ∧
    ∀ (x a : Fin 4 → Fin 4 → ℝ) (p u : Fin 3 → ℝ),
      FourState x p → ApproxState η a u →
      4-η≤pairSum x a+pairingSum p u → CommonFullCross x a := by
  classical
  by_contra hn
  push_neg at hn
  let ε : ℕ → ℝ := fun n => 1/((n : ℝ)+1)
  have hεpos (n : ℕ) : 0<ε n := by dsimp [ε]; positivity
  have hεone (n : ℕ) : ε n≤1 := by
    dsimp [ε]
    apply (div_le_one (by positivity)).mpr
    have := Nat.cast_nonneg (α:=ℝ) n
    linarith
  choose x a p u hx ha hB hbad using fun n => hn (ε n) (hεpos n) (hεone n)
  let seq (n : ℕ) : StateData := ((x n,a n),(p n,u n))
  have hmem (n : ℕ) : seq n∈Set.Icc (0 : StateData) 1 := by
    constructor
    · exact ⟨⟨(hx n).nonneg,(ha n).nonneg⟩,⟨(hx n).u_nonneg,(ha n).u_nonneg⟩⟩
    · refine ⟨⟨(hx n).le_one,(ha n).le_one⟩,⟨?_,?_⟩⟩
      · intro α
        exact (coordinate_le_forest (hx n) α).trans (hx n).u_sum
      · intro α
        exact (coordinate_le_forest (ha n).toFourState α).trans (ha n).u_sum
  obtain ⟨v,_,φ,hφ,hlim⟩ := (isCompact_Icc : IsCompact (Set.Icc (0 : StateData) 1)).tendsto_subseq hmem
  have hxl (i j : Fin 4) : Tendsto (fun n => x (φ n) i j) atTop (𝓝 (v.1.1 i j)) := by
    have hc : Continuous (fun w : StateData => w.1.1 i j) := by fun_prop
    exact hc.tendsto v |>.comp hlim
  have hal (i j : Fin 4) : Tendsto (fun n => a (φ n) i j) atTop (𝓝 (v.1.2 i j)) := by
    have hc : Continuous (fun w : StateData => w.1.2 i j) := by fun_prop
    exact hc.tendsto v |>.comp hlim
  have hpl (i : Fin 3) : Tendsto (fun n => p (φ n) i) atTop (𝓝 (v.2.1 i)) := by
    have hc : Continuous (fun w : StateData => w.2.1 i) := by fun_prop
    exact hc.tendsto v |>.comp hlim
  have hul (i : Fin 3) : Tendsto (fun n => u (φ n) i) atTop (𝓝 (v.2.2 i)) := by
    have hc : Continuous (fun w : StateData => w.2.2 i) := by fun_prop
    exact hc.tendsto v |>.comp hlim
  have hεlim : Tendsto (fun n => ε (φ n)) atTop (𝓝 0) :=
    tendsto_one_div_add_atTop_nhds_zero_nat.comp hφ.tendsto_atTop
  have hX := fourState_limit (fun n => hx (φ n)) hxl hpl
  have hY := fourState_limit (fun n => (ha (φ n)).toFourState) hal hul
  have hL := approxState_limit hεlim (fun n => ha (φ n)) hal hul
  have hbil := tendsto_bilinear hxl hal hpl hul
  have hfour : 4≤pairSum v.1.1 v.1.2+pairingSum v.2.1 v.2.2 := by
    have hh := le_of_tendsto_of_tendsto (tendsto_const_nhds.sub hεlim) hbil
      (Eventually.of_forall fun n => hB (φ n))
    simpa using hh
  have hc := common_full_cross_of_limit hX hY hL hfour
  have hev := eventually_common_cross (fun n => hx (φ n))
    (fun n => (ha (φ n)).toFourState) hxl hal hc
  obtain ⟨n,hn⟩ := hev.exists
  exact hbad (φ n) hn

/-- A cap error and a small-shore contribution each at most one quarter of the
compactness tolerance suffice, uniformly even when the small rank is bounded. -/
theorem cap_near_total (η e z q B : ℝ) (hη : 0≤η)
    (he : e≤η/4) (hq : q≤z/2)
    (htotal : 4≤e+q+B) (hcap : z+B≤4+η/4) : 4-η≤B := by
  linarith

end Erdos1016.ExactMaximumSupport.Shortening.FourCutCompactness
