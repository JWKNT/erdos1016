import Erdos1016.ExactMaximumSupport.Shortening.FourCutApproxState
import Erdos1016.ExactMaximumSupport.Shortening.FourCutLimitRigidity
import Mathlib.Topology.Sequences
import Mathlib.Analysis.SpecificLimits.Basic

set_option autoImplicit false
set_option maxHeartbeats 2000000

/-! Passing actual four-pole states and variable-tolerance gadget laws to limits.
The full-star restriction is closed because the fixed gap turns limiting unit
coordinates into eventual exact fullness. -/
noncomputable section
namespace Erdos1016.ExactMaximumSupport.Shortening.FourCutCompactness
open ExactMaximum FourCutArithmeticProof Filter
open scoped Topology

/-- The gap makes fullness an isolated coordinate value. -/
theorem eventually_full {f : ℕ → ℝ}
    (hlim : Tendsto f atTop (𝓝 1))
    (hgap : ∀ n,f n=1 ∨ f n≤15/16) : ∀ᶠ n in atTop,f n=1 := by
  have hh := hlim.eventually_const_lt (by norm_num : (15 : ℝ)/16<1)
  filter_upwards [hh] with n hn
  exact (hgap n).resolve_right (not_le_of_gt hn)

/-- Basic bounds, the gap, and the conditional full-star bounds survive limits. -/
theorem fourState_limit
    {a : ℕ → Fin 4 → Fin 4 → ℝ} {u : ℕ → Fin 3 → ℝ}
    {a₀ : Fin 4 → Fin 4 → ℝ} {u₀ : Fin 3 → ℝ}
    (hs : ∀ n,FourState (a n) (u n))
    (ha : ∀ i j,Tendsto (fun n => a n i j) atTop (𝓝 (a₀ i j)))
    (hu : ∀ i,Tendsto (fun n => u n i) atTop (𝓝 (u₀ i))) : FourState a₀ u₀ := by
  refine ⟨?_,?_,?_,?_,?_,?_,?_⟩
  · intro i j
    have h1 := ha i j
    have he : (fun n => a n i j)=(fun n => a n j i) := funext fun n => (hs n).symm i j
    rw [he] at h1
    exact tendsto_nhds_unique h1 (ha j i)
  · intro i j
    exact le_of_tendsto_of_tendsto tendsto_const_nhds (ha i j)
      (Eventually.of_forall fun n => (hs n).nonneg i j)
  · intro i j
    exact le_of_tendsto (ha i j) (Eventually.of_forall fun n => (hs n).le_one i j)
  · intro i
    exact le_of_tendsto_of_tendsto tendsto_const_nhds (hu i)
      (Eventually.of_forall fun n => (hs n).u_nonneg i)
  · exact le_of_tendsto (((hu 0).add (hu 1)).add (hu 2))
      (Eventually.of_forall fun n => (hs n).u_sum)
  · intro i j hij
    have hc : IsClosed (({1} : Set ℝ) ∪ Set.Iic (15/16)) :=
      isClosed_singleton.union isClosed_Iic
    exact hc.mem_of_tendsto (ha i j) (Eventually.of_forall fun n => (hs n).gap i j hij)
  · intro i hstar α
    have he : ∀ᶠ n in atTop,∀ j,j≠i → a n i j=1 := by
      apply Filter.eventually_all.mpr
      intro j
      by_cases hj : j=i
      · exact Eventually.of_forall fun _ hji => (hji hj).elim
      · have hh : Tendsto (fun n => a n i j) atTop (𝓝 1) := by rw [←hstar j hj]; exact ha i j
        exact (eventually_full hh (fun n => (hs n).gap i j (Ne.symm hj))).mono
          (fun n hn _ => hn)
    apply le_of_tendsto (hu α)
    filter_upwards [he] with n hn
    exact (hs n).star i hn α

/-- Vanishing approximate errors give the exact qualitative gadget laws. -/
theorem approxState_limit
    {η : ℕ → ℝ} {a : ℕ → Fin 4 → Fin 4 → ℝ} {u : ℕ → Fin 3 → ℝ}
    {a₀ : Fin 4 → Fin 4 → ℝ} {u₀ : Fin 3 → ℝ}
    (hη : Tendsto η atTop (𝓝 0)) (hs : ∀ n,ApproxState (η n) (a n) (u n))
    (ha : ∀ i j,Tendsto (fun n => a n i j) atTop (𝓝 (a₀ i j)))
    (hu : ∀ i,Tendsto (fun n => u n i) atTop (𝓝 (u₀ i))) :
    FourCutLimitRigidity.LimitState a₀ u₀ := by
  have hb := fourState_limit (fun n => (hs n).toFourState) ha hu
  refine ⟨hb.symm,hb.nonneg,hb.le_one,hb.u_nonneg,hb.u_sum,?_,?_,?_⟩
  · intro i j k hij hik hjk hpos
    by_contra hn
    have ht : ∀ᶠ n in atTop,1+η n≤a n i k+a n j k := by
      have hh := (tendsto_const_nhds.add hη).eventually_lt ((ha i k).add (ha j k))
        (by simpa using lt_of_not_ge hn)
      exact hh.mono fun _ h => h.le
    have hz : a₀ i j≤0 := le_of_tendsto_of_tendsto (ha i j) hη (by
      filter_upwards [ht] with n hn
      exact (hs n).t1 i j k hij hik hjk hn)
    exact (not_le_of_gt hpos) hz
  · intro i j k l hd hpos
    have ht : ∀ᶠ n in atTop,2+η n≤a n i k+a n i l+a n j k+a n j l := by
      have hh := (tendsto_const_nhds.add hη).eventually_lt
        ((((ha i k).add (ha i l)).add (ha j k)).add (ha j l)) (by simpa using hpos)
      exact hh.mono fun _ h => h.le
    have hz : u₀ (pairingOf i k)+u₀ (pairingOf i l)≤0 :=
      le_of_tendsto_of_tendsto ((hu _).add (hu _)) hη (by
        filter_upwards [ht] with n hn
        exact (hs n).t2 i j k l hd hn)
    exact le_antisymm hz (add_nonneg (hb.u_nonneg _) (hb.u_nonneg _))
  · intro i j k l hd hpos
    by_contra hn
    have ht : ∀ᶠ n in atTop,1+η n≤a n i j+u n (pairingOf i k)+u n (pairingOf i l) := by
      have hh := (tendsto_const_nhds.add hη).eventually_lt
        (((ha i j).add (hu _)).add (hu _)) (by simpa using lt_of_not_ge hn)
      exact hh.mono fun _ h => h.le
    have hz : a₀ k l≤0 := le_of_tendsto_of_tendsto (ha k l) hη (by
      filter_upwards [ht] with n hn
      exact (hs n).t3 i j k l hd hn)
    exact (not_le_of_gt hpos) hz

/-- The literal gluing polynomial is continuous in all its coordinates. -/
theorem tendsto_bilinear
    {x a : ℕ → Fin 4 → Fin 4 → ℝ} {p u : ℕ → Fin 3 → ℝ}
    {x₀ a₀ : Fin 4 → Fin 4 → ℝ} {p₀ u₀ : Fin 3 → ℝ}
    (hx : ∀ i j,Tendsto (fun n => x n i j) atTop (𝓝 (x₀ i j)))
    (ha : ∀ i j,Tendsto (fun n => a n i j) atTop (𝓝 (a₀ i j)))
    (hp : ∀ i,Tendsto (fun n => p n i) atTop (𝓝 (p₀ i)))
    (hu : ∀ i,Tendsto (fun n => u n i) atTop (𝓝 (u₀ i))) :
    Tendsto (fun n => pairSum (x n) (a n)+pairingSum (p n) (u n)) atTop
      (𝓝 (pairSum x₀ a₀+pairingSum p₀ u₀)) := by
  unfold pairSum pairingSum
  exact ((((((hx 0 1).mul (ha 0 1)).add ((hx 0 2).mul (ha 0 2))).add
    ((hx 0 3).mul (ha 0 3))).add ((hx 1 2).mul (ha 1 2))).add
    ((hx 1 3).mul (ha 1 3))).add ((hx 2 3).mul (ha 2 3)) |>.add
    ((((hp 0).mul ((hu 1).add (hu 2))).add ((hp 1).mul ((hu 0).add (hu 2)))).add
      ((hp 2).mul ((hu 0).add (hu 1))))

/-- A common full cross in the limit becomes an actual common full cross eventually. -/
theorem eventually_common_cross
    {x a : ℕ → Fin 4 → Fin 4 → ℝ} {p u : ℕ → Fin 3 → ℝ}
    {x₀ a₀ : Fin 4 → Fin 4 → ℝ}
    (hsx : ∀ n,FourState (x n) (p n)) (hsa : ∀ n,FourState (a n) (u n))
    (hx : ∀ i j,Tendsto (fun n => x n i j) atTop (𝓝 (x₀ i j)))
    (ha : ∀ i j,Tendsto (fun n => a n i j) atTop (𝓝 (a₀ i j)))
    (hc : CommonFullCross x₀ a₀) : ∀ᶠ n in atTop,CommonFullCross (x n) (a n) := by
  obtain ⟨i,j,k,l,hd,hx1,hx2,hx3,hx4,ha1,ha2,ha3,ha4⟩ := hc
  have ex (v w : Fin 4) (hvw : v≠w) (hf : x₀ v w=1) :
      ∀ᶠ n in atTop,x n v w=1 := by
    apply eventually_full (by rw [←hf]; exact hx v w)
    exact fun n => (hsx n).gap v w hvw
  have ea (v w : Fin 4) (hvw : v≠w) (hf : a₀ v w=1) :
      ∀ᶠ n in atTop,a n v w=1 := by
    apply eventually_full (by rw [←hf]; exact ha v w)
    exact fun n => (hsa n).gap v w hvw
  filter_upwards [ex i k hd.2.1 hx1,ex i l hd.2.2.1 hx2,
    ex j k hd.2.2.2.1 hx3,ex j l hd.2.2.2.2.1 hx4,
    ea i k hd.2.1 ha1,ea i l hd.2.2.1 ha2,
    ea j k hd.2.2.2.1 ha3,ea j l hd.2.2.2.2.1 ha4] with n h1 h2 h3 h4 h5 h6 h7 h8
  exact ⟨i,j,k,l,hd,h1,h2,h3,h4,h5,h6,h7,h8⟩

end Erdos1016.ExactMaximumSupport.Shortening.FourCutCompactness
