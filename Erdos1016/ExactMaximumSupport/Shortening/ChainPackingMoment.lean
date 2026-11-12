import Erdos1016.ExactMaximumSupport.LargeGirth.GoodRow
import Erdos1016.Probability.Moments.SmallCutRegionBound

set_option autoImplicit false
set_option maxHeartbeats 1000000

/-!
# A heavy two-link row for disjoint cyclic regions

Use the actual event that a region has zero boundary word and nonzero interior.
The exceptional-partner count bounds the error by `(d+1)μ`, independently of
the sizes of the regions. No choice of a cycle seed is needed.
-/
noncomputable section
open scoped BigOperators
namespace Erdos1016.ExactMaximumSupport.Shortening.ChainPackingMoment
open FiniteMultiGraph BoundaryDecay BoundaryTrace
open FiniteMultiGraph.SeedPairCorrelation PolynomialBound.TwoLinkMoment
open PolynomialBound.Averaging LargeGirth

local instance momentDecidable (p : Prop) : Decidable p := Classical.propDecidable p

variable {ι : Type*} [Fintype ι]
variable (G : FiniteMultiGraph) (U : ι → Finset G.Vertex)

def regionWeight (i : ι) : ℝ := Finite.density (G.RegionCycleEvent (U i))

omit [Fintype ι] in
theorem regionWeight_nonneg (i : ι) : 0 ≤ regionWeight G U i := Finite.density_nonneg _
omit [Fintype ι] in
theorem regionWeight_le_one (i : ι) : regionWeight G U i ≤ 1 := Finite.density_le_one _

private theorem zeroCut_density_pos (A : Finset G.Vertex) :
    0 < Finite.density (fun x : G.CycleSpace => x ∈ G.zeroCutSpace A) := by
  have he : (fun x : G.CycleSpace => x ∈ G.zeroCutSpace A) =
      fun x => ∀ e ∈ G.cutEdges A, x.1 e = 0 := by
    funext x
    exact propext (G.mem_zeroCutSpace_iff A x)
  rw [he]
  exact lt_of_lt_of_le (by positivity) (G.zeroCoordinates_probability_ge _)

private theorem card_le_two_of_dyadic {n : ℕ} (h : dyadic ((n : ℤ) - 1) ≤ 2) : n ≤ 2 := by
  by_contra hn
  have hm : dyadic 2 ≤ dyadic ((n : ℤ) - 1) := by
    unfold dyadic
    exact zpow_le_zpow_right₀ (by norm_num) (by omega)
  have he : dyadic 2 = 4 := by norm_num [dyadic]
  rw [he] at hm
  linarith

omit [Fintype ι] in
theorem region_pair_exact (i j : ι) (hG : G.toSimpleGraph.Connected)
    (hd : Disjoint (U i) (U j))
    (hi : (G.toSimpleGraph.induce (↑(U i) : Set G.Vertex)).Connected)
    (hj : (G.toSimpleGraph.induce (↑(U j) : Set G.Vertex)).Connected) :
    Finite.density (fun x => G.RegionCycleEvent (U i) x ∧ G.RegionCycleEvent (U j) x) =
      dyadic ((Nat.card (Links G (U i) (U j)) : ℤ) - 1) *
        (regionWeight G U i * regionWeight G U j) := by
  rw [G.regionCycleEvent_pair_density _ _ hd, zeroCut_pair_exact G _ _ hG hd hi hj]
  simp only [regionWeight, G.regionCycleEvent_density]
  ring

/-- The two-link kernel keeps the factor two only where it is needed. -/
theorem second_moment_le (s : Finset ι) (d : ℕ)
    (hG : G.toSimpleGraph.Connected)
    (hdisj : Pairwise (fun i j => Disjoint (U i) (U j)))
    (hconn : ∀ i, (G.toSimpleGraph.induce (↑(U i) : Set G.Vertex)).Connected)
    (hcut : ∀ i ∈ s, (G.cutEdges (U i)).card ≤ d) :
    average (fun x => (∑ i ∈ s, indicator (G.RegionCycleEvent (U i)) x)^2) ≤
      (∑ i ∈ s, regionWeight G U i)^2 +
        (∑ i ∈ s, ∑ j ∈ s, twoLink G U i j * (regionWeight G U i * regionWeight G U j)) +
        (1+(d:ℝ)) * (∑ i ∈ s, regionWeight G U i) := by
  classical
  apply weighted_sum_second_moment_le_kernel s _ (regionWeight G U)
    (DisjointRegionCuts.Exceptional G U) (twoLink G U) (d:ℝ)
  · intro i hi x; simp only [indicator]; split_ifs <;> norm_num
  · intro i hi x; simp only [indicator]; split_ifs <;> norm_num
  · intro i hi; exact average_indicator _
  · intro i hi j hj; exact twoLink_nonneg G U i j
  · intro i hi j hj hij hex
    have hd := hdisj hij
    have he (k : ι) : DisjointRegionCuts.ZeroCut G (U k) =
        fun x : G.CycleSpace => x ∈ G.zeroCutSpace (U k) := by
      funext x
      exact propext (G.mem_zeroCutSpace_iff (U k) x).symm
    have hcutpair := le_of_not_gt hex
    simp only [DisjointRegionCuts.Exceptional, he] at hcutpair
    rw [zeroCut_pair_exact G _ _ hG hd (hconn i) (hconn j)] at hcutpair
    have hfactor : dyadic ((Nat.card (Links G (U i) (U j)) : ℤ)-1) ≤ 2 := by
      have hp := mul_pos (zeroCut_density_pos G (U i)) (zeroCut_density_pos G (U j))
      nlinarith
    have hc := card_le_two_of_dyadic hfactor
    simp only [indicator_mul, average_indicator]
    rw [region_pair_exact G U i j hG hd (hconn i) (hconn j)]
    apply mul_le_mul_of_nonneg_right _
      (mul_nonneg (regionWeight_nonneg G U i) (regionWeight_nonneg G U j))
    by_cases h2 : Nat.card (Links G (U i) (U j)) = 2
    · rw [(twoLink_eq_one_iff G U i j).mpr ⟨hij,hd,h2⟩]
      linarith
    · have hone : dyadic ((Nat.card (Links G (U i) (U j)) : ℤ)-1) ≤ 1 := by
        unfold dyadic
        apply zpow_le_one_of_nonpos₀ (by norm_num)
        omega
      linarith [twoLink_nonneg G U i j]
  · intro i hi
    have hpair (j : ι) :
        average (fun x => indicator (G.RegionCycleEvent (U i)) x *
          indicator (G.RegionCycleEvent (U j)) x) ≤ regionWeight G U i := by
      rw [regionWeight, ← average_indicator]
      apply average_mono
      intro x
      by_cases hp : G.RegionCycleEvent (U i) x <;>
        by_cases hq : G.RegionCycleEvent (U j) x <;> simp [indicator,hp,hq]
    have hs := Finset.sum_le_sum (fun j (_ : j ∈ s) =>
      show (if i≠j ∧ DisjointRegionCuts.Exceptional G U i j then
        average (fun x => indicator (G.RegionCycleEvent (U i)) x *
          indicator (G.RegionCycleEvent (U j)) x) else 0) ≤
        (if i≠j ∧ DisjointRegionCuts.Exceptional G U i j then regionWeight G U i else 0) from by
          split_ifs <;> simp only [le_refl,hpair])
    have hc : (s.filter fun j => i≠j ∧ DisjointRegionCuts.Exceptional G U i j).card ≤ d := by
      simpa only [ne_comm] using
        (DisjointRegionCuts.exceptional_partner_card_le G U hG hdisj hconn i s).trans (hcut i hi)
    have heq : (∑ j ∈ s, if i≠j ∧ DisjointRegionCuts.Exceptional G U i j then
        regionWeight G U i else 0) =
        ((s.filter fun j => i≠j ∧ DisjointRegionCuts.Exceptional G U i j).card:ℝ) *
          regionWeight G U i := by rw [← Finset.sum_filter]; simp
    rw [heq] at hs
    exact hs.trans (mul_le_mul_of_nonneg_right (by exact_mod_cast hc) (regionWeight_nonneg G U i))

/-- A forest event avoids every region event. Its probability forces two-link mass. -/
theorem twoLink_weight_ge (s : Finset ι) (d : ℕ) (E : Finset G.Edge)
    (hG : G.toSimpleGraph.Connected)
    (hdisj : Pairwise (fun i j => Disjoint (U i) (U j)))
    (hconn : ∀ i, (G.toSimpleGraph.induce (↑(U i) : Set G.Vertex)).Connected)
    (hcut : ∀ i ∈ s, (G.cutEdges (U i)).card ≤ d)
    (hE : ∀ i ∈ s, G.internalEdges (U i) ⊆ E)
    (hforest : (2/5:ℝ) ≤ Finite.density (fun x : G.CycleSpace =>
      G.IsForestWord (G.restrictEdges E x.1))) :
    (2/3:ℝ) * (∑ i ∈ s, regionWeight G U i)^2 -
      (1+(d:ℝ)) * (∑ i ∈ s, regionWeight G U i) ≤
        ∑ i ∈ s, ∑ j ∈ s, twoLink G U i j * (regionWeight G U i * regionWeight G U j) := by
  classical
  apply Averaging.kernel_weight_ge_two_fifths
    (fun x => ∑ i ∈ s, indicator (G.RegionCycleEvent (U i)) x) _ _ _
  · simp only [average_sum,average_indicator,regionWeight]
  · exact second_moment_le G U s d hG hdisj hconn hcut
  · apply hforest.trans
    rw [← average_indicator, ← average_indicator]
    apply average_mono
    intro x
    by_cases hx : G.IsForestWord (G.restrictEdges E x.1)
    · have hno (i : ι) (hi : i ∈ s) : ¬ G.RegionCycleEvent (U i) x := by
        intro hc
        apply G.regionCycleEvent_not_forest (U i) x hc
        apply hx.mono
        intro e he
        by_cases hm : e ∈ G.internalEdges (U i)
        · have hl := hE i hi hm
          simpa only [restrictEdges,hm,hl,↓reduceIte] using he
        · simp [restrictEdges,hm] at he
      have hz : (∑ i ∈ s, indicator (G.RegionCycleEvent (U i)) x)=0 :=
        Finset.sum_eq_zero (fun i hi => by simp [indicator,hno i hi])
      change (if G.IsForestWord (G.restrictEdges E x.1) then (1:ℝ) else 0) ≤
        if (∑ i ∈ s, indicator (G.RegionCycleEvent (U i)) x)=0 then 1 else 0
      rw [if_pos hx,if_pos hz]
    · simp only [indicator,hx,↓reduceIte]
      split_ifs <;> norm_num

omit [Fintype ι] in
/-- Pairwise disjoint regions with weights at most one have vertex load at most one. -/
theorem disjoint_weight_load (s : Finset ι) (a : ι → ℝ)
    (hdisj : Pairwise (fun i j => Disjoint (U i) (U j)))
    (ha : ∀ i ∈ s, a i ≤ 1) (v : G.Vertex) :
    (∑ i ∈ s, if v ∈ U i then a i else 0) ≤ 1 := by
  classical
  by_cases hv : ∃ i ∈ s, v ∈ U i
  · obtain ⟨i,hi,hvi⟩ := hv
    rw [Finset.sum_eq_single i]
    · simpa [hvi] using ha i hi
    · intro j hj hji
      have hvj : v ∉ U j := fun h => Finset.disjoint_left.mp (hdisj hji) h hvi
      simp [hvj]
    · exact fun hn => (hn hi).elim
  · have he : (∑ i ∈ s, if v ∈ U i then a i else 0)=0 := by
      apply Finset.sum_eq_zero
      intro i hi
      exact if_neg (fun h => hv ⟨i,hi,h⟩)
    rw [he]; norm_num

/-- The good row has mass at least `μ/3-2d`, for any positive total mass. -/
theorem exists_good_row (p : G.Vertex) (s : Finset ι) (d : ℕ) (E : Finset G.Edge)
    (hG : G.toSimpleGraph.Connected)
    (hdisj : Pairwise (fun i j => Disjoint (U i) (U j)))
    (hconn : ∀ i, (G.toSimpleGraph.induce (↑(U i) : Set G.Vertex)).Connected)
    (hp : ∀ i ∈ s, p ∉ U i) (hd : 1 ≤ d)
    (hcut : ∀ i ∈ s, (G.cutEdges (U i)).card ≤ d)
    (hE : ∀ i ∈ s, G.internalEdges (U i) ⊆ E)
    (hforest : (2/5:ℝ) ≤ Finite.density (fun x : G.CycleSpace =>
      G.IsForestWord (G.restrictEdges E x.1)))
    (hpos : 0 < ∑ i ∈ s, regionWeight G U i) :
    ∃ i ∈ s, (∑ j ∈ s, regionWeight G U j)/3-2*d ≤
      ∑ j ∈ s, goodTwoLink G U p i j * regionWeight G U j := by
  have hW := twoLink_weight_ge G U s d E hG hdisj hconn hcut hE hforest
  have hj (i : ι) (hi : i ∈ s) :
      (∑ j ∈ s, joinedPair G U i j * regionWeight G U j) ≤ (d:ℝ) := by
    have hh := joinedPair_row_le G U s (regionWeight G U) 1 i
      (fun j _ => regionWeight_nonneg G U j) (by norm_num)
      (disjoint_weight_load G U s _ hdisj (fun j _ => regionWeight_le_one G U j))
    have hdc : ((G.cutEdges (U i)).card:ℝ) ≤ d := by exact_mod_cast hcut i hi
    simpa only [mul_one] using hh.trans (by simpa using hdc)
  obtain ⟨i,hi,hr⟩ := Averaging.exists_good_row_relative s (regionWeight G U)
    (twoLink G U) (farTwoLink G U p) (joinedPair G U) (goodTwoLink G U p)
    (2/3) (1+d) d (fun i _ => regionWeight_nonneg G U i) hpos
    (fun i _ j _ => twoLink_le_good_far_joined G U p i j)
    (fun i hi j hj => farTwoLink_add_reverse_le G U p i j hG (hconn i) (hconn j) (hp i hi)) hW hj
  refine ⟨i,hi,?_⟩
  have hd' : (1:ℝ) ≤ d := by exact_mod_cast hd
  linarith

end Erdos1016.ExactMaximumSupport.Shortening.ChainPackingMoment
