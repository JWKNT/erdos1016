import Erdos1016.Probability.Avoidance.FewComponentForest

set_option autoImplicit false
set_option maxHeartbeats 1000000

/-!
# The forest estimate for a larger marked set

This module keeps the existing graph constructions and probability bounds.
It extends the marked-size range to twice the rank divided by its squared
binary logarithm. No existing theorem or shared import is changed.
-/
noncomputable section
open Filter
open scoped Topology BigOperators

namespace Erdos1016.Proof.LogSquaredMarkedForest
open FiniteMultiGraph FiniteMultiGraph.InducedSimpleRealization
open DeficitCutoffParameters ForestCutoffParameters SimpleRunWeight
open Nonbacktracking LowDegreeTraceCycles

local instance markedDecidable (p : Prop) : Decidable p := Classical.propDecidable p

/-- The unchanged short-region packing is smaller than rank/log-squared. -/
theorem eventually_packing_size_logSquared :
    ∀ᶠ x : ℝ in atTop, ∀ n : ℕ,
      n ≤ packingCutoff x * girthCutoff x →
      (n : ℝ) ≤ (2 : ℝ) ^ x / x ^ 2 := by
  have hdec := polynomial_dyadic_decay 3 (1 / 2) (by norm_num)
  filter_upwards [eventually_ge_atTop (1 : ℝ),
    hdec.eventually_lt_const (by norm_num : (0 : ℝ) < 5)] with x hx hdec
  intro n hn
  have hxpos : 0 < x := by linarith
  have hp : 0 < (2 : ℝ) ^ (x / 2) := by positivity
  have hpow : (2 : ℝ) ^ x = (2 : ℝ) ^ (x / 2) * (2 : ℝ) ^ (x / 2) := by
    rw [← Real.rpow_add (by norm_num : (0 : ℝ) < 2)]
    congr 1
    ring
  have hsmall : x ^ 3 ≤ 5 * (2 : ℝ) ^ (x / 2) := by
    rw [show -(1 / 2 : ℝ) * x = -(x / 2) by ring,
      Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 2)] at hdec
    have hh : x ^ 3 / (2 : ℝ) ^ (x / 2) < 5 := by
      simpa only [div_eq_mul_inv] using hdec
    exact ((div_lt_iff₀ hp).mp hh).le
  have hD : (girthCutoff x : ℝ) ≤ x / 10 := Nat.floor_le (by positivity)
  have hB := packingCutoff_le x hxpos.le
  have hnR : (n : ℝ) ≤ packingCutoff x * (girthCutoff x : ℝ) := by exact_mod_cast hn
  have hn' : (n : ℝ) ≤ x * (2 : ℝ) ^ (x / 2) / 5 := by
    have hh := hnR.trans (mul_le_mul hB hD (by positivity) (by positivity))
    nlinarith only [hh]
  apply (le_div_iff₀ (sq_pos_of_pos hxpos)).mpr
  calc
    (n : ℝ) * x ^ 2 ≤ (x * (2 : ℝ) ^ (x / 2) / 5) * x ^ 2 :=
      mul_le_mul_of_nonneg_right hn' (sq_nonneg x)
    _ = x ^ 3 * (2 : ℝ) ^ (x / 2) / 5 := by ring
    _ ≤ (5 * (2 : ℝ) ^ (x / 2)) * (2 : ℝ) ^ (x / 2) / 5 :=
      div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hsmall hp.le) (by norm_num)
    _ = (2 : ℝ) ^ x := by rw [hpow]; ring

/-- Uniform order and degree deficit after deleting marks and the packing. -/
theorem eventually_retained_size_and_deficit_logSquared :
    ∀ᶠ x : ℝ in atTop, ∀ (G : FiniteMultiGraph) (P S : Finset G.Vertex)
      (hloop : ∀ e ∈ G.internalEdges (P ∪ S)ᶜ, G.src e ≠ G.dst e)
      (hsimple : ∀ e ∈ G.internalEdges (P ∪ S)ᶜ,
        ∀ f ∈ G.internalEdges (P ∪ S)ᶜ,
        ((G.src e = G.src f ∧ G.dst e = G.dst f) ∨
          (G.src e = G.dst f ∧ G.dst e = G.src f)) → e = f),
      G.toSimpleGraph.Connected → (∀ v, G.degree v ≤ 3) →
      (∀ v, v ∉ P → G.degree v = 3) →
      (G.cycleRank : ℝ) = (2 : ℝ) ^ x →
      (P.card : ℝ) ≤ 2 * (2 : ℝ) ^ x / x ^ 2 →
      S.card ≤ packingCutoff x * girthCutoff x →
      let J := graph G (P ∪ S)ᶜ hloop hsimple
      (∀ v, J.degree v ≤ 3) ∧
      (2 : ℝ) ^ x ≤ J.vertexCount ∧ J.vertexCount ≤ 3 * (2 : ℝ) ^ x ∧
      Nonbacktracking.degreeDeficit J ≤ 9 * (2 : ℝ) ^ x / x ^ 2 := by
  have hzero := polynomial_dyadic_decay 0 1 (by norm_num)
  filter_upwards [eventually_packing_size_logSquared, eventually_ge_atTop (4 : ℝ),
    hzero.eventually_lt_const (by norm_num : (0 : ℝ) < 1 / 4)] with x hpack hx hzero
  intro G P S hloop hsimple hG hmax hcubic hrank hP hS
  let J := graph G (P ∪ S)ᶜ hloop hsimple
  have hxpos : 0 < x := by linarith
  have hr : 0 < (2 : ℝ) ^ x := by positivity
  have htwo : (2 : ℝ) ≤ (2 : ℝ) ^ x / 2 := by
    simp only [pow_zero, one_mul, neg_mul, Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 2)] at hzero
    have hh : 1 / (2 : ℝ) ^ x < 1 / 4 := by simpa only [one_div] using hzero
    have hh' := (div_lt_iff₀ hr).mp hh
    linarith
  have hU : ((P ∪ S).card : ℝ) ≤ 3 * (2 : ℝ) ^ x / x ^ 2 := by
    have hu : ((P ∪ S).card : ℝ) ≤ (P.card : ℝ) + S.card := by
      exact_mod_cast Finset.card_union_le P S
    have hs := hpack S.card hS
    calc
      _ ≤ 2 * (2 : ℝ) ^ x / x ^ 2 + (2 : ℝ) ^ x / x ^ 2 := by linarith
      _ = _ := by ring
  have hsmall : 3 * (2 : ℝ) ^ x / x ^ 2 ≤ (2 : ℝ) ^ x / 2 := by
    apply (div_le_iff₀ (sq_pos_of_pos hxpos)).mpr
    nlinarith [mul_nonneg hr.le (show 0 ≤ x ^ 2 - 6 by nlinarith)]
  have hPsmall : 3 * (P.card : ℝ) ≤ (2 : ℝ) ^ x := by
    have hp := (le_div_iff₀ (sq_pos_of_pos hxpos)).mp hP
    have hc : (0 : ℝ) ≤ P.card := by positivity
    have hh := mul_nonneg hc (show 0 ≤ x ^ 2 - 6 by nlinarith)
    nlinarith
  have horder := marked_order_bounds G (P ∪ S)ᶜ hloop hsimple P hG hmax hcubic
  simp only [compl_compl] at horder
  have hlo : 2 * (G.cycleRank : ℝ) ≤ (J.vertexCount : ℝ) + (P ∪ S).card + 2 := by
    exact_mod_cast horder.1
  have hhi : (J.vertexCount : ℝ) ≤ 2 * G.cycleRank + 3 * P.card := by
    exact_mod_cast horder.2
  rw [hrank] at hlo hhi
  have hdegree := degreeDeficit_le_deleted G (P ∪ S)ᶜ hloop hsimple hmax (by
    intro v hv
    apply hcubic v
    exact fun hvP => (Finset.mem_compl.mp hv) (Finset.mem_union_left S hvP))
  simp only [compl_compl] at hdegree
  refine ⟨max_degree_three G (P ∪ S)ᶜ hloop hsimple hmax, ?_, ?_, ?_⟩
  · linarith
  · linarith
  · dsimp [J]
    calc
      _ ≤ 3 * ((P ∪ S).card : ℝ) := hdegree
      _ ≤ 3 * (3 * (2 : ℝ) ^ x / x ^ 2) := mul_le_mul_of_nonneg_left hU (by norm_num)
      _ = _ := by ring

/-- The same cycle mass holds when the deficit is at most C*rank/log-squared.
The retained graph can be disconnected and can have vertices of low degree. -/
theorem eventually_cycleWordMass_ge_loglog_logSquared (C : ℝ) :
    ∀ᶠ x : ℝ in atTop, ∀ G : PhysicalGraph,
      (∀ v, G.degree v ≤ 3) →
      (2 : ℝ) ^ x ≤ G.vertexCount → G.vertexCount ≤ 3 * (2 : ℝ) ^ x →
      degreeDeficit G ≤ C * (2 : ℝ) ^ x / x ^ 2 →
      ShortWalks.GirthGreater G.toSimpleGraph (girthCutoff x) →
      Real.logb 2 (Real.logb 2 x) / 64 ≤
        ∑ ell ∈ Finset.Icc 1 (2 * upperHalfLength x), cycleWordMassAtLength G ell := by
  have hy : Tendsto (Real.logb 2) atTop atTop := Real.tendsto_logb_atTop (by norm_num)
  have hz := hy.comp hy
  have he := (polynomial_dyadic_decay 0 2 (by norm_num)).const_mul 9
  have hc := (polynomial_dyadic_decay 4 (1 / 20) (by norm_num)).const_mul 9
  filter_upwards [eventually_ge_atTop (100 : ℝ), hy.eventually_ge_atTop 4,
    hz.eventually_ge_atTop 32,
    logb_div_self_tendsto_zero.eventually_lt_const (by norm_num : (0 : ℝ) < 1),
    eventually_ge_atTop (4 * C ^ 2 : ℝ),
    he.eventually_lt_const (by norm_num : (9 : ℝ) * 0 < 1 / 4),
    hc.eventually_lt_const (by norm_num : (9 : ℝ) * 0 < 1 / 2)] with
    x hx hY hZ hYX hMain hError hCollision
  intro G hmax hnlo hnhi hdg hg
  have hxpos : 0 < x := by linarith
  have hyx : Real.logb 2 x ≤ x := ((div_lt_one hxpos).mp hYX).le
  obtain ⟨hM, hK, hMK, hKhi, hs, hsD, hslo, hlog⟩ := cutoff_bounds x hx hY hyx hZ
  have hnR : (0 : ℝ) < G.vertexCount := (Real.rpow_pos_of_pos (by norm_num) x).trans_le hnlo
  have hn : 0 < G.vertexCount := by exact_mod_cast hnR
  have hd0 := degreeDeficit_nonneg G hmax
  have hK0 : (0 : ℝ) ≤ upperHalfLength x := Nat.cast_nonneg _
  have hroot : 0 ≤ Real.sqrt x := Real.sqrt_nonneg x
  have hrootSq : Real.sqrt x ^ 2 = x := Real.sq_sqrt hxpos.le
  have hCroot : C ≤ Real.sqrt x / 2 := by nlinarith only [hMain, hrootSq, hroot]
  have hKsharp : (upperHalfLength x : ℝ) ≤ x * Real.sqrt x / 2 := by
    have hf := Nat.floor_le (show 0 ≤ x * Real.sqrt (Real.logb 2 x) / 2 by positivity)
    change (upperHalfLength x : ℝ) ≤ _ at hf
    have hh := Real.sqrt_le_sqrt hyx
    nlinarith [mul_le_mul_of_nonneg_left hh hxpos.le]
  have hCK : C * (upperHalfLength x : ℝ) ≤ x ^ 2 / 4 := by
    calc
      _ ≤ (Real.sqrt x / 2) * (x * Real.sqrt x / 2) :=
        mul_le_mul hCroot hKsharp hK0 (by positivity)
      _ = x ^ 2 / 4 := by nlinarith [hrootSq]
  have hnum : degreeDeficit G * (upperHalfLength x : ℝ) ≤ (2 : ℝ) ^ x / 4 := by
    have hdmul := (le_div_iff₀ (sq_pos_of_pos hxpos)).mp hdg
    apply (mul_le_mul_right (sq_pos_of_pos hxpos)).mp
    calc
      _ = (degreeDeficit G * x ^ 2) * (upperHalfLength x : ℝ) := by ring
      _ ≤ (C * (2 : ℝ) ^ x) * (upperHalfLength x : ℝ) :=
        mul_le_mul_of_nonneg_right hdmul hK0
      _ = (2 : ℝ) ^ x * (C * (upperHalfLength x : ℝ)) := by ring
      _ ≤ (2 : ℝ) ^ x * (x ^ 2 / 4) := mul_le_mul_of_nonneg_left hCK (by positivity)
      _ = ((2 : ℝ) ^ x / 4) * x ^ 2 := by ring
  have hmain : degreeDeficit G * (upperHalfLength x : ℝ) / G.vertexCount ≤ 1 / 4 := by
    apply (div_le_iff₀ hnR).mpr
    linarith
  have hd : degreeDeficit G < G.vertexCount := by
    have hK1 : (1 : ℝ) ≤ upperHalfLength x := by exact_mod_cast hK
    have hdk : degreeDeficit G ≤ degreeDeficit G * (upperHalfLength x : ℝ) := by nlinarith
    have hbound := (div_le_iff₀ hnR).mp hmain
    linarith
  have hError' : (9 : ℝ) / (2 : ℝ) ^ (2 * x) ≤ 1 / 4 := by
    rw [show -(2 : ℝ) * x = -(2 * x) by ring,
      Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 2)] at hError
    simpa only [pow_zero, one_mul, div_eq_mul_inv] using hError.le
  have hMpower : (2 : ℝ) ^ (3 * x) ≤ (2 : ℝ) ^ lowerHalfLength x := by
    rw [← Real.rpow_natCast]
    exact Real.rpow_le_rpow_of_exponent_le (by norm_num) (Nat.le_ceil _)
  have herr : 3 * (G.vertexCount : ℝ) / (2 : ℝ) ^ lowerHalfLength x ≤ 1 / 4 := by
    calc
      _ ≤ (9 * (2 : ℝ) ^ x) / (2 : ℝ) ^ lowerHalfLength x := by
        apply div_le_div_of_nonneg_right _ (by positivity)
        linarith
      _ ≤ (9 * (2 : ℝ) ^ x) / (2 : ℝ) ^ (3 * x) :=
        div_le_div_of_nonneg_left (by positivity) (by positivity) hMpower
      _ = 9 / (2 : ℝ) ^ (2 * x) := by
        have hpow : (2 : ℝ) ^ (3 * x) = (2 : ℝ) ^ x * (2 : ℝ) ^ (2 * x) := by
          rw [← Real.rpow_add (by norm_num : (0 : ℝ) < 2)]
          congr 1
          ring
        rw [hpow]
        field_simp
        ring
      _ ≤ _ := hError'
  have hCollision' : 9 * x ^ 4 / (2 : ℝ) ^ (x / 20) ≤ 1 / 2 := by
    rw [show -(1 / 20 : ℝ) * x = -(x / 20) by ring,
      Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 2)] at hCollision
    simpa only [div_eq_mul_inv, mul_assoc] using hCollision.le
  have hsPow : (1 / 2 : ℝ) ^ suffixCutoff x ≤ 4 / (2 : ℝ) ^ (x / 20) := by
    have h := Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 2) hslo
    have hlow : (2 : ℝ) ^ (x / 20 - 2) = (2 : ℝ) ^ (x / 20) / 4 := by
      rw [Real.rpow_sub (by norm_num : (0 : ℝ) < 2)]
      norm_num
    rw [hlow, Real.rpow_natCast] at h
    have hpos : (0 : ℝ) < (2 : ℝ) ^ (x / 20) := by positivity
    have hpowpos : (0 : ℝ) < (2 : ℝ) ^ suffixCutoff x := by positivity
    have hrecip : (1 / 2 : ℝ) ^ suffixCutoff x = 1 / (2 : ℝ) ^ suffixCutoff x := by
      rw [div_pow, one_pow]
    rw [hrecip, div_le_div_iff₀ hpowpos hpos]
    linarith
  have hcollision : (9 / 4 : ℝ) * ((2 * upperHalfLength x : ℕ) : ℝ) ^ 2 *
      (1 / 2 : ℝ) ^ suffixCutoff x ≤ 1 / 2 := by
    have hlen : ((2 * upperHalfLength x : ℕ) : ℝ) ≤ x ^ 2 := by
      push_cast
      linarith
    have hsq : (((2 * upperHalfLength x : ℕ) : ℝ)) ^ 2 ≤ x ^ 4 := by
      calc
        _ ≤ (x ^ 2) ^ 2 := pow_le_pow_left₀ (by positivity) hlen 2
        _ = _ := by ring
    calc
      _ ≤ (9 / 4 : ℝ) * x ^ 4 * (4 / (2 : ℝ) ^ (x / 20)) := by
        exact mul_le_mul (mul_le_mul_of_nonneg_left hsq (by norm_num)) hsPow
          (by positivity) (by positivity)
      _ = 9 * x ^ 4 / (2 : ℝ) ^ (x / 20) := by ring
      _ ≤ _ := hCollision'
  have hmass := cycleWordMass_ge_log_ratio G hmax hn hd
    (lowerHalfLength x) (upperHalfLength x) (suffixCutoff x) (girthCutoff x)
    hM hMK hmain herr hg hsD hs hcollision
  linarith


end Erdos1016.Proof.LogSquaredMarkedForest


namespace Erdos1016.ShortProof
open FiniteMultiGraph FiniteMultiGraph.InducedSimpleRealization
open Proof.DeficitCutoffParameters Proof.ForestCutoffParameters
open Proof.ExceptionalLoadCutoffs Proof.SimpleRunWeight
open Proof.LogSquaredMarkedForest

/-- A failed forest estimate supplies a single retained graph with all
required degree, girth, and cycle-mass properties in the larger marked range. -/
theorem eventually_exists_retained_cycle_supply_logSquared :
    ∀ᶠ x : ℝ in atTop, ∀ (G : FiniteMultiGraph) (P : Finset G.Vertex),
      G.toSimpleGraph.Connected → (∀ v, G.degree v ≤ 3) →
      (∀ v, v ∉ P → G.degree v = 3) →
      (G.cycleRank : ℝ) = (2 : ℝ) ^ x →
      (P.card : ℝ) ≤ 2 * (2 : ℝ) ^ x / x ^ 2 →
      (1 / 2 : ℝ) + 20 / Real.logb 2 (Real.logb 2 x) < G.regionForestProbability Pᶜ →
      ∃ F : Finset (Finset G.Vertex),
      ∃ hloop : ∀ e ∈ G.internalEdges (P ∪ F.biUnion id)ᶜ, G.src e ≠ G.dst e,
      ∃ hsimple : ∀ e ∈ G.internalEdges (P ∪ F.biUnion id)ᶜ,
        ∀ f ∈ G.internalEdges (P ∪ F.biUnion id)ᶜ,
        ((G.src e = G.src f ∧ G.dst e = G.dst f) ∨
          (G.src e = G.dst f ∧ G.dst e = G.src f)) → e = f,
      (∀ U ∈ F, G.ShortCyclicRegion P (girthCutoff x) U) ∧
      (∀ U, G.ShortCyclicRegion P (girthCutoff x) U → ((F.biUnion id) ∩ U).Nonempty) ∧
      let J := graph G (P ∪ F.biUnion id)ᶜ hloop hsimple
      (∀ v, J.degree v ≤ 3) ∧
      Nonbacktracking.ShortWalks.GirthGreater J.toSimpleGraph (girthCutoff x) ∧
      Real.logb 2 (Real.logb 2 x) / 64 ≤
        ∑ ell ∈ Finset.Icc 1 (2 * upperHalfLength x), cycleWordMassAtLength J ell := by
  filter_upwards [eventually_packing_threshold, eventually_geometry_cutoffs,
    eventually_retained_size_and_deficit_logSquared, eventually_cycleWordMass_ge_loglog_logSquared 9]
    with x hpacking hgeometry hsize hmass
  intro G P hG hmax hcubic hrank hP hforest
  obtain ⟨F, hF, _, _, hFS, _, hhit⟩ := G.exists_short_region_packing P
    (girthCutoff x) (packingCutoff x) (20 / Real.logb 2 (Real.logb 2 x)) hG
    (packingCutoff_pos x) hpacking hforest
  have hloop := G.retained_no_loops P (F.biUnion id) (girthCutoff x)
    (by have := hgeometry.1; omega) hmax hhit
  have hsimple := G.retained_simple P (F.biUnion id) (girthCutoff x)
    (by have := hgeometry.1; omega) hmax hhit
  let J := graph G (P ∪ F.biUnion id)ᶜ hloop hsimple
  have hg := G.retained_girth P (F.biUnion id) (girthCutoff x) hloop hsimple hmax hhit
  obtain ⟨hJmax, hnlo, hnhi, hd⟩ := hsize G P (F.biUnion id) hloop hsimple
    hG hmax hcubic hrank hP hFS
  exact ⟨F, hloop, hsimple, hF, hhit, hJmax, hg, hmass J hJmax hnlo hnhi hd hg⟩


/-- The marked forest estimate for marks up to twice rank/log-squared.
The threshold is uniform over the graph and the marked set. -/
theorem eventually_marked_forest_bound_logSquared :
    ∀ᶠ x : ℝ in atTop, ∀ (G : FiniteMultiGraph) (P : Finset G.Vertex),
      G.toSimpleGraph.Connected → (∀ v, G.degree v ≤ 3) →
      (∀ v, v ∉ P → G.degree v = 3) →
      (G.cycleRank : ℝ) = (2 : ℝ) ^ x →
      (P.card : ℝ) ≤ 2 * (2 : ℝ) ^ x / x ^ 2 →
      100 * (Nat.card (G.toSimpleGraph.induce (↑P : Set G.Vertex)).ConnectedComponent : ℝ) ≤ x →
      G.regionForestProbability Pᶜ ≤
        (1 / 2 : ℝ) + 20 / Real.logb 2 (Real.logb 2 x) := by
  classical
  have hy : Tendsto (Real.logb 2) atTop atTop := Real.tendsto_logb_atTop (by norm_num)
  have hz := hy.comp hy
  filter_upwards [eventually_exists_retained_cycle_supply_logSquared, eventually_geometry_cutoffs,
    eventually_cutoff_exceptional_load_le_quarter 300000 (3 / 2) (by norm_num) (by norm_num),
    eventually_ge_atTop (100 : ℝ), hy.eventually_ge_atTop 2, hz.eventually_gt_atTop 0]
    with x hsupply hgeometry hload hx hy hz
  intro G P hG hmax hcubic hrank hP hcomponents
  by_contra hn
  have hbad : (1 / 2 : ℝ) + 20 / Real.logb 2 (Real.logb 2 x) < G.regionForestProbability Pᶜ :=
    lt_of_not_ge hn
  obtain ⟨F, hloop, hsimple, hF, hhit, hJmax, hg, hmass⟩ :=
    hsupply G P hG hmax hcubic hrank hP hbad
  let R := (P ∪ F.biUnion id)ᶜ
  let J := graph G R hloop hsimple
  let c : ℝ := Fintype.card (ExteriorComponents.Component G P)
  let e : ℝ := 300000 * linkEnvelope x
  let M : ℝ := (2 : ℝ) ^ (c + e)
  let L := 2 * upperHalfLength x
  let z := Real.logb 2 (Real.logb 2 x)
  have hc : c ≤ x / 100 := by
    have hc' : 100 * c ≤ x := by
      simpa only [Nat.card_eq_fintype_card] using hcomponents
    linarith
  have hL : (L : ℝ) ≤ x * Real.sqrt (Real.logb 2 x) := by
    have hf := Nat.floor_le (show 0 ≤ x * Real.sqrt (Real.logb 2 x) / 2 by positivity)
    change (upperHalfLength x : ℝ) ≤ _ at hf
    dsimp [L]
    push_cast
    linarith
  have hs : 0 < suffixCutoff x := by
    unfold suffixCutoff
    have := hgeometry.1
    omega
  have hshort : 2 * suffixCutoff x ≤ girthCutoff x := by unfold suffixCutoff; omega
  have herror : M * ((3 / 2 : ℝ) * (L : ℝ) ^ 3 * (1 / 2 : ℝ) ^ suffixCutoff x) ≤ 1 / 4 :=
    hload c e hc (le_refl _)
  have hlinks : ∀ C C' : J.CycleWord,
      BoundaryDecay.Cycle.length C ≤ L → BoundaryDecay.Cycle.length C' ≤ L → C ≠ C' →
      Disjoint (cycleRegion G R hloop hsimple C) (cycleRegion G R hloop hsimple C') →
      BoundaryDecay.dyadic ((Nat.card (SeedPairCorrelation.Links G
        (cycleRegion G R hloop hsimple C) (cycleRegion G R hloop hsimple C')) : ℤ) - 1) ≤ M := by
    intro C C' hlen hlen' _ hdisj
    have hd : Disjoint (BoundaryDecay.Cycle.vertices C) (BoundaryDecay.Cycle.vertices C') := by
      apply Finset.disjoint_left.mpr
      intro v hv hv'
      exact Finset.disjoint_left.mp hdisj
        ((mem_cycleRegion_vertex G R hloop hsimple C v).mpr hv)
        ((mem_cycleRegion_vertex G R hloop hsimple C' v).mpr hv')
    have hcard := actual_cycle_links_le G P F (girthCutoff x) (smallCutCutoff x) L
      hloop hsimple C C' hd hmax hcubic hF hhit hgeometry.1 hgeometry.2.1
      hgeometry.2.2.2.1 hgeometry.2.2.2.2 hlen hlen' hG (20 / z) (by positivity) hbad
    have hsmall : ((smallCutCutoff x : ℝ) + 1) * (2 : ℝ) ^ smallCutCutoff x / (2 * (20 / z)) =
        ((smallCutCutoff x : ℝ) + 1) * (2 : ℝ) ^ smallCutCutoff x * z / 40 := by
      have hz' : z ≠ 0 := ne_of_gt hz
      field_simp [hz']
      ring
    rw [hsmall] at hcard
    have henv := link_error_le_envelope x hx hy hz.le L hL
    have hcount : (Nat.card (SeedPairCorrelation.Links G
        (cycleRegion G R hloop hsimple C) (cycleRegion G R hloop hsimple C')) : ℝ) ≤ c + e := by
      dsimp [c, e, z, R] at *
      linarith
    dsimp [M]
    unfold BoundaryDecay.dyadic
    rw [← Real.rpow_intCast]
    apply Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 2)
    push_cast
    linarith
  have hE : G.internalEdges R ⊆ G.internalEdges Pᶜ := by
    intro a ha
    have hends := (Finset.mem_filter.mp ha).2
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ _, Finset.mem_compl.mpr ?_, Finset.mem_compl.mpr ?_⟩
    · exact fun hv => (Finset.mem_compl.mp hends.1) (Finset.mem_union_left _ hv)
    · exact fun hv => (Finset.mem_compl.mp hends.2) (Finset.mem_union_left _ hv)
  have hbound := InducedCycleAvoidance.forest_le_half_add_twenty G R hloop hsimple
    hG (fun v _ => hmax v) hJmax (girthCutoff x) L (suffixCutoff x) M z hg hs hshort
    (by dsimp [M]; positivity) hz hlinks hmass herror (G.internalEdges Pᶜ) hE
  rw [← G.regionForestProbability_eq_density] at hbound
  exact (not_lt_of_ge hbound) hbad



open PhysicalGraph Erdos1016.Extremal

/-- Transfer to actual nonempty cycle unions in a simple graph.
The support may have rank/log-squared edges; the existing square-root
forest estimate and its definition remain unchanged. -/
theorem fewComponentForestEstimate_logSquared :
    ∃ rmin : ℕ, ∀ (G : PhysicalGraph), G.IsConnected → rmin ≤ G.cycleRank →
      ∀ F : Finset G.CycleWord, F.Nonempty →
        ((witnessSupportEdges G F).card : ℝ) ≤
          (G.cycleRank : ℝ) / (Real.logb 2 (G.cycleRank : ℝ)) ^ 2 →
        100 * (Nat.card (cycleUnionGraph G F).ConnectedComponent : ℝ) ≤
          Real.logb 2 (G.cycleRank : ℝ) →
        outsideForestProbability G (witnessSupportEdges G F) ≤
          (1 / 2 : ℝ) + 20 / tripleLog G.cycleRank := by
  have ht : Tendsto (fun r : ℕ => Real.logb 2 (r : ℝ)) atTop atTop :=
    (Real.tendsto_logb_atTop (by norm_num)).comp tendsto_natCast_atTop_atTop
  obtain ⟨rmin, hrmin⟩ :=
    eventually_atTop.mp (ht.eventually eventually_marked_forest_bound_logSquared)
  refine ⟨max rmin 1, ?_⟩
  intro G hG hr F hF hsize hcomponents
  have hrpos : 0 < G.cycleRank := by omega
  have hrR : (0 : ℝ) < G.cycleRank := by exact_mod_cast hrpos
  let x := Real.logb 2 (G.cycleRank : ℝ)
  have hpow : (2 : ℝ) ^ x = G.cycleRank :=
    Real.rpow_logb (by norm_num) (by norm_num) hrR
  obtain ⟨Γ, P, hconn, hrank, hdeg, hcubic, _, hcard, hcomp, hprob⟩ :=
    exists_marked_subcubic_reduction G hG F hF
  have hmark : (P.card : ℝ) ≤ 2 * (2 : ℝ) ^ x / x ^ 2 := by
    rw [hcard, Nat.cast_mul, Nat.cast_ofNat, hpow]
    change ((witnessSupportEdges G F).card : ℝ) ≤ (G.cycleRank : ℝ) / x ^ 2 at hsize
    calc
      _ ≤ 2 * ((G.cycleRank : ℝ) / x ^ 2) :=
        mul_le_mul_of_nonneg_left hsize (by norm_num)
      _ = _ := by ring
  have hc : 100 *
      (Nat.card (Γ.toSimpleGraph.induce (↑P : Set Γ.Vertex)).ConnectedComponent : ℝ) ≤ x := by
    have hcompR :
        (Nat.card (Γ.toSimpleGraph.induce (↑P : Set Γ.Vertex)).ConnectedComponent : ℝ) ≤
          Nat.card (cycleUnionGraph G F).ConnectedComponent := by exact_mod_cast hcomp
    dsimp [x]
    linarith
  have hbound := hrmin G.cycleRank (by omega) Γ P hconn (fun v => (hdeg v).2)
    hcubic (by rw [hrank]; exact hpow.symm) hmark hc
  exact hprob.trans hbound

end Erdos1016.ShortProof
