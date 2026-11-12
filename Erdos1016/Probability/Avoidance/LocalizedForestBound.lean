import Erdos1016.Graph.Multigraph.RegionLocalization
import Erdos1016.Probability.Avoidance.LogSquaredMarkedForest
import Mathlib.Analysis.SpecialFunctions.Log.Monotone

set_option autoImplicit false
set_option maxHeartbeats 1000000

/-!
# Forest bounds after localization to a region

The concrete cap construction retains all internal physical labels and has
one connected marked cycle. No connectedness of the region is assumed.
This module applies the log-squared marked-forest estimate to that cap.
-/
noncomputable section
open Filter
open scoped Topology

namespace Erdos1016.Probability.LocalizedForestBound
open FiniteMultiGraph RegionLocalization

local instance localizeDecidable (p : Prop) : Decidable p := Classical.propDecidable p

/-- A connected nonempty simple graph has exactly one component. -/
theorem connectedComponent_natCard_eq_one {V : Type*} (H : SimpleGraph V)
    (hH : H.Connected) : Nat.card H.ConnectedComponent = 1 := by
  letI : Nonempty V := hH.nonempty
  letI : Nonempty H.ConnectedComponent := ⟨H.connectedComponentMk (Classical.choice hH.nonempty)⟩
  letI : Subsingleton H.ConnectedComponent := hH.preconnected.subsingleton_connectedComponent
  letI : Unique H.ConnectedComponent :=
    ⟨⟨Classical.choice (inferInstance : Nonempty H.ConnectedComponent)⟩,
      fun _ => Subsingleton.elim _ _⟩
  exact Nat.card_unique

/-- A connected induced complement makes the region proper. -/
theorem proper_of_connected_complement (G : FiniteMultiGraph) (X : Finset G.Vertex)
    (hout : (G.toSimpleGraph.induce (↑(Xᶜ) : Set G.Vertex)).Connected) : X ≠ Finset.univ := by
  obtain ⟨v⟩ := hout.nonempty
  intro hh
  have hv := v.2
  simp [hh] at hv

/-- The exact logarithmic-parameter estimate on a localized cubic region. -/
theorem eventually_localized_forest_bound :
    ∀ᶠ x : ℝ in atTop, ∀ (G : FiniteMultiGraph) (X : Finset G.Vertex),
      G.toSimpleGraph.Connected →
      (G.toSimpleGraph.induce (↑(Xᶜ) : Set G.Vertex)).Connected →
      (∀ v ∈ X, G.degree v = 3) →
      ((CycleCap.graph G X).cycleRank : ℝ) = (2 : ℝ) ^ x →
      (CycleCap.capSize G X : ℝ) ≤ 2 * (2 : ℝ) ^ x / x ^ 2 →
      G.regionForestProbability X ≤ (1 / 2 : ℝ) + 20 / Real.logb 2 (Real.logb 2 x) := by
  filter_upwards [ShortProof.eventually_marked_forest_bound_logSquared,
    eventually_ge_atTop (100 : ℝ)] with x hbound hx
  intro G X hG hout hcubic hrank hsize
  rw [CycleCap.regionForestProbability_eq G X hout]
  apply hbound (CycleCap.graph G X) (CycleCap.markedVertices G X)
    (CycleCap.graph_connected G X hG (proper_of_connected_complement G X hout))
    (CycleCap.subcubic G X (fun v hv => (hcubic v hv).le))
    (CycleCap.cubic_outside_marked G X hcubic) hrank
  · simpa only [CycleCap.marked_card] using hsize
  · rw [connectedComponent_natCard_eq_one _ (CycleCap.marked_connected G X)]
    simpa using hx

/-- Any fixed excess above one half is eventually excluded under the cap-size budget. -/
theorem eventually_localized_forest_le (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ x : ℝ in atTop, ∀ (G : FiniteMultiGraph) (X : Finset G.Vertex),
      G.toSimpleGraph.Connected →
      (G.toSimpleGraph.induce (↑(Xᶜ) : Set G.Vertex)).Connected →
      (∀ v ∈ X, G.degree v = 3) →
      ((CycleCap.graph G X).cycleRank : ℝ) = (2 : ℝ) ^ x →
      (CycleCap.capSize G X : ℝ) ≤ 2 * (2 : ℝ) ^ x / x ^ 2 →
      G.regionForestProbability X ≤ (1 / 2 : ℝ) + ε := by
  have hlog : Tendsto (Real.logb 2) atTop atTop := Real.tendsto_logb_atTop (by norm_num)
  have hz := hlog.comp hlog
  filter_upwards [eventually_localized_forest_bound, hz.eventually_gt_atTop 0,
    hz.eventually_ge_atTop (20 / ε)] with x hb hzpos hzbound
  intro G X hG hout hcubic hrank hsize
  have he : 20 / Real.logb 2 (Real.logb 2 x) ≤ ε := by
    apply (div_le_iff₀ hzpos).mpr
    have hh := (div_le_iff₀ hε).mp hzbound
    nlinarith
  exact (hb G X hG hout hcubic hrank hsize).trans (add_le_add_left he _)

/-- Scalar comparison between the order boundary budget and the cap rank budget. -/
theorem cap_budget_of_region_budget (m d r : ℝ)
    (_hm : 4 ≤ m) (hd : 0 ≤ d) (hr : 2 * r = m + d + 2)
    (hlog : 2 ≤ Real.logb 2 m) (hpad : 12 * (Real.logb 2 m) ^ 2 ≤ m)
    (hcut : d ≤ m / (4 * (Real.logb 2 m) ^ 2)) :
    0 < r ∧ m / 2 ≤ r ∧ r ≤ m ∧
      max d 3 ≤ 2 * r / (Real.logb 2 r) ^ 2 := by
  let y := Real.logb 2 m
  have hy : 2 ≤ y := hlog
  have hy2 : 0 < y ^ 2 := by positivity
  have hden : 0 < 4 * y ^ 2 := by positivity
  have hcut' : d * (4 * y ^ 2) ≤ m := (le_div_iff₀ hden).mp hcut
  have hy2ge : 4 ≤ y ^ 2 := by nlinarith
  have hdsmall : d ≤ m / 4 := by nlinarith [mul_nonneg hd (show 0 ≤ y ^ 2 - 1 by linarith)]
  have hrpos : 0 < r := by linarith
  have hrlo : m / 2 ≤ r := by linarith
  have hrhi : r ≤ m := by linarith
  have hrge : 1 ≤ r := by linarith
  have hx : 0 ≤ Real.logb 2 r := Real.logb_nonneg (by norm_num) hrge
  have hxy : Real.logb 2 r ≤ y := (Real.logb_le_logb (by norm_num) hrpos (by linarith)).2 hrhi
  have hxpos : 0 < Real.logb 2 r := Real.logb_pos (by norm_num) (by linarith)
  have hx2 : (Real.logb 2 r) ^ 2 ≤ y ^ 2 := by nlinarith
  have hpad' : 3 ≤ m / (4 * y ^ 2) := by
    apply (le_div_iff₀ hden).mpr
    nlinarith [hpad]
  have hmax : max d 3 ≤ m / (4 * y ^ 2) := max_le hcut hpad'
  refine ⟨hrpos, hrlo, hrhi, hmax.trans ?_⟩
  apply (div_le_div_iff₀ hden (sq_pos_of_pos hxpos)).mpr
  have hmul := mul_le_mul_of_nonneg_left hx2 (show 0 ≤ m by linarith)
  have hmr : m ≤ 2*r := by linarith
  nlinarith [mul_nonneg (show 0 ≤ 8*r-m by linarith) (le_of_lt hy2)]

/-- The logarithmic-square padding condition holds eventually. -/
theorem eventually_twelve_logb_square_le :
    ∀ᶠ m : ℝ in atTop, 12 * (Real.logb 2 m) ^ 2 ≤ m := by
  have h := (isLittleO_log_rpow_rpow_atTop (2 : ℝ) (by norm_num : (0 : ℝ) < 1)).tendsto_div_nhds_zero
  have hraw : Tendsto (fun m : ℝ => (Real.log m) ^ 2 / m) atTop (𝓝 0) := by
    simpa only [Real.rpow_two, Real.rpow_one] using h
  have hh := hraw.div_const ((Real.log 2)^2)
  have hb : Tendsto (fun m : ℝ => (Real.logb 2 m)^2 / m) atTop (𝓝 0) := by
    convert hh using 1
    · ext m; simp only [Real.logb]; ring
    · simp
  filter_upwards [hb.eventually_lt_const (by norm_num : (0 : ℝ) < 1/12),
    eventually_gt_atTop (0 : ℝ)] with m hm hpos
  have hh := (div_lt_iff₀ hpos).mp hm
  nlinarith

/-- Uniform exclusion of large cubic regions with a logarithmically small boundary.
The complement is connected; the region itself may have any number of components. -/
theorem eventually_region_forest_le (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ m : ℝ in atTop, ∀ (G : FiniteMultiGraph) (X : Finset G.Vertex),
      (X.card : ℝ) = m → G.toSimpleGraph.Connected →
      (G.toSimpleGraph.induce (↑(Xᶜ) : Set G.Vertex)).Connected →
      (∀ v ∈ X, G.degree v = 3) →
      ((G.cutEdges X).card : ℝ) ≤ m / (4 * (Real.logb 2 m)^2) →
      G.regionForestProbability X ≤ (1/2 : ℝ) + ε := by
  obtain ⟨x₀, hx₀⟩ := Filter.eventually_atTop.mp (eventually_localized_forest_le ε hε)
  have hlog : Tendsto (Real.logb 2) atTop atTop := Real.tendsto_logb_atTop (by norm_num)
  have hhalf : Tendsto (fun m : ℝ => m/2) atTop atTop :=
    Filter.tendsto_id.atTop_div_const (by norm_num)
  filter_upwards [eventually_ge_atTop (4 : ℝ), hlog.eventually_ge_atTop 2,
    eventually_twelve_logb_square_le, (hlog.comp hhalf).eventually_ge_atTop x₀]
    with m hm hlogm hpad hxlo
  intro G X hcard hG hout hcubic hcut
  let r : ℝ := (CycleCap.graph G X).cycleRank
  let d : ℝ := (G.cutEdges X).card
  have hr : 2*r = m+d+2 := by
    rw [← hcard]
    dsimp [r, d]
    exact_mod_cast CycleCap.cubic_rank_ledger G X hG (proper_of_connected_complement G X hout) hcubic
  obtain ⟨hrpos, hrlo, hrhi, hbudget⟩ := cap_budget_of_region_budget m d r hm (by positivity)
    hr hlogm hpad hcut
  have hx : x₀ ≤ Real.logb 2 r := hxlo.trans
    ((Real.logb_le_logb (by norm_num) (by linarith) hrpos).2 hrlo)
  have hpow : (2 : ℝ) ^ Real.logb 2 r = r := Real.rpow_logb (by norm_num) (by norm_num) hrpos
  have hsize : (CycleCap.capSize G X : ℝ) ≤ 2 * (2 : ℝ)^Real.logb 2 r / (Real.logb 2 r)^2 := by
    rw [hpow]
    have he : (CycleCap.capSize G X : ℝ) = max d 3 := by
      simp [CycleCap.capSize, CycleCap.BoundaryEdge, d, Nat.cast_max]
    rw [he]
    exact hbudget
  exact hx₀ _ hx G X hG hout hcubic hpow.symm hsize

/-- A single rank-independent order threshold for the localized forest bound. -/
theorem exists_region_forest_threshold (ε : ℝ) (hε : 0 < ε) :
    ∃ M : ℕ, ∀ (G : FiniteMultiGraph) (X : Finset G.Vertex),
      M ≤ X.card → G.toSimpleGraph.Connected →
      (G.toSimpleGraph.induce (↑(Xᶜ) : Set G.Vertex)).Connected →
      (∀ v ∈ X, G.degree v = 3) →
      ((G.cutEdges X).card : ℝ) ≤ (X.card : ℝ) / (4 * (Real.logb 2 X.card)^2) →
      G.regionForestProbability X ≤ (1/2 : ℝ) + ε := by
  obtain ⟨m₀, hm₀⟩ := Filter.eventually_atTop.mp (eventually_region_forest_le ε hε)
  refine ⟨⌈m₀⌉₊, ?_⟩
  intro G X hsize hG hout hcubic hcut
  have hm : m₀ ≤ (X.card : ℝ) := (Nat.le_ceil m₀).trans (by exact_mod_cast hsize)
  exact hm₀ _ hm G X rfl hG hout hcubic hcut

/-- Close a region by keeping the component containing the connected marker outside.
This increases the region and cannot increase its physical boundary. -/
theorem exists_connected_complement_closure (G : FiniteMultiGraph)
    (P X : Finset G.Vertex)
    (hP : (G.toSimpleGraph.induce (↑P : Set G.Vertex)).Connected) (hXP : X ⊆ Pᶜ) :
    ∃ Y : Finset G.Vertex, X ⊆ Y ∧ Y ⊆ Pᶜ ∧
      (G.toSimpleGraph.induce (↑(Yᶜ) : Set G.Vertex)).Connected ∧
      G.cutEdges Y ⊆ G.cutEdges X := by
  obtain ⟨p⟩ := hP.nonempty
  have hPU : P ⊆ Xᶜ := by
    intro v hv
    exact Finset.mem_compl.mpr (fun hx => Finset.mem_compl.mp (hXP hx) hv)
  let inc : (G.toSimpleGraph.induce (↑P : Set G.Vertex)) →g
      (G.toSimpleGraph.induce (↑(Xᶜ) : Set G.Vertex)) :=
    (SimpleGraph.induceHomOfLE (G := G.toSimpleGraph)
      (show (↑P : Set G.Vertex) ⊆ ↑(Xᶜ) from hPU)).toHom
  let c : ExteriorComponents.Component G Xᶜ :=
    (ExteriorComponents.graph G Xᶜ).connectedComponentMk ⟨p.1, hPU p.2⟩
  let C := ExteriorComponents.vertices G Xᶜ c
  have hPC : P ⊆ C := by
    intro v hv
    apply (ExteriorComponents.mem_vertices G Xᶜ c v).mpr
    refine ⟨hPU hv, ?_⟩
    obtain ⟨route⟩ := hP.preconnected ⟨v, hv⟩ p
    exact SimpleGraph.ConnectedComponent.sound ⟨route.map inc⟩
  refine ⟨Cᶜ, ?_, ?_, ?_, ?_⟩
  · intro v hv
    apply Finset.mem_compl.mpr
    intro hc
    exact Finset.mem_compl.mp (ExteriorComponents.vertices_subset G Xᶜ c hc) hv
  · intro v hv
    exact Finset.mem_compl.mpr (fun hp => Finset.mem_compl.mp hv (hPC hp))
  · have he : (↑(Cᶜᶜ) : Set G.Vertex) = (↑C : Set G.Vertex) := by
      ext v
      simp
    rw [he]
    exact ExteriorComponents.vertices_connected G Xᶜ c
  · rw [G.cutEdges_compl]
    have hh := ExteriorComponents.cut_subset G Xᶜ c
    simpa only [G.cutEdges_compl] using hh

/-- Forest probability decreases when the retained vertex region increases. -/
theorem regionForestProbability_antitone (G : FiniteMultiGraph) (X Y : Finset G.Vertex)
    (hXY : X ⊆ Y) : G.regionForestProbability Y ≤ G.regionForestProbability X := by
  classical
  unfold regionForestProbability
  apply div_le_div_of_nonneg_right _ (by positivity)
  apply Nat.cast_le.mpr
  apply Finset.card_le_card
  intro z hz
  refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩
  apply ((Finset.mem_filter.mp hz).2).mono
  intro e he
  have hx : e ∈ G.internalEdges X := by
    by_contra hn
    simp [restrictEdges, hn] at he
  have hy : e ∈ G.internalEdges Y := by
    have hh := (Finset.mem_filter.mp hx).2
    simp [internalEdges, hXY hh.1, hXY hh.2]
  simpa [restrictEdges, hx, hy] using he

/-- The order divided by its squared binary logarithm is increasing beyond exp(2). -/
theorem logSquaredBudget_mono {a b : ℝ} (ha : Real.exp 2 ≤ a) (hab : a ≤ b) :
    a / (4 * (Real.logb 2 a)^2) ≤ b / (4 * (Real.logb 2 b)^2) := by
  have hap : 0 < a := (Real.exp_pos 2).trans_le ha
  have hbp : 0 < b := hap.trans_le hab
  have ha1 : 1 < a := (Real.one_lt_exp_iff.mpr (by norm_num : (0 : ℝ) < 2)).trans_le ha
  have hb1 : 1 < b := ha1.trans_le hab
  have hla : 0 < Real.log a := Real.log_pos ha1
  have hlb : 0 < Real.log b := Real.log_pos hb1
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hsqa : 0 < Real.sqrt a := Real.sqrt_pos.mpr hap
  have hsqb : 0 < Real.sqrt b := Real.sqrt_pos.mpr hbp
  have hh := Real.log_div_sqrt_antitoneOn ha (ha.trans hab) hab
  have hmul : Real.log b * Real.sqrt a ≤ Real.log a * Real.sqrt b :=
    (div_le_div_iff₀ hsqb hsqa).mp hh
  have hsquare : (Real.log b)^2 * a ≤ (Real.log a)^2 * b := by
    have hh' := sq_le_sq₀ (by positivity : 0 ≤ Real.log b * Real.sqrt a)
      (by positivity : 0 ≤ Real.log a * Real.sqrt b)
    have hh'' := hh'.mpr hmul
    simpa only [mul_pow, Real.sq_sqrt hap.le, Real.sq_sqrt hbp.le] using hh''
  have hba : 0 < Real.logb 2 a := Real.logb_pos (by norm_num) ha1
  have hbb : 0 < Real.logb 2 b := Real.logb_pos (by norm_num) hb1
  apply (div_le_div_iff₀ (by positivity : 0 < 4*(Real.logb 2 a)^2)
    (by positivity : 0 < 4*(Real.logb 2 b)^2)).mpr
  simp only [Real.logb, div_pow]
  have ht : (4*a*(Real.log b)^2)/(Real.log 2)^2 ≤
      (4*b*(Real.log a)^2)/(Real.log 2)^2 :=
    div_le_div_of_nonneg_right (by nlinarith [hsquare]) (sq_nonneg _)
  convert ht using 1 <;> ring

/-- A large small-boundary region outside a connected marker forces the global
outside-forest probability to be at most one half plus any fixed epsilon. -/
theorem exists_small_boundary_forest_threshold (ε : ℝ) (hε : 0 < ε) :
    ∃ M : ℕ, ∀ (G : FiniteMultiGraph) (P X : Finset G.Vertex),
      G.toSimpleGraph.Connected →
      (G.toSimpleGraph.induce (↑P : Set G.Vertex)).Connected →
      (∀ v, v ∉ P → G.degree v = 3) →
      X ⊆ Pᶜ → M ≤ X.card →
      ((G.cutEdges X).card : ℝ) ≤ (X.card : ℝ)/(4*(Real.logb 2 X.card)^2) →
      G.regionForestProbability Pᶜ ≤ (1/2 : ℝ) + ε := by
  obtain ⟨M, hM⟩ := exists_region_forest_threshold ε hε
  refine ⟨max M ⌈Real.exp 2⌉₊, ?_⟩
  intro G P X hG hP hcubic hXP hsize hcut
  obtain ⟨Y, hXY, hYP, hout, hboundary⟩ := exists_connected_complement_closure G P X hP hXP
  have hcard : X.card ≤ Y.card := Finset.card_le_card hXY
  have hYsize : M ≤ Y.card := (le_max_left _ _).trans (hsize.trans hcard)
  have hXlarge : Real.exp 2 ≤ (X.card : ℝ) := (Nat.le_ceil _).trans (by
    exact_mod_cast (le_max_right M ⌈Real.exp 2⌉₊).trans hsize)
  have hYcut : ((G.cutEdges Y).card : ℝ) ≤ (Y.card : ℝ)/(4*(Real.logb 2 Y.card)^2) := by
    have hb : ((G.cutEdges Y).card : ℝ) ≤ (G.cutEdges X).card := by
      exact_mod_cast Finset.card_le_card hboundary
    exact hb.trans (hcut.trans (logSquaredBudget_mono hXlarge (by exact_mod_cast hcard)))
  exact (regionForestProbability_antitone G Y Pᶜ hYP).trans
    (hM G Y hYsize hG hout (fun v hv => hcubic v (Finset.mem_compl.mp (hYP hv))) hYcut)

end Erdos1016.Probability.LocalizedForestBound
