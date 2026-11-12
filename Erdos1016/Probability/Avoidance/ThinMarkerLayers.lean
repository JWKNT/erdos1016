import Erdos1016.Probability.Avoidance.LocalizedForestBound
import Erdos1016.Probability.Avoidance.SymmetricWindow
import Erdos1016.Probability.Avoidance.LevelWindowBoundary

set_option autoImplicit false
set_option maxHeartbeats 1500000

/-!
# Quadratic width of levels meeting a thin connected marker

A forest probability above one half excludes every sufficiently large
small-boundary region. Expanding symmetric windows turns a large level
into such a region. The graph, region, and boundary estimates are concrete;
no stopping or growth hypothesis is left in the final theorem.
-/
noncomputable section
open Filter
open scoped Topology

namespace Erdos1016.Probability.ThinMarkerLayers
open FiniteMultiGraph LevelWindowBoundary SymmetricWindow LocalizedForestBound

local instance thinDecidable (p : Prop) : Decidable p := Classical.propDecidable p

/-- Uniform quadratic bound for the unmarked vertices in every integer level. -/
theorem exists_unmarked_layer_bound (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ (G : FiniteMultiGraph) (P : Finset G.Vertex)
      (level : G.Vertex → ℤ) (k : ℕ),
      G.toSimpleGraph.Connected → (∀ v, G.degree v ≤ 3) →
      (G.toSimpleGraph.induce (↑P : Set G.Vertex)).Connected →
      (∀ v, v ∉ P → G.degree v = 3) →
      (∀ e, level (G.src e) ≤ level (G.dst e)+1 ∧ level (G.dst e) ≤ level (G.src e)+1) →
      (∀ j, (markedLayer G P level j).card ≤ k) →
      (1/2 : ℝ)+ε < G.regionForestProbability Pᶜ →
      ∀ j, (window G P level j 0).card < C*(k+1)^2 := by
  obtain ⟨M, hM⟩ := exists_small_boundary_forest_threshold ε hε
  obtain ⟨R, hR⟩ := Filter.eventually_atTop.mp eventually_window_overhead_budget
  let C := max M (max ⌈R⌉₊ 2)
  have hC : 2 ≤ C := (le_max_right _ _).trans (le_max_right _ _)
  refine ⟨C, hC, ?_⟩
  intro G P level k hG hdegree hP hcubic hlevel hmark hq j
  by_contra hn
  have hlarge : C*(k+1)^2 ≤ (window G P level j 0).card := Nat.le_of_not_gt hn
  let mass : ℕ → ℕ := fun n => (window G P level j n).card
  have hmono : Monotone mass := mass_monotone G P level j
  have hCmass : C ≤ mass 0 := by
    have hp : 1 ≤ (k+1)^2 := one_le_pow₀ (by omega)
    dsimp [mass]
    nlinarith
  have hstart : 2 ≤ mass 0 := hC.trans hCmass
  obtain ⟨N, hstop, hspan⟩ := exists_short_stopped_window mass hmono hstart (mass_bounded G P level j)
  let μ : ℝ := mass N
  let L := Real.logb 2 μ
  have hmassmono : mass 0 ≤ mass N := hmono (Nat.zero_le N)
  have hμnat : C*(k+1)^2 ≤ mass N := hlarge.trans hmassmono
  have hμ : 0 ≤ μ := by positivity
  have hRμ : R ≤ μ := (Nat.le_ceil R).trans (by
    have hh : ⌈R⌉₊ ≤ mass N :=
      (le_max_left _ _).trans ((le_max_right _ _).trans (hCmass.trans hmassmono))
    dsimp [μ]
    exact_mod_cast hh)
  obtain ⟨hL, hbudget⟩ := hR μ hRμ
  have hk2 : (k : ℝ)^2 ≤ μ := by
    have hh : k^2 ≤ mass N := by
      have hm := Nat.mul_le_mul_right ((k+1)^2) (show 1 ≤ C by omega)
      have hm' : (k+1)^2 ≤ C*(k+1)^2 := by simpa only [one_mul] using hm
      exact (pow_le_pow_left' (Nat.le_succ k) 2).trans (hm'.trans hμnat)
    dsimp [μ]
    exact_mod_cast hh
  have hover : 3*(k : ℝ)*(96*L^3+3) ≤ μ/(8*L^2) :=
    marker_overhead_le hμ hL (Nat.cast_nonneg k) hk2 hbudget
  have hring : ((ring G P level j N).card : ℝ) = (mass (N+1) : ℝ)-μ := by
    have hh := ring_card_add G P level j N
    have hr : ((ring G P level j N).card : ℝ)+(mass N : ℝ) = mass (N+1) := by
      exact_mod_cast hh
    dsimp [μ]
    linarith
  have hboundary : ((G.cutEdges (window G P level j N)).card : ℝ) ≤ μ/(4*L^2) := by
    have hb : ((G.cutEdges (window G P level j N)).card : ℝ) ≤
        3*((ring G P level j N).card : ℝ)+3*(k : ℝ)*(2*(N : ℝ)+3) := by
      exact_mod_cast cut_window_le G P level hdegree hlevel k hmark j N
    have hnspan : (N : ℝ) ≤ 48*L^3 := hspan
    have hmstop : (mass (N+1) : ℝ)-μ ≤ μ/(24*L^2) := hstop
    have hfirst : 3*((ring G P level j N).card : ℝ) ≤ μ/(8*L^2) := by
      rw [hring]
      have hh := mul_le_mul_of_nonneg_left hmstop (by norm_num : (0 : ℝ) ≤ 3)
      have he : 3*(μ/(24*L^2)) = μ/(8*L^2) := by ring
      linarith
    have hsecond : 3*(k : ℝ)*(2*(N : ℝ)+3) ≤ μ/(8*L^2) := by
      have hh := mul_le_mul_of_nonneg_left hnspan (by positivity : (0 : ℝ) ≤ 6*k)
      nlinarith
    have he : μ/(8*L^2)+μ/(8*L^2) = μ/(4*L^2) := by ring
    linarith
  have hsize : M ≤ (window G P level j N).card :=
    (le_max_left _ _).trans (hCmass.trans hmassmono)
  have hh := hM G P (window G P level j N) hG hP hcubic
    (window_subset_unmarked G P level j N) hsize hboundary
  exact (not_lt_of_ge hh) hq

/-- The complete level, including the marker, has uniformly quadratic width. -/
theorem exists_layer_width_bound (ε : ℝ) (hε : 0 < ε) :
    ∃ B : ℕ, ∀ (G : FiniteMultiGraph) (P : Finset G.Vertex)
      (level : G.Vertex → ℤ) (k : ℕ),
      G.toSimpleGraph.Connected → (∀ v, G.degree v ≤ 3) →
      (G.toSimpleGraph.induce (↑P : Set G.Vertex)).Connected →
      (∀ v, v ∉ P → G.degree v = 3) →
      (∀ e, level (G.src e) ≤ level (G.dst e)+1 ∧ level (G.dst e) ≤ level (G.src e)+1) →
      (∀ j, (markedLayer G P level j).card ≤ k) →
      (1/2 : ℝ)+ε < G.regionForestProbability Pᶜ →
      ∀ j, (Finset.univ.filter fun v => level v = j).card ≤ B*(k+1)^2 := by
  obtain ⟨C, hC, hb⟩ := exists_unmarked_layer_bound ε hε
  refine ⟨C+1, ?_⟩
  intro G P level k hG hdegree hP hcubic hlevel hmark hq j
  have hunmarked := hb G P level k hG hdegree hP hcubic hlevel hmark hq j
  have he : (Finset.univ.filter fun v => level v = j) =
      window G P level j 0 ∪ markedLayer G P level j := by
    ext v
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_union,
      mem_window, Nat.cast_zero, sub_zero, add_zero, markedLayer]
    by_cases hp : v ∈ P
    · simp [hp]
    · simp [hp]
      omega
  rw [he]
  have hc := Finset.card_union_le (window G P level j 0) (markedLayer G P level j)
  have hm := hmark j
  nlinarith

/-- The fixed three-fifths form used for thin tree markers in normalized poles. -/
theorem exists_layer_width_bound_three_fifths :
    ∃ B : ℕ, ∀ (G : FiniteMultiGraph) (P : Finset G.Vertex)
      (level : G.Vertex → ℤ) (k : ℕ),
      G.toSimpleGraph.Connected → (∀ v, G.degree v ≤ 3) →
      (G.toSimpleGraph.induce (↑P : Set G.Vertex)).Connected →
      (∀ v, v ∉ P → G.degree v = 3) →
      (∀ e, level (G.src e) ≤ level (G.dst e)+1 ∧ level (G.dst e) ≤ level (G.src e)+1) →
      (∀ j, (markedLayer G P level j).card ≤ k) →
      (3/5 : ℝ) ≤ G.regionForestProbability Pᶜ →
      ∀ j, (Finset.univ.filter fun v => level v = j).card ≤ B*(k+1)^2 := by
  obtain ⟨B, hB⟩ := exists_layer_width_bound (1/20) (by norm_num)
  refine ⟨B, ?_⟩
  intro G P level k hG hdegree hP hcubic hlevel hmark hq
  apply hB G P level k hG hdegree hP hcubic hlevel hmark
  linarith

end Erdos1016.Probability.ThinMarkerLayers
