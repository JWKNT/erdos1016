import Erdos1016.ExactMaximum.PoleCycleCount
import Erdos1016.ExactMaximumSupport.PoleMarginLayers
import Erdos1016.ExactMaximumSupport.CycleTwoStrands
import Erdos1016.ExactMaximumSupport.LayerMatchingInput

set_option autoImplicit false
set_option maxHeartbeats 2000000

/-! The actual cycle-code count, with the layer budget left as a parameter. -/
noncomputable section
namespace Erdos1016.ExactMaximumSupport.Shortening.MarginFewCyclesCore
open BoundaryTrace BoundaryTrace.Network BoundaryDecay ExactMaximum
local instance coreDecidable (p : Prop) : Decidable p := Classical.propDecidable p

/-- The fixed-margin counting proof uses only these literal layer conclusions. -/
theorem cycles_sq_le_of_layers {V E : Type} [Fintype V] [Fintype E]
    (N : Network V E) (s t : V) (hN : N.IsBridgelessTwoPole s t) (C : ℕ)
    (hdist : ∀ v, N.graph.dist s v ≤ networkRank N + C)
    (hbad : Nat.card {v : V // ¬N.IsOrdinaryLayer s t (N.graph.dist s v)} ≤ C)
    (h2' : N.TwoStrandsAt s t) (hM' : N.MatchingsAt s t) :
    N.numCycles ^ 2 ≤ 2 ^ (2 * (3 * (C + 4)) + 8 + C) * 2 ^ networkRank N := by
  haveI : Nonempty E := by
    have h : 0 < N.deg (fun _ => 1) s := by
      rw [hN.deg_s]
      norm_num
    obtain ⟨e, _⟩ := N.exists_edge_of_deg_pos h
    exact ⟨e⟩
  -- a separating edge for each pair of layers
  have hsep : ∀ l : ℕ, ∃ ε : E, Nat.card {m : N.Word // N.IsLayerMatching s l m} ≤ 2 →
      ∀ m m' : N.Word, N.IsLayerMatching s l m → N.IsLayerMatching s l m' → m ε = m' ε →
        m = m' := by
    intro l
    by_cases h : Nat.card {m : N.Word // N.IsLayerMatching s l m} ≤ 2
    · obtain ⟨ε, hε⟩ := exists_separating_edge (fun m : N.Word => N.IsLayerMatching s l m) h
      exact ⟨ε, fun _ => hε⟩
    · exact ⟨Classical.arbitrary E, fun h' => absurd h' h⟩
  choose ε hε using hsep
  obtain ⟨n, hn⟩ : ∃ n, n = networkRank N + C := ⟨_, rfl⟩
  obtain ⟨K₀, hK₀⟩ : ∃ K₀, K₀ = 3 * (C + 4) := ⟨_, rfl⟩
  -- the cycles with a given first and last layer
  have hfiber : ∀ i j : ℕ,
      Nat.card {Z : N.Word // (N.IsCycleWord Z ∧ N.hi s Z = j) ∧ N.lo s Z = i} ≤
        2 ^ (K₀ + (j - i) / 2) := by
    intro i j
    refine le_trans (natCard_le_of_determined _ (N.codeSet s t ε i j) ?_)
      (Nat.pow_le_pow_right (by norm_num) ?_)
    · rintro Z Z' ⟨⟨hZ, hj⟩, hi⟩ ⟨⟨hZ', hj'⟩, hi'⟩ hres
      exact N.eq_of_restrict_codeSet hN h2' hM' ε hε hZ hZ' hi hj hi' hj' hres
    · rw [hK₀]
      exact N.natCard_codeSet_le hN hM' ε hbad i j
  -- the cycles with a given last layer
  have hlast : ∀ j : ℕ, Nat.card {Z : N.Word // N.IsCycleWord Z ∧ N.hi s Z = j} ≤
      2 ^ K₀ * halfPowSum j := by
    intro j
    rw [natCard_eq_sum_fibers (fun Z : N.Word => N.IsCycleWord Z ∧ N.hi s Z = j)
      (fun Z => N.lo s Z) (Finset.range (j + 1)) ?_]
    · calc (∑ i ∈ Finset.range (j + 1),
            Nat.card {Z : N.Word // (N.IsCycleWord Z ∧ N.hi s Z = j) ∧ N.lo s Z = i})
          ≤ ∑ i ∈ Finset.range (j + 1), 2 ^ K₀ * 2 ^ ((j - i) / 2) :=
            Finset.sum_le_sum (fun i _ => by
              rw [← pow_add]
              exact hfiber i j)
        _ = 2 ^ K₀ * halfPowSum j := by rw [← Finset.mul_sum, sum_range_half_pow_sub]
    · rintro Z ⟨hZ, hj⟩
      rw [Finset.mem_range]
      show N.lo s Z < j + 1
      obtain ⟨v, hv⟩ := hZ.exists_vertex
      have h1 := N.lo_le_dist s hv
      have h3 := N.dist_le_hi s hv
      omega
  -- all cycles
  have hall : N.numCycles ≤ 2 ^ K₀ * (16 * 2 ^ (n / 2)) := by
    unfold numCycles
    rw [natCard_eq_sum_fibers (fun Z : N.Word => N.IsCycleWord Z) (fun Z => N.hi s Z)
      (Finset.range (n + 1)) ?_]
    · calc (∑ j ∈ Finset.range (n + 1),
            Nat.card {Z : N.Word // N.IsCycleWord Z ∧ N.hi s Z = j})
          ≤ ∑ j ∈ Finset.range (n + 1), 2 ^ K₀ * halfPowSum j :=
            Finset.sum_le_sum (fun j _ => hlast j)
        _ = 2 ^ K₀ * ∑ j ∈ Finset.range (n + 1), halfPowSum j := by rw [Finset.mul_sum]
        _ ≤ 2 ^ K₀ * (16 * 2 ^ (n / 2)) := Nat.mul_le_mul_left _ (sum_halfPowSum_le n)
    · intro Z hZ
      rw [Finset.mem_range]
      show N.hi s Z < n + 1
      obtain ⟨v, hv⟩ := hZ.exists_vertex
      obtain ⟨w, _, hw⟩ := N.meets_hi s hv
      have h1 := hdist w
      omega
  -- the square
  have hsq : N.numCycles ^ 2 ≤ (2 ^ K₀ * (16 * 2 ^ (n / 2))) ^ 2 := Nat.pow_le_pow_left hall 2
  have e1 : (2 ^ K₀ * (16 * 2 ^ (n / 2))) ^ 2 = 2 ^ (2 * K₀ + 8 + 2 * (n / 2)) := by
    have h16 : (16 : ℕ) = 2 ^ 4 := by norm_num
    rw [h16, ← pow_add, ← pow_add, ← pow_mul]
    congr 1
    ring
  have e2 : 2 ^ (2 * K₀ + 8 + 2 * (n / 2)) ≤
      2 ^ (2 * (3 * (C + 4)) + 8 + C) * 2 ^ networkRank N := by
    rw [← pow_add]
    apply Nat.pow_le_pow_right (by norm_num)
    omega
  rw [e1] at hsq
  exact le_trans hsq e2


/-- Every fixed positive path margin gives a uniform square-root cycle bound. -/
theorem exists_bound (ε : ℝ) (hε : 0 < ε) :
    ∃ K : ℕ, ∀ (V E : Type) [Fintype V] [Fintype E] (N : Network V E) (s t : V),
      N.IsBridgelessTwoPole s t →
      (1/2 + ε) * (2:ℝ)^networkRank N ≤ N.numPaths s t →
      N.numCycles ^ 2 ≤ K * 2 ^ networkRank N := by
  obtain ⟨C,hC⟩ := PoleMarginLayers.exists_thin_layer_bound ε hε
  refine ⟨2 ^ (2 * (3 * (C + 4)) + 8 + C), ?_⟩
  intro V E _ _ N s t hN hrich
  obtain ⟨hdist,hbad⟩ := hC V E N s t hN hrich
  exact cycles_sq_le_of_layers N s t hN C hdist hbad
    (CycleTwoStrands.twoStrandsStatement V E N s t hN)
    (layerMatchingStatement V E N s t hN)

end Erdos1016.ExactMaximumSupport.Shortening.MarginFewCyclesCore
