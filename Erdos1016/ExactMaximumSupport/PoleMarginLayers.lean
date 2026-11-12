import Erdos1016.ExactMaximumSupport.PoleMarginOutsideRank
import Erdos1016.ExactMaximumSupport.PoleAvoidingShortCycle

set_option autoImplicit false
set_option maxHeartbeats 2000000

/-!
# Thin layers and short cycles at every positive margin

These are the parameterized forms needed by the bounded-girth argument.
The fixed-margin theorems remain available through their existing interfaces.
-/
noncomputable section
namespace Erdos1016.ExactMaximumSupport.PoleMarginLayers
open BoundaryTrace BoundaryTrace.Network BoundaryDecay
local instance marginLayersDecidable (p : Prop) : Decidable p := Classical.propDecidable p

/-- Proposition 5.3 holds at each positive path-density margin. -/
theorem exists_thin_layer_bound (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℕ, ∀ (V E : Type) [Fintype V] [Fintype E] (N : Network V E) (s t : V),
      N.IsBridgelessTwoPole s t →
      (1/2 + ε) * (2:ℝ)^networkRank N ≤ N.numPaths s t →
      (∀ v, N.graph.dist s v ≤ networkRank N + C) ∧
        Nat.card {v : V // ¬ N.IsOrdinaryLayer s t (N.graph.dist s v)} ≤ C := by
  obtain ⟨C,hC⟩ := PoleMarginOutsideRank.exists_network_bound ε hε
  refine ⟨10 * C + 8,?_⟩
  intro V E _ _ N s t hN hpaths
  obtain ⟨A,hA,hshort⟩ := NetworkGeodesic.exists_shortest_path N hN.connected s t hN.ne
  have hdegree (v : V) : N.deg (fun _ => 1) v ≤ 3 := by
    by_cases hs : v = s
    · subst v
      exact hN.deg_s.le.trans (by decide)
    by_cases ht : v = t
    · subst v
      exact hN.deg_t.le.trans (by decide)
    exact (hN.deg_other v hs ht).le
  have hout := hC V E N s t A hN.connected hN.deg_s.le hN.deg_t.le
    hN.deg_other hA hshort hpaths
  have horder := PolePathRank.bridgeless_order N s t hN
  have hdefect : networkRank N ≤ N.graph.dist s t + C := by
    have h := PolePathRank.bridgeless_path_rank N s t hN A hA
    rw [hshort] at h
    omega
  let level : V → ℕ := N.graph.dist s
  let ell := N.graph.dist s t
  have hcard (j : ℕ) : (LayerCountLedger.layer level j).card =
      Nat.card {v : V // N.graph.dist s v = j} := by
    simp only [LayerCountLedger.layer, level, Nat.card_eq_fintype_card,
      Fintype.card_subtype]
  have hlower (j : ℕ) (hj : 0 < j) (hjell : j < ell) :
      2 ≤ (LayerCountLedger.layer level j).card := by
    rw [hcard]
    exact BridgelessLayers.internal_layer_card_ge_two N s t hN j hj hjell
  have hthin (j : ℕ) : LayerCountLedger.Thin level ell j ↔ N.IsThinLayer s t j := by
    unfold LayerCountLedger.Thin Network.IsThinLayer
    rw [hcard]
  have hsmall : (LayerCountLedger.exceptional level ell).card ≤ 6 * C + 6 :=
    LayerCountLedger.exceptional_card_le level ell C hlower (by omega)
  have hell : ell ≤ networkRank N + 1 :=
    LayerCountLedger.ell_le_rank_add_one level ell (networkRank N) hlower horder
  let bad : Finset V := Finset.univ.filter fun v => N.deg A v = 0 ∧ N.OnParallel v
  have hbad : bad.card ≤ 2 * C := by
    have h := PoleParallelCount.card_parallel_outside_le_twice_rank N A hA
      hN.deg_s.le hN.deg_t.le hdegree
    exact h.trans (Nat.mul_le_mul_left 2 hout)
  have hcharge (j : ℕ) (hj : LayerCountLedger.Thin level ell j)
      (hno : ¬ N.IsOrdinaryLayer s t j) : ∃ v ∈ bad, level v = j := by
    obtain ⟨v,hv,hzero,hparallel⟩ :=
      NetworkPathMarker.parallel_witness_of_not_ordinary N hN.connected hA hshort j
        ((hthin j).mp hj) hno
    exact ⟨v,Finset.mem_filter.mpr ⟨Finset.mem_univ _,hzero,hparallel⟩,hv⟩
  have hordinary := LayerCountLedger.nonordinary_card_le level ell
    (N.IsOrdinaryLayer s t) bad hcharge
  constructor
  · intro v
    have hd := LayerCountLedger.level_le_ell_add_exceptional level ell v
      (fun j hj => BridgelessLayers.exists_vertex_at_distance N hN.connected s v j hj)
    change level v ≤ networkRank N + (10 * C + 8)
    omega
  · have hcount : Nat.card {v : V // ¬ N.IsOrdinaryLayer s t (N.graph.dist s v)} =
        (Finset.univ.filter fun v => ¬ N.IsOrdinaryLayer s t (level v)).card := by
      simp only [Nat.card_eq_fintype_card, Fintype.card_subtype, level]
    rw [hcount]
    omega

/-- Any bounded forbidden set is avoided by a short cycle when the pole rank is large enough. -/
theorem exists_avoiding_constant (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℕ, ∀ (k : ℕ) (V E : Type) [Fintype V] [Fintype E]
      (N : Network V E) (s t : V),
      N.IsBridgelessTwoPole s t →
      (1/2 + ε) * (2:ℝ)^networkRank N ≤ N.numPaths s t →
      ∀ X : Finset V, X.card ≤ k → 5*C+4*k+5 ≤ networkRank N →
      ∃ z : N.Word, N.IsCycleWord z ∧ size z ≤ 4 ∧
        ∀ v, 0 < N.deg z v → v ∉ X := by
  obtain ⟨C,hC⟩ := exists_thin_layer_bound ε hε
  refine ⟨C,?_⟩
  intro k V E _ _ N s t hN hpaths X hX hrank
  exact PoleAvoidingShortCycle.exists_cycle_avoiding_of_nonordinary_bound N s t hN C k
    (hC V E N s t hN hpaths).2 X hX hrank

end Erdos1016.ExactMaximumSupport.PoleMarginLayers
