import Erdos1016.ExactMaximum.ShortCycle
import Erdos1016.ExactMaximumSupport.Shortening.TransversalTransport

set_option autoImplicit false
set_option maxHeartbeats 2000000

/-! The short-cycle exit estimate from an actual bounded-port girth bound.
This uses physical edge restrictions and does not lift any cyclic shore. -/
noncomputable section
open scoped BigOperators
namespace Erdos1016.BoundaryTrace.Network
open BoundaryDecay
local instance (priority := 100) propDecidable (p : Prop) : Decidable p := Classical.propDecidable p
variable {V E : Type} [Fintype V] [Fintype E]

theorem ShortSetting.exit_bound_of_girth {m G B₁ : ℕ}
    (hpair : ∀ (V E : Type) [Fintype V] [Fintype E] (K : Network V E), K.IsWeakPole →
      Nat.card {v : V // K.IsPort v} ≤ G + 2 → B₁ ≤ networkRank K →
      (∀ z : K.Word, K.IsCycleWord z → 5 ≤ size z) →
      ∀ s t : V, K.IsPort s → K.IsPort t → s ≠ t →
        2 ^ (m + 1) * K.numPaths s t < (2 ^ m + 2) * 2 ^ networkRank K)
    {N : Network V E} {C : N.Word} {e : E} (H : N.ShortSetting C e)
    (hG : 12 * size C ≤ G)
    (D : V → Prop) (hD : ∀ v, D v → 0 < N.deg C v)
    (hdeg : ∀ v, ¬ D v → 2 ≤ (N.sub (N.keep e D)).deg (fun _ => 1) v) {x y : V} (hxy : x ≠ y)
    (hx : (N.sub (N.keep e D)).deg (fun _ => 1) x ≤ 2)
    (hy : (N.sub (N.keep e D)).deg (fun _ => 1) y ≤ 2) (k : ℕ)
    (hk : k ≤ Nat.card {g : E // N.arcEdges C e D g}) :
    2 ^ (m + 1) * N.numPathsIn (N.keep e D) x y ≤
      (2 ^ m + 2) * 2 ^ (networkRank N - 1 - k) + 2 ^ (m + 1) * 2 ^ B₁ := by
  -- the paths lie in the component of `x`
  have hP : N.numPathsIn (N.keep e D) x y ≤
      (N.sub (N.compEdges (N.keep e D) x)).numPaths x y := by
    rw [← N.numPathsIn_eq]
    exact natCard_le_of_imp (fun z hz => ⟨hz.1, hz.1.within_compEdges hz.2⟩)
  by_cases hzero : (N.sub (N.compEdges (N.keep e D) x)).numPaths x y = 0
  · have h0 : N.numPathsIn (N.keep e D) x y = 0 := by omega
    rw [h0, mul_zero]
    exact Nat.zero_le _
  -- a path of the component
  have hpos : 0 < (N.sub (N.compEdges (N.keep e D) x)).numPaths x y := Nat.pos_of_ne_zero hzero
  obtain ⟨⟨z, hz⟩⟩ := Finite.card_pos_iff.1 hpos
  have hdx := hz.deg_left_pos
  have hdy := hz.deg_right_pos
  have hdle : ∀ v, (N.sub (N.compEdges (N.keep e D) x)).deg z v ≤
      (N.sub (N.compEdges (N.keep e D) x)).deg (fun _ => 1) v := by
    intro v
    unfold deg
    apply Finset.card_le_card
    intro k' hk'
    exact Finset.mem_filter.2 ⟨Finset.mem_univ k', one_ne_zero, (Finset.mem_filter.1 hk').2.2⟩
  have hrx : (N.sub (N.keep e D)).graph.Reachable x x := SimpleGraph.Reachable.refl x
  have hry : (N.sub (N.keep e D)).graph.Reachable x y := Classical.not_not.1 fun h => by
    have h1 := N.deg_compEdges_of_not_reachable (N.keep e D) x h
    have h2 := hdle y
    omega
  have hnDx : ¬ D x := by
    intro hDx
    have h1 := N.deg_compEdges_of_reachable (N.keep e D) x hrx
    have h2 := H.deg_keep_of_mem D hDx
    have h3 := hdle x
    omega
  -- the vertices of the component are not deleted
  have hnD : ∀ v, (N.sub (N.keep e D)).graph.Reachable x v → ¬ D v := by
    intro v hv hDv
    have h1 := N.eq_of_reachable_of_deg_eq_zero (N.keep e D) hv (H.deg_keep_of_mem D hDv)
    rw [← h1] at hDv
    exact hnDx hDv
  have hle3 : ∀ v, (N.sub (N.keep e D)).deg (fun _ => 1) v ≤ 3 := by
    intro v
    have h1 := N.deg_restrict_le (N.keep e D) v
    have h2 := H.cubic v
    omega
  -- the component is a pole
  have hpole : (N.sub (N.compEdges (N.keep e D) x)).IsWeakPole := by
    apply N.isWeakPole_compEdges
    intro v hv
    have h1 := hdeg v (hnD v hv)
    have h2 := hle3 v
    omega
  have hportx : (N.sub (N.compEdges (N.keep e D) x)).IsPort x := by
    have h1 := N.deg_compEdges_of_reachable (N.keep e D) x hrx
    have h2 := hdeg x hnDx
    unfold IsPort
    omega
  have hporty : (N.sub (N.compEdges (N.keep e D) x)).IsPort y := by
    have h1 := N.deg_compEdges_of_reachable (N.keep e D) x hry
    have h2 := hdeg y (hnD y hry)
    unfold IsPort
    omega
  -- the number of ports
  have hports : Nat.card {v : V // (N.sub (N.compEdges (N.keep e D) x)).IsPort v} ≤ G + 2 := by
    have h1 := N.natCard_ports_compEdges_le H.cubic (N.keep e D) x
    have h2 := H.natCard_not_keep_le D hD
    omega
  -- the rank
  have hrank : networkRank (N.sub (N.compEdges (N.keep e D) x)) + 1 + k ≤ networkRank N := by
    have h1 := N.rank_compEdges_add_le H.conn (N.keep e D) x (by
      intro v _
      by_cases hDv : D v
      · exact Or.inl (H.deg_keep_of_mem D hDv)
      · exact Or.inr (hdeg v hDv))
    have h2 := H.natCard_not_keep_ge D hD
    have h3 : Nat.card {v : V // ¬ (N.sub (N.keep e D)).graph.Reachable x v ∧
        (N.sub (N.keep e D)).deg (fun _ => 1) v = 0} ≤ Nat.card {v : V // D v} := by
      apply natCard_le_of_imp
      intro v hv
      refine Classical.not_not.1 fun hDv => ?_
      have := hdeg v hDv
      omega
    omega
  have hpow : 2 ^ networkRank (N.sub (N.compEdges (N.keep e D) x)) ≤
      2 ^ (networkRank N - 1 - k) := Nat.pow_le_pow_right (by norm_num) (by omega)
  have hmul : 2 ^ (m + 1) * N.numPathsIn (N.keep e D) x y ≤
      2 ^ (m + 1) * (N.sub (N.compEdges (N.keep e D) x)).numPaths x y :=
    Nat.mul_le_mul_left _ hP
  by_cases hB : B₁ ≤ networkRank (N.sub (N.compEdges (N.keep e D) x))
  · have hgirth : ∀ z : (N.sub (N.compEdges (N.keep e D) x)).Word,
        (N.sub (N.compEdges (N.keep e D) x)).IsCycleWord z → 5 ≤ size z := by
      intro z hz
      let R := ExactMaximumSupport.Shortening.TransversalTransport.subEmbed N
        (N.compEdges (N.keep e D) x)
      have hc := (R.isCycleWord_push_iff z).mpr hz
      have hs := H.short _ hc
      rw [ExactMaximumSupport.Shortening.TransversalTransport.size_push] at hs
      exact H.five.trans hs
    have hlt := hpair V _ (N.sub (N.compEdges (N.keep e D) x)) hpole hports hB
      hgirth x y hportx hporty hxy
    have h1 : (2 ^ m + 2) * 2 ^ networkRank (N.sub (N.compEdges (N.keep e D) x)) ≤
        (2 ^ m + 2) * 2 ^ (networkRank N - 1 - k) := Nat.mul_le_mul_left _ hpow
    omega
  · have h1 := (N.sub (N.compEdges (N.keep e D) x)).numPaths_le_two_pow x y
    have h2 : 2 ^ networkRank (N.sub (N.compEdges (N.keep e D) x)) ≤ 2 ^ B₁ :=
      Nat.pow_le_pow_right (by norm_num) (by omega)
    have h3 : 2 ^ (m + 1) * (N.sub (N.compEdges (N.keep e D) x)).numPaths x y ≤
        2 ^ (m + 1) * 2 ^ B₁ := Nat.mul_le_mul_left _ (le_trans h1 h2)
    omega


end Erdos1016.BoundaryTrace.Network
