import Erdos1016.ExactMaximumSupport.Shortening.BoundedPortCount
import Erdos1016.ExactMaximumSupport.Shortening.BoundedPortGirth

set_option autoImplicit false
set_option maxHeartbeats 2000000

/-! The complete bounded-short-cycle case using the direct bounded-port theorem. -/
noncomputable section
open scoped BigOperators
namespace Erdos1016.BoundaryTrace.Network
open BoundaryDecay
local instance (priority := 100) boundedPortShortDecidable (p : Prop) : Decidable p := Classical.propDecidable p
variable {V E : Type} [Fintype V] [Fintype E]

theorem numCycles_lt_of_short_cycle_of_girth {m G B₁ B₂ : ℕ}
    (hpair : ∀ (V E : Type) [Fintype V] [Fintype E] (K : Network V E), K.IsWeakPole →
      Nat.card {v : V // K.IsPort v} ≤ G + 2 → B₁ ≤ networkRank K →
      (∀ z : K.Word, K.IsCycleWord z → 5 ≤ size z) →
      ∀ s t : V, K.IsPort s → K.IsPort t → s ≠ t →
        2 ^ (m + 1) * K.numPaths s t < (2 ^ m + 2) * 2 ^ networkRank K)
    (hbound : ∀ (V E : Type) [Fintype V] [Fintype E] (N : Network V E), B₂ ≤ networkRank N →
      2 ^ (m + 1) * N.numCycles ≤ (2 ^ m + 1) * 2 ^ networkRank N)
    (N : Network V E) (hN : N.graph.Connected) (hcubic : N.IsCubic)
    (C : N.Word)
    (hC : N.IsCycleWord C) (hmin : ∀ z : N.Word, N.IsCycleWord z → size C ≤ size z)
    (h5 : 5 ≤ size C) (hG : 12 * size C ≤ G) (hm : size C + 2 ≤ m)
    (hr : size C + m + B₁ + B₂ + 3 ≤ networkRank N) :
    N.numCycles < 2 ^ (networkRank N - 1) := by
  obtain ⟨e, he⟩ := hC.exists_edge
  have hj : N.Joins e (N.src e) (N.dst e) := Or.inl ⟨rfl, rfl⟩
  have H : N.ShortSetting C e := ⟨hN, hcubic, hC, hmin, h5, he⟩
  have St := H.initial hj
  have hsz : size (C + unitWord e) = size C - 1 := by
    have h1 := size_add_of_subword (N.isSubword_unitWord he)
    rw [size_unitWord] at h1
    omega
  have hcount := ShortState.count_of_girth hpair H hG (by omega) (Or.inr rfl) (size C - 1) _ _ _
    St hsz
  rw [N.numPathsIn_congr (q' := fun g => g ≠ e)
    (fun g => ⟨fun h => h.1, fun h => ⟨h, fun k => k, fun k => k⟩⟩)] at hcount
  have e1 : networkRank N - size C + (size C - 1) = networkRank N - 1 := by omega
  rw [e1] at hcount
  -- the cycles through `e` and the other cycles
  have hE := N.numCycles_le_add_numPathsIn hj
  have hrank := N.networkRank_sub_ne hN hC.boundary_eq_zero he
  have hb := hbound V _ (N.sub fun g => g ≠ e) (by omega)
  have e2 : networkRank (N.sub fun g => g ≠ e) = networkRank N - 1 := by omega
  rw [e2] at hb
  -- the arithmetic
  have hX : 0 < 2 ^ (networkRank N - 1) := Nat.two_pow_pos _
  have h4 : 8 * 2 ^ (networkRank N - 1) ≤ (2 ^ m + 2) * 2 ^ (networkRank N - size C) := by
    have k1 : 8 * 2 ^ (networkRank N - 1) = 2 ^ (networkRank N - 1 + 3) := by
      rw [pow_add]
      norm_num
      ring
    have k2 : 2 ^ (networkRank N - 1 + 3) ≤ 2 ^ (m + (networkRank N - size C)) :=
      Nat.pow_le_pow_right (by norm_num) (by omega)
    have k3 : 2 ^ (m + (networkRank N - size C)) = 2 ^ m * 2 ^ (networkRank N - size C) :=
      pow_add 2 m _
    have k4 : 2 ^ m * 2 ^ (networkRank N - size C) ≤
        (2 ^ m + 2) * 2 ^ (networkRank N - size C) :=
      Nat.mul_le_mul_right _ (Nat.le_add_right _ _)
    omega
  have h5' : 2 ^ (m + 1) + (size C - 1) * (2 ^ (m + 1) * 2 ^ B₁) ≤ 2 ^ (networkRank N - 1) := by
    have k1 : size C ≤ 2 ^ size C := Nat.lt_two_pow_self.le
    have k2 : 1 ≤ 2 ^ B₁ := Nat.one_le_two_pow
    have k3 : 2 ^ (m + 1) + (size C - 1) * (2 ^ (m + 1) * 2 ^ B₁) ≤
        size C * (2 ^ (m + 1) * 2 ^ B₁) := by
      have k4 : 2 ^ (m + 1) ≤ 2 ^ (m + 1) * 2 ^ B₁ := Nat.le_mul_of_pos_right _ (by omega)
      have k5 : size C * (2 ^ (m + 1) * 2 ^ B₁) =
          (size C - 1) * (2 ^ (m + 1) * 2 ^ B₁) + 2 ^ (m + 1) * 2 ^ B₁ := by
        have k6 : size C = (size C - 1) + 1 := by omega
        rw [k6, Nat.add_mul, one_mul, Nat.add_sub_cancel]
      omega
    have k7 : size C * (2 ^ (m + 1) * 2 ^ B₁) ≤ 2 ^ size C * (2 ^ (m + 1) * 2 ^ B₁) :=
      Nat.mul_le_mul_right _ k1
    have k8 : 2 ^ size C * (2 ^ (m + 1) * 2 ^ B₁) = 2 ^ (size C + (m + 1 + B₁)) := by
      rw [pow_add 2 (size C), pow_add 2 (m + 1) B₁]
    have k9 : 2 ^ (size C + (m + 1 + B₁)) ≤ 2 ^ (networkRank N - 1) :=
      Nat.pow_le_pow_right (by norm_num) (by omega)
    omega
  exact short_cycle_arith (pow_succ' 2 m) rfl hE hb hcount h4 h5' hX

end Erdos1016.BoundaryTrace.Network

namespace Erdos1016.ExactMaximumSupport.Shortening.BoundedPortShortCycle
open BoundaryTrace BoundaryTrace.Network BoundaryDecay ExactMaximum
local instance (priority := 100) propDecidable (p : Prop) : Decidable p := Classical.propDecidable p

theorem shortCycleStatement : ShortCycleStatement := by
  intro D₀
  obtain ⟨B₁, hB₁⟩ := BoundedPortGirth.exists_bound (D₀ + 2) (12 * D₀)
  obtain ⟨B₂, hB₂⟩ := numCycles_le_of_large_rank_margin (D₀ + 2)
  refine ⟨D₀ + (D₀ + 2) + B₁ + B₂ + 12, ?_⟩
  rintro M hconn hcubic hloop hR hno4 ⟨x, hx, hlen⟩
  have hl : M.IsLoopless := M.isLoopless_iff_not_hasLoop.2 hloop
  have hN : M.looplessNetwork.graph.Connected := M.connected_iff_looplessNetwork.1 hconn
  have hcub : M.looplessNetwork.IsCubic := by
    intro v
    rw [← M.degree_eq_deg hl v]
    exact hcubic v
  have hrank : D₀ + (D₀ + 2) + B₁ + B₂ + 12 ≤ networkRank M.looplessNetwork := by
    rw [← M.cycleRank_eq_networkRank hl]
    exact hR
  -- the cut edges of a vertex set are the crossing edges
  have hcutcard : ∀ W : Finset M.Vertex,
      (M.cutEdges W).card = M.looplessNetwork.cutSize (fun v => v ∈ W) := by
    intro W
    have h2 : Nat.card {e : M.Edge // e ∈ M.cutEdges W} = (M.cutEdges W).card := by
      rw [Nat.card_eq_fintype_card, Fintype.card_coe]
    have h3 : M.looplessNetwork.cutSize (fun v => v ∈ W) =
        Nat.card {e : M.NonloopEdge // M.looplessNetwork.crosses (fun v => v ∈ W) e} := rfl
    obtain ⟨f, hf⟩ : ∃ f : {e : M.NonloopEdge // M.looplessNetwork.crosses (fun v => v ∈ W) e} →
        {e : M.Edge // e ∈ M.cutEdges W}, ∀ a, (f a).1 = a.1.1 :=
      ⟨fun e => ⟨e.1.1, (M.mem_cutEdges_iff_crosses W e.1).2 e.2⟩, fun _ => rfl⟩
    have hbij : Function.Bijective f := by
      constructor
      · intro a b hab
        have h1 : a.1.1 = b.1.1 := by rw [← hf a, ← hf b, hab]
        exact Subtype.ext (Subtype.ext h1)
      · intro b
        refine ⟨⟨⟨b.1, hl b.1⟩, (M.mem_cutEdges_iff_crosses W ⟨b.1, hl b.1⟩).1 b.2⟩, ?_⟩
        apply Subtype.ext
        rw [hf]
    have h1 := Nat.card_eq_of_bijective f hbij
    omega
  -- every cyclic cut of the network has at least five crossing edges
  have hcut : ∀ S : M.Vertex → Prop, M.looplessNetwork.IsCyclicCut S →
      5 ≤ M.looplessNetwork.cutSize S := by
    intro S hS
    obtain ⟨W, hW⟩ : ∃ W : Finset M.Vertex, (fun v => v ∈ W) = S :=
      ⟨Finset.univ.filter S, funext fun v => propext (by
        rw [Finset.mem_filter]
        exact ⟨fun h => h.2, fun h => ⟨Finset.mem_univ v, h⟩⟩)⟩
    subst hW
    refine Nat.le_of_not_lt fun hlt => ?_
    apply hno4
    refine ⟨W, ⟨?_, ?_⟩, ?_⟩
    · have h := hS.1
      rw [numCycles_sub] at h
      obtain ⟨⟨z, hz, hw⟩⟩ := Finite.card_pos_iff.1 h
      exact (M.hasCycleIn_iff_looplessNetwork hl W).2 ⟨z, hz, hw⟩
    · have h := hS.2
      rw [numCycles_sub] at h
      obtain ⟨⟨z, hz, hw⟩⟩ := Finite.card_pos_iff.1 h
      exact (M.hasCycleIn_iff_looplessNetwork hl Wᶜ).2 ⟨z, hz, fun g hg =>
        ⟨Finset.mem_compl.2 (hw g hg).1, Finset.mem_compl.2 (hw g hg).2⟩⟩
    · rw [hcutcard W]
      omega
  -- the short cycle of the multigraph is a short cycle of the network
  have hy : M.looplessNetwork.IsCycleWord (M.nonloopWord x) :=
    (M.isCycleWord_iff_looplessNetwork x (hl.word x)).1 hx
  have hysize : size (M.nonloopWord x) ≤ M.wordLength x := by
    unfold size FiniteMultiGraph.wordLength
    apply Finset.card_le_card_of_injOn (fun g : M.NonloopEdge => g.1)
    · intro g hg
      exact Finset.mem_filter.2 ⟨Finset.mem_univ g.1, (Finset.mem_filter.1 hg).2⟩
    · intro g _ g' _ hgg
      exact Subtype.ext hgg
  -- a shortest cycle of the network
  have hex : ∃ n, ∃ z : M.looplessNetwork.Word, M.looplessNetwork.IsCycleWord z ∧ size z = n :=
    ⟨_, M.nonloopWord x, hy, rfl⟩
  obtain ⟨C, hC, hCsize⟩ := Nat.find_spec hex
  have hmin : ∀ z : M.looplessNetwork.Word, M.looplessNetwork.IsCycleWord z →
      size C ≤ size z := by
    intro z hz
    rw [hCsize]
    exact Nat.find_min' hex ⟨z, hz, rfl⟩
  have hCD : size C < D₀ := lt_of_le_of_lt (hmin _ hy) (lt_of_le_of_lt hysize hlen)
  have h5 : 5 ≤ size C :=
    ExactMaximumSupport.NetworkShortCycleCut.four_lt_size_of_cyclic_cut_lower_bound
      M.looplessNetwork (fun v => le_of_eq (hcub v)) (by omega) hcut C hC
  have h := numCycles_lt_of_short_cycle_of_girth hB₁ hB₂ M.looplessNetwork hN hcub C hC hmin h5
    (by omega) (by omega) (by omega)
  rw [M.numCycles_eq_looplessNetwork hl, M.cycleRank_eq_networkRank hl]
  exact h


end Erdos1016.ExactMaximumSupport.Shortening.BoundedPortShortCycle
