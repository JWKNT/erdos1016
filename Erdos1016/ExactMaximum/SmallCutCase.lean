import Erdos1016.ExactMaximum.Cases
import Erdos1016.ExactMaximum.LooplessBridge
import Erdos1016.ExactMaximum.ThreeCut

set_option autoImplicit false

/-!
# Proposition 6.3: a cyclic cut of size at most three

This file proves Proposition 6.3 of the paper "The maximum number of cycles in a graph of large
rank" from the two statements about poles of `TwoCut.lean`:

* `numCycles_le_of_small_cut`: a connected cubic network of large rank `r` with a cyclic cut of
  size at most three has at most `2^(r-1) + 4 K 2^⌈r/2⌉` cycles;
* `threeCutStatement_of_poles`: `FewCyclesStatement` and `PoleCycleBoundStatement` imply
  `ThreeCutStatement`, the statement about multigraphs that the reduction to five cases uses.

The proof takes a cyclic cut with the smallest number of crossing edges. This number is not
zero, because the network is connected. The cases one, two and three are
`numCycles_le_of_bridge`, `numCycles_le_of_two_cut` and `numCycles_le_of_three_cut`.
-/

noncomputable section
open scoped BigOperators

namespace Erdos1016.ExactMaximum

open BoundaryTrace BoundaryTrace.Network BoundaryDecay

local instance smallCutCaseDecidable (p : Prop) : Decidable p := Classical.propDecidable p

/-- A cycle within a set of edges gives the part of the network on this set a cycle. -/
theorem numCycles_sub_pos {V E : Type*} [Fintype V] [Fintype E] (N : Network V E)
    (p : E → Prop) [Fintype {e : E // p e}] {y : N.Word} (hy : N.IsCycleWord y)
    (hw : Within y p) : 0 < (N.sub p).numCycles := by
  rw [numCycles_sub]
  haveI : Nonempty {x : N.Word // N.IsCycleWord x ∧ Within x p} := ⟨⟨y, hy, hw⟩⟩
  exact Nat.card_pos

/-- **Proposition 6.3 of the paper for networks.** Let `N` be a connected cubic network of rank
`r` with a cyclic cut of size at most three. If `r` is large, then `N` has at most
`2^(r-1) + 4 K 2^⌈r/2⌉` cycles. The constants `K` and `B` are those of the two statements about
poles. -/
theorem numCycles_le_of_small_cut {K B : ℕ} (hK : 1 ≤ K) (hF : FewCyclesWith K)
    (hG : PoleCycleBoundWith B) {V E : Type} [Fintype V] [Fintype E] (N : Network V E)
    (hN : N.graph.Connected) (hcubic : N.IsCubic) (S : V → Prop) (hcyc : N.IsCyclicCut S)
    (hS : N.cutSize S ≤ 3) (hR : 2 * max B (2000000 * K) + 10 ≤ networkRank N) :
    N.numCycles ≤ 2 ^ (networkRank N - 1) + 4 * K * 2 ^ ((networkRank N + 1) / 2) := by
  -- a cyclic cut with the smallest number of crossing edges
  have hex : ∃ d, ∃ S' : V → Prop, N.IsCyclicCut S' ∧ N.cutSize S' = d := ⟨_, S, hcyc, rfl⟩
  obtain ⟨S₀, hcyc₀, hS₀⟩ := Nat.find_spec hex
  have hmin : ∀ S' : V → Prop, N.IsCyclicCut S' → Nat.find hex ≤ N.cutSize S' :=
    fun S' h' => Nat.find_min' hex ⟨S', h', rfl⟩
  have hd3 : Nat.find hex ≤ 3 := le_trans (hmin S hcyc) hS
  generalize Nat.find hex = d at hS₀ hmin hd3
  have hcases : d = 0 ∨ d = 1 ∨ d = 2 ∨ d = 3 := by omega
  rcases hcases with rfl | rfl | rfl | rfl
  · -- no crossing edge: the network is not connected
    exfalso
    haveI : Nonempty V := hN.nonempty
    have hcyc' : 0 < (N.sub (N.inside fun v => ¬ S₀ v)).numCycles := hcyc₀.2
    obtain ⟨s₀, hs₀, -⟩ := N.exists_ne_of_numCycles_pos S₀ hcyc₀.1 (Classical.arbitrary V)
    obtain ⟨t₀, ht₀, -⟩ :=
      N.exists_ne_of_numCycles_pos (fun v => ¬ S₀ v) hcyc' (Classical.arbitrary V)
    have hclosed : ∀ e, S₀ (N.src e) ↔ S₀ (N.dst e) := by
      intro e
      refine Classical.not_not.1 fun hc => ?_
      haveI : Nonempty {g : E // N.crosses S₀ g} := ⟨⟨e, hc⟩⟩
      have hpos : 0 < Nat.card {g : E // N.crosses S₀ g} := Nat.card_pos
      have h0 : Nat.card {g : E // N.crosses S₀ g} = 0 := hS₀
      omega
    exact ht₀ (N.mem_of_reachable_of_closed S₀ hclosed (hN s₀ t₀) hs₀)
  · -- one crossing edge
    have hcard : (Finset.univ.filter fun g : E => N.crosses S₀ g).card = 1 := by
      rw [← natCard_subtype_eq_card_filter]
      exact hS₀
    obtain ⟨e, hCe⟩ := Finset.card_eq_one.1 hcard
    have hmem : ∀ g, N.crosses S₀ g ↔ g = e := by
      intro g
      have h1 : g ∈ (Finset.univ.filter fun g : E => N.crosses S₀ g) ↔ N.crosses S₀ g :=
        ⟨fun h => (Finset.mem_filter.1 h).2, fun h => Finset.mem_filter.2 ⟨Finset.mem_univ g, h⟩⟩
      rw [← h1, hCe, Finset.mem_singleton]
    obtain ⟨s, t, he, hs, ht⟩ := exists_joins_of_crosses N ((hmem e).2 rfl)
    have h := N.numCycles_le_of_bridge S₀ hN he hs ht (fun g hg => (hmem g).1 hg) hcyc₀.1
      hcyc₀.2
    exact le_trans h (Nat.le_add_right _ _)
  · -- two crossing edges
    have hmax : max B (16 * K) ≤ max B (2000000 * K) := max_le_max (le_refl B) (by omega)
    have h := numCycles_le_of_two_cut hK hF hG N hN hcubic hmin S₀ hS₀ hcyc₀ (by omega)
    have hle : 2 * K * 2 ^ ((networkRank N + 1) / 2) ≤
        4 * K * 2 ^ ((networkRank N + 1) / 2) := Nat.mul_le_mul_right _ (by omega)
    exact le_trans h (Nat.add_le_add_left hle _)
  · -- three crossing edges
    exact numCycles_le_of_three_cut hF hG N hN hcubic hmin S₀ hS₀ hcyc₀ hR

/-- **Proposition 6.3 of the paper**, from Theorem 5.4 for `ε = 1/1000` and Corollary 3.11 for
poles. A connected cubic multigraph of large rank `r`, without a loop and with a cyclic cut of
size at most three, has at most `2^(r-1) + K 2^⌈r/2⌉` cycles. -/
theorem threeCutStatement_of_poles (hF : FewCyclesStatement) (hG : PoleCycleBoundStatement) :
    ThreeCutStatement := by
  obtain ⟨K, hK, hF⟩ := hF
  obtain ⟨B, hG⟩ := hG
  refine ⟨4 * K, 2 * max B (2000000 * K) + 10, ?_⟩
  rintro M hconn hcubic hloop hR ⟨U, hU, hcard⟩
  have hl : M.IsLoopless := M.isLoopless_iff_not_hasLoop.2 hloop
  have hN : M.looplessNetwork.graph.Connected := M.connected_iff_looplessNetwork.1 hconn
  have hcub : M.looplessNetwork.IsCubic := by
    intro v
    rw [← M.degree_eq_deg hl v]
    exact hcubic v
  -- the two sides contain a cycle
  have hcyc : M.looplessNetwork.IsCyclicCut (fun v => v ∈ U) := by
    constructor
    · obtain ⟨y, hy, hw⟩ := (M.hasCycleIn_iff_looplessNetwork hl U).1 hU.1
      exact numCycles_sub_pos _ _ hy hw
    · obtain ⟨y, hy, hw⟩ := (M.hasCycleIn_iff_looplessNetwork hl Uᶜ).1 hU.2
      exact numCycles_sub_pos _ _ hy
        (fun e he => ⟨Finset.mem_compl.1 (hw e he).1, Finset.mem_compl.1 (hw e he).2⟩)
  -- the crossing edges are cut edges
  have hsize : M.looplessNetwork.cutSize (fun v => v ∈ U) ≤ 3 := by
    obtain ⟨f, hf⟩ : ∃ f : {e : M.NonloopEdge // M.looplessNetwork.crosses (fun v => v ∈ U) e} →
        {e : M.Edge // e ∈ M.cutEdges U}, ∀ a, (f a).1 = a.1.1 :=
      ⟨fun e => ⟨e.1.1, (M.mem_cutEdges_iff_crosses U e.1).2 e.2⟩, fun _ => rfl⟩
    have hinj : Function.Injective f := by
      intro a b hab
      have h1 : a.1.1 = b.1.1 := by rw [← hf a, ← hf b, hab]
      exact Subtype.ext (Subtype.ext h1)
    have h1 := Nat.card_le_card_of_injective f hinj
    have h2 : Nat.card {e : M.Edge // e ∈ M.cutEdges U} = (M.cutEdges U).card := by
      rw [Nat.card_eq_fintype_card, Fintype.card_coe]
    have h3 : M.looplessNetwork.cutSize (fun v => v ∈ U) =
        Nat.card {e : M.NonloopEdge // M.looplessNetwork.crosses (fun v => v ∈ U) e} := rfl
    omega
  have h := numCycles_le_of_small_cut hK hF hG M.looplessNetwork hN hcub (fun v => v ∈ U) hcyc
    hsize (by rw [← M.cycleRank_eq_networkRank hl]; exact hR)
  rw [M.numCycles_eq_looplessNetwork hl, M.cycleRank_eq_networkRank hl]
  exact h

end Erdos1016.ExactMaximum
