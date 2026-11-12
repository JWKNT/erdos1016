import Erdos1016.Graph.TerminalForest

set_option autoImplicit false
set_option maxHeartbeats 1000000

/-!
# Counting degree-two strings in a finite forest

The forest degree ledger bounds the number of components of a degree-two
region by the number of vertices outside it. A boundary-restricted version
then ignores unrelated vertices and isolated components.
-/

noncomputable section
open scoped BigOperators
namespace Erdos1016.ExactMaximumSupport.LargeGirth.TerminalStringCount

variable {V : Type*} [Fintype V]

local instance terminalCountDecidable (p : Prop) : Decidable p := Classical.propDecidable p
local instance terminalCountDecidableEq : DecidableEq V := Classical.decEq V
local instance componentFintype (G : SimpleGraph V) : Fintype G.ConnectedComponent :=
  Fintype.ofSurjective G.connectedComponentMk Quot.mk_surjective

def componentVertexEquiv (G : SimpleGraph V) : (Σ c : G.ConnectedComponent, c.supp) ≃ V where
  toFun x := x.2.1
  invFun v := ⟨G.connectedComponentMk v,
    ⟨v, by simp [SimpleGraph.ConnectedComponent.mem_supp_iff]⟩⟩
  left_inv := by
    rintro ⟨c, ⟨v, hv⟩⟩
    have hc := (SimpleGraph.ConnectedComponent.mem_supp_iff c v).mp hv
    subst c
    rfl
  right_inv _ := rfl

theorem sum_components (G : SimpleGraph V) (f : V → ℕ) :
    (∑ c : G.ConnectedComponent, ∑ v : c.supp, f v.1) = ∑ v, f v := by
  rw [← Fintype.sum_sigma' (fun (c : G.ConnectedComponent) (v : c.supp) => f v.1)]
  exact Fintype.sum_equiv (componentVertexEquiv G) _ _ (fun _ => rfl)

theorem forest_degree_ledger (G : SimpleGraph V) (hG : G.IsAcyclic) :
    (∑ v, G.degree v) + 2 * Fintype.card G.ConnectedComponent = 2 * Fintype.card V := by
  have hc (c : G.ConnectedComponent) :
      (∑ v : c.supp, G.degree v.1) + 2 = 2 * Fintype.card c.supp := by
    have ht : (G.induce c.supp).IsTree := by
      refine ⟨c.connected_induce_supp, ?_⟩
      intro v p hp
      let emb : G.induce c.supp ↪g G := SimpleGraph.Embedding.induce c.supp
      exact hG (p.map emb.toHom) (hp.map emb.injective)
    have he := ht.card_edgeFinset
    have hd := (G.induce c.supp).sum_degrees_eq_twice_card_edges
    simp only [TerminalForest.component_degree] at hd
    omega
  have hh := Finset.sum_congr (s₁ := Finset.univ) rfl (fun c _ => hc c)
  have hv : (∑ c : G.ConnectedComponent, Fintype.card c.supp) = Fintype.card V := by
    simpa only [Fintype.card_sigma] using Fintype.card_congr (componentVertexEquiv G)
  simp only [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ,
    nsmul_eq_mul, Nat.cast_id, ← Finset.mul_sum] at hh
  rw [sum_components G (fun v => G.degree v), hv] at hh
  omega

theorem degree_eq_sum (G : SimpleGraph V) (v : V) :
    G.degree v = ∑ w : V, if G.Adj v w then 1 else 0 := by
  simp only [SimpleGraph.degree, SimpleGraph.neighborFinset_eq_filter,
    Finset.card_eq_sum_ones, Finset.sum_filter]

omit [Fintype V] in
theorem induced_degree_eq_sum (G : SimpleGraph V) (W : Finset V) (v : (↑W : Set V)) :
    (G.induce (↑W : Set V)).degree v = ∑ w ∈ W, if G.Adj v.1 w then 1 else 0 := by
  rw [degree_eq_sum]
  exact Finset.sum_coe_sort W (fun w => if G.Adj v.1 w then 1 else 0)

def boundaryCount (G : SimpleGraph V) (W : Finset V) : ℕ :=
  ∑ v ∈ W, ∑ w ∈ Wᶜ, if G.Adj v w then 1 else 0

theorem induced_degree_boundary (G : SimpleGraph V) (W : Finset V) :
    (∑ v : (↑W : Set V), (G.induce (↑W : Set V)).degree v) + boundaryCount G W =
      ∑ v ∈ W, G.degree v := by
  simp only [induced_degree_eq_sum]
  rw [Finset.sum_finset_coe (fun v => ∑ w ∈ W, if G.Adj v w then 1 else 0) W]
  unfold boundaryCount
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro v _
  rw [Finset.sum_add_sum_compl, ← degree_eq_sum]

theorem boundary_le_complement_degree (G : SimpleGraph V) (W : Finset V) :
    boundaryCount G W ≤ ∑ w ∈ Wᶜ, G.degree w := by
  unfold boundaryCount
  rw [Finset.sum_comm]
  apply Finset.sum_le_sum
  intro w _
  rw [degree_eq_sum]
  have hs : (∑ v ∈ W, if G.Adj v w then 1 else 0) =
      ∑ v ∈ W, if G.Adj w v then 1 else 0 := by
    apply Finset.sum_congr rfl
    intro v _
    rw [G.adj_comm]
  rw [hs]
  exact Finset.sum_le_sum_of_subset (Finset.subset_univ W)

/-- Every degree-two component consumes at least one vertex outside the region. -/
theorem component_count_le_complement (G : SimpleGraph V) (hG : G.IsAcyclic)
    (W : Finset V) (hdegree : ∀ v ∈ W, G.degree v = 2) :
    Nat.card (G.induce (↑W : Set V)).ConnectedComponent ≤ Wᶜ.card := by
  have hW : (G.induce (↑W : Set V)).IsAcyclic := by
    intro v p hp
    let emb : G.induce (↑W : Set V) ↪g G := SimpleGraph.Embedding.induce (↑W : Set V)
    exact hG (p.map emb.toHom) (hp.map emb.injective)
  have hall := forest_degree_ledger G hG
  have hinside := forest_degree_ledger (G.induce (↑W : Set V)) hW
  have hsplit := induced_degree_boundary G W
  have hbound := boundary_le_complement_degree G W
  have hdeg : (∑ v ∈ W, G.degree v) = 2 * W.card := by
    rw [Finset.sum_congr rfl (fun v hv => hdegree v hv)]
    simp [Nat.mul_comm]
  have htotal := Finset.sum_add_sum_compl W (fun v => G.degree v)
  have hcard := Finset.card_add_card_compl W
  have hWcard : Fintype.card ((↑W : Set V)) = W.card := Fintype.card_coe W
  rw [hWcard] at hinside
  rw [hdeg] at hsplit htotal
  rw [Nat.card_eq_fintype_card]
  omega

/-- Unrelated ambient vertices do not affect the string count. Every edge
leaving the degree-two region must end in the designated boundary set. -/
theorem component_count_le_boundary (G : SimpleGraph V) (hG : G.IsAcyclic)
    (W B : Finset V) (hdegree : ∀ v ∈ W, G.degree v = 2)
    (hboundary : ∀ v ∈ W, ∀ w, G.Adj v w → w ∉ W → w ∈ B) :
    Nat.card (G.induce (↑W : Set V)).ConnectedComponent ≤ B.card := by
  let Z : Set V := ↑(W ∪ B)
  letI : Fintype Z := Subtype.fintype (Membership.mem Z)
  letI : DecidableEq Z := Classical.decEq Z
  let H := G.induce Z
  let S : Finset Z := Finset.univ.filter fun v => v.1 ∈ W
  have hH : H.IsAcyclic := by
    intro v p hp
    let emb : H ↪g G := SimpleGraph.Embedding.induce Z
    exact hG (p.map emb.toHom) (hp.map emb.injective)
  have hd : ∀ v ∈ S, H.degree v = 2 := by
    intro v hv
    have hvW : v.1 ∈ W := (Finset.mem_filter.mp hv).2
    have he : H.degree v = G.degree v.1 := by
      apply G.degree_induce_of_neighborSet_subset (s := Z) (v := v)
      intro w hw
      by_cases hwW : w ∈ W
      · exact Finset.mem_union_left B hwW
      · exact Finset.mem_union_right W (hboundary v.1 hvW w hw hwW)
    exact he.trans (hdegree v.1 hvW)
  let iso : H.induce (↑S : Set Z) ≃g G.induce (↑W : Set V) :=
    { toFun := fun v => ⟨v.1.1, (Finset.mem_filter.mp v.2).2⟩
      invFun := fun v => ⟨⟨v.1, Finset.mem_union_left B v.2⟩, by simp [S, v.2]⟩
      left_inv := by intro v; rfl
      right_inv := by intro v; rfl
      map_rel_iff' := by intro v w; rfl }
  have hcard : Sᶜ.card ≤ B.card := by
    let f : (Sᶜ : Finset Z) → B := fun v => ⟨v.1.1, by
      have hnot : v.1.1 ∉ W := by simpa only [S, Finset.mem_compl, Finset.mem_filter,
        Finset.mem_univ, true_and] using v.2
      exact (Finset.mem_union.mp v.1.2).resolve_left hnot⟩
    have hinj : Function.Injective f := by
      intro v w h
      apply Subtype.ext
      apply Subtype.ext
      exact congrArg (fun a : B => (a : V)) h
    simpa only [Fintype.card_coe] using Fintype.card_le_of_injective f hinj
  rw [← Nat.card_congr iso.connectedComponentEquiv]
  exact (component_count_le_complement H hH S hd).trans hcard

end Erdos1016.ExactMaximumSupport.LargeGirth.TerminalStringCount
