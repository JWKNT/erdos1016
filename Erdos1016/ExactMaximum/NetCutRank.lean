import Erdos1016.ExactMaximum.NetCut

set_option autoImplicit false

/-!
# The rank of a network with a cut

Let `S` be a set of vertices of a connected network `N` such that both sides of the cut are
connected: any two vertices of `S` are joined by edges inside `S`, and any two vertices outside
`S` are joined by edges outside `S`. Let `b₁`, `b₂` be the ranks of the two sides and `d` the
number of crossing edges. Then

  `r + 1 = b₁ + b₂ + d`,

which is the relation `r = b₁ + b₂ + d - 1` that Section 6 of the paper "The maximum number of
cycles in a graph of large rank" uses for a cyclic cut (`networkRank_add_one_of_cut`).

The proof applies Euler's formula `network_rank_euler` to `N` and to the two sides. A side is a
network on all vertices of `N`, so its components are one component for its own vertices and one
component for every other vertex (`natCard_component_of_side`).
-/

noncomputable section
open scoped BigOperators

namespace Erdos1016.BoundaryTrace.Network

open BoundaryDecay

local instance netCutRankDecidable (p : Prop) : Decidable p := Classical.propDecidable p

variable {V E : Type*} [Fintype V] [Fintype E]

omit [Fintype E] in
/-- Let every edge of `M` have both ends in `S`, and let every vertex of `S` be joined to
`s₀ ∈ S`. Then the components of `M` are the component of `s₀` and one component for every
vertex outside `S`. -/
theorem natCard_component_of_side (M : Network V E) (S : V → Prop) {s₀ : V} (hs₀ : S s₀)
    (hedge : ∀ e, S (M.src e) ∧ S (M.dst e)) (hconn : ∀ u, S u → M.graph.Reachable s₀ u) :
    Nat.card M.Component = Nat.card {v : V // ¬ S v} + 1 := by
  -- a vertex outside `S` is joined to no other vertex
  have hiso : ∀ v w, ¬ S v → M.graph.Reachable v w → v = w := by
    intro v w hv hr
    obtain ⟨p⟩ := hr
    cases p with
    | nil => rfl
    | cons hadj _ =>
      exfalso
      obtain ⟨e, h | h⟩ := hadj
      · exact hv (h.1 ▸ (hedge e).1)
      · exact hv (h.2 ▸ (hedge e).2)
  let g : Option {v : V // ¬ S v} → M.Component := fun o =>
    match o with
    | none => M.graph.connectedComponentMk s₀
    | some v => M.graph.connectedComponentMk v.1
  have hg : Function.Bijective g := by
    constructor
    · intro a b hab
      rcases a with _ | a <;> rcases b with _ | b
      · rfl
      · exfalso
        have h1 : M.graph.connectedComponentMk s₀ = M.graph.connectedComponentMk b.1 := hab
        have h2 : M.graph.Reachable s₀ b.1 := SimpleGraph.ConnectedComponent.exact h1
        have h3 : b.1 = s₀ := hiso b.1 s₀ b.2 h2.symm
        exact b.2 (h3 ▸ hs₀)
      · exfalso
        have h1 : M.graph.connectedComponentMk a.1 = M.graph.connectedComponentMk s₀ := hab
        have h2 : M.graph.Reachable a.1 s₀ := SimpleGraph.ConnectedComponent.exact h1
        have h3 : a.1 = s₀ := hiso a.1 s₀ a.2 h2
        exact a.2 (h3 ▸ hs₀)
      · have h1 : M.graph.connectedComponentMk a.1 = M.graph.connectedComponentMk b.1 := hab
        have h2 : M.graph.Reachable a.1 b.1 := SimpleGraph.ConnectedComponent.exact h1
        exact congrArg some (Subtype.ext (hiso a.1 b.1 a.2 h2))
    · intro c
      refine SimpleGraph.ConnectedComponent.ind (fun u => ?_) c
      by_cases hu : S u
      · exact ⟨none, SimpleGraph.ConnectedComponent.sound (hconn u hu)⟩
      · exact ⟨some ⟨u, hu⟩, rfl⟩
  rw [← Nat.card_eq_of_bijective g hg, Finite.card_option]

/-- **The rank of a network with a cut.** Let `N` be connected, let `s₀ ∈ S` and `t₀ ∉ S`, let
every vertex of `S` be joined to `s₀` by edges inside `S`, and let every vertex outside `S` be
joined to `t₀` by edges outside `S`. Then the rank of `N` plus one is the sum of the ranks of the
two sides and of the number of crossing edges. -/
theorem networkRank_add_one_of_cut (N : Network V E) (S : V → Prop) {s₀ t₀ : V} (hs₀ : S s₀)
    (ht₀ : ¬ S t₀) (hN : N.graph.Connected)
    (hin : ∀ u, S u → (N.sub (N.inside S)).graph.Reachable s₀ u)
    (hout : ∀ u, ¬ S u → (N.sub (N.outside S)).graph.Reachable t₀ u) :
    networkRank N + 1 =
      networkRank (N.sub (N.inside S)) + networkRank (N.sub (N.outside S)) +
        Nat.card {e : E // N.crosses S e} := by
  have e0 := network_rank_euler N
  rw [connected_component_card N hN] at e0
  have e1 := network_rank_euler (N.sub (N.inside S))
  have e2 := network_rank_euler (N.sub (N.outside S))
  simp only [← Nat.card_eq_fintype_card] at e0 e1 e2
  have c1 : Nat.card (N.sub (N.inside S)).Component = Nat.card {v : V // ¬ S v} + 1 :=
    natCard_component_of_side (N.sub (N.inside S)) S hs₀ (fun e => e.2) hin
  have c2 : Nat.card (N.sub (N.outside S)).Component = Nat.card {v : V // ¬ ¬ S v} + 1 :=
    natCard_component_of_side (N.sub (N.outside S)) (fun v => ¬ S v) ht₀ (fun e => e.2) hout
  have c3 : Nat.card {v : V // ¬ ¬ S v} = Nat.card {v : V // S v} :=
    Nat.card_congr (Equiv.subtypeEquivRight fun _ => Classical.not_not)
  have hE : Nat.card E = Nat.card {e : E // N.inside S e} +
      (Nat.card {e : E // N.outside S e} + Nat.card {e : E // N.crosses S e}) := by
    rw [← natCard_or_of_disjoint (fun e : E => N.outside S e) (fun e => N.crosses S e)
        (fun e h1 h2 => N.not_crosses_of_outside h1 h2),
      ← natCard_or_of_disjoint (fun e : E => N.inside S e)
        (fun e => N.outside S e ∨ N.crosses S e)
        (fun e h1 h2 => by
          rcases h2 with h2 | h2
          · exact N.not_outside_of_inside h1 h2
          · exact N.not_crosses_of_inside h1 h2)]
    exact (Nat.card_congr
      (Equiv.subtypeUnivEquiv (fun e => N.inside_or_outside_or_crosses S e))).symm
  have hV : Nat.card V = Nat.card {v : V // S v} + Nat.card {v : V // ¬ S v} := by
    rw [← natCard_or_of_disjoint (fun v : V => S v) (fun v => ¬ S v) (fun v h1 h2 => h2 h1)]
    exact (Nat.card_congr (Equiv.subtypeUnivEquiv (fun v => Classical.em (S v)))).symm
  rw [c1] at e1
  rw [c2, c3] at e2
  omega

end Erdos1016.BoundaryTrace.Network
