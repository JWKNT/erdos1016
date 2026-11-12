import Erdos1016.ExactMaximum.NetEmbed
import Erdos1016.ExactMaximum.NetJoin
import Erdos1016.ExactMaximum.NetCutFour
import Erdos1016.ExactMaximum.NetBridgeCut

set_option autoImplicit false

/-!
# A new vertex of degree two

Lemma 5.7 of the paper "The maximum number of cycles in a graph of large rank" changes a pole `N`
into a pole `N'` and applies Theorem 5.4 to two ports of `N'`. The changes are: a new vertex that
is joined to two ports (parts (b) and (c)), and a new edge between two ports (part (d)). A new
edge with a vertex in its middle is a new vertex that is joined to the two ports, and the middle
vertex does not change the paths and cycles that the lemma counts. So one construction is enough.

The network `N.addVertex a b` has the vertices `some v` of `N` and the new vertex `none`. Its
edges are the edges `inl e` of `N`, the edge `inr false` from `none` to `a`, and the edge
`inr true` from `none` to `b`. This file proves:

* the rank grows by at most one (`networkRank_addVertex_le`);
* a path of `N` from `a` to `b` and the two new edges form a cycle
  (`numPaths_le_numCycles_addVertex`);
* a path of `N` from `a` or from `b` to `c` and one new edge form a path from the new vertex to
  `c` (`numPaths_add_le_numPaths_addVertex`);
* a path of `N` from `c` to `d`, and a pair of disjoint paths of `N` between `c, d` and `a, b`
  with the two new edges, are paths from `c` to `d` (`numPaths_pairs_le_numPaths_addVertex`);
* the degrees, and that the result is a pole if `N` is a pole and `a ≠ b` are ports
  (`isWeakPole_addVertex`).
-/

noncomputable section
open scoped BigOperators

namespace Erdos1016.BoundaryTrace.Network

open BoundaryDecay

local instance netAddVertexDecidable (p : Prop) : Decidable p := Classical.propDecidable p

/-! ### More about embedded words -/

namespace Embed

universe u₁ u₂ u₃ u₄

variable {V : Type u₁} {E : Type u₂} {V' : Type u₃} {E' : Type u₄}
variable {N : Network V E} {N' : Network V' E'} (R : Embed N N')

theorem push_add (x y : E → Bit) : R.push (x + y) = R.push x + R.push y := by
  funext e'
  by_cases he : R.image e'
  · obtain ⟨e, rfl⟩ := he
    rw [Pi.add_apply, R.push_apply, R.push_apply, R.push_apply]
    rfl
  · rw [Pi.add_apply, R.push_apply_of_not_image _ he, R.push_apply_of_not_image _ he,
      R.push_apply_of_not_image _ he, add_zero]

/-- A connection of the smaller network is a connection of the larger network. -/
theorem reachable_push {u v : V} (h : N.graph.Reachable u v) :
    N'.graph.Reachable (R.φ u) (R.φ v) := by
  refine N.mem_of_reachable_of_closed (fun z => N'.graph.Reachable (R.φ u) (R.φ z)) ?_ h
    (SimpleGraph.Reachable.refl _)
  intro g
  have hadj : N'.graph.Adj (R.φ (N.src g)) (R.φ (N.dst g)) :=
    ⟨R.ψ g, Or.inl ⟨R.src g, R.dst g⟩⟩
  exact ⟨fun k => k.trans hadj.reachable, fun k => k.trans hadj.symm.reachable⟩

variable [Fintype E] [Fintype E']

/-- The degree of an embedded word at an embedded vertex. -/
theorem deg_push (x : E → Bit) (v : V) : N'.deg (R.push x) (R.φ v) = N.deg x v := by
  unfold deg
  symm
  apply Finset.card_bij (fun e _ => R.ψ e)
  · intro e he
    rw [Finset.mem_filter] at he ⊢
    refine ⟨Finset.mem_univ _, ?_, ?_⟩
    · rw [R.push_apply]
      exact he.2.1
    · rw [R.src, R.dst]
      rcases he.2.2 with h | h
      · exact Or.inl (by rw [h])
      · exact Or.inr (by rw [h])
  · intro e₁ _ e₂ _ h
    exact R.ψ_inj h
  · intro e' he'
    rw [Finset.mem_filter] at he'
    obtain ⟨e, rfl⟩ := R.within_push x e' he'.2.1
    refine ⟨e, ?_, rfl⟩
    rw [Finset.mem_filter]
    refine ⟨Finset.mem_univ _, ?_, ?_⟩
    · have h := he'.2.1
      rwa [R.push_apply] at h
    · have h := he'.2.2
      rw [R.src, R.dst] at h
      rcases h with h | h
      · exact Or.inl (R.φ_inj h)
      · exact Or.inr (R.φ_inj h)

omit [Fintype E] in
/-- An embedded word has degree zero at a vertex outside the image. -/
theorem deg_push_of_not_range (x : E → Bit) {v' : V'} (h : ¬ ∃ v, R.φ v = v') :
    N'.deg (R.push x) v' = 0 := by
  apply N'.deg_eq_zero_of_forall
  intro e' he'
  refine Classical.not_not.1 fun hne => ?_
  obtain ⟨e, rfl⟩ := R.within_push x e' hne
  rw [R.src, R.dst] at he'
  rcases he' with k | k
  · exact h ⟨_, k⟩
  · exact h ⟨_, k⟩

/-- Embedded words are vertex-disjoint if the words are. -/
theorem vertexDisjoint_push {A B : E → Bit} (h : N.VertexDisjoint A B) :
    N'.VertexDisjoint (R.push A) (R.push B) := by
  intro v'
  by_cases hv : ∃ v, R.φ v = v'
  · obtain ⟨v, rfl⟩ := hv
    rw [R.deg_push, R.deg_push]
    exact h v
  · exact Or.inl (R.deg_push_of_not_range A hv)

end Embed

variable {V E : Type*}

/-! ### The construction -/

/-- The network with the new vertex `none`, which is joined to `a` by the edge `inr false` and
to `b` by the edge `inr true`. -/
def addVertex (N : Network V E) (a b : V) : Network (Option V) (E ⊕ Bool) where
  src g := Sum.elim (fun e => some (N.src e)) (fun _ => none) g
  dst g := Sum.elim (fun e => some (N.dst e)) (fun c => some (cond c b a)) g
  noLoops g := by
    rcases g with e | c
    · exact fun h => N.noLoops e (Option.some.inj h)
    · exact fun h => Option.noConfusion h

/-- The network `N` inside `N.addVertex a b`. -/
def addVertexEmbed (N : Network V E) (a b : V) : Embed N (N.addVertex a b) where
  φ := some
  ψ := Sum.inl
  φ_inj := Option.some_injective V
  ψ_inj := Sum.inl_injective
  src _ := rfl
  dst _ := rfl

section Basic

variable (N : Network V E) (a b : V)

theorem addVertex_joins_left : (N.addVertex a b).Joins (Sum.inr false) (some a) none :=
  Or.inr ⟨rfl, rfl⟩

theorem addVertex_joins_right : (N.addVertex a b).Joins (Sum.inr true) (some b) none :=
  Or.inr ⟨rfl, rfl⟩

theorem addVertex_push_inl (x : E → Bit) (e : E) :
    (N.addVertexEmbed a b).push x (Sum.inl e) = x e :=
  (N.addVertexEmbed a b).push_apply x e

theorem addVertex_push_inr (x : E → Bit) (c : Bool) :
    (N.addVertexEmbed a b).push x (Sum.inr c) = 0 :=
  (N.addVertexEmbed a b).push_apply_of_not_image x (by
    rintro ⟨e, he⟩
    exact Sum.inl_ne_inr he)

/-- The new vertex is not an old vertex. -/
theorem addVertex_not_range : ¬ ∃ v, (N.addVertexEmbed a b).φ v = none := by
  rintro ⟨v, hv⟩
  exact Option.noConfusion hv

end Basic

variable [Fintype V] [Fintype E]

/-- Two injective maps with disjoint images. -/
theorem natCard_add_le_of_injective {α β γ : Type*} [Finite γ] (f₁ : α → γ) (f₂ : β → γ)
    (h₁ : Function.Injective f₁) (h₂ : Function.Injective f₂) (h : ∀ a b, f₁ a ≠ f₂ b) :
    Nat.card α + Nat.card β ≤ Nat.card γ := by
  haveI : Finite α := Finite.of_injective f₁ h₁
  haveI : Finite β := Finite.of_injective f₂ h₂
  rw [← Nat.card_sum]
  apply Nat.card_le_card_of_injective (Sum.elim f₁ f₂)
  rintro (x | x) (y | y) hxy
  · exact congrArg Sum.inl (h₁ hxy)
  · exact absurd hxy (h x y)
  · exact absurd hxy.symm (h y x)
  · exact congrArg Sum.inr (h₂ hxy)

section Main

variable (N : Network V E) (a b : V)

/-! ### Cycles through the new vertex -/

/-- A path of `N` from `a` to `b` and the two new edges form a cycle. -/
theorem isCycleWord_addVertex {P : N.Word} (hP : N.IsPathWord a b P) :
    (N.addVertex a b).IsCycleWord
      ((N.addVertexEmbed a b).push P + unitWord (Sum.inr true) + unitWord (Sum.inr false)) := by
  have hP' : (N.addVertex a b).IsPathWord (some a) (some b) ((N.addVertexEmbed a b).push P) :=
    ((N.addVertexEmbed a b).isPathWord_push_iff a b P).2 hP
  have h0 : (N.addVertex a b).deg ((N.addVertexEmbed a b).push P) none = 0 :=
    (N.addVertexEmbed a b).deg_push_of_not_range P (N.addVertex_not_range a b)
  have h1 := hP'.add_pendant (N.addVertex_joins_right a b) h0
  refine h1.add_closing (N.addVertex_joins_left a b) ?_
  rw [Pi.add_apply, N.addVertex_push_inr, zero_add, unitWord_apply,
    if_neg (fun h : (Sum.inr true : E ⊕ Bool) = Sum.inr false => Bool.noConfusion (Sum.inr.inj h))]

/-- **Paths between `a` and `b` are cycles of the new network.** -/
theorem numPaths_le_numCycles_addVertex :
    N.numPaths a b ≤ (N.addVertex a b).numCycles := by
  obtain ⟨f, hf⟩ : ∃ f : {P : N.Word // N.IsPathWord a b P} →
      {Z : (N.addVertex a b).Word // (N.addVertex a b).IsCycleWord Z},
      ∀ P, (f P).1 = (N.addVertexEmbed a b).push P.1 + unitWord (Sum.inr true) +
        unitWord (Sum.inr false) :=
    ⟨fun P => ⟨_, N.isCycleWord_addVertex a b P.2⟩, fun _ => rfl⟩
  apply Nat.card_le_card_of_injective f
  intro P Q h
  have h1 : (N.addVertexEmbed a b).push P.1 + unitWord (Sum.inr true) +
      unitWord (Sum.inr false) = (N.addVertexEmbed a b).push Q.1 + unitWord (Sum.inr true) +
      unitWord (Sum.inr false) := by rw [← hf P, ← hf Q, h]
  exact Subtype.ext
    ((N.addVertexEmbed a b).push_injective (add_right_cancel (add_right_cancel h1)))

/-! ### Paths from the new vertex -/

/-- A path of `N` from `a` to `c` and the new edge at `a` form a path from the new vertex. -/
theorem isPathWord_addVertex_left {c : V} {P : N.Word} (hP : N.IsPathWord a c P) :
    (N.addVertex a b).IsPathWord none (some c)
      ((N.addVertexEmbed a b).push P + unitWord (Sum.inr false)) := by
  have hP' : (N.addVertex a b).IsPathWord (some c) (some a) ((N.addVertexEmbed a b).push P) :=
    (((N.addVertexEmbed a b).isPathWord_push_iff a c P).2 hP).symm
  have h0 : (N.addVertex a b).deg ((N.addVertexEmbed a b).push P) none = 0 :=
    (N.addVertexEmbed a b).deg_push_of_not_range P (N.addVertex_not_range a b)
  exact (hP'.add_pendant (N.addVertex_joins_left a b) h0).symm

/-- A path of `N` from `b` to `c` and the new edge at `b` form a path from the new vertex. -/
theorem isPathWord_addVertex_right {c : V} {P : N.Word} (hP : N.IsPathWord b c P) :
    (N.addVertex a b).IsPathWord none (some c)
      ((N.addVertexEmbed a b).push P + unitWord (Sum.inr true)) := by
  have hP' : (N.addVertex a b).IsPathWord (some c) (some b) ((N.addVertexEmbed a b).push P) :=
    (((N.addVertexEmbed a b).isPathWord_push_iff b c P).2 hP).symm
  have h0 : (N.addVertex a b).deg ((N.addVertexEmbed a b).push P) none = 0 :=
    (N.addVertexEmbed a b).deg_push_of_not_range P (N.addVertex_not_range a b)
  exact (hP'.add_pendant (N.addVertex_joins_right a b) h0).symm

/-- **Paths from the new vertex.** The paths of `N` from `a` to `c` and from `b` to `c` give
different paths from the new vertex to `c`. -/
theorem numPaths_add_le_numPaths_addVertex (c : V) :
    N.numPaths a c + N.numPaths b c ≤ (N.addVertex a b).numPaths none (some c) := by
  obtain ⟨f₁, hf₁⟩ : ∃ f : {P : N.Word // N.IsPathWord a c P} →
      {W : (N.addVertex a b).Word // (N.addVertex a b).IsPathWord none (some c) W},
      ∀ P, (f P).1 = (N.addVertexEmbed a b).push P.1 + unitWord (Sum.inr false) :=
    ⟨fun P => ⟨_, N.isPathWord_addVertex_left a b P.2⟩, fun _ => rfl⟩
  obtain ⟨f₂, hf₂⟩ : ∃ f : {P : N.Word // N.IsPathWord b c P} →
      {W : (N.addVertex a b).Word // (N.addVertex a b).IsPathWord none (some c) W},
      ∀ P, (f P).1 = (N.addVertexEmbed a b).push P.1 + unitWord (Sum.inr true) :=
    ⟨fun P => ⟨_, N.isPathWord_addVertex_right a b P.2⟩, fun _ => rfl⟩
  apply natCard_add_le_of_injective f₁ f₂
  · intro P Q h
    have h1 : (N.addVertexEmbed a b).push P.1 + unitWord (Sum.inr false) =
        (N.addVertexEmbed a b).push Q.1 + unitWord (Sum.inr false) := by rw [← hf₁ P, ← hf₁ Q, h]
    exact Subtype.ext ((N.addVertexEmbed a b).push_injective (add_right_cancel h1))
  · intro P Q h
    have h1 : (N.addVertexEmbed a b).push P.1 + unitWord (Sum.inr true) =
        (N.addVertexEmbed a b).push Q.1 + unitWord (Sum.inr true) := by rw [← hf₂ P, ← hf₂ Q, h]
    exact Subtype.ext ((N.addVertexEmbed a b).push_injective (add_right_cancel h1))
  · intro P Q h
    have h1 : ((N.addVertexEmbed a b).push P.1 + unitWord (Sum.inr false) :
        E ⊕ Bool → Bit) (Sum.inr false) = ((N.addVertexEmbed a b).push Q.1 +
        unitWord (Sum.inr true) : E ⊕ Bool → Bit) (Sum.inr false) := by
      rw [← hf₁ P, ← hf₂ Q, h]
    rw [Pi.add_apply, Pi.add_apply, N.addVertex_push_inr, N.addVertex_push_inr, unitWord_apply,
      unitWord_apply, if_pos rfl,
      if_neg (fun k : (Sum.inr true : E ⊕ Bool) = Sum.inr false =>
        Bool.noConfusion (Sum.inr.inj k)), zero_add, zero_add] at h1
    exact one_ne_zero h1

/-! ### Paths between old vertices through the new vertex -/

/-- A pair of disjoint paths of `N`, from `c` to `a` and from `b` to `d`, and the two new edges
form a path from `c` to `d`. -/
theorem isPathWord_addVertex_pair {c d : V} {A B : N.Word} (h : N.IsPathPair c a b d A B) :
    (N.addVertex a b).IsPathWord (some c) (some d)
      ((N.addVertexEmbed a b).push A + (N.addVertexEmbed a b).push B +
        (unitWord (Sum.inr false) + unitWord (Sum.inr true))) := by
  have hA' : (N.addVertex a b).IsPathWord (some c) (some a) ((N.addVertexEmbed a b).push A) :=
    ((N.addVertexEmbed a b).isPathWord_push_iff c a A).2 h.1
  have hB' : (N.addVertex a b).IsPathWord (some b) (some d) ((N.addVertexEmbed a b).push B) :=
    ((N.addVertexEmbed a b).isPathWord_push_iff b d B).2 h.2.1
  have h0 : (N.addVertex a b).deg ((N.addVertexEmbed a b).push A) none = 0 :=
    (N.addVertexEmbed a b).deg_push_of_not_range A (N.addVertex_not_range a b)
  have h0' : (N.addVertex a b).deg ((N.addVertexEmbed a b).push B) none = 0 :=
    (N.addVertexEmbed a b).deg_push_of_not_range B (N.addVertex_not_range a b)
  have hBa : (N.addVertex a b).deg ((N.addVertexEmbed a b).push B) (some a) = 0 := by
    have h1 := (N.addVertexEmbed a b).deg_push B a
    rw [h.2.2.deg_right_eq_zero h.1.deg_right_pos] at h1
    exact h1
  have h1 := hA'.add_pendant (N.addVertex_joins_left a b) h0
  have hd : (N.addVertex a b).VertexDisjoint
      ((N.addVertexEmbed a b).push A + unitWord (Sum.inr false))
      ((N.addVertexEmbed a b).push B) :=
    VertexDisjoint.add_left ((N.addVertexEmbed a b).vertexDisjoint_push h.2.2)
      ((N.addVertex a b).vertexDisjoint_unitWord (N.addVertex_joins_left a b) hBa h0').symm
  have h2 := h1.glue hB' (N.addVertex_joins_right a b).symm hd
  have e : (N.addVertexEmbed a b).push A + unitWord (Sum.inr false) +
      (N.addVertexEmbed a b).push B + unitWord (Sum.inr true) =
      (N.addVertexEmbed a b).push A + (N.addVertexEmbed a b).push B +
        (unitWord (Sum.inr false) + unitWord (Sum.inr true)) := by abel
  rw [← e]
  exact h2

/-- A pair of disjoint paths of `N`, from `c` to `b` and from `a` to `d`, and the two new edges
form a path from `c` to `d`. -/
theorem isPathWord_addVertex_pair' {c d : V} {A B : N.Word} (h : N.IsPathPair c b a d A B) :
    (N.addVertex a b).IsPathWord (some c) (some d)
      ((N.addVertexEmbed a b).push A + (N.addVertexEmbed a b).push B +
        (unitWord (Sum.inr false) + unitWord (Sum.inr true))) := by
  have hA' : (N.addVertex a b).IsPathWord (some c) (some b) ((N.addVertexEmbed a b).push A) :=
    ((N.addVertexEmbed a b).isPathWord_push_iff c b A).2 h.1
  have hB' : (N.addVertex a b).IsPathWord (some a) (some d) ((N.addVertexEmbed a b).push B) :=
    ((N.addVertexEmbed a b).isPathWord_push_iff a d B).2 h.2.1
  have h0 : (N.addVertex a b).deg ((N.addVertexEmbed a b).push A) none = 0 :=
    (N.addVertexEmbed a b).deg_push_of_not_range A (N.addVertex_not_range a b)
  have h0' : (N.addVertex a b).deg ((N.addVertexEmbed a b).push B) none = 0 :=
    (N.addVertexEmbed a b).deg_push_of_not_range B (N.addVertex_not_range a b)
  have hBb : (N.addVertex a b).deg ((N.addVertexEmbed a b).push B) (some b) = 0 := by
    have h1 := (N.addVertexEmbed a b).deg_push B b
    rw [h.2.2.deg_right_eq_zero h.1.deg_right_pos] at h1
    exact h1
  have h1 := hA'.add_pendant (N.addVertex_joins_right a b) h0
  have hd : (N.addVertex a b).VertexDisjoint
      ((N.addVertexEmbed a b).push A + unitWord (Sum.inr true))
      ((N.addVertexEmbed a b).push B) :=
    VertexDisjoint.add_left ((N.addVertexEmbed a b).vertexDisjoint_push h.2.2)
      ((N.addVertex a b).vertexDisjoint_unitWord (N.addVertex_joins_right a b) hBb h0').symm
  have h2 := h1.glue hB' (N.addVertex_joins_left a b).symm hd
  have e : (N.addVertexEmbed a b).push A + unitWord (Sum.inr true) +
      (N.addVertexEmbed a b).push B + unitWord (Sum.inr false) =
      (N.addVertexEmbed a b).push A + (N.addVertexEmbed a b).push B +
        (unitWord (Sum.inr false) + unitWord (Sum.inr true)) := by abel
  rw [← e]
  exact h2

/-- **Paths between two old vertices.** The paths of `N` from `c` to `d`, and the pairs of
disjoint paths of `N` between `c, d` and `a, b` in the two possible ways, give different paths
of the new network from `c` to `d`. -/
theorem numPaths_pairs_le_numPaths_addVertex (c d : V) :
    N.numPaths c d + N.numPathPairs c a b d + N.numPathPairs c b a d ≤
      (N.addVertex a b).numPaths (some c) (some d) := by
  obtain ⟨f₀, hf₀⟩ : ∃ f : {P : N.Word // N.IsPathWord c d P} →
      {W : (N.addVertex a b).Word // (N.addVertex a b).IsPathWord (some c) (some d) W},
      ∀ P, (f P).1 = (N.addVertexEmbed a b).push P.1 :=
    ⟨fun P => ⟨_, ((N.addVertexEmbed a b).isPathWord_push_iff c d P.1).2 P.2⟩, fun _ => rfl⟩
  obtain ⟨f₁, hf₁⟩ : ∃ f : {AB : N.Word × N.Word // N.IsPathPair c a b d AB.1 AB.2} →
      {W : (N.addVertex a b).Word // (N.addVertex a b).IsPathWord (some c) (some d) W},
      ∀ AB, (f AB).1 = (N.addVertexEmbed a b).push AB.1.1 + (N.addVertexEmbed a b).push AB.1.2 +
        (unitWord (Sum.inr false) + unitWord (Sum.inr true)) :=
    ⟨fun AB => ⟨_, N.isPathWord_addVertex_pair a b AB.2⟩, fun _ => rfl⟩
  obtain ⟨f₂, hf₂⟩ : ∃ f : {AB : N.Word × N.Word // N.IsPathPair c b a d AB.1 AB.2} →
      {W : (N.addVertex a b).Word // (N.addVertex a b).IsPathWord (some c) (some d) W},
      ∀ AB, (f AB).1 = (N.addVertexEmbed a b).push AB.1.1 + (N.addVertexEmbed a b).push AB.1.2 +
        (unitWord (Sum.inr false) + unitWord (Sum.inr true)) :=
    ⟨fun AB => ⟨_, N.isPathWord_addVertex_pair' a b AB.2⟩, fun _ => rfl⟩
  -- the values at the new edge at `a`
  have hval0 : ∀ P : N.Word, (N.addVertexEmbed a b).push P (Sum.inr false) = 0 :=
    fun P => N.addVertex_push_inr a b P false
  have hval1 : ∀ A B : N.Word, ((N.addVertexEmbed a b).push A + (N.addVertexEmbed a b).push B +
      (unitWord (Sum.inr false) + unitWord (Sum.inr true)) : E ⊕ Bool → Bit) (Sum.inr false) =
      1 := by
    intro A B
    rw [Pi.add_apply, Pi.add_apply, Pi.add_apply, N.addVertex_push_inr, N.addVertex_push_inr,
      unitWord_apply, unitWord_apply, if_pos rfl,
      if_neg (fun k : (Sum.inr true : E ⊕ Bool) = Sum.inr false =>
        Bool.noConfusion (Sum.inr.inj k)), zero_add, zero_add, add_zero]
  -- the sum of the two paths of a pair
  have hsum : ∀ A B A' B' : N.Word,
      (N.addVertexEmbed a b).push A + (N.addVertexEmbed a b).push B +
        (unitWord (Sum.inr false) + unitWord (Sum.inr true)) =
      (N.addVertexEmbed a b).push A' + (N.addVertexEmbed a b).push B' +
        (unitWord (Sum.inr false) + unitWord (Sum.inr true)) → A + B = A' + B' := by
    intro A B A' B' h
    have h1 := add_right_cancel h
    rw [← (N.addVertexEmbed a b).push_add, ← (N.addVertexEmbed a b).push_add] at h1
    exact (N.addVertexEmbed a b).push_injective h1
  have h01 : ∀ (P : {P : N.Word // N.IsPathWord c d P})
      (AB : {AB : N.Word × N.Word // N.IsPathPair c a b d AB.1 AB.2}), f₀ P ≠ f₁ AB := by
    intro P AB h
    have h1 : (f₀ P).1 (Sum.inr false) = (f₁ AB).1 (Sum.inr false) := by rw [h]
    rw [hf₀, hf₁, hval0, hval1] at h1
    exact one_ne_zero h1.symm
  have h02 : ∀ (P : {P : N.Word // N.IsPathWord c d P})
      (AB : {AB : N.Word × N.Word // N.IsPathPair c b a d AB.1 AB.2}), f₀ P ≠ f₂ AB := by
    intro P AB h
    have h1 : (f₀ P).1 (Sum.inr false) = (f₂ AB).1 (Sum.inr false) := by rw [h]
    rw [hf₀, hf₂, hval0, hval1] at h1
    exact one_ne_zero h1.symm
  have h12 : ∀ (AB : {AB : N.Word × N.Word // N.IsPathPair c a b d AB.1 AB.2})
      (AB' : {AB : N.Word × N.Word // N.IsPathPair c b a d AB.1 AB.2}), f₁ AB ≠ f₂ AB' := by
    intro AB AB' h
    have h1 : (f₁ AB).1 = (f₂ AB').1 := by rw [h]
    rw [hf₁, hf₂] at h1
    exact AB.2.false_of_add_eq AB'.2 (hsum _ _ _ _ h1) AB.2.2.1.deg_left_pos
  have hinj₀ : Function.Injective f₀ := by
    intro P Q h
    have h1 : (N.addVertexEmbed a b).push P.1 = (N.addVertexEmbed a b).push Q.1 := by
      rw [← hf₀ P, ← hf₀ Q, h]
    exact Subtype.ext ((N.addVertexEmbed a b).push_injective h1)
  have hinj₁ : Function.Injective f₁ := by
    intro AB AB' h
    have h1 : (f₁ AB).1 = (f₁ AB').1 := by rw [h]
    rw [hf₁, hf₁] at h1
    obtain ⟨k1, k2⟩ := AB.2.eq_of_add_eq AB'.2 (hsum _ _ _ _ h1)
    exact Subtype.ext (Prod.ext k1 k2)
  have hinj₂ : Function.Injective f₂ := by
    intro AB AB' h
    have h1 : (f₂ AB).1 = (f₂ AB').1 := by rw [h]
    rw [hf₂, hf₂] at h1
    obtain ⟨k1, k2⟩ := AB.2.eq_of_add_eq AB'.2 (hsum _ _ _ _ h1)
    exact Subtype.ext (Prod.ext k1 k2)
  -- the first two families together, then the third
  have hinj₀₁ : Function.Injective (Sum.elim f₀ f₁) := by
    rintro (x | x) (y | y) hxy
    · exact congrArg Sum.inl (hinj₀ hxy)
    · exact absurd hxy (h01 x y)
    · exact absurd hxy.symm (h01 y x)
    · exact congrArg Sum.inr (hinj₁ hxy)
  have hstep := natCard_add_le_of_injective (Sum.elim f₀ f₁) f₂ hinj₀₁ hinj₂ (by
    rintro (x | x) y
    · exact h02 x y
    · exact h12 x y)
  haveI : Finite {P : N.Word // N.IsPathWord c d P} := Subtype.finite
  haveI : Finite {AB : N.Word × N.Word // N.IsPathPair c a b d AB.1 AB.2} := Subtype.finite
  rw [Nat.card_sum] at hstep
  exact hstep

/-! ### The rank -/

/-- At most `2^b` words have a given boundary. -/
theorem natCard_boundary_eq_le (δ : N.Demand) :
    Nat.card {y : N.Word // N.boundary y = δ} ≤ 2 ^ networkRank N := by
  by_cases hne : Nonempty {y : N.Word // N.boundary y = δ}
  · obtain ⟨y₀⟩ := hne
    rw [← N.natCard_even]
    obtain ⟨f, hf⟩ : ∃ f : {y : N.Word // N.boundary y = δ} → {x : N.Word // N.boundary x = 0},
        ∀ y, (f y).1 = y.1 + y₀.1 :=
      ⟨fun y => ⟨y.1 + y₀.1, by rw [map_add, y.2, y₀.2]; exact word_add_self δ⟩, fun _ => rfl⟩
    apply Nat.card_le_card_of_injective f
    intro y y' h
    have h1 : y.1 + y₀.1 = y'.1 + y₀.1 := by rw [← hf y, ← hf y', h]
    exact Subtype.ext (add_right_cancel h1)
  · haveI : IsEmpty {y : N.Word // N.boundary y = δ} := not_nonempty_iff.1 hne
    rw [Nat.card_of_isEmpty]
    exact Nat.zero_le _

omit [Fintype V] in
/-- A word of the new network: its old part and its two new edges. -/
theorem addVertex_word_eq (x : E ⊕ Bool → Bit) :
    x = (N.addVertexEmbed a b).push ((N.addVertexEmbed a b).pull x) +
      (x (Sum.inr false) • unitWord (Sum.inr false) +
        x (Sum.inr true) • unitWord (Sum.inr true)) := by
  funext g
  rcases g with e | c
  · rw [Pi.add_apply, Pi.add_apply, N.addVertex_push_inl, Pi.smul_apply, Pi.smul_apply,
      unitWord_apply, unitWord_apply, if_neg (fun k => Sum.inr_ne_inl k),
      if_neg (fun k => Sum.inr_ne_inl k), smul_zero, smul_zero, add_zero, add_zero]
    rfl
  · cases c
    · rw [Pi.add_apply, Pi.add_apply, N.addVertex_push_inr, Pi.smul_apply, Pi.smul_apply,
        unitWord_apply, unitWord_apply, if_pos rfl,
        if_neg (fun k : (Sum.inr true : E ⊕ Bool) = Sum.inr false =>
          Bool.noConfusion (Sum.inr.inj k)), smul_zero, add_zero, zero_add, smul_eq_mul, mul_one]
    · rw [Pi.add_apply, Pi.add_apply, N.addVertex_push_inr, Pi.smul_apply, Pi.smul_apply,
        unitWord_apply, unitWord_apply, if_pos rfl,
        if_neg (fun k : (Sum.inr false : E ⊕ Bool) = Sum.inr true =>
          Bool.noConfusion (Sum.inr.inj k)), smul_zero, zero_add, zero_add, smul_eq_mul, mul_one]

/-- **The rank grows by at most one.** -/
theorem networkRank_addVertex_le : networkRank (N.addVertex a b) ≤ networkRank N + 1 := by
  have hba : (N.addVertex a b).boundary (unitWord (Sum.inr false)) =
      unitWord (some a) + unitWord none :=
    (N.addVertex a b).boundary_unitWord_of_joins (N.addVertex_joins_left a b)
  have hbb : (N.addVertex a b).boundary (unitWord (Sum.inr true)) =
      unitWord (some b) + unitWord none :=
    (N.addVertex a b).boundary_unitWord_of_joins (N.addVertex_joins_right a b)
  -- an even word takes both new edges or none
  have hboth : ∀ x : E ⊕ Bool → Bit, (N.addVertex a b).boundary x = 0 →
      x (Sum.inr true) = x (Sum.inr false) := by
    intro x hx
    have h1 : (N.addVertex a b).boundary x none = x (Sum.inr false) + x (Sum.inr true) := by
      conv_lhs => rw [N.addVertex_word_eq a b x]
      rw [map_add, map_add, map_smul, map_smul, hba, hbb, Pi.add_apply,
        (N.addVertexEmbed a b).boundary_push_of_not_range _ (N.addVertex_not_range a b)]
      simp [unitWord_apply]
    rw [hx] at h1
    exact (bit_eq_of_add_eq_zero h1.symm).symm
  -- without the new edges
  have hzero : ∀ x : E ⊕ Bool → Bit, (N.addVertex a b).boundary x = 0 →
      x (Sum.inr false) = 0 → N.boundary ((N.addVertexEmbed a b).pull x) = 0 := by
    intro x hx h0
    have h0' : x (Sum.inr true) = 0 := by rw [hboth x hx, h0]
    have hdec := N.addVertex_word_eq a b x
    rw [h0, h0', zero_smul, zero_smul, add_zero, add_zero] at hdec
    rw [← (N.addVertexEmbed a b).boundary_push_eq_zero_iff, ← hdec]
    exact hx
  -- with the new edges
  have hone : ∀ x : E ⊕ Bool → Bit, (N.addVertex a b).boundary x = 0 →
      x (Sum.inr false) ≠ 0 →
      N.boundary ((N.addVertexEmbed a b).pull x) = N.pathDemand a b := by
    intro x hx h1
    have h1a : x (Sum.inr false) = 1 := bit_eq_one_of_ne_zero h1
    have h1b : x (Sum.inr true) = 1 := by rw [hboth x hx, h1a]
    have hdec := N.addVertex_word_eq a b x
    rw [h1a, h1b, one_smul, one_smul] at hdec
    have hsum : (N.addVertex a b).boundary
        ((N.addVertexEmbed a b).push ((N.addVertexEmbed a b).pull x)) +
        ((N.addVertex a b).boundary (unitWord (Sum.inr false)) +
          (N.addVertex a b).boundary (unitWord (Sum.inr true))) = 0 := by
      rw [← map_add, ← map_add, ← hdec]
      exact hx
    have hpd : (N.addVertex a b).boundary
        ((N.addVertexEmbed a b).push ((N.addVertexEmbed a b).pull x)) =
        (N.addVertex a b).pathDemand ((N.addVertexEmbed a b).φ a)
          ((N.addVertexEmbed a b).φ b) := by
      rw [word_eq_of_add_eq_zero hsum, hba, hbb]
      show (unitWord (some a) + unitWord none : Option V → Bit) +
        (unitWord (some b) + unitWord none) = unitWord (some a) + unitWord (some b)
      calc (unitWord (some a) + unitWord none : Option V → Bit) +
            (unitWord (some b) + unitWord none)
          = unitWord (some a) + unitWord (some b) + (unitWord none + unitWord none) := by abel
        _ = unitWord (some a) + unitWord (some b) := by
            rw [word_add_self (unitWord (none : Option V)), add_zero]
    exact ((N.addVertexEmbed a b).boundary_push_eq_pathDemand_iff _ a b).1 hpd
  -- an injective map from the even words of the new network
  obtain ⟨f, hf0, hf1⟩ : ∃ f : {x : E ⊕ Bool → Bit // (N.addVertex a b).boundary x = 0} →
      {y : N.Word // N.boundary y = 0} ⊕ {y : N.Word // N.boundary y = N.pathDemand a b},
      (∀ x, x.1 (Sum.inr false) = 0 →
        ∃ w, f x = Sum.inl w ∧ w.1 = (N.addVertexEmbed a b).pull x.1) ∧
      (∀ x, x.1 (Sum.inr false) ≠ 0 →
        ∃ w, f x = Sum.inr w ∧ w.1 = (N.addVertexEmbed a b).pull x.1) := by
    refine ⟨fun x => if h : x.1 (Sum.inr false) = 0 then
      Sum.inl ⟨(N.addVertexEmbed a b).pull x.1, hzero x.1 x.2 h⟩ else
      Sum.inr ⟨(N.addVertexEmbed a b).pull x.1, hone x.1 x.2 h⟩, ?_, ?_⟩
    · intro x h
      exact ⟨_, dif_pos h, rfl⟩
    · intro x h
      exact ⟨_, dif_neg h, rfl⟩
  have hinj : Function.Injective f := by
    intro x y hxy
    have ex := N.addVertex_word_eq a b x.1
    have ey := N.addVertex_word_eq a b y.1
    by_cases hx : x.1 (Sum.inr false) = 0
    · obtain ⟨w, hw, hwv⟩ := hf0 x hx
      by_cases hy : y.1 (Sum.inr false) = 0
      · obtain ⟨w', hw', hwv'⟩ := hf0 y hy
        have hww : w = w' := Sum.inl.inj (by rw [← hw, ← hw', hxy])
        have hpull : (N.addVertexEmbed a b).pull x.1 = (N.addVertexEmbed a b).pull y.1 := by
          rw [← hwv, ← hwv', hww]
        apply Subtype.ext
        rw [ex, ey, hpull, hboth x.1 x.2, hboth y.1 y.2, hx, hy]
      · obtain ⟨w', hw', _⟩ := hf1 y hy
        rw [hw, hw'] at hxy
        exact absurd hxy Sum.inl_ne_inr
    · obtain ⟨w, hw, hwv⟩ := hf1 x hx
      by_cases hy : y.1 (Sum.inr false) = 0
      · obtain ⟨w', hw', _⟩ := hf0 y hy
        rw [hw, hw'] at hxy
        exact absurd hxy Sum.inr_ne_inl
      · obtain ⟨w', hw', hwv'⟩ := hf1 y hy
        have hww : w = w' := Sum.inr.inj (by rw [← hw, ← hw', hxy])
        have hpull : (N.addVertexEmbed a b).pull x.1 = (N.addVertexEmbed a b).pull y.1 := by
          rw [← hwv, ← hwv', hww]
        apply Subtype.ext
        rw [ex, ey, hpull, hboth x.1 x.2, hboth y.1 y.2, bit_eq_one_of_ne_zero hx,
          bit_eq_one_of_ne_zero hy]
  have hcard := Nat.card_le_card_of_injective f hinj
  rw [Nat.card_sum, (N.addVertex a b).natCard_even, N.natCard_even] at hcard
  have h2 := N.natCard_boundary_eq_le (N.pathDemand a b)
  have h3 : 2 ^ networkRank (N.addVertex a b) ≤ 2 ^ (networkRank N + 1) := by
    rw [pow_succ]
    omega
  exact (Nat.pow_le_pow_iff_right (by norm_num)).1 h3

/-! ### Degrees and poles -/

omit [Fintype V] in
/-- The degree of the new vertex is two. -/
theorem deg_addVertex_none : (N.addVertex a b).deg (fun _ => 1) none = 2 := by
  have hones : (fun _ : E ⊕ Bool => (1 : Bit)) =
      (N.addVertexEmbed a b).push (fun _ => 1) +
        (unitWord (Sum.inr false) + unitWord (Sum.inr true)) := by
    have h := N.addVertex_word_eq a b (fun _ => 1)
    rw [one_smul, one_smul] at h
    exact h
  have hd1 : ∀ g, (N.addVertexEmbed a b).push (fun _ => (1 : Bit)) g ≠ 0 →
      (unitWord (Sum.inr false) + unitWord (Sum.inr true) : E ⊕ Bool → Bit) g = 0 := by
    intro g hg
    rcases g with e | c
    · rw [Pi.add_apply, unitWord_apply, unitWord_apply, if_neg (fun k => Sum.inr_ne_inl k),
        if_neg (fun k => Sum.inr_ne_inl k), add_zero]
    · exact absurd (N.addVertex_push_inr a b _ c) hg
  have hd2 : ∀ g, (unitWord (Sum.inr false) : E ⊕ Bool → Bit) g ≠ 0 →
      (unitWord (Sum.inr true) : E ⊕ Bool → Bit) g = 0 := by
    intro g hg
    rw [unitWord_apply] at hg ⊢
    by_cases k : (Sum.inr false : E ⊕ Bool) = g
    · rw [if_neg (fun k' : (Sum.inr true : E ⊕ Bool) = g =>
        Bool.noConfusion (Sum.inr.inj (k'.trans k.symm)))]
    · rw [if_neg k] at hg
      exact absurd rfl hg
  rw [hones, (N.addVertex a b).deg_add_of_disjoint hd1 none,
    (N.addVertex a b).deg_add_of_disjoint hd2 none,
    (N.addVertexEmbed a b).deg_push_of_not_range _ (N.addVertex_not_range a b),
    (N.addVertex a b).deg_unitWord_eq_one (N.addVertex_joins_left a b).at_right,
    (N.addVertex a b).deg_unitWord_eq_one (N.addVertex_joins_right a b).at_right]

omit [Fintype V] in
/-- The degree of an old vertex: one more for `a` and one more for `b`. -/
theorem deg_addVertex_some (v : V) :
    (N.addVertex a b).deg (fun _ => 1) (some v) =
      N.deg (fun _ => 1) v + ((if v = a then 1 else 0) + (if v = b then 1 else 0)) := by
  have hones : (fun _ : E ⊕ Bool => (1 : Bit)) =
      (N.addVertexEmbed a b).push (fun _ => 1) +
        (unitWord (Sum.inr false) + unitWord (Sum.inr true)) := by
    have h := N.addVertex_word_eq a b (fun _ => 1)
    rw [one_smul, one_smul] at h
    exact h
  have hd1 : ∀ g, (N.addVertexEmbed a b).push (fun _ => (1 : Bit)) g ≠ 0 →
      (unitWord (Sum.inr false) + unitWord (Sum.inr true) : E ⊕ Bool → Bit) g = 0 := by
    intro g hg
    rcases g with e | c
    · rw [Pi.add_apply, unitWord_apply, unitWord_apply, if_neg (fun k => Sum.inr_ne_inl k),
        if_neg (fun k => Sum.inr_ne_inl k), add_zero]
    · exact absurd (N.addVertex_push_inr a b _ c) hg
  have hd2 : ∀ g, (unitWord (Sum.inr false) : E ⊕ Bool → Bit) g ≠ 0 →
      (unitWord (Sum.inr true) : E ⊕ Bool → Bit) g = 0 := by
    intro g hg
    rw [unitWord_apply] at hg ⊢
    by_cases k : (Sum.inr false : E ⊕ Bool) = g
    · rw [if_neg (fun k' : (Sum.inr true : E ⊕ Bool) = g =>
        Bool.noConfusion (Sum.inr.inj (k'.trans k.symm)))]
    · rw [if_neg k] at hg
      exact absurd rfl hg
  have hleft : (N.addVertex a b).deg (unitWord (Sum.inr false)) (some v) =
      if v = a then 1 else 0 := by
    by_cases hv : v = a
    · rw [if_pos hv, hv]
      exact (N.addVertex a b).deg_unitWord_eq_one (N.addVertex_joins_left a b).at_left
    · rw [if_neg hv]
      exact (N.addVertex a b).deg_unitWord_of_joins (N.addVertex_joins_left a b)
        (fun k => hv (Option.some.inj k)) (fun k => Option.noConfusion k)
  have hright : (N.addVertex a b).deg (unitWord (Sum.inr true)) (some v) =
      if v = b then 1 else 0 := by
    by_cases hv : v = b
    · rw [if_pos hv, hv]
      exact (N.addVertex a b).deg_unitWord_eq_one (N.addVertex_joins_right a b).at_left
    · rw [if_neg hv]
      exact (N.addVertex a b).deg_unitWord_of_joins (N.addVertex_joins_right a b)
        (fun k => hv (Option.some.inj k)) (fun k => Option.noConfusion k)
  have hpush : (N.addVertex a b).deg ((N.addVertexEmbed a b).push (fun _ => 1)) (some v) =
      N.deg (fun _ => 1) v := (N.addVertexEmbed a b).deg_push _ v
  rw [hones, (N.addVertex a b).deg_add_of_disjoint hd1 (some v),
    (N.addVertex a b).deg_add_of_disjoint hd2 (some v), hpush, hleft, hright]

omit [Fintype V] in
/-- The new vertex is a port. -/
theorem isPort_addVertex_none : (N.addVertex a b).IsPort none := N.deg_addVertex_none a b

omit [Fintype V] in
/-- A port of `N` other than `a` and `b` is a port of the new network. -/
theorem isPort_addVertex_some {c : V} (hca : c ≠ a) (hcb : c ≠ b) (hc : N.IsPort c) :
    (N.addVertex a b).IsPort (some c) := by
  unfold IsPort
  rw [N.deg_addVertex_some a b c, if_neg hca, if_neg hcb]
  exact hc

omit [Fintype V] in
/-- **The new network is a pole**, if `N` is a pole and `a`, `b` are two of its ports. -/
theorem isWeakPole_addVertex (hN : N.IsWeakPole) (hab : a ≠ b) (ha : N.IsPort a)
    (hb : N.IsPort b) : (N.addVertex a b).IsWeakPole := by
  have ha2 : N.deg (fun _ => 1) a = 2 := ha
  have hb2 : N.deg (fun _ => 1) b = 2 := hb
  -- every vertex of positive degree is joined to `a`
  have hreach : ∀ w : Option V, 0 < (N.addVertex a b).deg (fun _ => 1) w →
      (N.addVertex a b).graph.Reachable (some a) w := by
    intro w hw
    rcases w with _ | v
    · have hadj : (N.addVertex a b).graph.Adj (some a) none :=
        ⟨Sum.inr false, N.addVertex_joins_left a b⟩
      exact hadj.reachable
    · have hv : 0 < N.deg (fun _ => 1) v := by
        rw [N.deg_addVertex_some a b v] at hw
        by_cases hva : v = a
        · rw [hva, ha2]
          norm_num
        · by_cases hvb : v = b
          · rw [hvb, hb2]
            norm_num
          · rw [if_neg hva, if_neg hvb] at hw
            omega
      exact (N.addVertexEmbed a b).reachable_push (hN.2 a v (by omega) hv)
  constructor
  · intro w
    rcases w with _ | v
    · exact Or.inr (Or.inl (N.deg_addVertex_none a b))
    · rw [N.deg_addVertex_some a b v]
      by_cases hva : v = a
      · have hvb : v ≠ b := fun k => hab (hva.symm.trans k)
        rw [if_pos hva, if_neg hvb, hva, ha2]
        exact Or.inr (Or.inr rfl)
      · by_cases hvb : v = b
        · rw [if_neg hva, if_pos hvb, hvb, hb2]
          exact Or.inr (Or.inr rfl)
        · rw [if_neg hva, if_neg hvb, add_zero, add_zero]
          exact hN.1 v
  · intro u w hu hw
    exact (hreach u hu).symm.trans (hreach w hw)

end Main

end Erdos1016.BoundaryTrace.Network
