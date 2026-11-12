import Erdos1016.ExactMaximum.NetTransfer
import Erdos1016.ExactMaximum.NetCut

set_option autoImplicit false

/-!
# A network inside another network

An embedding of a network `N` into a network `N'` is an injective map of the vertices and an
injective map of the edges that respect the ends. A word of `N` gives a word of `N'` that is
zero outside the image. This file proves that the embedding keeps boundaries, cycles and paths:

* `Embed.isCycleWord_push_iff`, `Embed.isPathWord_push_iff`;
* `Embed.numCycles_eq`, `Embed.numPaths_eq`: the cycles (paths) of `N` are the cycles (paths) of
  `N'` within the image of the edges;
* `Embed.networkRank_eq_sub`: the rank of `N` is the rank of the part of `N'` on the image.

The main example is the network `N.induce S` that a set `S` of vertices induces. Its vertices are
the vertices of `S`, and its edges are the edges inside `S`. It has the cycles, the paths and
the rank of the first side `N.sub (N.inside S)` of the cut (`numCycles_induce`, `numPaths_induce`,
`networkRank_induce`), and it is connected if the side is (`connected_induce`).
-/

noncomputable section
open scoped BigOperators

namespace Erdos1016.BoundaryTrace.Network

open BoundaryDecay

local instance netEmbedDecidable (p : Prop) : Decidable p := Classical.propDecidable p

universe u₁ u₂ u₃ u₄

variable {V : Type u₁} {E : Type u₂} {V' : Type u₃} {E' : Type u₄}

/-- An embedding of a network into another network. -/
structure Embed (N : Network V E) (N' : Network V' E') where
  /-- The map of the vertices. -/
  φ : V → V'
  /-- The map of the edges. -/
  ψ : E → E'
  φ_inj : Function.Injective φ
  ψ_inj : Function.Injective ψ
  src : ∀ e, N'.src (ψ e) = φ (N.src e)
  dst : ∀ e, N'.dst (ψ e) = φ (N.dst e)

namespace Embed

variable {N : Network V E} {N' : Network V' E'} (R : Embed N N')

/-- The image of the edges. -/
def image (e' : E') : Prop := ∃ e, R.ψ e = e'

/-- The word of the larger network: zero outside the image. -/
def push (x : E → Bit) : E' → Bit := Function.extend R.ψ x (0 : E' → Bit)

theorem push_apply (x : E → Bit) (e : E) : R.push x (R.ψ e) = x e :=
  R.ψ_inj.extend_apply x 0 e

theorem push_apply_of_not_image (x : E → Bit) {e' : E'} (h : ¬ R.image e') :
    R.push x e' = 0 :=
  Function.extend_apply' x (0 : E' → Bit) e' h

theorem within_push (x : E → Bit) : Within (R.push x) R.image :=
  fun _ he' => Classical.not_not.1 fun h => he' (R.push_apply_of_not_image x h)

/-- The word of the smaller network. -/
def pull (y : E' → Bit) : E → Bit := fun e => y (R.ψ e)

theorem pull_push (x : E → Bit) : R.pull (R.push x) = x :=
  funext fun e => R.push_apply x e

theorem push_pull {y : E' → Bit} (h : Within y R.image) : R.push (R.pull y) = y := by
  funext e'
  by_cases he : R.image e'
  · obtain ⟨e, rfl⟩ := he
    exact R.push_apply _ e
  · rw [R.push_apply_of_not_image _ he]
    exact (h.eq_zero he).symm

theorem push_injective : Function.Injective R.push := by
  intro x y h
  rw [← R.pull_push x, ← R.pull_push y, h]

theorem push_zero : R.push (0 : E → Bit) = 0 := by
  funext e'
  by_cases he : R.image e'
  · obtain ⟨e, rfl⟩ := he
    rw [R.push_apply]
    rfl
  · rw [R.push_apply_of_not_image _ he]
    rfl

theorem isSubword_push {x y : E → Bit} (h : N.IsSubword y x) :
    N'.IsSubword (R.push y) (R.push x) := by
  intro e' he'
  obtain ⟨e, rfl⟩ := R.within_push y e' he'
  rw [R.push_apply] at he' ⊢
  exact h e he'

theorem isSubword_pull {x : E → Bit} {y' : E' → Bit} (h : N'.IsSubword y' (R.push x)) :
    N.IsSubword (R.pull y') x := by
  intro e he
  have h1 := h (R.ψ e) he
  rw [R.push_apply] at h1
  exact h1

theorem within_of_isSubword_push {x : E → Bit} {y' : E' → Bit}
    (h : N'.IsSubword y' (R.push x)) : Within y' R.image :=
  fun e' he' => R.within_push x e' (h e' he')

variable [Fintype V] [Fintype E] [Fintype V'] [Fintype E']

/-- The boundary at a vertex of the image. -/
theorem boundary_push (x : E → Bit) (v : V) :
    N'.boundary (R.push x) (R.φ v) = N.boundary x v := by
  rw [boundary_apply, boundary_apply]
  have h1 : (∑ e, if N.src e = v then x e else 0) =
      ∑ e', if N'.src e' = R.φ v then R.push x e' else 0 := by
    apply Fintype.sum_of_injective R.ψ R.ψ_inj
    · intro e' he'
      rw [R.push_apply_of_not_image x he']
      exact ite_self 0
    · intro e
      rw [R.src, R.push_apply]
      by_cases h : N.src e = v
      · rw [if_pos h, if_pos (by rw [h])]
      · rw [if_neg h, if_neg (fun h' => h (R.φ_inj h'))]
  have h2 : (∑ e, if N.dst e = v then x e else 0) =
      ∑ e', if N'.dst e' = R.φ v then R.push x e' else 0 := by
    apply Fintype.sum_of_injective R.ψ R.ψ_inj
    · intro e' he'
      rw [R.push_apply_of_not_image x he']
      exact ite_self 0
    · intro e
      rw [R.dst, R.push_apply]
      by_cases h : N.dst e = v
      · rw [if_pos h, if_pos (by rw [h])]
      · rw [if_neg h, if_neg (fun h' => h (R.φ_inj h'))]
  rw [h1, h2]

omit [Fintype V] [Fintype E] in
/-- The boundary at a vertex outside the image. -/
theorem boundary_push_of_not_range (x : E → Bit) {v' : V'} (h : ¬ ∃ v, R.φ v = v') :
    N'.boundary (R.push x) v' = 0 := by
  rw [boundary_apply]
  have h1 : ∀ e', (if N'.src e' = v' then R.push x e' else 0) = 0 := by
    intro e'
    by_cases he : R.image e'
    · obtain ⟨e, rfl⟩ := he
      rw [if_neg]
      intro hs
      exact h ⟨N.src e, by rw [← R.src]; exact hs⟩
    · rw [R.push_apply_of_not_image x he]
      exact ite_self 0
  have h2 : ∀ e', (if N'.dst e' = v' then R.push x e' else 0) = 0 := by
    intro e'
    by_cases he : R.image e'
    · obtain ⟨e, rfl⟩ := he
      rw [if_neg]
      intro hs
      exact h ⟨N.dst e, by rw [← R.dst]; exact hs⟩
    · rw [R.push_apply_of_not_image x he]
      exact ite_self 0
  simp only [h1, h2, Finset.sum_const_zero, add_zero]

/-- A word is even in the smaller network if and only if it is even in the larger one. -/
theorem boundary_push_eq_zero_iff (x : E → Bit) :
    N'.boundary (R.push x) = 0 ↔ N.boundary x = 0 := by
  constructor
  · intro h
    funext v
    rw [← R.boundary_push x v, h]
    rfl
  · intro h
    funext v'
    by_cases hv : ∃ v, R.φ v = v'
    · obtain ⟨v, rfl⟩ := hv
      rw [R.boundary_push x v, h]
      rfl
    · rw [R.boundary_push_of_not_range x hv]
      rfl

/-- The demand of a path. -/
theorem boundary_push_eq_pathDemand_iff (x : E → Bit) (s t : V) :
    N'.boundary (R.push x) = N'.pathDemand (R.φ s) (R.φ t) ↔
      N.boundary x = N.pathDemand s t := by
  have hdem : ∀ v, N'.pathDemand (R.φ s) (R.φ t) (R.φ v) = N.pathDemand s t v := by
    intro v
    show unitWord (R.φ s) (R.φ v) + unitWord (R.φ t) (R.φ v) = unitWord s v + unitWord t v
    rw [unitWord_apply, unitWord_apply, unitWord_apply, unitWord_apply]
    simp only [R.φ_inj.eq_iff]
  constructor
  · intro h
    funext v
    rw [← R.boundary_push x v, h, hdem]
  · intro h
    funext v'
    by_cases hv : ∃ v, R.φ v = v'
    · obtain ⟨v, rfl⟩ := hv
      rw [R.boundary_push x v, h, hdem]
    · rw [R.boundary_push_of_not_range x hv]
      have h1 : v' ≠ R.φ s := fun h' => hv ⟨s, h'.symm⟩
      have h2 : v' ≠ R.φ t := fun h' => hv ⟨t, h'.symm⟩
      show (0 : Bit) = unitWord (R.φ s) v' + unitWord (R.φ t) v'
      rw [unitWord_apply, unitWord_apply, if_neg (Ne.symm h1), if_neg (Ne.symm h2), add_zero]

/-- **Cycles agree.** -/
theorem isCycleWord_push_iff (x : E → Bit) : N'.IsCycleWord (R.push x) ↔ N.IsCycleWord x := by
  rw [N'.isCycleWord_iff_minimal, N.isCycleWord_iff_minimal]
  constructor
  · rintro ⟨h1, h2, h3⟩
    refine ⟨fun h => h1 (by rw [h, R.push_zero]), (R.boundary_push_eq_zero_iff x).1 h2,
      fun y hy hy0 => ?_⟩
    rcases h3 (R.push y) (R.isSubword_push hy) ((R.boundary_push_eq_zero_iff y).2 hy0)
      with h | h
    · left
      apply R.push_injective
      rw [h, R.push_zero]
    · right
      exact R.push_injective h
  · rintro ⟨h1, h2, h3⟩
    refine ⟨fun h => h1 (R.push_injective (by rw [h, R.push_zero])),
      (R.boundary_push_eq_zero_iff x).2 h2, fun y' hy' hy0' => ?_⟩
    have hyeq := R.push_pull (R.within_of_isSubword_push hy')
    have hy0 : N.boundary (R.pull y') = 0 := by
      rw [← R.boundary_push_eq_zero_iff, hyeq]
      exact hy0'
    rcases h3 (R.pull y') (R.isSubword_pull hy') hy0 with h | h
    · left
      rw [← hyeq, h, R.push_zero]
    · right
      rw [← hyeq, h]

/-- **Paths agree.** -/
theorem isPathWord_push_iff (s t : V) (x : E → Bit) :
    N'.IsPathWord (R.φ s) (R.φ t) (R.push x) ↔ N.IsPathWord s t x := by
  rw [N'.isPathWord_iff_minimal, N.isPathWord_iff_minimal]
  constructor
  · rintro ⟨h1, h2, h3⟩
    refine ⟨fun h => h1 (by rw [h]), (R.boundary_push_eq_pathDemand_iff x s t).1 h2,
      fun y hy hy0 => ?_⟩
    apply R.push_injective
    rw [h3 (R.push y) (R.isSubword_push hy) ((R.boundary_push_eq_zero_iff y).2 hy0),
      R.push_zero]
  · rintro ⟨h1, h2, h3⟩
    refine ⟨fun h => h1 (R.φ_inj h), (R.boundary_push_eq_pathDemand_iff x s t).2 h2,
      fun y' hy' hy0' => ?_⟩
    have hyeq := R.push_pull (R.within_of_isSubword_push hy')
    have hy0 : N.boundary (R.pull y') = 0 := by
      rw [← R.boundary_push_eq_zero_iff, hyeq]
      exact hy0'
    rw [← hyeq, h3 (R.pull y') (R.isSubword_pull hy') hy0, R.push_zero]

/-- **The cycles of the smaller network.** -/
theorem numCycles_eq :
    N.numCycles = Nat.card {y : N'.Word // N'.IsCycleWord y ∧ Within y R.image} := by
  let f : {x : N.Word // N.IsCycleWord x} →
      {y : N'.Word // N'.IsCycleWord y ∧ Within y R.image} := fun x =>
    ⟨R.push x.1, (R.isCycleWord_push_iff x.1).2 x.2, R.within_push x.1⟩
  have hf : Function.Bijective f := by
    constructor
    · intro a b hab
      have h' : (f a).1 = (f b).1 := congrArg Subtype.val hab
      exact Subtype.ext (R.push_injective h')
    · rintro ⟨y, hy, hw⟩
      refine ⟨⟨R.pull y, ?_⟩, ?_⟩
      · rw [← R.isCycleWord_push_iff, R.push_pull hw]
        exact hy
      · exact Subtype.ext (R.push_pull hw)
  exact Nat.card_eq_of_bijective f hf

/-- **The paths of the smaller network.** -/
theorem numPaths_eq (s t : V) :
    N.numPaths s t =
      Nat.card {y : N'.Word // N'.IsPathWord (R.φ s) (R.φ t) y ∧ Within y R.image} := by
  let f : {x : N.Word // N.IsPathWord s t x} →
      {y : N'.Word // N'.IsPathWord (R.φ s) (R.φ t) y ∧ Within y R.image} := fun x =>
    ⟨R.push x.1, (R.isPathWord_push_iff s t x.1).2 x.2, R.within_push x.1⟩
  have hf : Function.Bijective f := by
    constructor
    · intro a b hab
      have h' : (f a).1 = (f b).1 := congrArg Subtype.val hab
      exact Subtype.ext (R.push_injective h')
    · rintro ⟨y, hy, hw⟩
      refine ⟨⟨R.pull y, ?_⟩, ?_⟩
      · rw [← R.isPathWord_push_iff, R.push_pull hw]
        exact hy
      · exact Subtype.ext (R.push_pull hw)
  exact Nat.card_eq_of_bijective f hf

/-- **The rank of the smaller network** is the rank of the part of the larger network on the
image of the edges. -/
theorem networkRank_eq_sub [Fintype {e' : E' // R.image e'}] :
    networkRank N = networkRank (N'.sub R.image) := by
  have hext : ∀ x : E → Bit, Network.extend R.image (Network.pull R.image (R.push x)) =
      R.push x := fun x => extend_pull R.image (R.within_push x)
  let f : N.CycleSpace → (N'.sub R.image).CycleSpace := fun x =>
    ⟨Network.pull R.image (R.push x.1), by
      rw [LinearMap.mem_ker, ← boundary_extend, hext]
      exact (R.boundary_push_eq_zero_iff x.1).2 (LinearMap.mem_ker.1 x.2)⟩
  have hf : Function.Bijective f := by
    constructor
    · intro a b hab
      have h' : (f a).1 = (f b).1 := congrArg Subtype.val hab
      have h'' : Network.pull R.image (R.push a.1) = Network.pull R.image (R.push b.1) := h'
      have h3 : R.push a.1 = R.push b.1 := by
        rw [← hext a.1, ← hext b.1, h'']
      exact Subtype.ext (R.push_injective h3)
    · rintro ⟨y, hy⟩
      have hw : Within (Network.extend R.image y) R.image := within_extend R.image y
      refine ⟨⟨R.pull (Network.extend R.image y), ?_⟩, ?_⟩
      · rw [LinearMap.mem_ker, ← R.boundary_push_eq_zero_iff, R.push_pull hw, boundary_extend]
        exact LinearMap.mem_ker.1 hy
      · apply Subtype.ext
        show Network.pull R.image (R.push (R.pull (Network.extend R.image y))) = y
        rw [R.push_pull hw, pull_extend]
  have hcard := Fintype.card_of_bijective hf
  rw [cycleSpace_card_network, cycleSpace_card_network] at hcard
  exact Nat.pow_right_injective (le_refl 2) hcard

end Embed

/-! ### The network induced on a set of vertices -/

/-- The network induced on the vertices of `S`: its edges are the edges with both ends in
`S`. -/
def induce (N : Network V E) (S : V → Prop) : Network {v : V // S v} {e : E // N.inside S e} where
  src e := ⟨N.src e.1, e.2.1⟩
  dst e := ⟨N.dst e.1, e.2.2⟩
  noLoops e h := N.noLoops e.1 (congrArg Subtype.val h)

/-- The induced network inside the network. -/
def induceEmbed (N : Network V E) (S : V → Prop) : Embed (N.induce S) N where
  φ := Subtype.val
  ψ := Subtype.val
  φ_inj := Subtype.val_injective
  ψ_inj := Subtype.val_injective
  src _ := rfl
  dst _ := rfl

theorem induceEmbed_image (N : Network V E) (S : V → Prop) (e : E) :
    (N.induceEmbed S).image e ↔ N.inside S e :=
  ⟨fun ⟨e', h⟩ => h ▸ e'.2, fun h => ⟨⟨e, h⟩, rfl⟩⟩

section Induce

variable [Fintype V] [Fintype E]

/-- **The cycles of the induced network** are the cycles of the first side of the cut. -/
theorem numCycles_induce (N : Network V E) (S : V → Prop) :
    (N.induce S).numCycles = (N.sub (N.inside S)).numCycles := by
  rw [(N.induceEmbed S).numCycles_eq, numCycles_sub]
  exact Nat.card_congr (Equiv.subtypeEquivRight fun y =>
    and_congr Iff.rfl ⟨fun h e he => (N.induceEmbed_image S e).1 (h e he),
      fun h e he => (N.induceEmbed_image S e).2 (h e he)⟩)

/-- **The paths of the induced network** are the paths of the first side of the cut. -/
theorem numPaths_induce (N : Network V E) (S : V → Prop) (s t : {v : V // S v}) :
    (N.induce S).numPaths s t = (N.sub (N.inside S)).numPaths s.1 t.1 := by
  rw [(N.induceEmbed S).numPaths_eq, numPaths_sub]
  exact Nat.card_congr (Equiv.subtypeEquivRight fun y =>
    and_congr Iff.rfl ⟨fun h e he => (N.induceEmbed_image S e).1 (h e he),
      fun h e he => (N.induceEmbed_image S e).2 (h e he)⟩)

omit [Fintype V] [Fintype E] in
/-- The rank of a part depends on the set of edges only. -/
theorem networkRank_sub_congr (N : Network V E) {p q : E → Prop} [i₁ : Fintype {e : E // p e}]
    [i₂ : Fintype {e : E // q e}] (h : p = q) :
    networkRank (N.sub p) = networkRank (N.sub q) := by
  subst h
  have hi : i₁ = i₂ := Subsingleton.elim _ _
  subst hi
  rfl

/-- **The rank of the induced network** is the rank of the first side of the cut. -/
theorem networkRank_induce (N : Network V E) (S : V → Prop) :
    networkRank (N.induce S) = networkRank (N.sub (N.inside S)) := by
  -- both are the rank of the part of `N` on the image, for two descriptions of the image
  have h1 := (N.induceEmbed S).networkRank_eq_sub
  have hp : (N.induceEmbed S).image = N.inside S :=
    funext fun e => propext (N.induceEmbed_image S e)
  rw [h1]
  exact N.networkRank_sub_congr hp

end Induce

/-- A walk in the first side that starts in `S` stays in `S`, and it is a walk of the induced
network. -/
theorem induce_reachable (N : Network V E) (S : V → Prop) :
    ∀ (a b : V), (N.sub (N.inside S)).graph.Walk a b → ∀ ha : S a,
      ∃ hb : S b, (N.induce S).graph.Reachable ⟨a, ha⟩ ⟨b, hb⟩ := by
  intro a b p
  induction p with
  | nil => exact fun ha => ⟨ha, SimpleGraph.Reachable.refl _⟩
  | @cons a c b hadj _ ih =>
    intro ha
    obtain ⟨e, he⟩ := hadj
    have hc : S c := by
      rcases he with ⟨_, h2⟩ | ⟨h1, _⟩
      · exact h2 ▸ e.2.2
      · exact h1 ▸ e.2.1
    obtain ⟨hb, hr⟩ := ih hc
    refine ⟨hb, SimpleGraph.Reachable.trans ?_ hr⟩
    have hadj' : (N.induce S).graph.Adj ⟨a, ha⟩ ⟨c, hc⟩ := by
      refine ⟨e, ?_⟩
      rcases he with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · exact Or.inl ⟨Subtype.ext h1, Subtype.ext h2⟩
      · exact Or.inr ⟨Subtype.ext h1, Subtype.ext h2⟩
    exact hadj'.reachable

/-- **The induced network is connected** if every vertex of `S` is joined to `s₀ ∈ S` by edges
inside `S`. -/
theorem connected_induce (N : Network V E) (S : V → Prop) {s₀ : V} (hs₀ : S s₀)
    (hin : ∀ u, S u → (N.sub (N.inside S)).graph.Reachable s₀ u) :
    (N.induce S).graph.Connected := by
  have hroot : ∀ u : {v : V // S v}, (N.induce S).graph.Reachable ⟨s₀, hs₀⟩ u := by
    intro u
    obtain ⟨p⟩ := hin u.1 u.2
    obtain ⟨_, hr⟩ := N.induce_reachable S s₀ u.1 p hs₀
    exact hr
  haveI : Nonempty {v : V // S v} := ⟨⟨s₀, hs₀⟩⟩
  exact ⟨fun u w => (hroot u).symm.trans (hroot w)⟩

end Erdos1016.BoundaryTrace.Network
