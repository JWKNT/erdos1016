import Mathlib.Combinatorics.SimpleGraph.Connectivity.WalkCounting

set_option autoImplicit false

/-!
# Nested separators

This file contains the graph-theoretic part of the chain argument in the
proof of the polynomial forest estimate. All statements are about a simple
graph `G`, two vertices `u` and `p`, and sets of vertices that separate `u`
from `p`.

* `AvoidReach G X a b`: a walk from `a` to `b` avoids the set `X`.
* `Separates G X u p`: `u` and `p` are outside `X`, and no walk from `u` to `p`
  avoids `X`.
* `nested`: two disjoint connected separators are nested. One of them lies on
  the side of `p` of the other, and then the other lies on the side of `u` of
  the first.
* `Before`: the resulting order on pairwise disjoint connected separators. It
  is total, asymmetric and transitive.
* `block`: the set of vertices between two separators. Every edge that leaves
  a block ends in one of the two separators. Different blocks are disjoint
  and not adjacent.

The sets are arbitrary connected sets. In the application they are the vertex
sets of cycles.
-/

namespace Erdos1016.PolynomialBound.Separation

open SimpleGraph

variable {V : Type*} (G : SimpleGraph V)

/-! ### Walks that avoid a set -/

/-- Some walk from `a` to `b` has no vertex in `X`. Both ends are outside `X`. -/
def AvoidReach (X : Set V) (a b : V) : Prop :=
  ∃ p : G.Walk a b, ∀ v ∈ p.support, v ∉ X

variable {G}

theorem AvoidReach.refl {X : Set V} {a : V} (ha : a ∉ X) : AvoidReach G X a a := by
  refine ⟨Walk.nil, ?_⟩
  intro v hv
  rw [Walk.support_nil, List.mem_singleton] at hv
  rw [hv]
  exact ha

theorem AvoidReach.symm {X : Set V} {a b : V} (h : AvoidReach G X a b) :
    AvoidReach G X b a := by
  obtain ⟨p, hp⟩ := h
  refine ⟨p.reverse, ?_⟩
  intro v hv
  rw [Walk.support_reverse, List.mem_reverse] at hv
  exact hp v hv

theorem AvoidReach.trans {X : Set V} {a b c : V} (h₁ : AvoidReach G X a b)
    (h₂ : AvoidReach G X b c) : AvoidReach G X a c := by
  obtain ⟨p, hp⟩ := h₁
  obtain ⟨q, hq⟩ := h₂
  refine ⟨p.append q, ?_⟩
  intro v hv
  rw [Walk.mem_support_append_iff] at hv
  rcases hv with h | h
  · exact hp v h
  · exact hq v h

theorem AvoidReach.left_not_mem {X : Set V} {a b : V} (h : AvoidReach G X a b) : a ∉ X := by
  obtain ⟨p, hp⟩ := h
  exact hp a p.start_mem_support

theorem AvoidReach.right_not_mem {X : Set V} {a b : V} (h : AvoidReach G X a b) : b ∉ X := by
  obtain ⟨p, hp⟩ := h
  exact hp b p.end_mem_support

theorem AvoidReach.mono {X Y : Set V} (hXY : X ⊆ Y) {a b : V} (h : AvoidReach G Y a b) :
    AvoidReach G X a b := by
  obtain ⟨p, hp⟩ := h
  exact ⟨p, fun v hv hvX => hp v hv (hXY hvX)⟩

/-- One more step along an edge whose end is outside `X`. -/
theorem AvoidReach.step {X : Set V} {a b c : V} (h : AvoidReach G X a b)
    (hadj : G.Adj b c) (hc : c ∉ X) : AvoidReach G X a c := by
  refine h.trans ⟨Walk.cons hadj Walk.nil, ?_⟩
  intro v hv
  rw [Walk.support_cons, Walk.support_nil, List.mem_cons, List.mem_singleton] at hv
  rcases hv with rfl | rfl
  · exact h.right_not_mem
  · exact hc

theorem AvoidReach.reachable {X : Set V} {a b : V} (h : AvoidReach G X a b) :
    G.Reachable a b := by
  obtain ⟨p, _⟩ := h
  exact ⟨p⟩

/-- Every vertex of a walk that avoids `X` can be reached from its start. -/
theorem avoidReach_of_mem_support {X : Set V} {a b : V} (p : G.Walk a b)
    (hp : ∀ v ∈ p.support, v ∉ X) {v : V} (hv : v ∈ p.support) : AvoidReach G X a v := by
  classical
  exact ⟨p.takeUntil v hv, fun w hw => hp w (p.support_takeUntil_subset hv hw)⟩

/-- A walk that starts outside `X` and meets `X` leaves the part reachable from
its start through an edge into `X`. -/
theorem exists_first_hit {X : Set V} {a b : V} (p : G.Walk a b) (ha : a ∉ X)
    (hhit : ∃ v ∈ p.support, v ∈ X) :
    ∃ z x, AvoidReach G X a z ∧ G.Adj z x ∧ x ∈ X := by
  induction p with
  | nil =>
    obtain ⟨v, hv, hvX⟩ := hhit
    rw [Walk.support_nil, List.mem_singleton] at hv
    rw [hv] at hvX
    exact absurd hvX ha
  | @cons a c b hadj q ih =>
    by_cases hc : c ∈ X
    · exact ⟨a, c, AvoidReach.refl ha, hadj, hc⟩
    · obtain ⟨v, hv, hvX⟩ := hhit
      rw [Walk.support_cons, List.mem_cons] at hv
      have hq : ∃ v ∈ q.support, v ∈ X := by
        rcases hv with rfl | hv
        · exact absurd hvX ha
        · exact ⟨v, hv, hvX⟩
      obtain ⟨z, x, hz, hzx, hx⟩ := ih hc hq
      exact ⟨z, x, ((AvoidReach.refl ha).step hadj hc).trans hz, hzx, hx⟩

/-! ### Connected sets, sides and separators -/

variable (G)

/-- Any two vertices of `C` are joined by a walk inside `C`. -/
def IsConnectedSet (C : Set V) : Prop :=
  ∀ a ∈ C, ∀ b ∈ C, ∃ p : G.Walk a b, ∀ v ∈ p.support, v ∈ C

/-- The vertices that can be reached from `a` after the deletion of `X`. -/
def side (X : Set V) (a : V) : Set V := {v | AvoidReach G X a v}

/-- `u` and `p` are outside `X`, and no walk from `u` to `p` avoids `X`. -/
def Separates (X : Set V) (u p : V) : Prop :=
  u ∉ X ∧ p ∉ X ∧ ¬ AvoidReach G X u p

variable {G}

theorem Separates.symm {X : Set V} {u p : V} (h : Separates G X u p) : Separates G X p u :=
  ⟨h.2.1, h.1, fun h' => h.2.2 h'.symm⟩

/-- A connected set that is disjoint from `X` lies in one side of `X`. -/
theorem IsConnectedSet.avoidReach {C X : Set V} (hC : IsConnectedSet G C)
    (hd : Disjoint C X) {a b : V} (ha : a ∈ C) (hb : b ∈ C) : AvoidReach G X a b := by
  obtain ⟨p, hp⟩ := hC a ha b hb
  exact ⟨p, fun v hv hvX => Set.disjoint_left.mp hd (hp v hv) hvX⟩

theorem mem_side_self {X : Set V} {a : V} (ha : a ∉ X) : a ∈ side G X a :=
  AvoidReach.refl ha

theorem side_disjoint_set (X : Set V) (a : V) : Disjoint (side G X a) X :=
  Set.disjoint_left.mpr fun _ hv hvX => AvoidReach.right_not_mem hv hvX

/-- The two sides of a separator are disjoint. -/
theorem Separates.sides_disjoint {X : Set V} {u p : V} (h : Separates G X u p) :
    Disjoint (side G X u) (side G X p) :=
  Set.disjoint_left.mpr fun _ hu hp => h.2.2 (AvoidReach.trans hu (AvoidReach.symm hp))

/-- A neighbour of a vertex of a side is in the side or in the deleted set. -/
theorem mem_side_or_mem_of_adj {X : Set V} {a v w : V} (hv : v ∈ side G X a)
    (hadj : G.Adj v w) : w ∈ side G X a ∨ w ∈ X := by
  by_cases hw : w ∈ X
  · exact Or.inr hw
  · exact Or.inl (AvoidReach.step hv hadj hw)

/-- If a connected set that is disjoint from `X` meets a side, it lies in it. -/
theorem IsConnectedSet.subset_side {C X : Set V} (hC : IsConnectedSet G C)
    (hd : Disjoint C X) {a x : V} (hx : x ∈ C) (hxs : x ∈ side G X a) : C ⊆ side G X a :=
  fun _ hy => AvoidReach.trans hxs (hC.avoidReach hd hx hy)

/-- A separator of two joined vertices has a vertex next to the side of the first. -/
theorem Separates.exists_frontier {X : Set V} {u p : V} (h : Separates G X u p)
    (hup : G.Reachable u p) : ∃ z x, z ∈ side G X u ∧ G.Adj z x ∧ x ∈ X := by
  obtain ⟨w⟩ := hup
  have hhit : ∃ v ∈ w.support, v ∈ X := by
    by_contra hno
    push_neg at hno
    exact h.2.2 ⟨w, hno⟩
  exact exists_first_hit w h.1 hhit

/-- A walk from `u` inside the side of `u` of `C₁` avoids every set that does
not meet that side. -/
theorem avoidReach_of_side_disjoint {C₁ C₂ : Set V} {u z : V}
    (hz : AvoidReach G C₁ u z) (hd : Disjoint C₂ (side G C₁ u)) : AvoidReach G C₂ u z := by
  obtain ⟨q, hq⟩ := hz
  exact ⟨q, fun v hv hv2 =>
    Set.disjoint_left.mp hd hv2 (avoidReach_of_mem_support q hq hv)⟩

/-- A connected separator that is disjoint from another connected separator
meets one of the two sides of the other, and then lies in it. -/
theorem subset_side_or_side {u p : V} {C₁ C₂ : Set V} (hup : G.Reachable u p)
    (h₁ : Separates G C₁ u p) (hc₁ : IsConnectedSet G C₁)
    (h₂ : Separates G C₂ u p) (hc₂ : IsConnectedSet G C₂) (hd : Disjoint C₁ C₂) :
    C₂ ⊆ side G C₁ u ∨ C₂ ⊆ side G C₁ p := by
  by_cases hu : ∃ x ∈ C₂, x ∈ side G C₁ u
  · obtain ⟨x, hx, hxs⟩ := hu
    exact Or.inl (hc₂.subset_side hd.symm hx hxs)
  by_cases hp : ∃ x ∈ C₂, x ∈ side G C₁ p
  · obtain ⟨x, hx, hxs⟩ := hp
    exact Or.inr (hc₂.subset_side hd.symm hx hxs)
  exfalso
  push_neg at hu hp
  have hdu : Disjoint C₂ (side G C₁ u) := Set.disjoint_left.mpr hu
  have hdp : Disjoint C₂ (side G C₁ p) := Set.disjoint_left.mpr hp
  obtain ⟨z, a, hz, hza, ha⟩ := h₁.exists_frontier hup
  obtain ⟨z', b, hz', hzb, hb⟩ := h₁.symm.exists_frontier hup.symm
  have s1 : AvoidReach G C₂ u z := avoidReach_of_side_disjoint hz hdu
  have ha2 : a ∉ C₂ := fun h => Set.disjoint_left.mp hd ha h
  have hb2 : b ∉ C₂ := fun h => Set.disjoint_left.mp hd hb h
  have s2 : AvoidReach G C₂ u a := s1.step hza ha2
  have s3 : AvoidReach G C₂ a b := hc₁.avoidReach hd ha hb
  have s4 : AvoidReach G C₂ p z' := avoidReach_of_side_disjoint hz' hdp
  have s5 : AvoidReach G C₂ p b := s4.step hzb hb2
  exact h₂.2.2 ((s2.trans s3).trans s5.symm)

/-- Two disjoint connected separators cannot each lie on the side of `p` of
the other. -/
theorem not_both_on_far_side {u p : V} {C₁ C₂ : Set V} (hup : G.Reachable u p)
    (h₁ : Separates G C₁ u p) (h₂ : Separates G C₂ u p) (hd : Disjoint C₁ C₂)
    (h21 : C₂ ⊆ side G C₁ p) (h12 : C₁ ⊆ side G C₂ p) : False := by
  obtain ⟨z, a, hz, hza, ha⟩ := h₁.exists_frontier hup
  have hdu : Disjoint C₂ (side G C₁ u) :=
    Set.disjoint_left.mpr fun x hx hxu =>
      Set.disjoint_left.mp h₁.sides_disjoint hxu (h21 hx)
  have s1 : AvoidReach G C₂ u z := avoidReach_of_side_disjoint hz hdu
  have ha2 : a ∉ C₂ := fun h => Set.disjoint_left.mp hd ha h
  have s2 : AvoidReach G C₂ u a := s1.step hza ha2
  exact h₂.2.2 (s2.trans (AvoidReach.symm (h12 ha)))

/-- **Nested separators.** Two disjoint connected separators of `u` from `p`
are nested: one lies on the side of `p` of the other, and then the other lies
on the side of `u` of the first. -/
theorem nested {u p : V} {C₁ C₂ : Set V} (hup : G.Reachable u p)
    (h₁ : Separates G C₁ u p) (hc₁ : IsConnectedSet G C₁)
    (h₂ : Separates G C₂ u p) (hc₂ : IsConnectedSet G C₂) (hd : Disjoint C₁ C₂) :
    (C₂ ⊆ side G C₁ p ∧ C₁ ⊆ side G C₂ u) ∨ (C₂ ⊆ side G C₁ u ∧ C₁ ⊆ side G C₂ p) := by
  rcases subset_side_or_side hup h₁ hc₁ h₂ hc₂ hd with h21 | h21
  · rcases subset_side_or_side hup h₂ hc₂ h₁ hc₁ hd.symm with h12 | h12
    · exact absurd (not_both_on_far_side hup.symm h₁.symm h₂.symm hd h21 h12) id
    · exact Or.inr ⟨h21, h12⟩
  · rcases subset_side_or_side hup h₂ hc₂ h₁ hc₁ hd.symm with h12 | h12
    · exact Or.inl ⟨h21, h12⟩
    · exact absurd (not_both_on_far_side hup h₁ h₂ hd h21 h12) id

/-! ### The order on disjoint separators -/

variable (G)

/-- `C₁` comes before `C₂`, seen from `u`: `C₁` lies on the side of `u` of `C₂`. -/
def Before (u : V) (C₁ C₂ : Set V) : Prop := C₁ ⊆ side G C₂ u

variable {G}

/-- Equivalent form: `C₂` lies on the side of `p` of `C₁`. -/
theorem before_iff {u p : V} {C₁ C₂ : Set V} (hup : G.Reachable u p)
    (h₁ : Separates G C₁ u p) (hc₁ : IsConnectedSet G C₁)
    (h₂ : Separates G C₂ u p) (hc₂ : IsConnectedSet G C₂) (hd : Disjoint C₁ C₂) :
    Before G u C₁ C₂ ↔ C₂ ⊆ side G C₁ p := by
  constructor
  · intro hb
    rcases nested hup h₁ hc₁ h₂ hc₂ hd with h | h
    · exact h.1
    · -- `C₁` lies on both sides of `C₂`
      obtain ⟨z, a, _, _, ha⟩ := h₁.exists_frontier hup
      exact absurd (Set.disjoint_left.mp h₂.sides_disjoint (hb ha) (h.2 ha)) id
  · intro hb
    rcases nested hup h₁ hc₁ h₂ hc₂ hd with h | h
    · exact h.2
    · obtain ⟨z, a, _, _, ha⟩ := h₂.exists_frontier hup
      exact absurd (Set.disjoint_left.mp h₁.sides_disjoint (h.1 ha) (hb ha)) id

/-- The order is total. -/
theorem before_total {u p : V} {C₁ C₂ : Set V} (hup : G.Reachable u p)
    (h₁ : Separates G C₁ u p) (hc₁ : IsConnectedSet G C₁)
    (h₂ : Separates G C₂ u p) (hc₂ : IsConnectedSet G C₂) (hd : Disjoint C₁ C₂) :
    Before G u C₁ C₂ ∨ Before G u C₂ C₁ := by
  rcases nested hup h₁ hc₁ h₂ hc₂ hd with h | h
  · exact Or.inl h.2
  · exact Or.inr h.1

/-- The order is asymmetric. -/
theorem before_asymm {u p : V} {C₁ C₂ : Set V} (hup : G.Reachable u p)
    (h₁ : Separates G C₁ u p) (hc₁ : IsConnectedSet G C₁)
    (h₂ : Separates G C₂ u p) (hc₂ : IsConnectedSet G C₂) (hd : Disjoint C₁ C₂)
    (h12 : Before G u C₁ C₂) (h21 : Before G u C₂ C₁) : False := by
  have h := (before_iff hup h₁ hc₁ h₂ hc₂ hd).mp h12
  obtain ⟨z, a, _, _, ha⟩ := h₂.exists_frontier hup
  exact Set.disjoint_left.mp h₁.sides_disjoint (h21 ha) (h ha)

/-- If `C₁` comes before `C₂`, the side of `u` grows. -/
theorem side_subset_side_of_before {u p : V} {C₁ C₂ : Set V} (hup : G.Reachable u p)
    (h₁ : Separates G C₁ u p) (hc₁ : IsConnectedSet G C₁)
    (h₂ : Separates G C₂ u p) (hc₂ : IsConnectedSet G C₂) (hd : Disjoint C₁ C₂)
    (hb : Before G u C₁ C₂) : side G C₁ u ⊆ side G C₂ u := by
  have h := (before_iff hup h₁ hc₁ h₂ hc₂ hd).mp hb
  have hdu : Disjoint C₂ (side G C₁ u) :=
    Set.disjoint_left.mpr fun x hx hxu =>
      Set.disjoint_left.mp h₁.sides_disjoint hxu (h hx)
  exact fun _ hx => avoidReach_of_side_disjoint hx hdu

/-- The order is transitive. -/
theorem before_trans {u p : V} {C₁ C₂ C₃ : Set V} (hup : G.Reachable u p)
    (h₂ : Separates G C₂ u p) (hc₂ : IsConnectedSet G C₂)
    (h₃ : Separates G C₃ u p) (hc₃ : IsConnectedSet G C₃)
    (hd23 : Disjoint C₂ C₃)
    (h12 : Before G u C₁ C₂) (h23 : Before G u C₂ C₃) : Before G u C₁ C₃ :=
  fun _ hx => side_subset_side_of_before hup h₂ hc₂ h₃ hc₃ hd23 h23 (h12 hx)

/-! ### Blocks -/

variable (G)

/-- The vertices strictly between two separators `C₁` and `C₂`, seen from `u`. -/
def block (u : V) (C₁ C₂ : Set V) : Set V := side G C₂ u \ (side G C₁ u ∪ C₁)

variable {G}

/-- Every edge that leaves a block ends in one of its two separators. -/
theorem mem_separator_of_adj_block {u : V} {C₁ C₂ : Set V} {x y : V}
    (hx : x ∈ block G u C₁ C₂) (hadj : G.Adj x y) (hy : y ∉ block G u C₁ C₂) :
    y ∈ C₁ ∨ y ∈ C₂ := by
  obtain ⟨hx2, hx1⟩ := hx
  rcases mem_side_or_mem_of_adj hx2 hadj with hy2 | hy2
  · by_cases hy1 : y ∈ side G C₁ u ∪ C₁
    · rcases hy1 with hy1 | hy1
      · exfalso
        by_cases hxC : x ∈ C₁
        · exact hx1 (Or.inr hxC)
        · exact hx1 (Or.inl (AvoidReach.step hy1 hadj.symm hxC))
      · exact Or.inl hy1
    · exact absurd ⟨hy2, hy1⟩ hy
  · exact Or.inr hy2

/-- A separator strictly between the two ends of a block lies in the block. -/
theorem subset_block {u p : V} {C₁ C₂ C₃ : Set V} (hup : G.Reachable u p)
    (h₁ : Separates G C₁ u p) (hc₁ : IsConnectedSet G C₁)
    (h₂ : Separates G C₂ u p) (hc₂ : IsConnectedSet G C₂)
    (hd12 : Disjoint C₁ C₂)
    (h12 : Before G u C₁ C₂) (h23 : Before G u C₂ C₃) : C₂ ⊆ block G u C₁ C₃ := by
  intro x hx
  refine ⟨h23 hx, ?_⟩
  rintro (h | h)
  · have hp := (before_iff hup h₁ hc₁ h₂ hc₂ hd12).mp h12
    exact Set.disjoint_left.mp h₁.sides_disjoint h (hp hx)
  · exact Set.disjoint_left.mp hd12 h hx

/-- Two blocks, one before the other, are disjoint and not adjacent. Here the
second block starts at `C₃`, and the side of `u` of the end `C₂` of the first
block lies inside the side of `u` of `C₃`. This holds when `C₂ = C₃` and when
`C₂` comes before `C₃`. -/
theorem block_not_adj {u : V} {C₁ C₂ C₃ C₄ : Set V} {x y : V}
    (hsides : side G C₂ u ⊆ side G C₃ u)
    (hx : x ∈ block G u C₁ C₂) (hy : y ∈ block G u C₃ C₄) : x ≠ y ∧ ¬ G.Adj x y := by
  have hx3 : x ∈ side G C₃ u := hsides hx.1
  constructor
  · rintro rfl
    exact hy.2 (Or.inl hx3)
  · intro hadj
    rcases mem_side_or_mem_of_adj hx3 hadj with h | h
    · exact hy.2 (Or.inl h)
    · exact hy.2 (Or.inr h)

/-- A block has no neighbour in a connected set `P` that contains `p` and is
disjoint from the far separator, and it does not meet `P`. -/
theorem block_no_neighbor_anchor {u p : V} {C₁ C₂ P : Set V}
    (h₂ : Separates G C₂ u p) (hP : IsConnectedSet G P) (hpP : p ∈ P)
    (hd : Disjoint P C₂) {x y : V} (hx : x ∈ block G u C₁ C₂) (hy : y ∈ P) :
    x ≠ y ∧ ¬ G.Adj x y := by
  have hyp : AvoidReach G C₂ y p := hP.avoidReach hd hy hpP
  constructor
  · rintro rfl
    exact h₂.2.2 (AvoidReach.trans hx.1 hyp)
  · intro hadj
    have hy2 : y ∉ C₂ := fun h => Set.disjoint_left.mp hd hy h
    exact h₂.2.2 ((AvoidReach.step hx.1 hadj hy2).trans hyp)

end Erdos1016.PolynomialBound.Separation
