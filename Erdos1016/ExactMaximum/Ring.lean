import Erdos1016.ExactMaximum.NetJoin

set_option autoImplicit false

/-!
# The ring of squares

The lower bound of the paper "The maximum number of cycles in a graph of large rank" uses the
rings of Horak and Kim. This file defines one network `ring k` that serves for both parities of
the rank, and proves the facts about a single tile.

The network `ring k` has `k + 1` tiles. The tile `i` is a square: its left vertices `L i x` and
its right vertices `R i y` (`x, y : Bool`) are joined by the four edges `sq i x y`. The edge
`link i x` joins `R i x` to `L (i+1) x`. Two more vertices `H false`, `H true` close the ring: the
edge `first x` joins `H x` to `L 0 x`, the edge `last x` joins `R k x` to `H x`, and the edge
`rung` joins `H false` and `H true`.

Without the edge `rung` this is a ring of `k + 1` squares in which one pair of connecting edges
is subdivided. It has rank `2k + 3` and as many cycles as the ring of `k + 1` squares. With the
edge `rung` it is the ring with `k + 1` squares and one single rung, of rank `2k + 4`.

This file proves, for every tile `i` and within the edges of the tile:

* there are at least two paths from `L i x` to `R i y` (`two_le_tile_paths`), from `L i false` to
  `L i true` (`two_le_tile_paths_left`), and from `R i false` to `R i true`
  (`two_le_tile_paths_right`);
* the edges `sq i x y` and `sq i x' y'` with `x ≠ x'`, `y ≠ y'` are a pair of disjoint paths
  (`isPathPair_tile`);
* the four edges of the tile form a cycle (`isCycleWord_tile`).

The count of the cycles of the ring is not in this file.
-/

noncomputable section
open scoped BigOperators

namespace Erdos1016.ExactMaximum.Ring

open BoundaryTrace BoundaryTrace.Network

local instance ringDecidable (p : Prop) : Decidable p := Classical.propDecidable p

/-- The vertices of the ring: the left and the right vertices of the tiles, and two hubs. -/
abbrev Vertex (k : ℕ) : Type := (Fin (k + 1) × Bool) ⊕ (Fin (k + 1) × Bool) ⊕ Bool

/-- The edges of the ring: the edges of the tiles, the links between consecutive tiles, the
edges at the hubs, and the rung. -/
abbrev Edge (k : ℕ) : Type :=
  (Fin (k + 1) × Bool × Bool) ⊕ (Fin k × Bool) ⊕ Bool ⊕ Bool ⊕ Unit

variable {k : ℕ}

/-- The left vertex `x` of the tile `i`. -/
def L (i : Fin (k + 1)) (x : Bool) : Vertex k := Sum.inl (i, x)

/-- The right vertex `x` of the tile `i`. -/
def R (i : Fin (k + 1)) (x : Bool) : Vertex k := Sum.inr (Sum.inl (i, x))

/-- The hub `x`. -/
def H (x : Bool) : Vertex k := Sum.inr (Sum.inr x)

/-- The edge of the tile `i` from its left vertex `x` to its right vertex `y`. -/
def sq (i : Fin (k + 1)) (x y : Bool) : Edge k := Sum.inl (i, x, y)

/-- The edge from the right vertex `x` of the tile `i` to the left vertex `x` of the next
tile. -/
def link (i : Fin k) (x : Bool) : Edge k := Sum.inr (Sum.inl (i, x))

/-- The edge from the hub `x` to the left vertex `x` of the first tile. -/
def first (x : Bool) : Edge k := Sum.inr (Sum.inr (Sum.inl x))

/-- The edge from the right vertex `x` of the last tile to the hub `x`. -/
def last (x : Bool) : Edge k := Sum.inr (Sum.inr (Sum.inr (Sum.inl x)))

/-- The edge between the two hubs. -/
def rung : Edge k := Sum.inr (Sum.inr (Sum.inr (Sum.inr ())))

/-- The first end of an edge. -/
def src : Edge k → Vertex k
  | Sum.inl (i, x, _) => L i x
  | Sum.inr (Sum.inl (i, x)) => R i.castSucc x
  | Sum.inr (Sum.inr (Sum.inl x)) => H x
  | Sum.inr (Sum.inr (Sum.inr (Sum.inl x))) => R (Fin.last k) x
  | Sum.inr (Sum.inr (Sum.inr (Sum.inr _))) => H false

/-- The second end of an edge. -/
def dst : Edge k → Vertex k
  | Sum.inl (i, _, y) => R i y
  | Sum.inr (Sum.inl (i, x)) => L i.succ x
  | Sum.inr (Sum.inr (Sum.inl x)) => L 0 x
  | Sum.inr (Sum.inr (Sum.inr (Sum.inl x))) => H x
  | Sum.inr (Sum.inr (Sum.inr (Sum.inr _))) => H true

theorem src_ne_dst (e : Edge k) : src e ≠ dst e := by
  rcases e with ⟨i, x, y⟩ | ⟨i, x⟩ | x | x | u
  all_goals
    intro h
    simp [src, dst, L, R, H] at h

/-- **The ring.** -/
def ring (k : ℕ) : Network (Vertex k) (Edge k) where
  src := src
  dst := dst
  noLoops := src_ne_dst

/-! ### The ends of the edges -/

theorem joins_sq (i : Fin (k + 1)) (x y : Bool) : (ring k).Joins (sq i x y) (L i x) (R i y) :=
  Or.inl ⟨rfl, rfl⟩

theorem joins_link (i : Fin k) (x : Bool) :
    (ring k).Joins (link i x) (R i.castSucc x) (L i.succ x) :=
  Or.inl ⟨rfl, rfl⟩

theorem joins_first (x : Bool) : (ring k).Joins (first x) (H x) (L 0 x) :=
  Or.inl ⟨rfl, rfl⟩

theorem joins_last (x : Bool) : (ring k).Joins (last x) (R (Fin.last k) x) (H x) :=
  Or.inl ⟨rfl, rfl⟩

theorem joins_rung : (ring k).Joins (rung : Edge k) (H false) (H true) :=
  Or.inl ⟨rfl, rfl⟩

/-! ### Different vertices and different edges -/

theorem L_ne_R (i i' : Fin (k + 1)) (x x' : Bool) : (L i x : Vertex k) ≠ R i' x' := by
  simp [L, R]

theorem L_ne_H (i : Fin (k + 1)) (x x' : Bool) : (L i x : Vertex k) ≠ H x' := by
  simp [L, H]

theorem R_ne_H (i : Fin (k + 1)) (x x' : Bool) : (R i x : Vertex k) ≠ H x' := by
  simp [R, H]

theorem L_ne_L {i : Fin (k + 1)} {x x' : Bool} (h : x ≠ x') : (L i x : Vertex k) ≠ L i x' := by
  simp [L, h]

theorem R_ne_R {i : Fin (k + 1)} {x x' : Bool} (h : x ≠ x') : (R i x : Vertex k) ≠ R i x' := by
  simp [R, h]

theorem sq_ne_left {i : Fin (k + 1)} {x x' : Bool} (y y' : Bool) (h : x ≠ x') :
    (sq i x y : Edge k) ≠ sq i x' y' := by
  simp [sq, h]

theorem sq_ne_right {i : Fin (k + 1)} (x x' : Bool) {y y' : Bool} (h : y ≠ y') :
    (sq i x y : Edge k) ≠ sq i x' y' := by
  simp [sq, h]

/-! ### Sets of edges and of vertices -/

/-- The edges of the tile `i`. -/
def tileEdge (i : Fin (k + 1)) : Edge k → Prop
  | Sum.inl (i', _, _) => i' = i
  | _ => False

/-- The edges of the tiles `0, …, i` and of the links between them. -/
def chainEdge (i : Fin (k + 1)) : Edge k → Prop
  | Sum.inl (i', _, _) => i' ≤ i
  | Sum.inr (Sum.inl (i', _)) => i'.succ ≤ i
  | _ => False

/-- The vertices of the tiles `0, …, i`. -/
def upTo (i : Fin (k + 1)) : Vertex k → Prop
  | Sum.inl (i', _) => i' ≤ i
  | Sum.inr (Sum.inl (i', _)) => i' ≤ i
  | Sum.inr (Sum.inr _) => False

theorem tileEdge_sq (i : Fin (k + 1)) (x y : Bool) : tileEdge i (sq i x y) := rfl

/-- An edge of a tile of the chain is an edge of the chain. -/
theorem chainEdge_of_tileEdge {i j : Fin (k + 1)} (hij : j ≤ i) {e : Edge k}
    (h : tileEdge j e) : chainEdge i e := by
  rcases e with ⟨i', x, y⟩ | ⟨i', x⟩ | x | x | u
  · have h' : i' = j := h
    show i' ≤ i
    rw [h']
    exact hij
  all_goals exact h.elim

/-- The chain grows with its last tile. -/
theorem chainEdge_mono {i j : Fin (k + 1)} (hij : j ≤ i) {e : Edge k} (h : chainEdge j e) :
    chainEdge i e := by
  rcases e with ⟨i', x, y⟩ | ⟨i', x⟩ | x | x | u
  · exact le_trans (show i' ≤ j from h) hij
  · exact le_trans (show i'.succ ≤ j from h) hij
  all_goals exact h.elim

/-- The links before the tile `i + 1` are edges of the chain that ends in this tile. -/
theorem chainEdge_link (i : Fin k) (x : Bool) : chainEdge i.succ (link i x) :=
  show i.succ ≤ i.succ from le_refl _

/-- An edge of the chain has both ends in the tiles of the chain. -/
theorem inside_of_chainEdge {i : Fin (k + 1)} {e : Edge k} (h : chainEdge i e) :
    (ring k).inside (upTo i) e := by
  rcases e with ⟨i', x, y⟩ | ⟨i', x⟩ | x | x | u
  · exact ⟨show i' ≤ i from h, show i' ≤ i from h⟩
  · have h' : i'.succ ≤ i := h
    exact ⟨show i'.castSucc ≤ i from le_trans (le_of_lt (Fin.castSucc_lt_succ i')) h', h'⟩
  all_goals exact h.elim

/-- An edge of the tile `i + 1` has no end in the tiles `0, …, i`. -/
theorem outside_of_tileEdge (i : Fin k) {e : Edge k} (h : tileEdge i.succ e) :
    (ring k).outside (upTo i.castSucc) e := by
  rcases e with ⟨i', x, y⟩ | ⟨i', x⟩ | x | x | u
  · have h' : i' = i.succ := h
    have hlt : ¬ i.succ ≤ i.castSucc := not_le.2 (Fin.castSucc_lt_succ i)
    constructor
    · show ¬ i' ≤ i.castSucc
      rw [h']
      exact hlt
    · show ¬ i' ≤ i.castSucc
      rw [h']
      exact hlt
  all_goals exact h.elim

/-! ### Words of a few edges -/

theorem unitWord_self (e : Edge k) : (unitWord e : Edge k → Bit) e = 1 := by
  rw [unitWord_apply, if_pos rfl]

theorem unitWord_of_ne {e g : Edge k} (h : e ≠ g) : (unitWord e : Edge k → Bit) g = 0 := by
  rw [unitWord_apply, if_neg h]

/-- Two edges that have no end at `v` have no vertex at `v`. -/
theorem deg_two_edges_eq_zero {e f : Edge k} {s₁ t₁ s₂ t₂ v : Vertex k}
    (he : (ring k).Joins e s₁ t₁) (hf : (ring k).Joins f s₂ t₂) (h1 : v ≠ s₁) (h2 : v ≠ t₁)
    (h3 : v ≠ s₂) (h4 : v ≠ t₂) : (ring k).deg (unitWord e + unitWord f) v = 0 := by
  have k1 := (ring k).deg_add_le (unitWord e) (unitWord f) v
  have k2 := (ring k).deg_unitWord_of_joins he h1 h2
  have k3 := (ring k).deg_unitWord_of_joins hf h3 h4
  omega

/-! ### One tile -/

/-- The paths from `s` to `t` within a set of edges. -/
abbrev PathsIn (p : Edge k → Prop) (s t : Vertex k) : Type :=
  {P : (ring k).Word // (ring k).IsPathWord s t P ∧ Within P p}

/-- The path of three edges of the tile `i` from `L i x` to `R i y` that avoids the edge between
these two vertices. -/
theorem isPathWord_tile_long (i : Fin (k + 1)) {x x' y y' : Bool} (hx : x ≠ x') (hy : y ≠ y') :
    (ring k).IsPathWord (L i x) (R i y)
      (unitWord (sq i x y') + unitWord (sq i x' y') + unitWord (sq i x' y)) := by
  have h1 : (ring k).IsPathWord (L i x) (R i y') (unitWord (sq i x y')) :=
    (ring k).isPathWord_unitWord (joins_sq i x y')
  have h2 : (ring k).IsPathWord (L i x) (L i x')
      (unitWord (sq i x y') + unitWord (sq i x' y')) := by
    apply h1.add_pendant (joins_sq i x' y').symm
    exact (ring k).deg_unitWord_of_joins (joins_sq i x y') (L_ne_L (Ne.symm hx)) (L_ne_R _ _ _ _)
  apply h2.add_pendant (joins_sq i x' y)
  exact deg_two_edges_eq_zero (joins_sq i x y') (joins_sq i x' y') (L_ne_R _ _ _ _).symm
    (R_ne_R hy) (L_ne_R _ _ _ _).symm (R_ne_R hy)

/-- **Paths across a tile.** Within the tile `i` there are at least two paths from its left
vertex `x` to its right vertex `y`. -/
theorem two_le_tile_paths (i : Fin (k + 1)) (x y : Bool) :
    2 ≤ Nat.card (PathsIn (tileEdge i) (L i x) (R i y)) := by
  have hx : x ≠ !x := by cases x <;> decide
  have hy : y ≠ !y := by cases y <;> decide
  let P₁ : PathsIn (tileEdge i) (L i x) (R i y) :=
    ⟨unitWord (sq i x y), (ring k).isPathWord_unitWord (joins_sq i x y),
      within_unitWord (tileEdge_sq i x y)⟩
  let P₂ : PathsIn (tileEdge i) (L i x) (R i y) :=
    ⟨unitWord (sq i x (!y)) + unitWord (sq i (!x) (!y)) + unitWord (sq i (!x) y),
      isPathWord_tile_long i hx hy,
      ((within_unitWord (tileEdge_sq i x (!y))).add (within_unitWord (tileEdge_sq i (!x) (!y)))).add
        (within_unitWord (tileEdge_sq i (!x) y))⟩
  have hne : P₁ ≠ P₂ := by
    intro h
    have h1 : P₁.1 (sq i x y) = P₂.1 (sq i x y) := by rw [h]
    have h2 : P₁.1 (sq i x y) = 1 := unitWord_self _
    have h3 : P₂.1 (sq i x y) = 0 := by
      show unitWord (sq i x (!y)) (sq i x y) + unitWord (sq i (!x) (!y)) (sq i x y) +
        unitWord (sq i (!x) y) (sq i x y) = 0
      rw [unitWord_of_ne (sq_ne_right x x (Ne.symm hy)),
        unitWord_of_ne (sq_ne_left (!y) y (Ne.symm hx)),
        unitWord_of_ne (sq_ne_left y y (Ne.symm hx)), add_zero, add_zero]
    rw [h2, h3] at h1
    exact one_ne_zero h1
  exact Finite.one_lt_card_iff_nontrivial.2 ⟨P₁, P₂, hne⟩

/-- The path of two edges of the tile `i` from `L i x` to `L i x'` through `R i y`. -/
theorem isPathWord_tile_left (i : Fin (k + 1)) {x x' : Bool} (hx : x ≠ x') (y : Bool) :
    (ring k).IsPathWord (L i x) (L i x') (unitWord (sq i x y) + unitWord (sq i x' y)) := by
  apply ((ring k).isPathWord_unitWord (joins_sq i x y)).add_pendant (joins_sq i x' y).symm
  exact (ring k).deg_unitWord_of_joins (joins_sq i x y) (L_ne_L (Ne.symm hx)) (L_ne_R _ _ _ _)

/-- The path of two edges of the tile `i` from `R i y` to `R i y'` through `L i x`. -/
theorem isPathWord_tile_right (i : Fin (k + 1)) (x : Bool) {y y' : Bool} (hy : y ≠ y') :
    (ring k).IsPathWord (R i y) (R i y') (unitWord (sq i x y) + unitWord (sq i x y')) := by
  apply ((ring k).isPathWord_unitWord (joins_sq i x y)).symm.add_pendant (joins_sq i x y')
  exact (ring k).deg_unitWord_of_joins (joins_sq i x y) (L_ne_R _ _ _ _).symm
    (R_ne_R (Ne.symm hy))

/-- **Paths between the two left vertices of a tile.** There are at least two. -/
theorem two_le_tile_paths_left (i : Fin (k + 1)) :
    2 ≤ Nat.card (PathsIn (tileEdge i) (L i false) (L i true)) := by
  have hx : false ≠ true := by decide
  let P : Bool → PathsIn (tileEdge i) (L i false) (L i true) := fun y =>
    ⟨unitWord (sq i false y) + unitWord (sq i true y), isPathWord_tile_left i hx y,
      (within_unitWord (tileEdge_sq i false y)).add (within_unitWord (tileEdge_sq i true y))⟩
  have hne : P false ≠ P true := by
    intro h
    have h1 : (P false).1 (sq i false false) = (P true).1 (sq i false false) := by rw [h]
    have h2 : (P false).1 (sq i false false) = 1 := by
      show unitWord (sq i false false) (sq i false false) +
        unitWord (sq i true false) (sq i false false) = 1
      rw [unitWord_self, unitWord_of_ne (sq_ne_left false false (Ne.symm hx)), add_zero]
    have h3 : (P true).1 (sq i false false) = 0 := by
      show unitWord (sq i false true) (sq i false false) +
        unitWord (sq i true true) (sq i false false) = 0
      rw [unitWord_of_ne (sq_ne_right false false (Ne.symm hx)),
        unitWord_of_ne (sq_ne_left true false (Ne.symm hx)), add_zero]
    rw [h2, h3] at h1
    exact one_ne_zero h1
  exact Finite.one_lt_card_iff_nontrivial.2 ⟨P false, P true, hne⟩

/-- **Paths between the two right vertices of a tile.** There are at least two. -/
theorem two_le_tile_paths_right (i : Fin (k + 1)) :
    2 ≤ Nat.card (PathsIn (tileEdge i) (R i false) (R i true)) := by
  have hy : false ≠ true := by decide
  let P : Bool → PathsIn (tileEdge i) (R i false) (R i true) := fun x =>
    ⟨unitWord (sq i x false) + unitWord (sq i x true), isPathWord_tile_right i x hy,
      (within_unitWord (tileEdge_sq i x false)).add (within_unitWord (tileEdge_sq i x true))⟩
  have hne : P false ≠ P true := by
    intro h
    have h1 : (P false).1 (sq i false false) = (P true).1 (sq i false false) := by rw [h]
    have h2 : (P false).1 (sq i false false) = 1 := by
      show unitWord (sq i false false) (sq i false false) +
        unitWord (sq i false true) (sq i false false) = 1
      rw [unitWord_self, unitWord_of_ne (sq_ne_right false false (Ne.symm hy)), add_zero]
    have h3 : (P true).1 (sq i false false) = 0 := by
      show unitWord (sq i true false) (sq i false false) +
        unitWord (sq i true true) (sq i false false) = 0
      rw [unitWord_of_ne (sq_ne_left false false (Ne.symm hy)),
        unitWord_of_ne (sq_ne_left true false (Ne.symm hy)), add_zero]
    rw [h2, h3] at h1
    exact one_ne_zero h1
  exact Finite.one_lt_card_iff_nontrivial.2 ⟨P false, P true, hne⟩

/-- **A path pair across a tile.** Two edges of the tile `i` without a common end are disjoint
paths from `L i x` to `R i y` and from `L i x'` to `R i y'`. -/
theorem isPathPair_tile (i : Fin (k + 1)) {x x' y y' : Bool} (hx : x ≠ x') (hy : y ≠ y') :
    (ring k).IsPathPair (L i x) (R i y) (L i x') (R i y') (unitWord (sq i x y))
      (unitWord (sq i x' y')) := by
  refine ⟨(ring k).isPathWord_unitWord (joins_sq i x y),
    (ring k).isPathWord_unitWord (joins_sq i x' y'), ?_⟩
  apply (ring k).vertexDisjoint_unitWord (joins_sq i x' y')
  · exact (ring k).deg_unitWord_of_joins (joins_sq i x y) (L_ne_L (Ne.symm hx)) (L_ne_R _ _ _ _)
  · exact (ring k).deg_unitWord_of_joins (joins_sq i x y) (L_ne_R _ _ _ _).symm
      (R_ne_R (Ne.symm hy))

/-- **The cycle of a tile.** The four edges of the tile `i` form a cycle. -/
theorem isCycleWord_tile (i : Fin (k + 1)) :
    (ring k).IsCycleWord
      (unitWord (sq i false true) + unitWord (sq i true true) + unitWord (sq i true false) +
        unitWord (sq i false false)) := by
  have hb : false ≠ true := by decide
  have hP := isPathWord_tile_long (k := k) i hb hb
  apply hP.add_closing (joins_sq i false false)
  show unitWord (sq i false true) (sq i false false) +
    unitWord (sq i true true) (sq i false false) +
    unitWord (sq i true false) (sq i false false) = 0
  rw [unitWord_of_ne (sq_ne_right false false (Ne.symm hb)),
    unitWord_of_ne (sq_ne_left true false (Ne.symm hb)),
    unitWord_of_ne (sq_ne_left false false (Ne.symm hb)), add_zero, add_zero]

end Erdos1016.ExactMaximum.Ring
