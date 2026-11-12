import Erdos1016.ExactMaximum.NetCut

set_option autoImplicit false

/-!
# The subdivision of a network

The network `N.subdivide` has a new vertex on every edge of the network `N`. Its vertices are the
vertices and the edges of `N`. The edge `(e, false)` joins the first end of `e` and the new
vertex of `e`, and the edge `(e, true)` joins the new vertex and the second end of `e`.

The subdivision has no two edges with the same two ends (`subdivide_simple`), the same rank
(`networkRank_subdivide`) and the same number of cycles (`numCycles_subdivide`). So a statement
about the number of cycles of simple graphs of a given cyclomatic number holds for all networks.

The proofs use the even words. An even word of the subdivision takes both halves of an edge or
none (`eq_double_half_of_boundary_eq_zero`), so the even words of `N` and of `N.subdivide`
correspond, and the cycles are the minimal nonzero even words.
-/

noncomputable section
open scoped BigOperators

namespace Erdos1016.BoundaryTrace.Network

open BoundaryDecay

local instance netSubdivideDecidable (p : Prop) : Decidable p := Classical.propDecidable p

variable {V E : Type*}

/-- The network with a new vertex on every edge. -/
def subdivide (N : Network V E) : Network (V ⊕ E) (E × Bool) where
  src p := cond p.2 (Sum.inr p.1) (Sum.inl (N.src p.1))
  dst p := cond p.2 (Sum.inl (N.dst p.1)) (Sum.inr p.1)
  noLoops p := by
    rcases p with ⟨e, b⟩
    cases b
    · exact Sum.inl_ne_inr
    · exact Sum.inr_ne_inl

theorem subdivide_src_false (N : Network V E) (e : E) :
    N.subdivide.src (e, false) = Sum.inl (N.src e) := rfl

theorem subdivide_dst_false (N : Network V E) (e : E) :
    N.subdivide.dst (e, false) = Sum.inr e := rfl

theorem subdivide_src_true (N : Network V E) (e : E) :
    N.subdivide.src (e, true) = Sum.inr e := rfl

theorem subdivide_dst_true (N : Network V E) (e : E) :
    N.subdivide.dst (e, true) = Sum.inl (N.dst e) := rfl

/-- **No parallel edges.** An edge of the subdivision that joins the two ends of another edge is
this edge. -/
theorem subdivide_simple (N : Network V E) (p q : E × Bool)
    (h : N.subdivide.Joins p (N.subdivide.src q) (N.subdivide.dst q)) : p = q := by
  rcases p with ⟨e, b⟩
  rcases q with ⟨f, c⟩
  cases b <;> cases c
  · rcases h with ⟨_, h2⟩ | ⟨h1, _⟩
    · have hef : e = f := Sum.inr.inj h2
      rw [hef]
    · exact absurd h1 Sum.inl_ne_inr
  · rcases h with ⟨h1, _⟩ | ⟨h1, h2⟩
    · exact absurd h1 Sum.inl_ne_inr
    · have hef : e = f := Sum.inr.inj h2
      have h3 : N.src e = N.dst f := Sum.inl.inj h1
      rw [← hef] at h3
      exact absurd h3 (N.noLoops e)
  · rcases h with ⟨h1, _⟩ | ⟨h1, h2⟩
    · exact absurd h1 Sum.inr_ne_inl
    · have hef : e = f := Sum.inr.inj h1
      have h3 : N.dst e = N.src f := Sum.inl.inj h2
      rw [← hef] at h3
      exact absurd h3.symm (N.noLoops e)
  · rcases h with ⟨h1, _⟩ | ⟨h1, _⟩
    · have hef : e = f := Sum.inr.inj h1
      rw [hef]
    · exact absurd h1 Sum.inr_ne_inl

/-! ### Words -/

/-- The word of the subdivision that takes both halves of the edges of `x`. -/
def double (x : E → Bit) : E × Bool → Bit := fun p => x p.1

/-- The word of the first halves. -/
def half (y : E × Bool → Bit) : E → Bit := fun e => y (e, false)

theorem double_zero : double (0 : E → Bit) = 0 := rfl

theorem half_double (x : E → Bit) : half (double x) = x := rfl

theorem double_injective : Function.Injective (double : (E → Bit) → E × Bool → Bit) :=
  fun _ _ h => funext fun e => congrFun h (e, false)

variable [Fintype V] [Fintype E]

/-- The boundary at a new vertex: the sum of the two halves. -/
theorem boundary_subdivide_inr (N : Network V E) (y : E × Bool → Bit) (e₀ : E) :
    N.subdivide.boundary y (Sum.inr e₀) = y (e₀, false) + y (e₀, true) := by
  rw [boundary_apply, Fintype.sum_prod_type, Fintype.sum_prod_type]
  simp only [Fintype.sum_bool, subdivide_src_true, subdivide_src_false, subdivide_dst_true,
    subdivide_dst_false]
  rw [Finset.sum_eq_single_of_mem e₀ (Finset.mem_univ e₀) (fun e _ he => by
      rw [if_neg (fun h => he (Sum.inr.inj h)), if_neg Sum.inl_ne_inr, add_zero]),
    Finset.sum_eq_single_of_mem e₀ (Finset.mem_univ e₀) (fun e _ he => by
      rw [if_neg Sum.inl_ne_inr, if_neg (fun h => he (Sum.inr.inj h)), add_zero]),
    if_pos rfl, if_neg Sum.inl_ne_inr, if_neg Sum.inl_ne_inr, if_pos rfl, add_zero, zero_add,
    add_comm]

/-- The boundary at an old vertex. -/
theorem boundary_subdivide_inl (N : Network V E) (y : E × Bool → Bit) (v : V) :
    N.subdivide.boundary y (Sum.inl v) =
      (∑ e, if N.src e = v then y (e, false) else 0) +
        (∑ e, if N.dst e = v then y (e, true) else 0) := by
  rw [boundary_apply, Fintype.sum_prod_type, Fintype.sum_prod_type]
  simp only [Fintype.sum_bool, subdivide_src_true, subdivide_src_false, subdivide_dst_true,
    subdivide_dst_false]
  congr 1
  · apply Finset.sum_congr rfl
    intro e _
    rw [if_neg Sum.inr_ne_inl, zero_add]
    by_cases he : N.src e = v
    · rw [if_pos he, if_pos (by rw [he])]
    · rw [if_neg he, if_neg (fun h => he (Sum.inl.inj h))]
  · apply Finset.sum_congr rfl
    intro e _
    rw [if_neg Sum.inr_ne_inl, add_zero]
    by_cases he : N.dst e = v
    · rw [if_pos he, if_pos (by rw [he])]
    · rw [if_neg he, if_neg (fun h => he (Sum.inl.inj h))]

/-- The boundary of a doubled word at an old vertex is the boundary of the word. -/
theorem boundary_double_inl (N : Network V E) (x : E → Bit) (v : V) :
    N.subdivide.boundary (double x) (Sum.inl v) = N.boundary x v := by
  rw [boundary_subdivide_inl, boundary_apply]
  rfl

/-- The boundary of a doubled word at a new vertex is zero. -/
theorem boundary_double_inr (N : Network V E) (x : E → Bit) (e : E) :
    N.subdivide.boundary (double x) (Sum.inr e) = 0 := by
  rw [boundary_subdivide_inr]
  exact CharTwo.add_self_eq_zero (x e)

/-- A doubled word is even if and only if the word is even. -/
theorem boundary_double_eq_zero_iff (N : Network V E) (x : E → Bit) :
    N.subdivide.boundary (double x) = 0 ↔ N.boundary x = 0 := by
  constructor
  · intro h
    funext v
    rw [← N.boundary_double_inl x v, h]
    rfl
  · intro h
    funext w
    rcases w with v | e
    · rw [N.boundary_double_inl, h]
      rfl
    · rw [N.boundary_double_inr]
      rfl

/-- An even word of the subdivision takes both halves of an edge or none. -/
theorem eq_double_half_of_boundary_eq_zero (N : Network V E) {y : E × Bool → Bit}
    (h : N.subdivide.boundary y = 0) : y = double (half y) := by
  funext p
  rcases p with ⟨e, b⟩
  cases b
  · rfl
  · have h1 := congrFun h (Sum.inr e)
    rw [boundary_subdivide_inr] at h1
    exact (bit_eq_of_add_eq_zero h1).symm

/-! ### Cycles and rank -/

/-- A doubled word is a cycle of the subdivision if and only if the word is a cycle. -/
theorem isCycleWord_double_iff (N : Network V E) (x : E → Bit) :
    N.subdivide.IsCycleWord (double x) ↔ N.IsCycleWord x := by
  rw [N.subdivide.isCycleWord_iff_minimal (double x), N.isCycleWord_iff_minimal x]
  constructor
  · rintro ⟨h0, hb, hmin⟩
    refine ⟨fun hx => h0 (by rw [hx, double_zero]), (N.boundary_double_eq_zero_iff x).1 hb,
      fun z hsub hz => ?_⟩
    have hsub' : N.subdivide.IsSubword (double z) (double x) := fun p hp => hsub p.1 hp
    rcases hmin (double z) hsub' ((N.boundary_double_eq_zero_iff z).2 hz) with h | h
    · exact Or.inl (double_injective (by rw [h, double_zero]))
    · exact Or.inr (double_injective h)
  · rintro ⟨h0, hb, hmin⟩
    refine ⟨fun hx => h0 (double_injective (by rw [hx, double_zero])),
      (N.boundary_double_eq_zero_iff x).2 hb, fun y hsub hy => ?_⟩
    have hd := N.eq_double_half_of_boundary_eq_zero hy
    have hsub' : N.IsSubword (half y) x := fun e he => hsub (e, false) he
    have hz : N.boundary (half y) = 0 :=
      (N.boundary_double_eq_zero_iff (half y)).1 (by rw [← hd]; exact hy)
    rcases hmin (half y) hsub' hz with h | h
    · left
      rw [hd, h, double_zero]
    · right
      rw [hd, h]

/-- **The subdivision has the same number of cycles.** -/
theorem numCycles_subdivide (N : Network V E) : N.subdivide.numCycles = N.numCycles := by
  obtain ⟨f, hf⟩ : ∃ f : {x : N.Word // N.IsCycleWord x} →
      {y : N.subdivide.Word // N.subdivide.IsCycleWord y}, ∀ x, (f x).1 = double x.1 :=
    ⟨fun x => ⟨double x.1, (N.isCycleWord_double_iff x.1).2 x.2⟩, fun _ => rfl⟩
  have hbij : Function.Bijective f := by
    constructor
    · intro a b hab
      have h1 : double a.1 = double b.1 := by rw [← hf a, ← hf b, hab]
      exact Subtype.ext (double_injective h1)
    · intro y
      have hd := N.eq_double_half_of_boundary_eq_zero y.2.boundary_eq_zero
      have hc : N.subdivide.IsCycleWord (double (half y.1)) := by
        rw [← hd]
        exact y.2
      refine ⟨⟨half y.1, (N.isCycleWord_double_iff (half y.1)).1 hc⟩, ?_⟩
      apply Subtype.ext
      rw [hf]
      exact hd.symm
  exact (Nat.card_eq_of_bijective f hbij).symm

/-- **The subdivision has the same rank.** -/
theorem networkRank_subdivide (N : Network V E) : networkRank N.subdivide = networkRank N := by
  obtain ⟨f, hf⟩ : ∃ f : N.CycleSpace → N.subdivide.CycleSpace, ∀ x, (f x).1 = double x.1 :=
    ⟨fun x => ⟨double x.1, LinearMap.mem_ker.2
      ((N.boundary_double_eq_zero_iff x.1).2 (LinearMap.mem_ker.1 x.2))⟩, fun _ => rfl⟩
  have hbij : Function.Bijective f := by
    constructor
    · intro a b hab
      have h1 : double a.1 = double b.1 := by rw [← hf a, ← hf b, hab]
      exact Subtype.ext (double_injective h1)
    · intro y
      have hy : N.subdivide.boundary y.1 = 0 := LinearMap.mem_ker.1 y.2
      have hd := N.eq_double_half_of_boundary_eq_zero hy
      have hz : N.boundary (half y.1) = 0 :=
        (N.boundary_double_eq_zero_iff (half y.1)).1 (by rw [← hd]; exact hy)
      refine ⟨⟨half y.1, LinearMap.mem_ker.2 hz⟩, ?_⟩
      apply Subtype.ext
      rw [hf]
      exact hd.symm
  have h1 := Fintype.card_of_bijective hbij
  rw [cycleSpace_card_network, cycleSpace_card_network] at h1
  exact (Nat.pow_right_injective (le_refl 2) h1).symm

end Erdos1016.BoundaryTrace.Network
