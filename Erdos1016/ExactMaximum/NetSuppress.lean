import Erdos1016.ExactMaximum.NetBridge

set_option autoImplicit false

/-!
# Removing a vertex of degree two

Let the vertex `v` of the network `N` be on exactly two edges: `e` joins `u` and `v`, and `f`
joins `v` and `w`, with `u ≠ w` (`Thread`). The network `N.suppress e f u w` has the same
vertices. It does not have the edge `f`, and its edge `e` joins `u` and `w`. So `v` is an
isolated vertex of the new network.

This is the step of Lemma 5.2 (a) of the paper "The maximum number of cycles in a graph of large
rank". The new network has the same rank (`networkRank_suppress`), the same number of cycles
(`numCycles_suppress`) and the same number of paths between two vertices other than `v`
(`numPaths_suppress`). Every other vertex keeps its degree (`deg_suppress`).

The proofs use the even words. An even word of `N` takes both edges `e`, `f` or none, so the
words of the new network correspond to the words of `N` with this property (`grow`).
-/

noncomputable section
open scoped BigOperators

namespace Erdos1016.BoundaryTrace.Network

open BoundaryDecay

local instance netSuppressDecidable (p : Prop) : Decidable p := Classical.propDecidable p

variable {V E : Type*}

/-- The vertex `v` is on exactly the two edges `e` and `f`. The edge `e` joins `u` and `v`, the
edge `f` joins `v` and `w`, and `u ≠ w`. -/
structure Thread (N : Network V E) (e f : E) (u v w : V) : Prop where
  he : N.Joins e u v
  hf : N.Joins f v w
  hef : e ≠ f
  huw : u ≠ w
  only : ∀ g, N.src g = v ∨ N.dst g = v → g = e ∨ g = f

/-- The network without the edge `f`, in which the edge `e` joins `u` and `w`. -/
def suppress (N : Network V E) (e f : E) (u w : V) (huw : u ≠ w) : Network V {g : E // g ≠ f} where
  src g := if g.1 = e then u else N.src g.1
  dst g := if g.1 = e then w else N.dst g.1
  noLoops g := by
    by_cases h : g.1 = e
    · dsimp only
      rw [if_pos h, if_pos h]
      exact huw
    · dsimp only
      rw [if_neg h, if_neg h]
      exact N.noLoops g.1

section Basic

variable (N : Network V E) {e f : E} {u w : V} (huw : u ≠ w)

theorem suppress_src_of_ne (g : {g : E // g ≠ f}) (hg : g.1 ≠ e) :
    (N.suppress e f u w huw).src g = N.src g.1 := if_neg hg

theorem suppress_dst_of_ne (g : {g : E // g ≠ f}) (hg : g.1 ≠ e) :
    (N.suppress e f u w huw).dst g = N.dst g.1 := if_neg hg

theorem suppress_src_of_eq (g : {g : E // g ≠ f}) (hg : g.1 = e) :
    (N.suppress e f u w huw).src g = u := if_pos hg

theorem suppress_dst_of_eq (g : {g : E // g ≠ f}) (hg : g.1 = e) :
    (N.suppress e f u w huw).dst g = w := if_pos hg

/-- In the new network the edge `e` joins `u` and `w`. -/
theorem suppress_joins_of_eq (g : {g : E // g ≠ f}) (hg : g.1 = e) :
    (N.suppress e f u w huw).Joins g u w :=
  Or.inl ⟨N.suppress_src_of_eq huw g hg, N.suppress_dst_of_eq huw g hg⟩

/-- Every other edge joins the same vertices. -/
theorem suppress_joins_of_ne (g : {g : E // g ≠ f}) (hg : g.1 ≠ e) (a b : V) :
    (N.suppress e f u w huw).Joins g a b ↔ N.Joins g.1 a b := by
  unfold Joins
  rw [N.suppress_src_of_ne huw g hg, N.suppress_dst_of_ne huw g hg]

end Basic

namespace Thread

variable {N : Network V E} {e f : E} {u v w : V} (T : Thread N e f u v w)
include T

theorem u_ne_v : u ≠ v := T.he.ne

theorem v_ne_w : v ≠ w := T.hf.ne

/-- An edge other than `e` and `f` has no end at `v`. -/
theorem not_at_v {g : E} (hge : g ≠ e) (hgf : g ≠ f) : ¬ (N.src g = v ∨ N.dst g = v) := by
  intro h
  rcases T.only g h with h1 | h1
  · exact hge h1
  · exact hgf h1

/-- The edge `e` is at the vertex `z ≠ v` if and only if `z = u`. -/
theorem e_at_iff {z : V} (hz : z ≠ v) : (N.src e = z ∨ N.dst e = z) ↔ z = u := by
  constructor
  · rintro (h | h)
    · rcases T.he with ⟨h1, _⟩ | ⟨h1, _⟩
      · exact h.symm.trans h1
      · exact absurd (h.symm.trans h1) hz
    · rcases T.he with ⟨_, h2⟩ | ⟨_, h2⟩
      · exact absurd (h.symm.trans h2) hz
      · exact h.symm.trans h2
  · intro h
    rw [h]
    exact T.he.at_left

/-- The edge `f` is at the vertex `z ≠ v` if and only if `z = w`. -/
theorem f_at_iff {z : V} (hz : z ≠ v) : (N.src f = z ∨ N.dst f = z) ↔ z = w := by
  constructor
  · rintro (h | h)
    · rcases T.hf with ⟨h1, _⟩ | ⟨h1, _⟩
      · exact absurd (h.symm.trans h1) hz
      · exact h.symm.trans h1
    · rcases T.hf with ⟨_, h2⟩ | ⟨_, h2⟩
      · exact h.symm.trans h2
      · exact absurd (h.symm.trans h2) hz
  · intro h
    rw [h]
    exact T.hf.at_right

end Thread

/-! ### Words -/

/-- The word of `N` that agrees with `y` on the edges other than `f` and takes `f` if and only if
`y` takes `e`. -/
def grow (e f : E) (hef : e ≠ f) (y : {g : E // g ≠ f} → Bit) : E → Bit :=
  fun g => if h : g = f then y ⟨e, hef⟩ else y ⟨g, h⟩

section Words

variable {e f : E} (hef : e ≠ f)

theorem grow_apply_f (y : {g : E // g ≠ f} → Bit) : grow e f hef y f = y ⟨e, hef⟩ := dif_pos rfl

theorem grow_apply_of_ne (y : {g : E // g ≠ f} → Bit) {g : E} (h : g ≠ f) :
    grow e f hef y g = y ⟨g, h⟩ := dif_neg h

theorem grow_apply_e (y : {g : E // g ≠ f} → Bit) : grow e f hef y e = y ⟨e, hef⟩ :=
  grow_apply_of_ne hef y hef

theorem grow_zero : grow e f hef 0 = 0 := by
  funext g
  by_cases h : g = f
  · rw [h, grow_apply_f]
    rfl
  · rw [grow_apply_of_ne hef 0 h]
    rfl

theorem pull_grow (y : {g : E // g ≠ f} → Bit) : pull (fun g => g ≠ f) (grow e f hef y) = y := by
  funext g
  exact grow_apply_of_ne hef y g.2

theorem grow_injective : Function.Injective (grow e f hef) := by
  intro a b h
  rw [← pull_grow hef a, ← pull_grow hef b, h]

/-- A word that takes both edges `e`, `f` or none comes from a word of the new network. -/
theorem grow_pull {x : E → Bit} (hx : x f = x e) :
    grow e f hef (pull (fun g => g ≠ f) x) = x := by
  funext g
  by_cases h : g = f
  · rw [h, grow_apply_f]
    exact hx.symm
  · rw [grow_apply_of_ne hef _ h]
    rfl

theorem grow_add (y z : {g : E // g ≠ f} → Bit) :
    grow e f hef (y + z) = grow e f hef y + grow e f hef z := by
  funext g
  by_cases h : g = f
  · rw [Pi.add_apply, h, grow_apply_f, grow_apply_f, grow_apply_f]
    rfl
  · rw [Pi.add_apply, grow_apply_of_ne hef _ h, grow_apply_of_ne hef _ h,
      grow_apply_of_ne hef _ h]
    rfl

/-- The word `grow y` is a sub-word of `grow z` if and only if `y` is a sub-word of `z`. -/
theorem grow_ne_zero_imp {y z : {g : E // g ≠ f} → Bit} (h : ∀ g, y g ≠ 0 → z g ≠ 0) (g : E)
    (hg : grow e f hef y g ≠ 0) : grow e f hef z g ≠ 0 := by
  by_cases hgf : g = f
  · rw [hgf, grow_apply_f] at hg
    rw [hgf, grow_apply_f]
    exact h _ hg
  · rw [grow_apply_of_ne hef _ hgf] at hg
    rw [grow_apply_of_ne hef _ hgf]
    exact h _ hg

end Words

variable [Fintype V] [Fintype E]

/-- `grow` as a linear map. -/
def growL (e f : E) (hef : e ≠ f) : ({g : E // g ≠ f} → Bit) →ₗ[Bit] (E → Bit) where
  toFun := grow e f hef
  map_add' := grow_add hef
  map_smul' c y := by
    funext g
    show grow e f hef (c • y) g = c • grow e f hef y g
    by_cases h : g = f
    · rw [h, grow_apply_f, grow_apply_f]
      rfl
    · rw [grow_apply_of_ne hef _ h, grow_apply_of_ne hef _ h]
      rfl

namespace Thread

variable {N : Network V E} {e f : E} {u v w : V} (T : Thread N e f u v w)
include T

omit [Fintype V] in
/-- The edge `e` of the new network grows to the two edges `e` and `f`. -/
theorem grow_unitWord_e :
    grow e f T.hef (unitWord (⟨e, T.hef⟩ : {g : E // g ≠ f})) = unitWord e + unitWord f := by
  funext g
  by_cases hgf : g = f
  · rw [hgf, grow_apply_f, Pi.add_apply, unitWord_apply, unitWord_apply, unitWord_apply,
      if_pos rfl, if_neg T.hef, if_pos rfl, zero_add]
  · rw [grow_apply_of_ne T.hef _ hgf, Pi.add_apply, unitWord_apply, unitWord_apply,
      unitWord_apply, if_neg (fun h : f = g => hgf h.symm), add_zero]
    by_cases hge : e = g
    · rw [if_pos (Subtype.ext hge), if_pos hge]
    · rw [if_neg (fun h => hge (congrArg Subtype.val h)), if_neg hge]

omit [Fintype V] in
/-- Every other edge of the new network grows to itself. -/
theorem grow_unitWord_of_ne (g : {g : E // g ≠ f}) (hg : g.1 ≠ e) :
    grow e f T.hef (unitWord g) = unitWord g.1 := by
  funext g'
  by_cases h : g' = f
  · rw [h, grow_apply_f, unitWord_apply, unitWord_apply,
      if_neg (fun k => hg (congrArg Subtype.val k)), if_neg g.2]
  · rw [grow_apply_of_ne T.hef _ h, unitWord_apply, unitWord_apply]
    by_cases hgg : g.1 = g'
    · rw [if_pos (Subtype.ext hgg), if_pos hgg]
    · rw [if_neg (fun k => hgg (congrArg Subtype.val k)), if_neg hgg]

/-- **The boundary.** The boundary of `grow y` in `N` is the boundary of `y` in the new
network. -/
theorem boundary_grow (y : {g : E // g ≠ f} → Bit) :
    N.boundary (grow e f T.hef y) = (N.suppress e f u w T.huw).boundary y := by
  have h : N.boundary.comp (growL e f T.hef) = (N.suppress e f u w T.huw).boundary := by
    apply LinearMap.pi_ext
    intro g c
    rcases bit_cases c with hc | hc
    · rw [hc, Pi.single_zero, map_zero, map_zero]
    · have hu : (Pi.single g c : {g : E // g ≠ f} → Bit) = unitWord g := by
        funext g'
        rw [hc, unitWord_apply, Pi.single_apply]
        by_cases hgg : g' = g
        · rw [if_pos hgg, if_pos hgg.symm]
        · rw [if_neg hgg, if_neg (fun k : g = g' => hgg k.symm)]
      rw [hu, LinearMap.comp_apply]
      show N.boundary (grow e f T.hef (unitWord g)) =
        (N.suppress e f u w T.huw).boundary (unitWord g)
      by_cases hg : g.1 = e
      · have hg' : g = ⟨e, T.hef⟩ := Subtype.ext hg
        rw [hg', T.grow_unitWord_e, map_add, N.boundary_unitWord_of_joins T.he,
          N.boundary_unitWord_of_joins T.hf,
          (N.suppress e f u w T.huw).boundary_unitWord_of_joins
            (N.suppress_joins_of_eq T.huw ⟨e, T.hef⟩ rfl)]
        have hvv : (unitWord v : V → Bit) + unitWord v = 0 := word_add_self _
        calc (unitWord u : V → Bit) + unitWord v + (unitWord v + unitWord w)
            = unitWord u + (unitWord v + unitWord v) + unitWord w := by abel
          _ = unitWord u + unitWord w := by rw [hvv, add_zero]
      · rw [T.grow_unitWord_of_ne g hg, boundary_unit, boundary_unit,
          N.suppress_src_of_ne T.huw g hg, N.suppress_dst_of_ne T.huw g hg]
  exact LinearMap.congr_fun h y

omit [Fintype V] in
/-- The vertex `v` is isolated in the new network. -/
theorem deg_suppress_v (y : {g : E // g ≠ f} → Bit) :
    (N.suppress e f u w T.huw).deg y v = 0 := by
  apply deg_eq_zero_of_forall
  intro g hg
  exfalso
  by_cases hge : g.1 = e
  · rw [N.suppress_src_of_eq T.huw g hge, N.suppress_dst_of_eq T.huw g hge] at hg
    rcases hg with h | h
    · exact T.u_ne_v h
    · exact T.v_ne_w h.symm
  · rw [N.suppress_src_of_ne T.huw g hge, N.suppress_dst_of_ne T.huw g hge] at hg
    exact T.not_at_v hge g.2 hg

/-- A word of `N` that is even at `v` takes both edges `e`, `f` or none. -/
theorem apply_f_eq_of_boundary (x : E → Bit) (hx : N.boundary x v = 0) : x f = x e := by
  have hdecomp : x = grow e f T.hef (pull (fun g => g ≠ f) x) + (x f + x e) • unitWord f := by
    funext g
    by_cases hgf : g = f
    · rw [hgf, Pi.add_apply, grow_apply_f, Pi.smul_apply, unitWord_apply, if_pos rfl,
        smul_eq_mul, mul_one]
      show x f = x e + (x f + x e)
      rw [add_left_comm, bit_add_self, add_zero]
    · rw [Pi.add_apply, grow_apply_of_ne T.hef _ hgf, Pi.smul_apply, unitWord_apply,
        if_neg (fun h : f = g => hgf h.symm), smul_zero, add_zero]
      rfl
  have h2 : N.boundary (unitWord f) v = 1 := by
    rw [N.boundary_unitWord_of_joins T.hf, Pi.add_apply, unitWord_apply, unitWord_apply,
      if_pos rfl, if_neg (fun h : w = v => T.v_ne_w h.symm), add_zero]
  have h1 : N.boundary x v =
      N.boundary (grow e f T.hef (pull (fun g => g ≠ f) x) + (x f + x e) • unitWord f) v := by
    rw [← hdecomp]
  rw [map_add, map_smul, Pi.add_apply, Pi.smul_apply, h2, smul_eq_mul, mul_one,
    T.boundary_grow, hx, boundary_eq_deg, T.deg_suppress_v, Nat.cast_zero, zero_add] at h1
  exact bit_eq_of_add_eq_zero h1.symm

/-- A word of `N` that is even at `v` comes from a word of the new network. -/
theorem grow_pull_of_even {x : E → Bit} (hx : N.boundary x v = 0) :
    grow e f T.hef (pull (fun g => g ≠ f) x) = x :=
  grow_pull T.hef (T.apply_f_eq_of_boundary x hx)

/-- The boundary of the corresponding word of the new network. -/
theorem boundary_pull {x : E → Bit} (hx : N.boundary x v = 0) :
    (N.suppress e f u w T.huw).boundary (pull (fun g => g ≠ f) x) = N.boundary x := by
  rw [← T.boundary_grow, T.grow_pull_of_even hx]

/-! ### Cycles, paths and rank -/

/-- A word of the new network is a cycle if and only if the corresponding word of `N` is a
cycle. -/
theorem isCycleWord_grow_iff (y : {g : E // g ≠ f} → Bit) :
    N.IsCycleWord (grow e f T.hef y) ↔ (N.suppress e f u w T.huw).IsCycleWord y := by
  rw [N.isCycleWord_iff_minimal (grow e f T.hef y),
    (N.suppress e f u w T.huw).isCycleWord_iff_minimal y, T.boundary_grow]
  constructor
  · rintro ⟨h0, hb, hmin⟩
    refine ⟨fun hy => h0 (by rw [hy, grow_zero]), hb, fun z hsub hz => ?_⟩
    have hsub' : N.IsSubword (grow e f T.hef z) (grow e f T.hef y) :=
      grow_ne_zero_imp T.hef hsub
    rcases hmin (grow e f T.hef z) hsub' (by rw [T.boundary_grow]; exact hz) with h | h
    · exact Or.inl (grow_injective T.hef (by rw [h, grow_zero]))
    · exact Or.inr (grow_injective T.hef h)
  · rintro ⟨h0, hb, hmin⟩
    refine ⟨fun hy => h0 (grow_injective T.hef (by rw [hy, grow_zero])), hb,
      fun x hsub hx => ?_⟩
    have hxv : N.boundary x v = 0 := by
      rw [hx]
      rfl
    have hg := T.grow_pull_of_even hxv
    have hsub' : (N.suppress e f u w T.huw).IsSubword (pull (fun g => g ≠ f) x) y := by
      intro g hg'
      have h1 := hsub g.1 hg'
      rwa [grow_apply_of_ne T.hef y g.2] at h1
    have hz : (N.suppress e f u w T.huw).boundary (pull (fun g => g ≠ f) x) = 0 := by
      rw [T.boundary_pull hxv, hx]
    rcases hmin _ hsub' hz with h | h
    · left
      rw [← hg, h, grow_zero]
    · right
      rw [← hg, h]

/-- A word of the new network is a path from `s` to `t` if and only if the corresponding word of
`N` is one. -/
theorem isPathWord_grow_iff (s t : V) (y : {g : E // g ≠ f} → Bit) :
    N.IsPathWord s t (grow e f T.hef y) ↔ (N.suppress e f u w T.huw).IsPathWord s t y := by
  rw [N.isPathWord_iff_minimal s t (grow e f T.hef y),
    (N.suppress e f u w T.huw).isPathWord_iff_minimal s t y, T.boundary_grow]
  constructor
  · rintro ⟨hst, hb, hmin⟩
    refine ⟨hst, hb, fun z hsub hz => ?_⟩
    have hsub' : N.IsSubword (grow e f T.hef z) (grow e f T.hef y) :=
      grow_ne_zero_imp T.hef hsub
    have h := hmin (grow e f T.hef z) hsub' (by rw [T.boundary_grow]; exact hz)
    exact grow_injective T.hef (by rw [h, grow_zero])
  · rintro ⟨hst, hb, hmin⟩
    refine ⟨hst, hb, fun x hsub hx => ?_⟩
    have hxv : N.boundary x v = 0 := by
      rw [hx]
      rfl
    have hg := T.grow_pull_of_even hxv
    have hsub' : (N.suppress e f u w T.huw).IsSubword (pull (fun g => g ≠ f) x) y := by
      intro g hg'
      have h1 := hsub g.1 hg'
      rwa [grow_apply_of_ne T.hef y g.2] at h1
    have hz : (N.suppress e f u w T.huw).boundary (pull (fun g => g ≠ f) x) = 0 := by
      rw [T.boundary_pull hxv, hx]
    rw [← hg, hmin _ hsub' hz, grow_zero]

/-- **The new network has the same number of cycles.** -/
theorem numCycles_suppress : (N.suppress e f u w T.huw).numCycles = N.numCycles := by
  obtain ⟨φ, hφ⟩ : ∃ φ : {y : (N.suppress e f u w T.huw).Word //
      (N.suppress e f u w T.huw).IsCycleWord y} → {x : N.Word // N.IsCycleWord x},
      ∀ y, (φ y).1 = grow e f T.hef y.1 :=
    ⟨fun y => ⟨grow e f T.hef y.1, (T.isCycleWord_grow_iff y.1).2 y.2⟩, fun _ => rfl⟩
  have hbij : Function.Bijective φ := by
    constructor
    · intro a b hab
      have h1 : grow e f T.hef a.1 = grow e f T.hef b.1 := by rw [← hφ a, ← hφ b, hab]
      exact Subtype.ext (grow_injective T.hef h1)
    · intro x
      have hxv : N.boundary x.1 v = 0 := by
        rw [x.2.boundary_eq_zero]
        rfl
      have hg := T.grow_pull_of_even hxv
      have hc : N.IsCycleWord (grow e f T.hef (pull (fun g => g ≠ f) x.1)) := by
        rw [hg]
        exact x.2
      refine ⟨⟨pull (fun g => g ≠ f) x.1, (T.isCycleWord_grow_iff _).1 hc⟩, ?_⟩
      apply Subtype.ext
      rw [hφ]
      exact hg
  exact Nat.card_eq_of_bijective φ hbij

/-- **The new network has the same number of paths** between two vertices other than `v`. -/
theorem numPaths_suppress {s t : V} (hs : s ≠ v) (ht : t ≠ v) :
    (N.suppress e f u w T.huw).numPaths s t = N.numPaths s t := by
  obtain ⟨φ, hφ⟩ : ∃ φ : {y : (N.suppress e f u w T.huw).Word //
      (N.suppress e f u w T.huw).IsPathWord s t y} → {x : N.Word // N.IsPathWord s t x},
      ∀ y, (φ y).1 = grow e f T.hef y.1 :=
    ⟨fun y => ⟨grow e f T.hef y.1, (T.isPathWord_grow_iff s t y.1).2 y.2⟩, fun _ => rfl⟩
  have hbij : Function.Bijective φ := by
    constructor
    · intro a b hab
      have h1 : grow e f T.hef a.1 = grow e f T.hef b.1 := by rw [← hφ a, ← hφ b, hab]
      exact Subtype.ext (grow_injective T.hef h1)
    · intro x
      have hxv : N.boundary x.1 v = 0 := by
        rw [x.2.boundary_eq]
        unfold pathDemand
        rw [Pi.add_apply, Pi.single_eq_of_ne (Ne.symm hs), Pi.single_eq_of_ne (Ne.symm ht),
          add_zero]
      have hg := T.grow_pull_of_even hxv
      have hc : N.IsPathWord s t (grow e f T.hef (pull (fun g => g ≠ f) x.1)) := by
        rw [hg]
        exact x.2
      refine ⟨⟨pull (fun g => g ≠ f) x.1, (T.isPathWord_grow_iff s t _).1 hc⟩, ?_⟩
      apply Subtype.ext
      rw [hφ]
      exact hg
  exact Nat.card_eq_of_bijective φ hbij

/-- **The new network has the same rank.** -/
theorem networkRank_suppress : networkRank (N.suppress e f u w T.huw) = networkRank N := by
  obtain ⟨φ, hφ⟩ : ∃ φ : (N.suppress e f u w T.huw).CycleSpace → N.CycleSpace,
      ∀ y, (φ y).1 = grow e f T.hef y.1 :=
    ⟨fun y => ⟨grow e f T.hef y.1, LinearMap.mem_ker.2
      (by rw [T.boundary_grow]; exact LinearMap.mem_ker.1 y.2)⟩, fun _ => rfl⟩
  have hbij : Function.Bijective φ := by
    constructor
    · intro a b hab
      have h1 : grow e f T.hef a.1 = grow e f T.hef b.1 := by rw [← hφ a, ← hφ b, hab]
      exact Subtype.ext (grow_injective T.hef h1)
    · intro x
      have hx : N.boundary x.1 = 0 := LinearMap.mem_ker.1 x.2
      have hxv : N.boundary x.1 v = 0 := by
        rw [hx]
        rfl
      have hg := T.grow_pull_of_even hxv
      have hz : (N.suppress e f u w T.huw).boundary (pull (fun g => g ≠ f) x.1) = 0 := by
        rw [T.boundary_pull hxv, hx]
      refine ⟨⟨pull (fun g => g ≠ f) x.1, LinearMap.mem_ker.2 hz⟩, ?_⟩
      apply Subtype.ext
      rw [hφ]
      exact hg
  have h1 := Fintype.card_of_bijective hbij
  rw [cycleSpace_card_network, cycleSpace_card_network] at h1
  exact Nat.pow_right_injective (le_refl 2) h1

/-! ### Degrees and connections -/

omit [Fintype V] in
/-- **Every vertex other than `v` keeps its degree.** -/
theorem deg_suppress {z : V} (hz : z ≠ v) :
    (N.suppress e f u w T.huw).deg (fun _ => 1) z = N.deg (fun _ => 1) z := by
  -- the edge `e` of the new network stands for `f` at `w` and for `e` at `u`
  obtain ⟨i, hi_pos, hi_neg⟩ : ∃ i : {g : E // g ≠ f} → E,
      (∀ g, (g.1 = e ∧ z = w) → i g = f) ∧ (∀ g, ¬ (g.1 = e ∧ z = w) → i g = g.1) :=
    ⟨fun g => if g.1 = e ∧ z = w then f else g.1, fun _ h => if_pos h, fun _ h => if_neg h⟩
  unfold deg
  apply Finset.card_bij (fun g _ => i g)
  · intro g hg
    show i g ∈ Finset.univ.filter _
    rw [Finset.mem_filter] at hg ⊢
    refine ⟨Finset.mem_univ _, one_ne_zero, ?_⟩
    have hat := hg.2.2
    by_cases hge : g.1 = e
    · rw [N.suppress_src_of_eq T.huw g hge, N.suppress_dst_of_eq T.huw g hge] at hat
      by_cases hzw : z = w
      · rw [hi_pos g ⟨hge, hzw⟩]
        exact (T.f_at_iff hz).2 hzw
      · rw [hi_neg g (fun h => hzw h.2), hge]
        rcases hat with h | h
        · exact (T.e_at_iff hz).2 h.symm
        · exact absurd h.symm hzw
    · rw [hi_neg g (fun h => hge h.1)]
      rwa [N.suppress_src_of_ne T.huw g hge, N.suppress_dst_of_ne T.huw g hge] at hat
  · intro g₁ _ g₂ _ h
    have h' : i g₁ = i g₂ := h
    by_cases h1 : g₁.1 = e ∧ z = w
    · rw [hi_pos g₁ h1] at h'
      by_cases h2 : g₂.1 = e ∧ z = w
      · exact Subtype.ext (h1.1.trans h2.1.symm)
      · rw [hi_neg g₂ h2] at h'
        exact absurd h'.symm g₂.2
    · rw [hi_neg g₁ h1] at h'
      by_cases h2 : g₂.1 = e ∧ z = w
      · rw [hi_pos g₂ h2] at h'
        exact absurd h' g₁.2
      · rw [hi_neg g₂ h2] at h'
        exact Subtype.ext h'
  · intro g hg
    rw [Finset.mem_filter] at hg
    have hat := hg.2.2
    by_cases hgf : g = f
    · have hzw : z = w := (T.f_at_iff hz).1 (by rw [← hgf]; exact hat)
      refine ⟨⟨e, T.hef⟩, ?_, ?_⟩
      · rw [Finset.mem_filter]
        refine ⟨Finset.mem_univ _, one_ne_zero, Or.inr ?_⟩
        rw [N.suppress_dst_of_eq T.huw ⟨e, T.hef⟩ rfl, hzw]
      · show i ⟨e, T.hef⟩ = g
        rw [hi_pos ⟨e, T.hef⟩ ⟨rfl, hzw⟩, hgf]
    · by_cases hge : g = e
      · have hzu : z = u := (T.e_at_iff hz).1 (by rw [← hge]; exact hat)
        have hzw : z ≠ w := by
          rw [hzu]
          exact T.huw
        refine ⟨⟨e, T.hef⟩, ?_, ?_⟩
        · rw [Finset.mem_filter]
          refine ⟨Finset.mem_univ _, one_ne_zero, Or.inl ?_⟩
          rw [N.suppress_src_of_eq T.huw ⟨e, T.hef⟩ rfl, hzu]
        · show i ⟨e, T.hef⟩ = g
          rw [hi_neg ⟨e, T.hef⟩ (fun h => hzw h.2), hge]
      · refine ⟨⟨g, hgf⟩, ?_, ?_⟩
        · rw [Finset.mem_filter]
          refine ⟨Finset.mem_univ _, one_ne_zero, ?_⟩
          rw [N.suppress_src_of_ne T.huw ⟨g, hgf⟩ hge, N.suppress_dst_of_ne T.huw ⟨g, hgf⟩ hge]
          exact hat
        · show i ⟨g, hgf⟩ = g
          rw [hi_neg ⟨g, hgf⟩ (fun h => hge h.1)]

omit [Fintype V] [Fintype E] in
/-- **Connections.** Two vertices other than `v` that are joined in `N` are joined in the new
network. -/
theorem reachable_suppress {a b : V} (ha : a ≠ v) (hb : b ≠ v) (h : N.graph.Reachable a b) :
    (N.suppress e f u w T.huw).graph.Reachable a b := by
  -- an edge of the new network joins vertices with the same connection to `a`
  have hadj : ∀ (g : {g : E // g ≠ f}) (x y : V), (N.suppress e f u w T.huw).Joins g x y →
      ((N.suppress e f u w T.huw).graph.Reachable a x ↔
        (N.suppress e f u w T.huw).graph.Reachable a y) := by
    intro g x y hj
    have h1 : (N.suppress e f u w T.huw).graph.Adj x y := ⟨g, hj⟩
    exact ⟨fun k => k.trans h1.reachable, fun k => k.trans h1.symm.reachable⟩
  have huw' : (N.suppress e f u w T.huw).graph.Reachable a u ↔
      (N.suppress e f u w T.huw).graph.Reachable a w :=
    hadj ⟨e, T.hef⟩ u w (N.suppress_joins_of_eq T.huw ⟨e, T.hef⟩ rfl)
  -- the vertices that the new network joins to `a`, with `u` in the place of `v`
  obtain ⟨D, hD⟩ : ∃ D : V → Prop, ∀ z, D z ↔
      (N.suppress e f u w T.huw).graph.Reachable a (if z = v then u else z) :=
    ⟨_, fun _ => Iff.rfl⟩
  have hDv : D v ↔ (N.suppress e f u w T.huw).graph.Reachable a u := by
    rw [hD, if_pos rfl]
  have hDz : ∀ z, z ≠ v → (D z ↔ (N.suppress e f u w T.huw).graph.Reachable a z) := by
    intro z hz
    rw [hD, if_neg hz]
  have hclosed : ∀ g, D (N.src g) ↔ D (N.dst g) := by
    intro g
    by_cases hgf : g = f
    · rcases T.hf with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · rw [hgf, h1, h2, hDv, hDz w (Ne.symm T.v_ne_w)]
        exact huw'
      · rw [hgf, h1, h2, hDv, hDz w (Ne.symm T.v_ne_w)]
        exact huw'.symm
    · by_cases hge : g = e
      · rcases T.he with ⟨h1, h2⟩ | ⟨h1, h2⟩
        · rw [hge, h1, h2, hDv, hDz u T.u_ne_v]
        · rw [hge, h1, h2, hDv, hDz u T.u_ne_v]
      · have hnot := T.not_at_v hge hgf
        rw [hDz _ (fun k => hnot (Or.inl k)), hDz _ (fun k => hnot (Or.inr k))]
        exact hadj ⟨g, hgf⟩ _ _ ((N.suppress_joins_of_ne T.huw ⟨g, hgf⟩ hge _ _).2
          (Or.inl ⟨rfl, rfl⟩))
  have hDb := N.mem_of_reachable_of_closed D hclosed h ((hDz a ha).2 (SimpleGraph.Reachable.refl a))
  exact (hDz b hb).1 hDb

end Thread

end Erdos1016.BoundaryTrace.Network
