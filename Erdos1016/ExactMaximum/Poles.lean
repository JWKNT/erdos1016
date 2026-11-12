import Erdos1016.ExactMaximum.NetSmallCut

set_option autoImplicit false

/-!
# Poles, and the sides of a smallest cyclic cut

In the paper "The maximum number of cycles in a graph of large rank" a pole is a connected
multigraph without loops in which every vertex has degree two or three, and its ports are the
vertices of degree two. A side of a cut is a network on all vertices of the graph, so the vertices
of the other side are isolated in it. This file therefore uses poles with isolated vertices
(`IsWeakPole`).

It proves that the two sides of a smallest cyclic cut of a cubic network are such poles
(`isWeakPole_inside`), and that the ends of the crossing edges are ports (`isPort_inside`).
The second side of the cut `S` is the first side of the cut of the complement of `S`, so the
statements hold for it too.
-/

noncomputable section
open scoped BigOperators

namespace Erdos1016.BoundaryTrace.Network

open BoundaryDecay

local instance polesDecidable (p : Prop) : Decidable p := Classical.propDecidable p

variable {V E : Type*} [Fintype V] [Fintype E]

/-- A pole, possibly with isolated vertices: every vertex has degree zero, two or three, and any
two vertices of positive degree are joined. -/
def IsWeakPole (N : Network V E) : Prop :=
  (∀ v, N.deg (fun _ => 1) v = 0 ∨ N.deg (fun _ => 1) v = 2 ∨ N.deg (fun _ => 1) v = 3) ∧
    ∀ u v, 0 < N.deg (fun _ => 1) u → 0 < N.deg (fun _ => 1) v → N.graph.Reachable u v

/-- A port: a vertex of degree two. -/
def IsPort (N : Network V E) (v : V) : Prop := N.deg (fun _ => 1) v = 2

/-! ### The degrees in a side -/

omit [Fintype V] in
/-- The degree in a part is the number of the edges of the part at the vertex. -/
theorem deg_sub_ones (N : Network V E) (p : E → Prop) [Fintype {e : E // p e}] (v : V) :
    (N.sub p).deg (fun _ => 1) v = N.deg (restrict (fun _ => 1) p) v := by
  have h : extend p (fun _ => (1 : Bit)) = restrict (fun _ => 1) p := by
    funext e
    by_cases hp : p e
    · rw [extend_apply_of_pos p _ hp, restrict_apply_of_pos _ hp]
    · rw [extend_apply_of_neg p _ hp, restrict_apply_of_neg _ hp]
  rw [← N.deg_extend p (fun _ => 1) v, h]

omit [Fintype V] in
/-- The degree of a vertex is the sum of its degrees in the edges inside, outside and across. -/
theorem deg_split (N : Network V E) (S : V → Prop) (v : V) :
    N.deg (fun _ => 1) v =
      N.deg (restrict (fun _ => 1) (N.inside S)) v +
        N.deg (restrict (fun _ => 1) (N.outside S)) v +
        N.deg (restrict (fun _ => 1) (N.crosses S)) v := by
  have h := N.restrict_add_restrict_add_restrict S (fun _ => (1 : Bit))
  have d1 : ∀ e, restrict (fun _ => (1 : Bit)) (N.inside S) e ≠ 0 →
      restrict (fun _ => (1 : Bit)) (N.outside S) e = 0 := fun e he =>
    restrict_apply_of_neg _ (N.not_outside_of_inside ((restrict_ne_zero_iff _ _ e).1 he).1)
  have d2 : ∀ e, (restrict (fun _ => (1 : Bit)) (N.inside S) +
      restrict (fun _ => (1 : Bit)) (N.outside S)) e ≠ 0 →
      restrict (fun _ => (1 : Bit)) (N.crosses S) e = 0 := by
    intro e he
    apply restrict_apply_of_neg
    intro hc
    apply he
    show restrict (fun _ => (1 : Bit)) (N.inside S) e +
      restrict (fun _ => (1 : Bit)) (N.outside S) e = 0
    rw [restrict_apply_of_neg _ (N.not_inside_of_crosses hc),
      restrict_apply_of_neg _ (N.not_outside_of_crosses hc), add_zero]
  rw [← N.deg_add_of_disjoint d1 v, ← N.deg_add_of_disjoint d2 v, h]

omit [Fintype V] in
/-- A vertex of `S` is on no edge of the second side. -/
theorem deg_outside_eq_zero (N : Network V E) (S : V → Prop) {v : V} (hv : S v) :
    N.deg (restrict (fun _ => 1) (N.outside S)) v = 0 := by
  apply N.deg_eq_zero_of_forall
  intro g hg
  apply restrict_apply_of_neg
  intro ho
  rcases hg with hg | hg
  · exact ho.1 (by rw [hg]; exact hv)
  · exact ho.2 (by rw [hg]; exact hv)

omit [Fintype V] in
/-- A vertex outside `S` is on no edge of the first side. -/
theorem deg_inside_eq_zero (N : Network V E) (S : V → Prop) {v : V} (hv : ¬ S v) :
    N.deg (restrict (fun _ => 1) (N.inside S)) v = 0 := by
  apply N.deg_eq_zero_of_forall
  intro g hg
  apply restrict_apply_of_neg
  intro hi
  rcases hg with hg | hg
  · exact hv (by rw [← hg]; exact hi.1)
  · exact hv (by rw [← hg]; exact hi.2)

/-- **At most one crossing edge at a vertex.** In a cubic network, let `S` be a smallest cyclic
cut, with `d ≤ 3` crossing edges. Then a vertex of `S` is on at most one crossing edge. -/
theorem crossDeg_le_one (N : Network V E) (hcubic : N.IsCubic) {d : ℕ} (hd : d ≤ 3)
    (hmin : ∀ S : V → Prop, N.IsCyclicCut S → d ≤ N.cutSize S) (S : V → Prop)
    (hS : N.cutSize S = d) (hcyc : 0 < (N.sub (N.inside S)).numCycles) {v : V} (hv : S v) :
    N.deg (restrict (fun _ => 1) (N.crosses S)) v ≤ 1 := by
  refine Nat.le_of_not_lt fun h1 => ?_
  have h1' : 1 < (Finset.univ.filter fun g : E =>
      restrict (fun _ => (1 : Bit)) (N.crosses S) g ≠ 0 ∧ (N.src g = v ∨ N.dst g = v)).card :=
    h1
  obtain ⟨a, ha, b, hb, hab⟩ := Finset.one_lt_card.1 h1'
  have ha := (Finset.mem_filter.1 ha).2
  have hb := (Finset.mem_filter.1 hb).2
  have hca : N.crosses S a := ((restrict_ne_zero_iff _ _ a).1 ha.1).1
  have hcb : N.crosses S b := ((restrict_ne_zero_iff _ _ b).1 hb.1).1
  obtain ⟨wa, hwa⟩ := N.exists_joins ha.2
  obtain ⟨wb, hwb⟩ := N.exists_joins hb.2
  -- the other end of a crossing edge at `v` is not in `S`
  have hother : ∀ (g : E) (w : V), N.crosses S g → N.Joins g v w → ¬ S w := by
    intro g w hc hj hw
    apply hc
    rcases hj with ⟨k1, k2⟩ | ⟨k1, k2⟩
    · rw [k1, k2]
      exact ⟨fun _ => hw, fun _ => hv⟩
    · rw [k1, k2]
      exact ⟨fun _ => hv, fun _ => hw⟩
  exact N.false_of_two_crossing_at hcubic hd hmin S hS hcyc hab hwa hwb hv
    (hother a wa hca hwa) (hother b wb hcb hwb)

omit [Fintype V] in
/-- The degree of a vertex of `S` in the first side, in a cubic network: three minus the number
of crossing edges at the vertex. -/
theorem deg_inside_add (N : Network V E) (hcubic : N.IsCubic) (S : V → Prop) {v : V}
    (hv : S v) :
    (N.sub (N.inside S)).deg (fun _ => 1) v + N.deg (restrict (fun _ => 1) (N.crosses S)) v =
      3 := by
  have h1 := N.deg_split S v
  rw [hcubic v, N.deg_outside_eq_zero S hv, add_zero] at h1
  rw [N.deg_sub_ones (N.inside S) v]
  exact h1.symm

/-- **A side of a smallest cyclic cut is a pole.** In a cubic network, let `1 ≤ d ≤ 3`, let every
cyclic cut have at least `d` crossing edges, and let the cut `S` have exactly `d` crossing edges
and a cycle in its first side. Then the first side is a pole, possibly with isolated vertices. -/
theorem isWeakPole_inside (N : Network V E) (hcubic : N.IsCubic) {d : ℕ} (hd : d ≤ 3)
    (hd1 : 1 ≤ d) (hmin : ∀ S : V → Prop, N.IsCyclicCut S → d ≤ N.cutSize S) (S : V → Prop)
    (hS : N.cutSize S = d) (hcyc : 0 < (N.sub (N.inside S)).numCycles) {s₀ t₀ : V}
    (hs₀ : S s₀) (ht₀ : ¬ S t₀) : (N.sub (N.inside S)).IsWeakPole := by
  have hzero : ∀ v, ¬ S v → (N.sub (N.inside S)).deg (fun _ => 1) v = 0 := by
    intro v hv
    rw [N.deg_sub_ones (N.inside S) v]
    exact N.deg_inside_eq_zero S hv
  constructor
  · intro v
    by_cases hv : S v
    · have h1 := N.deg_inside_add hcubic S hv
      have h2 := N.crossDeg_le_one hcubic hd hmin S hS hcyc hv
      omega
    · exact Or.inl (hzero v hv)
  · intro u v hu hv
    have hSu : S u := Classical.not_not.1 fun h => by
      have := hzero u h
      omega
    have hSv : S v := Classical.not_not.1 fun h => by
      have := hzero v h
      omega
    have hr := N.reachable_inside_of_minimal hcubic hd hd1 hmin S hS hs₀ ht₀
    exact (hr u hSu).symm.trans (hr v hSv)

/-- **The ends of the crossing edges are ports.** In the setting of `isWeakPole_inside`, let the
edge `e` join `s ∈ S` and `t ∉ S`. Then `s` has degree two in the first side. -/
theorem isPort_inside (N : Network V E) (hcubic : N.IsCubic) {d : ℕ} (hd : d ≤ 3)
    (hmin : ∀ S : V → Prop, N.IsCyclicCut S → d ≤ N.cutSize S) (S : V → Prop)
    (hS : N.cutSize S = d) (hcyc : 0 < (N.sub (N.inside S)).numCycles) {e : E} {s t : V}
    (he : N.Joins e s t) (hs : S s) (ht : ¬ S t) : (N.sub (N.inside S)).IsPort s := by
  have h1 := N.deg_inside_add hcubic S hs
  have h2 := N.crossDeg_le_one hcubic hd hmin S hS hcyc hs
  have h3 : 0 < N.deg (restrict (fun _ => 1) (N.crosses S)) s := by
    have hne : restrict (fun _ => (1 : Bit)) (N.crosses S) e ≠ 0 := by
      rw [restrict_apply_of_pos _ (N.crosses_of_joins he hs ht)]
      exact one_ne_zero
    rcases he.at_left with h | h
    · rw [← h]
      exact N.deg_src_pos hne
    · rw [← h]
      exact N.deg_dst_pos hne
  unfold IsPort
  omega

end Erdos1016.BoundaryTrace.Network
