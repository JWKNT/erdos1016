import Erdos1016.ExactMaximum.ThreeCut

set_option autoImplicit false

/-!
# A cut with one crossing edge

Let `e` be the only edge that crosses the cut `S` of the network `N`. This file proves the facts
that Lemma 5.2 (b) of the paper "The maximum number of cycles in a graph of large rank" uses for
a bridge:

* an even word does not take `e`, a join of two vertices of `S` does not take `e`, and a join of
  a vertex of `S` and a vertex outside `S` takes `e`;
* the rank of `N` is the sum of the ranks of the two sides (`networkRank_of_one_crossing`);
* the number of paths from `a ∈ S` to `b ∉ S` is the product of the numbers of paths of the two
  sides to the ends of `e` (`numPaths_of_one_crossing`);
* if every vertex has degree zero or at least two, both sides have positive rank
  (`rank_side_pos_of_one_crossing`);
* then at most half of the possible paths join two vertices of the same side
  (`two_mul_numPaths_le_of_same_side`), and the same holds for a vertex of degree two on `e` and
  a vertex of the other side (`two_mul_numPaths_le_of_bridge_at`).
-/

noncomputable section
open scoped BigOperators

namespace Erdos1016.BoundaryTrace.Network

open BoundaryDecay

local instance netBridgeCutDecidable (p : Prop) : Decidable p := Classical.propDecidable p

variable {V E : Type*} [Fintype V] [Fintype E]

/-! ### Parity at the crossing edge -/

/-- The value of a word at the only crossing edge is the sum of its boundary over `S`. -/
theorem sum_boundary_of_one_crossing (N : Network V E) (S : V → Prop) {e : E}
    (hC : ∀ g, N.crosses S g → g = e) (hce : N.crosses S e) (x : N.Word) :
    (∑ v, if S v then N.boundary x v else 0) = x e := by
  rw [N.cut_parity S x,
    Finset.sum_eq_single e (fun g _ hg => if_neg (fun h => hg (hC g h)))
      (fun h => absurd (Finset.mem_univ e) h), if_pos hce]

/-- An even word does not take the only crossing edge. -/
theorem eq_zero_of_even_of_one_crossing (N : Network V E) (S : V → Prop) {e : E}
    (hC : ∀ g, N.crosses S g → g = e) (hce : N.crosses S e) {x : N.Word}
    (hx : N.boundary x = 0) : x e = 0 := by
  rw [← N.sum_boundary_of_one_crossing S hC hce x]
  apply Finset.sum_eq_zero
  intro v _
  by_cases hS : S v
  · rw [if_pos hS, hx]
    rfl
  · rw [if_neg hS]

omit [Fintype E] in
/-- The sum over `S` of the parity pattern of a path. -/
theorem sum_pathDemand (N : Network V E) (S : V → Prop) (a b : V) :
    (∑ v, if S v then N.pathDemand a b v else 0) =
      (if S a then (1 : Bit) else 0) + (if S b then (1 : Bit) else 0) := by
  have key : ∀ u : V, (∑ v, if S v then (if u = v then (1 : Bit) else 0) else 0) =
      if S u then (1 : Bit) else 0 := fun u => sum_ite_eq_ite S 1 u
  have h1 : ∀ v, (if S v then N.pathDemand a b v else 0) =
      (if S v then (if a = v then (1 : Bit) else 0) else 0) +
        (if S v then (if b = v then (1 : Bit) else 0) else 0) := by
    intro v
    by_cases hS : S v
    · rw [if_pos hS, if_pos hS, if_pos hS]
      show (unitWord a + unitWord b : V → Bit) v = _
      rw [Pi.add_apply, unitWord_apply, unitWord_apply]
    · rw [if_neg hS, if_neg hS, if_neg hS, add_zero]
  rw [Finset.sum_congr rfl (fun v _ => h1 v), Finset.sum_add_distrib, key a, key b]

/-- A join of two vertices of `S` does not take the only crossing edge. -/
theorem eq_zero_of_join_same_side (N : Network V E) (S : V → Prop) {e : E}
    (hC : ∀ g, N.crosses S g → g = e) (hce : N.crosses S e) {a b : V} (ha : S a) (hb : S b)
    {R : N.Word} (hR : N.boundary R = N.pathDemand a b) : R e = 0 := by
  rw [← N.sum_boundary_of_one_crossing S hC hce R, hR, N.sum_pathDemand S a b, if_pos ha,
    if_pos hb]
  exact bit_add_self 1

/-- A join of a vertex of `S` and a vertex outside `S` takes the only crossing edge. -/
theorem eq_one_of_join_across (N : Network V E) (S : V → Prop) {e : E}
    (hC : ∀ g, N.crosses S g → g = e) (hce : N.crosses S e) {a b : V} (ha : S a) (hb : ¬ S b)
    {R : N.Word} (hR : N.boundary R = N.pathDemand a b) : R e = 1 := by
  rw [← N.sum_boundary_of_one_crossing S hC hce R, hR, N.sum_pathDemand S a b, if_pos ha,
    if_neg hb, add_zero]

/-! ### The rank -/

/-- The number of even words is two to the rank. -/
theorem natCard_even (N : Network V E) :
    Nat.card {x : N.Word // N.boundary x = 0} = 2 ^ networkRank N := by
  rw [← cycleSpace_card_network, ← Nat.card_eq_fintype_card]
  exact Nat.card_congr (Equiv.subtypeEquivRight fun _ => LinearMap.mem_ker.symm)

/-- **The rank of a network with a cut of one edge** is the sum of the ranks of the sides. -/
theorem networkRank_of_one_crossing (N : Network V E) (S : V → Prop) {e : E}
    (hC : ∀ g, N.crosses S g → g = e) (hce : N.crosses S e) :
    networkRank N = networkRank (N.sub (N.inside S)) + networkRank (N.sub (N.outside S)) := by
  obtain ⟨φ, hφ⟩ : ∃ φ : {P : N.Word // N.boundary P = 0 ∧ Within P (N.inside S)} ×
      {Q : N.Word // N.boundary Q = 0 ∧ Within Q (N.outside S)} →
      {x : N.Word // N.boundary x = 0}, ∀ z, (φ z).1 = z.1.1 + z.2.1 :=
    ⟨fun z => ⟨z.1.1 + z.2.1, by rw [map_add, z.1.2.1, z.2.2.1, add_zero]⟩, fun _ => rfl⟩
  have hbij : Function.Bijective φ := by
    constructor
    · intro z z' h
      have h1 : z.1.1 + z.2.1 = z'.1.1 + z'.2.1 := by rw [← hφ z, ← hφ z', h]
      have hP : z.1.1 = z'.1.1 := by
        have h2 : restrict (z.1.1 + z.2.1) (N.inside S) =
            restrict (z'.1.1 + z'.2.1) (N.inside S) := by rw [h1]
        rw [restrict_add, restrict_add, restrict_eq_self z.1.2.2, restrict_eq_self z'.1.2.2,
          restrict_eq_zero (N.inside S) z.2.2.2 (fun g hg => N.not_inside_of_outside hg),
          restrict_eq_zero (N.inside S) z'.2.2.2 (fun g hg => N.not_inside_of_outside hg),
          add_zero, add_zero] at h2
        exact h2
      have hQ : z.2.1 = z'.2.1 := by
        have h2 : restrict (z.1.1 + z.2.1) (N.outside S) =
            restrict (z'.1.1 + z'.2.1) (N.outside S) := by rw [h1]
        rw [restrict_add, restrict_add, restrict_eq_self z.2.2.2, restrict_eq_self z'.2.2.2,
          restrict_eq_zero (N.outside S) z.1.2.2 (fun g hg => N.not_outside_of_inside hg),
          restrict_eq_zero (N.outside S) z'.1.2.2 (fun g hg => N.not_outside_of_inside hg),
          zero_add, zero_add] at h2
        exact h2
      exact Prod.ext (Subtype.ext hP) (Subtype.ext hQ)
    · intro x
      have hxe : x.1 e = 0 := N.eq_zero_of_even_of_one_crossing S hC hce x.2
      have hcross : restrict x.1 (N.crosses S) = 0 := by
        funext g
        by_cases hg : N.crosses S g
        · rw [restrict_apply_of_pos x.1 hg, hC g hg]
          exact hxe
        · exact restrict_apply_of_neg x.1 hg
      have hsum : restrict x.1 (N.inside S) + restrict x.1 (N.outside S) = x.1 := by
        have h := N.restrict_add_restrict_add_restrict S x.1
        rw [hcross, add_zero] at h
        exact h
      have hb : N.boundary (restrict x.1 (N.inside S)) +
          N.boundary (restrict x.1 (N.outside S)) = (0 : N.Demand) + 0 := by
        rw [← map_add, hsum, x.2, add_zero]
      obtain ⟨hbP, hbQ⟩ := N.boundary_split (within_restrict x.1 (N.inside S))
        (within_restrict x.1 (N.outside S)) (fun _ _ => rfl) (fun _ _ => rfl) hb
      refine ⟨(⟨restrict x.1 (N.inside S), hbP, within_restrict _ _⟩,
        ⟨restrict x.1 (N.outside S), hbQ, within_restrict _ _⟩), ?_⟩
      apply Subtype.ext
      rw [hφ]
      exact hsum
  have hcard := Nat.card_eq_of_bijective φ hbij
  rw [Nat.card_prod, N.natCard_even_within (N.inside S), N.natCard_even_within (N.outside S),
    N.natCard_even, ← pow_add] at hcard
  exact (Nat.pow_right_injective (le_refl 2) hcard).symm

/-! ### Paths across the cut -/

/-- **Paths across a cut of one edge.** Let the only crossing edge `e` join `x ∈ S` and `y ∉ S`,
and let `a ∈ S` and `b ∉ S` be other vertices. Then the number of paths from `a` to `b` is the
number of paths from `a` to `x` in the first side times the number of paths from `y` to `b` in
the second side. -/
theorem numPaths_of_one_crossing (N : Network V E) (S : V → Prop) {e : E} {x y a b : V}
    (he : N.Joins e x y) (hx : S x) (hy : ¬ S y) (hC : ∀ g, N.crosses S g → g = e) (ha : S a)
    (hb : ¬ S b) (hax : a ≠ x) (hyb : y ≠ b) :
    N.numPaths a b =
      (N.sub (N.inside S)).numPaths a x * (N.sub (N.outside S)).numPaths y b := by
  have hce : N.crosses S e := N.crosses_of_joins he hx hy
  rw [numPaths_sub, numPaths_sub, ← Nat.card_prod]
  symm
  obtain ⟨φ, hφ⟩ : ∃ φ : {P : N.Word // N.IsPathWord a x P ∧ Within P (N.inside S)} ×
      {Q : N.Word // N.IsPathWord y b Q ∧ Within Q (N.outside S)} →
      {R : N.Word // N.IsPathWord a b R}, ∀ z, (φ z).1 = z.1.1 + z.2.1 + unitWord e :=
    ⟨fun z => ⟨z.1.1 + z.2.1 + unitWord e,
      N.isPathWord_glue S he hx hy z.1.2.1 z.1.2.2 z.2.2.1 z.2.2.2⟩, fun _ => rfl⟩
  have hbij : Function.Bijective φ := by
    constructor
    · intro z z' h
      have h0 : z.1.1 + z.2.1 + unitWord e = z'.1.1 + z'.2.1 + unitWord e := by
        rw [← hφ z, ← hφ z', h]
      have h1 : z.1.1 + z.2.1 = z'.1.1 + z'.2.1 := add_right_cancel h0
      have hP : z.1.1 = z'.1.1 := by
        have h2 : restrict (z.1.1 + z.2.1) (N.inside S) =
            restrict (z'.1.1 + z'.2.1) (N.inside S) := by rw [h1]
        rw [restrict_add, restrict_add, restrict_eq_self z.1.2.2, restrict_eq_self z'.1.2.2,
          restrict_eq_zero (N.inside S) z.2.2.2 (fun g hg => N.not_inside_of_outside hg),
          restrict_eq_zero (N.inside S) z'.2.2.2 (fun g hg => N.not_inside_of_outside hg),
          add_zero, add_zero] at h2
        exact h2
      have hQ : z.2.1 = z'.2.1 := by
        have h2 : restrict (z.1.1 + z.2.1) (N.outside S) =
            restrict (z'.1.1 + z'.2.1) (N.outside S) := by rw [h1]
        rw [restrict_add, restrict_add, restrict_eq_self z.2.2.2, restrict_eq_self z'.2.2.2,
          restrict_eq_zero (N.outside S) z.1.2.2 (fun g hg => N.not_outside_of_inside hg),
          restrict_eq_zero (N.outside S) z'.1.2.2 (fun g hg => N.not_outside_of_inside hg),
          zero_add, zero_add] at h2
        exact h2
      exact Prod.ext (Subtype.ext hP) (Subtype.ext hQ)
    · intro R
      have hRe : R.1 e = 1 := N.eq_one_of_join_across S hC hce ha hb R.2.boundary_eq
      have hcross : restrict R.1 (N.crosses S) = unitWord e := by
        funext g
        by_cases hg : N.crosses S g
        · rw [restrict_apply_of_pos R.1 hg, hC g hg, hRe, unitWord_apply, if_pos rfl]
        · rw [restrict_apply_of_neg R.1 hg, unitWord_apply,
            if_neg (fun h : e = g => hg (h ▸ hce))]
      have hsum : restrict R.1 (N.inside S) + restrict R.1 (N.outside S) + unitWord e = R.1 := by
        rw [← hcross]
        exact N.restrict_add_restrict_add_restrict S R.1
      have hPQ : restrict R.1 (N.inside S) + restrict R.1 (N.outside S) =
          R.1 + unitWord e := by
        have h2 : restrict R.1 (N.inside S) + restrict R.1 (N.outside S) + unitWord e +
            unitWord e = R.1 + unitWord e := by rw [hsum]
        rw [add_assoc, word_add_self (unitWord e), add_zero] at h2
        exact h2
      have hdem : N.pathDemand a b + N.boundary (unitWord e) =
          N.pathDemand a x + N.pathDemand y b := by
        rw [N.boundary_unitWord_of_joins he]
        show (unitWord a + unitWord b : V → Bit) + (unitWord x + unitWord y) =
          unitWord a + unitWord x + (unitWord y + unitWord b)
        abel
      have hb' : N.boundary (restrict R.1 (N.inside S)) +
          N.boundary (restrict R.1 (N.outside S)) = N.pathDemand a x + N.pathDemand y b := by
        rw [← map_add, hPQ, map_add, R.2.boundary_eq, hdem]
      have ha1 : ∀ v, ¬ S v → N.pathDemand a x v = 0 := by
        intro v hv
        have h1 : v ≠ a := fun h => hv (h ▸ ha)
        have h2 : v ≠ x := fun h => hv (h ▸ hx)
        simp [pathDemand, h1, h2]
      have hb1 : ∀ v, S v → N.pathDemand y b v = 0 := by
        intro v hv
        have h1 : v ≠ y := fun h => hy (h ▸ hv)
        have h2 : v ≠ b := fun h => hb (h ▸ hv)
        simp [pathDemand, h1, h2]
      obtain ⟨hbP, hbQ⟩ := N.boundary_split (within_restrict R.1 (N.inside S))
        (within_restrict R.1 (N.outside S)) ha1 hb1 hb'
      have hminP : ∀ z : N.Word, N.IsSubword z (restrict R.1 (N.inside S)) →
          N.boundary z = 0 → z = 0 := fun z hsub hz =>
        R.2.eq_zero_of_even_subword (fun g hg => N.restrict_isSubword R.1 _ g (hsub g hg)) hz
      have hminQ : ∀ z : N.Word, N.IsSubword z (restrict R.1 (N.outside S)) →
          N.boundary z = 0 → z = 0 := fun z hsub hz =>
        R.2.eq_zero_of_even_subword (fun g hg => N.restrict_isSubword R.1 _ g (hsub g hg)) hz
      refine ⟨(⟨restrict R.1 (N.inside S), N.isPathWord_of_minimal hax hbP hminP,
        within_restrict _ _⟩, ⟨restrict R.1 (N.outside S),
        N.isPathWord_of_minimal hyb hbQ hminQ, within_restrict _ _⟩), ?_⟩
      apply Subtype.ext
      rw [hφ]
      exact hsum
  exact Nat.card_eq_of_bijective φ hbij

/-! ### The rank of a side -/

omit [Fintype V] in
/-- The count of the edge ends in `S`: twice the edges inside plus the crossing edges. -/
theorem sum_ends_eq (N : Network V E) (S : V → Prop) :
    (∑ e, ((if S (N.src e) then 1 else 0) + (if S (N.dst e) then 1 else 0))) =
      2 * Nat.card {e : E // N.inside S e} + N.cutSize S := by
  unfold cutSize
  rw [natCard_subtype_eq_card_filter, natCard_subtype_eq_card_filter, Finset.card_filter,
    Finset.card_filter, Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro e _
  by_cases h1 : S (N.src e) <;> by_cases h2 : S (N.dst e)
  · have hi : N.inside S e := ⟨h1, h2⟩
    rw [if_pos h1, if_pos h2, if_pos hi, if_neg (N.not_crosses_of_inside hi)]
    omega
  · have hc : N.crosses S e := fun h => h2 (h.1 h1)
    rw [if_pos h1, if_neg h2, if_neg (N.not_inside_of_crosses hc), if_pos hc]
    omega
  · have hc : N.crosses S e := fun h => h1 (h.2 h2)
    rw [if_neg h1, if_pos h2, if_neg (N.not_inside_of_crosses hc), if_pos hc]
    omega
  · have ho : N.outside S e := ⟨h1, h2⟩
    rw [if_neg h1, if_neg h2, if_neg (N.not_inside_of_outside ho),
      if_neg (N.not_crosses_of_outside ho)]
    omega

/-- **The rank of a part.** Let every edge of the part have both ends in the nonempty set `T`.
Then the rank of the part is at least the number of its edges plus one minus the number of the
vertices of `T`. -/
theorem rank_sub_ge (N : Network V E) (p : E → Prop) (T : V → Prop) {s₀ : V} (hs₀ : T s₀)
    (hedge : ∀ e, p e → T (N.src e) ∧ T (N.dst e)) :
    Nat.card {e : E // p e} + 1 ≤ networkRank (N.sub p) + Nat.card {v : V // T v} := by
  have e1 := network_rank_euler (N.sub p)
  simp only [← Nat.card_eq_fintype_card] at e1
  have c1 := natCard_component_ge (N.sub p) T hs₀ (fun e => hedge e.1 e.2)
  have hV : Nat.card V = Nat.card {v : V // T v} + Nat.card {v : V // ¬ T v} := by
    rw [← natCard_or_of_disjoint (fun v : V => T v) (fun v => ¬ T v) (fun v h1 h2 => h2 h1)]
    exact (Nat.card_congr (Equiv.subtypeUnivEquiv (fun v => Classical.em (T v)))).symm
  omega

/-- **A side of a cut of one edge has positive rank**, if every vertex has degree zero or at
least two. -/
theorem rank_side_pos_of_one_crossing (N : Network V E)
    (hdeg : ∀ v, N.deg (fun _ => 1) v = 0 ∨ 2 ≤ N.deg (fun _ => 1) v) (S : V → Prop) {e : E}
    {x y : V} (he : N.Joins e x y) (hx : S x) (hy : ¬ S y) (hC : ∀ g, N.crosses S g → g = e) :
    0 < networkRank (N.sub (N.inside S)) := by
  have hce : N.crosses S e := N.crosses_of_joins he hx hy
  have hone : ∀ g : E, (fun _ : E => (1 : Bit)) g ≠ 0 := fun _ => one_ne_zero
  have hxpos : 0 < N.deg (fun _ => 1) x := by
    rcases he.at_left with h | h
    · rw [← h]
      exact N.deg_src_pos (hone e)
    · rw [← h]
      exact N.deg_dst_pos (hone e)
  -- Euler's formula for the side and the vertices of positive degree
  have h1 : Nat.card {g : E // N.inside S g} + 1 ≤ networkRank (N.sub (N.inside S)) +
      Nat.card {v : V // S v ∧ 0 < N.deg (fun _ => 1) v} :=
    N.rank_sub_ge (N.inside S) (fun v => S v ∧ 0 < N.deg (fun _ => 1) v) ⟨hx, hxpos⟩
      (fun g hg => ⟨⟨hg.1, N.deg_src_pos (hone g)⟩, ⟨hg.2, N.deg_dst_pos (hone g)⟩⟩)
  -- the count of the edge ends
  have h2 := N.sum_deg_eq S
  rw [N.sum_ends_eq S] at h2
  have hcut : N.cutSize S = 1 :=
    Nat.card_eq_one_iff_unique.2
      ⟨⟨fun a b => Subtype.ext ((hC a.1 a.2).trans (hC b.1 b.2).symm)⟩, ⟨⟨e, hce⟩⟩⟩
  have h3 : 2 * Nat.card {v : V // S v ∧ 0 < N.deg (fun _ => 1) v} ≤
      ∑ v, if S v then N.deg (fun _ => 1) v else 0 := by
    rw [natCard_subtype_eq_card_filter, Finset.card_filter, Finset.mul_sum]
    apply Finset.sum_le_sum
    intro v _
    by_cases hS : S v
    · by_cases hpos : 0 < N.deg (fun _ => 1) v
      · rw [if_pos ⟨hS, hpos⟩, if_pos hS, mul_one]
        rcases hdeg v with h | h <;> omega
      · rw [if_neg (fun h => hpos h.2), mul_zero]
        exact Nat.zero_le _
    · rw [if_neg (fun h => hS h.1), mul_zero]
      exact Nat.zero_le _
  omega

/-! ### Too few paths -/

/-- **Two vertices of the same side.** Let every vertex have degree zero or at least two, and let
`e` be the only crossing edge of the cut `S`. Then at most half of the possible paths join two
vertices of `S`. -/
theorem two_mul_numPaths_le_of_same_side (N : Network V E)
    (hdeg : ∀ v, N.deg (fun _ => 1) v = 0 ∨ 2 ≤ N.deg (fun _ => 1) v) (S : V → Prop) {e : E}
    {x y : V} (he : N.Joins e x y) (hx : S x) (hy : ¬ S y) (hC : ∀ g, N.crosses S g → g = e)
    {a b : V} (ha : S a) (hb : S b) : 2 * N.numPaths a b ≤ 2 ^ networkRank N := by
  have hce : N.crosses S e := N.crosses_of_joins he hx hy
  -- a cycle of the second side
  have hpos : 0 < networkRank (N.sub (N.outside S)) :=
    N.rank_side_pos_of_one_crossing hdeg (fun v => ¬ S v) he.symm hy (fun h => h hx)
      (fun g hg => hC g ((N.crosses_not_iff S g).1 hg))
  obtain ⟨Z', hZ'⟩ := (N.sub (N.outside S)).exists_isCycleWord_of_rank_pos hpos
  have hZ : N.IsCycleWord (extend (N.outside S) Z') :=
    (N.isCycleWord_extend_iff (N.outside S) Z').2 hZ'
  have hZout : Within (extend (N.outside S) Z') (N.outside S) := within_extend _ _
  apply N.two_mul_numPaths_le_of_disjoint_cycle a b hZ
  intro R hR
  -- the path is within the first side
  have hRe : R e = 0 := N.eq_zero_of_join_same_side S hC hce ha hb hR.boundary_eq
  have hcross : restrict R (N.crosses S) = 0 := by
    funext g
    by_cases hg : N.crosses S g
    · rw [restrict_apply_of_pos R hg, hC g hg]
      exact hRe
    · exact restrict_apply_of_neg R hg
  have hsum : restrict R (N.inside S) + restrict R (N.outside S) = R := by
    have h := N.restrict_add_restrict_add_restrict S R
    rw [hcross, add_zero] at h
    exact h
  have hb' : N.boundary (restrict R (N.inside S)) + N.boundary (restrict R (N.outside S)) =
      N.pathDemand a b + 0 := by
    rw [← map_add, hsum, hR.boundary_eq, add_zero]
  have ha1 : ∀ v, ¬ S v → N.pathDemand a b v = 0 := by
    intro v hv
    have h1 : v ≠ a := fun h => hv (h ▸ ha)
    have h2 : v ≠ b := fun h => hv (h ▸ hb)
    simp [pathDemand, h1, h2]
  obtain ⟨_, hbQ⟩ := N.boundary_split (within_restrict R (N.inside S))
    (within_restrict R (N.outside S)) ha1 (fun _ _ => rfl) hb'
  have hQ0 : restrict R (N.outside S) = 0 :=
    hR.eq_zero_of_even_subword (N.restrict_isSubword R _) hbQ
  have hRin : Within R (N.inside S) := by
    intro g hg
    rcases N.inside_or_outside_or_crosses S g with h | h | h
    · exact h
    · exfalso
      have h0 := congrFun hQ0 g
      rw [restrict_apply_of_pos R h] at h0
      exact hg h0
    · exfalso
      rw [hC g h] at hg
      exact hg hRe
  exact N.vertexDisjoint_of_within hRin hZout

/-- **The crossing edge at a vertex of degree two.** Let every vertex have degree zero or at
least two, and let the only crossing edge `e` of the cut `S` join `a ∈ S` and `y ∉ S`, where `a`
has degree at most two. Then at most half of the possible paths join `a` and a vertex outside
`S`. -/
theorem two_mul_numPaths_le_of_bridge_at (N : Network V E)
    (hdeg : ∀ v, N.deg (fun _ => 1) v = 0 ∨ 2 ≤ N.deg (fun _ => 1) v) (S : V → Prop) {e : E}
    {a y : V} (he : N.Joins e a y) (ha : S a) (hy : ¬ S y) (hC : ∀ g, N.crosses S g → g = e)
    (hadeg : N.deg (fun _ => 1) a ≤ 2) {b : V} (hb : ¬ S b) :
    2 * N.numPaths a b ≤ 2 ^ networkRank N := by
  have hce : N.crosses S e := N.crosses_of_joins he ha hy
  -- a cycle of the first side
  have hpos : 0 < networkRank (N.sub (N.inside S)) :=
    N.rank_side_pos_of_one_crossing hdeg S he ha hy hC
  obtain ⟨Z', hZ'⟩ := (N.sub (N.inside S)).exists_isCycleWord_of_rank_pos hpos
  have hZ : N.IsCycleWord (extend (N.inside S) Z') :=
    (N.isCycleWord_extend_iff (N.inside S) Z').2 hZ'
  have hZin : Within (extend (N.inside S) Z') (N.inside S) := within_extend _ _
  -- the cycle does not use the vertex `a`
  have hZa : N.deg (extend (N.inside S) Z') a = 0 := by
    have hsub : N.IsSubword (extend (N.inside S) Z') (restrict (fun _ => 1) (N.inside S)) := by
      intro g hg
      rw [restrict_apply_of_pos _ (hZin g hg)]
      exact one_ne_zero
    have h1 := hsub.deg_le a
    have h2 := N.deg_split S a
    have h3 : 0 < N.deg (restrict (fun _ => 1) (N.crosses S)) a := by
      have hne : restrict (fun _ => (1 : Bit)) (N.crosses S) e ≠ 0 := by
        rw [restrict_apply_of_pos _ hce]
        exact one_ne_zero
      rcases he.at_left with h | h
      · rw [← h]
        exact N.deg_src_pos hne
      · rw [← h]
        exact N.deg_dst_pos hne
    rcases hZ.2.1 a with h | h
    · exact h
    · omega
  apply N.two_mul_numPaths_le_of_disjoint_cycle a b hZ
  intro R hR
  have hRe : R e = 1 := N.eq_one_of_join_across S hC hce ha hb hR.boundary_eq
  -- the path has no edge of the first side
  have hcross : restrict R (N.crosses S) = unitWord e := by
    funext g
    by_cases hg : N.crosses S g
    · rw [restrict_apply_of_pos R hg, hC g hg, hRe, unitWord_apply, if_pos rfl]
    · rw [restrict_apply_of_neg R hg, unitWord_apply, if_neg (fun h : e = g => hg (h ▸ hce))]
  have hsum : restrict R (N.inside S) + restrict R (N.outside S) + unitWord e = R := by
    rw [← hcross]
    exact N.restrict_add_restrict_add_restrict S R
  have hPQ : restrict R (N.inside S) + restrict R (N.outside S) = R + unitWord e := by
    have h2 : restrict R (N.inside S) + restrict R (N.outside S) + unitWord e + unitWord e =
        R + unitWord e := by rw [hsum]
    rw [add_assoc, word_add_self (unitWord e), add_zero] at h2
    exact h2
  have hdem : N.pathDemand a b + N.boundary (unitWord e) = 0 + N.pathDemand y b := by
    rw [N.boundary_unitWord_of_joins he, zero_add]
    show (unitWord a + unitWord b : V → Bit) + (unitWord a + unitWord y) =
      unitWord y + unitWord b
    calc (unitWord a + unitWord b : V → Bit) + (unitWord a + unitWord y)
        = (unitWord a + unitWord a) + (unitWord y + unitWord b) := by abel
      _ = unitWord y + unitWord b := by rw [word_add_self (unitWord a), zero_add]
  have hb' : N.boundary (restrict R (N.inside S)) + N.boundary (restrict R (N.outside S)) =
      0 + N.pathDemand y b := by
    rw [← map_add, hPQ, map_add, hR.boundary_eq, hdem]
  have hb1 : ∀ v, S v → N.pathDemand y b v = 0 := by
    intro v hv
    have h1 : v ≠ y := fun h => hy (h ▸ hv)
    have h2 : v ≠ b := fun h => hb (h ▸ hv)
    simp [pathDemand, h1, h2]
  obtain ⟨hbP, _⟩ := N.boundary_split (within_restrict R (N.inside S))
    (within_restrict R (N.outside S)) (fun _ _ => rfl) hb1 hb'
  have hP0 : restrict R (N.inside S) = 0 :=
    hR.eq_zero_of_even_subword (N.restrict_isSubword R _) hbP
  -- the path and the cycle have no common vertex
  intro v
  by_cases hv : S v
  · by_cases hva : v = a
    · right
      rw [hva]
      exact hZa
    · left
      apply N.deg_eq_zero_of_forall
      intro g hg
      rcases N.inside_or_outside_or_crosses S g with h | h | h
      · have h0 := congrFun hP0 g
        rw [restrict_apply_of_pos R h] at h0
        exact h0
      · exfalso
        rcases hg with k | k
        · exact h.1 (k ▸ hv)
        · exact h.2 (k ▸ hv)
      · exfalso
        rw [hC g h] at hg
        rcases he with ⟨k1, k2⟩ | ⟨k1, k2⟩
        · rcases hg with k | k
          · exact hva (k.symm.trans k1)
          · exact hy ((k.symm.trans k2) ▸ hv)
        · rcases hg with k | k
          · exact hy ((k.symm.trans k1) ▸ hv)
          · exact hva (k.symm.trans k2)
  · right
    exact Classical.not_not.1 fun hne =>
      hv (N.mem_of_within_inside hZin (Nat.pos_of_ne_zero hne))

end Erdos1016.BoundaryTrace.Network
