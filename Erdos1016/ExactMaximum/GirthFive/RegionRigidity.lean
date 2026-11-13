import Erdos1016.ExactMaximum.GirthFive.TwoTerminalRegion
import Erdos1016.Graph.Multigraph.RegionLocalization

set_option autoImplicit false
set_option maxHeartbeats 1000000

/-!
# A region with many slabs is not rigid

`N` is a multigraph without cycles of length less than five and with all degrees at most three.
Let `R` be a connected set of vertices and `w` a word on the internal edges of `R`. The region
is *rigid* for `w` if every word `w + z`, with `z` an even word on the internal edges of `R`, is
a forest. This file shows that a region with many large slabs is not rigid
(`region_not_rigid`).

A *slab* is a connected set `B i ⊆ R` on which the boundary of `w` vanishes. Its vertices are
cubic and have all neighbours in `B i`, with the exception of a small set `D i`, and
`|B i| > 400 (|D i| + 2)`. Two vertices `sm i`, `sp i` of `R` outside the slab are adjacent to
two different vertices `xm i`, `xp i` of the slab. The slabs are pairwise disjoint, and every
other slab is joined to `sm i` or to `sp i` by a walk in `R` that avoids `B i`. The number of
slabs is larger than the number of vertices with a nonzero boundary of `w`.

The proof has three steps.

1. A vertex of `R` that no walk in `R - B i` joins to `sm i` or `sp i` is joined to `sm j` or
   `sp j` in `R - B j`, for every other slab `j` (`side_of_other_slab`). So some slab `i` has
   no component of `R - B i` away from `sm i`, `sp i` with an odd boundary sum.
2. For this slab there is a word outside the slab with boundary `∂w`, or with boundary
   `∂w + sm i + sp i` (`exists_word_two_terminals`).
3. In the first case a nonzero even word of the slab gives a word `w + z` that is not a forest.
   In the second case every word of the slab with boundary `xm i + xp i` is a forest, and
   `two_terminal_region` bounds the slab.
-/

noncomputable section
open scoped BigOperators

namespace Erdos1016.ExactMaximum.GirthFive

open SimpleGraph FiniteMultiGraph Erdos1016.Nonbacktracking.ShortWalks
open Erdos1016.ExactMaximumSupport.LargeGirth Erdos1016.PolynomialBound.Separation

local instance regionRigidityDecidable (p : Prop) : Decidable p := Classical.propDecidable p

variable (N : FiniteMultiGraph)

/-! ### Small facts on demands and words -/

theorem sum_vertexUnit_of_mem {S : Finset N.Vertex} {s : N.Vertex} (h : s ∈ S) :
    (∑ u ∈ S, N.vertexUnit s u) = 1 := by
  rw [Finset.sum_eq_single s]
  · simp only [vertexUnit, Pi.single_eq_same]
  · intro u _ hu
    simp only [vertexUnit, Pi.single_eq_of_ne hu]
  · intro hn
    exact absurd h hn

theorem sum_vertexUnit_of_not_mem {S : Finset N.Vertex} {s : N.Vertex} (h : s ∉ S) :
    (∑ u ∈ S, N.vertexUnit s u) = 0 := by
  apply Finset.sum_eq_zero
  intro u hu
  have hne : u ≠ s := fun hus => h (hus ▸ hu)
  simp only [vertexUnit, Pi.single_eq_of_ne hne]

theorem sum_add_smul_units (S : Finset N.Vertex) (b : N.Demand) (s t : N.Vertex) (p q : F₂) :
    (∑ u ∈ S, (b + p • N.vertexUnit s + q • N.vertexUnit t) u) =
      (∑ u ∈ S, b u) + p * (∑ u ∈ S, N.vertexUnit s u) + q * (∑ u ∈ S, N.vertexUnit t u) := by
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Finset.sum_add_distrib, Finset.mul_sum]

/-- The boundary of a word on the internal edges of a region vanishes outside the region. -/
theorem boundary_eq_zero_of_not_mem (R : Finset N.Vertex) (w : N.EdgeWord)
    (hw : ∀ e, w e ≠ 0 → e ∈ N.internalEdges R) {v : N.Vertex} (hv : v ∉ R) :
    N.boundary w v = 0 := by
  show (∑ e, ((if N.src e = v then w e else 0) + (if N.dst e = v then w e else 0))) = 0
  apply Finset.sum_eq_zero
  intro e _
  have hz : (N.src e = v ∨ N.dst e = v) → w e = 0 := by
    intro h
    by_contra hne
    have hmem := Finset.mem_filter.mp (hw e hne)
    rcases h with h | h
    · exact hv (h ▸ hmem.2.1)
    · exact hv (h ▸ hmem.2.2)
  by_cases h1 : N.src e = v
  · by_cases h2 : N.dst e = v
    · rw [if_pos h1, if_pos h2, hz (Or.inl h1), add_zero]
    · rw [if_pos h1, if_neg h2, hz (Or.inl h1), add_zero]
  · by_cases h2 : N.dst e = v
    · rw [if_neg h1, if_pos h2, hz (Or.inr h2), add_zero]
    · rw [if_neg h1, if_neg h2, add_zero]

/-- The word of one edge between two adjacent vertices. -/
def adjWord {u v : N.Vertex} (h : N.toSimpleGraph.Adj u v) : N.EdgeWord :=
  N.walkWord (Walk.cons h Walk.nil)

theorem boundary_adjWord {u v : N.Vertex} (h : N.toSimpleGraph.Adj u v) :
    N.boundary (adjWord N h) = N.vertexUnit u + N.vertexUnit v :=
  N.boundary_walkWord _

theorem adjWord_support {u v : N.Vertex} (h : N.toSimpleGraph.Adj u v) (e : N.Edge)
    (he : adjWord N h e ≠ 0) :
    (N.src e = u ∧ N.dst e = v) ∨ (N.src e = v ∧ N.dst e = u) := by
  have hee : e = N.edgeForAdj h := by
    by_contra hne
    apply he
    show (Pi.single (N.edgeForAdj h) (1 : F₂) : N.EdgeWord) e +
      N.walkWord (Walk.nil : N.toSimpleGraph.Walk v v) e = 0
    rw [Pi.single_apply, if_neg hne, zero_add]
    rfl
  rw [hee]
  exact N.edgeForAdj_endpoints h

/-- A region with few exceptional vertices has a nonzero even word on its internal edges. -/
theorem exists_internal_cycle (h3 : ¬ N.HasCycleShorterThan 3) (B D : Finset N.Vertex)
    (hD : ∀ v ∈ B, v ∉ D → N.degree v = 3 ∧ ∀ u, N.toSimpleGraph.Adj v u → u ∈ B)
    (hlarge : 3 * D.card < B.card) : ∃ c : N.internalCycleSpace B, c ≠ 0 := by
  by_contra hno
  push_neg at hno
  have h1 := sum_card_nbrs_le N B
  have h2 := card_internalEdges_le N B hno
  have hlow : 3 * (B \ D).card ≤
      ∑ v ∈ B, ((nbrs N.toSimpleGraph v).filter (fun u => u ∈ B)).card := by
    calc
      3 * (B \ D).card = ∑ _v ∈ B \ D, 3 := by
        rw [Finset.sum_const, smul_eq_mul, mul_comm]
      _ ≤ ∑ v ∈ B \ D, ((nbrs N.toSimpleGraph v).filter (fun u => u ∈ B)).card := by
        apply Finset.sum_le_sum
        intro v hv
        obtain ⟨hvB, hvD⟩ := Finset.mem_sdiff.mp hv
        obtain ⟨hdeg, hin⟩ := hD v hvB hvD
        have hall : (nbrs N.toSimpleGraph v).filter (fun u => u ∈ B) =
            nbrs N.toSimpleGraph v := by
          apply Finset.filter_true_of_mem
          intro u hu
          exact hin u ((mem_nbrs N.toSimpleGraph v u).mp hu)
        rw [hall, card_nbrs_eq_degree N h3, hdeg]
      _ ≤ ∑ v ∈ B, ((nbrs N.toSimpleGraph v).filter (fun u => u ∈ B)).card :=
        Finset.sum_le_sum_of_subset Finset.sdiff_subset
  have hsd : B.card ≤ (B \ D).card + D.card := Finset.card_le_card_sdiff_add_card
  omega

/-! ### Walks that avoid a set -/

/-- A walk that starts outside `X` and ends in `X` leaves the part reachable from its start
through an edge into `Y`, if every vertex of the walk in `X` is in `Y`. -/
theorem exists_first_hit_mem {V : Type*} {G : SimpleGraph V} {X Y : Set V} {a b : V}
    (p : G.Walk a b) (hp : ∀ v ∈ p.support, v ∈ X → v ∈ Y) (ha : a ∉ X) (hb : b ∈ X) :
    ∃ z y, AvoidReach G X a z ∧ G.Adj z y ∧ y ∈ Y := by
  induction p with
  | nil => exact absurd hb ha
  | @cons a c b hadj q ih =>
    by_cases hc : c ∈ X
    · exact ⟨a, c, AvoidReach.refl ha, hadj,
        hp c (List.mem_cons_of_mem _ q.start_mem_support) hc⟩
    · obtain ⟨z, y, hz, hzy, hy⟩ := ih (fun v hv => hp v (List.mem_cons_of_mem _ hv)) hc hb
      exact ⟨z, y, ((AvoidReach.refl ha).step hadj hc).trans hz, hzy, hy⟩

/-- The vertices that a walk outside `X` joins to `v`, and the same set for `s`, are equal if
a walk outside `X` joins `s` to `v`. -/
theorem class_filter_eq (X : Set N.Vertex) {s v : N.Vertex}
    (h : AvoidReach N.toSimpleGraph X s v) :
    Finset.univ.filter (fun u => AvoidReach N.toSimpleGraph X v u) =
      Finset.univ.filter (fun u => AvoidReach N.toSimpleGraph X s u) := by
  ext u
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  exact ⟨fun hu => h.trans hu, fun hu => h.symm.trans hu⟩

/-- **Two terminals outside a set.** Let `b` be a demand with total zero that vanishes on `X`,
and let `s`, `t` be outside `X`. Suppose that `b` has sum zero on every component of the
complement of `X` that contains neither `s` nor `t`. Then `b`, or `b + s + t`, is the boundary
of a word whose edges have no end in `X`. -/
theorem exists_word_two_terminals (X : Set N.Vertex) (b : N.Demand)
    (hsum : (∑ v, b v) = 0) (hX : ∀ v, v ∈ X → b v = 0) (s t : N.Vertex)
    (hs : s ∉ X) (ht : t ∉ X)
    (hside : ∀ v, v ∉ X → ¬ AvoidReach N.toSimpleGraph X s v →
      ¬ AvoidReach N.toSimpleGraph X t v →
      (∑ u ∈ Finset.univ.filter (fun u => AvoidReach N.toSimpleGraph X v u), b u) = 0) :
    (∃ w : N.EdgeWord, N.boundary w = b ∧ ∀ e, w e ≠ 0 → N.src e ∉ X ∧ N.dst e ∉ X) ∨
    (∃ w : N.EdgeWord, N.boundary w = b + N.vertexUnit s + N.vertexUnit t ∧
      ∀ e, w e ≠ 0 → N.src e ∉ X ∧ N.dst e ∉ X) := by
  have hchar : ∀ a : F₂, a + a = 0 := by decide
  have hkey : ∀ a c : F₂, a + c = 0 → a = c := by decide
  let cls : N.Vertex → Finset N.Vertex := fun v =>
    Finset.univ.filter (fun u => AvoidReach N.toSimpleGraph X v u)
  have hmem : ∀ v u, u ∈ cls v ↔ AvoidReach N.toSimpleGraph X v u := by
    intro v u
    simp only [cls, Finset.mem_filter, Finset.mem_univ, true_and]
  let p : F₂ := ∑ u ∈ cls s, b u
  let q : F₂ := ∑ u ∈ cls t, b u
  let q' : F₂ := if AvoidReach N.toSimpleGraph X s t then 0 else q
  let b' : N.Demand := b + p • N.vertexUnit s + q' • N.vertexUnit t
  have hb'X : ∀ v, v ∈ X → b' v = 0 := by
    intro v hv
    have h1 : v ≠ s := fun h => hs (h ▸ hv)
    have h2 : v ≠ t := fun h => ht (h ▸ hv)
    show b v + p • N.vertexUnit s v + q' • N.vertexUnit t v = 0
    simp only [vertexUnit, Pi.single_eq_of_ne h1, Pi.single_eq_of_ne h2, smul_zero, add_zero]
    exact hX v hv
  have hev : ∀ v, v ∉ X → (∑ u ∈ cls v, b' u) = 0 := by
    intro v hv
    show (∑ u ∈ cls v, (b + p • N.vertexUnit s + q' • N.vertexUnit t) u) = 0
    rw [sum_add_smul_units]
    by_cases h1 : AvoidReach N.toSimpleGraph X s v
    · have hcls : cls v = cls s := class_filter_eq N X h1
      have hsv : s ∈ cls v := (hmem v s).mpr h1.symm
      rw [sum_vertexUnit_of_mem N hsv, mul_one]
      have hthird : q' * (∑ u ∈ cls v, N.vertexUnit t u) = 0 := by
        by_cases hst : AvoidReach N.toSimpleGraph X s t
        · have hq0 : q' = 0 := if_pos hst
          rw [hq0, zero_mul]
        · have htv : t ∉ cls v := fun h => hst (h1.trans ((hmem v t).mp h))
          rw [sum_vertexUnit_of_not_mem N htv, mul_zero]
      rw [hthird, add_zero, hcls]
      exact hchar p
    · by_cases h2 : AvoidReach N.toSimpleGraph X t v
      · have hcls : cls v = cls t := class_filter_eq N X h2
        have hsv : s ∉ cls v := fun h => h1 ((hmem v s).mp h).symm
        have htv : t ∈ cls v := (hmem v t).mpr h2.symm
        have hst : ¬ AvoidReach N.toSimpleGraph X s t := fun h => h1 (h.trans h2)
        have hq' : q' = q := if_neg hst
        rw [sum_vertexUnit_of_not_mem N hsv, sum_vertexUnit_of_mem N htv, mul_zero, mul_one,
          add_zero, hq', hcls]
        exact hchar q
      · have hsv : s ∉ cls v := fun h => h1 ((hmem v s).mp h).symm
        have htv : t ∉ cls v := fun h => h2 ((hmem v t).mp h).symm
        rw [sum_vertexUnit_of_not_mem N hsv, sum_vertexUnit_of_not_mem N htv, mul_zero,
          mul_zero, add_zero, add_zero]
        exact hside v hv h1 h2
  obtain ⟨w', hw', hsup⟩ := exists_word_of_sides_even N X _ b' rfl hb'X hev
  have htot : (∑ v, b' v) = 0 := by
    rw [← hw']
    exact RegionLocalization.sum_boundary_eq_zero N w'
  have htot' : p + q' = 0 := by
    have h := sum_add_smul_units N Finset.univ b s t p q'
    rw [sum_vertexUnit_of_mem N (Finset.mem_univ s),
      sum_vertexUnit_of_mem N (Finset.mem_univ t), mul_one, mul_one, hsum, zero_add] at h
    rw [← h]
    exact htot
  have hpq : p = q' := hkey p q' htot'
  rcases Fin.exists_fin_two.mp ⟨p, rfl⟩ with hp | hp
  · left
    have hp0 : p = 0 := hp
    refine ⟨w', ?_, hsup⟩
    rw [hw']
    show b + p • N.vertexUnit s + q' • N.vertexUnit t = b
    rw [← hpq, hp0]
    simp only [zero_smul, add_zero]
  · right
    have hp1 : p = 1 := hp
    refine ⟨w', ?_, hsup⟩
    rw [hw']
    show b + p • N.vertexUnit s + q' • N.vertexUnit t = b + N.vertexUnit s + N.vertexUnit t
    rw [← hpq, hp1]
    simp only [one_smul]

/-! ### Slabs -/

/-- The complement of a region, together with a slab. -/
def slabCut (R B : Finset N.Vertex) : Set N.Vertex := {v | v ∉ R ∨ v ∈ B}

theorem not_mem_slabCut {R B : Finset N.Vertex} {v : N.Vertex} :
    v ∉ slabCut N R B ↔ v ∈ R ∧ v ∉ B := by
  show ¬ (v ∉ R ∨ v ∈ B) ↔ v ∈ R ∧ v ∉ B
  constructor
  · intro h
    exact ⟨by_contra fun h1 => h (Or.inl h1), fun h2 => h (Or.inr h2)⟩
  · rintro ⟨h1, h2⟩ (h | h)
    · exact h h1
    · exact h2 h

/-- A vertex that is not joined to the two spine vertices of a slab is joined to a spine vertex
of every other slab. -/
theorem side_of_other_slab (R B B' : Finset N.Vertex)
    (hR : IsConnectedSet N.toSimpleGraph (↑R : Set N.Vertex))
    (hBR : B ⊆ R) (hdisj : Disjoint B B') {x : N.Vertex} (hx : x ∈ B)
    (sm sp sm' sp' : N.Vertex)
    (h1 : ∀ v ∈ B', AvoidReach N.toSimpleGraph (slabCut N R B) sm v ∨
      AvoidReach N.toSimpleGraph (slabCut N R B) sp v)
    (h2 : ∀ v ∈ B, AvoidReach N.toSimpleGraph (slabCut N R B') sm' v ∨
      AvoidReach N.toSimpleGraph (slabCut N R B') sp' v)
    {u : N.Vertex} (hu : u ∉ slabCut N R B)
    (hum : ¬ AvoidReach N.toSimpleGraph (slabCut N R B) sm u)
    (hup : ¬ AvoidReach N.toSimpleGraph (slabCut N R B) sp u) :
    AvoidReach N.toSimpleGraph (slabCut N R B') sm' u ∨
      AvoidReach N.toSimpleGraph (slabCut N R B') sp' u := by
  have huR : u ∈ R := ((not_mem_slabCut N).mp hu).1
  obtain ⟨p, hp⟩ := hR u (by exact_mod_cast huR) x (by exact_mod_cast hBR hx)
  have hpX : ∀ v ∈ p.support, v ∈ slabCut N R B → v ∈ (↑B : Set N.Vertex) := by
    intro v hv hvX
    rcases hvX with h | h
    · exact absurd (by exact_mod_cast hp v hv) h
    · exact_mod_cast h
  obtain ⟨z, y, hz, hzy, hy⟩ := exists_first_hit_mem p hpX hu (Or.inr hx)
  have hyB : y ∈ B := by exact_mod_cast hy
  obtain ⟨pz, hpz⟩ := hz
  -- the walk to `z` avoids the other slab
  have hpz' : ∀ v ∈ pz.support, v ∉ slabCut N R B' := by
    intro v hv
    have hvR : v ∈ R := ((not_mem_slabCut N).mp (hpz v hv)).1
    have huv : AvoidReach N.toSimpleGraph (slabCut N R B) u v :=
      avoidReach_of_mem_support pz hpz hv
    refine (not_mem_slabCut N).mpr ⟨hvR, ?_⟩
    intro hvB'
    rcases h1 v hvB' with h | h
    · exact hum (h.trans huv.symm)
    · exact hup (h.trans huv.symm)
  have hyB' : y ∉ B' := fun h => Finset.disjoint_left.mp hdisj hyB h
  have huy : AvoidReach N.toSimpleGraph (slabCut N R B') u y :=
    AvoidReach.step ⟨pz, hpz'⟩ hzy ((not_mem_slabCut N).mpr ⟨hBR hyB, hyB'⟩)
  rcases h2 y hyB with h | h
  · exact Or.inl (h.trans huy.symm)
  · exact Or.inr (h.trans huy.symm)

/-- **A region with many slabs is not rigid.** -/
theorem region_not_rigid (h5 : ¬ N.HasCycleShorterThan 5) (hmax : ∀ v, N.degree v ≤ 3)
    (R : Finset N.Vertex) (hR : IsConnectedSet N.toSimpleGraph (↑R : Set N.Vertex))
    {ι : Type*} [Fintype ι]
    (B D : ι → Finset N.Vertex) (sm sp xm xp : ι → N.Vertex)
    (hBR : ∀ i, B i ⊆ R)
    (hBconn : ∀ i, IsConnectedSet N.toSimpleGraph (↑(B i) : Set N.Vertex))
    (hdisj : ∀ i j, i ≠ j → Disjoint (B i) (B j))
    (hD : ∀ i, ∀ v ∈ B i, v ∉ D i →
      N.degree v = 3 ∧ ∀ u, N.toSimpleGraph.Adj v u → u ∈ B i)
    (hsize : ∀ i, 400 * ((D i).card + 2) < (B i).card)
    (hsm : ∀ i, sm i ∈ R ∧ sm i ∉ B i) (hsp : ∀ i, sp i ∈ R ∧ sp i ∉ B i)
    (hxm : ∀ i, xm i ∈ B i ∧ N.toSimpleGraph.Adj (sm i) (xm i))
    (hxp : ∀ i, xp i ∈ B i ∧ N.toSimpleGraph.Adj (sp i) (xp i))
    (hxne : ∀ i, xm i ≠ xp i)
    (hspine : ∀ i j, i ≠ j → ∀ v ∈ B j,
      AvoidReach N.toSimpleGraph (slabCut N R (B i)) (sm i) v ∨
      AvoidReach N.toSimpleGraph (slabCut N R (B i)) (sp i) v)
    (w : N.EdgeWord) (hw : ∀ e, w e ≠ 0 → e ∈ N.internalEdges R)
    (hb : ∀ i, ∀ v ∈ B i, N.boundary w v = 0)
    (hcount : (Finset.univ.filter (fun v => N.boundary w v ≠ 0)).card < Fintype.card ι) :
    ∃ z : N.internalCycleSpace R, ¬ N.IsForestWord (w + z.1.1) := by
  by_contra hall
  push_neg at hall
  have h3 := no_short_three_of_le N 5 (by norm_num) h5
  have hchar : ∀ a : F₂, a + a = 0 := by decide
  -- a slab without an odd side component
  have hpigeon : ∃ i, ∀ v, v ∉ slabCut N R (B i) →
      ¬ AvoidReach N.toSimpleGraph (slabCut N R (B i)) (sm i) v →
      ¬ AvoidReach N.toSimpleGraph (slabCut N R (B i)) (sp i) v →
      (∑ u ∈ Finset.univ.filter
        (fun u => AvoidReach N.toSimpleGraph (slabCut N R (B i)) v u), N.boundary w u) = 0 := by
    by_contra hno
    push_neg at hno
    have hex : ∀ i, ∃ u, N.boundary w u ≠ 0 ∧ u ∉ slabCut N R (B i) ∧
        ¬ AvoidReach N.toSimpleGraph (slabCut N R (B i)) (sm i) u ∧
        ¬ AvoidReach N.toSimpleGraph (slabCut N R (B i)) (sp i) u := by
      intro i
      obtain ⟨v, _, hvm, hvp, hsumne⟩ := hno i
      obtain ⟨u, hu, hbu⟩ := Finset.exists_ne_zero_of_sum_ne_zero hsumne
      have hvu := (Finset.mem_filter.mp hu).2
      exact ⟨u, hbu, hvu.right_not_mem, fun h => hvm (h.trans hvu.symm),
        fun h => hvp (h.trans hvu.symm)⟩
    choose u hu1 hu2 hu3 hu4 using hex
    have hinj : Function.Injective u := by
      intro i j hij
      by_contra hne
      have hside := side_of_other_slab N R (B i) (B j) hR (hBR i) (hdisj i j hne) (hxm i).1
        (sm i) (sp i) (sm j) (sp j) (hspine i j hne) (hspine j i (Ne.symm hne))
        (hu2 i) (hu3 i) (hu4 i)
      rw [hij] at hside
      rcases hside with h | h
      · exact hu3 j h
      · exact hu4 j h
    have hle : Fintype.card ι ≤
        (Finset.univ.filter (fun v => N.boundary w v ≠ 0)).card := by
      rw [← Finset.card_univ]
      apply Finset.card_le_card_of_injOn u
      · intro i _
        exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hu1 i⟩
      · intro i _ j _ h
        exact hinj h
    exact absurd hle (not_le.mpr hcount)
  obtain ⟨i, hi⟩ := hpigeon
  have hX : ∀ v, v ∈ slabCut N R (B i) → N.boundary w v = 0 := by
    intro v hv
    rcases hv with h | h
    · exact boundary_eq_zero_of_not_mem N R w hw h
    · exact hb i v h
  have hsmX : sm i ∉ slabCut N R (B i) := (not_mem_slabCut N).mpr (hsm i)
  have hspX : sp i ∉ slabCut N R (B i) := (not_mem_slabCut N).mpr (hsp i)
  -- an edge whose ends are outside the cut is an internal edge of the region
  have hinR : ∀ e, N.src e ∉ slabCut N R (B i) → N.dst e ∉ slabCut N R (B i) →
      e ∈ N.internalEdges R := by
    intro e h1 h2
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, ((not_mem_slabCut N).mp h1).1,
      ((not_mem_slabCut N).mp h2).1⟩
  have hwR : ∀ e, e ∉ N.internalEdges R → w e = 0 := by
    intro e he
    by_contra hne
    exact he (hw e hne)
  have hBint : ∀ e, e ∈ N.internalEdges (B i) → e ∈ N.internalEdges R := by
    intro e he
    have h := Finset.mem_filter.mp he
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hBR i h.2.1, hBR i h.2.2⟩
  rcases exists_word_two_terminals N (slabCut N R (B i)) (N.boundary w)
    (RegionLocalization.sum_boundary_eq_zero N w) hX (sm i) (sp i) hsmX hspX hi with
    ⟨w₀, hw₀, hsup⟩ | ⟨w₀, hw₀, hsup⟩
  · -- a word outside the slab with the same boundary: add a nonzero even word of the slab
    obtain ⟨c, hc⟩ := exists_internal_cycle N h3 (B i) (D i) (hD i) (by have := hsize i; omega)
    have hcB : ∀ e, c.1.1 e ≠ 0 → e ∈ N.internalEdges (B i) := by
      intro e he
      by_contra hne
      exact he (c.2 e hne)
    have hw₀B : ∀ e, e ∈ N.internalEdges (B i) → w₀ e = 0 := by
      intro e he
      by_contra hne
      exact (hsup e hne).1 (Or.inr (Finset.mem_filter.mp he).2.1)
    have hc0 : N.boundary c.1.1 = 0 := LinearMap.mem_ker.mp c.1.2
    have hzker : w + w₀ + c.1.1 ∈ LinearMap.ker N.boundary := by
      rw [LinearMap.mem_ker, map_add, map_add, hw₀, hc0, add_zero]
      funext t
      exact hchar _
    have hzint : (⟨w + w₀ + c.1.1, hzker⟩ : N.CycleSpace) ∈ N.internalCycleSpace R := by
      intro e he
      have h1 : w e = 0 := hwR e he
      have h2 : w₀ e = 0 := by
        by_contra hne
        exact he (hinR e (hsup e hne).1 (hsup e hne).2)
      have h3' : c.1.1 e = 0 := by
        by_contra hne
        exact he (hBint e (hcB e hne))
      show w e + w₀ e + c.1.1 e = 0
      rw [h1, h2, h3', add_zero, add_zero]
    have hf := hall ⟨⟨w + w₀ + c.1.1, hzker⟩, hzint⟩
    have hzero := (isForestWord_iff_no_even_support N _).mp hf c.1 ?_
    · apply hc
      apply Subtype.ext
      apply Subtype.ext
      exact hzero
    · intro e he
      show w e + (w e + w₀ e + c.1.1 e) ≠ 0
      rw [hw₀B e (hcB e he), add_zero, ← add_assoc, hchar, zero_add]
      exact he
  · -- two terminals: every word of the slab with boundary `xm + xp` is a forest
    have hrigid : ∀ j : N.EdgeWord, (∀ e, j e ≠ 0 → e ∈ N.internalEdges (B i)) →
        N.boundary j = N.vertexUnit (xm i) + N.vertexUnit (xp i) → N.IsForestWord j := by
      intro j hj hbj
      let am : N.EdgeWord := adjWord N (hxm i).2
      let ap : N.EdgeWord := adjWord N (hxp i).2
      have hkey : ∀ y a b c d : F₂, y + (y + a + b + (a + c) + (b + d) + (c + d)) = 0 := by
        decide
      have hzker : w + (w₀ + am + ap + j) ∈ LinearMap.ker N.boundary := by
        rw [LinearMap.mem_ker, map_add, map_add, map_add, map_add, hw₀, hbj,
          boundary_adjWord, boundary_adjWord]
        funext t
        exact hkey _ _ _ _ _
      have hamR : ∀ e, am e ≠ 0 → e ∈ N.internalEdges R := by
        intro e he
        rcases adjWord_support N (hxm i).2 e he with h | h
        · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, by rw [h.1]; exact (hsm i).1,
            by rw [h.2]; exact hBR i (hxm i).1⟩
        · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, by rw [h.1]; exact hBR i (hxm i).1,
            by rw [h.2]; exact (hsm i).1⟩
      have hapR : ∀ e, ap e ≠ 0 → e ∈ N.internalEdges R := by
        intro e he
        rcases adjWord_support N (hxp i).2 e he with h | h
        · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, by rw [h.1]; exact (hsp i).1,
            by rw [h.2]; exact hBR i (hxp i).1⟩
        · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, by rw [h.1]; exact hBR i (hxp i).1,
            by rw [h.2]; exact (hsp i).1⟩
      have hzint : (⟨w + (w₀ + am + ap + j), hzker⟩ : N.CycleSpace) ∈
          N.internalCycleSpace R := by
        intro e he
        have h1 : w e = 0 := hwR e he
        have h2 : w₀ e = 0 := by
          by_contra hne
          exact he (hinR e (hsup e hne).1 (hsup e hne).2)
        have h3' : am e = 0 := by
          by_contra hne
          exact he (hamR e hne)
        have h4 : ap e = 0 := by
          by_contra hne
          exact he (hapR e hne)
        have h5' : j e = 0 := by
          by_contra hne
          exact he (hBint e (hj e hne))
        show w e + (w₀ e + am e + ap e + j e) = 0
        rw [h1, h2, h3', h4, h5', add_zero, add_zero, add_zero, add_zero]
      have hf := hall ⟨⟨w + (w₀ + am + ap + j), hzker⟩, hzint⟩
      apply hf.mono
      intro e he
      have heB := Finset.mem_filter.mp (hj e he)
      have h2 : w₀ e = 0 := by
        by_contra hne
        exact (hsup e hne).1 (Or.inr heB.2.1)
      have h3' : am e = 0 := by
        by_contra hne
        rcases adjWord_support N (hxm i).2 e hne with h | h
        · exact (hsm i).2 (h.1 ▸ heB.2.1)
        · exact (hsm i).2 (h.2 ▸ heB.2.2)
      have h4 : ap e = 0 := by
        by_contra hne
        rcases adjWord_support N (hxp i).2 e hne with h | h
        · exact (hsp i).2 (h.1 ▸ heB.2.1)
        · exact (hsp i).2 (h.2 ▸ heB.2.2)
      show w e + (w e + (w₀ e + am e + ap e + j e)) ≠ 0
      rw [h2, h3', h4, add_zero, add_zero, zero_add, ← add_assoc, hchar, zero_add]
      exact he
    have hbound := two_terminal_region N h5 hmax (B i) (hBconn i) (hxm i).1 (hxp i).1
      (hxne i) hrigid (D i) (hD i)
    have := hsize i
    omega

end Erdos1016.ExactMaximum.GirthFive
