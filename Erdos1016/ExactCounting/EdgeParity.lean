import Mathlib.Combinatorics.SimpleGraph.Acyclic
import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Combinatorics.SimpleGraph.Path
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic

set_option autoImplicit false

/-!
# Parity of edge sets

For a finite set `X` of edges, `par X v` is the parity of the number of edges
of `X` at the vertex `v`. The set `X` is even if all these parities are zero.
The parity is additive for the symmetric difference.

The edge set of a trail from `a` to `b` has odd parity exactly at `a` and `b`
if `a ≠ b`, and it is even if `a = b`. The edge set of a path contains no
nonempty even set. A nonempty even subset of the edge set of a cycle is the
whole edge set.
-/

namespace Erdos1016.ExactCounting

variable {V : Type*} [DecidableEq V]

/-- The parity of the number of edges of `X` at the vertex `v`. -/
def par (X : Finset (Sym2 V)) (v : V) : ZMod 2 :=
  ((X.filter fun e => v ∈ e).card : ZMod 2)

/-- Every vertex lies on an even number of edges of `X`. -/
def IsEven (X : Finset (Sym2 V)) : Prop := ∀ v, par X v = 0

instance decidableIsEven [Fintype V] : DecidablePred (IsEven (V := V)) := fun X =>
  inferInstanceAs (Decidable (∀ v, par X v = 0))

@[simp] theorem par_empty (v : V) : par (∅ : Finset (Sym2 V)) v = 0 := by
  simp [par]

theorem isEven_empty : IsEven (∅ : Finset (Sym2 V)) := fun v => par_empty v

theorem two_eq_zero : (1 : ZMod 2) + 1 = 0 := by decide

theorem par_insert {X : Finset (Sym2 V)} {e : Sym2 V} (he : e ∉ X) (v : V) :
    par (insert e X) v = (if v ∈ e then 1 else 0) + par X v := by
  unfold par
  rw [Finset.filter_insert]
  by_cases h : v ∈ e
  · rw [if_pos h, if_pos h, Finset.card_insert_of_not_mem (by simp [he])]
    push_cast
    ring
  · rw [if_neg h, if_neg h, zero_add]

theorem par_union_of_disjoint {X Y : Finset (Sym2 V)} (h : Disjoint X Y) (v : V) :
    par (X ∪ Y) v = par X v + par Y v := by
  unfold par
  rw [Finset.filter_union, Finset.card_union_of_disjoint (Finset.disjoint_filter_filter h)]
  push_cast
  rfl

theorem par_symmDiff (X Y : Finset (Sym2 V)) (v : V) :
    par (symmDiff X Y) v = par X v + par Y v := by
  have hX : par X v = par (X \ Y) v + par (X ∩ Y) v := by
    conv_lhs => rw [← Finset.sdiff_union_inter X Y]
    exact par_union_of_disjoint (Finset.disjoint_sdiff_inter X Y) v
  have hY : par Y v = par (Y \ X) v + par (X ∩ Y) v := by
    conv_lhs => rw [← Finset.sdiff_union_inter Y X]
    rw [Finset.inter_comm Y X]
    exact par_union_of_disjoint
      (by rw [Finset.inter_comm X Y]; exact Finset.disjoint_sdiff_inter Y X) v
  have hD : par (symmDiff X Y) v = par (X \ Y) v + par (Y \ X) v := by
    have : symmDiff X Y = (X \ Y) ∪ (Y \ X) := rfl
    rw [this]
    exact par_union_of_disjoint disjoint_sdiff_sdiff v
  have h2 : par (X ∩ Y) v + par (X ∩ Y) v = 0 := CharTwo.add_self_eq_zero _
  rw [hD, hX, hY]
  linear_combination -h2

theorem IsEven.symmDiff {X Y : Finset (Sym2 V)} (hX : IsEven X) (hY : IsEven Y) :
    IsEven (symmDiff X Y) := by
  intro v
  rw [par_symmDiff, hX v, hY v, add_zero]

theorem IsEven.union_of_disjoint {X Y : Finset (Sym2 V)} (hX : IsEven X) (hY : IsEven Y)
    (h : Disjoint X Y) : IsEven (X ∪ Y) := by
  intro v
  rw [par_union_of_disjoint h, hX v, hY v, add_zero]

/-- The indicator of an edge with two distinct ends is the sum of the indicators of the ends. -/
theorem indicator_mem_pair {a c : V} (hac : a ≠ c) (v : V) :
    (if v ∈ s(a, c) then (1 : ZMod 2) else 0) =
      (if v = a then 1 else 0) + (if v = c then 1 else 0) := by
  by_cases h1 : v = a
  · subst h1
    simp [hac]
  · by_cases h2 : v = c
    · subst h2
      simp [h1]
    · simp [h1, h2]

/-- The edge set of a trail has odd parity exactly at its two ends. -/
theorem par_edges_of_isTrail {G : SimpleGraph V} {a b : V} (p : G.Walk a b)
    (hp : p.IsTrail) (v : V) :
    par p.edges.toFinset v = (if v = a then 1 else 0) + (if v = b then 1 else 0) := by
  induction p with
  | nil =>
    rw [SimpleGraph.Walk.edges_nil, List.toFinset_nil, par_empty]
    exact (CharTwo.add_self_eq_zero _).symm
  | @cons a c b h p ih =>
    rw [SimpleGraph.Walk.cons_isTrail_iff] at hp
    have hnot : s(a, c) ∉ p.edges.toFinset := by simpa using hp.2
    rw [SimpleGraph.Walk.edges_cons, List.toFinset_cons, par_insert hnot, ih hp.1,
      indicator_mem_pair h.ne]
    have h2 : (if v = c then (1 : ZMod 2) else 0) + (if v = c then 1 else 0) = 0 :=
      CharTwo.add_self_eq_zero _
    linear_combination h2

/-- The edge set of a closed trail is even. -/
theorem isEven_edges_of_isTrail {G : SimpleGraph V} {a : V} (p : G.Walk a a)
    (hp : p.IsTrail) : IsEven p.edges.toFinset := by
  intro v
  rw [par_edges_of_isTrail p hp]
  exact CharTwo.add_self_eq_zero _

/-- The edge set of a path contains no nonempty even set. -/
theorem eq_empty_of_subset_path {G : SimpleGraph V} {a b : V} (p : G.Walk a b)
    (hp : p.IsPath) {X : Finset (Sym2 V)} (hX : X ⊆ p.edges.toFinset) (hev : IsEven X) :
    X = ∅ := by
  induction p with
  | nil => simpa using hX
  | @cons a c b h p ih =>
    rw [SimpleGraph.Walk.cons_isPath_iff] at hp
    have hsub : ∀ e ∈ X, e = s(a, c) ∨ e ∈ p.edges := by
      intro e he
      have := hX he
      simpa using this
    by_cases he : s(a, c) ∈ X
    · exfalso
      have hfilter : (X.filter fun e => a ∈ e) = {s(a, c)} := by
        ext e
        constructor
        · intro hmem
          rw [Finset.mem_filter] at hmem
          rcases hsub e hmem.1 with rfl | hep
          · simp
          · exfalso
            revert hmem hep
            refine Sym2.ind (fun x y => ?_) e
            intro hmem hep
            rcases Sym2.mem_iff.1 hmem.2 with rfl | rfl
            · exact hp.2 (p.fst_mem_support_of_mem_edges hep)
            · exact hp.2 (p.snd_mem_support_of_mem_edges hep)
        · intro hmem
          rw [Finset.mem_singleton] at hmem
          subst hmem
          simp [he]
      have hpar : par X a = 1 := by simp [par, hfilter]
      rw [hev a] at hpar
      exact zero_ne_one hpar
    · apply ih hp.1
      intro e heX
      rcases hsub e heX with rfl | h'
      · exact absurd heX he
      · simpa using h'

/-- A nonempty even subset of the edge set of a cycle is the whole edge set. -/
theorem eq_edges_of_subset_cycle {G : SimpleGraph V} {a : V} (p : G.Walk a a)
    (hp : p.IsCycle) {X : Finset (Sym2 V)} (hX : X ⊆ p.edges.toFinset) (hev : IsEven X)
    (hne : X.Nonempty) : X = p.edges.toFinset := by
  have hCeven : IsEven p.edges.toFinset := isEven_edges_of_isTrail p hp.isCircuit.isTrail
  cases p with
  | nil => exact absurd rfl hp.ne_nil
  | @cons a c b h q =>
    have hc := (SimpleGraph.Walk.cons_isCycle_iff q h).1 hp
    have hmemC : ∀ e, e ∈ (SimpleGraph.Walk.cons h q).edges.toFinset ↔
        e = s(a, c) ∨ e ∈ q.edges := by
      intro e
      simp
    by_cases he : s(a, c) ∈ X
    · have hdiff : (SimpleGraph.Walk.cons h q).edges.toFinset \ X = ∅ := by
        apply eq_empty_of_subset_path q hc.1
        · intro e heY
          rw [Finset.mem_sdiff] at heY
          rcases (hmemC e).1 heY.1 with rfl | h'
          · exact absurd he heY.2
          · simpa using h'
        · have hs : (SimpleGraph.Walk.cons h q).edges.toFinset \ X =
              symmDiff (SimpleGraph.Walk.cons h q).edges.toFinset X := by
            have : symmDiff (SimpleGraph.Walk.cons h q).edges.toFinset X =
                ((SimpleGraph.Walk.cons h q).edges.toFinset \ X) ∪
                  (X \ (SimpleGraph.Walk.cons h q).edges.toFinset) := rfl
            rw [this, Finset.sdiff_eq_empty_iff_subset.2 hX, Finset.union_empty]
          rw [hs]
          exact hCeven.symmDiff hev
      exact Finset.Subset.antisymm hX (Finset.sdiff_eq_empty_iff_subset.1 hdiff)
    · exfalso
      have hempty : X = ∅ := by
        apply eq_empty_of_subset_path q hc.1 _ hev
        intro e heX
        rcases (hmemC e).1 (hX heX) with rfl | h'
        · exact absurd heX he
        · simpa using h'
      exact hne.ne_empty hempty

end Erdos1016.ExactCounting
