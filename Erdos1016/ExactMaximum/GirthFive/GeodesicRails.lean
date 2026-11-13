import Erdos1016.ExactMaximum.GirthFive.RailBound
import Erdos1016.Nonbacktracking.Girth.CollisionGeometry

set_option autoImplicit false

/-!
# A shortest path in a graph of girth at least five

`K` is a simple graph in which every cycle has more than four edges
(`ShortWalks.GirthGreater K 4`), and `A` is a shortest walk from `x` to `y`. This file proves:

* `no_short_closed`: a closed sequence of at most four steps without an immediate reversal does
  not exist;
* `geodesic_le`, `geodesic_getVert_injective`: the vertex `A.getVert n` has distance `n` from
  `x`, and a walk between `A.getVert i` and `A.getVert j` has at least `|i - j|` steps;
* `attach_unique`: a vertex outside `A` has at most one neighbour on `A`;
* `no_rail`: there is no sequence `v 0, ..., v 6` of pairwise different vertices outside `A`,
  each adjacent to the next, such that every `v k` has a neighbour at an inner position of `A`
  (the rail lemma for graphs). The proof reduces it to the arithmetic statement `rail_bound`.

Walks are built from sequences of vertices (`exists_walk_of_fn`), and a walk is reduced if its
vertices at distance two are different (`reduced_of_getVert`).
-/

namespace Erdos1016.ExactMaximum.GirthFive

open SimpleGraph Erdos1016.Nonbacktracking Erdos1016.Nonbacktracking.ShortWalks
open Erdos1016.Proof.CyclicRunCollisionGeometry

variable {V : Type*} {K : SimpleGraph V}

/-- A sequence of vertices in which consecutive vertices are adjacent gives a walk. -/
theorem exists_walk_of_fn (f : ℕ → V) : ∀ (n i : ℕ),
    (∀ k, i ≤ k → k < i + n → K.Adj (f k) (f (k + 1))) →
    ∃ q : K.Walk (f i) (f (i + n)), q.length = n ∧ ∀ m, m ≤ n → q.getVert m = f (i + m) := by
  intro n
  induction n with
  | zero =>
    intro i _
    refine ⟨Walk.nil, rfl, ?_⟩
    intro m hm
    have hm0 : m = 0 := by omega
    subst hm0
    rfl
  | succ n ih =>
    intro i h
    obtain ⟨q, hq, hv⟩ := ih (i + 1) (fun k hk1 hk2 => h k (by omega) (by omega))
    have hadj : K.Adj (f i) (f (i + 1)) := h i le_rfl (by omega)
    have e : i + 1 + n = i + (n + 1) := by omega
    refine ⟨(Walk.cons hadj q).copy rfl (by rw [e]), ?_, ?_⟩
    · simp [hq]
    · intro m hm
      rw [Walk.getVert_copy]
      cases m with
      | zero => simp
      | succ m =>
        rw [Walk.getVert_cons_succ, hv m (by omega)]
        congr 1
        omega

/-- A walk is reduced if its vertices at distance two are different. -/
theorem reduced_of_getVert {u v : V} (q : K.Walk u v)
    (h : ∀ m, m + 2 ≤ q.length → q.getVert (m + 2) ≠ q.getVert m) : Reduced q := by
  induction q with
  | nil => trivial
  | @cons a b c hadj p ih =>
    refine ⟨ih ?_, ?_⟩
    · intro m hm
      have hh := h (m + 1) (by simp only [Walk.length_cons]; omega)
      rw [show m + 1 + 2 = (m + 2) + 1 from rfl, Walk.getVert_cons_succ,
        Walk.getVert_cons_succ] at hh
      exact hh
    · intro hnil
      have hlen : 1 ≤ p.length := by
        rw [Walk.nil_iff_length_eq] at hnil
        omega
      have hh := h 0 (by simp only [Walk.length_cons]; omega)
      rw [show 0 + 2 = 1 + 1 from rfl, Walk.getVert_cons_succ, Walk.getVert_zero] at hh
      exact hh

/-- **No short closed sequence.** If every cycle has more than four edges, then there is no closed
sequence of `n` steps, `1 ≤ n ≤ 4`, in which vertices at distance two are different. -/
theorem no_short_closed (hg : GirthGreater K 4) (f : ℕ → V) (n : ℕ) (hn : 1 ≤ n) (hn4 : n ≤ 4)
    (hclosed : f n = f 0) (hadj : ∀ k, k < n → K.Adj (f k) (f (k + 1)))
    (hred : ∀ m, m + 2 ≤ n → f (m + 2) ≠ f m) : False := by
  obtain ⟨q, hlen, hv⟩ := exists_walk_of_fn (K := K) f n 0 (fun k _ hk => hadj k (by omega))
  have hend : f (0 + n) = f 0 := by rw [zero_add, hclosed]
  let c : K.Walk (f 0) (f 0) := q.copy rfl hend
  have hc : Reduced c := by
    rw [reduced_copy]
    apply reduced_of_getVert
    intro m hm
    rw [hlen] at hm
    rw [hv (m + 2) hm, hv m (by omega)]
    simpa only [zero_add] using hred m hm
  have hnil : ¬ c.Nil := by
    rw [Walk.nil_iff_length_eq]
    simp only [c, Walk.length_copy, hlen]
    omega
  have hlong := reduced_closed_nonempty_length_gt 4 hg c hc hnil
  simp only [c, Walk.length_copy, hlen] at hlong
  omega

/-- A sequence of at most five vertices as a function on the natural numbers. -/
def seq5 (a b c d e : V) : ℕ → V
  | 0 => a
  | 1 => b
  | 2 => c
  | 3 => d
  | _ => e

section Geodesic

variable {x y : V} (A : K.Walk x y) (hshort : ∀ q : K.Walk x y, A.length ≤ q.length)

include hshort in
/-- A walk from `x` to the vertex at position `n` of a shortest walk has at least `n` steps. -/
theorem geodesic_prefix {n : ℕ} (hn : n ≤ A.length) (W : K.Walk x (A.getVert n)) :
    n ≤ W.length := by
  obtain ⟨q, hq, _⟩ := exists_walk_of_fn (K := K) A.getVert (A.length - n) n
    (fun k _ hk => A.adj_getVert_succ (by omega))
  have hend : A.getVert (n + (A.length - n)) = y := by
    rw [show n + (A.length - n) = A.length by omega, Walk.getVert_length]
  have h := hshort (W.append (q.copy rfl hend))
  simp only [Walk.length_append, Walk.length_copy, hq] at h
  omega

/-- The initial part of a walk, as a walk with `n` steps. -/
theorem exists_prefix {n : ℕ} (hn : n ≤ A.length) :
    ∃ W : K.Walk x (A.getVert n), W.length = n := by
  obtain ⟨q, hq, _⟩ := exists_walk_of_fn (K := K) A.getVert n 0
    (fun k _ hk => A.adj_getVert_succ (by omega))
  exact ⟨q.copy (Walk.getVert_zero A) (by rw [zero_add]), by simp [hq]⟩

include hshort in
/-- The positions on a shortest walk are different vertices. -/
theorem geodesic_getVert_injective {i j : ℕ} (hi : i ≤ A.length) (hj : j ≤ A.length)
    (h : A.getVert i = A.getVert j) : i = j := by
  obtain ⟨Wi, hWi⟩ := exists_prefix A hi
  obtain ⟨Wj, hWj⟩ := exists_prefix A hj
  have h1 := geodesic_prefix A hshort hj (Wi.copy rfl h)
  have h2 := geodesic_prefix A hshort hi (Wj.copy rfl h.symm)
  simp only [Walk.length_copy, hWi, hWj] at h1 h2
  omega

include hshort in
/-- A walk between two positions of a shortest walk is not shorter than their difference. -/
theorem geodesic_le {i j : ℕ} (hi : i ≤ A.length) (hj : j ≤ A.length)
    (W : K.Walk (A.getVert i) (A.getVert j)) : j ≤ i + W.length := by
  obtain ⟨Wi, hWi⟩ := exists_prefix A hi
  have h := geodesic_prefix A hshort hj (Wi.append W)
  simp only [Walk.length_append, hWi] at h
  exact h

include hshort in
/-- **A vertex outside a shortest walk has at most one neighbour on it.** -/
theorem attach_unique (hg : GirthGreater K 4) {v : V} (hv : v ∉ A.support) {i j : ℕ}
    (hi : i ≤ A.length) (hj : j ≤ A.length)
    (hvi : K.Adj v (A.getVert i)) (hvj : K.Adj v (A.getVert j)) : i = j := by
  by_contra hne
  -- it suffices to treat `i < j`
  have key : ∀ i j : ℕ, i ≤ A.length → j ≤ A.length → K.Adj v (A.getVert i) →
      K.Adj v (A.getVert j) → i < j → False := by
    intro i j hi hj hvi hvj hij
    have hvi' : v ≠ A.getVert i := fun h => hv (h ▸ A.getVert_mem_support i)
    have hle := geodesic_le A hshort hi hj (Walk.cons hvi.symm (Walk.cons hvj Walk.nil))
    simp only [Walk.length_cons, Walk.length_nil] at hle
    have hinj : ∀ a b : ℕ, a ≤ A.length → b ≤ A.length → a ≠ b → A.getVert a ≠ A.getVert b :=
      fun a b ha hb hab h => hab (geodesic_getVert_injective A hshort ha hb h)
    have hnot : ∀ a : ℕ, A.getVert a ≠ v := fun a h => hv (h ▸ A.getVert_mem_support a)
    rcases (show j = i + 1 ∨ j = i + 2 by omega) with rfl | rfl
    · -- a triangle
      refine no_short_closed hg (seq5 (A.getVert i) v (A.getVert (i + 1)) (A.getVert i)
        (A.getVert i)) 3 (by norm_num) (by norm_num) rfl ?_ ?_
      · intro k hk
        interval_cases k
        · exact hvi.symm
        · exact hvj
        · exact (A.adj_getVert_succ (by omega)).symm
      · intro m hm
        have hm' : m ≤ 1 := by omega
        interval_cases m
        · exact hinj _ _ hj hi (by omega)
        · exact fun h => hnot i h
    · -- a cycle of length four
      refine no_short_closed hg (seq5 (A.getVert i) v (A.getVert (i + 2)) (A.getVert (i + 1))
        (A.getVert i)) 4 (by norm_num) (by norm_num) rfl ?_ ?_
      · intro k hk
        interval_cases k
        · exact hvi.symm
        · exact hvj
        · exact (A.adj_getVert_succ (by omega)).symm
        · exact (A.adj_getVert_succ (by omega)).symm
      · intro m hm
        have hm' : m ≤ 2 := by omega
        interval_cases m
        · exact hinj _ _ hj hi (by omega)
        · exact fun h => hnot (i + 1) h
        · exact hinj _ _ hi hj (by omega)
  rcases Nat.lt_or_gt_of_ne hne with h | h
  · exact key i j hi hj hvi hvj h
  · exact key j i hj hi hvj hvi h

include hshort in
/-- **The rail lemma for graphs.** In a graph in which every cycle has more than four edges and
no vertex has four neighbours, let `A` be a shortest walk. Then there are no seven pairwise
different vertices `v 0, ..., v 6` outside `A`, each adjacent to the next, such that every `v k`
has a neighbour at an inner position `p k` of `A`. -/
theorem no_rail (hg : GirthGreater K 4)
    (hdeg : ∀ z a b c d : V, K.Adj z a → K.Adj z b → K.Adj z c → K.Adj z d →
      a = b ∨ a = c ∨ a = d ∨ b = c ∨ b = d ∨ c = d)
    (v : ℕ → V) (p : ℕ → ℕ)
    (hvA : ∀ k, k ≤ 6 → v k ∉ A.support)
    (hvadj : ∀ k, k < 6 → K.Adj (v k) (v (k + 1)))
    (hvinj : ∀ k l, k < l → l ≤ 6 → v k ≠ v l)
    (hp : ∀ k, k ≤ 6 → 0 < p k ∧ p k < A.length)
    (hatt : ∀ k, k ≤ 6 → K.Adj (v k) (A.getVert (p k))) : False := by
  have hinj : ∀ a b : ℕ, a ≤ A.length → b ≤ A.length → a ≠ b → A.getVert a ≠ A.getVert b :=
    fun a b ha hb hab h => hab (geodesic_getVert_injective A hshort ha hb h)
  have hnot : ∀ a k : ℕ, k ≤ 6 → A.getVert a ≠ v k :=
    fun a k hk h => hvA k hk (h ▸ A.getVert_mem_support a)
  -- different vertices of the rail have different positions
  have hne : ∀ k l, k < l → l ≤ 6 → p k ≠ p l := by
    intro k l hkl hl heq
    have hk : k ≤ 6 := by omega
    obtain ⟨hp0, hp1⟩ := hp k hk
    have h1 : K.Adj (A.getVert (p k)) (A.getVert (p k - 1)) := by
      have := A.adj_getVert_succ (show p k - 1 < A.length by omega)
      rw [show p k - 1 + 1 = p k by omega] at this
      exact this.symm
    have h2 : K.Adj (A.getVert (p k)) (A.getVert (p k + 1)) := A.adj_getVert_succ hp1
    have h3 : K.Adj (A.getVert (p k)) (v k) := (hatt k hk).symm
    have h4 : K.Adj (A.getVert (p k)) (v l) := by
      rw [heq]
      exact (hatt l hl).symm
    rcases hdeg _ _ _ _ _ h1 h2 h3 h4 with h | h | h | h | h | h
    · exact hinj _ _ (by omega) (by omega) (by omega) h
    · exact hnot _ k hk h
    · exact hnot _ l hl h
    · exact hnot _ k hk h
    · exact hnot _ l hl h
    · exact hvinj k l hkl hl h
  -- the bound from the shortest walk
  have hgeo : ∀ k l, k < l → l ≤ 6 →
      p l ≤ p k + (l - k) + 2 ∧ p k ≤ p l + (l - k) + 2 := by
    intro k l hkl hl
    have hk : k ≤ 6 := by omega
    obtain ⟨q, hq, _⟩ := exists_walk_of_fn (K := K) v (l - k) k
      (fun m _ hm => hvadj m (by omega))
    have hend : v (k + (l - k)) = v l := by rw [show k + (l - k) = l by omega]
    let W : K.Walk (A.getVert (p k)) (A.getVert (p l)) :=
      Walk.cons (hatt k hk).symm ((q.copy rfl hend).concat (hatt l hl))
    have hW : W.length = (l - k) + 2 := by
      simp only [W, Walk.length_cons, Walk.length_concat, Walk.length_copy, hq]
    have h1 := geodesic_le A hshort (hp k hk).2.le (hp l hl).2.le W
    have h2 := geodesic_le A hshort (hp l hl).2.le (hp k hk).2.le W.reverse
    rw [Walk.length_reverse] at h2
    rw [hW] at h1 h2
    omega
  -- consecutive vertices of the rail: the positions differ by at least two
  have hstep : ∀ k, k < 6 → p k + 2 ≤ p (k + 1) ∨ p (k + 1) + 2 ≤ p k := by
    intro k hk
    by_contra hcon
    have hne' := hne k (k + 1) (by omega) (by omega)
    have hk6 : k ≤ 6 := by omega
    have hk6' : k + 1 ≤ 6 := by omega
    rcases (show p (k + 1) = p k + 1 ∨ p k = p (k + 1) + 1 by omega) with h | h
    · refine no_short_closed hg (seq5 (A.getVert (p k)) (v k) (v (k + 1))
        (A.getVert (p (k + 1))) (A.getVert (p k))) 4 (by norm_num) (by norm_num) rfl ?_ ?_
      · intro m hm
        interval_cases m
        · exact (hatt k hk6).symm
        · exact hvadj k hk
        · exact hatt (k + 1) hk6'
        · show K.Adj (A.getVert (p (k + 1))) (A.getVert (p k))
          rw [h]
          exact (A.adj_getVert_succ (hp k hk6).2).symm
      · intro m hm
        have hm' : m ≤ 2 := by omega
        interval_cases m
        · exact fun h' => hnot _ (k + 1) hk6' h'.symm
        · exact fun h' => hnot _ k hk6 h'
        · exact fun h' => hnot _ (k + 1) hk6' h'
    · refine no_short_closed hg (seq5 (A.getVert (p k)) (v k) (v (k + 1))
        (A.getVert (p (k + 1))) (A.getVert (p k))) 4 (by norm_num) (by norm_num) rfl ?_ ?_
      · intro m hm
        interval_cases m
        · exact (hatt k hk6).symm
        · exact hvadj k hk
        · exact hatt (k + 1) hk6'
        · show K.Adj (A.getVert (p (k + 1))) (A.getVert (p k))
          rw [h]
          exact A.adj_getVert_succ (hp (k + 1) hk6').2
      · intro m hm
        have hm' : m ≤ 2 := by omega
        interval_cases m
        · exact fun h' => hnot _ (k + 1) hk6' h'.symm
        · exact fun h' => hnot _ k hk6 h'
        · exact fun h' => hnot _ (k + 1) hk6' h'
  exact rail_bound p hne hgeo hstep

end Geodesic

end Erdos1016.ExactMaximum.GirthFive
