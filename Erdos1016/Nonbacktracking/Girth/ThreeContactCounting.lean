import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Tactic
import Mathlib.Combinatorics.SimpleGraph.Metric
import Erdos1016.Nonbacktracking.Walks.ShortPathUniqueness

set_option autoImplicit false

/-!
# Section 8.1 three-contact layer count

This isolates the finite branching calculation in Lemma 8.1. `level k` is
the size of the kth breadth-first layer in a collision-free cubic ball, and
`tokens k` counts outgoing boundary tokens based at that layer. The remaining
graph-theoretic step is to derive these layer equations from girth and the
ambient degree-three condition.
-/

namespace Erdos1016.Proof.ThreeContactCounting

open Erdos1016.Nonbacktracking.ShortWalks

private theorem isPath_reduced {V : Type*} {J : SimpleGraph V}
    {u v : V} (p : J.Walk u v) (hp : p.IsPath) :
    Erdos1016.Nonbacktracking.ShortWalks.Reduced p := by
  induction p with
  | nil => trivial
  | @cons u v w huv p ih =>
      rw [SimpleGraph.Walk.cons_isPath_iff] at hp
      constructor
      · exact ih hp.1
      · intro _ heq
        exact hp.2 (heq ▸ p.getVert_mem_support 1)

/-- In a graph of girth greater than `D`, a target at distance at most `r`
has a unique shortest walk from the root whenever `2r≤D`. -/
theorem shortest_walk_unique_of_girth
    {V : Type*} [DecidableEq V] (J : SimpleGraph V) (D r : ℕ)
    (hg : GirthGreater J D) (h2r : 2 * r ≤ D)
    {u v : V} (p q : J.Walk u v)
    (hp : p.length = J.dist u v) (hq : q.length = J.dist u v)
    (hr : J.dist u v ≤ r) : p = q := by
  have hppath : p.IsPath := p.isPath_of_length_eq_dist hp
  have hqpath : q.IsPath := q.isPath_of_length_eq_dist hq
  have hpred := isPath_reduced p hppath
  have hqred := isPath_reduced q hqpath
  apply reduced_walk_unique_of_girth D hg p q hpred hqred
  rw [hp, hq]
  omega

/-- An edge in a connected induced region joins only equal or consecutive
breadth-first layers. -/
theorem adjacent_distances_within_one
    {V : Type*} [DecidableEq V] (J : SimpleGraph V)
    (hconn : J.Connected) (root u v : V) (huv : J.Adj u v) :
    J.dist root v ≤ J.dist root u + 1 ∧
      J.dist root u ≤ J.dist root v + 1 := by
  constructor
  · calc
      J.dist root v ≤ J.dist root u + J.dist u v := hconn.dist_triangle
      _ = J.dist root u + 1 := by simp [huv]
  · calc
      J.dist root u ≤ J.dist root v + J.dist v u := hconn.dist_triangle
      _ = J.dist root v + 1 := by simp [huv.symm]

/-- A vertex within radius `r` has at most one neighbor in the preceding
BFS sphere. Two such neighbors would give two geodesics of the same length
to that vertex, contrary to high-girth shortest-walk uniqueness. -/
theorem preceding_sphere_neighbor_unique_of_girth
    {V : Type*} [DecidableEq V] (J : SimpleGraph V)
    (hconn : J.Connected) (D r : ℕ)
    (hg : GirthGreater J D) (h2r : 2 * r ≤ D)
    (root v : V) (hv : J.dist root v ≤ r)
    (w₁ w₂ : V) (h₁ : J.Adj w₁ v) (h₂ : J.Adj w₂ v)
    (hd₁ : J.dist root w₁ + 1 = J.dist root v)
    (hd₂ : J.dist root w₂ + 1 = J.dist root v) : w₁ = w₂ := by
  obtain ⟨p₁, hp₁⟩ := hconn.exists_walk_length_eq_dist root w₁
  obtain ⟨p₂, hp₂⟩ := hconn.exists_walk_length_eq_dist root w₂
  let q₁ := p₁.concat h₁
  let q₂ := p₂.concat h₂
  have hq₁ : q₁.length = J.dist root v := by
    simp [q₁, hp₁, hd₁]
  have hq₂ : q₂.length = J.dist root v := by
    simp [q₂, hp₂, hd₂]
  have heq := shortest_walk_unique_of_girth J D r hg h2r q₁ q₂ hq₁ hq₂ hv
  have hpen₁ : q₁.penultimate = w₁ := by
    simpa [q₁] using SimpleGraph.Walk.penultimate_concat p₁ h₁
  have hpen₂ : q₂.penultimate = w₂ := by
    simpa [q₂] using SimpleGraph.Walk.penultimate_concat p₂ h₂
  calc
    w₁ = q₁.penultimate := hpen₁.symm
    _ = q₂.penultimate := by rw [heq]
    _ = w₂ := hpen₂

private theorem take_length_eq_of_le
    {V : Type*} {J : SimpleGraph V} {u v : V} (p : J.Walk u v) :
    ∀ i, i ≤ p.length → (p.take i).length = i := by
  induction p with
  | nil =>
      intro i hi
      have : i = 0 := by simpa using hi
      subst i
      rfl
  | @cons u v w huv p ih =>
      intro i hi
      cases i with
      | zero => rfl
      | succ i =>
          simp only [SimpleGraph.Walk.length_cons] at hi
          simp only [SimpleGraph.Walk.take, SimpleGraph.Walk.length_cons]
          exact congrArg Nat.succ (ih i (by omega))

private theorem dist_le_geodesic_prefix
    {V : Type*} {J : SimpleGraph V} {u v : V}
    (p : J.Walk u v) (i : ℕ) (hi : i ≤ p.length) :
    J.dist u (p.getVert i) ≤ i := by
  have h := J.dist_le (p.take i)
  rw [take_length_eq_of_le p i hi] at h
  exact h

private theorem endpoint_not_mem_geodesic_support
    {V : Type*} [DecidableEq V] {J : SimpleGraph V} {root u v : V}
    (p : J.Walk root u) (hp : p.length = J.dist root u)
    (huv : u ≠ v) (hd : J.dist root u = J.dist root v) :
    v ∉ p.support := by
  intro hv
  obtain ⟨i, heq, hi⟩ := SimpleGraph.Walk.mem_support_iff_exists_getVert.mp hv
  by_cases hieq : i = p.length
  · have hlast : p.getVert p.length = u := by simp
    have hcontra : u = v := by
      calc
        u = p.getVert p.length := hlast.symm
        _ = v := by simpa [hieq] using heq
    exact huv hcontra
  · have hilt : i < p.length := by omega
    have hprefix := dist_le_geodesic_prefix p i hi
    have hprefix' : J.dist root v ≤ i := by simpa [heq] using hprefix
    omega

private theorem isPath_concat_of_endpoint_not_mem
    {V : Type*} [DecidableEq V] {J : SimpleGraph V} {u v w : V}
    {p : J.Walk u v} (hp : p.IsPath) (hw : w ∉ p.support)
    (h : J.Adj v w) : (p.concat h).IsPath := by
  have hp' : p.support.Nodup := (SimpleGraph.Walk.isPath_def p).mp hp
  rw [SimpleGraph.Walk.isPath_def, SimpleGraph.Walk.support_concat, List.concat_eq_append]
  rw [List.nodup_append]
  simp [hp', hw]

/-- Adjacent vertices in a sphere below radius `r` cannot be in that same
sphere when girth exceeds `D ≥ 2r+1`. -/
theorem no_same_sphere_edge_of_girth
    {V : Type*} [DecidableEq V] (J : SimpleGraph V)
    (hconn : J.Connected) (D r : ℕ)
    (hg : GirthGreater J D) (hD : 2 * r + 1 ≤ D)
    (root u v : V) (huv : J.Adj u v)
    (hlevel : J.dist root u = J.dist root v)
    (hr : J.dist root u < r) : False := by
  obtain ⟨p, hp⟩ := hconn.exists_path_of_dist root u
  obtain ⟨q, hq⟩ := hconn.exists_path_of_dist root v
  have huvne : u ≠ v := J.ne_of_adj huv
  have hvNotP := endpoint_not_mem_geodesic_support p hp.2 huvne hlevel
  have hconcatPath := isPath_concat_of_endpoint_not_mem hp.1 hvNotP huv
  let q' := p.concat huv
  let E₁ := p.edges.toFinset
  let E₂ := q.edges.toFinset
  let S := E₁ ∪ E₂ ∪ {s(u, v)}
  have hScard : S.card ≤ D := by
    have h₁ : E₁.card ≤ p.length := by simpa [E₁] using List.toFinset_card_le p.edges
    have h₂ : E₂.card ≤ q.length := by simpa [E₂] using List.toFinset_card_le q.edges
    calc
      S.card ≤ (E₁.card + E₂.card) + 1 := by
        dsimp [S]
        calc
          (E₁ ∪ E₂ ∪ {s(u, v)}).card ≤ (E₁ ∪ E₂).card + 1 := by
            simpa using Finset.card_union_le (E₁ ∪ E₂) ({s(u, v)} : Finset (Sym2 V))
          _ ≤ (E₁.card + E₂.card) + 1 := by
            exact Nat.add_le_add_right (Finset.card_union_le E₁ E₂) 1
      _ ≤ (p.length + q.length) + 1 := by omega
      _ = (J.dist root u + J.dist root v) + 1 := by rw [hp.2, hq.2]
      _ ≤ 2 * r + 1 := by omega
      _ ≤ D := hD
  have hforest := edgeSpan_acyclic D hg S hScard
  have hpEdges : ∀ e ∈ p.edges, e ∈ S := by
    intro e he
    exact Finset.mem_union_left _ (Finset.mem_union_left _ (List.mem_toFinset.2 he))
  have hqEdges : ∀ e ∈ q.edges, e ∈ S := by
    intro e he
    exact Finset.mem_union_left _ (Finset.mem_union_right _ (List.mem_toFinset.2 he))
  have hconcatEdges : ∀ e ∈ q'.edges, e ∈ S := by
    intro e he
    rw [SimpleGraph.Walk.edges_concat] at he
    simp only [List.concat_eq_append, List.mem_append, List.mem_singleton] at he
    rcases he with he | he
    · exact Finset.mem_union_left _ (Finset.mem_union_left _ (List.mem_toFinset.2 he))
    · have : e = s(u, v) := by simpa [q'] using he
      subst e
      exact Finset.mem_union_right _ (Finset.mem_singleton_self _)
  let pSpan := restrictWalk S q hqEdges
  let qSpan := restrictWalk S q' hconcatEdges
  have hpSpanPath : pSpan.IsPath := by
    apply reduced_isPath_of_acyclic hforest
    exact reduced_restrictWalk S q hqEdges (isPath_reduced q hq.1)
  have hqSpanPath : qSpan.IsPath := by
    apply reduced_isPath_of_acyclic hforest
    exact reduced_restrictWalk S q' hconcatEdges (isPath_reduced q' hconcatPath)
  have hspanEq : pSpan = qSpan :=
    congrArg Subtype.val (hforest.path_unique ⟨pSpan, hpSpanPath⟩ ⟨qSpan, hqSpanPath⟩)
  have hmap := congrArg (fun w => w.mapLe (edgeSpan_le S)) hspanEq
  have hwalk : q = q' := by
    simpa only [pSpan, qSpan, restrictWalk_mapLe] using hmap
  have hlen := congrArg SimpleGraph.Walk.length hwalk
  simp only [q', SimpleGraph.Walk.length_concat, hq.2, hp.2, hlevel] at hlen
  omega


private def layerTokens (tokens : ℕ → ℝ) (k : ℕ) : ℝ :=
  ∑ i ∈ Finset.range k, tokens i

/-- If at most two boundary tokens occur before depth `r`, a cubic layer
process with no collisions through that depth has at least `2^r` vertices. -/
theorem ball_size_lower_bound_of_cubic_layers
    (level tokens : ℕ → ℝ) (r : ℕ)
    (hroot : level 0 = 1)
    (hfirst : level 1 = 3 - tokens 0)
    (hstep : ∀ k, 1 ≤ k → k < r → level (k + 1) = 2 * level k - tokens k)
    (htokenNonneg : ∀ k, 0 ≤ tokens k)
    (hprefix : ∀ k, k ≤ r → layerTokens tokens k ≤ 2) :
    2 ^ r ≤ ∑ k ∈ Finset.range (r + 1), level k := by
  have hlevel : ∀ k, 1 ≤ k → k ≤ r →
      2 ^ (k - 1) * (3 - layerTokens tokens k) ≤ level k := by
    intro k
    induction k using Nat.strong_induction_on with
    | h k ih =>
      intro hk hkR
      by_cases hkOne : k = 1
      · subst k
        have htok : layerTokens tokens 1 = tokens 0 := by simp [layerTokens]
        change (2 : ℝ) ^ (1 - 1) * (3 - layerTokens tokens 1) ≤ level 1
        rw [hfirst, htok]
        norm_num
      · have hkTwo : 2 ≤ k := by omega
        have hprev := ih (k - 1) (by omega) (by omega) (by omega)
        have hsum : layerTokens tokens k =
            layerTokens tokens (k - 1) + tokens (k - 1) := by
          rw [show k = (k - 1) + 1 by omega, layerTokens, Finset.sum_range_succ]
          rfl
        have hexp : (2 : ℝ) ^ (k - 1) =
            2 * (2 : ℝ) ^ ((k - 1) - 1) := by
          have hidx : (k - 1 - 1) + 1 = k - 1 := by omega
          calc
            (2 : ℝ) ^ (k - 1) = (2 : ℝ) ^ (((k - 1) - 1) + 1) := by rw [hidx]
            _ = (2 : ℝ) ^ ((k - 1) - 1) * 2 := by rw [pow_succ]
            _ = 2 * (2 : ℝ) ^ ((k - 1) - 1) := by ring
        have hP : 1 ≤ (2 : ℝ) ^ ((k - 1) - 1) := one_le_pow₀ (by norm_num)
        have hprevsum : layerTokens tokens (k - 1) ≤ 2 :=
          hprefix (k - 1) (by omega)
        have hmul : 0 ≤
            ((2 : ℝ) * (2 : ℝ) ^ ((k - 1) - 1) - 1) * tokens (k - 1) :=
          mul_nonneg (by nlinarith) (htokenNonneg (k - 1))
        have hrec : level k = 2 * level (k - 1) - tokens (k - 1) := by
          rw [show k = (k - 1) + 1 by omega]
          exact hstep (k - 1) (by omega) (by omega)
        rw [hrec, hsum, hexp]
        nlinarith [mul_le_mul_of_nonneg_left hprev (by norm_num : (0 : ℝ) ≤ 2)]
  have hball : ∀ k, k ≤ r →
      (2 : ℝ) ^ k ≤ ∑ i ∈ Finset.range (k + 1), level i := by
    intro k
    induction k with
    | zero =>
        intro _
        simp [hroot]
    | succ k ih =>
        intro hkR
        have hprev := ih (by omega)
        have hlast := hlevel (k + 1) (by omega) (by omega)
        have hlast' : (2 : ℝ) ^ k ≤ level (k + 1) := by
          have hprefix' := hprefix (k + 1) (by omega)
          have hnonneg : 1 ≤ 3 - layerTokens tokens (k + 1) := by linarith
          have hexp : (k + 1) - 1 = k := by omega
          rw [hexp] at hlast
          nlinarith [mul_le_mul_of_nonneg_left hnonneg (show 0 ≤ (2 : ℝ) ^ k by positivity)]
        rw [show k + 1 + 1 = (k + 1) + 1 by omega, Finset.sum_range_succ]
        calc
          (2 : ℝ) ^ (k + 1) = (2 : ℝ) ^ k * 2 := by rw [pow_succ]
          _ ≤ (∑ i ∈ Finset.range (k + 1), level i) + level (k + 1) := by linarith
  exact hball r (by omega)

/-- Consequently, if the vertex budget is smaller than `2^r`, the first `r`
layers of the rooted search must contain at least three boundary tokens. -/
theorem three_tokens_before_radius_of_small_order
    (level tokens : ℕ → ℝ) (r : ℕ) (n : ℝ)
    (hroot : level 0 = 1)
    (hfirst : level 1 = 3 - tokens 0)
    (hstep : ∀ k, 1 ≤ k → k < r → level (k + 1) = 2 * level k - tokens k)
    (htokenNonneg : ∀ k, 0 ≤ tokens k)
    (hvolume : (∑ k ∈ Finset.range (r + 1), level k) ≤ n)
    (hsmall : n < 2 ^ r) :
    2 < layerTokens tokens r := by
  by_contra h
  have htotal : layerTokens tokens r ≤ 2 := le_of_not_gt h
  have hprefix : ∀ k, k ≤ r → layerTokens tokens k ≤ 2 := by
    intro k hk
    have hsubset : Finset.range k ⊆ Finset.range r := Finset.range_mono hk
    have hsum := Finset.sum_le_sum_of_subset_of_nonneg hsubset
      (by intro j hj hnot; exact htokenNonneg j)
    simpa [layerTokens] using hsum.trans htotal
  have hball := ball_size_lower_bound_of_cubic_layers
    level tokens r hroot hfirst hstep htokenNonneg hprefix
  linarith

end Erdos1016.Proof.ThreeContactCounting
