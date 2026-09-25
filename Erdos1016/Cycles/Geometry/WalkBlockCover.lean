import Erdos1016.Cycles.Geometry.ShortJoiningPaths

set_option autoImplicit false

/-! Consecutive blocks along actual walks supply short padding arcs.
Together with high-girth uniqueness this gives a concrete length-based
bound on short paths joining two disjoint cycle supports. -/
noncomputable section
namespace Erdos1016.Proof.ShortJoiningPaths
open SimpleGraph
open Erdos1016.Nonbacktracking.ShortWalks

variable {V : Type*} {G : SimpleGraph V}

/-- The segment starting at index `a` and extending `k` steps has at most
 `k` edges and stays inside the original walk, even beyond its endpoint. -/
theorem exists_short_segment {u v : V} (p : G.Walk u v) (a k : ℕ) :
    ∃ q : G.Walk (p.getVert a) (p.getVert (a + k)),
      q.length ≤ k ∧ ∀ x ∈ q.support, x ∈ p.support := by
  induction p generalizing a k with
  | nil =>
      exact ⟨Walk.nil, Nat.zero_le _, fun x hx => hx⟩
  | @cons u v w huv p ih =>
      cases a with
      | zero =>
          cases k with
          | zero => exact ⟨Walk.nil, le_rfl, by simp⟩
          | succ k =>
              obtain ⟨q, hlen, hsup⟩ := ih 0 k
              let r := q.copy (p.getVert_zero)
                (show p.getVert (0 + k) = (Walk.cons huv p).getVert (0 + (k + 1)) by
                  simp only [Nat.zero_add, Walk.getVert_cons_succ])
              refine ⟨Walk.cons huv r, ?_, ?_⟩
              · simpa only [r, Walk.length_cons, Walk.length_copy, Nat.succ_eq_add_one] using Nat.succ_le_succ hlen
              · intro x hx
                rcases List.mem_cons.mp hx with rfl | hx
                · exact List.mem_cons_self
                · exact List.mem_cons_of_mem _ (hsup x (by simpa [r] using hx))
      | succ a =>
          obtain ⟨q, hlen, hsup⟩ := ih a k
          have hend : p.getVert (a + k) = (Walk.cons huv p).getVert (a + 1 + k) := by
            rw [show a + 1 + k = (a + k) + 1 by omega]
            rfl
          let r := q.copy rfl hend
          refine ⟨r, ?_, ?_⟩
          · simpa [r] using hlen
          · intro x hx
            exact List.mem_cons_of_mem _ (hsup x (by simpa [r] using hx))

/-- Divide the vertex positions of a walk into consecutive blocks. Each
 vertex has an actual simple path of at most `b` edges from its block's
 representative, using only vertices of the original walk. -/
theorem exists_walk_block_cover [DecidableEq V]
    {u v : V} (p : G.Walk u v) (b : ℕ) (hb : 0 < b) :
    ∃ (label : {x // x ∈ p.support} → Fin (p.length / b + 1))
      (rep : Fin (p.length / b + 1) → V),
      ∀ x : {x // x ∈ p.support},
        ∃ q : G.Walk (rep (label x)) x.1,
          q.IsPath ∧ q.length ≤ b ∧ ∀ z ∈ q.support, z ∈ p.support := by
  have hindex : ∀ x : {x // x ∈ p.support},
      ∃ k, p.getVert k = x.1 ∧ k ≤ p.length := by
    intro x
    exact Walk.mem_support_iff_exists_getVert.mp x.2
  choose index hval hbound using hindex
  let label : {x // x ∈ p.support} → Fin (p.length / b + 1) :=
    fun x => ⟨index x / b, Nat.lt_succ_of_le (Nat.div_le_div_right (hbound x))⟩
  let rep : Fin (p.length / b + 1) → V := fun a => p.getVert (a.1 * b)
  refine ⟨label, rep, ?_⟩
  intro x
  obtain ⟨q, hlen, hsup⟩ := exists_short_segment p (index x / b * b) (index x % b)
  have hend : p.getVert (index x / b * b + index x % b) = x.1 := by
    rw [Nat.mul_comm (index x / b) b, Nat.div_add_mod, hval]
  let r := q.copy rfl hend
  refine ⟨r.bypass, r.bypass_isPath, ?_, ?_⟩
  · calc
      r.bypass.length ≤ r.length := r.length_bypass_le
      _ = q.length := by simp [r]
      _ ≤ index x % b := hlen
      _ ≤ b := (Nat.mod_lt _ hb).le
  · intro z hz
    apply hsup z
    simpa [r] using r.support_bypass_subset hz

/-- Concrete block count for actual boundary walks. No partition or
 short-padding-path hypotheses remain: those paths are constructed above.
 This applies in particular when the two boundary walks are simple cycles. -/
theorem card_short_joining_paths_le_length_blocks
    [DecidableEq V] {I : Type*} [Fintype I]
    {a a' b b' : V} (A : G.Walk a a') (B : G.Walk b b')
    (hAB : Disjoint {x | x ∈ A.support} {x | x ∈ B.support})
    (D t q : ℕ) (hq : 0 < q) (hg : GirthGreater G D)
    (hbudget : 2 * (t + 2 * q) ≤ D)
    (start finish : I → V) (hstart : Function.Injective start)
    (hstartA : ∀ i, start i ∈ A.support) (hfinishB : ∀ i, finish i ∈ B.support)
    (join : ∀ i, G.Walk (start i) (finish i))
    (join_path : ∀ i, (join i).IsPath) (join_length : ∀ i, (join i).length ≤ t)
    (join_A : ∀ i x, x ∈ (join i).support → x ∈ A.support → x = start i)
    (join_B : ∀ i x, x ∈ (join i).support → x ∈ B.support → x = finish i) :
    Fintype.card I ≤ (A.length / q + 1) * (B.length / q + 1) := by
  obtain ⟨labelA, repA, harcA⟩ := exists_walk_block_cover A q hq
  obtain ⟨labelB, repB, harcB⟩ := exists_walk_block_cover B q hq
  choose arcA arcA_path arcA_length arcA_inside using harcA
  choose arcB arcB_path arcB_length arcB_inside using harcB
  let start' : I → {x // x ∈ A.support} := fun i => ⟨start i, hstartA i⟩
  let finish' : I → {x // x ∈ B.support} := fun i => ⟨finish i, hfinishB i⟩
  simpa only [Fintype.card_fin] using card_short_joining_paths_le_blocks
    {x | x ∈ A.support} {x | x ∈ B.support} hAB D t q hg hbudget
    (fun i => labelA (start' i)) (fun i => labelB (finish' i)) repA repB
    start finish hstart hstartA hfinishB join join_path join_length join_A join_B
    (fun i => arcA (start' i)) (fun i => (arcB (finish' i)).reverse)
    (fun i => arcA_path (start' i)) (fun i => (arcB_path (finish' i)).reverse)
    (fun i => arcA_length (start' i))
    (fun i => by simpa using arcB_length (finish' i))
    (fun i => arcA_inside (start' i))
    (fun i z hz => arcB_inside (finish' i) z (by simpa using hz))

/-- The concrete block count has the claimed quadratic scale, with an
 explicit universal constant. This controls the integer floor in D/8. -/
theorem length_blocks_le_ratio (n L D : ℕ) (hD : 8 ≤ D)
    (hn : n ≤ L) (hDL : D ≤ L) :
    ((n / (D / 8) + 1 : ℕ) : ℝ) ≤ 17 * (L : ℝ) / D := by
  have hq : 1 ≤ D / 8 := by omega
  have hDq : D ≤ 16 * (D / 8) := by
    have := Nat.mod_add_div D 8
    have := Nat.mod_lt D (by omega : 0 < 8)
    omega
  have hdiv := Nat.div_mul_le_self n (D / 8)
  have hmul := Nat.mul_le_mul_left (n / (D / 8)) hDq
  have hfin : (n / (D / 8) + 1) * D ≤ 17 * L := by nlinarith
  apply (le_div_iff₀ (by exact_mod_cast (show 0 < D by omega))).mpr
  exact_mod_cast hfin

theorem length_block_product_le_quadratic (m n L D : ℕ) (hD : 8 ≤ D)
    (hm : m ≤ L) (hn : n ≤ L) (hDL : D ≤ L) :
    (((m / (D / 8) + 1) * (n / (D / 8) + 1) : ℕ) : ℝ) ≤
      289 * ((L : ℝ) / D) ^ 2 := by
  have hm' := length_blocks_le_ratio m L D hD hm hDL
  have hn' := length_blocks_le_ratio n L D hD hn hDL
  have h := mul_le_mul hm' hn' (by positivity) (by positivity)
  push_cast at h ⊢
  convert h using 1 <;> ring

theorem eighth_block_budget (D t : ℕ) (ht : 4 * t ≤ D) :
    2 * (t + 2 * (D / 8)) ≤ D := by
  have := Nat.div_mul_le_self D 8
  omega

end Erdos1016.Proof.ShortJoiningPaths
