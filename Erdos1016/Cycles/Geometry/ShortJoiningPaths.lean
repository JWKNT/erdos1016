import Erdos1016.Nonbacktracking.Walks.ShortPathUniqueness
import Mathlib.Data.Fintype.Card
import Mathlib.Tactic

set_option autoImplicit false

/-! Short joining paths between two disjoint vertex sets are determined by
 their endpoint blocks. The proof extends each actual path to fixed block
 representatives and uses girth; no path-count assumption is introduced. -/
noncomputable section
namespace Erdos1016.Proof.ShortJoiningPaths
open SimpleGraph
open Erdos1016.Nonbacktracking.ShortWalks

variable {V : Type*} {G : SimpleGraph V}

theorem isPath_reduced {u v : V} (p : G.Walk u v) (hp : p.IsPath) : Reduced p := by
  induction p with
  | nil => trivial
  | @cons u v w huv p ih =>
      rw [Walk.cons_isPath_iff] at hp
      exact ⟨ih hp.1, fun _ heq => hp.2 (heq ▸ p.getVert_mem_support 1)⟩

/-- Concatenating paths that meet only at their common endpoint is a path. -/
theorem append_isPath_of_only_common_endpoint {u v w : V}
    (p : G.Walk u v) (q : G.Walk v w) (hp : p.IsPath) (hq : q.IsPath)
    (hmeet : ∀ x, x ∈ p.support → x ∈ q.support → x = v) :
    (p.append q).IsPath := by
  rw [Walk.isPath_def, Walk.support_append, List.nodup_append]
  have hqn : q.support.Nodup := hq.support_nodup
  have hvnot : v ∉ q.support.tail := by
    rw [q.support_eq_cons, List.nodup_cons] at hqn
    exact hqn.1
  refine ⟨hp.support_nodup, hq.support_nodup.tail, ?_⟩
  intro x hxp hxq
  have hxv := hmeet x hxp (List.mem_of_mem_tail hxq)
  exact hvnot (hxv ▸ hxq)

/-- Padding a joining path by paths inside its two disjoint boundary sets
 creates a simple path between the block representatives. -/
theorem padded_isPath (A B : Set V) (hAB : Disjoint A B)
    {a u v b : V} (p : G.Walk a u) (q : G.Walk u v) (r : G.Walk v b)
    (hp : p.IsPath) (hq : q.IsPath) (hr : r.IsPath)
    (hpA : ∀ x ∈ p.support, x ∈ A) (hrB : ∀ x ∈ r.support, x ∈ B)
    (hqA : ∀ x ∈ q.support, x ∈ A → x = u)
    (hqB : ∀ x ∈ q.support, x ∈ B → x = v) :
    ((p.append q).append r).IsPath := by
  have hpq := append_isPath_of_only_common_endpoint p q hp hq
    (fun x hxp hxq => hqA x hxq (hpA x hxp))
  apply append_isPath_of_only_common_endpoint (p.append q) r hpq hr
  intro x hxpq hxr
  rcases (Walk.mem_support_append_iff p q).mp hxpq with hxp | hxq
  · exact False.elim (Set.disjoint_left.mp hAB (hpA x hxp) (hrB x hxr))
  · exact hqB x hxq (hrB x hxr)

/-- A family of short reduced walks with a distinguishing edge injects into
 its pair of endpoint labels. Endpoints are the actual label representatives. -/
theorem blockPair_injective_of_marked_reduced_walks
    [DecidableEq V] {I A B : Type*}
    (D H : ℕ) (hg : GirthGreater G D) (hH : 2 * H ≤ D)
    (left : I → A) (right : I → B) (repA : A → V) (repB : B → V)
    (p : ∀ i, G.Walk (repA (left i)) (repB (right i)))
    (hred : ∀ i, Reduced (p i)) (hlen : ∀ i, (p i).length ≤ H)
    (mark : I → Sym2 V) (hmark : ∀ i, mark i ∈ (p i).edges)
    (hmark_unique : ∀ i j, mark i ∈ (p j).edges → i = j) :
    Function.Injective (fun i => (left i, right i)) := by
  intro i j hij
  have ha := congrArg Prod.fst hij
  have hb := congrArg Prod.snd hij
  let q := (p j).copy (congrArg repA ha).symm (congrArg repB hb).symm
  have hqred : Reduced q := (reduced_copy _ _ _).mpr (hred j)
  have hqlen : q.length = (p j).length := by simp [q]
  have heq : p i = q := reduced_walk_unique_of_girth D hg (p i) q
    (hred i) hqred (by rw [hqlen]; have := hlen i; have := hlen j; omega)
  apply hmark_unique i j
  have hm := hmark i
  rw [heq] at hm
  simpa [q] using hm

/-- The resulting cardinal bound depends only on the numbers of blocks. -/
theorem card_le_block_product_of_marked_reduced_walks
    [DecidableEq V] {I A B : Type*} [Fintype I] [Fintype A] [Fintype B]
    (D H : ℕ) (hg : GirthGreater G D) (hH : 2 * H ≤ D)
    (left : I → A) (right : I → B) (repA : A → V) (repB : B → V)
    (p : ∀ i, G.Walk (repA (left i)) (repB (right i)))
    (hred : ∀ i, Reduced (p i)) (hlen : ∀ i, (p i).length ≤ H)
    (mark : I → Sym2 V) (hmark : ∀ i, mark i ∈ (p i).edges)
    (hmark_unique : ∀ i j, mark i ∈ (p j).edges → i = j) :
    Fintype.card I ≤ Fintype.card A * Fintype.card B := by
  simpa only [Fintype.card_prod] using Fintype.card_le_of_injective
    (fun i => (left i, right i))
    (blockPair_injective_of_marked_reduced_walks D H hg hH left right repA repB
      p hred hlen mark hmark hmark_unique)

private theorem first_edge_mem {u v : V} (p : G.Walk u v) (hp : ¬p.Nil) :
    s(u, p.snd) ∈ p.edges := by
  cases p with
  | nil => exact (hp Walk.Nil.nil).elim
  | cons h p => simp

/-- Actual simple joining paths, including direct edges, are counted by
 pairs of short boundary blocks. The joining paths have distinct starts;
 each stays off both boundary sets except at its own endpoints. Padding
 arcs lie inside those boundary sets. Neither a path-count bound nor a
 reduced-walk certificate is assumed. -/
theorem card_short_joining_paths_le_blocks
    [DecidableEq V] {I LA LB : Type*} [Fintype I] [Fintype LA] [Fintype LB]
    (A B : Set V) (hAB : Disjoint A B)
    (D t b : ℕ) (hg : GirthGreater G D) (hbudget : 2 * (t + 2 * b) ≤ D)
    (left : I → LA) (right : I → LB) (repA : LA → V) (repB : LB → V)
    (start finish : I → V) (hstart : Function.Injective start)
    (hstartA : ∀ i, start i ∈ A) (hfinishB : ∀ i, finish i ∈ B)
    (join : ∀ i, G.Walk (start i) (finish i))
    (join_path : ∀ i, (join i).IsPath) (join_length : ∀ i, (join i).length ≤ t)
    (join_A : ∀ i x, x ∈ (join i).support → x ∈ A → x = start i)
    (join_B : ∀ i x, x ∈ (join i).support → x ∈ B → x = finish i)
    (arcA : ∀ i, G.Walk (repA (left i)) (start i))
    (arcB : ∀ i, G.Walk (finish i) (repB (right i)))
    (arcA_path : ∀ i, (arcA i).IsPath) (arcB_path : ∀ i, (arcB i).IsPath)
    (arcA_length : ∀ i, (arcA i).length ≤ b)
    (arcB_length : ∀ i, (arcB i).length ≤ b)
    (arcA_inside : ∀ i x, x ∈ (arcA i).support → x ∈ A)
    (arcB_inside : ∀ i x, x ∈ (arcB i).support → x ∈ B) :
    Fintype.card I ≤ Fintype.card LA * Fintype.card LB := by
  let p := fun i => ((arcA i).append (join i)).append (arcB i)
  have hpath : ∀ i, (p i).IsPath := by
    intro i
    exact padded_isPath A B hAB (arcA i) (join i) (arcB i)
      (arcA_path i) (join_path i) (arcB_path i)
      (arcA_inside i) (arcB_inside i) (join_A i) (join_B i)
  have hnonil : ∀ i, ¬(join i).Nil := by
    intro i
    apply Walk.not_nil_of_ne
    intro heq
    exact Set.disjoint_left.mp hAB (hstartA i) (heq ▸ hfinishB i)
  have hsnd_notA : ∀ i, (join i).snd ∉ A := by
    intro i hi
    have heq := join_A i _ ((join i).getVert_mem_support 1) hi
    exact ((join i).adj_snd (hnonil i)).ne heq.symm
  let mark := fun i => s(start i, (join i).snd)
  apply card_le_block_product_of_marked_reduced_walks D (t + 2 * b) hg hbudget
    left right repA repB p (fun i => isPath_reduced _ (hpath i)) ?_ mark ?_ ?_
  · intro i
    dsimp [p]
    simp only [Walk.length_append]
    have := arcA_length i
    have := arcB_length i
    have := join_length i
    omega
  · intro i
    dsimp [p, mark]
    simp only [Walk.edges_append, List.mem_append]
    exact Or.inl (Or.inr (first_edge_mem (join i) (hnonil i)))
  · intro i j hij
    change s(start i, (join i).snd) ∈
      (((arcA j).append (join j)).append (arcB j)).edges at hij
    simp only [Walk.edges_append, List.mem_append] at hij
    rcases hij with (hA | hJ) | hB
    · exact False.elim (hsnd_notA i (arcA_inside j _
        ((arcA j).snd_mem_support_of_mem_edges hA)))
    · exact hstart (join_A j _ ((join j).fst_mem_support_of_mem_edges hJ) (hstartA i))
    · exact False.elim (Set.disjoint_left.mp hAB (hstartA i)
        (arcB_inside j _ ((arcB j).fst_mem_support_of_mem_edges hB)))

end Erdos1016.Proof.ShortJoiningPaths
