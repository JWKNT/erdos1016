import Erdos1016.Cycles.Geometry.ShortJoiningPaths
import Mathlib.Combinatorics.SimpleGraph.Acyclic
import Mathlib.Combinatorics.SimpleGraph.DegreeSum

set_option autoImplicit false

/-! Cubic induced trees have exactly two more boundary incidences than
 vertices. Attachments on two exterior sets yield short actual joining
 paths, with no assumption about a chosen path decomposition. -/
noncomputable section
namespace Erdos1016.Proof.CubicTreeBoundary
open SimpleGraph
open scoped BigOperators
open ShortJoiningPaths
local instance (p : Prop) : Decidable p := Classical.propDecidable p

variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V)

private theorem internal_degree_sum (F : Finset V)
    (htree : (G.induce (↑F : Set V)).IsTree) :
    (∑ v ∈ F, (G.neighborFinset v ∩ F).card) = 2 * (F.card - 1) := by
  classical
  let K := G.induce (↑F : Set V)
  have hdeg (v : ↑(↑F : Set V)) :
      K.degree v = (G.neighborFinset v.1 ∩ F).card := by
    calc
      K.degree v = (K.neighborFinset v).card := (K.card_neighborFinset_eq_degree v).symm
      _ = ((K.neighborFinset v).map (Function.Embedding.subtype (↑F : Set V))).card :=
        (Finset.card_map _).symm
      _ = _ := by
        congr 1
        ext w
        simp only [Finset.mem_map, Finset.mem_inter, SimpleGraph.mem_neighborFinset, K]
        constructor
        · rintro ⟨⟨z, hz⟩, hAdj, rfl⟩
          exact ⟨hAdj, hz⟩
        · rintro ⟨hAdj, hz⟩
          exact ⟨⟨w, hz⟩, hAdj, rfl⟩
  have hsum : (∑ v ∈ F, (G.neighborFinset v ∩ F).card) = ∑ v, K.degree v := by
    rw [Finset.sum_subtype F (by intro v; rfl)]
    exact Finset.sum_congr rfl (fun v hv => (hdeg ⟨v, by simpa using hv⟩).symm)
  rw [hsum, K.sum_degrees_eq_twice_card_edges]
  have hcard := htree.card_edgeFinset
  have hvertices : Fintype.card ↑(↑F : Set V) = F.card := Fintype.card_coe F
  change K.edgeFinset.card + 1 = _ at hcard
  rw [hvertices] at hcard
  omega

/-- The actual cut is counted once per edge at its endpoint in the tree. -/
theorem boundary_eq_card_add_two (F : Finset V)
    (htree : (G.induce (↑F : Set V)).IsTree)
    (hcubic : ∀ v ∈ F, G.degree v = 3) :
    (∑ v ∈ F, (G.neighborFinset v \ F).card) = F.card + 2 := by
  classical
  have hsplit : (∑ v ∈ F, G.degree v) =
      (∑ v ∈ F, (G.neighborFinset v ∩ F).card) +
        ∑ v ∈ F, (G.neighborFinset v \ F).card := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro v hv
    rw [Finset.card_inter_add_card_sdiff, G.card_neighborFinset_eq_degree]
  have hsum : (∑ v ∈ F, G.degree v) = 3 * F.card := by
    calc
      _ = ∑ _v ∈ F, 3 := Finset.sum_congr rfl hcubic
      _ = _ := by simp [Nat.mul_comm]
  have hint := internal_degree_sum G F htree
  have hpos : 0 < F.card := by
    obtain ⟨v⟩ := htree.1.nonempty
    exact Finset.card_pos.mpr ⟨v.1, v.2⟩
  omega

/-- Two attachments to a connected induced region give a simple joining
 path with all intermediate vertices in that region. Its length is at
 most one more than the number of region vertices. -/
theorem exists_joining_path_through_region (F : Finset V)
    (hconn : (G.induce (↑F : Set V)).Connected)
    {a b x y : V} (ha : a ∉ F) (hb : b ∉ F) (hab : a ≠ b)
    (hx : x ∈ F) (hy : y ∈ F) (hax : G.Adj a x) (hyb : G.Adj y b) :
    ∃ p : G.Walk a b, p.IsPath ∧ p.length ≤ F.card + 1 ∧
      ∀ v ∈ p.support, v = a ∨ v = b ∨ v ∈ F := by
  classical
  obtain ⟨q, hq⟩ := (hconn ⟨x, hx⟩ ⟨y, hy⟩).exists_isPath
  let inc : G.induce (↑F : Set V) →g G := (Embedding.induce (↑F : Set V)).toHom
  let r := q.map inc
  have hr : r.IsPath := (Walk.map_isPath_iff_of_injective Subtype.val_injective).mpr hq
  have hrF : ∀ v ∈ r.support, v ∈ F := by
    intro v hv
    change v ∈ (q.map inc).support at hv
    rw [Walk.support_map] at hv
    obtain ⟨z, hz, heq⟩ := List.mem_map.mp hv
    exact heq ▸ z.2
  have htail : (r.append hyb.toWalk).IsPath := by
    apply append_isPath_of_only_common_endpoint r hyb.toWalk hr (Walk.IsPath.of_adj hyb)
    intro v hvr hvlast
    rcases (show v = y ∨ v = b from by simpa using hvlast) with h | h
    · exact h
    · exact False.elim (hb (h ▸ hrF v hvr))
  have ha_not : a ∉ (r.append hyb.toWalk).support := by
    intro hav
    rcases (Walk.mem_support_append_iff r hyb.toWalk).mp hav with har | halast
    · exact ha (hrF a har)
    · have : a = y ∨ a = b := by simpa using halast
      rcases this with heq | heq
      · exact ha (heq ▸ hy)
      · exact hab heq
  let p := Walk.cons hax (r.append hyb.toWalk)
  refine ⟨p, (Walk.cons_isPath_iff _ _).mpr ⟨htail, ha_not⟩, ?_, ?_⟩
  · have hlen := hq.length_lt
    have hcard : Fintype.card ↑(↑F : Set V) = F.card := Fintype.card_coe F
    rw [hcard] at hlen
    simp only [p, Walk.length_cons, Walk.length_append, r, Walk.length_map]
    simpa using (show q.length + 1 + 1 ≤ F.card + 1 by omega)
  · intro v hv
    rcases List.mem_cons.mp hv with heq | hrest
    · exact Or.inl heq
    · rcases (Walk.mem_support_append_iff r hyb.toWalk).mp hrest with hvr | hvlast
      · exact Or.inr (Or.inr (hrF v hvr))
      · rcases (show v = y ∨ v = b from by simpa using hvlast) with heq | heq
        · exact Or.inr (Or.inr (heq ▸ hy))
        · exact Or.inr (Or.inl heq)

/-- For a cubic induced tree the joining path is shorter than its cut.
 In particular it has at most d edges when the cut has at most d edges. -/
theorem exists_joining_path_through_cubic_tree (F : Finset V)
    (htree : (G.induce (↑F : Set V)).IsTree)
    (hcubic : ∀ v ∈ F, G.degree v = 3)
    {a b x y : V} (ha : a ∉ F) (hb : b ∉ F) (hab : a ≠ b)
    (hx : x ∈ F) (hy : y ∈ F) (hax : G.Adj a x) (hyb : G.Adj y b) :
    ∃ p : G.Walk a b, p.IsPath ∧
      p.length < (∑ v ∈ F, (G.neighborFinset v \ F).card) ∧
      ∀ v ∈ p.support, v = a ∨ v = b ∨ v ∈ F := by
  obtain ⟨p, hp, hlen, hsup⟩ := exists_joining_path_through_region G F htree.1
    ha hb hab hx hy hax hyb
  refine ⟨p, hp, ?_, hsup⟩
  rw [boundary_eq_card_add_two G F htree hcubic]
  omega

end Erdos1016.Proof.CubicTreeBoundary
