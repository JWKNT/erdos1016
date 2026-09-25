import Mathlib.Combinatorics.SimpleGraph.DegreeSum
import Erdos1016.Nonbacktracking.Walks.CycleWords

set_option autoImplicit false

/-! A nonzero even edge word cannot be a forest. -/

noncomputable section
namespace Erdos1016.Proof.CycleSpaceForestZero
open Erdos1016 Erdos1016.Nonbacktracking Erdos1016.PhysicalGraph
local instance evenForestDecidable (p : Prop) : Decidable p := Classical.propDecidable p

/-- A physical edge word with zero boundary and acyclic selected support is
the zero word. -/
theorem word_eq_zero_of_boundary_zero_of_forest
    (G : PhysicalGraph) (x : G.Word)
    (hboundary : G.boundary x = 0) (hforest : G.IsForest x) : x = 0 := by
  classical
  funext e
  by_cases he : x e = 0
  · exact he
  · let S := G.selectedGraph x
    let u := G.src e
    let v := G.dst e
    have huv : u ≠ v := G.noLoops e
    have hadj : S.Adj u v := ⟨e, he, Or.inl ⟨rfl, rfl⟩⟩
    let c := S.connectedComponentMk u
    have hu : u ∈ c.supp := by
      simp [c, SimpleGraph.ConnectedComponent.mem_supp_iff]
    have hv : v ∈ c.supp := by
      exact (c.mem_supp_congr_adj hadj).mp hu
    let H := S.induce c.supp
    have hconn : H.Connected := c.connected_induce_supp
    have hacyc : H.IsAcyclic := by
      intro a p hp
      let inc : H →g S :=
        { toFun := fun z => z.1
          map_rel' := by intro z w hzw; exact hzw }
      have hmap : (p.map inc).IsCycle := by
        exact (SimpleGraph.Walk.map_isCycle_iff_of_injective Subtype.val_injective).2 hp
      exact hforest (p.map inc) hmap
    have htree : H.IsTree := ⟨hconn, hacyc⟩
    have htreecard : Finset.card H.edgeFinset + 1 = Fintype.card (↑c.supp) := by
      simpa using htree.card_edgeFinset
    have hneigh (w : ↑c.supp) : ∃ z : ↑c.supp, H.Adj w z := by
      by_cases hwu : w.1 = u
      · refine ⟨⟨v, hv⟩, ?_⟩
        change S.Adj w.1 v
        simpa [hwu] using hadj
      · obtain ⟨p⟩ := hconn w ⟨u, hu⟩
        cases p with
        | nil => exact (hwu rfl).elim
        | cons hfirst p => exact ⟨_, hfirst⟩
    have hdegree_eq (w : ↑c.supp) : H.degree w = G.selectedDegree x w.1 := by
      let f : H.neighborSet w ≃ S.neighborSet w.1 := {
        toFun := fun z => ⟨z.1.1, by
          change S.Adj w.1 z.1.1
          exact z.2⟩
        invFun := fun z => ⟨⟨z.1, (c.mem_supp_congr_adj z.2).mp w.2⟩, by
          change S.Adj w.1 z.1
          exact z.2⟩
        left_inv := by intro z; apply Subtype.ext; rfl
        right_inv := by intro z; apply Subtype.ext; rfl }
      calc
        H.degree w = Fintype.card (H.neighborSet w) := by
          symm
          rw [SimpleGraph.card_neighborSet_eq_degree]
        _ = Fintype.card (S.neighborSet w.1) := Fintype.card_congr f
        _ = (S.neighborSet w.1).ncard := by
          rw [Set.ncard_eq_toFinset_card', Set.toFinset_card]
        _ = G.selectedDegree x w.1 :=
          (selectedDegree_eq_neighbor_ncard G x w.1).symm
    have hdegree_even (w : ↑c.supp) : 2 ∣ H.degree w := by
      have hbit : (G.selectedDegree x w.1 : F₂) = 0 := by
        calc
          (G.selectedDegree x w.1 : F₂) = G.boundary x w.1 :=
            (boundary_eq_selectedDegree_cast G x w.1).symm
          _ = 0 := congrFun hboundary w.1
      have hdiv : 2 ∣ G.selectedDegree x w.1 :=
        (ZMod.natCast_zmod_eq_zero_iff_dvd _ 2).mp hbit
      rw [hdegree_eq w]
      exact hdiv
    have hdegree_ge_two (w : ↑c.supp) : 2 ≤ H.degree w := by
      have hpos : 0 < H.degree w := by
        rw [SimpleGraph.degree_pos_iff_exists_adj]
        exact hneigh w
      obtain ⟨k, hk⟩ := hdegree_even w
      omega
    have hsum_lower : 2 * Fintype.card (↑c.supp) ≤
        ∑ w : ↑c.supp, H.degree w := by
      calc
        2 * Fintype.card (↑c.supp) = ∑ _w : ↑c.supp, 2 := by
          simp
          omega
        _ ≤ ∑ w : ↑c.supp, H.degree w :=
          Finset.sum_le_sum fun w _ => hdegree_ge_two w
    have hsum := H.sum_degrees_eq_twice_card_edges
    rw [hsum] at hsum_lower
    omega

end Erdos1016.Proof.CycleSpaceForestZero
