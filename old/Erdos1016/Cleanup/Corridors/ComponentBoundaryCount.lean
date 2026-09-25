import Erdos1016.Cleanup.Protection.UnprotectedDegreeTwoAcyclicity
import Erdos1016.Cleanup.Corridors.TreeIncidenceCount
import Mathlib.Combinatorics.SimpleGraph.Path

set_option autoImplicit false

noncomputable section

local instance {V : Type*} (H : SimpleGraph V) : DecidableRel H.Adj := Classical.decRel _
local instance {V : Type*} [Finite V] (H : SimpleGraph V)
    (c : H.ConnectedComponent) : Fintype c.supp := by
  classical
  letI : Fintype V := Fintype.ofFinite V
  letI : DecidablePred (fun v : V => v ∈ c.supp) := fun v =>
    Classical.propDecidable _
  exact Subtype.fintype _

namespace Erdos1016.Proof.ComponentBoundaryCount

open Erdos1016
open SimpleGraph

/-- For a component of the induced subgraph on unprotected degree-two
vertices, its physical ambient boundary has exactly two incidences. -/
theorem component_boundaryCount_eq_two
    (G : PhysicalGraph) (P : Finset G.Vertex)
    (hconn : G.toSimpleGraph.Connected) (hP : P.Nonempty)
    (hdeg : ∀ v, v ∉ P → G.degree v = 2)
    (c : (G.toSimpleGraph.induce {v | v ∉ P}).ConnectedComponent) :
    DegreeTwoComponentCut.boundaryCount G.toSimpleGraph
      ((c.supp.toFinset).map (Function.Embedding.subtype {v | v ∉ P})) = 2 := by
  classical
  let U : Set G.Vertex := {v | v ∉ P}
  let H := G.toSimpleGraph
  let D : SimpleGraph U := H.induce U
  let S : Finset U := c.supp.toFinset
  have hSset : (↑S : Set U) = c.supp := by
    ext x
    simp [S]
  let emb : U ↪ G.Vertex := Function.Embedding.subtype U
  let C : Finset G.Vertex := S.map emb
  have hacycU : D.IsAcyclic := by
    exact Erdos1016.Proof.UnprotectedDegreeTwoAcyclicity.induced_unprotected_isAcyclic
      G P hconn hP hdeg
  have hacycC : (D.induce c.supp).IsAcyclic := by
    intro x p hp
    let f : D.induce c.supp ↪g D := @SimpleGraph.Embedding.induce U D c.supp
    have hc : (p.map f.toHom).IsCycle :=
      (SimpleGraph.Walk.map_isCycle_iff_of_injective f.injective).2 hp
    exact hacycU (p.map f.toHom) hc
  have hconnC : (D.induce (↑S : Set U)).Connected := by
    rw [hSset]
    exact c.connected_induce_supp
  have hacycTree : (D.induce (↑S : Set U)).IsAcyclic := by
    rw [hSset]
    exact hacycC
  have htreeInternal :=
    Erdos1016.Proof.TreeIncidenceCount.internal_incidence_sum_eq_tree_value
      D S hconnC hacycTree
  have hSpos : 0 < S.card := by
    obtain ⟨x, hx⟩ := c.nonempty_supp
    exact Finset.card_pos.mpr ⟨x, Set.mem_toFinset.mpr hx⟩
  have hCcard : C.card = S.card := by simp [C]
  have hCdeg (v : G.Vertex) (hv : v ∈ C) : G.degree v = 2 := by
    obtain ⟨x, hx, heq⟩ := Finset.mem_map.mp hv
    subst v
    have : x.1 ∉ P := x.2
    exact hdeg x.1 this
  have hCinternal_sum :
      (∑ v ∈ C, (H.neighborFinset v ∩ C).card) = 2 * (C.card - 1) := by
    have hsumDegree :
        (∑ v ∈ C, (H.neighborFinset v ∩ C).card) =
          ∑ x ∈ S, D.degree x := by
      symm
      refine Finset.sum_bij'
        (i := fun x _ => emb x)
        (j := fun v hv => Classical.choose (Finset.mem_map.mp hv))
        ?_ ?_ ?_ ?_ ?_
      · intro x hx
        exact Finset.mem_map.mpr ⟨x, hx, rfl⟩
      · intro v hv
        exact (Classical.choose_spec (Finset.mem_map.mp hv)).1
      · intro x hx
        have hm := Classical.choose_spec
          (Finset.mem_map.mp (show emb x ∈ C from Finset.mem_map.mpr ⟨x, hx, rfl⟩))
        apply emb.injective
        exact hm.2
      · intro v hv
        exact (Classical.choose_spec (Finset.mem_map.mp hv)).2
      · intro x hx
        have hdegMap : D.degree x = (H.neighborFinset x.1 ∩ C).card := by
          have hmap := SimpleGraph.map_neighborFinset_induce (G := H) x
          have hset : H.neighborFinset x.1 ∩ U.toFinset =
              H.neighborFinset x.1 ∩ C := by
            ext w
            simp only [Finset.mem_inter]
            constructor
            · rintro ⟨hw, hwu⟩
              refine ⟨hw, ?_⟩
              let y : U := ⟨w, Set.mem_toFinset.mp hwu⟩
              have hadj : D.Adj x y := by
                change H.Adj x.1 w
                exact (SimpleGraph.mem_neighborFinset H x.1 w).1 hw
              have hcomp := (c.mem_supp_congr_adj hadj).mp
                (Set.mem_toFinset.mp hx)
              exact Finset.mem_map.mpr ⟨y, Set.mem_toFinset.mpr hcomp, rfl⟩
            · rintro ⟨hw, hwC⟩
              obtain ⟨y, hy, rfl⟩ := Finset.mem_map.mp hwC
              exact ⟨hw, Set.mem_toFinset.mpr y.2⟩
          calc
            D.degree x = (D.neighborFinset x).card := D.card_neighborFinset_eq_degree x
            _ = (Finset.map emb (D.neighborFinset x)).card :=
              (Finset.card_map (f := emb) (s := D.neighborFinset x)).symm
            _ = (H.neighborFinset x.1 ∩ U.toFinset).card := by rw [hmap]
            _ = (H.neighborFinset x.1 ∩ C).card := by
              rw [hset]
        exact hdegMap
    calc
      _ = ∑ x ∈ S, D.degree x := hsumDegree
      _ = ∑ x ∈ S, (D.neighborFinset x ∩ S).card := by
        apply Finset.sum_congr rfl
        intro x hx
        have hneigh : D.neighborFinset x ⊆ S := by
          intro y hy
          have hadj : D.Adj x y := (SimpleGraph.mem_neighborFinset D x y).mp hy
          have hmem := (c.mem_supp_congr_adj hadj).mp (Set.mem_toFinset.mp hx)
          exact Set.mem_toFinset.mpr hmem
        have hinter : D.neighborFinset x ∩ S = D.neighborFinset x :=
          Finset.inter_eq_left.mpr hneigh
        rw [hinter]
        symm
        exact D.card_neighborFinset_eq_degree x
      _ = 2 * (S.card - 1) := htreeInternal
      _ = 2 * (C.card - 1) := by rw [hCcard]
  have hDegreeSum : (∑ v ∈ C, (H.neighborFinset v).card) = 2 * C.card := by
    calc
      _ = ∑ v ∈ C, G.degree v := by
        apply Finset.sum_congr rfl
        intro v hv
        exact (Erdos1016.Proof.PhysicalSimpleGraphDegreeBridge.degree_eq_neighborFinset_card G v).symm
      _ = ∑ v ∈ C, 2 := by
        apply Finset.sum_congr rfl
        intro v hv
        exact hCdeg v hv
      _ = _ := by simp [Nat.mul_comm]
  have hboundary :=
    DegreeTwoComponentCut.degree_sum_eq_internal_plus_boundary H C
  have hpos : 0 < C.card := by rw [hCcard]; exact hSpos
  have hEq : 2 * C.card = 2 * (C.card - 1) +
      DegreeTwoComponentCut.boundaryCount H C := by
    rw [← hDegreeSum, ← hCinternal_sum]
    exact hboundary
  unfold DegreeTwoComponentCut.boundaryCount at hEq
  change DegreeTwoComponentCut.boundaryCount H C = 2
  omega

end Erdos1016.Proof.ComponentBoundaryCount

end
