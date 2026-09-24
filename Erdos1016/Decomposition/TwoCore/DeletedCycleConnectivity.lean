import Erdos1016.Decomposition.TwoCore.PathConvexity
import Erdos1016.Cycles.Geometry.TreeBoundaryIncidences
import Erdos1016.Cycles.Geometry.BoundaryContactGeometry

set_option autoImplicit false

/-!
# Connectivity after deleting a retained cycle from the residual two-core

A minimum-degree-two subgraph cannot enter a complementary tree which has
at most one edge back to that subgraph. Applied to the small components after
one more selected cycle is deleted, this places the entire remaining core
in the giant component. Core path convexity then proves it is connected.
-/

noncomputable section
namespace Erdos1016.Proof.ConditionalCoreComplement

open Erdos1016.SafeCore Erdos1016.Nonbacktracking.FiniteTwoCore
open Erdos1016.Proof.TwoCorePathGeometry Erdos1016.Proof.TreeBoundaryInMinTwo

local instance propDecidable (p : Prop) : Decidable p := Classical.propDecidable p

private theorem crossing_adjacencies_unique
    (G : PhysicalGraph) (R D : Finset G.Vertex) (hdisj : Disjoint R D)
    (hunique : ∀ e f, e ∈ crossing G R D → f ∈ crossing G R D → e = f)
    {r s u v : G.Vertex} (hr : r ∈ R) (hs : s ∈ R) (hu : u ∈ D) (hv : v ∈ D)
    (hru : G.toSimpleGraph.Adj r u) (hsv : G.toSimpleGraph.Adj s v) :
    r = s ∧ u = v := by
  obtain ⟨e, _, he⟩ := hru
  obtain ⟨f, _, hf⟩ := hsv
  have hecross : e ∈ crossing G R D := by
    apply (mem_crossing G R D e).mpr
    rcases he with h | h
    · exact Or.inl ⟨h.1 ▸ hr, h.2 ▸ hu⟩
    · exact Or.inr ⟨h.1 ▸ hu, h.2 ▸ hr⟩
  have hfcross : f ∈ crossing G R D := by
    apply (mem_crossing G R D f).mpr
    rcases hf with h | h
    · exact Or.inl ⟨h.1 ▸ hs, h.2 ▸ hv⟩
    · exact Or.inr ⟨h.1 ▸ hv, h.2 ▸ hs⟩
  have hef := hunique e f hecross hfcross
  subst f
  rcases he with he | he <;> rcases hf with hf | hf
  · exact ⟨he.1.symm.trans hf.1, he.2.symm.trans hf.2⟩
  · exact (Finset.disjoint_left.mp hdisj hr (he.1 ▸ hf.1 ▸ hv)).elim
  · exact (Finset.disjoint_left.mp hdisj hs (hf.1 ▸ he.1 ▸ hu)).elim
  · exact ⟨he.2.symm.trans hf.2, he.1.symm.trans hf.1⟩

/-- A small tree component with at most one contact to the newly deleted
region contains no vertex of any minimum-degree-two residual subgraph. -/
theorem minTwo_disjoint_small_tree
    (G : PhysicalGraph) (U D K R : Finset G.Vertex)
    (hKU : K ⊆ Uᶜ) (hmin : MinTwo G.toSimpleGraph K)
    (hR : R ∈ components G (U ∪ D)ᶜ)
    (htree : (G.toSimpleGraph.induce (↑R : Set G.Vertex)).IsAcyclic)
    (hunique : ∀ e f, e ∈ crossing G R D → f ∈ crossing G R D → e = f) :
    Disjoint K R := by
  classical
  apply Finset.disjoint_left.mpr
  intro v hvK hvR
  obtain ⟨A, hA, hvA⟩ := components_cover G (Finset.mem_inter.mpr ⟨hvK, hvR⟩)
  have hAK : A ⊆ K := fun z hz => (Finset.mem_inter.mp (component_subset G hA hz)).1
  have hAR : A ⊆ R := fun z hz => (Finset.mem_inter.mp (component_subset G hA hz)).2
  have hAtree : (G.toSimpleGraph.induce (↑A : Set G.Vertex)).IsTree := by
    refine ⟨(connectedRegion_iff_induce_connected G A).mp (component_connected G hA), ?_⟩
    intro z p hp
    let incl : G.toSimpleGraph.induce (↑A : Set G.Vertex) →g
        G.toSimpleGraph.induce (↑R : Set G.Vertex) :=
      { toFun := fun z => ⟨z.1, hAR z.2⟩, map_rel' := fun h => h }
    have hinj : Function.Injective incl := by
      intro a b h
      apply Subtype.ext
      exact congrArg (fun z : (↑R : Set G.Vertex) => z.1) h
    exact htree (p.map incl)
      ((SimpleGraph.Walk.map_isCycle_iff_of_injective hinj).mpr hp)
  have htoD : ∀ a ∈ A, ∀ b ∈ K \ A, G.toSimpleGraph.Adj a b → b ∈ D := by
    intro a ha b hb hab
    obtain ⟨hbK, hbA⟩ := Finset.mem_sdiff.mp hb
    have hbR : b ∉ R := by
      intro hbR
      exact hbA (component_closed G hA a ha b (Finset.mem_inter.mpr ⟨hbK, hbR⟩) hab)
    apply Classical.byContradiction
    intro hbD
    have hbU : b ∉ U := Finset.mem_compl.mp (hKU hbK)
    have hbUD : b ∈ (U ∪ D)ᶜ := by simp [hbU, hbD]
    exact hbR (component_closed G hR a (hAR ha) b hbUD hab)
  have hdisj : Disjoint R D := by
    apply Finset.disjoint_left.mpr
    intro z hzR hzD
    exact Finset.mem_compl.mp (component_subset G hR hzR) (Finset.mem_union_right _ hzD)
  have hpair : ∀ a ∈ A, ∀ b ∈ K \ A, ∀ c ∈ A, ∀ d ∈ K \ A,
      G.toSimpleGraph.Adj a b → G.toSimpleGraph.Adj c d → a = c ∧ b = d := by
    intro a ha b hb c hc d hd hab hcd
    exact crossing_adjacencies_unique G R D hdisj hunique
      (hAR ha) (hAR hc) (htoD a ha b hb hab) (htoD c hc d hd hcd) hab hcd
  have hlow := tree_has_two_boundary_incidences G.toSimpleGraph A K hAK hmin hAtree
  have hhigh := sum_fiber_card_le_one A (K \ A) G.toSimpleGraph.Adj hpair
  omega

/-- After deleting a retained cycle, every surviving core vertex lies in
the giant component if each other component is a tree with at most one
contact to the deleted cycle. -/
theorem twoCore_sdiff_subset_giant
    (G : PhysicalGraph) (U D B : Finset G.Vertex)
    (hsmall : ∀ R ∈ components G (U ∪ D)ᶜ, R ≠ B →
      (G.toSimpleGraph.induce (↑R : Set G.Vertex)).IsAcyclic ∧
      (∀ e f, e ∈ crossing G R D → f ∈ crossing G R D → e = f)) :
    vertices G.toSimpleGraph Uᶜ \ D ⊆ B := by
  intro v hv
  obtain ⟨hvK, hvD⟩ := Finset.mem_sdiff.mp hv
  have hvU := Finset.mem_compl.mp (vertices_subset G.toSimpleGraph Uᶜ hvK)
  have hvUD : v ∈ (U ∪ D)ᶜ := by simp [hvU, hvD]
  obtain ⟨R, hR, hvR⟩ := components_cover G hvUD
  by_cases hRB : R = B
  · simpa only [hRB] using hvR
  · obtain ⟨htree, hunique⟩ := hsmall R hR hRB
    have hdisj := minTwo_disjoint_small_tree G U D (vertices G.toSimpleGraph Uᶜ) R
      (vertices_subset G.toSimpleGraph Uᶜ) (vertices_minTwo G.toSimpleGraph Uᶜ)
      hR htree hunique
    exact (Finset.disjoint_left.mp hdisj hvK hvR).elim

/-- The core with the newly selected cycle removed is connected or empty,
which is the topological input to the conditional cycle-probability formula. -/
theorem twoCore_sdiff_connected_or_empty
    (G : PhysicalGraph) (U D B : Finset G.Vertex)
    (hB : B ∈ components G (U ∪ D)ᶜ)
    (hsmall : ∀ R ∈ components G (U ∪ D)ᶜ, R ≠ B →
      (G.toSimpleGraph.induce (↑R : Set G.Vertex)).IsAcyclic ∧
      (∀ e f, e ∈ crossing G R D → f ∈ crossing G R D → e = f)) :
    vertices G.toSimpleGraph Uᶜ \ D = ∅ ∨
      ConnectedRegion G (vertices G.toSimpleGraph Uᶜ \ D) := by
  let K := vertices G.toSimpleGraph Uᶜ
  by_cases hempty : K \ D = ∅
  · exact Or.inl hempty
  · right
    refine ⟨Finset.nonempty_iff_ne_empty.mpr hempty, ?_⟩
    intro u hu v hv
    have hsub := twoCore_sdiff_subset_giant G U D B hsmall
    have hconn := (connectedRegion_iff_induce_connected G B).mp (component_connected G hB)
    obtain ⟨p, hp, _⟩ := hconn.exists_path_of_dist ⟨u, hsub hu⟩ ⟨v, hsub hv⟩
    let incl : G.toSimpleGraph.induce (↑B : Set G.Vertex) →g G.toSimpleGraph :=
      { toFun := Subtype.val, map_rel' := fun h => h }
    let q : G.toSimpleGraph.Walk u v := p.map incl
    have hq : q.IsPath :=
      (SimpleGraph.Walk.map_isPath_iff_of_injective Subtype.val_injective).mpr hp
    have hqB : ∀ z ∈ q.support, z ∈ B := by
      intro z hz
      obtain ⟨w, _, hwz⟩ : ∃ w, w ∈ p.support ∧ incl w = z := by
        simpa [q, SimpleGraph.Walk.support_map] using hz
      exact hwz ▸ w.2
    have hqU : ∀ z ∈ q.support, z ∈ Uᶜ := by
      intro z hz
      have h := Finset.mem_compl.mp (component_subset G hB (hqB z hz))
      exact Finset.mem_compl.mpr (fun hzU => h (Finset.mem_union_left _ hzU))
    have hqCore := path_support_subset_twoCore G.toSimpleGraph Uᶜ q hq
      (Finset.mem_sdiff.mp hu).1 (Finset.mem_sdiff.mp hv).1 hqU
    have hqTarget : ∀ z ∈ q.support, z ∈ K \ D := by
      intro z hz
      refine Finset.mem_sdiff.mpr ⟨hqCore z hz, ?_⟩
      intro hzD
      exact Finset.mem_compl.mp (component_subset G hB (hqB z hz))
        (Finset.mem_union_right _ hzD)
    have aux : ∀ {a b : G.Vertex} (w : G.toSimpleGraph.Walk a b),
        (∀ z ∈ w.support, z ∈ K \ D) → InReach G (K \ D) a b := by
      intro a b w hw
      induction w with
      | nil => exact .refl _ (hw _ (by simp))
      | @cons a b c hab w ih =>
        exact (InReach.step (InReach.refl a (hw _ (by simp)))
          (hw _ (by simp)) hab).trans (ih (fun z hz => hw z (by simp [hz])))
    exact aux q hqTarget

end Erdos1016.Proof.ConditionalCoreComplement

end
