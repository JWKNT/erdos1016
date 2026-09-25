import Erdos1016.Cleanup.Paths.DegreeTwoComponents
import Erdos1016.Cleanup.Paths.ComponentBoundaryEndpoints
import Erdos1016.Decomposition.Regions.CutIncidences

set_option autoImplicit false
set_option maxHeartbeats 600000

noncomputable section

namespace Erdos1016.Proof.PhysicalDegreeTwoCoreBoundaryAccounting

open Erdos1016
open SimpleGraph

open Erdos1016.Proof.PhysicalDegreeTwoCoreComponents
open Erdos1016.Proof.DegreeTwoComponentCut
open Erdos1016.Proof.ComponentBoundaryCount
open Erdos1016.Proof.PhysicalCutBoundaryCount

local instance {V : Type*} (H : SimpleGraph V) : DecidableRel H.Adj := Classical.decRel _
local instance {V : Type*} [Finite V] (H : SimpleGraph V)
    (c : H.ConnectedComponent) : Fintype c.supp := Fintype.ofFinite _

/-- Every vertex outside the protected-or-branch set has ambient degree two
when the original unprotected vertices have degree two or three. -/
theorem degree_eq_two_outside_protectedOrBranch
    (G : PhysicalGraph) (P : Finset G.Vertex)
    (hdegree : ∀ v, v ∉ P → G.degree v = 2 ∨ G.degree v = 3)
    {v : G.Vertex} (hv : v ∉ protectedOrBranch G P) :
    G.degree v = 2 := by
  have hvP : v ∉ P := by
    intro h
    exact hv (Finset.mem_union.mpr (Or.inl h))
  rcases hdegree v hvP with htwo | hthree
  · exact htwo
  · have hvb : v ∈ Finset.univ.filter (fun w : G.Vertex => G.degree w = 3) := by
      simp [hthree]
    exact (hv (Finset.mem_union.mpr (Or.inr hvb))).elim



/-- The vertices of a core component, viewed as physical vertices. -/
noncomputable def componentVertices (G : PhysicalGraph) (P : Finset G.Vertex)
    (c : (G.toSimpleGraph.induce
      {v | v ∉ protectedOrBranch G P}).ConnectedComponent) : Finset G.Vertex := by
  classical
  exact c.supp.toFinset.map
    (Function.Embedding.subtype {v | v ∉ protectedOrBranch G P})







/-- Every core vertex belongs to exactly one induced connected component.
This uniqueness is the disjointness fact needed when aggregating component
corridors. -/
theorem core_component_unique_for_vertex
    (G : PhysicalGraph) (P : Finset G.Vertex) {v : G.Vertex}
    (hv : v ∉ protectedOrBranch G P)
    (c d : (G.toSimpleGraph.induce
      {w | w ∉ protectedOrBranch G P}).ConnectedComponent)
    (hc : v ∈ componentVertices G P c)
    (hd : v ∈ componentVertices G P d) : c = d := by
  classical
  obtain ⟨z, hz, hzv⟩ := Finset.mem_map.mp hc
  have hzv' : z.1 = v := by
    change z.1 = v at hzv
    exact hzv
  subst v
  have hzC : z ∈ c.supp := Set.mem_toFinset.mp hz
  have hzD : z ∈ d.supp := by
    obtain ⟨w, hw, hwz⟩ := Finset.mem_map.mp hd
    have hwz' : w.1 = z.1 := by
      change w.1 = z.1 at hwz
      exact hwz
    have : w = z := Subtype.ext hwz'
    subst w
    exact Set.mem_toFinset.mp hw
  have hC := (c.mem_supp_iff z).mp hzC
  have hD := (d.mem_supp_iff z).mp hzD
  exact hC.symm.trans hD

/-- A physical edge with both endpoints in the degree-two core belongs to
exactly one induced core component. -/
theorem core_internal_edge_has_unique_component
    (G : PhysicalGraph) (P : Finset G.Vertex) (e : G.Edge)
    (hs : G.src e ∉ protectedOrBranch G P)
    (ht : G.dst e ∉ protectedOrBranch G P) :
    ∃! c : (G.toSimpleGraph.induce
        {v | v ∉ protectedOrBranch G P}).ConnectedComponent,
      G.src e ∈ componentVertices G P c ∧ G.dst e ∈ componentVertices G P c := by
  classical
  let U : Set G.Vertex := {v | v ∉ protectedOrBranch G P}
  let H : SimpleGraph U := G.toSimpleGraph.induce U
  let u : U := ⟨G.src e, hs⟩
  let v : U := ⟨G.dst e, ht⟩
  have hAdj : G.toSimpleGraph.Adj (G.src e) (G.dst e) := by
    exact ⟨e, by simp [PhysicalGraph.toSimpleGraph, PhysicalGraph.selectedGraph],
      Or.inl ⟨rfl, rfl⟩⟩
  have huv : H.Adj u v := hAdj
  let c := H.connectedComponentMk u
  have hu : u ∈ c.supp := (c.mem_supp_iff u).mpr rfl
  have hv : v ∈ c.supp := (c.mem_supp_congr_adj huv).mp hu
  have hsrc : G.src e ∈ componentVertices G P c := by
    apply Finset.mem_map.mpr
    exact ⟨u, Set.mem_toFinset.mpr hu, rfl⟩
  have hdst : G.dst e ∈ componentVertices G P c := by
    apply Finset.mem_map.mpr
    exact ⟨v, Set.mem_toFinset.mpr hv, rfl⟩
  refine ⟨c, ⟨hsrc, hdst⟩, ?_⟩
  intro d hd
  exact (core_component_unique_for_vertex G P hs c d hsrc hd.1).symm

/-- A vertex listed in a core component is outside the protected-or-branch
set by construction. -/
theorem componentVertices_mem_not_protected
    (G : PhysicalGraph) (P : Finset G.Vertex)
    (c : (G.toSimpleGraph.induce
      {v | v ∉ protectedOrBranch G P}).ConnectedComponent)
    {v : G.Vertex} (hv : v ∈ componentVertices G P c) :
    v ∉ protectedOrBranch G P := by
  classical
  obtain ⟨z, hz, rfl⟩ := Finset.mem_map.mp hv
  exact z.2

/-- A core component is closed under adjacent core vertices. -/
theorem componentVertices_adj_closed
    (G : PhysicalGraph) (P : Finset G.Vertex)
    (c : (G.toSimpleGraph.induce
      {v | v ∉ protectedOrBranch G P}).ConnectedComponent)
    {u v : G.Vertex} (hu : u ∈ componentVertices G P c)
    (hv : v ∉ protectedOrBranch G P)
    (hadj : G.toSimpleGraph.Adj u v) :
    v ∈ componentVertices G P c := by
  classical
  let U : Set G.Vertex := {x | x ∉ protectedOrBranch G P}
  obtain ⟨u', hu', rfl⟩ := Finset.mem_map.mp hu
  let v' : U := ⟨v, hv⟩
  have hUadj : (G.toSimpleGraph.induce U).Adj u' v' := hadj
  have hvComp : v' ∈ c.supp :=
    (c.mem_supp_congr_adj hUadj).mp (Set.mem_toFinset.mp hu')
  exact Finset.mem_map.mpr ⟨v', Set.mem_toFinset.mpr hvComp, rfl⟩



/-- The outside endpoint of any edge crossing the protected-or-branch
boundary is a member of a unique degree-two core component. -/
theorem crossing_edge_has_core_component
    (G : PhysicalGraph) (P : Finset G.Vertex) (e : G.Edge)
    (hcross : (G.src e ∈ protectedOrBranch G P ∧ G.dst e ∉ protectedOrBranch G P) ∨
      (G.src e ∉ protectedOrBranch G P ∧ G.dst e ∈ protectedOrBranch G P)) :
    ∃ c : (G.toSimpleGraph.induce
        {v | v ∉ protectedOrBranch G P}).ConnectedComponent,
      (if G.src e ∈ protectedOrBranch G P then G.dst e else G.src e) ∈
        componentVertices G P c := by
  classical
  let x := if G.src e ∈ protectedOrBranch G P then G.dst e else G.src e
  have hx : x ∉ protectedOrBranch G P := by
    dsimp [x]
    by_cases hs : G.src e ∈ protectedOrBranch G P
    · simp only [hs, ↓reduceIte]
      rcases hcross with h | h
      · exact h.2
      · exact (h.1 hs).elim
    · simp only [hs, ↓reduceIte]
      intro hfalse
      exact hfalse
  let z : {v : G.Vertex // v ∉ protectedOrBranch G P} := ⟨x, hx⟩
  let c := (G.toSimpleGraph.induce
    {v | v ∉ protectedOrBranch G P}).connectedComponentMk z
  refine ⟨c, ?_⟩
  apply Finset.mem_map.mpr
  refine ⟨z, ?_, rfl⟩
  exact Set.mem_toFinset.mpr ((c.mem_supp_iff z).mpr rfl)

/-- A crossing edge also has a unique owner component: its endpoint outside
the protected-or-branch set. -/
theorem crossing_edge_has_unique_core_component
    (G : PhysicalGraph) (P : Finset G.Vertex) (e : G.Edge)
    (hcross : (G.src e ∈ protectedOrBranch G P ∧ G.dst e ∉ protectedOrBranch G P) ∨
      (G.src e ∉ protectedOrBranch G P ∧ G.dst e ∈ protectedOrBranch G P)) :
    ∃! c : (G.toSimpleGraph.induce
        {v | v ∉ protectedOrBranch G P}).ConnectedComponent,
      (if G.src e ∈ protectedOrBranch G P then G.dst e else G.src e) ∈
        componentVertices G P c := by
  obtain ⟨c, hc⟩ := crossing_edge_has_core_component G P e hcross
  refine ⟨c, hc, ?_⟩
  intro d hd
  have hx : (if G.src e ∈ protectedOrBranch G P then G.dst e else G.src e) ∉
      protectedOrBranch G P := by
    rcases hcross with h | h
    · by_cases hs : G.src e ∈ protectedOrBranch G P
      · simp [hs, h.2]
      · exact (hs h.1).elim
    · by_cases hs : G.src e ∈ protectedOrBranch G P
      · exact (h.1 hs).elim
      · simp [hs, h.1]
  exact (core_component_unique_for_vertex G P hx c d hc hd).symm

/-- Every edge touching the degree-two core has a unique component owner.
For a crossing edge the owner is its core endpoint; for an internal edge it
is the component containing both endpoints. This is the canonical ownership
certificate needed to assemble component corridors without overlap. -/
theorem core_edge_has_unique_component
    (G : PhysicalGraph) (P : Finset G.Vertex) (e : G.Edge)
    (hcore : G.src e ∉ protectedOrBranch G P ∨
      G.dst e ∉ protectedOrBranch G P) :
    ∃! c : (G.toSimpleGraph.induce
        {v | v ∉ protectedOrBranch G P}).ConnectedComponent,
      G.src e ∈ componentVertices G P c ∨
        G.dst e ∈ componentVertices G P c := by
  classical
  by_cases hs : G.src e ∉ protectedOrBranch G P
  · by_cases ht : G.dst e ∉ protectedOrBranch G P
    · obtain ⟨c, hc, _⟩ := core_internal_edge_has_unique_component G P e hs ht
      refine ⟨c, Or.inl hc.1, ?_⟩
      intro d hd
      rcases hd with hsrc | hdst
      · exact (core_component_unique_for_vertex G P hs c d hc.1 hsrc).symm
      · exact (core_component_unique_for_vertex G P ht c d hc.2 hdst).symm
    · have hdstQ : G.dst e ∈ protectedOrBranch G P := by
        exact not_not.mp ht
      have hcross : (G.src e ∈ protectedOrBranch G P ∧
          G.dst e ∉ protectedOrBranch G P) ∨
          (G.src e ∉ protectedOrBranch G P ∧
            G.dst e ∈ protectedOrBranch G P) := Or.inr ⟨hs, hdstQ⟩
      obtain ⟨c, hc, _⟩ := crossing_edge_has_unique_core_component G P e hcross
      have hcsrc : G.src e ∈ componentVertices G P c := by
        simpa [hs] using hc
      refine ⟨c, Or.inl hcsrc, ?_⟩
      intro d hd
      rcases hd with hsrc | hdst
      · exact (core_component_unique_for_vertex G P hs c d hcsrc hsrc).symm
      · exact False.elim ((componentVertices_mem_not_protected G P d hdst) hdstQ)
  · have hsrcQ : G.src e ∈ protectedOrBranch G P := by
      exact not_not.mp hs
    have ht : G.dst e ∉ protectedOrBranch G P := by
      rcases hcore with h | h
      · exact (hs h).elim
      · exact h
    have hcross : (G.src e ∈ protectedOrBranch G P ∧
        G.dst e ∉ protectedOrBranch G P) ∨
        (G.src e ∉ protectedOrBranch G P ∧
          G.dst e ∈ protectedOrBranch G P) := Or.inl ⟨hsrcQ, ht⟩
    obtain ⟨c, hc, _⟩ := crossing_edge_has_unique_core_component G P e hcross
    have hcdst : G.dst e ∈ componentVertices G P c := by
      simpa [hsrcQ] using hc
    refine ⟨c, Or.inr hcdst, ?_⟩
    intro d hd
    rcases hd with hsrc | hdst
    · exact False.elim ((componentVertices_mem_not_protected G P d hsrc) hsrcQ)
    · exact (core_component_unique_for_vertex G P ht c d hcdst hdst).symm


end Erdos1016.Proof.PhysicalDegreeTwoCoreBoundaryAccounting

end
