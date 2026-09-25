import Erdos1016.Cleanup.Corridors.ComponentIncidenceSaturation
import Erdos1016.Cleanup.Paths.DegreeTwoBoundaryAccounting

set_option autoImplicit false

noncomputable section

local instance {V : Type*} (H : SimpleGraph V) : DecidableRel H.Adj :=
  Classical.decRel _
local instance {V : Type*} [Finite V] (H : SimpleGraph V)
    (c : H.ConnectedComponent) : Fintype c.supp := Fintype.ofFinite _

namespace Erdos1016.Proof.CoreIncidenceCoverage

open Erdos1016
open Erdos1016.Proof.PhysicalPartition
open Erdos1016.Proof.PhysicalDegreeTwoCoreComponents
open Erdos1016.Proof.PhysicalDegreeTwoCoreBoundaryAccounting
open Erdos1016.Proof.ComponentIncidenceSaturation

/-- A corridor built from the spanning path of a protected-or-branch
complement component contains every physical edge incident to that component.
The path vertices are internal corridor vertices, so the existing degree-two
saturation lemma applies at each of them. -/
theorem attached_core_corridor_incident_edge_mem_support
    (G : PhysicalGraph) (P : Finset G.Vertex)
    (hdegree : ∀ v, v ∉ P → G.degree v = 2 ∨ G.degree v = 3)
    (c : (G.toSimpleGraph.induce
      {v | v ∉ protectedOrBranch G P}).ConnectedComponent)
    (a b u w : G.Vertex) (p : G.toSimpleGraph.Walk a b)
    (Ccorr : PhysicalCorridor G)
    (hsupport : p.support.toFinset = componentVertices G P c)
    (hverts : Ccorr.vertices = u :: p.support ++ [w])
    (e : G.Edge)
    (he : G.src e ∈ componentVertices G P c ∨
      G.dst e ∈ componentVertices G P c) :
    e ∈ Ccorr.support := by
  have hdegreeQ : ∀ v, v ∉ protectedOrBranch G P → G.degree v = 2 := by
    intro v hv
    exact degree_eq_two_outside_protectedOrBranch G P hdegree hv
  have hsupport' : p.support.toFinset =
      Finset.map (Function.Embedding.subtype
        {v | v ∉ protectedOrBranch G P})
        (@Set.toFinset _ c.supp (Subtype.fintype (Membership.mem c.supp))) := by
    ext v
    have h := congrArg (fun S : Finset G.Vertex => v ∈ S) hsupport
    simpa [componentVertices] using h
  have he' : G.src e ∈
        Finset.map (Function.Embedding.subtype
          {v | v ∉ protectedOrBranch G P})
          (@Set.toFinset _ c.supp (Subtype.fintype (Membership.mem c.supp))) ∨
      G.dst e ∈
        Finset.map (Function.Embedding.subtype
          {v | v ∉ protectedOrBranch G P})
          (@Set.toFinset _ c.supp (Subtype.fintype (Membership.mem c.supp))) := by
    rcases he with hs | ht
    · exact Or.inl (by simpa [componentVertices] using hs)
    · exact Or.inr (by simpa [componentVertices] using ht)
  exact component_incident_edge_mem_support G (protectedOrBranch G P)
    hdegreeQ c a b u w p Ccorr
    hsupport' hverts e he'

end Erdos1016.Proof.CoreIncidenceCoverage

end
