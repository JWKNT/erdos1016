import Erdos1016.Probability.Conditional.VertexLoads
import Mathlib.Combinatorics.SimpleGraph.Matching
import Erdos1016.Cleanup.Corridors.DegreeTwoComponentCut
import Erdos1016.Cycles.Geometry.DegreeTwoTreePaths

set_option autoImplicit false

namespace Erdos1016.Proof.PhysicalDegreeTwoCoreComponents

open Erdos1016







/-- Mark both the originally protected vertices and every degree-three
vertex. The remaining vertices are precisely the degree-two corridor core. -/
noncomputable def protectedOrBranch (G : PhysicalGraph) (P : Finset G.Vertex) : Finset G.Vertex :=
  P ∪ Finset.univ.filter (fun v => G.degree v = 3)

theorem protectedOrBranch_nonempty (G : PhysicalGraph) (P : Finset G.Vertex)
    (hP : P.Nonempty) : (protectedOrBranch G P).Nonempty := by
  exact Finset.Nonempty.mono Finset.subset_union_left hP



end Erdos1016.Proof.PhysicalDegreeTwoCoreComponents
