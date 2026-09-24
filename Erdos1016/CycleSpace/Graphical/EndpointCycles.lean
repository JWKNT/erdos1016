import Erdos1016.Graph.Basic

set_option autoImplicit false

namespace Erdos1016.Proof.GraphicalLinkCycleLemmas

open Erdos1016

private theorem double_zero (x : F₂) : x + x = 0 := by
  have htwo : (2 : F₂) = 0 := ZMod.natCast_self 2
  calc
    x + x = (2 : F₂) * x := by ring
    _ = 0 := by rw [htwo]; simp

/-- The symmetric difference of two physical edge words with the same
boundary is a cycle word. In particular this applies to two `u`-`v` path words. -/
theorem add_mem_cycleSpace_of_boundary_eq (G : PhysicalGraph)
    (x y : G.Word) (h : G.boundary x = G.boundary y) :
    x + y ∈ G.CycleSpace := by
  change G.boundary (x + y) = 0
  rw [G.boundary.map_add, h]
  ext v
  exact double_zero (G.boundary y v)



end Erdos1016.Proof.GraphicalLinkCycleLemmas
