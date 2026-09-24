import Erdos1016.Cycles.Counting.RootedRunEncoding

set_option autoImplicit false

noncomputable section
namespace Erdos1016.Nonbacktracking

/-- A closed simple cycle walk, with its starting vertex retained, at a
specified length. -/
abbrev RootedSimpleCycle (G : PhysicalGraph) (ℓ : ℕ) :=
  {p : Σ a : G.Vertex, G.toSimpleGraph.Walk a a //
    p.2.IsCycle ∧ p.2.length = ℓ}

















end Erdos1016.Nonbacktracking
end
