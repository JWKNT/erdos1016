import Erdos1016.Graph.Multigraph.BoundaryImage
import Erdos1016.Extremal.Capacity.LinearForestRestriction
import Erdos1016.CycleSpace.Graphical.SurjectiveCutRestriction

set_option autoImplicit false

noncomputable section

namespace Erdos1016.Proof.InternalRegionBoundaryRepair

open Erdos1016

local notation "𝔽" => F₂

/-- Keep the host vertex set and retain only edges in `I`; every other edge
is turned into a loop, so it contributes zero to the boundary. -/
def internalMultiGraph (G : PhysicalGraph) (I : Finset G.Edge) : FiniteMultiGraph where
  vertexCount := G.vertexCount
  edgeCount := G.edgeCount
  src := G.src
  dst e := if e ∈ I then G.dst e else G.src e

/-- A componentwise-even demand in the graph induced by `I` can be filled by
an edge word supported entirely on `I`. -/
theorem exists_internal_word_of_componentEven
    (G : PhysicalGraph) (I : Finset G.Edge) (t : G.Demand)
    (hEven : (internalMultiGraph G I).ComponentEven t) :
    ∃ z : G.Word, G.boundary z = t ∧ ∀ e, e ∉ I → z e = 0 := by
  classical
  let H := internalMultiGraph G I
  obtain ⟨x, hx⟩ := H.componentEven_mem_range t hEven
  change H.boundary x = t at hx
  let z : G.Word := fun e => if e ∈ I then x e else 0
  refine ⟨z, ?_, ?_⟩
  · ext v
    change (∑ e : G.Edge,
      ((if G.src e = v then (if e ∈ I then x e else 0) else 0) +
       (if G.dst e = v then (if e ∈ I then x e else 0) else 0))) = t v
    have hsum : (∑ e : G.Edge,
      ((if G.src e = v then (if e ∈ I then x e else 0) else 0) +
       (if G.dst e = v then (if e ∈ I then x e else 0) else 0))) =
      H.boundary x v := by
      unfold H internalMultiGraph
      apply Finset.sum_congr rfl
      intro e he
      by_cases hi : e ∈ I
      · simp [hi]
      · simp [hi]
        by_cases hs : G.src e = v <;> simp [hs]
        · have htwo : (2 : F₂) = 0 := by decide
          calc
            (0 : F₂) = (2 : F₂) * x e := by rw [htwo]; simp
            _ = x e + x e := by ring
    rw [hsum, hx]
  · intro e he
    simp [z, he]

/-- Apply the boundary repair to the raw quotient lift. This is the exact
surjectivity repair premise from `GraphicalActualCutMultigraphSurjective`,
provided the raw-lift boundary is componentwise even on the internal-edge
graph. -/
theorem rawLift_boundary_repair_of_internalComponentEven
    (G : PhysicalGraph) (M : FiniteMultiGraph)
    (edgeMap : M.Edge → G.Edge) (I : Finset G.Edge)
    (hdisjoint : ∀ e : M.Edge, edgeMap e ∉ I)
    (y : M.CycleSpace)
    (hEven : (internalMultiGraph G I).ComponentEven
      (G.boundary (Erdos1016.Proof.GraphicalActualCutMultigraphSurjective.rawLiftWord
        M edgeMap y.1))) :
    ∃ z : G.Word,
      G.boundary z = G.boundary
        (Erdos1016.Proof.GraphicalActualCutMultigraphSurjective.rawLiftWord
          M edgeMap y.1) ∧
      ∀ e : M.Edge, z (edgeMap e) = 0 := by
  obtain ⟨z, hz, hzero⟩ := exists_internal_word_of_componentEven G I
    (G.boundary
      (Erdos1016.Proof.GraphicalActualCutMultigraphSurjective.rawLiftWord
        M edgeMap y.1)) hEven
  refine ⟨z, hz, ?_⟩
  intro e
  exact hzero (edgeMap e) (hdisjoint e)

end Erdos1016.Proof.InternalRegionBoundaryRepair

end
