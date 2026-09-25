import Erdos1016.Graph.InducedShore

set_option autoImplicit false

/-!
# Exact degree-two deficit of a cubic shore

This records the precise bridge from the target's original cut budget to the
degree-two count used by the actual nonbacktracking theorem on the induced
shore graph. No degree suppression is involved.
-/

noncomputable section
namespace Erdos1016.Extremal

open Erdos1016.BoundaryTrace Erdos1016.BoundaryDecay
open Erdos1016.Nonbacktracking.FiniteTwoCore
open Erdos1016.SafeCore

local instance deficitBridgeDecidable (p : Prop) : Decidable p :=
  Classical.propDecidable p

/-- Reindexing the degree-two vertices of the induced physical shore gives
exactly the degree-two vertices of its actual inside network. -/
def inducedShoreDegreeTwoEquiv (G : PhysicalGraph) (U : Finset G.Vertex) :
    {w : (inducedShoreGraph G U).Vertex //
      (inducedShoreGraph G U).degree w = 2} ≃
    {v : Network.Shore.InsideVertex U // G.traceInsideDegree U v.1 = 2} where
  toFun w := by
    let v := (inducedShoreVertexEquiv G U).symm w.1
    have hdeg := inducedShore_degree_eq_traceInsideDegree G U v
    refine ⟨v, ?_⟩
    have hpoint : inducedShoreVertexEquiv G U v = w.1 := by
      simp [v]
    have hdeg' : (inducedShoreGraph G U).degree w.1 =
        G.traceInsideDegree U v.1 := by rw [← hpoint]; exact hdeg
    exact hdeg'.symm.trans w.2
  invFun v := by
    refine ⟨inducedShoreVertexEquiv G U v.1, ?_⟩
    exact (inducedShore_degree_eq_traceInsideDegree G U v.1).trans v.2
  left_inv w := by
    apply Subtype.ext
    simp
  right_inv v := by
    apply Subtype.ext
    simp

/-- The cut-edge coordinates of the actual shore are precisely the original
owner-cut edge labels. -/
def shoreCutEdgeOwnerCutEquiv (G : PhysicalGraph) (U : Finset G.Vertex) :
    Network.Shore.CutEdge G.traceNetwork U ≃
      {e : G.Edge // e ∈ SafeCore.ownerCut G U} where
  toFun e := ⟨e.1, by
    apply (SafeCore.mem_ownerCut G U e.1).2
    have he := e.2
    change (G.src e.1 ∈ U ∧ G.dst e.1 ∉ U) ∨
      (G.src e.1 ∉ U ∧ G.dst e.1 ∈ U) at he
    exact he⟩
  invFun e := ⟨e.1, by
    exact (SafeCore.mem_ownerCut G U e.1).1 e.2⟩
  left_inv e := by
    apply Subtype.ext
    rfl
  right_inv e := by
    apply Subtype.ext
    rfl

/-- In a cubic owner, each induced degree-two vertex contributes one and only
one original cut edge. Hence the induced graph's exact deficit is the target
shore's cut size. -/
theorem inducedShore_degreeTwoCount_eq_cutSize
    (G : PhysicalGraph) (U : Finset G.Vertex)
    (hcubic : ∀ v ∈ U, G.degree v = 3)
    (hmin : MinTwo G U) :
    Nonbacktracking.degreeTwoCount (inducedShoreGraph G U) =
      SafeCore.cutSize G U := by
  let H := inducedShoreGraph G U
  have hdegree : Nonbacktracking.degreeTwoCount H =
      Fintype.card {w : H.Vertex // H.degree w = 2} := by
    unfold Nonbacktracking.degreeTwoCount
    symm
    exact Fintype.card_subtype (fun w : H.Vertex => H.degree w = 2)
  have hinside : Fintype.card {w : H.Vertex // H.degree w = 2} =
      Fintype.card {v : Network.Shore.InsideVertex U //
        G.traceInsideDegree U v.1 = 2} :=
    Fintype.card_congr (inducedShoreDegreeTwoEquiv G U)
  have hpins : Fintype.card (Network.Shore.CutEdge G.traceNetwork U) =
      Fintype.card {v : Network.Shore.InsideVertex U //
        G.traceInsideDegree U v.1 = 2} := by
    exact Fintype.card_congr (G.cutPinEquivDegreeTwo U hcubic hmin)
  have hcut : Fintype.card (Network.Shore.CutEdge G.traceNetwork U) =
      SafeCore.cutSize G U := by
    calc
      _ = Fintype.card {e : G.Edge // e ∈ SafeCore.ownerCut G U} :=
        Fintype.card_congr (shoreCutEdgeOwnerCutEquiv G U)
      _ = SafeCore.cutSize G U := by
        simp only [SafeCore.cutSize, Fintype.card_coe]
  calc
    Nonbacktracking.degreeTwoCount H =
        Fintype.card {w : H.Vertex // H.degree w = 2} := hdegree
    _ = Fintype.card {v : Network.Shore.InsideVertex U //
        G.traceInsideDegree U v.1 = 2} := hinside
    _ = Fintype.card (Network.Shore.CutEdge G.traceNetwork U) := hpins.symm
    _ = SafeCore.cutSize G U := hcut

end Erdos1016.Extremal
end
