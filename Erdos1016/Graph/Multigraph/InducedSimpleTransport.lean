import Erdos1016.Graph.Multigraph.InducedSimpleRealization
import Erdos1016.Graph.CutPacking
import Erdos1016.Graph.ExteriorComponents

set_option autoImplicit false

/-! Actual region and cut transport through the finite relabeling of a
 simple induced multigraph region. No labels are dropped at a retained
 component whose incident edges all remain in the retained graph. -/
noncomputable section
namespace Erdos1016.FiniteMultiGraph.InducedSimpleRealization
local instance (p : Prop) : Decidable p := Classical.propDecidable p

variable (G : FiniteMultiGraph) (R : Finset G.Vertex)
  (hloop : ∀ e ∈ G.internalEdges R, G.src e ≠ G.dst e)
  (hsimple : ∀ e ∈ G.internalEdges R, ∀ f ∈ G.internalEdges R,
    ((G.src e = G.src f ∧ G.dst e = G.dst f) ∨
      (G.src e = G.dst f ∧ G.dst e = G.src f)) → e = f)

def region (A : Finset G.Vertex) : Finset (graph G R hloop hsimple).Vertex :=
  Finset.univ.filter (fun v => vertex G R hloop hsimple v ∈ A)

@[simp] theorem mem_region (A : Finset G.Vertex) (v : (graph G R hloop hsimple).Vertex) :
    v ∈ region G R hloop hsimple A ↔ vertex G R hloop hsimple v ∈ A := by
  simp [region]

@[simp] theorem vertex_vertexEquiv (v : RetainedVertex G R) :
    vertex G R hloop hsimple (vertexEquiv G R v) = v.1 := by simp [vertex]

theorem vertex_mem (v : (graph G R hloop hsimple).Vertex) :
    vertex G R hloop hsimple v ∈ R := ((vertexEquiv G R).symm v).2

def regionEquiv (A : Finset G.Vertex) (hAR : A ⊆ R) :
    region G R hloop hsimple A ≃ A where
  toFun v := ⟨vertex G R hloop hsimple v.1, (mem_region G R hloop hsimple A v).mp v.2⟩
  invFun v := ⟨vertexEquiv G R ⟨v.1, hAR v.2⟩, by simp [v.2]⟩
  left_inv v := by apply Subtype.ext; simp [vertex]
  right_inv v := by apply Subtype.ext; simp

theorem region_card (A : Finset G.Vertex) (hAR : A ⊆ R) :
    (region G R hloop hsimple A).card = A.card := by
  simpa only [Fintype.card_coe] using Fintype.card_congr (regionEquiv G R hloop hsimple A hAR)

/-- A cut edge in the physical realization is exactly the original labelled
 cut edge under the retained-edge injection. -/
theorem mem_cut_iff (A : Finset G.Vertex) (e : (graph G R hloop hsimple).Edge) :
    e ∈ (graph G R hloop hsimple).cutEdges (region G R hloop hsimple A) ↔
      edge G R hloop hsimple e ∈ G.cutEdges A := by
  simp only [PhysicalGraph.cutEdges, FiniteMultiGraph.cutEdges, Finset.mem_filter,
    Finset.mem_univ, true_and, mem_region, vertex_src, vertex_dst]

/-- Every original cut edge is retained under the stated, literal edge
 support inclusion. Thus the two cut sets are in bijection. -/
def cutEquiv (A : Finset G.Vertex) (hcut : G.cutEdges A ⊆ G.internalEdges R) :
    (graph G R hloop hsimple).cutEdges (region G R hloop hsimple A) ≃ G.cutEdges A where
  toFun e := ⟨edge G R hloop hsimple e.1, (mem_cut_iff G R hloop hsimple A e).mp e.2⟩
  invFun e := ⟨edgeEquiv G R ⟨e.1, hcut e.2⟩, by
    rw [mem_cut_iff]
    simpa [edge] using e.2⟩
  left_inv e := by apply Subtype.ext; simp [edge]
  right_inv e := by apply Subtype.ext; simp [edge]

theorem cut_card_eq (A : Finset G.Vertex) (hcut : G.cutEdges A ⊆ G.internalEdges R) :
    ((graph G R hloop hsimple).cutEdges (region G R hloop hsimple A)).card =
      (G.cutEdges A).card := by
  simpa only [Fintype.card_coe] using Fintype.card_congr (cutEquiv G R hloop hsimple A hcut)

/-- A retained component has all its incident labels retained when all
 vertices outside the larger component region U are also retained. In the
 application those outside vertices are the two cycles. -/
theorem component_incident_retained (U : Finset G.Vertex)
    (c : ExteriorComponents.Component G U)
    (hcR : ExteriorComponents.vertices G U c ⊆ R)
    (hout : ∀ v, v ∉ U → v ∈ R) :
    ∀ e : G.Edge, (G.src e ∈ ExteriorComponents.vertices G U c ∨
      G.dst e ∈ ExteriorComponents.vertices G U c) → e ∈ G.internalEdges R := by
  intro e he
  have hother {v w : G.Vertex} (hv : v ∈ ExteriorComponents.vertices G U c)
      (hedge : (G.src e = v ∧ G.dst e = w) ∨ (G.src e = w ∧ G.dst e = v)) : w ∈ R := by
    by_cases hw : w ∈ U
    · by_cases hvw : v = w
      · exact hcR (hvw ▸ hv)
      · exact hcR (ExteriorComponents.adjacent_stays G U c hv hw ⟨hvw, e, hedge⟩)
    · exact hout w hw
  rcases he with hs | ht
  · simp [FiniteMultiGraph.internalEdges, hcR hs, hother hs (Or.inl ⟨rfl, rfl⟩)]
  · simp [FiniteMultiGraph.internalEdges, hcR ht, hother ht (Or.inr ⟨rfl, rfl⟩)]

/-- In particular the actual exterior-component cut is preserved exactly. -/
theorem component_cut_card_eq (U : Finset G.Vertex)
    (c : ExteriorComponents.Component G U)
    (hcR : ExteriorComponents.vertices G U c ⊆ R)
    (hout : ∀ v, v ∉ U → v ∈ R) :
    ((graph G R hloop hsimple).cutEdges
      (region G R hloop hsimple (ExteriorComponents.vertices G U c))).card =
        (G.cutEdges (ExteriorComponents.vertices G U c)).card := by
  apply cut_card_eq
  intro e he
  apply component_incident_retained G R U c hcR hout e
  have h := (Finset.mem_filter.mp he).2
  exact h.elim (fun h => Or.inl h.1) (fun h => Or.inr h.2)

end Erdos1016.FiniteMultiGraph.InducedSimpleRealization
