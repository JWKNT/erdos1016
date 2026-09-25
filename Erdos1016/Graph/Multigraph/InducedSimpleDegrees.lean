import Erdos1016.Graph.Multigraph.InducedSimpleTransport
import Erdos1016.Graph.Multigraph.RegionDegrees
import Erdos1016.Graph.PhysicalDegree

set_option autoImplicit false

noncomputable section
namespace Erdos1016.FiniteMultiGraph.InducedSimpleRealization
local instance (p : Prop) : Decidable p := Classical.propDecidable p

private theorem physical_degree_eq_singleton_cut (H : PhysicalGraph) (v : H.Vertex) :
    H.degree v = (H.cutEdges {v}).card := by
  unfold PhysicalGraph.degree PhysicalGraph.selectedDegree PhysicalGraph.cutEdges
  congr 1
  ext e
  simp only [Finset.mem_filter, Finset.mem_univ, one_ne_zero, true_and,
    PhysicalGraph.incident, Finset.mem_singleton]
  by_cases hs : H.src e = v <;> by_cases ht : H.dst e = v <;> simp [hs, ht]
  exact (H.noLoops e (hs.trans ht.symm)).elim

variable (G : FiniteMultiGraph) (R : Finset G.Vertex)
  (hloop : ∀ e ∈ G.internalEdges R, G.src e ≠ G.dst e)
  (hsimple : ∀ e ∈ G.internalEdges R, ∀ f ∈ G.internalEdges R,
    ((G.src e = G.src f ∧ G.dst e = G.dst f) ∨
      (G.src e = G.dst f ∧ G.dst e = G.src f)) → e = f)

@[simp] theorem region_singleton (v : RetainedVertex G R) :
    region G R hloop hsimple {v.1} = {vertexEquiv G R v} := by
  ext w
  simp only [mem_region, Finset.mem_singleton]
  constructor
  · intro h
    apply vertex_injective G R hloop hsimple
    simpa only [vertex_vertexEquiv] using h
  · rintro rfl
    exact vertex_vertexEquiv G R hloop hsimple v

/-- Incidence degree is exactly preserved at any retained vertex whose
 incident physical labels are all retained. -/
theorem degree_eq_of_incident_retained (v : RetainedVertex G R)
    (hinc : ∀ e : G.Edge, (G.src e = v.1 ∨ G.dst e = v.1) → e ∈ G.internalEdges R) :
    (graph G R hloop hsimple).degree (vertexEquiv G R v) = G.degree v.1 := by
  have hcut : G.cutEdges {v.1} ⊆ G.internalEdges R := by
    intro e he
    have h := (Finset.mem_filter.mp he).2
    apply hinc
    rcases h with h | h
    · exact Or.inl (Finset.mem_singleton.mp h.1)
    · exact Or.inr (Finset.mem_singleton.mp h.2)
  have hempty : G.internalEdges {v.1} = ∅ := by
    apply Finset.eq_empty_iff_forall_not_mem.mpr
    intro e he
    have hends := (Finset.mem_filter.mp he).2
    have hs := Finset.mem_singleton.mp hends.1
    have ht := Finset.mem_singleton.mp hends.2
    exact hloop e (hinc e (Or.inl hs)) (hs.trans ht.symm)
  have hledger := G.sum_region_degree {v.1}
  simp only [Finset.sum_singleton, hempty, Finset.card_empty, mul_zero, zero_add] at hledger
  calc
    _ = ((graph G R hloop hsimple).cutEdges {vertexEquiv G R v}).card :=
      physical_degree_eq_singleton_cut _ _
    _ = (G.cutEdges {v.1}).card := by
      rw [← region_singleton G R hloop hsimple v]
      exact cut_card_eq G R hloop hsimple {v.1} hcut
    _ = _ := hledger.symm

/-- Deletion never increases the incidence degree, including when the
ambient graph has loops or parallel labels outside the retained region. -/
theorem degree_le (v : RetainedVertex G R) :
    (graph G R hloop hsimple).degree (vertexEquiv G R v) ≤ G.degree v.1 := by
  have hcut : ((graph G R hloop hsimple).cutEdges
      (region G R hloop hsimple {v.1})).card ≤ (G.cutEdges {v.1}).card := by
    let f : (graph G R hloop hsimple).cutEdges (region G R hloop hsimple {v.1}) →
        G.cutEdges {v.1} := fun e =>
      ⟨edge G R hloop hsimple e.1, (mem_cut_iff G R hloop hsimple {v.1} e.1).mp e.2⟩
    have hf : Function.Injective f := by
      intro e f' h
      have he : edge G R hloop hsimple e.1 = edge G R hloop hsimple f'.1 := congrArg (fun z : G.cutEdges {v.1} => z.1) h
      exact Subtype.ext (edge_injective G R hloop hsimple he)
    simpa only [Fintype.card_coe] using Fintype.card_le_of_injective f hf
  rw [region_singleton] at hcut
  rw [physical_degree_eq_singleton_cut]
  have hs := G.sum_region_degree {v.1}
  simp only [Finset.sum_singleton] at hs
  omega

/-- Cubicity on an exterior component survives deletion of P and the packed
 regions once that component and both boundary cycles are retained. -/
theorem component_degree_eq (U : Finset G.Vertex)
    (c : ExteriorComponents.Component G U)
    (hcR : ExteriorComponents.vertices G U c ⊆ R)
    (hout : ∀ v, v ∉ U → v ∈ R)
    (v : RetainedVertex G R) (hv : v.1 ∈ ExteriorComponents.vertices G U c) :
    (graph G R hloop hsimple).degree (vertexEquiv G R v) = G.degree v.1 := by
  apply degree_eq_of_incident_retained
  intro e he
  apply component_incident_retained G R U c hcR hout e
  exact he.elim (fun hs => Or.inl (hs.symm ▸ hv)) (fun ht => Or.inr (ht.symm ▸ hv))

theorem graph_degree_eq_physical (v : (graph G R hloop hsimple).Vertex) :
    (graph G R hloop hsimple).toSimpleGraph.degree v =
      (graph G R hloop hsimple).degree v := by
  rw [Erdos1016.Proof.PhysicalSimpleGraphDegreeBridge.degree_eq_neighborFinset_card,
    SimpleGraph.card_neighborFinset_eq_degree]

end Erdos1016.FiniteMultiGraph.InducedSimpleRealization
