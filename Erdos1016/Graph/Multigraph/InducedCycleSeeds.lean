import Erdos1016.Graph.Multigraph.InducedCycleSpace
import Erdos1016.Probability.Cylinders.RegionCycleEvents

set_option autoImplicit false

/-!
# Actual cycle seeds in an ambient multigraph

A physical cycle of the retained simple graph extends by zero to an ambient
even word. Its connected support, incidence degree two, and geometric weight
are preserved exactly. Cycles remain indexed by their original physical
words, so trace counts and vertex-weight sums need no quotienting.
-/

noncomputable section
open scoped BigOperators
namespace Erdos1016.FiniteMultiGraph.InducedSimpleRealization

open BoundaryDecay
local instance inducedCycleSeedDecidable (p : Prop) : Decidable p := Classical.propDecidable p

variable (G : FiniteMultiGraph) (R : Finset G.Vertex)
  (hloop : ∀ e ∈ G.internalEdges R, G.src e ≠ G.dst e)
  (hsimple : ∀ e ∈ G.internalEdges R, ∀ f ∈ G.internalEdges R,
    ((G.src e = G.src f ∧ G.dst e = G.dst f) ∨
      (G.src e = G.dst f ∧ G.dst e = G.src f)) → e = f)

/-- The actual ambient vertex support of a retained cycle. -/
def cycleRegion (C : (graph G R hloop hsimple).CycleWord) : Finset G.Vertex :=
  (Cycle.vertices C).image (vertex G R hloop hsimple)

theorem cycleRegion_subset (C : (graph G R hloop hsimple).CycleWord) :
    cycleRegion G R hloop hsimple C ⊆ R := by
  intro v hv
  obtain ⟨u, hu, rfl⟩ := Finset.mem_image.mp hv
  exact ((vertexEquiv G R).symm u).2

@[simp] theorem mem_cycleRegion_vertex (C : (graph G R hloop hsimple).CycleWord)
    (v : (graph G R hloop hsimple).Vertex) :
    vertex G R hloop hsimple v ∈ cycleRegion G R hloop hsimple C ↔ v ∈ Cycle.vertices C := by
  constructor
  · intro hv
    obtain ⟨u, hu, huv⟩ := Finset.mem_image.mp hv
    exact (vertex_injective G R hloop hsimple huv) ▸ hu
  · intro hv
    exact Finset.mem_image.mpr ⟨v, hv, rfl⟩

theorem cycleRegion_card (C : (graph G R hloop hsimple).CycleWord) :
    (cycleRegion G R hloop hsimple C).card = BoundaryDecay.Cycle.length C := by
  rw [cycleRegion, Finset.card_image_of_injective _ (vertex_injective G R hloop hsimple)]
  exact (Cycle.length_eq_vertices_card C).symm

theorem liftCycle_supported (C : (graph G R hloop hsimple).CycleWord) :
    ∀ e, e ∉ G.internalEdges (cycleRegion G R hloop hsimple C) →
      liftWord G R hloop hsimple C.1 e = 0 := by
  intro e he
  by_cases hmem : e ∈ G.internalEdges R
  · let f : (graph G R hloop hsimple).Edge := edgeEquiv G R ⟨e, hmem⟩
    have hef : edge G R hloop hsimple f = e := by simp [f, edge]
    rw [← hef, liftWord_edge]
    by_contra hn
    apply he
    have hs := src_mem_used_of_ne_zero C.1 f hn
    have ht := dst_mem_used_of_ne_zero C.1 f hn
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ _, ?_, ?_⟩
    · have hsrc : vertex G R hloop hsimple ((graph G R hloop hsimple).src f) = G.src e := by
        rw [vertex_src, hef]
      exact Finset.mem_image.mpr ⟨_, hs, hsrc⟩
    · have hdst : vertex G R hloop hsimple ((graph G R hloop hsimple).dst f) = G.dst e := by
        rw [vertex_dst, hef]
      exact Finset.mem_image.mpr ⟨_, ht, hdst⟩
  · exact liftWord_zero_outside G R hloop hsimple C.1 e hmem

/-- The literal ambient cycle-space seed, supported on the original cycle region. -/
def cycleSeed (C : (graph G R hloop hsimple).CycleWord) :
    G.internalCycleSpace (cycleRegion G R hloop hsimple C) :=
  ⟨liftCycleSpace G R hloop hsimple (Cycle.seed C), liftCycle_supported G R hloop hsimple C⟩

theorem cycleSeed_nonzero (C : (graph G R hloop hsimple).CycleWord) :
    cycleSeed G R hloop hsimple C ≠ 0 := by
  intro h
  have hw : liftWord G R hloop hsimple C.1 = 0 :=
    congrArg (fun z : G.internalCycleSpace (cycleRegion G R hloop hsimple C) => z.1.1) h
  have hinj := liftWord_injective G R hloop hsimple
  exact C.2.1 (hinj (by simpa only [map_zero] using hw))

theorem cycleSeed_degree (C : (graph G R hloop hsimple).CycleWord) :
    ∀ v ∈ cycleRegion G R hloop hsimple C,
      G.selectedDegree (cycleSeed G R hloop hsimple C).1.1 v = 2 := by
  intro v hv
  obtain ⟨u, hu, rfl⟩ := Finset.mem_image.mp hv
  change G.selectedDegree (liftWord G R hloop hsimple C.1) (vertex G R hloop hsimple u) = 2
  rw [selectedDegree_liftWord]
  exact C.2.2.2.2 u hu

/-- Selected support connectivity is preserved, not merely ambient connectivity. -/
theorem cycleSeed_connected (C : (graph G R hloop hsimple).CycleWord) :
    ((G.selectedGraph (cycleSeed G R hloop hsimple C).1.1).induce
      (↑(cycleRegion G R hloop hsimple C) : Set G.Vertex)).Connected := by
  let f : ((graph G R hloop hsimple).selectedGraph C.1).induce (↑(Cycle.vertices C) : Set _) →g
      (G.selectedGraph (cycleSeed G R hloop hsimple C).1.1).induce
        (↑(cycleRegion G R hloop hsimple C) : Set G.Vertex) := {
    toFun := fun v => ⟨vertex G R hloop hsimple v.1, Finset.mem_image.mpr ⟨v.1, v.2, rfl⟩⟩
    map_rel' := by
      intro u v huv
      rcases huv with ⟨e, he, hend⟩
      refine ⟨?_, edge G R hloop hsimple e, ?_, ?_⟩
      · intro hsame
        have huv' := vertex_injective G R hloop hsimple hsame
        rcases hend with h | h
        · exact (graph G R hloop hsimple).noLoops e (h.1.trans (huv'.trans h.2.symm))
        · exact (graph G R hloop hsimple).noLoops e (h.1.trans (huv'.symm.trans h.2.symm))
      · change liftWord G R hloop hsimple C.1 (edge G R hloop hsimple e) ≠ 0
        simpa only [liftWord_edge] using he
      · rcases hend with h | h
        · exact Or.inl ⟨(vertex_src G R hloop hsimple e).symm.trans (congrArg _ h.1),
            (vertex_dst G R hloop hsimple e).symm.trans (congrArg _ h.2)⟩
        · exact Or.inr ⟨(vertex_src G R hloop hsimple e).symm.trans (congrArg _ h.1),
            (vertex_dst G R hloop hsimple e).symm.trans (congrArg _ h.2)⟩ }
  apply SimpleGraph.Connected.map f _ C.2.2.2.1
  intro v
  obtain ⟨u, hu, huv⟩ := Finset.mem_image.mp v.2
  exact ⟨⟨u, hu⟩, Subtype.ext huv⟩

theorem cycleRegion_connected (C : (graph G R hloop hsimple).CycleWord) :
    (G.toSimpleGraph.induce (↑(cycleRegion G R hloop hsimple C) : Set G.Vertex)).Connected := by
  apply SimpleGraph.Connected.mono _ (cycleSeed_connected G R hloop hsimple C)
  intro u v huv
  rcases huv with ⟨hne, e, he, hend⟩
  exact ⟨hne, e, hend⟩

theorem cycleSeed_support_card (C : (graph G R hloop hsimple).CycleWord) :
    (G.seedSupport (cycleSeed G R hloop hsimple C).1).card = BoundaryDecay.Cycle.length C := by
  rw [← cycleRegion_card G R hloop hsimple C]
  exact G.support_card_eq_of_two_regular _ _ (cycleSeed_degree G R hloop hsimple C)
    (cycleSeed G R hloop hsimple C).2

/-- Distinct retained physical cycles remain distinct ambient even words. -/
theorem cycleSeed_injective : Function.Injective
    (fun C : (graph G R hloop hsimple).CycleWord => (cycleSeed G R hloop hsimple C).1) := by
  intro C D hCD
  apply Subtype.ext
  have h := liftCycleSpace_injective G R hloop hsimple hCD
  exact congrArg (fun z : (graph G R hloop hsimple).CycleSpace => z.1) h

end Erdos1016.FiniteMultiGraph.InducedSimpleRealization
