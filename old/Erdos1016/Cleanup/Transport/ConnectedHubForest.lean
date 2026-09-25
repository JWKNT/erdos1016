import Erdos1016.Graph.ConnectedHubExtension
import Erdos1016.CycleSpace.EmbeddedForestMarginals
import Erdos1016.Graph.Embeddings.Acyclicity

set_option autoImplicit false
set_option maxHeartbeats 1000000

noncomputable section

namespace Erdos1016.Proof.ConnectedHubForest

open Erdos1016 PhysicalGraph

/-- The original vertex carrier in the connected extension. -/
def vertex (G : PhysicalGraph) (v : G.Vertex) : (connectByHub G).Vertex :=
  Fintype.equivFin (G.Vertex ⊕ Unit) (Sum.inl v)

abbrev edge (G : PhysicalGraph) := hubOldEdgeEmbedding G

theorem vertex_injective (G : PhysicalGraph) : Function.Injective (vertex G) :=
  (Fintype.equivFin (G.Vertex ⊕ Unit)).injective.comp Sum.inl_injective

theorem edge_injective (G : PhysicalGraph) : Function.Injective (edge G) :=
  (Fintype.equivFin (G.Edge ⊕ HubComponent G)).injective.comp Sum.inl_injective

@[simp] theorem src_edge (G : PhysicalGraph) (e : G.Edge) :
    (connectByHub G).src (edge G e) = vertex G (G.src e) := by
  simp [edge, hubOldEdgeEmbedding, vertex, connectByHub, BoundaryDecay.physicalize, hubNetwork]

@[simp] theorem dst_edge (G : PhysicalGraph) (e : G.Edge) :
    (connectByHub G).dst (edge G e) = vertex G (G.dst e) := by
  simp [edge, hubOldEdgeEmbedding, vertex, connectByHub, BoundaryDecay.physicalize, hubNetwork]

theorem cycle_coordinate (G : PhysicalGraph) (x : G.CycleSpace) (e : (connectByHub G).Edge) :
    (hubCycleSpaceEquiv G x).1 e =
      match (Fintype.equivFin (G.Edge ⊕ HubComponent G)).symm e with
      | .inl f => x.1 f
      | .inr _ => 0 := by rfl

@[simp] theorem cycle_coordinate_old (G : PhysicalGraph) (x : G.CycleSpace) (e : G.Edge) :
    (hubCycleSpaceEquiv G x).1 (edge G e) = x.1 e := by
  rw [cycle_coordinate]
  simp [edge, hubOldEdgeEmbedding]

/-- Every nonzero coordinate comes from an original edge, including after
an arbitrary fixed witness has been transported. -/
theorem nonzero_old (G : PhysicalGraph) (x : G.CycleSpace) (e : (connectByHub G).Edge)
    (he : (hubCycleSpaceEquiv G x).1 e ≠ 0) : ∃ f, edge G f = e := by
  rw [cycle_coordinate] at he
  cases h : (Fintype.equivFin (G.Edge ⊕ HubComponent G)).symm e with
  | inl f =>
      refine ⟨f, ?_⟩
      change Fintype.equivFin _ (Sum.inl f) = e
      rw [← h, Equiv.apply_symm_apply]
  | inr c => simp [h] at he

abbrev witness (G : PhysicalGraph) (E : Finset G.Edge) : Finset (connectByHub G).Edge :=
  E.image (edge G)

@[simp] theorem edge_mem_witness (G : PhysicalGraph) (E : Finset G.Edge) (e : G.Edge) :
    edge G e ∈ witness G E ↔ e ∈ E := by
  constructor
  · intro h
    obtain ⟨f, hf, heq⟩ := Finset.mem_image.mp h
    exact edge_injective G heq ▸ hf
  · intro he
    exact Finset.mem_image.mpr ⟨e, he, rfl⟩

/-- Selected adjacency in the hub extension has both endpoints in the
original carrier, with the exact original witness restriction. -/
theorem adjacency_lift (G : PhysicalGraph) (E : Finset G.Edge) (x : G.CycleSpace)
    {a b : (connectByHub G).Vertex}
    (h : ((connectByHub G).restrictedSelectedGraph (witness G E)ᶜ
      ((connectByHub G).restrictWord (witness G E)ᶜ (hubCycleSpaceEquiv G x).1)).Adj a b) :
    ∃ u v, (G.restrictedSelectedGraph Eᶜ (G.restrictWord Eᶜ x.1)).Adj u v ∧
      vertex G u = a ∧ vertex G v = b := by
  classical
  obtain ⟨e, he, hor⟩ := h
  obtain ⟨f, hf⟩ := nonzero_old G x e.1 he
  have hfE : f ∈ Eᶜ := by
    apply Finset.mem_compl.mpr
    intro hm
    exact (Finset.mem_compl.mp e.2) (hf ▸ Finset.mem_image.mpr ⟨f, hm, rfl⟩)
  have hfnz : x.1 f ≠ 0 := by simpa only [PhysicalGraph.restrictWord, ← hf, cycle_coordinate_old] using he
  rw [← hf, src_edge, dst_edge] at hor
  rcases hor with h | h
  · exact ⟨G.src f, G.dst f, ⟨⟨f, hfE⟩, hfnz, Or.inl ⟨rfl, rfl⟩⟩, h⟩
  · exact ⟨G.dst f, G.src f, ⟨⟨f, hfE⟩, hfnz, Or.inr ⟨rfl, rfl⟩⟩, h.2, h.1⟩

def selectedEmbedding (G : PhysicalGraph) (E : Finset G.Edge) (x : G.CycleSpace) :
    G.restrictedSelectedGraph Eᶜ (G.restrictWord Eᶜ x.1) ↪g
      (connectByHub G).restrictedSelectedGraph (witness G E)ᶜ
        ((connectByHub G).restrictWord (witness G E)ᶜ (hubCycleSpaceEquiv G x).1) where
  toFun := vertex G
  inj' := vertex_injective G
  map_rel_iff' := by
    intro a b
    constructor
    · intro h
      obtain ⟨u, v, huv, hu, hv⟩ := adjacency_lift G E x h
      exact (vertex_injective G hu) ▸ (vertex_injective G hv) ▸ huv
    · rintro ⟨e, he, hor⟩
      have heW : edge G e.1 ∈ (witness G E)ᶜ := by
        exact Finset.mem_compl.mpr (fun h => (Finset.mem_compl.mp e.2) ((edge_mem_witness G E e.1).mp h))
      refine ⟨⟨edge G e.1, heW⟩, ?_, ?_⟩
      · simpa only [PhysicalGraph.restrictWord, cycle_coordinate_old] using he
      · simpa only [src_edge, dst_edge] using hor.elim
          (fun h => Or.inl ⟨congrArg (vertex G) h.1, congrArg (vertex G) h.2⟩)
          (fun h => Or.inr ⟨congrArg (vertex G) h.1, congrArg (vertex G) h.2⟩)

/-- For a lifted cycle, every selected incidence at an original vertex is
one of the original restricted incidences. Spokes contribute zero. -/
theorem degree_old_eq (G : PhysicalGraph) (E : Finset G.Edge) (x : G.CycleSpace) (v : G.Vertex) :
    (connectByHub G).restrictedSelectedDegree (witness G E)ᶜ
      ((connectByHub G).restrictWord (witness G E)ᶜ (hubCycleSpaceEquiv G x).1) (vertex G v) =
      G.restrictedSelectedDegree Eᶜ (G.restrictWord Eᶜ x.1) v := by
  classical
  symm
  let f : G.RestrictedEdge Eᶜ → (connectByHub G).RestrictedEdge (witness G E)ᶜ := fun e =>
    ⟨edge G e.1, Finset.mem_compl.mpr (fun he =>
      (Finset.mem_compl.mp e.2) ((edge_mem_witness G E e.1).mp he))⟩
  apply Finset.card_bij (fun e _ => f e)
  · intro e he
    have hh : x.1 e.1 ≠ 0 ∧ G.incident e.1 v := (Finset.mem_filter.mp he).2
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ _, ?_, ?_⟩
    · change (hubCycleSpaceEquiv G x).1 (edge G e.1) ≠ 0
      simpa only [cycle_coordinate_old] using hh.1
    · change (connectByHub G).incident (edge G e.1) (vertex G v)
      rcases hh.2 with hs | ht
      · exact Or.inl ((src_edge G e.1).trans (congrArg (vertex G) hs))
      · exact Or.inr ((dst_edge G e.1).trans (congrArg (vertex G) ht))
  · intro e _ d _ h
    exact Subtype.ext (edge_injective G (congrArg Subtype.val h))
  · intro e he
    have hh : (hubCycleSpaceEquiv G x).1 e.1 ≠ 0 ∧
        (connectByHub G).incident e.1 (vertex G v) := (Finset.mem_filter.mp he).2
    obtain ⟨p, hp⟩ := nonzero_old G x e.1 hh.1
    have hpE : p ∈ Eᶜ := Finset.mem_compl.mpr (fun h =>
      (Finset.mem_compl.mp e.2) (hp ▸ Finset.mem_image.mpr ⟨p, h, rfl⟩))
    refine ⟨⟨p, hpE⟩, ?_, Subtype.ext hp⟩
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ _, ?_, ?_⟩
    · change x.1 p ≠ 0
      simpa only [← hp, cycle_coordinate_old] using hh.1
    · rcases hh.2 with hs | ht
      · exact Or.inl (vertex_injective G (by simpa only [← hp, src_edge] using hs))
      · exact Or.inr (vertex_injective G (by simpa only [← hp, dst_edge] using ht))

/-- Outside the embedded old carrier, every selected degree is zero. -/
theorem degree_new_eq_zero (G : PhysicalGraph) (E : Finset G.Edge) (x : G.CycleSpace)
    (v : (connectByHub G).Vertex) (hv : ¬ ∃ u, vertex G u = v) :
    (connectByHub G).restrictedSelectedDegree (witness G E)ᶜ
      ((connectByHub G).restrictWord (witness G E)ᶜ (hubCycleSpaceEquiv G x).1) v = 0 := by
  classical
  apply Finset.card_eq_zero.mpr
  apply Finset.eq_empty_iff_forall_not_mem.mpr
  intro e he
  have hh : (hubCycleSpaceEquiv G x).1 e.1 ≠ 0 ∧
      (connectByHub G).incident e.1 v := (Finset.mem_filter.mp he).2
  obtain ⟨p, hp⟩ := nonzero_old G x e.1 hh.1
  apply hv
  rcases hh.2 with hs | ht
  · exact ⟨G.src p, by simpa only [← hp, src_edge] using hs⟩
  · exact ⟨G.dst p, by simpa only [← hp, dst_edge] using ht⟩

/-- Hub extension preserves the forest event for the same fixed witness;
no new choice of canonical cycles is made. -/
theorem forest_iff (G : PhysicalGraph) (E : Finset G.Edge) (x : G.CycleSpace) :
    G.IsRestrictedLinearForest Eᶜ (G.restrictWord Eᶜ x.1) ↔
      (connectByHub G).IsRestrictedLinearForest (witness G E)ᶜ
        ((connectByHub G).restrictWord (witness G E)ᶜ (hubCycleSpaceEquiv G x).1) := by
  constructor
  · intro hx
    constructor
    · apply ClosedGraphEmbeddingAcyclic.acyclic (selectedEmbedding G E x) _ hx.1
      intro a b hab
      obtain ⟨u, v, _, hu, hv⟩ := adjacency_lift G E x hab
      exact ⟨u, v, hu, hv⟩
    · intro v
      by_cases hv : ∃ u, vertex G u = v
      · obtain ⟨u, rfl⟩ := hv
        rw [degree_old_eq]
        exact hx.2 u
      · rw [degree_new_eq_zero G E x v hv]
        omega
  · exact PhysicalEmbeddingForestProbability.forest_pullback G (connectByHub G)
      (vertex G) (edge G) (vertex_injective G) (edge_injective G) (src_edge G) (dst_edge G)
      (witness G E) E (fun e => (edge_mem_witness G E e).symm)
      (hubCycleSpaceEquiv G x).1 x.1 (fun e => (cycle_coordinate_old G x e).symm)

/-- Exact probability preservation under the cycle-space bijection. -/
theorem outside_probability_eq (G : PhysicalGraph) (E : Finset G.Edge) :
    G.outsideLinearForestProbability E =
      (connectByHub G).outsideLinearForestProbability (witness G E) := by
  rw [PhysicalEmbeddingForestProbability.outside_probability_eq_density,
    PhysicalEmbeddingForestProbability.outside_probability_eq_density]
  exact Finite.density_equiv (hubCycleSpaceEquiv G).toEquiv (forest_iff G E)

end Erdos1016.Proof.ConnectedHubForest

end
