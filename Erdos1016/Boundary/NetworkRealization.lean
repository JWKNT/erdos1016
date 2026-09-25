import Erdos1016.Boundary.PhysicalGraph

set_option autoImplicit false

/-!
# Physical realization of a finite simple labelled network

This is a relabelling by finite bijections, NOT a contraction, suppression,
or replacement of a graph. It is used to apply the physical cycle-event
lemmas to the one-apex network already constructed in the trace patch.
-/

noncomputable section
open scoped BigOperators
namespace Erdos1016.BoundaryDecay

open BoundaryTrace
local instance networkPhysicalDecidable (p : Prop) : Decidable p := Classical.propDecidable p

variable {V E : Type*} [Fintype V] [Fintype E]

def SimpleNetwork (N : Network V E) : Prop :=
  ∀ e f, ((N.src e = N.src f ∧ N.dst e = N.dst f) ∨
    (N.src e = N.dst f ∧ N.dst e = N.src f)) → e = f

def physicalize (N : Network V E) (hs : SimpleNetwork N) : PhysicalGraph where
  vertexCount := Fintype.card V
  edgeCount := Fintype.card E
  src e := Fintype.equivFin V (N.src ((Fintype.equivFin E).symm e))
  dst e := Fintype.equivFin V (N.dst ((Fintype.equivFin E).symm e))
  noLoops e h := N.noLoops _ ((Fintype.equivFin V).injective h)
  simple e f h := by
    apply (Fintype.equivFin E).symm.injective
    apply hs
    rcases h with h | h
    · exact Or.inl ⟨(Fintype.equivFin V).injective h.1,
        (Fintype.equivFin V).injective h.2⟩
    · exact Or.inr ⟨(Fintype.equivFin V).injective h.1,
        (Fintype.equivFin V).injective h.2⟩

def physicalReindex (N : Network V E) (hs : SimpleNetwork N) :
    Network.Reindex N (physicalize N hs).traceNetwork where
  vertices := Fintype.equivFin V
  edges := Fintype.equivFin E
  endpoints := by intro e; left; simp [physicalize, PhysicalGraph.traceNetwork]

def physicalCycleEquiv (N : Network V E) (hs : SimpleNetwork N) :
    N.CycleSpace ≃ (physicalize N hs).CycleSpace :=
  (physicalReindex N hs).cycleEquiv.trans (physicalize N hs).traceCycleEquiv.symm

/-- Reindexing selected adjacency as well as owner adjacency. -/
theorem selected_reindex_adj {V' E' : Type*} [Fintype V'] [Fintype E']
    {N : Network V E} {N' : Network V' E'} (r : Network.Reindex N N')
    (x : N.Word) (u v : V) :
    (N'.selectedGraph (r.wordEquiv x)).Adj (r.vertices u) (r.vertices v) ↔
      (N.selectedGraph x).Adj u v := by
  constructor
  · rintro ⟨f, hxf, hends⟩
    let e := r.edges.symm f
    have hef : r.edges e = f := r.edges.apply_symm_apply f
    have hxe : x e ≠ 0 := by simpa only [Network.Reindex.wordEquiv] using hxf
    have he := r.endpoints e
    rw [hef] at he
    refine ⟨e, hxe, ?_⟩
    rcases he with he | he <;> rcases hends with hends | hends
    · exact Or.inl ⟨r.vertices.injective (he.1.trans hends.1),
        r.vertices.injective (he.2.trans hends.2)⟩
    · exact Or.inr ⟨r.vertices.injective (he.1.trans hends.1),
        r.vertices.injective (he.2.trans hends.2)⟩
    · exact Or.inr ⟨r.vertices.injective (he.1.trans hends.2),
        r.vertices.injective (he.2.trans hends.1)⟩
    · exact Or.inl ⟨r.vertices.injective (he.1.trans hends.2),
        r.vertices.injective (he.2.trans hends.1)⟩
  · rintro ⟨e, hxe, hends⟩
    refine ⟨r.edges e, by simpa using hxe, ?_⟩
    rcases r.endpoints e with he | he <;> rcases hends with hends | hends
    · exact Or.inl ⟨he.1.symm.trans (congrArg r.vertices hends.1),
        he.2.symm.trans (congrArg r.vertices hends.2)⟩
    · exact Or.inr ⟨he.1.symm.trans (congrArg r.vertices hends.1),
        he.2.symm.trans (congrArg r.vertices hends.2)⟩
    · exact Or.inr ⟨he.2.symm.trans (congrArg r.vertices hends.2),
        he.1.symm.trans (congrArg r.vertices hends.1)⟩
    · exact Or.inl ⟨he.2.symm.trans (congrArg r.vertices hends.2),
        he.1.symm.trans (congrArg r.vertices hends.1)⟩

theorem acyclic_iff_of_iso {V' : Type*} {J : SimpleGraph V} {J' : SimpleGraph V'}
    (e : J ≃g J') : J.IsAcyclic ↔ J'.IsAcyclic := by
  constructor
  · intro h v p hp
    exact h (p.map e.symm.toHom)
      ((SimpleGraph.Walk.map_isCycle_iff_of_injective e.symm.injective).2 hp)
  · intro h v p hp
    exact h (p.map e.toHom)
      ((SimpleGraph.Walk.map_isCycle_iff_of_injective e.injective).2 hp)

/-- Image of an original shore under physical relabelling. -/
def physicalShore (N : Network V E) (hs : SimpleNetwork N) (S : Finset V) :
    Finset (physicalize N hs).Vertex := S.image (Fintype.equivFin V)

def shoreVertexEquiv (e : V ≃ Fin (Fintype.card V)) (S : Finset V) :
    {v : V // v ∈ S} ≃ {v : Fin (Fintype.card V) // v ∈ S.image e} where
  toFun v := ⟨e v.1, Finset.mem_image.2 ⟨v.1, v.2, rfl⟩⟩
  invFun v := ⟨e.symm v.1, by
    obtain ⟨u, hu, huv⟩ := Finset.mem_image.1 v.2
    simpa only [← huv, Equiv.symm_apply_apply] using hu⟩
  left_inv v := Subtype.ext (e.symm_apply_apply v.1)
  right_inv v := Subtype.ext (e.apply_symm_apply v.1)

/-- Induced selected supports are isomorphic, including isolated shore vertices. -/
def physicalSelectedShoreIso (N : Network V E) (hs : SimpleNetwork N)
    (S : Finset V) (x : N.Word) :
    (N.selectedGraph x).induce (↑S : Set V) ≃g
      ((physicalize N hs).selectedGraph ((physicalReindex N hs).wordEquiv x)).induce
        (↑(physicalShore N hs S) : Set (physicalize N hs).Vertex) where
  toEquiv := shoreVertexEquiv (Fintype.equivFin V) S
  map_rel_iff' := by
    intro u v
    exact selected_reindex_adj (physicalReindex N hs) x u.1 v.1

/-- Equality of full-owner marginal laws, not merely a support injection. -/
theorem physical_forest_fraction_eq (N : Network V E) (hs : SimpleNetwork N)
    (S : Finset V) :
    (physicalize N hs).originalForestFraction (physicalShore N hs S) =
      Finite.density (fun x : N.CycleSpace =>
        ((N.selectedGraph x.1).induce (↑S : Set V)).IsAcyclic) := by
  symm
  apply Finite.density_equiv (physicalCycleEquiv N hs)
  intro x
  exact acyclic_iff_of_iso (physicalSelectedShoreIso N hs S x.1)

/-- Incident-edge count on arbitrary finite vertex/edge labels. -/
def networkDegree (N : Network V E) (v : V) : ℕ :=
  (Finset.univ.filter fun e => N.src e = v ∨ N.dst e = v).card

/-- On a simple endpoint network, counting incident physical edges is the same
as counting neighbors in its associated simple graph. -/
theorem networkDegree_eq_graph_degree (N : Network V E) (hs : SimpleNetwork N)
    (v : V) : networkDegree N v = N.graph.degree v := by
  classical
  let incident := Finset.univ.filter fun e : E => N.src e = v ∨ N.dst e = v
  let neigh := N.graph.neighborFinset v
  have hcard : incident.card = neigh.card := by
    refine Finset.card_bij (fun e _ => if N.src e = v then N.dst e else N.src e) ?_ ?_ ?_
    · intro e he
      have he' := (Finset.mem_filter.1 he).2
      by_cases hsrc : N.src e = v
      · simp only [hsrc, if_pos]
        rcases he' with h | h
        · exact (SimpleGraph.mem_neighborFinset N.graph v _).2
            ⟨e, Or.inl ⟨hsrc, rfl⟩⟩
        · exact False.elim (N.noLoops e (hsrc.trans h.symm))
      · have hdst : N.dst e = v := he'.resolve_left hsrc
        rw [SimpleGraph.mem_neighborFinset]
        simp only [hsrc, if_neg]
        exact ⟨e, Or.inr ⟨rfl, hdst⟩⟩
    · intro e he f hf hef
      have he' := (Finset.mem_filter.1 he).2
      have hf' := (Finset.mem_filter.1 hf).2
      by_cases hsrc : N.src e = v <;> by_cases hsrcf : N.src f = v
      · simp [hsrc, hsrcf] at hef
        apply hs e f
        exact Or.inl ⟨hsrc.trans hsrcf.symm, hef⟩
      · have hdstf : N.dst f = v := hf'.resolve_left hsrcf
        simp [hsrc, hsrcf] at hef
        apply hs e f
        exact Or.inr ⟨hsrc.trans hdstf.symm, hef⟩
      · have hdst : N.dst e = v := he'.resolve_left hsrc
        simp [hsrc, hsrcf] at hef
        apply hs e f
        exact Or.inr ⟨hef, hdst.trans hsrcf.symm⟩
      · have hdst : N.dst e = v := he'.resolve_left hsrc
        have hdstf : N.dst f = v := hf'.resolve_left hsrcf
        simp [hsrc, hsrcf] at hef
        apply hs e f
        exact Or.inl ⟨hef, hdst.trans hdstf.symm⟩
    · intro w hw
      have hadj := (SimpleGraph.mem_neighborFinset N.graph v w).1 hw
      rcases hadj with ⟨e, h | h⟩
      · refine ⟨e, ?_, ?_⟩
        · simp [incident, h.1, h.2]
        · simp [h.1, h.2]
      · refine ⟨e, ?_, ?_⟩
        · simp [incident, h.1, h.2]
        · have hwv : w ≠ v := by
            intro heq
            apply N.noLoops e
            rw [h.1, heq, h.2]
          simpa [h.1, hwv]
  unfold networkDegree
  simpa [incident, neigh, SimpleGraph.card_neighborFinset_eq_degree] using hcard



theorem physical_degree_eq (N : Network V E) (hs : SimpleNetwork N) (v : V) :
    (physicalize N hs).degree (Fintype.equivFin V v) = networkDegree N v := by
  simp only [PhysicalGraph.degree, PhysicalGraph.selectedDegree, one_ne_zero,
    true_and, PhysicalGraph.incident, physicalize, networkDegree,
    Finset.card_eq_sum_ones, Finset.sum_filter]
  apply Fintype.sum_equiv (Fintype.equivFin E).symm
  intro e
  simp [(Fintype.equivFin V).injective.eq_iff]

end Erdos1016.BoundaryDecay
