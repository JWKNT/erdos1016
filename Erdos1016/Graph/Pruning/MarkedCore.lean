import Erdos1016.Graph.Pruning.CycleCore
import Erdos1016.Graph.Multigraph.Forest

set_option autoImplicit false
set_option maxHeartbeats 1000000

/-!
# Marked sets and forest laws under full two-core pruning

The marked set is pulled back along the actual finite vertex relabelling of
the induced two-core. A marked induced subgraph of minimum degree two survives
unchanged. The full cycle-space equivalence transports the forest comparison
on its complement.
-/

noncomputable section

namespace Erdos1016.ShortProof.CycleCore

open BoundaryTrace BoundaryDecay Nonbacktracking.FiniteTwoCore
local instance markedCoreDecidable (p : Prop) : Decidable p := Classical.propDecidable p

variable (G : PhysicalGraph)

def vertexLabels : Network.Shore.InsideVertex (core G) ≃ (corePhysical G).Vertex :=
  Fintype.equivFin _

def edgeLabels : Network.Shore.InsideEdge G.traceNetwork (core G) ≃ (corePhysical G).Edge :=
  Fintype.equivFin _

def vertexBack (v : (corePhysical G).Vertex) : G.Vertex := ((vertexLabels G).symm v).1
def edgeBack (e : (corePhysical G).Edge) : G.Edge := ((edgeLabels G).symm e).1

lemma vertexBack_injective : Function.Injective (vertexBack G) := by
  intro u v h
  exact (vertexLabels G).symm.injective (Subtype.ext h)

@[simp] lemma vertexBack_src (e : (corePhysical G).Edge) :
    vertexBack G ((corePhysical G).src e) = G.src (edgeBack G e) := by
  simp [vertexBack, vertexLabels, edgeBack, edgeLabels, corePhysical,
    inducedPhysical, inducedNetwork, physicalize, Network.Shore.inside, PhysicalGraph.traceNetwork]

@[simp] lemma vertexBack_dst (e : (corePhysical G).Edge) :
    vertexBack G ((corePhysical G).dst e) = G.dst (edgeBack G e) := by
  simp [vertexBack, vertexLabels, edgeBack, edgeLabels, corePhysical,
    inducedPhysical, inducedNetwork, physicalize, Network.Shore.inside, PhysicalGraph.traceNetwork]

@[simp] lemma physicalCycleEquiv_edge (x : G.CycleSpace) (e : (corePhysical G).Edge) :
    (physicalCycleEquiv G x).1 e = x.1 (edgeBack G e) := rfl

def graphIso : G.toSimpleGraph.induce (↑(core G) : Set G.Vertex) ≃g
    (corePhysical G).toSimpleGraph where
  toEquiv := vertexLabels G
  map_rel_iff' := by
    intro a b
    have h := (inducedPhysicalGraphIso G (core G)).map_rel_iff (a := a) (b := b)
    simpa only [inducedNetwork, Network.Shore.inside_graph_eq_induce,
      PhysicalGraph.traceNetwork_graph] using h

lemma core_adj_iff (u v : (corePhysical G).Vertex) :
    (corePhysical G).toSimpleGraph.Adj u v ↔ G.toSimpleGraph.Adj (vertexBack G u) (vertexBack G v) := by
  have h := (graphIso G).map_rel_iff (a := (vertexLabels G).symm u) (b := (vertexLabels G).symm v)
  change (corePhysical G).toSimpleGraph.Adj
    (vertexLabels G ((vertexLabels G).symm u)) (vertexLabels G ((vertexLabels G).symm v)) ↔
    G.toSimpleGraph.Adj (vertexBack G u) (vertexBack G v) at h
  simpa only [Equiv.apply_symm_apply] using h

/-- The actual marked vertices in the pruned physical graph. -/
def marks (P : Finset G.Vertex) : Finset (corePhysical G).Vertex :=
  Finset.univ.filter fun v => vertexBack G v ∈ P

@[simp] lemma mem_marks (P : Finset G.Vertex) (v : (corePhysical G).Vertex) :
    v ∈ marks G P ↔ vertexBack G v ∈ P := by simp [marks]

def markedVertexEquiv (P : Finset G.Vertex) (hP : P ⊆ core G) :
    {v // v ∈ P} ≃ {v // v ∈ marks G P} where
  toFun v := ⟨vertexLabels G ⟨v.1, hP v.2⟩, by simp [vertexBack, v.2]⟩
  invFun v := ⟨vertexBack G v.1, (mem_marks G P v.1).mp v.2⟩
  left_inv v := by apply Subtype.ext; simp [vertexBack]
  right_inv v := by apply Subtype.ext; simp [vertexBack]

theorem marks_card (P : Finset G.Vertex) (hP : MinTwo G.toSimpleGraph P) :
    (marks G P).card = P.card := by
  simpa only [Fintype.card_coe] using
    (Fintype.card_congr (markedVertexEquiv G P (marked_subset_core G P hP))).symm

def markedGraphIso (P : Finset G.Vertex) (hP : MinTwo G.toSimpleGraph P) :
    G.toSimpleGraph.induce (↑P : Set G.Vertex) ≃g
      (corePhysical G).toSimpleGraph.induce (↑(marks G P) : Set (corePhysical G).Vertex) where
  toEquiv := markedVertexEquiv G P (marked_subset_core G P hP)
  map_rel_iff' := by
    intro a b
    change (corePhysical G).toSimpleGraph.Adj
      (vertexLabels G ⟨a.1, _⟩) (vertexLabels G ⟨b.1, _⟩) ↔ G.toSimpleGraph.Adj a.1 b.1
    rw [core_adj_iff]
    simp [vertexBack]

theorem marked_component_count (P : Finset G.Vertex) (hP : MinTwo G.toSimpleGraph P) :
    Nat.card ((corePhysical G).toSimpleGraph.induce
      (↑(marks G P) : Set (corePhysical G).Vertex)).ConnectedComponent =
      Nat.card (G.toSimpleGraph.induce (↑P : Set G.Vertex)).ConnectedComponent :=
  (Nat.card_congr (markedGraphIso G P hP).connectedComponentEquiv).symm

/-- The underlying physical graph, retaining all labels in the multigraph interface. -/
def asMultigraph (H : PhysicalGraph) : FiniteMultiGraph where
  vertexCount := H.vertexCount
  edgeCount := H.edgeCount
  src := H.src
  dst := H.dst

def physicalMultigraphEquiv (H : PhysicalGraph) : H.CycleSpace ≃ₗ[F₂] (asMultigraph H).CycleSpace where
  toFun x := ⟨x.1, x.2⟩
  invFun x := ⟨x.1, x.2⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

def multigraphCycleEquiv : (asMultigraph G).CycleSpace ≃ₗ[F₂]
    (asMultigraph (corePhysical G)).CycleSpace :=
  (physicalMultigraphEquiv G).symm.trans
    ((physicalCycleEquiv G).trans (physicalMultigraphEquiv (corePhysical G)))

@[simp] lemma multigraphCycleEquiv_edge (x : (asMultigraph G).CycleSpace)
    (e : (corePhysical G).Edge) :
    (multigraphCycleEquiv G x).1 e = x.1 (edgeBack G e) := rfl

def regionWord (H : PhysicalGraph) (P : Finset H.Vertex) (x : (asMultigraph H).CycleSpace) :
    (asMultigraph H).EdgeWord :=
  (asMultigraph H).restrictEdges ((asMultigraph H).internalEdges Pᶜ) x.1

lemma regionWord_nonzero_iff (H : PhysicalGraph) (P : Finset H.Vertex)
    (x : (asMultigraph H).CycleSpace) (e : H.Edge) :
    regionWord H P x e ≠ 0 ↔ x.1 e ≠ 0 ∧ H.src e ∉ P ∧ H.dst e ∉ P := by
  by_cases he : e ∈ (asMultigraph H).internalEdges Pᶜ
  · have hend := (Finset.mem_filter.mp he).2
    simp only [regionWord, FiniteMultiGraph.restrictEdges, if_pos he]
    simp only [Finset.mem_compl] at hend
    exact ⟨fun h => ⟨h, hend⟩, fun h => h.1⟩
  · have hend : ¬ (H.src e ∉ P ∧ H.dst e ∉ P) := by
      simpa [FiniteMultiGraph.internalEdges, asMultigraph] using he
    simp only [regionWord, FiniteMultiGraph.restrictEdges, if_neg he, ne_eq,
      not_true_eq_false, false_iff, not_and]
    exact fun _ hs hd => hend ⟨hs, hd⟩

/-- Actual selected edges in the pruned complement embed in the original
selected complement, with an injective vertex map. -/
def selectedRegionHom (P : Finset G.Vertex) (x : (asMultigraph G).CycleSpace) :
    (asMultigraph (corePhysical G)).selectedGraph
        (regionWord (corePhysical G) (marks G P) (multigraphCycleEquiv G x)) →g
      (asMultigraph G).selectedGraph (regionWord G P x) where
  toFun := vertexBack G
  map_rel' := by
    rintro a b ⟨hab, e, he, hend⟩
    have he' := (regionWord_nonzero_iff _ _ _ e).mp he
    have hsrc : G.src (edgeBack G e) ∉ P := by
      simpa only [← vertexBack_src, ← mem_marks] using he'.2.1
    have hdst : G.dst (edgeBack G e) ∉ P := by
      simpa only [← vertexBack_dst, ← mem_marks] using he'.2.2
    refine ⟨fun h => hab (vertexBack_injective G h), edgeBack G e,
      (regionWord_nonzero_iff G P x _).mpr ⟨he'.1, hsrc, hdst⟩, ?_⟩
    rcases hend with h | h
    · exact Or.inl ⟨by simpa only [asMultigraph, vertexBack_src] using congrArg (vertexBack G) h.1,
        by simpa only [asMultigraph, vertexBack_dst] using congrArg (vertexBack G) h.2⟩
    · exact Or.inr ⟨by simpa only [asMultigraph, vertexBack_src] using congrArg (vertexBack G) h.1,
        by simpa only [asMultigraph, vertexBack_dst] using congrArg (vertexBack G) h.2⟩

theorem outside_forest_survives (P : Finset G.Vertex) (x : (asMultigraph G).CycleSpace)
    (hx : (asMultigraph G).IsForestWord (regionWord G P x)) :
    (asMultigraph (corePhysical G)).IsForestWord
      (regionWord (corePhysical G) (marks G P) (multigraphCycleEquiv G x)) := by
  refine ⟨fun e _ => (corePhysical G).noLoops e, fun e f _ _ h => (corePhysical G).simple e f h, ?_⟩
  intro v p hp
  exact hx.2.2 (p.map (selectedRegionHom G P x))
    ((SimpleGraph.Walk.map_isCycle_iff_of_injective (vertexBack_injective G)).mpr hp)

lemma regionForestProbability_eq_density (H : PhysicalGraph) (P : Finset H.Vertex) :
    (asMultigraph H).regionForestProbability Pᶜ =
      Finite.density (fun x : (asMultigraph H).CycleSpace =>
        (asMultigraph H).IsForestWord (regionWord H P x)) := by
  unfold FiniteMultiGraph.regionForestProbability Finite.density Finite.count regionWord
  have hc : (Fintype.card (asMultigraph H).CycleSpace : ℝ) =
      (2 : ℝ) ^ (asMultigraph H).cycleRank := by
    exact_mod_cast (asMultigraph H).cycleSpace_card
  rw [hc]
  simp only [Finset.sum_boole]

/-- Full two-core pruning preserves the uniform cycle-space law and can only
increase the probability of a forest outside the retained marks. -/
theorem regionForestProbability_le_core (P : Finset G.Vertex) :
    (asMultigraph G).regionForestProbability Pᶜ ≤
      (asMultigraph (corePhysical G)).regionForestProbability (marks G P)ᶜ := by
  rw [regionForestProbability_eq_density, regionForestProbability_eq_density]
  have heq := Finite.density_equiv (multigraphCycleEquiv G).toEquiv
    (P := fun x => (asMultigraph (corePhysical G)).IsForestWord
      (regionWord (corePhysical G) (marks G P) (multigraphCycleEquiv G x)))
    (Q := fun y => (asMultigraph (corePhysical G)).IsForestWord
      (regionWord (corePhysical G) (marks G P) y)) (fun _ => Iff.rfl)
  rw [← heq]
  unfold Finite.density
  exact div_le_div_of_nonneg_right (Finite.count_mono (outside_forest_survives G P)) (Nat.cast_nonneg _)

end Erdos1016.ShortProof.CycleCore
