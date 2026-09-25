import Erdos1016.Graph.Cubicization.IncidenceCycleSpace
import Erdos1016.Boundary.NetworkRealization
import Erdos1016.Graph.Multigraph.Forest

set_option autoImplicit false
set_option maxHeartbeats 1000000

/-! The incidence-path construction in the finite physical graph interfaces. -/

noncomputable section

namespace Erdos1016.ShortProof.IncidencePaths

open BoundaryTrace BoundaryDecay
local instance incidenceRealizationDecidable (p : Prop) : Decidable p := Classical.propDecidable p

variable (G : PhysicalGraph) (W : Finset G.Edge)

/-- Relabelling the expanded network by finite physical edge coordinates. -/
def realizationCycleEquiv : (network G W).CycleSpace ≃ₗ[F₂] (physical G W).CycleSpace where
  toEquiv := BoundaryDecay.physicalCycleEquiv (network G W) (network_simple G W)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

@[simp] theorem realizationCycleEquiv_edge (x : (network G W).CycleSpace) (e : Edge G W) :
    (realizationCycleEquiv G W x).1 (edgeLabels G W e) = x.1 e := by
  change x.1 ((edgeLabels G W).symm (edgeLabels G W e)) = x.1 e
  rw [Equiv.symm_apply_apply]

@[simp] theorem realizationCycleEquiv_symm_edge (x : (physical G W).CycleSpace) (e : Edge G W) :
    ((realizationCycleEquiv G W).symm x).1 e = x.1 (edgeLabels G W e) := rfl

/-- The actual finite physical expansion has the original cycle space. -/
def physicalCycleSpaceEquiv : (physical G W).CycleSpace ≃ₗ[F₂] G.CycleSpace :=
  (realizationCycleEquiv G W).symm.trans (cycleSpaceEquiv G W)

@[simp] theorem physicalCycleSpaceEquiv_original_edge (x : (physical G W).CycleSpace) (e : G.Edge) :
    (physicalCycleSpaceEquiv G W x).1 e = x.1 (edgeLabels G W (Sum.inr e)) := rfl

def physicalMultigraphCycleEquiv : (physical G W).CycleSpace ≃ₗ[F₂] (multigraph G W).CycleSpace where
  toFun x := ⟨x.1, x.2⟩
  invFun x := ⟨x.1, x.2⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

def multigraphCycleSpaceEquiv : (multigraph G W).CycleSpace ≃ₗ[F₂] G.CycleSpace :=
  (physicalMultigraphCycleEquiv G W).symm.trans (physicalCycleSpaceEquiv G W)

@[simp] theorem multigraphCycleSpaceEquiv_original_edge (x : (multigraph G W).CycleSpace) (e : G.Edge) :
    (multigraphCycleSpaceEquiv G W x).1 e = x.1 (edgeLabels G W (Sum.inr e)) := rfl

theorem physical_cycleRank : (physical G W).cycleRank = G.cycleRank :=
  (physicalCycleSpaceEquiv G W).finrank_eq

theorem multigraph_cycleRank : (multigraph G W).cycleRank = G.cycleRank :=
  (multigraphCycleSpaceEquiv G W).finrank_eq

theorem physical_degree_le_three (v : (physical G W).Vertex) : (physical G W).degree v ≤ 3 := by
  obtain ⟨a, rfl⟩ := (vertexLabels G W).surjective v
  change (physicalize (network G W) (network_simple G W)).degree (Fintype.equivFin _ a) ≤ 3
  rw [physical_degree_eq, networkDegree_eq_graph_degree _ (network_simple G W), network_graph]
  exact degree_le_three G W a

theorem physical_connected (h : G.IsConnected) : (physical G W).IsConnected := by
  have hn : (network G W).graph.Connected := by
    rw [network_graph]
    exact connected G W h
  have hp := ((physicalReindex (network G W) (network_simple G W)).connected_iff).mp hn
  rw [PhysicalGraph.traceNetwork_graph] at hp
  exact hp

def realizationGraphIso : graph G W ≃g (physical G W).toSimpleGraph where
  toEquiv := vertexLabels G W
  map_rel_iff' := by
    intro a b
    have h := (physicalReindex (network G W) (network_simple G W)).graph_adj_iff a b
    rw [network_graph, PhysicalGraph.traceNetwork_graph] at h
    exact h

theorem multigraph_graph : (multigraph G W).toSimpleGraph = (physical G W).toSimpleGraph := by
  ext u v
  constructor
  · rintro ⟨_, e, h⟩
    exact ⟨e, one_ne_zero, h⟩
  · rintro ⟨e, _, h⟩
    refine ⟨?_, e, h⟩
    intro heq
    rcases h with h | h
    · exact (physical G W).noLoops e (h.1.trans (heq.trans h.2.symm))
    · exact (physical G W).noLoops e (h.1.trans (heq.symm.trans h.2.symm))

theorem multigraph_degree_eq_physical (v : (physical G W).Vertex) :
    (multigraph G W).degree v = (physical G W).degree v := by
  let S := Finset.univ.filter fun e : (physical G W).Edge => (physical G W).src e = v
  let T := Finset.univ.filter fun e : (physical G W).Edge => (physical G W).dst e = v
  have hd : Disjoint S T := by
    apply Finset.disjoint_left.mpr
    intro e hs ht
    exact (physical G W).noLoops e
      ((Finset.mem_filter.mp hs).2.trans (Finset.mem_filter.mp ht).2.symm)
  change (multigraph G W).selectedDegree (fun _ => 1) v = _
  unfold FiniteMultiGraph.selectedDegree
  have hfull : (Finset.univ.filter fun _e : (multigraph G W).Edge => (1 : F₂) ≠ 0) =
      Finset.univ := by ext e; simp
  rw [hfull]
  change S.card + T.card = (physical G W).degree v
  rw [← Finset.card_union_of_disjoint hd]
  unfold PhysicalGraph.degree PhysicalGraph.selectedDegree
  congr 1
  ext e
  simp [S, T, PhysicalGraph.incident]

theorem multigraph_degree_le_three (v : (multigraph G W).Vertex) :
    (multigraph G W).degree v ≤ 3 := by
  rw [multigraph_degree_eq_physical]
  exact physical_degree_le_three G W v

theorem multigraph_connected (h : G.IsConnected) : (multigraph G W).toSimpleGraph.Connected := by
  rw [multigraph_graph]
  exact physical_connected G W h

/-- The marked vertices in the physical realization. -/
def markedVertices : Finset (physical G W).Vertex :=
  Finset.univ.filter fun v => Marked G W ((vertexLabels G W).symm v)

@[simp] theorem vertexLabels_mem_marked (a : Vertex G W) :
    vertexLabels G W a ∈ markedVertices G W ↔ Marked G W a := by
  simp [markedVertices]

def markedVertexLabels : MarkedVertex G W ≃ {v // v ∈ markedVertices G W} := {
    toFun a := ⟨vertexLabels G W a.1, (vertexLabels_mem_marked G W a.1).mpr a.2⟩
    invFun a := ⟨(vertexLabels G W).symm a.1, (Finset.mem_filter.mp a.2).2⟩
    left_inv a := Subtype.ext ((vertexLabels G W).symm_apply_apply a.1)
    right_inv a := Subtype.ext ((vertexLabels G W).apply_symm_apply a.1) }

theorem markedVertices_card : (markedVertices G W).card = 2 * W.card := by
  simpa only [Fintype.card_coe, marked_card] using
    (Fintype.card_congr (markedVertexLabels G W)).symm

def markedRealizationIso : markedGraph G W ≃g
    (physical G W).toSimpleGraph.induce (↑(markedVertices G W) : Set (physical G W).Vertex) where
  toEquiv := markedVertexLabels G W
  map_rel_iff' := by
    intro a b
    exact (realizationGraphIso G W).map_rel_iff

theorem marked_physical_component_count_le :
    Nat.card ((physical G W).toSimpleGraph.induce
      (↑(markedVertices G W) : Set (physical G W).Vertex)).ConnectedComponent ≤
      Nat.card (supportGraph G W).ConnectedComponent := by
  rw [← Nat.card_congr (markedRealizationIso G W).connectedComponentEquiv]
  exact marked_component_count_le G W

theorem original_source_marked_iff (e : G.Edge) :
    (physical G W).src (edgeLabels G W (Sum.inr e)) ∈ markedVertices G W ↔ e ∈ W := by
  change vertexLabels G W ((network G W).src ((edgeLabels G W).symm (edgeLabels G W (Sum.inr e)))) ∈ _ ↔ _
  rw [Equiv.symm_apply_apply, vertexLabels_mem_marked]
  exact source_marked_iff G W e

theorem original_target_marked_iff (e : G.Edge) :
    (physical G W).dst (edgeLabels G W (Sum.inr e)) ∈ markedVertices G W ↔ e ∈ W := by
  change vertexLabels G W ((network G W).dst ((edgeLabels G W).symm (edgeLabels G W (Sum.inr e)))) ∈ _ ↔ _
  rw [Equiv.symm_apply_apply, vertexLabels_mem_marked]
  exact target_marked_iff G W e

theorem density_physical_projection (P : G.CycleSpace → Prop) :
    Finite.density (fun x : (physical G W).CycleSpace => P (physicalCycleSpaceEquiv G W x)) =
      Finite.density P := by
  exact Finite.density_equiv (physicalCycleSpaceEquiv G W).toEquiv (fun _ => Iff.rfl)

theorem density_multigraph_projection (P : G.CycleSpace → Prop) :
    Finite.density (fun x : (multigraph G W).CycleSpace => P (multigraphCycleSpaceEquiv G W x)) =
      Finite.density P := by
  exact Finite.density_equiv (multigraphCycleSpaceEquiv G W).toEquiv (fun _ => Iff.rfl)

end Erdos1016.ShortProof.IncidencePaths
