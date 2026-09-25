import Erdos1016.Cycles.Geometry.CycleWalkExistence
import Erdos1016.Decomposition.TwoCore.PhysicalCore
import Erdos1016.Cycles.Geometry.ApexCycleLift

set_option autoImplicit false
set_option maxHeartbeats 800000

noncomputable section
namespace Erdos1016.Proof.PhysicalCycleEmbedding
open Nonbacktracking BoundaryDecay BoundaryTrace CycleSupply
open scoped BigOperators

local instance (p : Prop) : Decidable p := Classical.propDecidable p

/-- An embedding of actual physical vertices and edges preserving both
endpoints. No contraction or suppression is permitted. -/
structure Embedding (H G : PhysicalGraph) where
  vertex : H.Vertex ↪ G.Vertex
  edge : H.Edge ↪ G.Edge
  src : ∀ e, G.src (edge e) = vertex (H.src e)
  dst : ∀ e, G.dst (edge e) = vertex (H.dst e)

variable {H G : PhysicalGraph}

def Embedding.graphHom (E : Embedding H G) : H.toSimpleGraph →g G.toSimpleGraph where
  toFun := E.vertex
  map_rel' := by
    intro u v huv
    rcases huv with ⟨e, he, hs | hs⟩
    · exact ⟨E.edge e, one_ne_zero, Or.inl
        ⟨(E.src e).trans (congrArg E.vertex hs.1), (E.dst e).trans (congrArg E.vertex hs.2)⟩⟩
    · exact ⟨E.edge e, one_ne_zero, Or.inr
        ⟨(E.src e).trans (congrArg E.vertex hs.1), (E.dst e).trans (congrArg E.vertex hs.2)⟩⟩

private structure Representative (C : H.CycleWord) where
  root : H.Vertex
  walk : H.toSimpleGraph.Walk root root
  isCycle : walk.IsCycle
  word_eq : cycleWordOfWalk H walk isCycle = C

private def representative (C : H.CycleWord) : Representative C :=
  Classical.choice (by
    obtain ⟨u, p, hp, heq⟩ := exists_cycle_walk_of_cycleWord H C
    exact ⟨⟨u, p, hp, heq⟩⟩)

/-- Lift a physical cycle by mapping any representative simple closed walk.
The coordinate theorem below makes the result independent of that choice. -/
def Embedding.liftCycle (E : Embedding H G) (C : H.CycleWord) : G.CycleWord :=
  cycleWordOfWalk G ((representative C).walk.map E.graphHom)
    ((representative C).isCycle.map E.vertex.injective)

theorem Embedding.liftCycle_coord (E : Embedding H G) (C : H.CycleWord) (e : H.Edge) :
    (E.liftCycle C).1 (E.edge e) = C.1 e := by
  let r := representative C
  have hp : physicalPair G (E.edge e) = Sym2.map E.graphHom (physicalPair H e) := by
    change s(G.src (E.edge e), G.dst (E.edge e)) = s(E.vertex (H.src e), E.vertex (H.dst e))
    rw [E.src, E.dst]
  have hmem : physicalPair G (E.edge e) ∈ (r.walk.map E.graphHom).edges ↔
      physicalPair H e ∈ r.walk.edges := by
    rw [SimpleGraph.Walk.edges_map, hp]
    exact List.mem_map_of_injective (Sym2.map.injective E.vertex.injective)
  change walkWord G (r.walk.map E.graphHom) (E.edge e) = C.1 e
  have heq : walkWord H r.walk e = C.1 e := congrArg (fun C : H.CycleWord => C.1 e) r.word_eq
  rw [← heq]
  simp only [walkWord, hmem]

theorem Embedding.liftCycle_injective (E : Embedding H G) : Function.Injective E.liftCycle := by
  intro C D hCD
  apply Subtype.ext
  funext e
  have heq := congrArg (fun C : G.CycleWord => C.1 (E.edge e)) hCD
  simpa only [E.liftCycle_coord] using heq

theorem Embedding.liftCycle_length (E : Embedding H G) (C : H.CycleWord) :
    BoundaryDecay.Cycle.length (E.liftCycle C) = BoundaryDecay.Cycle.length C := by
  unfold Embedding.liftCycle
  rw [cycleWordOfWalk_length, SimpleGraph.Walk.length_map]
  have heq := congrArg BoundaryDecay.Cycle.length (representative C).word_eq
  rwa [cycleWordOfWalk_length] at heq

theorem Embedding.liftCycle_vertices (E : Embedding H G) (C : H.CycleWord) :
    Cycle.vertices (E.liftCycle C) = (Cycle.vertices C).image E.vertex := by
  let r := representative C
  have hv (v : H.Vertex) : v ∈ Cycle.vertices C ↔ v ∈ r.walk.support := by
    have ht := used_walkWord_iff H r.walk r.isCycle v
    change v ∈ Cycle.vertices (cycleWordOfWalk H r.walk r.isCycle) ↔ _ at ht
    simpa only [r.word_eq] using ht
  ext v
  change v ∈ G.usedVertices (walkWord G (r.walk.map E.graphHom)) ↔ _
  rw [used_walkWord_iff G _ (r.isCycle.map E.vertex.injective),
    SimpleGraph.Walk.support_map, List.mem_map, Finset.mem_image]
  constructor
  · rintro ⟨u, hu, heq⟩
    exact ⟨u, (hv u).mpr hu, heq⟩
  · rintro ⟨u, hu, heq⟩
    exact ⟨u, (hv u).mp hu, heq⟩

theorem Embedding.liftCycle_weight (E : Embedding H G) (C : H.CycleWord) :
    cycleWeight (E.liftCycle C) = cycleWeight C := by
  simp only [cycleWeight, E.liftCycle_length]

def Embedding.liftFamily (E : Embedding H G) (F : Finset H.CycleWord) : Finset G.CycleWord :=
  F.image E.liftCycle

theorem Embedding.liftFamily_weight (E : Embedding H G) (F : Finset H.CycleWord) :
    cycleWeightSum (E.liftFamily F) = cycleWeightSum F := by
  unfold cycleWeightSum Embedding.liftFamily
  rw [Finset.sum_image (fun C hC D hD heq => E.liftCycle_injective heq)]
  exact Finset.sum_congr rfl (fun C hC => E.liftCycle_weight C)

/-- The literal induced physical graph embeds by forgetting only its finite
reindexing and the proofs of shore membership. -/
def induced (G : PhysicalGraph) (S : Finset G.Vertex) :
    Embedding (FiniteTwoCore.inducedPhysical G S) G where
  vertex := {
    toFun := fun v => ((Fintype.equivFin (Network.Shore.InsideVertex S)).symm v).1
    inj' := fun u v huv => (Fintype.equivFin _).symm.injective (Subtype.ext huv) }
  edge := {
    toFun := fun e => ((Fintype.equivFin (Network.Shore.InsideEdge G.traceNetwork S)).symm e).1
    inj' := fun e f hef => (Fintype.equivFin _).symm.injective (Subtype.ext hef) }
  src := by
    intro e
    simp [FiniteTwoCore.inducedPhysical, FiniteTwoCore.inducedNetwork, physicalize]
    rfl
  dst := by
    intro e
    simp [FiniteTwoCore.inducedPhysical, FiniteTwoCore.inducedNetwork, physicalize]
    rfl

theorem induced_vertex_mem (G : PhysicalGraph) (S : Finset G.Vertex)
    (v : (FiniteTwoCore.inducedPhysical G S).Vertex) : (induced G S).vertex v ∈ S :=
  ((Fintype.equivFin (Network.Shore.InsideVertex S)).symm v).2

theorem induced_vertex_range (G : PhysicalGraph) (S : Finset G.Vertex) (v : G.Vertex) :
    (∃ u, (induced G S).vertex u = v) ↔ v ∈ S := by
  constructor
  · rintro ⟨u, rfl⟩
    exact induced_vertex_mem G S u
  · intro hv
    refine ⟨Fintype.equivFin (Network.Shore.InsideVertex S) ⟨v, hv⟩, ?_⟩
    simp [induced]

/-- The induced embedding reflects adjacency as well as preserving it. -/
theorem induced_adj_iff (G : PhysicalGraph) (S : Finset G.Vertex)
    (u v : (FiniteTwoCore.inducedPhysical G S).Vertex) :
    (FiniteTwoCore.inducedPhysical G S).toSimpleGraph.Adj u v ↔
      G.toSimpleGraph.Adj ((induced G S).vertex u) ((induced G S).vertex v) := by
  let e := Fintype.equivFin (Network.Shore.InsideVertex S)
  have ht := (FiniteTwoCore.inducedPhysicalGraphIso G S).map_rel_iff'
    (a := e.symm u) (b := e.symm v)
  change (FiniteTwoCore.inducedPhysical G S).toSimpleGraph.Adj (e (e.symm u)) (e (e.symm v)) ↔
    (Network.Shore.inside G.traceNetwork S).graph.Adj (e.symm u) (e.symm v) at ht
  simp only [Equiv.apply_symm_apply] at ht
  rw [Network.Shore.inside_graph_eq_induce, G.traceNetwork_graph] at ht
  exact ht

theorem induced_liftCycle_subset (G : PhysicalGraph) (S : Finset G.Vertex)
    (C : (FiniteTwoCore.inducedPhysical G S).CycleWord) :
    Cycle.vertices ((induced G S).liftCycle C) ⊆ S := by
  rw [(induced G S).liftCycle_vertices]
  intro v hv
  obtain ⟨u, hu, rfl⟩ := Finset.mem_image.mp hv
  exact induced_vertex_mem G S u

/-- Composition retains the literal vertex and edge injections. -/
def Embedding.comp {K : PhysicalGraph} (E : Embedding H G) (F : Embedding G K) :
    Embedding H K where
  vertex := E.vertex.trans F.vertex
  edge := E.edge.trans F.edge
  src := fun e => (F.src (E.edge e)).trans (congrArg F.vertex (E.src e))
  dst := fun e => (F.dst (E.edge e)).trans (congrArg F.vertex (E.dst e))

/-- The ordinary graph embeds in its literal one-apex completion. -/
def apex (H : PhysicalGraph) : Embedding H (coreApexGraph H) where
  vertex := ⟨coreVertexLift H, coreVertexLift_injective H⟩
  edge := ⟨coreEdgeLift H, coreEdgeLift_injective H⟩
  src := coreEdgeLift_src H
  dst := coreEdgeLift_dst H

/-- The original support of an induced cycle in the one-apex owner. -/
theorem induced_apex_liftCycle_vertices (G : PhysicalGraph) (S : Finset G.Vertex)
    (C : (FiniteTwoCore.inducedPhysical G S).CycleWord) :
    Cycle.vertices (((induced G S).comp (apex G)).liftCycle C) =
      ((Cycle.vertices C).image (induced G S).vertex).image (coreVertexLift G) := by
  rw [Embedding.liftCycle_vertices, Finset.image_image]
  rfl

end Erdos1016.Proof.PhysicalCycleEmbedding
