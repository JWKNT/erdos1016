import Erdos1016.ExactMaximumSupport.LargeGirth.SimpleRealization
import Erdos1016.Graph.Pruning.CycleCore
import Erdos1016.Graph.Pruning.MarkedCore
import Erdos1016.Graph.Multigraph.InducedDeletionBounds
import Erdos1016.Graph.Multigraph.InducedSimpleRegions
import Erdos1016.ExactMaximumSupport.CubicReduction.CubicCore
import Erdos1016.Cycles.Geometry.CycleWalkExistence

set_option autoImplicit false
set_option maxHeartbeats 1500000

/-!
# Actual induced cores of pieces

The induced multigraph retains every internal physical edge, including loops
and parallel labels. High girth supplies the simple realization needed by
the existing full two-core construction.
-/
noncomputable section
open scoped BigOperators
namespace Erdos1016.ExactMaximumSupport.LargeGirth.PieceCore
open FiniteMultiGraph ShortProof.CycleCore

local instance pieceDecidable (p : Prop) : Decidable p := Classical.propDecidable p

namespace Induced
variable (G : FiniteMultiGraph) (X : Finset G.Vertex)

abbrev Vertex := {v : G.Vertex // v ∈ X}
abbrev Edge := {e : G.Edge // e ∈ G.internalEdges X}
def vertices : Vertex G X ≃ Fin (Fintype.card (Vertex G X)) := Fintype.equivFin _
def edges : Edge G X ≃ Fin (Fintype.card (Edge G X)) := Fintype.equivFin _

def graph : FiniteMultiGraph where
  vertexCount := Fintype.card (Vertex G X)
  edgeCount := Fintype.card (Edge G X)
  src e := vertices G X ⟨G.src ((edges G X).symm e).1,
    (Finset.mem_filter.mp ((edges G X).symm e).2).2.1⟩
  dst e := vertices G X ⟨G.dst ((edges G X).symm e).1,
    (Finset.mem_filter.mp ((edges G X).symm e).2).2.2⟩

def vertex (v : (graph G X).Vertex) : G.Vertex := ((vertices G X).symm v).1
def edge (e : (graph G X).Edge) : G.Edge := ((edges G X).symm e).1

@[simp] theorem vertexCount : (graph G X).vertexCount = X.card := by
  simp [graph, Vertex, Fintype.card_coe]
@[simp] theorem edgeCount : (graph G X).edgeCount = (G.internalEdges X).card := by
  simp [graph, Edge, Fintype.card_coe]
@[simp] theorem vertex_src (e : (graph G X).Edge) :
    vertex G X ((graph G X).src e) = G.src (edge G X e) := by simp [vertex, graph, edge]
@[simp] theorem vertex_dst (e : (graph G X).Edge) :
    vertex G X ((graph G X).dst e) = G.dst (edge G X e) := by simp [vertex, graph, edge]
@[simp] theorem vertex_vertices (v : Vertex G X) :
    vertex G X (vertices G X v) = v.1 := by simp [vertex]
theorem vertex_injective : Function.Injective (vertex G X) := by
  intro a b h
  exact (vertices G X).symm.injective (Subtype.ext h)
theorem edge_injective : Function.Injective (edge G X) := by
  intro a b h
  exact (edges G X).symm.injective (Subtype.ext h)
theorem vertex_mem (v : (graph G X).Vertex) : vertex G X v ∈ X :=
  ((vertices G X).symm v).2

@[simp] theorem graph_src (e : Edge G X) :
    (graph G X).src (edges G X e) = vertices G X ⟨G.src e.1, (Finset.mem_filter.mp e.2).2.1⟩ := by
  simp [graph]
@[simp] theorem graph_dst (e : Edge G X) :
    (graph G X).dst (edges G X e) = vertices G X ⟨G.dst e.1, (Finset.mem_filter.mp e.2).2.2⟩ := by
  simp [graph]

/-- Exact underlying induced graph, without discarding physical labels. -/
def graphIso : G.toSimpleGraph.induce (↑X : Set G.Vertex) ≃g (graph G X).toSimpleGraph where
  toEquiv := vertices G X
  map_rel_iff' := by
    intro u v
    change (graph G X).toSimpleGraph.Adj (vertices G X u) (vertices G X v) ↔
      G.toSimpleGraph.Adj u.1 v.1
    constructor
    · rintro ⟨hne, e, he⟩
      have hne' : u.1 ≠ v.1 := by
        intro h
        exact hne (congrArg (vertices G X) (Subtype.ext h))
      refine ⟨hne', edge G X e, ?_⟩
      rcases he with he | he
      · left
        exact ⟨by simpa only [vertex_src, vertex_dst, vertex_vertices] using congrArg (vertex G X) he.1,
          by simpa only [vertex_src, vertex_dst, vertex_vertices] using congrArg (vertex G X) he.2⟩
      · right
        exact ⟨by simpa only [vertex_src, vertex_dst, vertex_vertices] using congrArg (vertex G X) he.1,
          by simpa only [vertex_src, vertex_dst, vertex_vertices] using congrArg (vertex G X) he.2⟩
    · rintro ⟨hne, e, he⟩
      have hm : e ∈ G.internalEdges X := by
        rcases he with he | he <;> simp [internalEdges, he.1, he.2, u.2, v.2]
      refine ⟨fun h => hne (congrArg Subtype.val ((vertices G X).injective h)), edges G X ⟨e, hm⟩, ?_⟩
      rw [graph_src, graph_dst]
      rcases he with he | he
      · exact Or.inl ⟨congrArg (vertices G X) (Subtype.ext he.1),
          congrArg (vertices G X) (Subtype.ext he.2)⟩
      · exact Or.inr ⟨congrArg (vertices G X) (Subtype.ext he.1),
          congrArg (vertices G X) (Subtype.ext he.2)⟩

theorem connected (hX : (G.toSimpleGraph.induce (↑X : Set G.Vertex)).Connected) :
    (graph G X).toSimpleGraph.Connected := (graphIso G X).connected_iff.mp hX

/-- Every retained incidence is an original physical incidence. -/
theorem degree_le (v : (graph G X).Vertex) :
    (graph G X).degree v ≤ G.degree (vertex G X v) := by
  have hs : (Finset.univ.filter (fun e => (graph G X).src e = v)).card ≤
      (Finset.univ.filter (fun e => G.src e = vertex G X v)).card := by
    apply Finset.card_le_card_of_injOn (edge G X)
    · intro e he
      have h := congrArg (vertex G X) (Finset.mem_filter.mp he).2
      simpa only [vertex_src, Finset.mem_filter, Finset.mem_univ, true_and] using h
    · intro a _ b _ h
      exact edge_injective G X h
  have ht : (Finset.univ.filter (fun e => (graph G X).dst e = v)).card ≤
      (Finset.univ.filter (fun e => G.dst e = vertex G X v)).card := by
    apply Finset.card_le_card_of_injOn (edge G X)
    · intro e he
      have h := congrArg (vertex G X) (Finset.mem_filter.mp he).2
      simpa only [vertex_dst, Finset.mem_filter, Finset.mem_univ, true_and] using h
    · intro a _ b _ h
      exact edge_injective G X h
  simpa [FiniteMultiGraph.degree, selectedDegree] using Nat.add_le_add hs ht

/-- Absence of loops and parallel labels is recovered on the retained labels. -/
theorem internal_simple (h3 : ¬ (graph G X).HasCycleShorterThan 3) :
    (∀ e ∈ G.internalEdges X, G.src e ≠ G.dst e) ∧
    (∀ e ∈ G.internalEdges X, ∀ f ∈ G.internalEdges X,
      ((G.src e = G.src f ∧ G.dst e = G.dst f) ∨
       (G.src e = G.dst f ∧ G.dst e = G.src f)) → e = f) := by
  constructor
  · intro e he h
    apply noLoops_of_no_short_cycle (graph G X) h3 (edges G X ⟨e, he⟩)
    rw [graph_src, graph_dst]
    exact congrArg (vertices G X) (Subtype.ext h)
  · intro e he f hf h
    have h' : (graph G X).src (edges G X ⟨e, he⟩) =
        (graph G X).src (edges G X ⟨f, hf⟩) ∧
        (graph G X).dst (edges G X ⟨e, he⟩) =
        (graph G X).dst (edges G X ⟨f, hf⟩) ∨
        (graph G X).src (edges G X ⟨e, he⟩) =
        (graph G X).dst (edges G X ⟨f, hf⟩) ∧
        (graph G X).dst (edges G X ⟨e, he⟩) =
        (graph G X).src (edges G X ⟨f, hf⟩) := by
      simp only [graph_src, graph_dst]
      rcases h with h | h
      · exact Or.inl ⟨congrArg (vertices G X) (Subtype.ext h.1),
          congrArg (vertices G X) (Subtype.ext h.2)⟩
      · exact Or.inr ⟨congrArg (vertices G X) (Subtype.ext h.1),
          congrArg (vertices G X) (Subtype.ext h.2)⟩
    exact congrArg Subtype.val ((edges G X).injective
      (simple_of_no_short_cycle (graph G X) h3 _ _ h'))

/-- The cubic region ledger uses the original physical boundary. -/
theorem order_rank_cut (hX : (G.toSimpleGraph.induce (↑X : Set G.Vertex)).Connected)
    (hcubic : ∀ v ∈ X, G.degree v = 3) :
    X.card + 2 = 2*(graph G X).cycleRank + (G.cutEdges X).card := by
  have he := (graph G X).connected_euler (connected G X hX)
  rw [vertexCount, edgeCount] at he
  have hs := G.sum_region_degree X
  have hd : (∑ v ∈ X, G.degree v) = 3*X.card := by
    rw [Finset.sum_congr rfl hcubic]
    simp [Nat.mul_comm]
  rw [hd] at hs
  omega

end Induced



open CubicReduction Nonbacktracking.FiniteTwoCore

private theorem physical_iso_degree {H K : PhysicalGraph}
    (i : H.toSimpleGraph ≃g K.toSimpleGraph) (v : H.Vertex) : K.degree (i v) = H.degree v := by
  rw [original_degree_eq_graph_degree, original_degree_eq_graph_degree,
    ← SimpleGraph.card_neighborSet_eq_degree, ← SimpleGraph.card_neighborSet_eq_degree]
  exact (Fintype.card_congr (i.mapNeighborSet v)).symm

private theorem physical_iso_rank {H K : PhysicalGraph}
    (i : H.toSimpleGraph ≃g K.toSimpleGraph) (hH : H.IsConnected) : K.cycleRank = H.cycleRank := by
  have hK : K.IsConnected := i.connected_iff.mp hH
  have hv : H.vertexCount = K.vertexCount := by
    simpa only [PhysicalGraph.Vertex, Fintype.card_fin] using i.card_eq
  have hs : (∑ v : K.Vertex, K.degree v) = ∑ v : H.Vertex, H.degree v := by
    calc
      _ = ∑ v : H.Vertex, K.degree (i v) := (Equiv.sum_comp i.toEquiv _).symm
      _ = _ := Finset.sum_congr rfl (fun v _ => physical_iso_degree i v)
  have hsumH := (asMultigraph H).sum_degree
  have hsumK := (asMultigraph K).sum_degree
  have hmH (v : H.Vertex) : (asMultigraph H).degree v = H.degree v :=
    asMultigraph_selectedDegree H (fun _ => 1) v
  have hmK (v : K.Vertex) : (asMultigraph K).degree v = K.degree v :=
    asMultigraph_selectedDegree K (fun _ => 1) v
  change (∑ v : H.Vertex, (asMultigraph H).degree v) = 2*H.edgeCount at hsumH
  change (∑ v : K.Vertex, (asMultigraph K).degree v) = 2*K.edgeCount at hsumK
  simp only [hmH] at hsumH
  simp only [hmK] at hsumK
  have heH := (asMultigraph H).connected_euler (by rwa [asMultigraph_toSimpleGraph])
  have heK := (asMultigraph K).connected_euler (by rwa [asMultigraph_toSimpleGraph])
  rw [asMultigraph_cycleRank] at heH heK
  change H.cycleRank + H.vertexCount = H.edgeCount + 1 at heH
  change K.cycleRank + K.vertexCount = K.edgeCount + 1 at heK
  omega

private theorem core_nonempty (H : PhysicalGraph) (hr : 0 < H.cycleRank) : (core H).Nonempty := by
  obtain ⟨x, hx⟩ : ∃ x : H.CycleSpace, x ≠ 0 :=
    Module.finrank_pos_iff_exists_ne_zero.mp hr
  have hx0 : x.1 ≠ 0 := fun h => hx (Subtype.ext h)
  obtain ⟨e, he⟩ := Function.ne_iff.mp hx0
  exact ⟨H.src e, (nonzero_edge_in_core H x e he).1⟩

namespace SimpleCore
open FiniteMultiGraph.InducedSimpleRealization
variable (G : FiniteMultiGraph) (X : Finset G.Vertex)
  (hl : ∀ e ∈ G.internalEdges X, G.src e ≠ G.dst e)
  (hp : ∀ e ∈ G.internalEdges X, ∀ f ∈ G.internalEdges X,
    ((G.src e = G.src f ∧ G.dst e = G.dst f) ∨
     (G.src e = G.dst f ∧ G.dst e = G.src f)) → e = f)

abbrev physical := InducedSimpleRealization.graph G X hl hp

/-- The pruned vertex set, returned to the original graph's labels. -/
def region : Finset G.Vertex := (core (physical G X hl hp)).image (Induced.vertex G X)

theorem region_subset : region G X hl hp ⊆ X := by
  intro v hv
  obtain ⟨w, _, rfl⟩ := Finset.mem_image.mp hv
  exact Induced.vertex_mem G X w

theorem region_pullback :
    InducedSimpleRealization.region G X hl hp (region G X hl hp) = core (physical G X hl hp) := by
  ext v
  rw [mem_region]
  change Induced.vertex G X v ∈ (core (physical G X hl hp)).image (Induced.vertex G X) ↔ _
  constructor
  · intro hv
    obtain ⟨w, hw, heq⟩ := Finset.mem_image.mp hv
    exact (Induced.vertex_injective G X heq) ▸ hw
  · intro hv
    exact Finset.mem_image.mpr ⟨v, hv, rfl⟩

private theorem region_internal (e : G.Edge) (he : e ∈ G.internalEdges (region G X hl hp)) :
    e ∈ G.internalEdges X := by
  have h := (Finset.mem_filter.mp he).2
  exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,
    region_subset G X hl hp h.1, region_subset G X hl hp h.2⟩

abbrev coreLoop := fun e he => hl e (region_internal G X hl hp e he)
abbrev coreSimple := fun e he f hf => hp e (region_internal G X hl hp e he)
  f (region_internal G X hl hp f hf)
abbrev result := InducedSimpleRealization.graph G (region G X hl hp)
  (coreLoop G X hl hp) (coreSimple G X hl hp)

/-- Both sides are the same induced core, with their two finite relabellings. -/
def coreIso : (result G X hl hp).toSimpleGraph ≃g
    (corePhysical (physical G X hl hp)).toSimpleGraph := by
  let a := InducedSimpleRealization.graphIso G (region G X hl hp)
    (coreLoop G X hl hp) (coreSimple G X hl hp)
  have b : G.toSimpleGraph.induce (↑(region G X hl hp) : Set G.Vertex) ≃g
      (physical G X hl hp).toSimpleGraph.induce (↑(core (physical G X hl hp)) : Set (physical G X hl hp).Vertex) := by
    have b := regionGraphIso G X hl hp (region G X hl hp) (region_subset G X hl hp)
    rw [region_pullback] at b
    exact b
  exact a.symm.trans (b.trans (ShortProof.CycleCore.graphIso (physical G X hl hp)))

theorem result_rank
    (hc : (G.toSimpleGraph.induce (↑X : Set G.Vertex)).Connected)
    (hr : 0 < (Induced.graph G X).cycleRank) :
    (Induced.graph G (region G X hl hp)).cycleRank = (Induced.graph G X).cycleRank := by
  have hH : (physical G X hl hp).IsConnected :=
    (InducedSimpleRealization.graphIso G X hl hp).connected_iff.mp hc
  have hR : (physical G X hl hp).cycleRank = (Induced.graph G X).cycleRank :=
    (asMultigraph_cycleRank (physical G X hl hp)).symm
  have hcore := ShortProof.CycleCore.physical_connected (physical G X hl hp) hH
    (core_nonempty _ (by rw [hR]; exact hr))
  have hi := physical_iso_rank (coreIso G X hl hp).symm hcore
  have hk := ShortProof.CycleCore.cycleRank_preserved (physical G X hl hp)
  change (asMultigraph (result G X hl hp)).cycleRank = _
  rw [asMultigraph_cycleRank, hi, hk, hR]


theorem result_connected
    (hc : (G.toSimpleGraph.induce (↑X : Set G.Vertex)).Connected)
    (hr : 0 < (Induced.graph G X).cycleRank) :
    (Induced.graph G (region G X hl hp)).toSimpleGraph.Connected := by
  have hH : (physical G X hl hp).IsConnected :=
    (InducedSimpleRealization.graphIso G X hl hp).connected_iff.mp hc
  have hR : (physical G X hl hp).cycleRank = (Induced.graph G X).cycleRank :=
    (asMultigraph_cycleRank (physical G X hl hp)).symm
  have hcore := ShortProof.CycleCore.physical_connected (physical G X hl hp) hH
    (core_nonempty _ (by rw [hR]; exact hr))
  change (asMultigraph (result G X hl hp)).toSimpleGraph.Connected
  rw [asMultigraph_toSimpleGraph]
  exact (coreIso G X hl hp).symm.connected_iff.mp hcore

theorem result_degree_bounds (hmax : ∀ v ∈ X, G.degree v ≤ 3) :
    ∀ v, 2 ≤ (Induced.graph G (region G X hl hp)).degree v ∧
      (Induced.graph G (region G X hl hp)).degree v ≤ 3 := by
  have hH : ∀ v, (physical G X hl hp).degree v ≤ 3 := by
    intro v
    have hd := Induced.degree_le G X v
    have hm := hmax _ (Induced.vertex_mem G X v)
    have he := asMultigraph_selectedDegree (physical G X hl hp) (fun _ => 1) v
    change (Induced.graph G X).degree v = (physical G X hl hp).degree v at he
    omega
  intro v
  have hlo := maximalPhysicalCore_minDegree (physical G X hl hp) (coreIso G X hl hp v)
  have hhi := maximalPhysicalCore_degree_le_three (physical G X hl hp) hH (coreIso G X hl hp v)
  have he := physical_iso_degree (coreIso G X hl hp) v
  change (corePhysical (physical G X hl hp)).degree (coreIso G X hl hp v) =
    (result G X hl hp).degree v at he
  have hm := asMultigraph_selectedDegree (result G X hl hp) (fun _ => 1) v
  change (Induced.graph G (region G X hl hp)).degree v = (result G X hl hp).degree v at hm
  change 2 ≤ (corePhysical (physical G X hl hp)).degree (coreIso G X hl hp v) at hlo
  change (corePhysical (physical G X hl hp)).degree (coreIso G X hl hp v) ≤ 3 at hhi
  omega

theorem result_no_short (g : ℕ) (hg : 3 ≤ g)
    (hshort : ¬ (Induced.graph G X).HasCycleShorterThan g) :
    ¬ (Induced.graph G (region G X hl hp)).HasCycleShorterThan g := by
  have hH : Nonbacktracking.ShortWalks.GirthGreater (physical G X hl hp).toSimpleGraph (g-1) := by
    intro v p hp'
    let C := Nonbacktracking.cycleWordOfWalk (physical G X hl hp) p hp'
    have hc : (Induced.graph G X).IsCycleWord C.1 :=
      (asMultigraph_isCycleWord_iff (physical G X hl hp) C.1).mpr C.2
    have he := Nonbacktracking.cycleWordOfWalk_length (physical G X hl hp) p hp'
    change (Induced.graph G X).wordLength C.1 = p.length at he
    have hn : ¬ (Induced.graph G X).wordLength C.1 < g := fun h => hshort ⟨C.1, hc, h⟩
    omega
  have hcore := maximalPhysicalCore_girthGreater (physical G X hl hp) (g-1) hH
  have hK := girthGreater_graphIso (coreIso G X hl hp).symm (g-1) hcore
  rintro ⟨x, hx, hlen⟩
  have hx' : (result G X hl hp).IsCycleWord x :=
    (asMultigraph_isCycleWord_iff (result G X hl hp) x).mp hx
  obtain ⟨v, p, hp', heq⟩ := Nonbacktracking.exists_cycle_walk_of_cycleWord
    (result G X hl hp) ⟨x, hx'⟩
  have he := Nonbacktracking.cycleWordOfWalk_length (result G X hl hp) p hp'
  rw [heq] at he
  change (Induced.graph G (region G X hl hp)).wordLength x = p.length at he
  have hlen' := hK v p hp'
  omega

/-- Removing leaves preserves rank, so its smaller order decreases the
cubic deficit. This is the original region's physical boundary budget. -/
theorem result_deficit_le
    (hc : (G.toSimpleGraph.induce (↑X : Set G.Vertex)).Connected)
    (hr : 0 < (Induced.graph G X).cycleRank)
    (hcubic : ∀ v ∈ X, G.degree v = 3) :
    (Induced.graph G (region G X hl hp)).cubicDeficit ≤ (G.cutEdges X).card := by
  have he := (Induced.graph G (region G X hl hp)).order_add_two_eq_twice_rank_add_deficit
    (result_connected G X hl hp hc hr)
    (fun v => (result_degree_bounds G X hl hp (fun w hw => (hcubic w hw).le) v).2)
  rw [Induced.vertexCount, result_rank G X hl hp hc hr] at he
  have ho := Induced.order_rank_cut G X hc hcubic
  have hs := Finset.card_le_card (region_subset G X hl hp)
  omega

end SimpleCore

/-- Actual core extraction for a connected cubic region of rank at least two.
The region may sit inside a multigraph; only its own girth is constrained. -/
theorem exists_induced_core (G : FiniteMultiGraph) (X : Finset G.Vertex)
    (hc : (G.toSimpleGraph.induce (↑X : Set G.Vertex)).Connected)
    (hcubic : ∀ v ∈ X, G.degree v = 3)
    (hr : 2 ≤ (Induced.graph G X).cycleRank)
    (g : ℕ) (hg : 3 ≤ g) (hshort : ¬ (Induced.graph G X).HasCycleShorterThan g) :
    ∃ U : Finset G.Vertex, U ⊆ X ∧
      (Induced.graph G U).toSimpleGraph.Connected ∧
      (Induced.graph G U).cycleRank = (Induced.graph G X).cycleRank ∧
      (∀ v, 2 ≤ (Induced.graph G U).degree v ∧ (Induced.graph G U).degree v ≤ 3) ∧
      ¬ (Induced.graph G U).HasCycleShorterThan g ∧
      (Induced.graph G U).cubicDeficit ≤ (G.cutEdges X).card := by
  obtain ⟨hl, hp⟩ := Induced.internal_simple G X
    (no_short_three_of_le (Induced.graph G X) g hg hshort)
  exact ⟨SimpleCore.region G X hl hp, SimpleCore.region_subset G X hl hp,
    SimpleCore.result_connected G X hl hp hc (by omega),
    SimpleCore.result_rank G X hl hp hc (by omega),
    SimpleCore.result_degree_bounds G X hl hp (fun v hv => (hcubic v hv).le),
    SimpleCore.result_no_short G X hl hp g hg hshort,
    SimpleCore.result_deficit_le G X hl hp hc (by omega) hcubic⟩

/-- Actual girth passes to any smaller induced region. Loops and parallel
labels are excluded by the given girth, not by an additional premise. -/
theorem Induced.no_short_mono (G : FiniteMultiGraph) (X Y : Finset G.Vertex)
    (hYX : Y ⊆ X) (g : ℕ) (hg : 3 ≤ g)
    (hshort : ¬ (Induced.graph G X).HasCycleShorterThan g) :
    ¬ (Induced.graph G Y).HasCycleShorterThan g := by
  obtain ⟨hl, hp⟩ := Induced.internal_simple G X
    (no_short_three_of_le (Induced.graph G X) g hg hshort)
  have hi : G.internalEdges Y ⊆ G.internalEdges X := by
    intro e he
    have h := (Finset.mem_filter.mp he).2
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hYX h.1, hYX h.2⟩
  let H := InducedSimpleRealization.graph G X hl hp
  let K := InducedSimpleRealization.graph G Y
    (fun e he => hl e (hi he)) (fun e he f hf => hp e (hi he) f (hi hf))
  let inc : K.toSimpleGraph →g H.toSimpleGraph := {
    toFun := fun v => Induced.vertices G X ⟨Induced.vertex G Y v,
      hYX (Induced.vertex_mem G Y v)⟩
    map_rel' := by
      intro a b hab
      exact (InducedSimpleRealization.graph_adj_iff G X hl hp _ _).mpr
        ((InducedSimpleRealization.adj_vertex_iff G Y _ _ a b).mp hab) }
  have hinj : Function.Injective inc := by
    intro a b he
    apply Induced.vertex_injective G Y
    exact congrArg (fun v : Induced.Vertex G X => v.1) ((Induced.vertices G X).injective he)
  rintro ⟨x, hx, hlen⟩
  have hx' : K.IsCycleWord x := (asMultigraph_isCycleWord_iff K x).mp hx
  obtain ⟨v, p, hp', heq⟩ := Nonbacktracking.exists_cycle_walk_of_cycleWord K ⟨x, hx'⟩
  let q := p.map inc
  have hq : q.IsCycle := (SimpleGraph.Walk.map_isCycle_iff_of_injective hinj).mpr hp'
  let C := Nonbacktracking.cycleWordOfWalk H q hq
  have hC : (Induced.graph G X).IsCycleWord C.1 :=
    (asMultigraph_isCycleWord_iff H C.1).mpr C.2
  have he := Nonbacktracking.cycleWordOfWalk_length K p hp'
  rw [heq] at he
  have hf := Nonbacktracking.cycleWordOfWalk_length H q hq
  change (Induced.graph G Y).wordLength x = p.length at he
  change (Induced.graph G X).wordLength C.1 = q.length at hf
  have hqLen : q.length = p.length := by simp [q]
  exact hshort ⟨C.1, hC, by omega⟩

end Erdos1016.ExactMaximumSupport.LargeGirth.PieceCore
