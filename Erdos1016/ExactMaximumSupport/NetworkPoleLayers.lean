import Erdos1016.ExactMaximumSupport.PathForestProbability
import Erdos1016.ExactMaximumSupport.NetworkMultigraph

set_option autoImplicit false
set_option maxHeartbeats 1000000

/-!
# Distance layers of path-rich networks

The canonical labelled multigraph preserves the original vertices, physical
edge labels, path counts, rank, and distances. The uniform affine layer bound
therefore applies to the network's actual distance layers.
-/

noncomputable section

namespace Erdos1016.ExactMaximumSupport.NetworkPoleLayers
open BoundaryTrace BoundaryTrace.Network BoundaryDecay FiniteMultiGraph

local instance networkPoleLayersDecidable (p : Prop) : Decidable p := Classical.propDecidable p

variable {V E : Type*} [Fintype V] [Fintype E] (N : Network V E)

/-- Canonical relabelling preserves ordinary distances on a connected network. -/
theorem distance_eq (hN : N.graph.Connected) (u v : V) :
    (NetworkMultigraph.graph N).toSimpleGraph.dist
      (NetworkMultigraph.vertices N u) (NetworkMultigraph.vertices N v) =
      N.graph.dist u v := by
  apply Nat.le_antisymm
  · obtain ⟨p, hp⟩ := hN.exists_walk_length_eq_dist u v
    have h := SimpleGraph.dist_le (p.map (NetworkMultigraph.graphIso N).toHom)
    simpa only [NetworkMultigraph.graphIso_apply, SimpleGraph.Walk.length_map, hp] using h
  · obtain ⟨p, hp⟩ := (NetworkMultigraph.connected N hN).exists_walk_length_eq_dist
      (NetworkMultigraph.vertices N u) (NetworkMultigraph.vertices N v)
    have h := SimpleGraph.dist_le (p.map (NetworkMultigraph.graphIso N).symm.toHom)
    change N.graph.dist ((NetworkMultigraph.vertices N).symm (NetworkMultigraph.vertices N u))
      ((NetworkMultigraph.vertices N).symm (NetworkMultigraph.vertices N v)) ≤ _ at h
    simpa only [Equiv.symm_apply_apply, SimpleGraph.Walk.length_map, hp] using h

/-- Integer-indexed layer cardinalities are exactly preserved, including empty layers. -/
theorem layer_card_eq (hN : N.graph.Connected) (s : V) (j : ℤ) :
    (Finset.univ.filter fun v : (NetworkMultigraph.graph N).Vertex =>
      ((NetworkMultigraph.graph N).toSimpleGraph.dist (NetworkMultigraph.vertices N s) v : ℤ)
        = j).card =
      (Finset.univ.filter fun v : V => (N.graph.dist s v : ℤ) = j).card := by
  classical
  let e := NetworkMultigraph.vertices N
  have hm : (Finset.univ.filter fun v : V => (N.graph.dist s v : ℤ) = j).map e.toEmbedding =
      Finset.univ.filter fun v : (NetworkMultigraph.graph N).Vertex =>
        ((NetworkMultigraph.graph N).toSimpleGraph.dist (e s) v : ℤ) = j := by
    ext w
    obtain ⟨v, rfl⟩ := e.surjective w
    simp only [Finset.mem_map, Finset.mem_filter, Finset.mem_univ, true_and,
      Equiv.toEmbedding_apply, e.injective.eq_iff, exists_eq_right]
    exact (congrArg (fun n : ℕ => (n : ℤ) = j) (distance_eq N hN s v).symm).to_iff
  rw [← hm, Finset.card_map]

omit N in
/-- A fixed excess above one half gives a uniform bound on actual network layers. -/
theorem exists_path_layer_bound_501 :
    ∃ B : ℕ, ∀ {V E : Type*} [Fintype V] [Fintype E]
      (N : Network V E) (ports : Finset V) (s t : V),
      N.graph.Connected → (∀ v, N.deg (fun _ => 1) v ≤ 3) →
      (∀ v, v ∉ ports → N.deg (fun _ => 1) v = 3) →
      s ∈ ports → t ∈ ports → s ≠ t →
      501 * 2 ^ networkRank N ≤ 1000 * N.numPaths s t →
      ∀ j : ℤ, (Finset.univ.filter fun v => (N.graph.dist s v : ℤ) = j).card ≤
        B * (ports.card + 1) ^ 2 := by
  classical
  obtain ⟨B, hB⟩ := PathForestProbability.exists_path_layer_bound_501
  refine ⟨B, ?_⟩
  intro V E _ _ N ports s t hN hdeg hcubic hs ht hst hp j
  let e := NetworkMultigraph.vertices N
  let P := ports.map e.toEmbedding
  have hdeg' : ∀ v, (NetworkMultigraph.graph N).degree v ≤ 3 := by
    intro w
    obtain ⟨v, rfl⟩ := e.surjective w
    simpa only [e, NetworkMultigraph.degree] using hdeg v
  have hcubic' : ∀ v, v ∉ P → (NetworkMultigraph.graph N).degree v = 3 := by
    intro w hw
    obtain ⟨v, rfl⟩ := e.surjective w
    have hv : v ∉ ports := by
      intro hv
      exact hw (Finset.mem_map.mpr ⟨v, hv, rfl⟩)
    simpa only [e, NetworkMultigraph.degree] using hcubic v hv
  have hp' : 501 * 2 ^ (NetworkMultigraph.graph N).cycleRank ≤
      1000 * (NetworkMultigraph.graph N).looplessNetwork.numPaths (e s) (e t) := by
    simpa only [e, NetworkMultigraph.cycleRank, NetworkMultigraph.numPaths] using hp
  have h := hB (NetworkMultigraph.graph N) P (e s) (e t)
    (NetworkMultigraph.isLoopless N) (NetworkMultigraph.connected N hN) hdeg' hcubic'
    (Finset.mem_map.mpr ⟨s, hs, rfl⟩) (Finset.mem_map.mpr ⟨t, ht, rfl⟩)
    (fun he => hst (e.injective he)) hp' j
  simpa only [P, e, Finset.card_map, layer_card_eq N hN s j] using h

omit N in
/-- With two designated ports, every layer has the uniform bound `9 * B`. -/
theorem exists_two_port_layer_bound_501 :
    ∃ B : ℕ, ∀ {V E : Type*} [Fintype V] [Fintype E]
      (N : Network V E) (s t : V),
      N.graph.Connected → (∀ v, N.deg (fun _ => 1) v ≤ 3) →
      (∀ v, v ≠ s → v ≠ t → N.deg (fun _ => 1) v = 3) → s ≠ t →
      501 * 2 ^ networkRank N ≤ 1000 * N.numPaths s t →
      ∀ j : ℤ, (Finset.univ.filter fun v => (N.graph.dist s v : ℤ) = j).card ≤ 9 * B := by
  classical
  obtain ⟨B, hB⟩ := exists_path_layer_bound_501
  refine ⟨B, ?_⟩
  intro V E _ _ N s t hN hdeg hcubic hst hp j
  have hcubic' : ∀ v, v ∉ ({s, t} : Finset V) → N.deg (fun _ => 1) v = 3 := by
    intro v hv
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hv
    exact hcubic v hv.1 hv.2
  have h := hB N {s, t} s t hN hdeg hcubic' (by simp) (by simp) hst hp j
  simpa only [Finset.card_pair hst, Nat.reduceAdd, Nat.reducePow, Nat.mul_comm B 9] using h

end Erdos1016.ExactMaximumSupport.NetworkPoleLayers
