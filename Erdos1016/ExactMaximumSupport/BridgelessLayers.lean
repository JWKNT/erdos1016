import Erdos1016.ExactMaximum.PoleLayers
import Erdos1016.ExactMaximum.NetSmallCut
import Erdos1016.ExactMaximumSupport.DistanceFourLayers
import Erdos1016.Probability.Avoidance.GeodesicMarker
import Erdos1016.Graph.ConnectedRegionBoundary

set_option autoImplicit false

/-!
# Nonempty and nonsingleton distance layers of a bridgeless pole

All cuts count physical edge labels. A singleton interior layer would have
at least two labels toward smaller distances and two toward larger distances,
contradicting its physical degree three. Parallel labels are retained.
-/
noncomputable section
namespace Erdos1016.ExactMaximumSupport.BridgelessLayers

open BoundaryTrace BoundaryTrace.Network
local instance bridgelessLayersDecidable (p : Prop) : Decidable p := Classical.propDecidable p

variable {V E : Type*} [Fintype V] [Fintype E] (N : Network V E)

/-- Every nontrivial vertex cut of a connected bridgeless network has at least
 two physical labels. A cycle through one crossing label crosses evenly. -/
theorem cutSize_ge_two (hconn : N.graph.Connected) (hbridge : N.IsBridgeless)
    (S : V → Prop) (u v : V) (hu : S u) (hv : ¬ S v) : 2 ≤ N.cutSize S := by
  obtain ⟨p, _⟩ := hconn.exists_isPath u v
  obtain ⟨a, b, ha, hb, hab⟩ :=
    Proof.ConnectedRegionBoundary.Walk.exists_adj_boundary (S := {w | S w}) p hu hv
  obtain ⟨e, he⟩ := hab
  have hc : N.crosses S e := N.crosses_of_joins he ha hb
  obtain ⟨z, hz, hze⟩ := hbridge e
  have hpos : 0 < (N.crossSet S z).card := Finset.card_pos.mpr
    ⟨e, N.mem_crossSet.mpr ⟨hc, hze⟩⟩
  obtain ⟨m, hm⟩ := N.even_card_crossSet S hz.boundary_eq_zero
  have htwo : 2 ≤ (N.crossSet S z).card := by omega
  have hsub : N.crossSet S z ⊆ Finset.univ.filter (N.crosses S) := by
    intro f hf
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ f, (N.mem_crossSet.mp hf).1⟩
  unfold Network.cutSize
  rw [natCard_subtype_eq_card_filter]
  exact htwo.trans (Finset.card_le_card hsub)

omit [Fintype V] [Fintype E] in
/-- Every integer up to an attained distance is itself attained. -/
theorem exists_vertex_at_distance (hconn : N.graph.Connected) (s v : V)
    (j : ℕ) (hj : j ≤ N.graph.dist s v) : ∃ w, N.graph.dist s w = j := by
  obtain ⟨p, hp⟩ := hconn.exists_walk_length_eq_dist s v
  exact ⟨p.getVert j, Probability.GeodesicMarker.dist_getVert hconn p hp j (by omega)⟩

omit [Fintype E] in
/-- In particular every layer up to an attained distance is nonempty. -/
theorem layer_card_pos (hconn : N.graph.Connected) (s v : V)
    (j : ℕ) (hj : j ≤ N.graph.dist s v) :
    0 < Nat.card {w : V // N.graph.dist s w = j} := by
  obtain ⟨w, hw⟩ := exists_vertex_at_distance N hconn s v j hj
  simp only [Nat.card_eq_fintype_card, Fintype.card_subtype]
  exact Finset.card_pos.mpr ⟨w, Finset.mem_filter.mpr ⟨Finset.mem_univ w, hw⟩⟩

omit [Fintype E] in
/-- Connectivity makes the zero layer precisely the source. -/
theorem zero_layer_card (hconn : N.graph.Connected) (s : V) :
    Nat.card {w : V // N.graph.dist s w = 0} = 1 := by
  simp only [Nat.card_eq_fintype_card, Fintype.card_subtype]
  have heq : (Finset.univ.filter fun w => N.graph.dist s w = 0) = {s} := by
    ext w
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
    exact hconn.dist_eq_zero_iff.trans eq_comm
  rw [heq, Finset.card_singleton]

/-- Every layer strictly between the two ports has at least two vertices. -/
theorem internal_layer_card_ge_two (s t : V) (hPole : N.IsBridgelessTwoPole s t)
    (j : ℕ) (hj0 : 0 < j) (hjt : j < N.graph.dist s t) :
    2 ≤ Nat.card {w : V // N.graph.dist s w = j} := by
  simp only [Nat.card_eq_fintype_card, Fintype.card_subtype]
  let layer : Finset V := Finset.univ.filter fun w => N.graph.dist s w = j
  change 2 ≤ layer.card
  by_contra hsmall
  obtain ⟨v, hv⟩ := exists_vertex_at_distance N hPole.connected s t j (by omega)
  have hunique : ∀ w, N.graph.dist s w = j → w = v := by
    intro w hw
    have hcard : layer.card ≤ 1 := by omega
    exact Finset.card_le_one.mp hcard w
      (Finset.mem_filter.mpr ⟨Finset.mem_univ w, hw⟩) v
      (Finset.mem_filter.mpr ⟨Finset.mem_univ v, hv⟩)
  let A : Finset E := Finset.univ.filter (N.crosses fun w => N.graph.dist s w < j)
  let B : Finset E := Finset.univ.filter (N.crosses fun w => N.graph.dist s w ≤ j)
  have hA : 2 ≤ A.card := by
    have h := cutSize_ge_two N hPole.connected hPole.bridgeless
      (fun w => N.graph.dist s w < j) s t (by change N.graph.dist s s < j; rw [SimpleGraph.dist_self]; exact hj0) (by omega)
    simpa only [Network.cutSize, natCard_subtype_eq_card_filter] using h
  have hB : 2 ≤ B.card := by
    have h := cutSize_ge_two N hPole.connected hPole.bridgeless
      (fun w => N.graph.dist s w ≤ j) s t (by change N.graph.dist s s ≤ j; rw [SimpleGraph.dist_self]; exact Nat.zero_le j) (by omega)
    simpa only [Network.cutSize, natCard_subtype_eq_card_filter] using h
  have hdist (e : E) : N.graph.dist s (N.src e) ≤ N.graph.dist s (N.dst e) + 1 ∧
      N.graph.dist s (N.dst e) ≤ N.graph.dist s (N.src e) + 1 :=
    DistanceFourLayers.dist_adj N.graph s hPole.connected ⟨e, Or.inl ⟨rfl, rfl⟩⟩
  have hAB : Disjoint A B := by
    apply Finset.disjoint_left.mpr
    intro e heA heB
    have ha := (Finset.mem_filter.mp heA).2
    have hb := (Finset.mem_filter.mp heB).2
    change ¬ (N.graph.dist s (N.src e) < j ↔ N.graph.dist s (N.dst e) < j) at ha
    change ¬ (N.graph.dist s (N.src e) ≤ j ↔ N.graph.dist s (N.dst e) ≤ j) at hb
    have hd := hdist e
    omega
  have hsub : A ∪ B ⊆ Finset.univ.filter
      (fun e => (1 : ZMod 2) ≠ 0 ∧ (N.src e = v ∨ N.dst e = v)) := by
    intro e he
    have hd := hdist e
    have heq : N.graph.dist s (N.src e) = j ∨ N.graph.dist s (N.dst e) = j := by
      rcases Finset.mem_union.mp he with heA | heB
      · have ha := (Finset.mem_filter.mp heA).2
        change ¬ (N.graph.dist s (N.src e) < j ↔ N.graph.dist s (N.dst e) < j) at ha
        omega
      · have hb := (Finset.mem_filter.mp heB).2
        change ¬ (N.graph.dist s (N.src e) ≤ j ↔ N.graph.dist s (N.dst e) ≤ j) at hb
        omega
    refine Finset.mem_filter.mpr ⟨Finset.mem_univ e, by decide, ?_⟩
    exact heq.elim (fun h => Or.inl (hunique _ h)) (fun h => Or.inr (hunique _ h))
  have hvS : v ≠ s := by intro h; subst v; rw [SimpleGraph.dist_self] at hv; omega
  have hvT : v ≠ t := by intro h; subst v; omega
  have hdegree := hPole.deg_other v hvS hvT
  have hcount := Finset.card_le_card hsub
  rw [Finset.card_union_of_disjoint hAB] at hcount
  change A.card + B.card ≤ N.deg (fun _ => 1) v at hcount
  omega

end Erdos1016.ExactMaximumSupport.BridgelessLayers
