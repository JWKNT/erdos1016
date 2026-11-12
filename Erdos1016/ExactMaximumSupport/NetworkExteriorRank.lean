import Erdos1016.ExactMaximumSupport.NetworkMultigraph
import Erdos1016.ExactMaximumSupport.CycleRegions
import Erdos1016.ExactMaximumSupport.LargeGirth.PieceCore
import Erdos1016.ExactMaximum.NetEmbed

set_option autoImplicit false
set_option maxHeartbeats 1500000

/-!
# Exact rank of the network outside a word

The network edge restriction and the induced physical multigraph have the
same cycle rank. The proof reindexes all retained physical labels and vertices;
parallel edges and isolated retained vertices are preserved.
-/
noncomputable section
namespace Erdos1016.ExactMaximumSupport.NetworkExteriorRank
open BoundaryTrace BoundaryTrace.Network BoundaryDecay FiniteMultiGraph
open LargeGirth PieceCore

local instance exteriorRankDecidable (p : Prop) : Decidable p := Classical.propDecidable p

variable {V E : Type*} [Fintype V] [Fintype E] (N : Network V E)

/-- Every induced subgraph of the canonical physical network model is loopless. -/
theorem induced_loopless (R : Finset (NetworkMultigraph.graph N).Vertex) :
    (Induced.graph (NetworkMultigraph.graph N) R).IsLoopless := by
  intro e he
  have h := congrArg (Induced.vertex (NetworkMultigraph.graph N) R) he
  rw [Induced.vertex_src,Induced.vertex_dst] at h
  exact NetworkMultigraph.isLoopless N _ h

section Induced
variable (S : V → Prop) (R : Finset (NetworkMultigraph.graph N).Vertex)
  (hS : ∀ v, S v ↔ NetworkMultigraph.vertices N v ∈ R)

def vertexEquiv : {v : V // S v} ≃ (Induced.graph (NetworkMultigraph.graph N) R).Vertex :=
  (Equiv.subtypeEquiv (NetworkMultigraph.vertices N) hS).trans
    (Induced.vertices (NetworkMultigraph.graph N) R)

include hS in
theorem inside_iff (e : E) : N.inside S e ↔
    NetworkMultigraph.edges N e ∈ (NetworkMultigraph.graph N).internalEdges R := by
  simp only [inside, internalEdges, Finset.mem_filter, Finset.mem_univ, true_and,
    NetworkMultigraph.src_edges,NetworkMultigraph.dst_edges,← hS]

def edgeEquiv : {e : E // N.inside S e} ≃
    (Induced.graph (NetworkMultigraph.graph N) R).Edge :=
  (Equiv.subtypeEquiv (NetworkMultigraph.edges N) (inside_iff N S R hS)).trans
    (Induced.edges (NetworkMultigraph.graph N) R)

/-- The induced network and physical induced graph are literally relabelled copies. -/
def inducedRelabel : Relabel (N.induce S)
    (Induced.graph (NetworkMultigraph.graph N) R).looplessNetwork where
  φ := vertexEquiv N S R hS
  ψ := (edgeEquiv N S R hS).trans (Equiv.subtypeUnivEquiv (induced_loopless N R)).symm
  src e := by
    change (Induced.graph (NetworkMultigraph.graph N) R).src (edgeEquiv N S R hS e) = _
    simp only [edgeEquiv,vertexEquiv,Equiv.trans_apply,Equiv.subtypeEquiv_apply,
      Induced.graph_src,NetworkMultigraph.src_edges]
    simp [Induced.graph,Network.induce,NetworkMultigraph.src_edges]
  dst e := by
    change (Induced.graph (NetworkMultigraph.graph N) R).dst (edgeEquiv N S R hS e) = _
    simp only [edgeEquiv,vertexEquiv,Equiv.trans_apply,Equiv.subtypeEquiv_apply,
      Induced.graph_dst,NetworkMultigraph.dst_edges]
    simp [Induced.graph,Network.induce,NetworkMultigraph.dst_edges]

include hS in
/-- Rank is unchanged when isolated excluded vertices are discarded and labels reindexed. -/
theorem rank_induce_eq : networkRank (N.induce S) =
    (Induced.graph (NetworkMultigraph.graph N) R).cycleRank := by
  rw [(Induced.graph (NetworkMultigraph.graph N) R).cycleRank_eq_networkRank (induced_loopless N R)]
  exact (inducedRelabel N S R hS).networkRank_eq.symm

end Induced

/-- The literal exterior-rank expression in the pole outside-rank statement. -/
theorem outside_rank_eq (A : N.Word) :
    networkRank (N.sub (fun e => N.deg A (N.src e)=0 ∧ N.deg A (N.dst e)=0)) =
      (Induced.graph (NetworkMultigraph.graph N)
        (CycleRegions.region (NetworkMultigraph.graph N) (NetworkMultigraph.wordEquiv N A))ᶜ).cycleRank := by
  let S : V → Prop := fun v => N.deg A v = 0
  let R := (CycleRegions.region (NetworkMultigraph.graph N) (NetworkMultigraph.wordEquiv N A))ᶜ
  have hS : ∀ v, S v ↔ NetworkMultigraph.vertices N v ∈ R := by
    intro v
    simp [S,R,CycleRegions.mem_region,NetworkMultigraph.selectedDegree_wordEquiv]
  calc
    networkRank (N.sub (fun e => N.deg A (N.src e)=0 ∧ N.deg A (N.dst e)=0)) =
        networkRank (N.sub (N.inside S)) := by
      apply N.networkRank_sub_congr
      rfl
    _ = networkRank (N.induce S) := (N.networkRank_induce S).symm
    _ = _ := rank_induce_eq N S R hS

end Erdos1016.ExactMaximumSupport.NetworkExteriorRank
