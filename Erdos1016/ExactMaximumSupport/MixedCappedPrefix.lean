import Erdos1016.ExactMaximumSupport.MixedTilesRank

set_option autoImplicit false

/-!
# A forward-oriented chain with one left cap

The tile and interface orientations are the original chain orientations.
The two additional labels go from the left cap to the first tile.
-/

noncomputable section
namespace Erdos1016.ExactMaximumSupport.MixedCappedPrefix
open BoundaryTrace BoundaryTrace.Network BoundaryDecay MixedTiles

variable {k : ℕ}

abbrev Vertex (T : Fin (k+1) → Kind) := MixedTiles.Vertex T ⊕ Unit
abbrev Edge (T : Fin (k+1) → Kind) := ChainEdge T ⊕ Bool

def src (T : Fin (k+1) → Kind) : Edge T → Vertex T
  | Sum.inl e => Sum.inl ((chain T).src e)
  | Sum.inr _ => Sum.inr ()

def dst (T : Fin (k+1) → Kind) : Edge T → Vertex T
  | Sum.inl e => Sum.inl ((chain T).dst e)
  | Sum.inr b => Sum.inl (left T 0 b)

def network (T : Fin (k+1) → Kind) : Network (Vertex T) (Edge T) where
  src := src T
  dst := dst T
  noLoops e := by
    rcases e with e | b
    · exact fun h => (chain T).noLoops e (Sum.inl.inj h)
    · exact Sum.inr_ne_inl

def chainHom (T : Fin (k+1) → Kind) : (chain T).graph →g (network T).graph where
  toFun := Sum.inl
  map_rel' := by
    intro u v h
    obtain ⟨e,he⟩ := h
    refine ⟨Sum.inl e,?_⟩
    rcases he with ⟨hs,ht⟩ | ⟨hs,ht⟩
    · exact Or.inl ⟨congrArg Sum.inl hs,congrArg Sum.inl ht⟩
    · exact Or.inr ⟨congrArg Sum.inl hs,congrArg Sum.inl ht⟩

/-- The one-left-cap model is connected, including a single tile. -/
theorem connected (T : Fin (k+1) → Kind) : (network T).graph.Connected := by
  apply (SimpleGraph.connected_iff_exists_forall_reachable _).mpr
  refine ⟨Sum.inr (),?_⟩
  rintro (⟨i,v⟩ | ⟨⟩)
  · have h : (network T).graph.Adj (Sum.inr ()) (Sum.inl (left T 0 false)) :=
      ⟨Sum.inr false,Or.inl ⟨rfl,rfl⟩⟩
    exact h.reachable.trans ((chain_reachable T i v).map (chainHom T))
  · exact SimpleGraph.Reachable.refl _

/-- The physical rank equals the tile weight. -/
theorem rank (T : Fin (k+1) → Kind) : networkRank (network T)=weight T := by
  have h := network_rank_euler (network T)
  rw [connected_component_card (network T) (connected T)] at h
  have hv : Fintype.card (Vertex T)=2*weight T+1 := by
    simp only [Vertex,Fintype.card_sum,Fintype.card_unit,MixedTiles.vertex_card]
  have he : Fintype.card (Edge T)=3*weight T := by
    change Fintype.card (ChainEdge T ⊕ Bool)=3*weight T
    rw [Fintype.card_sum,Fintype.card_bool]
    exact chain_edge_card T
  rw [hv,he] at h
  omega

/-- Arbitrary endpoint path counts are bounded by the tile weight. -/
theorem numPaths_le_weight (T : Fin (k+1) → Kind) (s t : Vertex T) :
    (network T).numPaths s t≤2^weight T := by
  have h := (network T).numPaths_le_two_pow s t
  rw [rank] at h
  exact h

end Erdos1016.ExactMaximumSupport.MixedCappedPrefix
