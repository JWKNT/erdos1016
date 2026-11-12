import Erdos1016.ExactMaximumSupport.MixedTiles
import Erdos1016.ExactMaximum.NetCutRank

set_option autoImplicit false

/-!
# Connectedness and rank of the physical mixed-tile models

Every local tile is connected. The labelled interfaces connect consecutive tiles.
The Euler rank calculation uses the exact physical vertex and edge counts.
-/

noncomputable section
namespace Erdos1016.ExactMaximumSupport.MixedTiles
open BoundaryTrace BoundaryTrace.Network BoundaryDecay

/-- Every local tile is connected. -/
theorem Kind.connected (t : Kind) : t.network.graph.Connected := by
  apply (SimpleGraph.connected_iff_exists_forall_reachable _).mpr
  cases t with
  | rung =>
      refine ⟨false,?_⟩
      intro b
      cases b
      · exact SimpleGraph.Reachable.refl _
      · exact (show Kind.rung.network.graph.Adj false true from
          ⟨(),Or.inl ⟨rfl,rfl⟩⟩).reachable
  | square =>
      refine ⟨(false,false),?_⟩
      rintro ⟨side,b⟩
      have hr (c : Bool) : Kind.square.network.graph.Reachable (false,false) (true,c) :=
        (show Kind.square.network.graph.Adj (false,false) (true,c) from
          ⟨(false,c),Or.inl ⟨rfl,rfl⟩⟩).reachable
      cases side
      · cases b
        · exact SimpleGraph.Reachable.refl _
        · exact (hr false).trans
            (show Kind.square.network.graph.Adj (true,false) (false,true) from
              ⟨(true,false),Or.inr ⟨rfl,rfl⟩⟩).reachable
      · exact hr b

variable {k : ℕ}

/-- Embed an actual local tile graph in its chain. -/
def tileHom (T : Fin (k+1) → Kind) (i : Fin (k+1)) :
    (T i).network.graph →g (chain T).graph where
  toFun v := ⟨i,v⟩
  map_rel' := by
    intro u v h
    obtain ⟨e,he⟩ := h
    refine ⟨inner T i e,?_⟩
    rcases he with ⟨hs,ht⟩ | ⟨hs,ht⟩
    · exact Or.inl ⟨congrArg (fun x => (⟨i,x⟩ : Vertex T)) hs,
        congrArg (fun x => (⟨i,x⟩ : Vertex T)) ht⟩
    · exact Or.inr ⟨congrArg (fun x => (⟨i,x⟩ : Vertex T)) hs,
        congrArg (fun x => (⟨i,x⟩ : Vertex T)) ht⟩

/-- Every vertex is joined to the first left port by actual physical labels. -/
theorem chain_reachable (T : Fin (k+1) → Kind) (i : Fin (k+1)) :
    ∀ v : (T i).Vertex, (chain T).graph.Reachable (left T 0 false) ⟨i,v⟩ := by
  induction i using Fin.induction with
  | zero =>
      intro v
      exact ((T 0).connected ((T 0).left false) v).map (tileHom T 0)
  | succ i ih =>
      intro v
      have hp := ih ((T i.castSucc).right false)
      have hlink : (chain T).graph.Adj (right T i.castSucc false) (left T i.succ false) :=
        ⟨link T i false,joins_link T i false⟩
      exact (hp.trans hlink.reachable).trans
        (((T i.succ).connected ((T i.succ).left false) v).map (tileHom T i.succ))

/-- The physical chain is connected. -/
theorem chain_connected (T : Fin (k+1) → Kind) : (chain T).graph.Connected := by
  apply (SimpleGraph.connected_iff_exists_forall_reachable _).mpr
  exact ⟨left T 0 false,fun ⟨i,v⟩ => chain_reachable T i v⟩

/-- Embed the chain graph in its capped ladder. -/
def cappedHom (T : Fin (k+1) → Kind) : (chain T).graph →g (capped T).graph where
  toFun := Sum.inl
  map_rel' := by
    intro u v h
    obtain ⟨e,he⟩ := h
    refine ⟨Sum.inl e,?_⟩
    rcases he with ⟨hs,ht⟩ | ⟨hs,ht⟩
    · exact Or.inl ⟨congrArg Sum.inl hs,congrArg Sum.inl ht⟩
    · exact Or.inr ⟨congrArg Sum.inl hs,congrArg Sum.inl ht⟩

/-- The physical capped ladder is connected. -/
theorem capped_connected (T : Fin (k+1) → Kind) : (capped T).graph.Connected := by
  apply (SimpleGraph.connected_iff_exists_forall_reachable _).mpr
  refine ⟨Sum.inl (left T 0 false),?_⟩
  rintro (⟨i,v⟩ | b)
  · exact (chain_reachable T i v).map (cappedHom T)
  · cases b
    · exact (show (capped T).graph.Adj (Sum.inl (left T 0 false)) (Sum.inr false) from
        ⟨Sum.inr (Sum.inl false),Or.inr ⟨rfl,rfl⟩⟩).reachable
    · exact ((chain_reachable T (Fin.last k) ((T (Fin.last k)).right false)).map
        (cappedHom T)).trans
        (show (capped T).graph.Adj (Sum.inl (right T (Fin.last k) false)) (Sum.inr true) from
          ⟨Sum.inr (Sum.inr false),Or.inl ⟨rfl,rfl⟩⟩).reachable

/-- Closing the chain preserves connectedness, for either closing twist. -/
theorem ring_connected (T : Fin (k+1) → Kind) (hk : 1 ≤ k) (twist : Equiv.Perm Bool) :
    (ring T hk twist).graph.Connected := by
  refine (chain_connected T).mono ?_
  intro u v h
  obtain ⟨e,he⟩ := h
  exact ⟨Sum.inl e,he⟩

/-- A chain has rank one below its weight. -/
theorem chain_rank (T : Fin (k+1) → Kind) : networkRank (chain T)+1=weight T := by
  have h := network_rank_euler (chain T)
  rw [connected_component_card (chain T) (chain_connected T),vertex_card] at h
  have hc := chain_edge_card T
  omega

/-- A capped ladder has rank one above its weight. -/
theorem capped_rank (T : Fin (k+1) → Kind) : networkRank (capped T)=weight T+1 := by
  have h := network_rank_euler (capped T)
  rw [connected_component_card (capped T) (capped_connected T),capped_vertex_card,
    capped_edge_card] at h
  omega

/-- A ring has rank one above its weight, for either closing twist. -/
theorem ring_rank (T : Fin (k+1) → Kind) (hk : 1 ≤ k) (twist : Equiv.Perm Bool) :
    networkRank (ring T hk twist)=weight T+1 := by
  have h := network_rank_euler (ring T hk twist)
  rw [connected_component_card (ring T hk twist) (ring_connected T hk twist),vertex_card,
    ring_edge_card] at h
  omega

end Erdos1016.ExactMaximumSupport.MixedTiles
