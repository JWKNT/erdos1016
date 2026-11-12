import Erdos1016.ExactMaximumSupport.MixedTilesRank
import Erdos1016.ExactMaximumSupport.MixedTileStates
import Erdos1016.ExactMaximum.NetBridgeCut

set_option autoImplicit false
set_option maxHeartbeats 2000000

/-!
# The physical suffix of a capped ladder

A nonempty tile sequence has one cap at its right end. The two left ports
remain distinct, and every physical interface has two original labels.
-/
noncomputable section
namespace Erdos1016.ExactMaximumSupport.MixedCappedSuffix
open BoundaryTrace BoundaryTrace.Network BoundaryDecay MixedTiles
local instance suffixDecidable (p : Prop) : Decidable p := Classical.propDecidable p
variable {k : ℕ}

abbrev Vertex (T : Fin (k+1) → Kind) := MixedTiles.Vertex T ⊕ Unit
abbrev Edge (T : Fin (k+1) → Kind) := ChainEdge T ⊕ Bool

def src (T : Fin (k+1) → Kind) : Edge T → Vertex T
  | Sum.inl e => Sum.inl ((chain T).src e)
  | Sum.inr b => Sum.inl (right T (Fin.last k) b)
def dst (T : Fin (k+1) → Kind) : Edge T → Vertex T
  | Sum.inl e => Sum.inl ((chain T).dst e)
  | Sum.inr _ => Sum.inr ()

def network (T : Fin (k+1) → Kind) : Network (Vertex T) (Edge T) where
  src := src T
  dst := dst T
  noLoops e := by
    rcases e with e | b
    · exact fun h => (chain T).noLoops e (Sum.inl.inj h)
    · exact Sum.inl_ne_inr

def cap (T : Fin (k+1) → Kind) : Vertex T := Sum.inr ()
def entry (T : Fin (k+1) → Kind) (b : Bool) : Vertex T := Sum.inl (left T 0 b)

def chainHom (T : Fin (k+1) → Kind) : (chain T).graph →g (network T).graph where
  toFun := Sum.inl
  map_rel' := by
    intro u v h
    obtain ⟨e,he⟩ := h
    refine ⟨Sum.inl e,?_⟩
    rcases he with ⟨hs,ht⟩ | ⟨hs,ht⟩
    · exact Or.inl ⟨congrArg Sum.inl hs,congrArg Sum.inl ht⟩
    · exact Or.inr ⟨congrArg Sum.inl hs,congrArg Sum.inl ht⟩

/-- Every suffix is connected, including the one-tile case. -/
theorem connected (T : Fin (k+1) → Kind) : (network T).graph.Connected := by
  apply (SimpleGraph.connected_iff_exists_forall_reachable _).mpr
  refine ⟨entry T false,?_⟩
  rintro (⟨i,v⟩ | ⟨⟩)
  · exact (chain_reachable T i v).map (chainHom T)
  · exact ((chain_reachable T (Fin.last k) ((T (Fin.last k)).right false)).map
      (chainHom T)).trans
      (show (network T).graph.Adj (Sum.inl (right T (Fin.last k) false)) (cap T) from
        ⟨Sum.inr false,Or.inl ⟨rfl,rfl⟩⟩).reachable

/-- Adding the one cap raises the chain rank to the tile weight. -/
theorem rank (T : Fin (k+1) → Kind) : networkRank (network T)=weight T := by
  have h:=network_rank_euler (network T)
  rw [connected_component_card (network T) (connected T)] at h
  have hv : Fintype.card (Vertex T)=2*weight T+1 := by
    simp only [Vertex,Fintype.card_sum,Fintype.card_unit,MixedTiles.vertex_card]
  have he : Fintype.card (Edge T)=3*weight T := by
    change Fintype.card (ChainEdge T ⊕ Bool)=3*weight T
    rw [Fintype.card_sum,Fintype.card_bool]
    exact chain_edge_card T
  rw [hv,he] at h
  omega

/-- The interface after a tile; the last one consists of the two cap labels. -/
def interface (T : Fin (k+1) → Kind) (i : Fin (k+1)) (b : Bool) : Edge T :=
  Fin.lastCases (Sum.inr b) (fun j => Sum.inl (link T j b)) i

@[simp] theorem interface_last (T : Fin (k+1) → Kind) (b : Bool) :
    interface T (Fin.last k) b=Sum.inr b := by simp [interface]
@[simp] theorem interface_cast (T : Fin (k+1) → Kind) (i : Fin k) (b : Bool) :
    interface T i.castSucc b=Sum.inl (link T i b) := by simp [interface]

theorem interface_ne (T : Fin (k+1) → Kind) (i : Fin (k+1)) :
    interface T i false≠interface T i true := by
  cases i using Fin.lastCases with
  | last => simp [interface]
  | cast j => simp [interface,link]

/-- The actual vertex prefixSet ending at a tile. -/
def prefixSet (T : Fin (k+1) → Kind) (j : Fin (k+1)) : Vertex T → Prop
  | Sum.inl v => v.1.val≤j.val
  | Sum.inr _ => False

/-- The physical cut of a prefixSet is precisely its next two labels. -/
theorem prefix_crosses (T : Fin (k+1) → Kind) (j : Fin (k+1)) (e : Edge T) :
    (network T).crosses (prefixSet T j) e ↔ e=interface T j false ∨ e=interface T j true := by
  cases j using Fin.lastCases with
  | last =>
      rcases e with (⟨i,e⟩ | ⟨i,b⟩) | b
      · simp [Network.crosses,network,src,dst,chain,chainSrc,chainDst,prefixSet,interface]
      · have hi:=i.isLt
        simp [Network.crosses,network,src,dst,chain,chainSrc,chainDst,prefixSet,
          right,left,interface,link,Fin.coe_castSucc,Fin.val_succ,Fin.val_last]
        omega
      · cases b <;> simp [Network.crosses,network,src,dst,prefixSet,right,interface]
  | cast j =>
      rcases e with (⟨i,e⟩ | ⟨i,b⟩) | b
      · simp [Network.crosses,network,src,dst,chain,chainSrc,chainDst,prefixSet,interface,link]
      · rw [interface_cast,interface_cast]
        change (¬(i.val≤j.val ↔ i.val+1≤j.val)) ↔
          (Sum.inl (Sum.inr (i,b)) : Edge T)=Sum.inl (Sum.inr (j,false)) ∨
            (Sum.inl (Sum.inr (i,b)) : Edge T)=Sum.inl (Sum.inr (j,true))
        cases b <;> simp only [Sum.inl.injEq,Sum.inr.injEq,Prod.mk.injEq,Bool.false_eq_true,
          Bool.true_eq_false,and_false,and_true,or_false,false_or,Fin.ext_iff] <;> omega
      · have hj:=j.isLt
        cases b <;> simp [Network.crosses,network,src,dst,prefixSet,right,interface,link]

/-- The prefixSet boundary sum is the parity of its two physical interface labels. -/
theorem prefix_parity (T : Fin (k+1) → Kind) (z : (network T).Word) (j : Fin (k+1)) :
    (∑ v,if prefixSet T j v then (network T).boundary z v else 0)=
      z (interface T j false)+z (interface T j true) := by
  classical
  rw [(network T).cut_parity]
  have hn:=interface_ne T j
  have hp (e : Edge T) :
      (if (network T).crosses (prefixSet T j) e then z e else 0)=
        (if e=interface T j false then z (interface T j false) else 0)+
        (if e=interface T j true then z (interface T j true) else 0) := by
    rw [prefix_crosses]
    by_cases h0 : e=interface T j false
    · subst e; simp [hn]
    by_cases h1 : e=interface T j true
    · subst e; simp [Ne.symm hn]
    simp [h0,h1]
  rw [Finset.sum_congr rfl (fun e _ => hp e),Finset.sum_add_distrib]
  simp

/-- Every terminal join selects an odd number of labels at every suffix interface. -/
theorem join_interface_odd (T : Fin (k+1) → Kind) (b : Bool)
    (z : (network T).Word) (hz : (network T).boundary z=(network T).pathDemand (entry T b) (cap T))
    (j : Fin (k+1)) : z (interface T j false)+z (interface T j true)=1 := by
  rw [←prefix_parity T z j,hz,(network T).sum_pathDemand]
  simp [prefixSet,entry,cap,left]

/-- Every even word has even parity at every suffix interface. -/
theorem even_interface_zero (T : Fin (k+1) → Kind)
    (z : (network T).Word) (hz : (network T).boundary z=0) (j : Fin (k+1)) :
    z (interface T j false)+z (interface T j true)=0 := by
  rw [←prefix_parity T z j,hz]
  simp

end Erdos1016.ExactMaximumSupport.MixedCappedSuffix
