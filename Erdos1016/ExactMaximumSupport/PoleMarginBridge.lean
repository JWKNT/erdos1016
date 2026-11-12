import Erdos1016.ExactMaximumSupport.ThirdPortBridges
import Erdos1016.ExactMaximumSupport.CyclicShoreMargin

set_option autoImplicit false
set_option maxHeartbeats 1500000

/-!
# A bridge split preserves the prescribed path-density margin

The two actual shores retain their physical labels and terminal ports.
Their ranks add and their path counts multiply.
-/
noncomputable section
namespace Erdos1016.ExactMaximumSupport.PoleMarginBridge
open BoundaryTrace BoundaryTrace.Network BoundaryDecay
local instance marginBridgeDecidable (p : Prop) : Decidable p := Classical.propDecidable p
variable {V E : Type*} [Fintype V] [Fintype E] (N : Network V E)

/-- The complete actual-network data for one bridge split. -/
structure Split (m : ℕ) (s t : V) (e : E) (S : V → Prop) (x y : V) : Prop where
  joins : N.Joins e x y
  mem_x : S x
  not_mem_y : ¬S y
  only_cross : ∀g,N.crosses S g → g=e
  mem_s : S s
  not_mem_t : ¬S t
  left_pole : (N.sub (N.inside S)).IsWeakTwoPole s x
  right_pole : (N.sub (N.outside S)).IsWeakTwoPole y t
  left_rank_pos : 0<networkRank (N.sub (N.inside S))
  right_rank_pos : 0<networkRank (N.sub (N.outside S))
  rank_eq : networkRank N=networkRank (N.sub (N.inside S))+networkRank (N.sub (N.outside S))
  paths_eq : N.numPaths s t=(N.sub (N.inside S)).numPaths s x*(N.sub (N.outside S)).numPaths y t
  left_rich : (2^m+2)*2^networkRank (N.sub (N.inside S))≤
    2^(m+1)*(N.sub (N.inside S)).numPaths s x
  right_rich : (2^m+2)*2^networkRank (N.sub (N.outside S))≤
    2^(m+1)*(N.sub (N.outside S)).numPaths y t

/-- Every physical bridge admits the exact split at the original rational margin. -/
theorem exists_split (m : ℕ) {s t : V} (hN : N.IsWeakTwoPole s t)
    (hrich : (2^m+2)*2^networkRank N≤2^(m+1)*N.numPaths s t)
    {e : E} (hbr : ∀z,N.IsCycleWord z → z e=0) :
    ∃ (S : V → Prop) (x y : V),Split N m s t e S x y := by
  have hmany := CyclicShoreMargin.strict_half m _ _ hrich
  obtain ⟨S,x,y,he,hx,hy,hC,hSs,hSt,hxs,hyt,hin,hout⟩ :=
    ThirdPortBridges.bridge_cut N hN.pole hN.port_s hN.port_t hmany hbr
  have hC' : ∀g,N.crosses (fun v => ¬S v) g → g=e :=
    fun g hg => hC g ((N.crosses_not_iff S g).mp hg)
  have hleft := N.isWeakTwoPole_side hN S he hx hy hC hSs hSt hxs hin
  have hright' := N.isWeakTwoPole_side hN.symm (fun v => ¬S v) he.symm hy
    (not_not.mpr hx) hC' hSt (not_not.mpr hSs) hyt hout
  have hright : (N.sub (N.outside S)).IsWeakTwoPole y t := hright'.symm
  have hce := N.crosses_of_joins he hx hy
  have hr := N.networkRank_of_one_crossing S hC hce
  have hp := N.numPaths_of_one_crossing S he hx hy hC hSs hSt hleft.ne hright.ne
  have hleftpos := N.rank_side_pos_of_one_crossing hN.pole.deg_zero_or_two_le S he hx hy hC
  have hrightpos := N.rank_side_pos_of_one_crossing hN.pole.deg_zero_or_two_le
    (fun v => ¬S v) he.symm hy (not_not.mpr hx) hC'
  refine ⟨S,x,y,he,hx,hy,hC,hSs,hSt,hleft,hright,hleftpos,hrightpos,hr,hp,?_,?_⟩
  · apply CyclicShoreMargin.left_factor m _ _ _ _ ((N.sub (N.outside S)).numPaths_le_two_pow y t)
    rwa [←hr,←hp]
  · apply CyclicShoreMargin.right_factor m _ _ _ _ ((N.sub (N.inside S)).numPaths_le_two_pow s x)
    rwa [←hr,←hp]

end Erdos1016.ExactMaximumSupport.PoleMarginBridge
