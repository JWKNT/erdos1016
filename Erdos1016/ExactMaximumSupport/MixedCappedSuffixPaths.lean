import Erdos1016.ExactMaximumSupport.MixedCappedSuffixSquareCut

set_option autoImplicit false
set_option maxHeartbeats 2000000
noncomputable section
namespace Erdos1016.ExactMaximumSupport.MixedCappedSuffix
open BoundaryTrace BoundaryTrace.Network MixedTiles
variable {k : ℕ} (T : Fin (k+1) → Kind)

/-- A nonzero even tile word selects every local label. -/
theorem even_tile_eq_one (t : Kind) (z : t.network.Word)
    (hz : t.network.boundary z=0) (hne : z≠0) : z=fun _ => 1 := by
  have ht:=nonzero_even_tile_is_square t z hz hne
  subst t
  exact square_even_eq_one z hz hne

/-- Every terminal parity join in the one-cap suffix is an actual simple path word. -/
theorem join_isPath (b : Bool) (x : (network T).Word)
    (hx : (network T).boundary x=(network T).pathDemand (entry T b) (cap T)) :
    (network T).IsPathWord (entry T b) (cap T) x := by
  apply (network T).isPathWord_of_minimal (show entry T b≠cap T from Sum.inl_ne_inr) hx
  intro z hsub hz
  have hzero := subword_interfaces_zero T b hx hz hsub
  have htiles (i : Fin (k+1)) : tileWord T z i=0 := by
    by_contra hn
    have he:=tile_even T z hz hzero i
    have hi:=nonzero_even_tile_is_square (T i) (tileWord T z i) he hn
    have hall:=even_tile_eq_one (T i) (tileWord T z i) he hn
    apply not_all_square_labels T b x hx i hi
    intro e
    apply (bit_cases _).resolve_left
    apply hsub (Sum.inl (inner T i e))
    change tileWord T z i e≠0
    rw [hall]
    exact one_ne_zero
  funext e
  rcases e with (⟨i,e⟩ | ⟨i,b⟩) | b
  · exact congrFun (htiles i) e
  · simpa only [interface_cast,link] using hzero i.castSucc b
  · simpa only [interface_last] using hzero (Fin.last k) b

/-- Paths from either left port to the right cap fill the entire affine fiber. -/
theorem numPaths_entry_cap (b : Bool) :
    (network T).numPaths (entry T b) (cap T)=2^weight T := by
  obtain ⟨w⟩ := connected T (entry T b) (cap T)
  obtain ⟨x,hx⟩ := (network T).pair_mem_range_of_walk w
  have hf : Nat.card {x : (network T).Word //
      (network T).IsPathWord (entry T b) (cap T) x} =
      Nat.card (Parity.Fiber (network T).boundary ((network T).pathDemand (entry T b) (cap T))) := by
    apply Nat.card_congr
    exact Equiv.subtypeEquivRight fun z =>
      ⟨fun h => h.boundary_eq,fun h => join_isPath T b z h⟩
  change Nat.card {x : (network T).Word //
      (network T).IsPathWord (entry T b) (cap T) x}=2^weight T
  rw [hf,(network T).card_joins (entry T b) (cap T) ⟨x,hx⟩,rank]

/-- Any two prefix endpoints have at most one path per rank coordinate. -/
theorem numPaths_le_weight (s t : Vertex T) :
    (network T).numPaths s t≤2^weight T := by
  have h:=(network T).numPaths_le_two_pow s t
  rw [rank] at h
  exact h

end Erdos1016.ExactMaximumSupport.MixedCappedSuffix
