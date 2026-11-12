import Erdos1016.ExactMaximumSupport.LadderTileSequence

set_option autoImplicit false
set_option maxHeartbeats 2000000

/-!
# Original physical labels of the canonical tiles

Square rail edges stay rail labels. Rungs and square cross edges stay matching
labels. Interfaces and cap edges occupy their exact original rail positions.
-/
noncomputable section
namespace Erdos1016.ExactMaximumSupport.LadderTileEdges
open BoundaryTrace BoundaryTrace.Network LadderPermutation MixedTiles LadderTileSequence
variable {n k : ℕ} (π : Equiv.Perm (Fin n)) (hc : (tileStarts π).card=k+1)

/-- A local tile label mapped to its original rail or matching label. -/
def innerMap (a b : Fin n) : (t : Kind) → t.Edge → PermutationLadder.Edge n
  | .rung,_ => Sum.inr a
  | .square,(r,s) => if r=s then Sum.inl (b.castSucc,r) else
      if r then Sum.inr b else Sum.inr a

/-- Every concrete capped label retains its original physical identity. -/
def edgeMap : CappedEdge (tiles π hc) → PermutationLadder.Edge n
  | Sum.inl (Sum.inl ⟨i,e⟩) => innerMap (anchor π hc i) (π (anchor π hc i)) (tiles π hc i) e
  | Sum.inl (Sum.inr (i,b)) => Sum.inl ((anchor π hc i.succ).castSucc,b)
  | Sum.inr (Sum.inl b) => Sum.inl (0,b)
  | Sum.inr (Sum.inr b) => Sum.inl (Fin.last n,b)

/-- The physical rail edge between consecutive inner coordinates. -/
theorem joins_adjacent (a b : Fin n) (hab : b.val=a.val+1) (r : Bool) :
    (PermutationLadder.network π).Joins (Sum.inl (b.castSucc,r))
      (Sum.inl (a,r)) (Sum.inl (b,r)) := by
  have hleft : b.castSucc.castSucc=a.succ.castSucc := Fin.ext hab
  have hright : b.castSucc.succ=b.succ.castSucc := rfl
  have hh := PermutationLadder.joins_rail π b.castSucc r
  rw [hleft,hright,PermutationLadder.railVertex_inner,PermutationLadder.railVertex_inner] at hh
  exact hh

/-- The matched coordinate is the rightmost coordinate of each tile. -/
theorem matched_endpoint (hπ : AvoidsLadderPatterns π) (i : Fin (k+1)) :
    (π (anchor π hc i)).val+1=(anchor π hc i).val+(tiles π hc i).weight := by
  cases ht : tiles π hc i with
  | rung => rw [rung_fixed π hc i ht]; rfl
  | square => rw [square_next π hc hπ i ht]; rfl

/-- All local labels join the exact physical coordinates of their tile vertices. -/
theorem inner_joins (hπ : AvoidsLadderPatterns π) (i : Fin (k+1)) (e : (tiles π hc i).Edge) :
    (PermutationLadder.network π).Joins
      (innerMap (anchor π hc i) (π (anchor π hc i)) (tiles π hc i) e)
      (vertices π hc hπ (Sum.inl ⟨i,(tiles π hc i).src e⟩))
      (vertices π hc hπ (Sum.inl ⟨i,(tiles π hc i).dst e⟩)) := by
  rw [vertices_inner,vertices_inner]
  have hfix := rung_fixed π hc i
  have hnext := square_next π hc hπ i
  change (PermutationLadder.network π).Joins
    (innerMap (anchor π hc i) (π (anchor π hc i)) (tiles π hc i) e)
    (Sum.inl (LadderTileCoordinates.localMap (anchor π hc i) (π (anchor π hc i))
      (tiles π hc i) ((tiles π hc i).src e)))
    (Sum.inl (LadderTileCoordinates.localMap (anchor π hc i) (π (anchor π hc i))
      (tiles π hc i) ((tiles π hc i).dst e)))
  generalize ht : tiles π hc i=t at e ⊢
  cases t with
  | rung =>
    cases e
    simpa [innerMap,LadderTileCoordinates.localMap,Kind.src,Kind.dst,hfix ht] using
      PermutationLadder.joins_matching π (anchor π hc i)
  | square =>
    rcases e with ⟨r,s⟩
    cases r <;> cases s
    · simpa [innerMap,LadderTileCoordinates.localMap,Kind.src,Kind.dst] using
        joins_adjacent π (anchor π hc i) (π (anchor π hc i)) (hnext ht) false
    · exact PermutationLadder.joins_matching π (anchor π hc i)
    · simpa [innerMap,LadderTileCoordinates.localMap,Kind.src,Kind.dst,
        involutive hπ (anchor π hc i)] using
        (PermutationLadder.joins_matching π (π (anchor π hc i))).symm
    · simpa [innerMap,LadderTileCoordinates.localMap,Kind.src,Kind.dst] using
        joins_adjacent π (anchor π hc i) (π (anchor π hc i)) (hnext ht) true

/-- Interface labels join the abutting right and left port pairs. -/
theorem interface_joins (hπ : AvoidsLadderPatterns π) (i : Fin k) (b : Bool) :
    (PermutationLadder.network π).Joins (Sum.inl ((anchor π hc i.succ).castSucc,b))
      (vertices π hc hπ (Sum.inl (MixedTiles.right (tiles π hc) i.castSucc b)))
      (vertices π hc hπ (Sum.inl (MixedTiles.left (tiles π hc) i.succ b))) := by
  rw [vertices_right,vertices_left]
  apply joins_adjacent
  have hh := matched_endpoint π hc hπ i.castSucc
  have hs := anchor_succ π hc hπ i
  omega

/-- The two left cap labels have their original first rail positions. -/
theorem left_cap_joins (hπ : AvoidsLadderPatterns π) (b : Bool) :
    (PermutationLadder.network π).Joins (Sum.inl (0,b))
      (vertices π hc hπ (Sum.inr false))
      (vertices π hc hπ (Sum.inl (MixedTiles.left (tiles π hc) 0 b))) := by
  rw [vertices_cap,vertices_left]
  have hh := PermutationLadder.joins_rail π 0 b
  have he : (0 : Fin (n+1)).succ=(anchor π hc 0).succ.castSucc := by
    apply Fin.ext
    have hzero := anchor_first π hc hπ
    change 1=(anchor π hc 0).val+1
    omega
  rw [he,PermutationLadder.railVertex_inner] at hh
  exact hh

/-- The two right cap labels have their original last rail positions. -/
theorem right_cap_joins (hπ : AvoidsLadderPatterns π) (b : Bool) :
    (PermutationLadder.network π).Joins (Sum.inl (Fin.last n,b))
      (vertices π hc hπ (Sum.inl (MixedTiles.right (tiles π hc) (Fin.last k) b)))
      (vertices π hc hπ (Sum.inr true)) := by
  rw [vertices_right,vertices_cap]
  have hh := PermutationLadder.joins_rail π (Fin.last n) b
  have he : (Fin.last n).castSucc=(π (anchor π hc (Fin.last k))).succ.castSucc := by
    apply Fin.ext
    have hlast := anchor_last π hc hπ
    have hm := matched_endpoint π hc hπ (Fin.last k)
    change n=(π (anchor π hc (Fin.last k))).val+1
    omega
  rw [he,PermutationLadder.railVertex_inner] at hh
  have hlast : (Fin.last n).succ=Fin.last (n+1) := rfl
  rw [hlast,PermutationLadder.railVertex_last] at hh
  exact hh

/-- The entire physical edge map preserves unordered endpoints. -/
theorem edgeMap_joins (hπ : AvoidsLadderPatterns π) (e : CappedEdge (tiles π hc)) :
    (PermutationLadder.network π).Joins (edgeMap π hc e)
      (vertices π hc hπ ((capped (tiles π hc)).src e))
      (vertices π hc hπ ((capped (tiles π hc)).dst e)) := by
  rcases e with (⟨i,e⟩ | ⟨i,b⟩) | (b | b)
  · exact inner_joins π hc hπ i e
  · exact interface_joins π hc hπ i b
  · exact left_cap_joins π hc hπ b
  · exact right_cap_joins π hc hπ b

end Erdos1016.ExactMaximumSupport.LadderTileEdges
