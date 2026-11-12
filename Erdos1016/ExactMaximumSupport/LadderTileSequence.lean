import Erdos1016.ExactMaximumSupport.LadderTileCoordinates
import Erdos1016.ExactMaximumSupport.PermutationLadder

set_option autoImplicit false
set_option maxHeartbeats 1500000

/-!
# The nonempty canonical tile sequence

Reindex the sorted canonical blocks to the concrete mixed-tile model.
The vertex equivalence retains the actual rail coordinates and both caps.
-/
noncomputable section
namespace Erdos1016.ExactMaximumSupport.LadderTileSequence
open LadderPermutation LadderTileOrder MixedTiles
variable {n k : ℕ} (π : Equiv.Perm (Fin n)) (hc : (tileStarts π).card=k+1)

/-- The concrete tile index identifies the same sorted canonical block. -/
def index : Fin (k+1) ≃ Fin (tileStarts π).card := finCongr hc.symm

def tiles (i : Fin (k+1)) : Kind := kind π (index π hc i)

def anchor (i : Fin (k+1)) : Fin n := start π (index π hc i)

/-- The reindexed block is still a canonical start. -/
theorem anchor_mem (i : Fin (k+1)) : anchor π hc i ∈ tileStarts π := start_mem π _

/-- The concrete tile's weight is the exact block weight. -/
theorem tiles_weight (i : Fin (k+1)) :
    (tiles π hc i).weight=tileWeight π (anchor π hc i) := kind_weight π _

/-- The sequence uses exactly all original inner rail positions. -/
theorem total_weight (hπ : AvoidsLadderPatterns π) : weight (tiles π hc)=n := by
  unfold weight tiles
  simp_rw [kind_weight]
  exact (Equiv.sum_comp (index π hc) (fun j => tileWeight π (start π j))).trans
    (ordered_total_weight hπ)

/-- Both original caps are retained by the concrete vertex equivalence. -/
def vertices (hπ : AvoidsLadderPatterns π) :
    CappedVertex (tiles π hc) ≃ PermutationLadder.Vertex n :=
  Equiv.sumCongr
    ((Equiv.sigmaCongrLeft (β := fun i => (kind π i).Vertex) (index π hc)).trans
      (LadderTileCoordinates.vertexEquiv hπ)) (Equiv.refl Bool)

@[simp] theorem vertices_inner (hπ : AvoidsLadderPatterns π)
    (i : Fin (k+1)) (x : (tiles π hc i).Vertex) :
    vertices π hc hπ (Sum.inl ⟨i,x⟩)=
      Sum.inl (LadderTileCoordinates.coordinate π (index π hc i) x) := rfl

@[simp] theorem vertices_cap (hπ : AvoidsLadderPatterns π) (b : Bool) :
    vertices π hc hπ (Sum.inr b)=Sum.inr b := rfl

/-- The first concrete tile starts at rail position zero. -/
theorem anchor_first (hπ : AvoidsLadderPatterns π) : (anchor π hc 0).val=0 :=
  first_start hπ _ rfl

/-- Concrete interfaces abut exactly at consecutive canonical blocks. -/
theorem anchor_succ (hπ : AvoidsLadderPatterns π) (i : Fin k) :
    (anchor π hc i.succ).val=(anchor π hc i.castSucc).val+(tiles π hc i.castSucc).weight := by
  rw [tiles_weight]
  exact consecutive_starts hπ _ _ rfl

/-- The last concrete tile ends at the final original rail position. -/
theorem anchor_last (hπ : AvoidsLadderPatterns π) :
    (anchor π hc (Fin.last k)).val+(tiles π hc (Fin.last k)).weight=n := by
  rw [tiles_weight]
  apply last_endpoint hπ
  change k+1=(tileStarts π).card
  exact hc.symm

/-- The fixed matching label is the unique position of a rung. -/
theorem rung_fixed (i : Fin (k+1)) (hi : tiles π hc i=.rung) :
    π (anchor π hc i)=anchor π hc i :=
  LadderTileCoordinates.rung_fixed π (index π hc i) hi

/-- A square's second position immediately follows its canonical start. -/
theorem square_next (hπ : AvoidsLadderPatterns π) (i : Fin (k+1))
    (hi : tiles π hc i=.square) :
    (π (anchor π hc i)).val=(anchor π hc i).val+1 := by
  have hne := LadderTileCoordinates.square_moved π (index π hc i) hi
  have hle : anchor π hc i ≤ π (anchor π hc i) := (Finset.mem_filter.mp (anchor_mem π hc i)).2
  have hdist := (displacement_le_one hπ (anchor π hc i)).1
  have hval : (π (anchor π hc i)).val ≠ (anchor π hc i).val := fun h => hne (Fin.ext h)
  change (anchor π hc i).val ≤ (π (anchor π hc i)).val at hle
  omega

/-- Each concrete left port has the canonical start coordinate. -/
theorem vertices_left (hπ : AvoidsLadderPatterns π) (i : Fin (k+1)) (b : Bool) :
    vertices π hc hπ (Sum.inl (MixedTiles.left (tiles π hc) i b))=
      Sum.inl (anchor π hc i,b) := by
  rw [show MixedTiles.left (tiles π hc) i b=⟨i,(tiles π hc i).left b⟩ from rfl,vertices_inner]
  unfold LadderTileCoordinates.coordinate tiles
  generalize ht : kind π (index π hc i)=t
  cases t <;> rfl

/-- Each concrete right port has the final position of its canonical block. -/
theorem vertices_right (hπ : AvoidsLadderPatterns π) (i : Fin (k+1)) (b : Bool) :
    vertices π hc hπ (Sum.inl (MixedTiles.right (tiles π hc) i b))=
      Sum.inl (π (anchor π hc i),b) := by
  rw [show MixedTiles.right (tiles π hc) i b=⟨i,(tiles π hc i).right b⟩ from rfl,vertices_inner]
  have hfix := rung_fixed π hc i
  unfold LadderTileCoordinates.coordinate tiles
  generalize ht : kind π (index π hc i)=t
  cases t with
  | rung =>
    have hh := hfix ht
    change Sum.inl (anchor π hc i,b)=Sum.inl (π (anchor π hc i),b)
    rw [hh]
  | square => rfl

end Erdos1016.ExactMaximumSupport.LadderTileSequence
