import Erdos1016.ExactMaximumSupport.MixedChainGlueEdges
import Erdos1016.ExactMaximumSupport.MixedRingUpper

set_option autoImplicit false

/-!
# Two physical chains form the canonical mixed ring

The concatenation retains every old vertex and physical label.
The central interface has no twist. The closing interface retains its given twist.
-/

noncomputable section
namespace Erdos1016.ExactMaximumSupport.MixedTiles
open BoundaryTrace BoundaryTrace.Network BoundaryDecay

variable {k l : ℕ} (T : Fin (k+1) → Kind) (U : Fin (l+1) → Kind)

/-- The glued model is physically isomorphic to the ring on the appended tile list. -/
def gluedRingIso (twist : Equiv.Perm Bool) :
    NetworkIso (glued T U twist) (ring (append T U) (by omega) twist) where
  vertices := appendVertices T U
  edges := gluedEdges T U
  joins e := by
    rcases e with ((e | ⟨i,b⟩) | (e | ⟨i,b⟩)) | (b | b)
    · exact Or.inl ⟨appendInnerEdges_src_left T U e,appendInnerEdges_dst_left T U e⟩
    · left
      constructor
      · change right (append T U) _ b=appendVertices T U (Sum.inl (right T i.castSucc b))
        rw [appendVertices_right_port]
        congr 1
      · change left (append T U) _ b=appendVertices T U (Sum.inl (left T i.succ b))
        rw [appendVertices_left_port]
        congr 1
    · exact Or.inl ⟨appendInnerEdges_src_right T U e,appendInnerEdges_dst_right T U e⟩
    · left
      constructor
      · change right (append T U) _ b=appendVertices T U (Sum.inr (right U i.castSucc b))
        rw [appendVertices_right_port']
        congr 1
      · change left (append T U) _ b=appendVertices T U (Sum.inr (left U i.succ b))
        rw [appendVertices_left_port']
        congr 1
    · left
      constructor
      · change right (append T U) _ b=appendVertices T U (Sum.inr (right U (Fin.last l) b))
        rw [appendVertices_right_port']
        congr 1
      · change left (append T U) _ (twist b)=appendVertices T U (Sum.inl (left T 0 (twist b)))
        rw [appendVertices_left_port]
        congr 1
    · left
      constructor
      · change right (append T U) _ b=appendVertices T U (Sum.inl (right T (Fin.last k) b))
        rw [appendVertices_right_port]
        congr 1
      · change left (append T U) _ b=appendVertices T U (Sum.inr (left U 0 b))
        rw [appendVertices_left_port']
        congr 1

/-- The actual rank of the glued network is the sum of the two weights plus one. -/
theorem glued_rank (twist : Equiv.Perm Bool) :
    networkRank (glued T U twist)=weight T+weight U+1 := by
  rw [← (gluedRingIso T U twist).networkRank_eq,ring_rank,append_weight]

/-- Every glued physical model of rank at least eight satisfies the Horak--Kim upper bound. -/
theorem glued_numCycles_le_horakKim_rank (twist : Equiv.Perm Bool)
    (hr : 8≤networkRank (glued T U twist)) :
    (glued T U twist).numCycles≤ExactMaximum.horakKim (networkRank (glued T U twist)) := by
  have hr' : 8≤networkRank (ring (append T U) (by omega) twist) := by
    rwa [(gluedRingIso T U twist).networkRank_eq]
  have hw : 7≤weight (append T U) := by rw [ring_rank] at hr'; omega
  have h := ring_numCycles_le_horakKim_rank (append T U) (by omega) twist hw
  rwa [(gluedRingIso T U twist).numCycles_eq,(gluedRingIso T U twist).networkRank_eq] at h

end Erdos1016.ExactMaximumSupport.MixedTiles
