import Erdos1016.ExactMaximumSupport.MixedCappedRungCounts
import Erdos1016.ExactMaximumSupport.MixedCappedSquareCounts
import Erdos1016.ExactMaximumSupport.MixedCappedInterfaceCounts
import Erdos1016.ExactMaximumSupport.MixedCappedRightCap
import Erdos1016.ExactMaximumSupport.ThirdPortCappedReduction

set_option autoImplicit false

/-! # Every marked physical label in a capped mixed ladder

The physical edge sum type is exhausted: local rungs, local square labels,
internal interfaces, left-cap labels and right-cap labels.
-/
noncomputable section
namespace Erdos1016.ExactMaximumSupport.MixedCappedMarkedCounts
open BoundaryTrace BoundaryTrace.Network BoundaryDecay MixedTiles

/-- The concrete marked-count input, with every physical label case discharged. -/
theorem cappedMarkedCountStatement : ThirdPortCappedReduction.CappedMarkedCountStatement := by
  intro k T e
  rcases e with (⟨p,e⟩ | ⟨i,b⟩) | (b | b)
  · by_cases h : T p=Kind.rung
    · exact MixedCappedRungCounts.rung_gap T p h e
    · have hs : T p=Kind.square := by cases hp : T p <;> simp_all
      obtain ⟨b,c,he⟩ := MixedCappedSquareGeometry.squareLabel_surjective T p hs e
      right
      change 8*MarkedPathCount.count (capped T) (Sum.inl (MixedTiles.inner T p e)) (Sum.inr true)≤_
      rw [he]
      exact MixedCappedSquareCounts.square_eighth T p hs b c
  · right
    have h := MixedCappedInterfaceCounts.interface_quarter T i b
    change 8*MarkedPathCount.count (capped T) (Sum.inl (link T i b)) (Sum.inr true)≤_
    omega
  · exact Or.inl (MixedCappedCapCounts.left_cap_count T b)
  · right
    have h := MixedCappedRightCap.right_cap_quarter T b
    omega

end Erdos1016.ExactMaximumSupport.MixedCappedMarkedCounts
