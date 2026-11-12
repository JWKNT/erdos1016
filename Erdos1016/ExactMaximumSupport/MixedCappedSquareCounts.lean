import Erdos1016.ExactMaximumSupport.MixedCappedSquareGeometry
import Erdos1016.ExactMaximumSupport.MixedCappedLocalCount
import Erdos1016.ExactMaximumSupport.ThirdPortArithmetic

set_option autoImplicit false
set_option maxHeartbeats 1500000

/-! # The actual marked square count in a capped ladder -/
noncomputable section
namespace Erdos1016.ExactMaximumSupport.MixedCappedSquareCounts
open BoundaryTrace BoundaryTrace.Network BoundaryDecay MixedTiles
open MixedCappedTileCut MixedCappedStem MixedCappedSquareGeometry
local instance (priority := 100) propDecidable (p : Prop) : Decidable p :=
  Classical.propDecidable p
variable {k : ℕ}

private theorem route_instances {A B : Type*} (N : Network A B)
    (i j : Fintype B) (a b : A) (d e : Decidable (a=b)) :
    @ite ℕ (a=b) d 1 (@Network.numPaths A B i N a b)=
      @ite ℕ (a=b) e 1 (@Network.numPaths A B j N a b) := by
  rw [Subsingleton.elim i j,Subsingleton.elim d e]

/-- Marking a square label gives its four literal prefix routes times the full suffix. -/
theorem count_eq (T : Fin (k+1) → Kind) (p : Fin (k+1)) (h : T p=Kind.square)
    (b c : Bool) :
    MarkedPathCount.count (capped T) (squareLabel T p h b c) (Sum.inr true)=
      (4+3*((capped T).sub (stem T p)).numPaths (L T p b) (L T p (!b)))*
        2^remainingWeight T p := by
  have hrc : R T p c≠R T p (!c) := by
    intro hh
    have hh' := R_inj T p hh
    cases c <;> contradiction
  have hh := MixedCappedLocalCount.count_eq T p (squareLabel T p h b c)
    (label_joins T p h b c) (after_left T p b) (after_right T p c) c
  have hf : MarkedPathCount.count (capped T) (squareLabel T p h b c) (Sum.inr true)=
    ((if L T p b=R T p c then 1 else (D T p h b c).numPaths (L T p b) (R T p c))+
      (if L T p b=R T p (!c) then 1 else (D T p h b c).numPaths (L T p b) (R T p (!c)))+
      (if R T p c=R T p c then 1 else (D T p h b c).numPaths (R T p c) (R T p c))+
      (if R T p c=R T p (!c) then 1 else (D T p h b c).numPaths (R T p c) (R T p (!c))))*
        2^remainingWeight T p := by
    calc
      _ = _ := hh
      _ = _ := by
        apply congrArg (fun n : ℕ => n*2^remainingWeight T p)
        apply congrArg₂ (fun x y : ℕ => x+y)
        · apply congrArg₂ (fun x y : ℕ => x+y)
          · apply congrArg₂ (fun x y : ℕ => x+y)
            · exact route_instances _ _ _ _ _ _ _
            · exact route_instances _ _ _ _ _ _ _
          · exact route_instances _ _ _ _ _ _ _
        · exact route_instances _ _ _ _ _ _ _
  rw [if_neg (L_ne_R T p h b c),if_neg (L_ne_R T p h b (!c)),if_pos rfl,if_neg hrc,
    local_route_sum] at hf
  exact hf

/-- Every actual square-label mark loses at least one eighth, including the first and last tile. -/
theorem square_eighth (T : Fin (k+1) → Kind) (p : Fin (k+1)) (h : T p=Kind.square)
    (b c : Bool) :
    8*MarkedPathCount.count (capped T) (squareLabel T p h b c) (Sum.inr true)≤
      7*2^(weight T+1) := by
  rw [count_eq]
  have hA := MixedCappedStem.numPaths_le T p (L T p b) (L T p (!b))
  have hs := ThirdPortArithmetic.square_eighth (precedingWeight T p) (remainingWeight T p)
    (((capped T).sub (stem T p)).numPaths (L T p b) (L T p (!b))) hA
  have hw := weight_split T p
  rw [h] at hw
  simp only [Kind.weight] at hw
  have he : precedingWeight T p+remainingWeight T p+3=weight T+1 := by omega
  rw [he] at hs
  exact hs

end Erdos1016.ExactMaximumSupport.MixedCappedSquareCounts
