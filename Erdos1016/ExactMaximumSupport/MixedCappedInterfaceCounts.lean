import Erdos1016.ExactMaximumSupport.MixedCappedPrefixEmbed
import Erdos1016.ExactMaximumSupport.NetworkCutDeletedPaths
import Erdos1016.ExactMaximumSupport.ThirdPortArithmetic

set_option autoImplicit false
set_option maxHeartbeats 1500000

/-! # Actual marked interface labels in capped ladders -/
noncomputable section
namespace Erdos1016.ExactMaximumSupport.MixedCappedInterfaceCounts
open BoundaryTrace BoundaryTrace.Network BoundaryDecay MixedTiles MixedCappedTailEmbed
open scoped BigOperators
local instance (priority := 100) propDecidable (p : Prop) : Decidable p :=
  Classical.propDecidable p
variable {k : ℕ}

/-- Exactly the two labels of the chosen interface cross its literal prefix cut. -/
theorem crossing_labels (T : Fin (k+1) → Kind) (i : Fin k) (b : Bool)
    (e : CappedEdge T) (he : (capped T).crosses (before T i.succ) e) :
    e=Sum.inl (link T i b) ∨ e=Sum.inl (link T i (!b)) := by
  rcases e with (⟨j,e⟩ | ⟨j,c⟩) | (c | c)
  · simp [Network.crosses,before,capped,cappedSrc,cappedDst,chain,chainSrc,chainDst] at he
  · have hji : j=i := by
      apply Fin.ext
      simp only [Network.crosses,before,capped,cappedSrc,cappedDst,chain,chainSrc,
        chainDst,right,left,Fin.coe_castSucc,Fin.val_succ] at he
      omega
    subst j
    cases b <;> cases c <;> simp [link]
  · have hi := i.isLt
    simp [Network.crosses,before,capped,cappedSrc,cappedDst,left] at he
  · have hi := i.isLt
    simp [Network.crosses,before,capped,cappedSrc,cappedDst,right] at he
    omega

/-- Marking an internal interface always loses at least one quarter. -/
theorem interface_quarter (T : Fin (k+1) → Kind) (i : Fin k) (b : Bool) :
    4*MarkedPathCount.count (capped T) (Sum.inl (link T i b)) (Sum.inr true)≤
      3*2^(weight T+1) := by
  let S := before T i.succ
  let p := ∑ j ∈ Finset.univ.filter (fun j : Fin (k+1) => j.val < i.succ.val), (T j).weight
  let q := weight (tail T i.succ)
  let A := if (Sum.inl (right T i.castSucc b) : CappedVertex T)=
      Sum.inl (right T i.castSucc (!b)) then 1 else
      ((capped T).sub ((capped T).inside S)).numPaths
        (Sum.inl (right T i.castSucc b)) (Sum.inl (right T i.castSucc (!b)))
  have hne : (Sum.inl (link T i b) : CappedEdge T)≠Sum.inl (link T i (!b)) := by
    cases b <;> simp [link]
  have he : (capped T).Joins (Sum.inl (link T i b))
      (Sum.inl (right T i.castSucc b)) (Sum.inl (left T i.succ b)) := Or.inl ⟨rfl,rfl⟩
  have hf : (capped T).Joins (Sum.inl (link T i (!b)))
      (Sum.inl (right T i.castSucc (!b))) (Sum.inl (left T i.succ (!b))) := Or.inl ⟨rfl,rfl⟩
  have hcount := NetworkCutDeletedPaths.marked_count_interface (capped T) S
    (t:=Sum.inr true) hne he (by simp [S,before,right]) (by simp [S,before,left])
    hf (by simp [S,before,right]) (by simp [S,before,left])
    (crossing_labels T i b) (by simp [S,before])
  have hformula : MarkedPathCount.count (capped T) (Sum.inl (link T i b)) (Sum.inr true)=
      (1+A)*2^q := by
    simpa [A,q,S,exterior_entry_count,Nat.add_mul,Nat.one_mul,Nat.add_comm] using hcount
  have hA : A≤2^p := MixedCappedPrefixEmbed.inside_route_le T i.succ _ _
  have hp : 1≤p := by
    have hmem : i.castSucc∈Finset.univ.filter (fun j : Fin (k+1) => j.val < i.succ.val) := by
      simp
    exact (Kind.weight_pos (T i.castSucc)).trans
      (Finset.single_le_sum (fun j _ => Nat.zero_le ((T j).weight)) hmem)
  have hw : p+q=weight T := by
    dsimp [p,q]
    rw [tail_weight]
    unfold weight
    simpa only [not_lt] using
      (Finset.sum_filter_add_sum_filter_not (s:=Finset.univ)
        (p:=fun j : Fin (k+1) => j.val < i.succ.val) (f:=fun j => (T j).weight))
  rw [hformula,←hw]
  exact ThirdPortArithmetic.interface_quarter p q A hp hA

end Erdos1016.ExactMaximumSupport.MixedCappedInterfaceCounts
