import Erdos1016.ExactMaximumSupport.MixedCappedSuffixPaths
import Erdos1016.ExactMaximumSupport.NetworkCutDeletedPaths
import Erdos1016.ExactMaximum.NetEmbed

set_option autoImplicit false
set_option maxHeartbeats 1500000

/-!
# Actual cap-edge continuation counts

Removing the left cap leaves precisely the already-counted one-cap suffix,
with the removed vertex retained as an ambient isolate. The physical embedding
identifies the exact edge restriction, so no simplicity/model law is assumed.
-/
noncomputable section
namespace Erdos1016.ExactMaximumSupport.MixedCappedCapCounts
open BoundaryTrace BoundaryTrace.Network MixedTiles
local instance (priority := 2000) propDecidable (p : Prop) : Decidable p :=
  Classical.propDecidable p
variable {k : ℕ}

/-- The one-cap network embeds on all labels except the two left-cap labels. -/
def suffixEmbed (T : Fin (k+1) → Kind) :
    Network.Embed (MixedCappedSuffix.network T) (capped T) where
  φ := Sum.map id (fun _ => true)
  ψ := Sum.map id Sum.inr
  φ_inj := Sum.map_injective.mpr ⟨Function.injective_id,fun a b _ => Subsingleton.elim a b⟩
  ψ_inj := Sum.map_injective.mpr ⟨Function.injective_id,Sum.inr_injective⟩
  src e := by cases e <;> rfl
  dst e := by cases e <;> rfl

/-- Its image is the literal exterior of the left-cap vertex. -/
theorem suffixEmbed_image (T : Fin (k+1) → Kind) (e : CappedEdge T) :
    (suffixEmbed T).image e ↔ (capped T).outside (fun v => v=Sum.inr false) e := by
  rcases e with e | b | b <;>
    simp [Network.Embed.image,suffixEmbed,Network.outside,capped,cappedSrc,cappedDst]

/-- Either first-tile entry has exactly the suffix count in the literal cap exterior. -/
theorem exterior_entry_count (T : Fin (k+1) → Kind) (b : Bool) :
    ((capped T).sub ((capped T).outside (fun v => v=Sum.inr false))).numPaths
      (Sum.inl (left T 0 b)) (Sum.inr true)=2^weight T := by
  rw [(capped T).numPaths_sub]
  have heq := (suffixEmbed T).numPaths_eq (MixedCappedSuffix.entry T b) (MixedCappedSuffix.cap T)
  have hc : Nat.card {R : (capped T).Word //
      (capped T).IsPathWord (Sum.inl (left T 0 b)) (Sum.inr true) R ∧
        Within R ((capped T).outside (fun v => v=Sum.inr false))} =
      Nat.card {R : (capped T).Word //
      (capped T).IsPathWord (Sum.inl (left T 0 b)) (Sum.inr true) R ∧
        Within R (suffixEmbed T).image} := by
    apply Nat.card_congr
    apply Equiv.subtypeEquivRight
    intro R
    apply and_congr Iff.rfl
    constructor
    · intro h e he
      exact (suffixEmbed_image T e).mpr (h e he)
    · intro h e he
      exact (suffixEmbed_image T e).mp (h e he)
  rw [hc]
  exact heq.symm.trans (MixedCappedSuffix.numPaths_entry_cap T b)

/-- Restoring either left-cap edge creates a full pair to the right cap. -/
theorem left_cap_count (T : Fin (k+1) → Kind) (b : Bool) :
    MarkedPathCount.count (capped T) (Sum.inr (Sum.inl b)) (Sum.inr true)=
      2^(weight T+1) := by
  let S : CappedVertex T → Prop := fun v => v=Sum.inr false
  have he : (capped T).Joins (Sum.inr (Sum.inl b))
      (Sum.inr false) (Sum.inl (left T 0 b)) := Or.inl ⟨rfl,rfl⟩
  have hf : (capped T).Joins (Sum.inr (Sum.inl (!b)))
      (Sum.inr false) (Sum.inl (left T 0 (!b))) := Or.inl ⟨rfl,rfl⟩
  have hne : (Sum.inr (Sum.inl b) : CappedEdge T)≠Sum.inr (Sum.inl (!b)) := by
    cases b <;> simp
  have hcover (g : CappedEdge T) (hg : (capped T).crosses S g) :
      g=Sum.inr (Sum.inl b) ∨ g=Sum.inr (Sum.inl (!b)) := by
    rcases g with g | c | c
    · simp [Network.crosses,S,capped,cappedSrc,cappedDst] at hg
    · cases b <;> cases c <;> simp
    · simp [Network.crosses,S,capped,cappedSrc,cappedDst] at hg
  have hh := NetworkCutDeletedPaths.marked_count_interface (capped T) S (t:=Sum.inr true) hne
    he rfl (by simp [S]) hf rfl (by simp [S]) hcover (by simp [S])
  simpa [S,exterior_entry_count,pow_succ,Nat.mul_two] using hh

end Erdos1016.ExactMaximumSupport.MixedCappedCapCounts
