import Erdos1016.ExactMaximumSupport.MixedRingParity

set_option autoImplicit false

/-!
# Cutting the physical ring at an unused interface

The cyclic tile order becomes a literal finite linear order.
Every selected physical edge then stays within a tile or joins consecutive levels.
-/

noncomputable section
namespace Erdos1016.ExactMaximumSupport.MixedTiles
open BoundaryTrace BoundaryTrace.Network

variable {k : ℕ} (T : Fin (k+1) → Kind)

/-- The interface after a tile, including the last tile's closing pair. -/
def interfaceEdge (i : Fin (k+1)) (b : Bool) : RingEdge T :=
  Fin.lastCases (Sum.inr b) (fun j => Sum.inl (link T j b)) i

@[simp] theorem interfaceEdge_castSucc (i : Fin k) (b : Bool) :
    interfaceEdge T i.castSucc b=Sum.inl (link T i b) := by simp [interfaceEdge]

@[simp] theorem interfaceEdge_last (b : Bool) :
    interfaceEdge T (Fin.last k) b=Sum.inr b := by simp [interfaceEdge]

/-- Tile level zero follows the chosen cut interface. -/
def tileLevel (c i : Fin (k+1)) : ℕ :=
  if i.val≤c.val then k-c.val+i.val else i.val-c.val-1

/-- These levels are within the length of the opened ring. -/
theorem tileLevel_le (c i : Fin (k+1)) : tileLevel c i≤k := by
  unfold tileLevel
  have := c.isLt
  have := i.isLt
  split_ifs <;> omega

/-- The opened-ring levels retain every tile distinctly. -/
theorem tileLevel_injective (c : Fin (k+1)) : Function.Injective (tileLevel c) := by
  intro i j h
  apply Fin.ext
  have := c.isLt
  have := i.isLt
  have := j.isLt
  simp only [tileLevel] at h
  split_ifs at h <;> omega

/-- The tile just before the cut has the last level. -/
theorem tileLevel_self (c : Fin (k+1)) : tileLevel c c=k := by
  have := c.isLt
  simp only [tileLevel,le_refl,if_true]
  omega

/-- Every non-cut ordinary interface increases the level by one. -/
theorem tileLevel_link (c : Fin (k+1)) (i : Fin k) (hi : i.castSucc≠c) :
    tileLevel c i.succ=tileLevel c i.castSucc+1 := by
  have hne : i.val≠c.val := fun h => hi (Fin.ext h)
  have := c.isLt
  have := i.isLt
  have hcast : i.castSucc.val=i.val := rfl
  simp only [tileLevel,Fin.val_succ,hcast]
  split_ifs <;> omega

/-- The non-cut closing interface also increases the level by one. -/
theorem tileLevel_close (c : Fin (k+1)) (hc : c≠Fin.last k) :
    tileLevel c 0=tileLevel c (Fin.last k)+1 := by
  have hne : c.val≠k := fun h => hc (Fin.ext h)
  have := c.isLt
  simp only [tileLevel,Fin.val_zero,Fin.val_last,Nat.zero_le,if_true,Nat.add_zero]
  split_ifs <;> omega

/-- At an unused cut, every selected physical edge is one-Lipschitz in tile level. -/
theorem selected_edge_level_lipschitz (hk : 1 ≤ k) (twist : Equiv.Perm Bool)
    (z : (ring T hk twist).Word) (c : Fin (k+1))
    (hc : ∀ b,z (interfaceEdge T c b)=0)
    (e : RingEdge T) (he : z e≠0) :
    tileLevel c ((ring T hk twist).src e).1≤
      tileLevel c ((ring T hk twist).dst e).1+1 ∧
    tileLevel c ((ring T hk twist).dst e).1≤
      tileLevel c ((ring T hk twist).src e).1+1 := by
  rcases e with (⟨i,e⟩ | ⟨i,b⟩) | b
  · change tileLevel c i≤tileLevel c i+1 ∧ tileLevel c i≤tileLevel c i+1
    omega
  · have hi : i.castSucc≠c := by
      intro h
      apply he
      have hh := hc b
      rw [←h,interfaceEdge_castSucc] at hh
      exact hh
    have hh := tileLevel_link c i hi
    change tileLevel c i.castSucc≤tileLevel c i.succ+1 ∧
      tileLevel c i.succ≤tileLevel c i.castSucc+1
    omega
  · have hlast : c≠Fin.last k := by
      intro h
      apply he
      have hh := hc b
      rw [h,interfaceEdge_last] at hh
      exact hh
    have hh := tileLevel_close c hlast
    change tileLevel c (Fin.last k)≤tileLevel c 0+1 ∧
      tileLevel c 0≤tileLevel c (Fin.last k)+1
    omega

end Erdos1016.ExactMaximumSupport.MixedTiles
