import Erdos1016.ExactMaximum.RingChain

set_option autoImplicit false

/-!
# Lower bounds for the chains of the ring

Let `m` be the index of the last tile of a chain of `ring k`, so that the chain has `m + 1`
tiles. This file proves by induction on `m` (`chainBounds`):

* at least `2^(2m+1)` paths from a left vertex of the first tile to a right vertex of the last
  tile;
* at least `2^(m+2) - 2` paths between the two left vertices of the first tile, and as many
  between the two right vertices of the last tile;
* at least `2^m` path pairs from the two left vertices of the first tile to the two right
  vertices of the last tile, for each of the two pairings;
* at least `gamma m` path pairs that consist of a path between the two left vertices of the first
  tile and a path between the two right vertices of the last tile;
* at least `kappa m` cycles.

The numbers `gamma m = m 2^(m+2) + 4 - 2^(m+2)` and `kappa m = 2^(m+3) - 3m - 7` are defined by
their recursions.
-/

noncomputable section
open scoped BigOperators

namespace Erdos1016.ExactMaximum.Ring

open BoundaryTrace BoundaryTrace.Network

local instance ringBoundsDecidable (p : Prop) : Decidable p := Classical.propDecidable p

/-- The lower bound for the number of path pairs between the two ends of a chain. -/
def gamma : ℕ → ℕ
  | 0 => 0
  | m + 1 => 2 * gamma m + 2 ^ (m + 3) - 4

/-- The lower bound for the number of cycles of a chain. -/
def kappa : ℕ → ℕ
  | 0 => 1
  | m + 1 => kappa m + 2 ^ (m + 3) - 3

variable {k : ℕ}

/-- The lower bounds for the chain that ends in the tile `i`. -/
structure ChainBounds (i : Fin (k + 1)) : Prop where
  paths : ∀ x y : Bool,
    2 ^ (2 * i.val + 1) ≤ Nat.card (PathsIn (chainEdge i) (L 0 x) (R i y))
  left : 2 ^ (i.val + 2) ≤ Nat.card (PathsIn (chainEdge i) (L 0 false) (L 0 true)) + 2
  right : 2 ^ (i.val + 2) ≤ Nat.card (PathsIn (chainEdge i) (R i false) (R i true)) + 2
  pairs : ∀ z : Bool, 2 ^ i.val ≤
    Nat.card ((ring k).PathPairsIn (chainEdge i) (L 0 false) (R i z) (L 0 true) (R i (!z)))
  ends : gamma i.val ≤
    Nat.card ((ring k).PathPairsIn (chainEdge i) (L 0 false) (L 0 true) (R i false) (R i true))
  cycles : kappa i.val ≤ Nat.card (CyclesIn (chainEdge i))

/-- The chain of the first tile alone. -/
theorem chainBounds_zero : ChainBounds (0 : Fin (k + 1)) := by
  have hsub : ∀ e : Edge k, tileEdge 0 e → chainEdge 0 e :=
    fun e he => chainEdge_of_tileEdge (le_refl _) he
  refine ⟨fun x y => ?_, ?_, ?_, fun z => ?_, ?_, ?_⟩
  · have h1 := two_le_tile_paths (k := k) 0 x y
    have h2 := natCard_pathsIn_mono hsub (L 0 x) (R (0 : Fin (k + 1)) y)
    simp only [Fin.val_zero]
    omega
  · have h1 := two_le_tile_paths_left (k := k) 0
    have h2 := natCard_pathsIn_mono hsub (L 0 false) (L (0 : Fin (k + 1)) true)
    simp only [Fin.val_zero]
    omega
  · have h1 := two_le_tile_paths_right (k := k) 0
    have h2 := natCard_pathsIn_mono hsub (R 0 false) (R (0 : Fin (k + 1)) true)
    simp only [Fin.val_zero]
    omega
  · simp only [Fin.val_zero, pow_zero]
    have hne : Nonempty ((ring k).PathPairsIn (chainEdge 0) (L 0 false) (R 0 z) (L 0 true)
        (R 0 (!z))) :=
      ⟨⟨(unitWord (sq 0 false z), unitWord (sq 0 true (!z))),
        isPathPair_tile 0 (by decide : false ≠ true) (by cases z <;> decide),
        within_unitWord (hsub _ (tileEdge_sq _ _ _)),
        within_unitWord (hsub _ (tileEdge_sq _ _ _))⟩⟩
    exact Nat.card_pos
  · simp only [Fin.val_zero, gamma]
    exact Nat.zero_le _
  · simp only [Fin.val_zero, kappa]
    have hne : Nonempty (CyclesIn (chainEdge (0 : Fin (k + 1)))) :=
      ⟨⟨_, isCycleWord_tile 0,
        (((within_unitWord (hsub _ (tileEdge_sq _ _ _))).add
          (within_unitWord (hsub _ (tileEdge_sq _ _ _)))).add
          (within_unitWord (hsub _ (tileEdge_sq _ _ _)))).add
          (within_unitWord (hsub _ (tileEdge_sq _ _ _)))⟩⟩
    exact Nat.card_pos

/-- The step from the chain that ends in the tile `i` to the chain that ends in the tile
`i + 1`. -/
theorem chainBounds_succ (i : Fin k) (h : ChainBounds i.castSucc) : ChainBounds i.succ := by
  obtain ⟨hA, hU, hW, hM, hG, hC⟩ := h
  simp only [Fin.coe_castSucc] at hA hU hW hM hG hC
  have hTl := two_le_tile_paths_left i.succ
  have hTr := two_le_tile_paths_right i.succ
  refine ⟨fun x y => ?_, ?_, ?_, fun z => ?_, ?_, ?_⟩
  · have h1 := step_paths i x y
    have h2 := Nat.mul_le_mul (hA x false) (two_le_tile_paths i.succ false y)
    have h3 := Nat.mul_le_mul (hA x true) (two_le_tile_paths i.succ true y)
    have e1 : 2 ^ (2 * (i.succ : Fin (k + 1)).val + 1) = 2 ^ (2 * i.val + 1) * 2 +
        2 ^ (2 * i.val + 1) * 2 := by
      rw [Fin.val_succ]
      ring
    rw [e1]
    exact le_trans (Nat.add_le_add h2 h3) h1
  · have h1 := step_left i
    have h2 := Nat.mul_le_mul (hM false) hTl
    have h3 := Nat.mul_le_mul (hM true) hTl
    have e1 : 2 ^ ((i.succ : Fin (k + 1)).val + 2) = 2 ^ (i.val + 2) + 2 ^ i.val * 2 +
        2 ^ i.val * 2 := by
      rw [Fin.val_succ]
      ring
    rw [e1]
    omega
  · have h1 := step_right i
    have e1 : 2 ^ ((i.succ : Fin (k + 1)).val + 2) = 2 ^ (i.val + 2) + 2 ^ (i.val + 2) := by
      rw [Fin.val_succ]
      ring
    rw [e1]
    omega
  · have h1 := step_pairs i z
    have e1 : 2 ^ (i.succ : Fin (k + 1)).val = 2 ^ i.val + 2 ^ i.val := by
      rw [Fin.val_succ]
      ring
    rw [e1]
    exact le_trans (Nat.add_le_add (hM false) (hM true)) h1
  · have h1 := step_ends i
    have h2 := Nat.mul_le_mul_left
      (Nat.card (PathsIn (chainEdge i.castSucc) (L 0 false) (L 0 true))) hTr
    have e1 : gamma (i.succ : Fin (k + 1)).val = 2 * gamma i.val + 2 ^ (i.val + 3) - 4 := by
      rw [Fin.val_succ]
      rfl
    have e2 : 2 ^ (i.val + 3) = 2 * 2 ^ (i.val + 2) := by ring
    rw [e1, e2]
    omega
  · have h1 := step_cycles i
    have h2 := Nat.mul_le_mul_left
      (Nat.card (PathsIn (chainEdge i.castSucc) (R i.castSucc false) (R i.castSucc true))) hTl
    have e1 : kappa (i.succ : Fin (k + 1)).val = kappa i.val + 2 ^ (i.val + 3) - 3 := by
      rw [Fin.val_succ]
      rfl
    have e2 : 2 ^ (i.val + 3) = 2 * 2 ^ (i.val + 2) := by ring
    rw [e1, e2]
    omega

/-- **The lower bounds for every chain.** -/
theorem chainBounds (i : Fin (k + 1)) : ChainBounds i := by
  induction i using Fin.induction with
  | zero => exact chainBounds_zero
  | succ i ih => exact chainBounds_succ i ih

/-- The closed form of `gamma`. -/
theorem gamma_add (m : ℕ) : gamma m + 2 ^ (m + 2) = m * 2 ^ (m + 2) + 4 := by
  induction m with
  | zero => simp [gamma]
  | succ m ih =>
    have e1 : gamma (m + 1) = 2 * gamma m + 2 ^ (m + 3) - 4 := rfl
    have e2 : 2 ^ (m + 3) = 2 * 2 ^ (m + 2) := by ring
    have e5 : (m + 1) * (2 * 2 ^ (m + 2)) = 2 * (m * 2 ^ (m + 2)) + 2 * 2 ^ (m + 2) := by ring
    have hpos : 4 ≤ 2 ^ (m + 2) := by
      have : 2 ^ 2 ≤ 2 ^ (m + 2) := Nat.pow_le_pow_right (by norm_num) (by omega)
      simpa using this
    rw [e1, e2, e5]
    omega

/-- The closed form of `kappa`. -/
theorem kappa_add (m : ℕ) : kappa m + 3 * m + 7 = 2 ^ (m + 3) := by
  induction m with
  | zero => simp [kappa]
  | succ m ih =>
    have e1 : kappa (m + 1) = kappa m + 2 ^ (m + 3) - 3 := rfl
    have e3 : 2 ^ (m + 1 + 3) = 2 * 2 ^ (m + 3) := by ring
    have hpos : 8 ≤ 2 ^ (m + 3) := by
      have : 2 ^ 3 ≤ 2 ^ (m + 3) := Nat.pow_le_pow_right (by norm_num) (by omega)
      simpa using this
    rw [e1, e3]
    omega

end Erdos1016.ExactMaximum.Ring
