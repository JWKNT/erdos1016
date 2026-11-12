import Erdos1016.ExactMaximum.Ring
import Erdos1016.ExactMaximum.NetCutFour

set_option autoImplicit false

/-!
# Chains of tiles of the ring

The chain that ends in the tile `i` consists of the tiles `0, …, i` of `ring k` and of the links
between them. This file proves lower bounds for the numbers of paths, of path pairs and of cycles
of a chain, by induction on `i`. In the step from the tile `i` to the tile `i + 1`, every path,
path pair or cycle of the longer chain that we count is glued from pieces in the shorter chain,
pieces in the new tile, and the two links between them.

The glued words are sums `X + Y + Z` with `X` in the shorter chain, `Y` in the new tile and `Z`
on the links. Such a sum determines its three parts (`parts_eq`), so the gluing maps are
injective.

The results are collected in `ChainBounds` and `chainBounds`.
-/

noncomputable section
open scoped BigOperators

namespace Erdos1016.ExactMaximum.Ring

open BoundaryTrace BoundaryTrace.Network

local instance ringChainDecidable (p : Prop) : Decidable p := Classical.propDecidable p

/-! ### Counting -/

/-- Two injective maps with disjoint images. -/
theorem natCard_add_le {α β γ : Type*} [Finite α] [Finite β] [Finite γ] (f₁ : α → γ)
    (f₂ : β → γ) (h₁ : Function.Injective f₁) (h₂ : Function.Injective f₂)
    (h : ∀ a b, f₁ a ≠ f₂ b) : Nat.card α + Nat.card β ≤ Nat.card γ := by
  rw [← Nat.card_sum]
  apply Nat.card_le_card_of_injective (Sum.elim f₁ f₂)
  rintro (a | a) (b | b) hab
  · exact congrArg Sum.inl (h₁ hab)
  · exact absurd hab (h a b)
  · exact absurd hab.symm (h b a)
  · exact congrArg Sum.inr (h₂ hab)

/-- Three injective maps with pairwise disjoint images. -/
theorem natCard_add_add_le {α β δ γ : Type*} [Finite α] [Finite β] [Finite δ] [Finite γ]
    (f₁ : α → γ) (f₂ : β → γ) (f₃ : δ → γ) (h₁ : Function.Injective f₁)
    (h₂ : Function.Injective f₂) (h₃ : Function.Injective f₃) (h12 : ∀ a b, f₁ a ≠ f₂ b)
    (h13 : ∀ a d, f₁ a ≠ f₃ d) (h23 : ∀ b d, f₂ b ≠ f₃ d) :
    Nat.card α + Nat.card β + Nat.card δ ≤ Nat.card γ := by
  rw [← Nat.card_sum]
  apply natCard_add_le (Sum.elim f₁ f₂) f₃
  · rintro (a | a) (b | b) hab
    · exact congrArg Sum.inl (h₁ hab)
    · exact absurd hab (h12 a b)
    · exact absurd hab.symm (h12 b a)
    · exact congrArg Sum.inr (h₂ hab)
  · exact h₃
  · rintro (a | a) d
    · exact h13 a d
    · exact h23 a d

/-- A sum of three words within three sets of edges that exclude each other determines the three
words. -/
theorem parts_eq {E : Type*} {p q r : E → Prop} (hpq : ∀ e, p e → ¬ q e)
    (hpr : ∀ e, p e → ¬ r e) (hqr : ∀ e, q e → ¬ r e) {X Y Z X' Y' Z' : E → Bit}
    (hX : Within X p) (hY : Within Y q) (hZ : Within Z r) (hX' : Within X' p)
    (hY' : Within Y' q) (hZ' : Within Z' r) (h : X + Y + Z = X' + Y' + Z') :
    X = X' ∧ Y = Y' ∧ Z = Z' := by
  have hval : ∀ e, X e + Y e + Z e = X' e + Y' e + Z' e := fun e => congrFun h e
  refine ⟨?_, ?_, ?_⟩
  · funext e
    by_cases hp : p e
    · have h1 := hval e
      rw [hY.eq_zero (hpq e hp), hZ.eq_zero (hpr e hp), hY'.eq_zero (hpq e hp),
        hZ'.eq_zero (hpr e hp)] at h1
      simp only [add_zero] at h1
      exact h1
    · rw [hX.eq_zero hp, hX'.eq_zero hp]
  · funext e
    by_cases hq : q e
    · have h1 := hval e
      rw [hX.eq_zero (fun hp => hpq e hp hq), hZ.eq_zero (hqr e hq),
        hX'.eq_zero (fun hp => hpq e hp hq), hZ'.eq_zero (hqr e hq)] at h1
      simp only [zero_add, add_zero] at h1
      exact h1
    · rw [hY.eq_zero hq, hY'.eq_zero hq]
  · funext e
    by_cases hr : r e
    · have h1 := hval e
      rw [hX.eq_zero (fun hp => hpr e hp hr), hY.eq_zero (fun hq => hqr e hq hr),
        hX'.eq_zero (fun hp => hpr e hp hr), hY'.eq_zero (fun hq => hqr e hq hr)] at h1
      simp only [zero_add] at h1
      exact h1
    · rw [hZ.eq_zero hr, hZ'.eq_zero hr]

variable {k : ℕ}

/-- The cycles within a set of edges. -/
abbrev CyclesIn (p : Edge k → Prop) : Type :=
  {x : (ring k).Word // (ring k).IsCycleWord x ∧ Within x p}

/-- A larger set of edges contains at least as many paths. -/
theorem natCard_pathsIn_mono {p q : Edge k → Prop} (hpq : ∀ e, p e → q e) (s t : Vertex k) :
    Nat.card (PathsIn p s t) ≤ Nat.card (PathsIn q s t) := by
  apply Nat.card_le_card_of_injective
    (fun P : PathsIn p s t => (⟨P.1, P.2.1, fun e he => hpq e (P.2.2 e he)⟩ : PathsIn q s t))
  intro a b hab
  have h := congrArg Subtype.val hab
  exact Subtype.ext h

/-! ### The step from the tile `i` to the tile `i + 1` -/

section Step

variable (i : Fin k)

/-- The two links between the tile `i` and the tile `i + 1`. -/
def linkEdge (e : Edge k) : Prop := ∃ x, e = link i x

theorem chain_not_tile (e : Edge k) (h : chainEdge i.castSucc e) : ¬ tileEdge i.succ e := by
  rcases e with ⟨i', x, y⟩ | ⟨i', x⟩ | x | x | u
  · intro h'
    have h1 : i' ≤ i.castSucc := h
    have h2 : i' = i.succ := h'
    rw [h2] at h1
    exact absurd h1 (not_le.2 (Fin.castSucc_lt_succ i))
  all_goals exact fun h' => h'

theorem chain_not_link (e : Edge k) (h : chainEdge i.castSucc e) : ¬ linkEdge i e := by
  rintro ⟨x, rfl⟩
  have h1 : i.succ ≤ i.castSucc := h
  exact absurd h1 (not_le.2 (Fin.castSucc_lt_succ i))

theorem tile_not_link (e : Edge k) (h : tileEdge i.succ e) : ¬ linkEdge i e := by
  rintro ⟨x, rfl⟩
  exact h

theorem within_link (x : Bool) : Within (unitWord (link i x) : Edge k → Bit) (linkEdge i) :=
  within_unitWord ⟨x, rfl⟩

theorem within_chain_succ {X : Edge k → Bit} (h : Within X (chainEdge i.castSucc)) :
    Within X (chainEdge i.succ) :=
  fun e he => chainEdge_mono (le_of_lt (Fin.castSucc_lt_succ i)) (h e he)

theorem within_tile_succ {X : Edge k → Bit} (h : Within X (tileEdge i.succ)) :
    Within X (chainEdge i.succ) :=
  fun e he => chainEdge_of_tileEdge (le_refl _) (h e he)

theorem within_link_succ (x : Bool) :
    Within (unitWord (link i x) : Edge k → Bit) (chainEdge i.succ) :=
  within_unitWord (chainEdge_link i x)

/-- A word in the chain and a word in the next tile have no common vertex. -/
theorem vd_chain_tile {X Y : (ring k).Word} (hX : Within X (chainEdge i.castSucc))
    (hY : Within Y (tileEdge i.succ)) : (ring k).VertexDisjoint X Y :=
  (ring k).vertexDisjoint_of_within (fun e he => inside_of_chainEdge (hX e he))
    (fun e he => outside_of_tileEdge i (hY e he))

theorem link_ne {x x' : Bool} (h : x ≠ x') : (link i x : Edge k) ≠ link i x' := by
  simp [link, h]

/-- **Paths across the chain.** A path of the chain from `L 0 x` to `R i z`, the link `z`, and a
path of the tile `i + 1` from its left vertex `z` to its right vertex `y` form a path of the
longer chain. So the number of paths from `L 0 x` to `R (i+1) y` is at least the sum over `z` of
the products of the two numbers. -/
theorem step_paths (x y : Bool) :
    Nat.card (PathsIn (chainEdge i.castSucc) (L 0 x) (R i.castSucc false)) *
          Nat.card (PathsIn (tileEdge i.succ) (L i.succ false) (R i.succ y)) +
        Nat.card (PathsIn (chainEdge i.castSucc) (L 0 x) (R i.castSucc true)) *
          Nat.card (PathsIn (tileEdge i.succ) (L i.succ true) (R i.succ y)) ≤
      Nat.card (PathsIn (chainEdge i.succ) (L 0 x) (R i.succ y)) := by
  rw [← Nat.card_prod, ← Nat.card_prod]
  have key : ∀ z : Bool, ∃ f : PathsIn (chainEdge i.castSucc) (L 0 x) (R i.castSucc z) ×
      PathsIn (tileEdge i.succ) (L i.succ z) (R i.succ y) →
      PathsIn (chainEdge i.succ) (L 0 x) (R i.succ y),
      ∀ a, (f a).1 = a.1.1 + a.2.1 + unitWord (link i z) := by
    intro z
    refine ⟨fun a => ⟨a.1.1 + a.2.1 + unitWord (link i z), ?_, ?_⟩, fun a => rfl⟩
    · exact a.1.2.1.glue a.2.2.1 (joins_link i z) (vd_chain_tile i a.1.2.2 a.2.2.2)
    · exact ((within_chain_succ i a.1.2.2).add (within_tile_succ i a.2.2.2)).add
        (within_link_succ i z)
  obtain ⟨f₁, hf₁⟩ := key false
  obtain ⟨f₂, hf₂⟩ := key true
  have hinj : ∀ (z : Bool) (f : PathsIn (chainEdge i.castSucc) (L 0 x) (R i.castSucc z) ×
      PathsIn (tileEdge i.succ) (L i.succ z) (R i.succ y) →
      PathsIn (chainEdge i.succ) (L 0 x) (R i.succ y)),
      (∀ a, (f a).1 = a.1.1 + a.2.1 + unitWord (link i z)) → Function.Injective f := by
    intro z f hf a b hab
    have h := congrArg Subtype.val hab
    rw [hf, hf] at h
    obtain ⟨h1, h2, _⟩ := parts_eq (chain_not_tile i) (chain_not_link i) (tile_not_link i)
      a.1.2.2 a.2.2.2 (within_link i z) b.1.2.2 b.2.2.2 (within_link i z) h
    exact Prod.ext (Subtype.ext h1) (Subtype.ext h2)
  apply natCard_add_le f₁ f₂ (hinj false f₁ hf₁) (hinj true f₂ hf₂)
  intro a b hab
  have h := congrArg Subtype.val hab
  rw [hf₁, hf₂] at h
  obtain ⟨_, _, h3⟩ := parts_eq (chain_not_tile i) (chain_not_link i) (tile_not_link i)
    a.1.2.2 a.2.2.2 (within_link i false) b.1.2.2 b.2.2.2 (within_link i true) h
  have h4 := congrFun h3 (link i false)
  rw [unitWord_self, unitWord_of_ne (link_ne i (by decide : true ≠ false))] at h4
  exact one_ne_zero h4

/-- **Cycles of the chain.** The cycles of the shorter chain, the cycle of the new tile, and the
cycles that consist of a path between the two right vertices of the shorter chain, the two links,
and a path between the two left vertices of the new tile are different cycles of the longer
chain. -/
theorem step_cycles :
    Nat.card (CyclesIn (chainEdge i.castSucc)) + 1 +
        Nat.card (PathsIn (chainEdge i.castSucc) (R i.castSucc false) (R i.castSucc true)) *
          Nat.card (PathsIn (tileEdge i.succ) (L i.succ false) (L i.succ true)) ≤
      Nat.card (CyclesIn (chainEdge i.succ)) := by
  rw [← Nat.card_prod]
  have h1 : (1 : ℕ) = Nat.card Unit := by simp
  rw [h1]
  -- the three maps
  obtain ⟨f₁, hf₁⟩ : ∃ f : CyclesIn (chainEdge i.castSucc) → CyclesIn (chainEdge i.succ),
      ∀ a, (f a).1 = a.1 :=
    ⟨fun a => ⟨a.1, a.2.1, within_chain_succ i a.2.2⟩, fun _ => rfl⟩
  obtain ⟨T, hT, hTin⟩ : ∃ T : (ring k).Word, (ring k).IsCycleWord T ∧
      Within T (tileEdge i.succ) :=
    ⟨_, isCycleWord_tile i.succ,
      (((within_unitWord (tileEdge_sq _ _ _)).add (within_unitWord (tileEdge_sq _ _ _))).add
        (within_unitWord (tileEdge_sq _ _ _))).add (within_unitWord (tileEdge_sq _ _ _))⟩
  obtain ⟨f₂, hf₂⟩ : ∃ f : Unit → CyclesIn (chainEdge i.succ), ∀ a, (f a).1 = T :=
    ⟨fun _ => ⟨T, hT, within_tile_succ i hTin⟩, fun _ => rfl⟩
  obtain ⟨f₃, hf₃⟩ : ∃ f : PathsIn (chainEdge i.castSucc) (R i.castSucc false)
      (R i.castSucc true) × PathsIn (tileEdge i.succ) (L i.succ false) (L i.succ true) →
      CyclesIn (chainEdge i.succ),
      ∀ a, (f a).1 = a.1.1 + a.2.1 + (unitWord (link i false) + unitWord (link i true)) := by
    refine ⟨fun a => ⟨a.1.1 + a.2.1 + (unitWord (link i false) + unitWord (link i true)),
      ?_, ?_⟩, fun a => rfl⟩
    · exact a.1.2.1.glue_cycle a.2.2.1 (joins_link i false) (joins_link i true)
        (vd_chain_tile i a.1.2.2 a.2.2.2)
    · exact ((within_chain_succ i a.1.2.2).add (within_tile_succ i a.2.2.2)).add
        ((within_link_succ i false).add (within_link_succ i true))
  have hlinks : Within (unitWord (link i false) + unitWord (link i true) : Edge k → Bit)
      (linkEdge i) := (within_link i false).add (within_link i true)
  have hlinks_ne : (unitWord (link i false) + unitWord (link i true) : Edge k → Bit) ≠ 0 := by
    intro h
    have h4 := congrFun h (link i false)
    have h5 : (unitWord (link i false) + unitWord (link i true) : Edge k → Bit) (link i false) =
        1 := unitPair_apply_left (link_ne i (by decide : false ≠ true))
    rw [h5] at h4
    exact one_ne_zero h4
  apply natCard_add_add_le f₁ f₂ f₃
  · intro a b hab
    have h := congrArg Subtype.val hab
    rw [hf₁, hf₁] at h
    exact Subtype.ext h
  · intro a b _
    rfl
  · intro a b hab
    have h := congrArg Subtype.val hab
    rw [hf₃, hf₃] at h
    obtain ⟨k1, k2, _⟩ := parts_eq (chain_not_tile i) (chain_not_link i) (tile_not_link i)
      a.1.2.2 a.2.2.2 hlinks b.1.2.2 b.2.2.2 hlinks h
    exact Prod.ext (Subtype.ext k1) (Subtype.ext k2)
  · -- a cycle of the shorter chain is not the cycle of the tile
    intro a b hab
    have h := congrArg Subtype.val hab
    rw [hf₁, hf₂] at h
    obtain ⟨e, he⟩ := a.2.1.exists_edge
    have h0 : T e = 0 := hTin.eq_zero (chain_not_tile i e (a.2.2 e he))
    rw [← h] at h0
    exact he h0
  · -- a cycle of the shorter chain uses no link
    intro a b hab
    have h := congrArg Subtype.val hab
    rw [hf₁, hf₃] at h
    have h' : a.1 + 0 + 0 = b.1.1 + b.2.1 + (unitWord (link i false) + unitWord (link i true)) := by
      rw [add_zero, add_zero]
      exact h
    obtain ⟨_, _, k3⟩ := parts_eq (chain_not_tile i) (chain_not_link i) (tile_not_link i)
      a.2.2 (fun e he => absurd rfl he) (fun e he => absurd rfl he) b.1.2.2 b.2.2.2 hlinks h'
    exact hlinks_ne k3.symm
  · -- the cycle of the tile uses no link
    intro a b hab
    have h := congrArg Subtype.val hab
    rw [hf₂, hf₃] at h
    have h' : 0 + T + 0 = b.1.1 + b.2.1 + (unitWord (link i false) + unitWord (link i true)) := by
      rw [add_zero, zero_add]
      exact h
    obtain ⟨_, _, k3⟩ := parts_eq (chain_not_tile i) (chain_not_link i) (tile_not_link i)
      (fun e he => absurd rfl he) hTin (fun e he => absurd rfl he) b.1.2.2 b.2.2.2 hlinks h'
    exact hlinks_ne k3.symm

/-! ### Paths that pass through the new tile and return -/

theorem bool_ne_not (z : Bool) : z ≠ !z := by
  cases z <;> decide

theorem within_links (z : Bool) :
    Within (unitWord (link i z) + unitWord (link i (!z)) : Edge k → Bit) (linkEdge i) :=
  (within_link i z).add (within_link i (!z))

theorem links_ne_zero (z : Bool) :
    (unitWord (link i z) + unitWord (link i (!z)) : Edge k → Bit) ≠ 0 := by
  intro h
  have h4 := congrFun h (link i z)
  have h5 : (unitWord (link i z) + unitWord (link i (!z)) : Edge k → Bit) (link i z) = 1 :=
    unitPair_apply_left (link_ne i (bool_ne_not z))
  rw [h5] at h4
  exact one_ne_zero h4

/-- A vertex outside the tiles of the chain is not a vertex of a word in the chain. -/
theorem deg_eq_zero_of_within_chain {X : (ring k).Word} (hX : Within X (chainEdge i.castSucc))
    {v : Vertex k} (hv : ¬ upTo i.castSucc v) : (ring k).deg X v = 0 := by
  rcases Nat.eq_zero_or_pos ((ring k).deg X v) with h | h
  · exact h
  · exact absurd ((ring k).mem_of_within_inside (fun e he => inside_of_chainEdge (hX e he)) h) hv

theorem not_upTo_L (x : Bool) : ¬ upTo i.castSucc (L i.succ x : Vertex k) :=
  fun h => absurd (show i.succ ≤ i.castSucc from h) (not_le.2 (Fin.castSucc_lt_succ i))

/-- The two edges of the new tile that a path uses when it enters at the right vertex `false`,
leaves through the link `z`, returns through the other link and ends at the right vertex
`true`. -/
theorem within_turn (z : Bool) :
    Within (unitWord (sq i.succ z false) + unitWord (sq i.succ (!z) true) : Edge k → Bit)
      (tileEdge i.succ) :=
  (within_unitWord (tileEdge_sq _ _ _)).add (within_unitWord (tileEdge_sq _ _ _))

theorem turn_ne :
    (unitWord (sq i.succ false false) + unitWord (sq i.succ (!false) true) : Edge k → Bit) ≠
      unitWord (sq i.succ true false) + unitWord (sq i.succ (!true) true) := by
  intro h
  have hb : false ≠ true := by decide
  have h1 := congrFun h (sq i.succ false false)
  have h2 : (unitWord (sq i.succ false false) + unitWord (sq i.succ (!false) true) :
      Edge k → Bit) (sq i.succ false false) = 1 := by
    show unitWord (sq i.succ false false) (sq i.succ false false) +
      unitWord (sq i.succ (!false) true) (sq i.succ false false) = 1
    rw [unitWord_self, unitWord_of_ne (sq_ne_right _ _ (Ne.symm hb)), add_zero]
  have h3 : (unitWord (sq i.succ true false) + unitWord (sq i.succ (!true) true) :
      Edge k → Bit) (sq i.succ false false) = 0 := by
    show unitWord (sq i.succ true false) (sq i.succ false false) +
      unitWord (sq i.succ (!true) true) (sq i.succ false false) = 0
    rw [unitWord_of_ne (sq_ne_left _ _ (Ne.symm hb)),
      unitWord_of_ne (sq_ne_right _ _ (Ne.symm hb)), add_zero]
  rw [h2, h3] at h1
  exact one_ne_zero h1

/-- A path between the two right vertices of the chain, the two links, and two edges of the new
tile form a path between the two right vertices of the new tile. -/
theorem isPathWord_through (z : Bool) {W : (ring k).Word}
    (hW : (ring k).IsPathWord (R i.castSucc false) (R i.castSucc true) W)
    (hWin : Within W (chainEdge i.castSucc)) :
    (ring k).IsPathWord (R i.succ false) (R i.succ true)
      (W + (unitWord (sq i.succ z false) + unitWord (sq i.succ (!z) true)) +
        (unitWord (link i z) + unitWord (link i (!z)))) := by
  have hWz : (ring k).IsPathWord (R i.castSucc z) (R i.castSucc (!z)) W := by
    cases z
    · exact hW
    · exact hW.symm
  have hA : (ring k).IsPathWord (R i.succ false) (L i.succ z) (unitWord (sq i.succ z false)) :=
    ((ring k).isPathWord_unitWord (joins_sq i.succ z false)).symm
  have hB : (ring k).IsPathWord (L i.succ (!z)) (R i.succ true)
      (unitWord (sq i.succ (!z) true)) :=
    (ring k).isPathWord_unitWord (joins_sq i.succ (!z) true)
  have hAin : Within (unitWord (sq i.succ z false) : Edge k → Bit) (tileEdge i.succ) :=
    within_unitWord (tileEdge_sq _ _ _)
  have hBin : Within (unitWord (sq i.succ (!z) true) : Edge k → Bit) (tileEdge i.succ) :=
    within_unitWord (tileEdge_sq _ _ _)
  have h := hA.glue_three hWz hB (joins_link i z).symm (joins_link i (!z))
    (vd_chain_tile i hWin hAin).symm
    (isPathPair_tile i.succ (bool_ne_not z) (by decide : false ≠ true)).2.2
    (vd_chain_tile i hWin hBin)
  have heq : W + (unitWord (sq i.succ z false) + unitWord (sq i.succ (!z) true)) +
      (unitWord (link i z) + unitWord (link i (!z))) =
      unitWord (sq i.succ z false) + W + unitWord (link i z) + unitWord (sq i.succ (!z) true) +
        unitWord (link i (!z)) := by
    abel
  rw [heq]
  exact h

/-! ### The other steps -/

/-- **Path pairs across the chain.** A path pair of the chain from the two left vertices of the
first tile to the two right vertices of the tile `i`, the two links, and two edges of the new
tile form a path pair of the longer chain. Both pairings of the shorter chain give each pairing
of the longer chain. -/
theorem step_pairs (z : Bool) :
    Nat.card ((ring k).PathPairsIn (chainEdge i.castSucc) (L 0 false) (R i.castSucc false)
          (L 0 true) (R i.castSucc (!false))) +
        Nat.card ((ring k).PathPairsIn (chainEdge i.castSucc) (L 0 false) (R i.castSucc true)
          (L 0 true) (R i.castSucc (!true))) ≤
      Nat.card ((ring k).PathPairsIn (chainEdge i.succ) (L 0 false) (R i.succ z) (L 0 true)
        (R i.succ (!z))) := by
  have key : ∀ z' : Bool, ∃ f : (ring k).PathPairsIn (chainEdge i.castSucc) (L 0 false)
      (R i.castSucc z') (L 0 true) (R i.castSucc (!z')) →
      (ring k).PathPairsIn (chainEdge i.succ) (L 0 false) (R i.succ z) (L 0 true)
        (R i.succ (!z)),
      ∀ a, (f a).1 = (a.1.1 + unitWord (sq i.succ z' z) + unitWord (link i z'),
        a.1.2 + unitWord (sq i.succ (!z') (!z)) + unitWord (link i (!z'))) := by
    intro z'
    have hC : Within (unitWord (sq i.succ z' z) : Edge k → Bit) (tileEdge i.succ) :=
      within_unitWord (tileEdge_sq _ _ _)
    have hD : Within (unitWord (sq i.succ (!z') (!z)) : Edge k → Bit) (tileEdge i.succ) :=
      within_unitWord (tileEdge_sq _ _ _)
    refine ⟨fun a => ⟨(a.1.1 + unitWord (sq i.succ z' z) + unitWord (link i z'),
      a.1.2 + unitWord (sq i.succ (!z') (!z)) + unitWord (link i (!z'))), ?_, ?_, ?_⟩,
      fun a => rfl⟩
    · exact a.2.1.glue (isPathPair_tile i.succ (bool_ne_not z') (bool_ne_not z))
        (joins_link i z') (joins_link i (!z')) (vd_chain_tile i a.2.2.1 hC)
        (vd_chain_tile i a.2.2.1 hD) (vd_chain_tile i a.2.2.2 hC) (vd_chain_tile i a.2.2.2 hD)
    · exact ((within_chain_succ i a.2.2.1).add (within_tile_succ i hC)).add
        (within_link_succ i z')
    · exact ((within_chain_succ i a.2.2.2).add (within_tile_succ i hD)).add
        (within_link_succ i (!z'))
  obtain ⟨f₁, hf₁⟩ := key false
  obtain ⟨f₂, hf₂⟩ := key true
  have hinj : ∀ (z' : Bool) (f : (ring k).PathPairsIn (chainEdge i.castSucc) (L 0 false)
      (R i.castSucc z') (L 0 true) (R i.castSucc (!z')) →
      (ring k).PathPairsIn (chainEdge i.succ) (L 0 false) (R i.succ z) (L 0 true)
        (R i.succ (!z))),
      (∀ a, (f a).1 = (a.1.1 + unitWord (sq i.succ z' z) + unitWord (link i z'),
        a.1.2 + unitWord (sq i.succ (!z') (!z)) + unitWord (link i (!z')))) →
      Function.Injective f := by
    intro z' f hf a b hab
    have h := congrArg Subtype.val hab
    rw [hf, hf] at h
    have h1 := congrArg Prod.fst h
    have h2 := congrArg Prod.snd h
    obtain ⟨k1, _, _⟩ := parts_eq (chain_not_tile i) (chain_not_link i) (tile_not_link i)
      a.2.2.1 (within_unitWord (tileEdge_sq _ _ _)) (within_link i z') b.2.2.1
      (within_unitWord (tileEdge_sq _ _ _)) (within_link i z') h1
    obtain ⟨k2, _, _⟩ := parts_eq (chain_not_tile i) (chain_not_link i) (tile_not_link i)
      a.2.2.2 (within_unitWord (tileEdge_sq _ _ _)) (within_link i (!z')) b.2.2.2
      (within_unitWord (tileEdge_sq _ _ _)) (within_link i (!z')) h2
    exact Subtype.ext (Prod.ext k1 k2)
  apply natCard_add_le f₁ f₂ (hinj false f₁ hf₁) (hinj true f₂ hf₂)
  intro a b hab
  have h := congrArg Subtype.val hab
  rw [hf₁, hf₂] at h
  have h1 := congrArg Prod.fst h
  obtain ⟨_, _, k3⟩ := parts_eq (chain_not_tile i) (chain_not_link i) (tile_not_link i)
    a.2.2.1 (within_unitWord (tileEdge_sq _ _ _)) (within_link i false) b.2.2.1
    (within_unitWord (tileEdge_sq _ _ _)) (within_link i true) h1
  have h4 := congrFun k3 (link i false)
  rw [unitWord_self, unitWord_of_ne (link_ne i (by decide : true ≠ false))] at h4
  exact one_ne_zero h4

/-- **Paths between the two left vertices of the first tile.** Such a path of the shorter chain
is one of the longer chain. Also, a path pair of the shorter chain to its two right vertices, the
two links, and a path between the two left vertices of the new tile form such a path. -/
theorem step_left :
    Nat.card (PathsIn (chainEdge i.castSucc) (L 0 false) (L 0 true)) +
        Nat.card ((ring k).PathPairsIn (chainEdge i.castSucc) (L 0 false) (R i.castSucc false)
            (L 0 true) (R i.castSucc (!false))) *
          Nat.card (PathsIn (tileEdge i.succ) (L i.succ false) (L i.succ true)) +
        Nat.card ((ring k).PathPairsIn (chainEdge i.castSucc) (L 0 false) (R i.castSucc true)
            (L 0 true) (R i.castSucc (!true))) *
          Nat.card (PathsIn (tileEdge i.succ) (L i.succ false) (L i.succ true)) ≤
      Nat.card (PathsIn (chainEdge i.succ) (L 0 false) (L 0 true)) := by
  rw [← Nat.card_prod, ← Nat.card_prod]
  obtain ⟨f₀, hf₀⟩ : ∃ f : PathsIn (chainEdge i.castSucc) (L 0 false) (L 0 true) →
      PathsIn (chainEdge i.succ) (L 0 false) (L 0 true), ∀ a, (f a).1 = a.1 :=
    ⟨fun a => ⟨a.1, a.2.1, within_chain_succ i a.2.2⟩, fun _ => rfl⟩
  have key : ∀ z : Bool, ∃ f : (ring k).PathPairsIn (chainEdge i.castSucc) (L 0 false)
      (R i.castSucc z) (L 0 true) (R i.castSucc (!z)) ×
      PathsIn (tileEdge i.succ) (L i.succ false) (L i.succ true) →
      PathsIn (chainEdge i.succ) (L 0 false) (L 0 true),
      ∀ a, (f a).1 = a.1.1.1 + a.1.1.2 + a.2.1 +
        (unitWord (link i z) + unitWord (link i (!z))) := by
    intro z
    refine ⟨fun a => ⟨a.1.1.1 + a.1.1.2 + a.2.1 +
      (unitWord (link i z) + unitWord (link i (!z))), ?_, ?_⟩, fun a => rfl⟩
    · have hQ := a.2.2.1
      have hQz : (ring k).IsPathWord (L i.succ z) (L i.succ (!z)) a.2.1 := by
        revert hQ
        cases z
        · exact fun hQ => hQ
        · exact fun hQ => hQ.symm
      have h := a.1.2.1.1.glue_three hQz a.1.2.1.2.1.symm (joins_link i z)
        (joins_link i (!z)).symm (vd_chain_tile i a.1.2.2.1 a.2.2.2) a.1.2.1.2.2
        (vd_chain_tile i a.1.2.2.2 a.2.2.2).symm
      have heq : a.1.1.1 + a.1.1.2 + a.2.1 + (unitWord (link i z) + unitWord (link i (!z))) =
          a.1.1.1 + a.2.1 + unitWord (link i z) + a.1.1.2 + unitWord (link i (!z)) := by
        abel
      rw [heq]
      exact h
    · exact (((within_chain_succ i a.1.2.2.1).add (within_chain_succ i a.1.2.2.2)).add
        (within_tile_succ i a.2.2.2)).add ((within_link_succ i z).add (within_link_succ i (!z)))
  obtain ⟨f₁, hf₁⟩ := key false
  obtain ⟨f₂, hf₂⟩ := key true
  have hinj : ∀ (z : Bool) (f : (ring k).PathPairsIn (chainEdge i.castSucc) (L 0 false)
      (R i.castSucc z) (L 0 true) (R i.castSucc (!z)) ×
      PathsIn (tileEdge i.succ) (L i.succ false) (L i.succ true) →
      PathsIn (chainEdge i.succ) (L 0 false) (L 0 true)),
      (∀ a, (f a).1 = a.1.1.1 + a.1.1.2 + a.2.1 +
        (unitWord (link i z) + unitWord (link i (!z)))) → Function.Injective f := by
    intro z f hf a b hab
    have h := congrArg Subtype.val hab
    rw [hf, hf] at h
    obtain ⟨k1, k2, _⟩ := parts_eq (chain_not_tile i) (chain_not_link i) (tile_not_link i)
      (a.1.2.2.1.add a.1.2.2.2) a.2.2.2 (within_links i z) (b.1.2.2.1.add b.1.2.2.2) b.2.2.2
      (within_links i z) h
    obtain ⟨k3, k4⟩ := a.1.2.1.eq_of_add_eq b.1.2.1 k1
    exact Prod.ext (Subtype.ext (Prod.ext k3 k4)) (Subtype.ext k2)
  apply natCard_add_add_le f₀ f₁ f₂ _ (hinj false f₁ hf₁) (hinj true f₂ hf₂)
  · -- a path of the shorter chain uses no link
    intro a b hab
    have h := congrArg Subtype.val hab
    rw [hf₀, hf₁] at h
    have h' : a.1 + 0 + 0 = b.1.1.1 + b.1.1.2 + b.2.1 +
        (unitWord (link i false) + unitWord (link i (!false))) := by
      rw [add_zero, add_zero]
      exact h
    obtain ⟨_, _, k3⟩ := parts_eq (chain_not_tile i) (chain_not_link i) (tile_not_link i)
      a.2.2 (fun e he => absurd rfl he) (fun e he => absurd rfl he)
      (b.1.2.2.1.add b.1.2.2.2) b.2.2.2 (within_links i false) h'
    exact links_ne_zero i false k3.symm
  · intro a b hab
    have h := congrArg Subtype.val hab
    rw [hf₀, hf₂] at h
    have h' : a.1 + 0 + 0 = b.1.1.1 + b.1.1.2 + b.2.1 +
        (unitWord (link i true) + unitWord (link i (!true))) := by
      rw [add_zero, add_zero]
      exact h
    obtain ⟨_, _, k3⟩ := parts_eq (chain_not_tile i) (chain_not_link i) (tile_not_link i)
      a.2.2 (fun e he => absurd rfl he) (fun e he => absurd rfl he)
      (b.1.2.2.1.add b.1.2.2.2) b.2.2.2 (within_links i true) h'
    exact links_ne_zero i true k3.symm
  · -- the two pairings give different paths
    intro a b hab
    have h := congrArg Subtype.val hab
    rw [hf₁, hf₂] at h
    obtain ⟨k1, _, _⟩ := parts_eq (chain_not_tile i) (chain_not_link i) (tile_not_link i)
      (a.1.2.2.1.add a.1.2.2.2) a.2.2.2 (within_links i false) (b.1.2.2.1.add b.1.2.2.2)
      b.2.2.2 (within_links i true) h
    exact a.1.2.1.false_of_add_eq b.1.2.1 k1 a.1.2.1.2.1.deg_right_pos
  · intro a b hab
    have h := congrArg Subtype.val hab
    rw [hf₀, hf₀] at h
    exact Subtype.ext h

/-- **Paths between the two right vertices of the last tile.** Such a path of the new tile is
one of the longer chain. Also, a path between the two right vertices of the shorter chain, the
two links, and two edges of the new tile form such a path, in two ways. -/
theorem step_right :
    Nat.card (PathsIn (tileEdge i.succ) (R i.succ false) (R i.succ true)) +
        Nat.card (PathsIn (chainEdge i.castSucc) (R i.castSucc false) (R i.castSucc true)) +
        Nat.card (PathsIn (chainEdge i.castSucc) (R i.castSucc false) (R i.castSucc true)) ≤
      Nat.card (PathsIn (chainEdge i.succ) (R i.succ false) (R i.succ true)) := by
  obtain ⟨f₀, hf₀⟩ : ∃ f : PathsIn (tileEdge i.succ) (R i.succ false) (R i.succ true) →
      PathsIn (chainEdge i.succ) (R i.succ false) (R i.succ true), ∀ a, (f a).1 = a.1 :=
    ⟨fun a => ⟨a.1, a.2.1, within_tile_succ i a.2.2⟩, fun _ => rfl⟩
  have key : ∀ z : Bool, ∃ f : PathsIn (chainEdge i.castSucc) (R i.castSucc false)
      (R i.castSucc true) → PathsIn (chainEdge i.succ) (R i.succ false) (R i.succ true),
      ∀ a, (f a).1 = a.1 + (unitWord (sq i.succ z false) + unitWord (sq i.succ (!z) true)) +
        (unitWord (link i z) + unitWord (link i (!z))) := by
    intro z
    refine ⟨fun a => ⟨a.1 + (unitWord (sq i.succ z false) + unitWord (sq i.succ (!z) true)) +
      (unitWord (link i z) + unitWord (link i (!z))), isPathWord_through i z a.2.1 a.2.2, ?_⟩,
      fun a => rfl⟩
    exact ((within_chain_succ i a.2.2).add (within_tile_succ i (within_turn i z))).add
      ((within_link_succ i z).add (within_link_succ i (!z)))
  obtain ⟨f₁, hf₁⟩ := key false
  obtain ⟨f₂, hf₂⟩ := key true
  have hinj : ∀ (z : Bool) (f : PathsIn (chainEdge i.castSucc) (R i.castSucc false)
      (R i.castSucc true) → PathsIn (chainEdge i.succ) (R i.succ false) (R i.succ true)),
      (∀ a, (f a).1 = a.1 + (unitWord (sq i.succ z false) + unitWord (sq i.succ (!z) true)) +
        (unitWord (link i z) + unitWord (link i (!z)))) → Function.Injective f := by
    intro z f hf a b hab
    have h := congrArg Subtype.val hab
    rw [hf, hf] at h
    obtain ⟨k1, _, _⟩ := parts_eq (chain_not_tile i) (chain_not_link i) (tile_not_link i)
      a.2.2 (within_turn i z) (within_links i z) b.2.2 (within_turn i z) (within_links i z) h
    exact Subtype.ext k1
  apply natCard_add_add_le f₀ f₁ f₂ _ (hinj false f₁ hf₁) (hinj true f₂ hf₂)
  · intro a b hab
    have h := congrArg Subtype.val hab
    rw [hf₀, hf₁] at h
    have h' : 0 + a.1 + 0 = b.1 +
        (unitWord (sq i.succ false false) + unitWord (sq i.succ (!false) true)) +
        (unitWord (link i false) + unitWord (link i (!false))) := by
      rw [add_zero, zero_add]
      exact h
    obtain ⟨_, _, k3⟩ := parts_eq (chain_not_tile i) (chain_not_link i) (tile_not_link i)
      (fun e he => absurd rfl he) a.2.2 (fun e he => absurd rfl he) b.2.2 (within_turn i false)
      (within_links i false) h'
    exact links_ne_zero i false k3.symm
  · intro a b hab
    have h := congrArg Subtype.val hab
    rw [hf₀, hf₂] at h
    have h' : 0 + a.1 + 0 = b.1 +
        (unitWord (sq i.succ true false) + unitWord (sq i.succ (!true) true)) +
        (unitWord (link i true) + unitWord (link i (!true))) := by
      rw [add_zero, zero_add]
      exact h
    obtain ⟨_, _, k3⟩ := parts_eq (chain_not_tile i) (chain_not_link i) (tile_not_link i)
      (fun e he => absurd rfl he) a.2.2 (fun e he => absurd rfl he) b.2.2 (within_turn i true)
      (within_links i true) h'
    exact links_ne_zero i true k3.symm
  · intro a b hab
    have h := congrArg Subtype.val hab
    rw [hf₁, hf₂] at h
    obtain ⟨_, k2, _⟩ := parts_eq (chain_not_tile i) (chain_not_link i) (tile_not_link i)
      a.2.2 (within_turn i false) (within_links i false) b.2.2 (within_turn i true)
      (within_links i true) h
    exact turn_ne i k2
  · intro a b hab
    have h := congrArg Subtype.val hab
    rw [hf₀, hf₀] at h
    exact Subtype.ext h

/-- **Path pairs between the two ends of the chain.** A path between the two left vertices of the
first tile in the shorter chain and a path between the two right vertices of the new tile are
such a pair. Also, a pair of the shorter chain gives two pairs of the longer chain: its second
path is continued through the two links and two edges of the new tile. -/
theorem step_ends :
    Nat.card (PathsIn (chainEdge i.castSucc) (L 0 false) (L 0 true)) *
          Nat.card (PathsIn (tileEdge i.succ) (R i.succ false) (R i.succ true)) +
        Nat.card ((ring k).PathPairsIn (chainEdge i.castSucc) (L 0 false) (L 0 true)
          (R i.castSucc false) (R i.castSucc true)) +
        Nat.card ((ring k).PathPairsIn (chainEdge i.castSucc) (L 0 false) (L 0 true)
          (R i.castSucc false) (R i.castSucc true)) ≤
      Nat.card ((ring k).PathPairsIn (chainEdge i.succ) (L 0 false) (L 0 true) (R i.succ false)
        (R i.succ true)) := by
  rw [← Nat.card_prod]
  obtain ⟨f₀, hf₀⟩ : ∃ f : PathsIn (chainEdge i.castSucc) (L 0 false) (L 0 true) ×
      PathsIn (tileEdge i.succ) (R i.succ false) (R i.succ true) →
      (ring k).PathPairsIn (chainEdge i.succ) (L 0 false) (L 0 true) (R i.succ false)
        (R i.succ true), ∀ a, (f a).1 = (a.1.1, a.2.1) :=
    ⟨fun a => ⟨(a.1.1, a.2.1), ⟨a.1.2.1, a.2.2.1, vd_chain_tile i a.1.2.2 a.2.2.2⟩,
      within_chain_succ i a.1.2.2, within_tile_succ i a.2.2.2⟩, fun _ => rfl⟩
  have key : ∀ z : Bool, ∃ f : (ring k).PathPairsIn (chainEdge i.castSucc) (L 0 false)
      (L 0 true) (R i.castSucc false) (R i.castSucc true) →
      (ring k).PathPairsIn (chainEdge i.succ) (L 0 false) (L 0 true) (R i.succ false)
        (R i.succ true),
      ∀ a, (f a).1 = (a.1.1, a.1.2 +
        (unitWord (sq i.succ z false) + unitWord (sq i.succ (!z) true)) +
        (unitWord (link i z) + unitWord (link i (!z)))) := by
    intro z
    refine ⟨fun a => ⟨(a.1.1, a.1.2 +
      (unitWord (sq i.succ z false) + unitWord (sq i.succ (!z) true)) +
      (unitWord (link i z) + unitWord (link i (!z)))),
      ⟨a.2.1.1, isPathWord_through i z a.2.1.2.1 a.2.2.2, ?_⟩, within_chain_succ i a.2.2.1,
      ?_⟩, fun a => rfl⟩
    · -- the first path has no common vertex with the continued second path
      have hU := a.2.2.1
      have hd := a.2.1.2.2
      have hW := a.2.1.2.1
      have hR : ∀ x : Bool, (ring k).deg a.1.1 (R i.castSucc x) = 0 := by
        intro x
        cases x
        · exact hd.deg_left_eq_zero hW.deg_left_pos
        · exact hd.deg_left_eq_zero hW.deg_right_pos
      have hLk : ∀ x : Bool, (ring k).VertexDisjoint a.1.1 (unitWord (link i x)) := fun x =>
        (ring k).vertexDisjoint_unitWord (joins_link i x) (hR x)
          (deg_eq_zero_of_within_chain i hU (not_upTo_L i x))
      exact (hd.add_right (vd_chain_tile i hU (within_turn i z))).add_right
        ((hLk z).add_right (hLk (!z)))
    · exact ((within_chain_succ i a.2.2.2).add (within_tile_succ i (within_turn i z))).add
        ((within_link_succ i z).add (within_link_succ i (!z)))
  obtain ⟨f₁, hf₁⟩ := key false
  obtain ⟨f₂, hf₂⟩ := key true
  have hinj : ∀ (z : Bool) (f : (ring k).PathPairsIn (chainEdge i.castSucc) (L 0 false)
      (L 0 true) (R i.castSucc false) (R i.castSucc true) →
      (ring k).PathPairsIn (chainEdge i.succ) (L 0 false) (L 0 true) (R i.succ false)
        (R i.succ true)),
      (∀ a, (f a).1 = (a.1.1, a.1.2 +
        (unitWord (sq i.succ z false) + unitWord (sq i.succ (!z) true)) +
        (unitWord (link i z) + unitWord (link i (!z))))) → Function.Injective f := by
    intro z f hf a b hab
    have h := congrArg Subtype.val hab
    rw [hf, hf] at h
    have h1 := congrArg Prod.fst h
    have h2 := congrArg Prod.snd h
    obtain ⟨k1, _, _⟩ := parts_eq (chain_not_tile i) (chain_not_link i) (tile_not_link i)
      a.2.2.2 (within_turn i z) (within_links i z) b.2.2.2 (within_turn i z) (within_links i z)
      h2
    exact Subtype.ext (Prod.ext h1 k1)
  apply natCard_add_add_le f₀ f₁ f₂ _ (hinj false f₁ hf₁) (hinj true f₂ hf₂)
  · intro a b hab
    have h := congrArg Subtype.val hab
    rw [hf₀, hf₁] at h
    have h2 := congrArg Prod.snd h
    have h' : 0 + a.2.1 + 0 = b.1.2 +
        (unitWord (sq i.succ false false) + unitWord (sq i.succ (!false) true)) +
        (unitWord (link i false) + unitWord (link i (!false))) := by
      rw [add_zero, zero_add]
      exact h2
    obtain ⟨_, _, k3⟩ := parts_eq (chain_not_tile i) (chain_not_link i) (tile_not_link i)
      (fun e he => absurd rfl he) a.2.2.2 (fun e he => absurd rfl he) b.2.2.2
      (within_turn i false) (within_links i false) h'
    exact links_ne_zero i false k3.symm
  · intro a b hab
    have h := congrArg Subtype.val hab
    rw [hf₀, hf₂] at h
    have h2 := congrArg Prod.snd h
    have h' : 0 + a.2.1 + 0 = b.1.2 +
        (unitWord (sq i.succ true false) + unitWord (sq i.succ (!true) true)) +
        (unitWord (link i true) + unitWord (link i (!true))) := by
      rw [add_zero, zero_add]
      exact h2
    obtain ⟨_, _, k3⟩ := parts_eq (chain_not_tile i) (chain_not_link i) (tile_not_link i)
      (fun e he => absurd rfl he) a.2.2.2 (fun e he => absurd rfl he) b.2.2.2
      (within_turn i true) (within_links i true) h'
    exact links_ne_zero i true k3.symm
  · intro a b hab
    have h := congrArg Subtype.val hab
    rw [hf₁, hf₂] at h
    have h2 := congrArg Prod.snd h
    obtain ⟨_, k2, _⟩ := parts_eq (chain_not_tile i) (chain_not_link i) (tile_not_link i)
      a.2.2.2 (within_turn i false) (within_links i false) b.2.2.2 (within_turn i true)
      (within_links i true) h2
    exact turn_ne i k2
  · intro a b hab
    have h := congrArg Subtype.val hab
    rw [hf₀, hf₀] at h
    exact Prod.ext (Subtype.ext (congrArg Prod.fst h)) (Subtype.ext (congrArg Prod.snd h))

end Step

end Erdos1016.ExactMaximum.Ring
