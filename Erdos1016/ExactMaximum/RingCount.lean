import Erdos1016.ExactMaximum.RingBounds
import Erdos1016.ExactMaximum.HorakKim

set_option autoImplicit false

/-!
# The number of cycles of the ring

The chain of all tiles of `ring k` is closed by the two hubs. This file counts, from below,

* the cycles of the ring without the rung (`closing_cycles`): the cycles of the chain, the cycles
  through one hub, and the cycles through both hubs;
* the paths between the two hubs in the ring without the rung (`closing_paths`);
* the cycles of the ring with the rung (`rung_cycles`): a cycle uses the rung or it does not.

With the bounds for chains this gives `numCyclesNoRung_ge` and `numPathsHubs_ge`. The comparison
with the numbers of Horak and Kim is in `horakKim_le_numCyclesNoRung` (rank `2k + 3`) and
`horakKim_le_numCycles_ring` (rank `2k + 4`).
-/

noncomputable section
open scoped BigOperators

namespace Erdos1016.ExactMaximum.Ring

open BoundaryTrace BoundaryTrace.Network

local instance ringCountDecidable (p : Prop) : Decidable p := Classical.propDecidable p

/-! ### Counting with tags -/

theorem ne_of_tags {α β γ T : Type*} (τ : γ → T) (f : α → γ) (g : β → γ) {s t : T}
    (hf : ∀ a, τ (f a) = s) (hg : ∀ b, τ (g b) = t) (hst : s ≠ t) (a : α) (b : β) :
    f a ≠ g b := by
  intro hab
  apply hst
  rw [← hf a, ← hg b, hab]

/-- Four injective maps whose images have four different tags. -/
theorem natCard_four_le {α₁ α₂ α₃ α₄ γ T : Type*} [Finite α₁] [Finite α₂] [Finite α₃]
    [Finite α₄] [Finite γ] (τ : γ → T) {t₁ t₂ t₃ t₄ : T} (f₁ : α₁ → γ) (f₂ : α₂ → γ)
    (f₃ : α₃ → γ) (f₄ : α₄ → γ) (i₁ : Function.Injective f₁) (i₂ : Function.Injective f₂)
    (i₃ : Function.Injective f₃) (i₄ : Function.Injective f₄) (h₁ : ∀ a, τ (f₁ a) = t₁)
    (h₂ : ∀ a, τ (f₂ a) = t₂) (h₃ : ∀ a, τ (f₃ a) = t₃) (h₄ : ∀ a, τ (f₄ a) = t₄)
    (d12 : t₁ ≠ t₂) (d13 : t₁ ≠ t₃) (d14 : t₁ ≠ t₄) (d23 : t₂ ≠ t₃) (d24 : t₂ ≠ t₄)
    (d34 : t₃ ≠ t₄) :
    Nat.card α₁ + Nat.card α₂ + Nat.card α₃ + Nat.card α₄ ≤ Nat.card γ := by
  rw [← Nat.card_sum, ← Nat.card_sum]
  refine natCard_add_le (Sum.elim (Sum.elim f₁ f₂) f₃) f₄ ?inj i₄ ?dis
  case dis =>
    rintro ((a | a) | a) b
    · exact ne_of_tags τ f₁ f₄ h₁ h₄ d14 a b
    · exact ne_of_tags τ f₂ f₄ h₂ h₄ d24 a b
    · exact ne_of_tags τ f₃ f₄ h₃ h₄ d34 a b
  case inj =>
    rintro ((a | a) | a) ((b | b) | b) hab
    · exact congrArg (fun u => Sum.inl (Sum.inl u)) (i₁ hab)
    · exact absurd hab (ne_of_tags τ f₁ f₂ h₁ h₂ d12 a b)
    · exact absurd hab (ne_of_tags τ f₁ f₃ h₁ h₃ d13 a b)
    · exact absurd hab.symm (ne_of_tags τ f₁ f₂ h₁ h₂ d12 b a)
    · exact congrArg (fun u => Sum.inl (Sum.inr u)) (i₂ hab)
    · exact absurd hab (ne_of_tags τ f₂ f₃ h₂ h₃ d23 a b)
    · exact absurd hab.symm (ne_of_tags τ f₁ f₃ h₁ h₃ d13 b a)
    · exact absurd hab.symm (ne_of_tags τ f₂ f₃ h₂ h₃ d23 b a)
    · exact congrArg Sum.inr (i₃ hab)

/-- A sum of two words within two sets of edges that exclude each other determines the two
words. -/
theorem parts_eq_two {E : Type*} {p r : E → Prop} (hpr : ∀ e, p e → ¬ r e) {X Z X' Z' : E → Bit}
    (hX : Within X p) (hZ : Within Z r) (hX' : Within X' p) (hZ' : Within Z' r)
    (h : X + Z = X' + Z') : X = X' ∧ Z = Z' := by
  have hval : ∀ e, X e + Z e = X' e + Z' e := fun e => congrFun h e
  constructor
  · funext e
    by_cases hp : p e
    · have h1 := hval e
      rw [hZ.eq_zero (hpr e hp), hZ'.eq_zero (hpr e hp), add_zero, add_zero] at h1
      exact h1
    · rw [hX.eq_zero hp, hX'.eq_zero hp]
  · funext e
    by_cases hr : r e
    · have h1 := hval e
      rw [hX.eq_zero (fun hp => hpr e hp hr), hX'.eq_zero (fun hp => hpr e hp hr), zero_add,
        zero_add] at h1
      exact h1
    · rw [hZ.eq_zero hr, hZ'.eq_zero hr]

variable {k : ℕ}

/-! ### The hubs -/

/-- All edges except the rung. -/
def noRung (e : Edge k) : Prop := e ≠ rung

/-- The edges that are not in the chain of all tiles. -/
def offChain (e : Edge k) : Prop := ¬ chainEdge (Fin.last k) e

theorem offChain_first (x : Bool) : offChain (first x : Edge k) := fun h => h

theorem offChain_last (x : Bool) : offChain (last x : Edge k) := fun h => h

theorem noRung_first (x : Bool) : noRung (first x : Edge k) := by
  simp [noRung, first, rung]

theorem noRung_last (x : Bool) : noRung (last x : Edge k) := by
  simp [noRung, last, rung]

theorem noRung_of_chain {i : Fin (k + 1)} {e : Edge k} (h : chainEdge i e) : noRung e := by
  intro he
  rw [he] at h
  exact h

theorem within_noRung {i : Fin (k + 1)} {X : Edge k → Bit} (h : Within X (chainEdge i)) :
    Within X noRung := fun e he => noRung_of_chain (h e he)

/-- A word in a chain has no vertex at a hub. -/
theorem deg_hub {i : Fin (k + 1)} {X : (ring k).Word} (h : Within X (chainEdge i)) (x : Bool) :
    (ring k).deg X (H x) = 0 := by
  rcases Nat.eq_zero_or_pos ((ring k).deg X (H x)) with h0 | h0
  · exact h0
  · exact ((ring k).mem_of_within_inside (fun e he => inside_of_chainEdge (h e he)) h0).elim

theorem deg_add_eq_zero {X Y : (ring k).Word} {v : Vertex k} (h1 : (ring k).deg X v = 0)
    (h2 : (ring k).deg Y v = 0) : (ring k).deg (X + Y) v = 0 := by
  have h3 := (ring k).deg_add_le X Y v
  omega

theorem H_ne {x x' : Bool} (h : x ≠ x') : (H x : Vertex k) ≠ H x' := by
  simp [H, h]

/-- The two edges at the hub `x`. -/
def hubWord (x : Bool) : Edge k → Bit := unitWord (last x) + unitWord (first x)

theorem within_hubWord (x : Bool) : Within (hubWord x : Edge k → Bit) offChain :=
  (within_unitWord (offChain_last x)).add (within_unitWord (offChain_first x))

theorem within_hubWord_noRung (x : Bool) : Within (hubWord x : Edge k → Bit) noRung :=
  (within_unitWord (noRung_last x)).add (within_unitWord (noRung_first x))

theorem hubWord_first (x x' : Bool) :
    (hubWord x : Edge k → Bit) (first x') = if x = x' then 1 else 0 := by
  show unitWord (last x) (first x') + unitWord (first x) (first x') = _
  rw [unitWord_apply, unitWord_apply]
  by_cases h : x = x'
  · simp [last, first, h]
  · simp [last, first, h]

/-- A word in the chain is zero at the edges at the hubs. -/
theorem chain_first {X : Edge k → Bit} (h : Within X (chainEdge (Fin.last k))) (x : Bool) :
    X (first x) = 0 := h.eq_zero (offChain_first x)

/-! ### Cycles through the hubs -/

/-- A path of the chain from the left vertex `x` of the first tile to the right vertex `x` of
the last tile and the two edges at the hub `x` form a cycle. -/
theorem isCycleWord_hub (x : Bool) {A : (ring k).Word}
    (hA : (ring k).IsPathWord (L 0 x) (R (Fin.last k) x) A)
    (hin : Within A (chainEdge (Fin.last k))) : (ring k).IsCycleWord (A + hubWord x) := by
  have h1 := hA.add_pendant (joins_last x) (deg_hub hin x)
  have h2 := h1.add_closing (joins_first x).symm (by
    show A (first x) + unitWord (last x) (first x) = 0
    rw [chain_first hin x, unitWord_apply]
    simp [last, first])
  have heq : A + hubWord x = A + unitWord (last x) + unitWord (first x) := by
    unfold hubWord
    abel
  rw [heq]
  exact h2

/-- Two disjoint paths of the chain from `L 0 false` to `R k true` and from `L 0 true` to
`R k false`, and the four edges at the hubs, form a cycle. -/
theorem isCycleWord_cross {A B : (ring k).Word}
    (h : (ring k).IsPathPair (L 0 false) (R (Fin.last k) true) (L 0 true)
      (R (Fin.last k) (!true)) A B)
    (hA : Within A (chainEdge (Fin.last k))) (hB : Within B (chainEdge (Fin.last k))) :
    (ring k).IsCycleWord (A + B + (hubWord true + hubWord false)) := by
  obtain ⟨pA, pB, hd⟩ := h
  have h1 := pA.add_pendant (joins_last true) (deg_hub hA true)
  have hd1 : (ring k).VertexDisjoint (A + unitWord (last true)) B :=
    VertexDisjoint.add_left hd ((ring k).vertexDisjoint_unitWord (joins_last true)
      (hd.deg_right_eq_zero pA.deg_right_pos) (deg_hub hB true)).symm
  have h2 := h1.glue pB (joins_first true) hd1
  have h3 := h2.add_pendant (joins_last false) (by
    apply deg_add_eq_zero (deg_add_eq_zero (deg_add_eq_zero (deg_hub hA false) _)
      (deg_hub hB false))
    · exact (ring k).deg_unitWord_of_joins (joins_first true) (H_ne (by decide))
        (L_ne_H _ _ _).symm
    · exact (ring k).deg_unitWord_of_joins (joins_last true) (R_ne_H _ _ _).symm
        (H_ne (by decide)))
  have h4 := h3.add_closing (joins_first false).symm (by
    show A (first false) + unitWord (last true) (first false) + B (first false) +
      unitWord (first true) (first false) + unitWord (last false) (first false) = 0
    rw [chain_first hA false, chain_first hB false, unitWord_apply, unitWord_apply,
      unitWord_apply]
    simp [last, first])
  have heq : A + B + (hubWord true + hubWord false) =
      A + unitWord (last true) + B + unitWord (first true) + unitWord (last false) +
        unitWord (first false) := by
    unfold hubWord
    abel
  rw [heq]
  exact h4

/-- A path of the chain between the two left vertices of the first tile, a disjoint path between
the two right vertices of the last tile, and the four edges at the hubs form a cycle. -/
theorem isCycleWord_ends {U W : (ring k).Word}
    (h : (ring k).IsPathPair (L 0 false) (L 0 true) (R (Fin.last k) false)
      (R (Fin.last k) true) U W)
    (hU : Within U (chainEdge (Fin.last k))) (hW : Within W (chainEdge (Fin.last k))) :
    (ring k).IsCycleWord (U + W + (hubWord true + hubWord false)) := by
  obtain ⟨pU, pW, hd⟩ := h
  have h1 := pU.add_pendant (joins_first true).symm (deg_hub hU true)
  have hd1 : (ring k).VertexDisjoint (U + unitWord (first true)) W :=
    VertexDisjoint.add_left hd ((ring k).vertexDisjoint_unitWord (joins_first true)
      (deg_hub hW true) (hd.deg_right_eq_zero pU.deg_right_pos)).symm
  have h2 := h1.glue pW.symm (joins_last true).symm hd1
  have h3 := h2.add_pendant (joins_last false) (by
    apply deg_add_eq_zero (deg_add_eq_zero (deg_add_eq_zero (deg_hub hU false) _)
      (deg_hub hW false))
    · exact (ring k).deg_unitWord_of_joins (joins_last true) (R_ne_H _ _ _).symm
        (H_ne (by decide))
    · exact (ring k).deg_unitWord_of_joins (joins_first true) (H_ne (by decide))
        (L_ne_H _ _ _).symm)
  have h4 := h3.add_closing (joins_first false).symm (by
    show U (first false) + unitWord (first true) (first false) + W (first false) +
      unitWord (last true) (first false) + unitWord (last false) (first false) = 0
    rw [chain_first hU false, chain_first hW false, unitWord_apply, unitWord_apply,
      unitWord_apply]
    simp [last, first])
  have heq : U + W + (hubWord true + hubWord false) =
      U + unitWord (first true) + W + unitWord (last true) + unitWord (last false) +
        unitWord (first false) := by
    unfold hubWord
    abel
  rw [heq]
  exact h4

/-- The tag of a word: its values at the two edges from the hubs to the first tile. -/
def tag (g : Edge k → Bit) : Bit × Bit := (g (first false), g (first true))

theorem tag_chain_add {X Z : Edge k → Bit} (h : Within X (chainEdge (Fin.last k))) :
    tag (X + Z) = tag Z := by
  show (X (first false) + Z (first false), X (first true) + Z (first true)) = _
  rw [chain_first h false, chain_first h true, zero_add, zero_add]
  rfl

theorem tag_hubWord_false : tag (hubWord false : Edge k → Bit) = (1, 0) := by
  show (hubWord false (first false), hubWord false (first true)) = _
  rw [hubWord_first, hubWord_first]
  simp

theorem tag_hubWord_true : tag (hubWord true : Edge k → Bit) = (0, 1) := by
  show (hubWord true (first false), hubWord true (first true)) = _
  rw [hubWord_first, hubWord_first]
  simp

theorem tag_hubWord_both : tag (hubWord true + hubWord false : Edge k → Bit) = (1, 1) := by
  show (hubWord true (first false) + hubWord false (first false),
    hubWord true (first true) + hubWord false (first true)) = _
  rw [hubWord_first, hubWord_first, hubWord_first, hubWord_first]
  simp

/-- **Cycles of the ring without the rung.** The cycles of the chain of all tiles, the cycles
through one hub, and the cycles through both hubs are different cycles. -/
theorem closing_cycles :
    Nat.card (CyclesIn (chainEdge (Fin.last k))) +
        Nat.card (PathsIn (chainEdge (Fin.last k)) (L 0 false) (R (Fin.last k) false)) +
        Nat.card (PathsIn (chainEdge (Fin.last k)) (L 0 true) (R (Fin.last k) true)) +
        (Nat.card ((ring k).PathPairsIn (chainEdge (Fin.last k)) (L 0 false)
            (R (Fin.last k) true) (L 0 true) (R (Fin.last k) (!true))) +
          Nat.card ((ring k).PathPairsIn (chainEdge (Fin.last k)) (L 0 false) (L 0 true)
            (R (Fin.last k) false) (R (Fin.last k) true))) ≤
      Nat.card (CyclesIn (noRung : Edge k → Prop)) := by
  rw [← Nat.card_sum
    (α := (ring k).PathPairsIn (chainEdge (Fin.last k)) (L 0 false) (R (Fin.last k) true)
      (L 0 true) (R (Fin.last k) (!true)))]
  have hex : ∀ e : Edge k, chainEdge (Fin.last k) e → ¬ offChain e := fun e he h => h he
  have hboth : Within (hubWord true + hubWord false : Edge k → Bit) offChain :=
    (within_hubWord true).add (within_hubWord false)
  have hbothR : Within (hubWord true + hubWord false : Edge k → Bit) noRung :=
    (within_hubWord_noRung true).add (within_hubWord_noRung false)
  obtain ⟨f₁, hf₁⟩ : ∃ f : CyclesIn (chainEdge (Fin.last k)) →
      CyclesIn (noRung : Edge k → Prop), ∀ a, (f a).1 = a.1 :=
    ⟨fun a => ⟨a.1, a.2.1, within_noRung a.2.2⟩, fun _ => rfl⟩
  have key : ∀ x : Bool, ∃ f : PathsIn (chainEdge (Fin.last k)) (L 0 x) (R (Fin.last k) x) →
      CyclesIn (noRung : Edge k → Prop), ∀ a, (f a).1 = a.1 + hubWord x := fun x =>
    ⟨fun a => ⟨a.1 + hubWord x, isCycleWord_hub x a.2.1 a.2.2,
      (within_noRung a.2.2).add (within_hubWord_noRung x)⟩, fun _ => rfl⟩
  obtain ⟨f₂, hf₂⟩ := key false
  obtain ⟨f₃, hf₃⟩ := key true
  obtain ⟨g₁, hg₁⟩ : ∃ f : (ring k).PathPairsIn (chainEdge (Fin.last k)) (L 0 false)
      (R (Fin.last k) true) (L 0 true) (R (Fin.last k) (!true)) →
      CyclesIn (noRung : Edge k → Prop),
      ∀ a, (f a).1 = a.1.1 + a.1.2 + (hubWord true + hubWord false) :=
    ⟨fun a => ⟨a.1.1 + a.1.2 + (hubWord true + hubWord false),
      isCycleWord_cross a.2.1 a.2.2.1 a.2.2.2,
      ((within_noRung a.2.2.1).add (within_noRung a.2.2.2)).add hbothR⟩, fun _ => rfl⟩
  obtain ⟨g₂, hg₂⟩ : ∃ f : (ring k).PathPairsIn (chainEdge (Fin.last k)) (L 0 false) (L 0 true)
      (R (Fin.last k) false) (R (Fin.last k) true) → CyclesIn (noRung : Edge k → Prop),
      ∀ a, (f a).1 = a.1.1 + a.1.2 + (hubWord true + hubWord false) :=
    ⟨fun a => ⟨a.1.1 + a.1.2 + (hubWord true + hubWord false),
      isCycleWord_ends a.2.1 a.2.2.1 a.2.2.2,
      ((within_noRung a.2.2.1).add (within_noRung a.2.2.2)).add hbothR⟩, fun _ => rfl⟩
  have hinj₂ : ∀ (x : Bool) (f : PathsIn (chainEdge (Fin.last k)) (L 0 x) (R (Fin.last k) x) →
      CyclesIn (noRung : Edge k → Prop)), (∀ a, (f a).1 = a.1 + hubWord x) →
      Function.Injective f := by
    intro x f hf a b hab
    have h := congrArg Subtype.val hab
    rw [hf, hf] at h
    exact Subtype.ext
      (parts_eq_two hex a.2.2 (within_hubWord x) b.2.2 (within_hubWord x) h).1
  refine natCard_four_le (fun g : CyclesIn (noRung : Edge k → Prop) => tag g.1) f₁ f₂ f₃
    (Sum.elim g₁ g₂) ?_ (hinj₂ false f₂ hf₂) (hinj₂ true f₃ hf₃) ?_ (t₁ := (0, 0))
    (t₂ := (1, 0)) (t₃ := (0, 1)) (t₄ := (1, 1)) ?_ ?_ ?_ ?_ (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide)
  · intro a b hab
    have h := congrArg Subtype.val hab
    rw [hf₁, hf₁] at h
    exact Subtype.ext h
  · -- the two kinds of cycles through both hubs
    rintro (a | a) (b | b) hab
    · have h := congrArg Subtype.val hab
      have h' : (g₁ a).1 = (g₁ b).1 := h
      rw [hg₁, hg₁] at h'
      have k1 := (parts_eq_two hex (a.2.2.1.add a.2.2.2) hboth (b.2.2.1.add b.2.2.2) hboth h').1
      obtain ⟨k3, k4⟩ := a.2.1.eq_of_add_eq b.2.1 k1
      exact congrArg Sum.inl (Subtype.ext (Prod.ext k3 k4))
    · exfalso
      have h := congrArg Subtype.val hab
      have h' : (g₁ a).1 = (g₂ b).1 := h
      rw [hg₁, hg₂] at h'
      have k1 := (parts_eq_two hex (a.2.2.1.add a.2.2.2) hboth (b.2.2.1.add b.2.2.2) hboth h').1
      exact a.2.1.false_of_add_eq b.2.1 k1 a.2.1.2.1.deg_left_pos
    · exfalso
      have h := congrArg Subtype.val hab
      have h' : (g₂ a).1 = (g₁ b).1 := h
      rw [hg₂, hg₁] at h'
      have k1 := (parts_eq_two hex (a.2.2.1.add a.2.2.2) hboth (b.2.2.1.add b.2.2.2) hboth h').1
      exact b.2.1.false_of_add_eq a.2.1 k1.symm b.2.1.2.1.deg_left_pos
    · have h := congrArg Subtype.val hab
      have h' : (g₂ a).1 = (g₂ b).1 := h
      rw [hg₂, hg₂] at h'
      have k1 := (parts_eq_two hex (a.2.2.1.add a.2.2.2) hboth (b.2.2.1.add b.2.2.2) hboth h').1
      obtain ⟨k3, k4⟩ := a.2.1.eq_of_add_eq b.2.1 k1
      exact congrArg Sum.inr (Subtype.ext (Prod.ext k3 k4))
  · intro a
    show tag (f₁ a).1 = (0, 0)
    rw [hf₁]
    show (a.1 (first false), a.1 (first true)) = (0, 0)
    rw [chain_first a.2.2 false, chain_first a.2.2 true]
  · intro a
    show tag (f₂ a).1 = (1, 0)
    rw [hf₂, tag_chain_add a.2.2, tag_hubWord_false]
  · intro a
    show tag (f₃ a).1 = (0, 1)
    rw [hf₃, tag_chain_add a.2.2, tag_hubWord_true]
  · rintro (a | a)
    · show tag (g₁ a).1 = (1, 1)
      rw [hg₁, tag_chain_add (a.2.2.1.add a.2.2.2), tag_hubWord_both]
    · show tag (g₂ a).1 = (1, 1)
      rw [hg₂, tag_chain_add (a.2.2.1.add a.2.2.2), tag_hubWord_both]

/-! ### Paths between the two hubs -/

/-- A path of the chain, continued at both ends by an edge to a hub. -/
theorem isPathWord_hubs {s t : Vertex k} {e₁ e₂ : Edge k} {x₁ x₂ : Bool} {X : (ring k).Word}
    (hX : (ring k).IsPathWord s t X) (hin : Within X (chainEdge (Fin.last k)))
    (he₁ : (ring k).Joins e₁ s (H x₁)) (he₂ : (ring k).Joins e₂ t (H x₂)) (hx : x₁ ≠ x₂) :
    (ring k).IsPathWord (H x₁) (H x₂) (X + (unitWord e₂ + unitWord e₁)) := by
  have ht : (H x₁ : Vertex k) ≠ t := by
    intro h
    have h1 := hX.2.2.1
    rw [← h, deg_hub hin x₁] at h1
    omega
  have h1 := hX.add_pendant he₂ (deg_hub hin x₂)
  have h2 := h1.symm.add_pendant he₁ (by
    apply deg_add_eq_zero (deg_hub hin x₁)
    exact (ring k).deg_unitWord_of_joins he₂ ht (H_ne hx))
  have heq : X + (unitWord e₂ + unitWord e₁) = X + unitWord e₂ + unitWord e₁ := by abel
  rw [heq]
  -- `h2` is a path from `H x₂` to `H x₁`
  exact h2.symm

/-- **Paths between the two hubs in the ring without the rung.** A path of the chain between two
of its four end vertices, one at each hub, gives a path between the hubs. -/
theorem closing_paths :
    Nat.card (PathsIn (chainEdge (Fin.last k)) (L 0 false) (L 0 true)) +
        Nat.card (PathsIn (chainEdge (Fin.last k)) (R (Fin.last k) false)
          (R (Fin.last k) true)) +
        Nat.card (PathsIn (chainEdge (Fin.last k)) (L 0 false) (R (Fin.last k) true)) +
        Nat.card (PathsIn (chainEdge (Fin.last k)) (L 0 true) (R (Fin.last k) false)) ≤
      Nat.card (PathsIn (noRung : Edge k → Prop) (H false) (H true)) := by
  have hex : ∀ e : Edge k, chainEdge (Fin.last k) e → ¬ offChain e := fun e he h => h he
  have hb : false ≠ true := by decide
  -- one family: paths of the chain from `s` to `t`, with the fixed edges `e₁`, `e₂`
  have fam : ∀ (s t : Vertex k) (Z : Edge k → Bit), Within Z offChain → Within Z noRung →
      (∀ X : (ring k).Word, (ring k).IsPathWord s t X → Within X (chainEdge (Fin.last k)) →
        (ring k).IsPathWord (H false) (H true) (X + Z)) →
      ∃ f : PathsIn (chainEdge (Fin.last k)) s t → PathsIn (noRung : Edge k → Prop) (H false)
        (H true), Function.Injective f ∧ ∀ a, tag (f a).1 = tag Z := by
    intro s t Z hZ hZR hpath
    refine ⟨fun a => ⟨a.1 + Z, hpath a.1 a.2.1 a.2.2, (within_noRung a.2.2).add hZR⟩, ?_, ?_⟩
    · intro a b hab
      have h := congrArg Subtype.val hab
      have h' : a.1 + Z = b.1 + Z := h
      exact Subtype.ext (add_right_cancel h')
    · intro a
      exact tag_chain_add a.2.2
  -- the four families
  obtain ⟨f₁, i₁, t₁⟩ := fam (L 0 false) (L 0 true) (unitWord (first true) + unitWord (first false))
    ((within_unitWord (offChain_first _)).add (within_unitWord (offChain_first _)))
    ((within_unitWord (noRung_first _)).add (within_unitWord (noRung_first _)))
    (fun X hX hin => isPathWord_hubs hX hin (joins_first false).symm (joins_first true).symm hb)
  obtain ⟨f₂, i₂, t₂⟩ := fam (R (Fin.last k) false) (R (Fin.last k) true)
    (unitWord (last true) + unitWord (last false))
    ((within_unitWord (offChain_last _)).add (within_unitWord (offChain_last _)))
    ((within_unitWord (noRung_last _)).add (within_unitWord (noRung_last _)))
    (fun X hX hin => isPathWord_hubs hX hin (joins_last false) (joins_last true) hb)
  obtain ⟨f₃, i₃, t₃⟩ := fam (L 0 false) (R (Fin.last k) true)
    (unitWord (last true) + unitWord (first false))
    ((within_unitWord (offChain_last _)).add (within_unitWord (offChain_first _)))
    ((within_unitWord (noRung_last _)).add (within_unitWord (noRung_first _)))
    (fun X hX hin => isPathWord_hubs hX hin (joins_first false).symm (joins_last true) hb)
  obtain ⟨f₄, i₄, t₄⟩ := fam (L 0 true) (R (Fin.last k) false)
    (unitWord (first true) + unitWord (last false))
    ((within_unitWord (offChain_first _)).add (within_unitWord (offChain_last _)))
    ((within_unitWord (noRung_first _)).add (within_unitWord (noRung_last _)))
    (fun X hX hin =>
      isPathWord_hubs hX.symm hin (joins_last false) (joins_first true).symm hb)
  refine natCard_four_le (fun g : PathsIn (noRung : Edge k → Prop) (H false) (H true) => tag g.1)
    f₁ f₂ f₃ f₄ i₁ i₂ i₃ i₄ (t₁ := (1, 1)) (t₂ := (0, 0)) (t₃ := (1, 0)) (t₄ := (0, 1))
    ?_ ?_ ?_ ?_ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
  · intro a
    show tag (f₁ a).1 = (1, 1)
    rw [t₁ a]
    simp [tag, unitWord_apply, first]
  · intro a
    show tag (f₂ a).1 = (0, 0)
    rw [t₂ a]
    simp [tag, unitWord_apply, first, last]
  · intro a
    show tag (f₃ a).1 = (1, 0)
    rw [t₃ a]
    simp [tag, unitWord_apply, first, last]
  · intro a
    show tag (f₄ a).1 = (0, 1)
    rw [t₄ a]
    simp [tag, unitWord_apply, first, last]

/-! ### The rung -/

/-- **Cycles of the ring with the rung.** A cycle without the rung and a path between the hubs
without the rung, closed by the rung, are different cycles. -/
theorem rung_cycles :
    Nat.card (CyclesIn (noRung : Edge k → Prop)) +
        Nat.card (PathsIn (noRung : Edge k → Prop) (H false) (H true)) ≤
      (ring k).numCycles := by
  have hr : ∀ X : Edge k → Bit, Within X noRung → X rung = 0 :=
    fun X hX => hX.eq_zero (fun h => h rfl)
  obtain ⟨f₁, hf₁⟩ : ∃ f : CyclesIn (noRung : Edge k → Prop) →
      {x : (ring k).Word // (ring k).IsCycleWord x}, ∀ a, (f a).1 = a.1 :=
    ⟨fun a => ⟨a.1, a.2.1⟩, fun _ => rfl⟩
  obtain ⟨f₂, hf₂⟩ : ∃ f : PathsIn (noRung : Edge k → Prop) (H false) (H true) →
      {x : (ring k).Word // (ring k).IsCycleWord x}, ∀ a, (f a).1 = a.1 + unitWord rung :=
    ⟨fun a => ⟨a.1 + unitWord rung, a.2.1.add_closing joins_rung (hr a.1 a.2.2)⟩, fun _ => rfl⟩
  unfold Network.numCycles
  apply natCard_add_le f₁ f₂
  · intro a b hab
    have h := congrArg Subtype.val hab
    rw [hf₁, hf₁] at h
    exact Subtype.ext h
  · intro a b hab
    have h := congrArg Subtype.val hab
    rw [hf₂, hf₂] at h
    exact Subtype.ext (add_right_cancel h)
  · intro a b hab
    have h := congrArg Subtype.val hab
    rw [hf₁, hf₂] at h
    have h1 := congrFun h rung
    have h2 : (b.1 + unitWord rung : Edge k → Bit) rung = 1 := by
      show b.1 rung + unitWord rung rung = 1
      rw [hr b.1 b.2.2, unitWord_self, zero_add]
    rw [hr a.1 a.2.2, h2] at h1
    exact zero_ne_one h1

/-! ### The numbers -/

/-- The ring without the rung has at least this number of cycles. -/
theorem numCyclesNoRung_ge (k : ℕ) :
    2 ^ (2 * k + 2) + 2 ^ k + kappa k + gamma k ≤
      Nat.card (CyclesIn (noRung : Edge k → Prop)) := by
  have hb := chainBounds (Fin.last k)
  have h1 := closing_cycles (k := k)
  have hA1 := hb.paths false false
  have hA2 := hb.paths true true
  have hM := hb.pairs true
  have hG := hb.ends
  have hC := hb.cycles
  simp only [Fin.val_last] at hA1 hA2 hM hG hC
  have e1 : 2 ^ (2 * k + 2) = 2 ^ (2 * k + 1) + 2 ^ (2 * k + 1) := by ring
  rw [e1]
  omega

/-- In the ring without the rung, the number of paths between the hubs is at least this
number. -/
theorem numPathsHubs_ge (k : ℕ) :
    2 ^ (2 * k + 2) + 2 ^ (k + 3) ≤
      Nat.card (PathsIn (noRung : Edge k → Prop) (H false) (H true)) + 4 := by
  have hb := chainBounds (Fin.last k)
  have h1 := closing_paths (k := k)
  have hU := hb.left
  have hW := hb.right
  have hA1 := hb.paths false true
  have hA2 := hb.paths true false
  simp only [Fin.val_last] at hU hW hA1 hA2
  have e1 : 2 ^ (2 * k + 2) = 2 ^ (2 * k + 1) + 2 ^ (2 * k + 1) := by ring
  have e2 : 2 ^ (k + 3) = 2 ^ (k + 2) + 2 ^ (k + 2) := by ring
  rw [e1, e2]
  omega

/-- **The ring without the rung has at least `H(2k+3)` cycles.** -/
theorem horakKim_le_numCyclesNoRung (k : ℕ) :
    horakKim (2 * (k + 1) + 1) ≤ Nat.card (CyclesIn (noRung : Edge k → Prop)) := by
  have h1 := numCyclesNoRung_ge k
  have h2 := horakKim_odd (k + 1) (by omega)
  have h3 := gamma_add k
  have h4 := kappa_add k
  have e1 : 2 ^ (2 * (k + 1)) = 2 ^ (2 * k + 2) := by ring_nf
  have e2 : (4 * (k + 1) + 1) * 2 ^ (k + 1 - 1) = 4 * (k * 2 ^ k) + 5 * 2 ^ k := by
    rw [Nat.add_sub_cancel]
    ring
  have e3 : 2 ^ (k + 3) = 8 * 2 ^ k := by ring
  have e4 : 2 ^ (k + 2) = 4 * 2 ^ k := by ring
  have e5 : k * 2 ^ (k + 2) = 4 * (k * 2 ^ k) := by ring
  rw [e1, e2] at h2
  rw [e5, e4] at h3
  rw [e3] at h4
  omega

/-- **The ring with the rung has at least `H(2k+4)` cycles.** -/
theorem horakKim_le_numCycles_ring (k : ℕ) :
    horakKim (2 * (k + 1) + 2) ≤ (ring k).numCycles := by
  have h0 := rung_cycles (k := k)
  have h1 := numCyclesNoRung_ge k
  have h1' := numPathsHubs_ge k
  have h2 := horakKim_even (k + 1) (by omega)
  have h3 := gamma_add k
  have h4 := kappa_add k
  have e1 : 2 ^ (2 * (k + 1) + 1) = 2 * 2 ^ (2 * k + 2) := by ring
  have e2 : (4 * (k + 1) + 9) * 2 ^ (k + 1 - 1) = 4 * (k * 2 ^ k) + 13 * 2 ^ k := by
    rw [Nat.add_sub_cancel]
    ring
  have e3 : 2 ^ (k + 3) = 8 * 2 ^ k := by ring
  have e4 : 2 ^ (k + 2) = 4 * 2 ^ k := by ring
  have e5 : k * 2 ^ (k + 2) = 4 * (k * 2 ^ k) := by ring
  rw [e1, e2] at h2
  rw [e5, e4] at h3
  rw [e3] at h4 h1'
  omega

end Erdos1016.ExactMaximum.Ring
