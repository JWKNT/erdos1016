import Mathlib.Order.Fin.Basic
import Mathlib.Order.RelClasses
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Data.Finset.Sort
import Erdos1016.PolynomialBound.Separation

set_option autoImplicit false

/-!
# A chain of separators and its blocks

A finite family of pairwise disjoint connected separators of `u` from `p` is
linearly ordered by `Separation.Before`. This file enumerates the family in
that order and cuts the chain into blocks.

* `SeparatorFamily`: the hypotheses on the family.
* `exists_chain`: an enumeration `e : Fin T → κ` of the family with
  `Before (C (e a)) (C (e b))` for `a < b`.
* `exists_blocks`: for `m * q < T` there are `m` pairwise disjoint blocks.
  Block `l` lies strictly between the separators number `l * q` and
  `(l + 1) * q`. It contains the `q - 1` separators between them. Every edge
  that leaves it ends in one of its two end separators.
-/

namespace Erdos1016.PolynomialBound.Separation

open SimpleGraph

variable {V : Type*} {G : SimpleGraph V} {κ : Type*}

/-- A separator of two joined vertices is not empty. -/
theorem Separates.nonempty {X : Set V} {u p : V} (h : Separates G X u p)
    (hup : G.Reachable u p) : X.Nonempty := by
  obtain ⟨_, x, _, _, hx⟩ := h.exists_frontier hup
  exact ⟨x, hx⟩

/-- No separator comes before itself. -/
theorem not_before_self {X : Set V} {u p : V} (h : Separates G X u p)
    (hup : G.Reachable u p) : ¬ Before G u X X := by
  intro hb
  obtain ⟨x, hx⟩ := h.nonempty hup
  exact AvoidReach.right_not_mem (hb hx) hx

/-- A connected set that is disjoint from the two ends of a block and meets
the block lies in the block. -/
theorem IsConnectedSet.subset_block {Y C₁ C₂ : Set V} {u : V}
    (hY : IsConnectedSet G Y) (h1 : Disjoint Y C₁) (h2 : Disjoint Y C₂)
    {x : V} (hx : x ∈ Y) (hxB : x ∈ block G u C₁ C₂) : Y ⊆ block G u C₁ C₂ := by
  intro y hy
  refine ⟨AvoidReach.trans hxB.1 (hY.avoidReach h2 hx hy), ?_⟩
  rintro (h | h)
  · exact hxB.2 (Or.inl (AvoidReach.trans h (hY.avoidReach h1 hy hx)))
  · exact Set.disjoint_left.mp h1 hy h

/-- A block does not meet its far end. -/
theorem block_disjoint_right (u : V) (C₁ C₂ : Set V) : Disjoint (block G u C₁ C₂) C₂ :=
  Set.disjoint_left.mpr fun _ hx hx2 => AvoidReach.right_not_mem hx.1 hx2

/-- A block does not meet its near end. -/
theorem block_disjoint_left (u : V) (C₁ C₂ : Set V) : Disjoint (block G u C₁ C₂) C₁ :=
  Set.disjoint_left.mpr fun _ hx hx1 => hx.2 (Or.inr hx1)

/-- A finite family of pairwise disjoint connected separators of `u` from `p`. -/
structure SeparatorFamily (G : SimpleGraph V) (u p : V) (F : Finset κ) (C : κ → Set V) :
    Prop where
  reach : G.Reachable u p
  sep : ∀ k ∈ F, Separates G (C k) u p
  conn : ∀ k ∈ F, IsConnectedSet G (C k)
  disj : ∀ k ∈ F, ∀ l ∈ F, k ≠ l → Disjoint (C k) (C l)

namespace SeparatorFamily

variable {u p : V} {F : Finset κ} {C : κ → Set V}

/-- The family is enumerated in the order of the separators. -/
theorem exists_chain (h : SeparatorFamily G u p F C) :
    ∃ e : Fin F.card → κ, Function.Injective e ∧ (∀ a, e a ∈ F) ∧
      ∀ a b : Fin F.card, a < b → Before G u (C (e a)) (C (e b)) := by
  classical
  let r : F → F → Prop := fun a b => Before G u (C a.1) (C b.1)
  haveI : IsStrictTotalOrder F r :=
    { trichotomous := by
        intro a b
        by_cases hab : a = b
        · exact Or.inr (Or.inl hab)
        · rcases before_total h.reach (h.sep a.1 a.2) (h.conn a.1 a.2) (h.sep b.1 b.2)
            (h.conn b.1 b.2) (h.disj a.1 a.2 b.1 b.2 fun hv => hab (Subtype.ext hv)) with hb | hb
          · exact Or.inl hb
          · exact Or.inr (Or.inr hb)
      irrefl := fun a => not_before_self (h.sep a.1 a.2) h.reach
      trans := by
        intro a b c hab hbc
        by_cases hbc' : b = c
        · subst hbc'
          exact hab
        · exact before_trans h.reach (h.sep b.1 b.2) (h.conn b.1 b.2)
            (h.sep c.1 c.2) (h.conn c.1 c.2)
            (h.disj b.1 b.2 c.1 c.2 fun hv => hbc' (Subtype.ext hv)) hab hbc }
  letI : LinearOrder F := linearOrderOfSTO r
  have hcard : (Finset.univ : Finset F).card = F.card := by simp
  let e := (Finset.univ : Finset F).orderEmbOfFin hcard
  refine ⟨fun a => (e a).1, ?_, fun a => (e a).2, ?_⟩
  · intro a b hab
    exact e.injective (Subtype.ext hab)
  · intro a b hab
    have hlt : e a < e b := e.strictMono hab
    exact hlt

/-- In an ordered enumeration the side of `u` grows. -/
theorem side_subset_of_le (h : SeparatorFamily G u p F C) (e : Fin F.card → κ)
    (hinj : Function.Injective e) (hmem : ∀ a, e a ∈ F)
    (hord : ∀ a b : Fin F.card, a < b → Before G u (C (e a)) (C (e b)))
    {a b : Fin F.card} (hab : a ≤ b) : side G (C (e a)) u ⊆ side G (C (e b)) u := by
  rcases hab.eq_or_lt with rfl | hlt
  · exact subset_rfl
  · exact side_subset_side_of_before h.reach (h.sep _ (hmem a)) (h.conn _ (hmem a))
      (h.sep _ (hmem b)) (h.conn _ (hmem b))
      (h.disj _ (hmem a) _ (hmem b) fun hv => hlt.ne (hinj hv)) (hord a b hlt)

/-- **Blocks.** If `m * q < T`, the chain has `m` pairwise disjoint blocks.
Block `l` lies between the separators `lo l` and `hi l`, contains `q - 1`
separators of the family, and every edge that leaves it ends in `C (lo l)` or
in `C (hi l)`. -/
theorem exists_blocks (h : SeparatorFamily G u p F C) (q m : ℕ) (hm : m * q < F.card) :
    ∃ (lo hi : Fin m → κ) (inner : Fin m → Finset κ),
      (∀ l, lo l ∈ F ∧ hi l ∈ F) ∧
      (∀ l l', l ≠ l' →
        Disjoint (block G u (C (lo l)) (C (hi l))) (block G u (C (lo l')) (C (hi l')))) ∧
      (∀ l, inner l ⊆ F ∧ (inner l).card = q - 1 ∧
        ∀ k ∈ inner l, C k ⊆ block G u (C (lo l)) (C (hi l))) := by
  classical
  obtain ⟨e, hinj, hmem, hord⟩ := h.exists_chain
  have hidx (l : Fin m) : l.1 * q < F.card ∧ (l.1 + 1) * q < F.card := by
    have h1 : (l.1 + 1) * q ≤ m * q := Nat.mul_le_mul_right q l.2
    have h2 : l.1 * q ≤ (l.1 + 1) * q := Nat.mul_le_mul_right q (Nat.le_succ _)
    omega
  let lo : Fin m → κ := fun l => e ⟨l.1 * q, (hidx l).1⟩
  let hi : Fin m → κ := fun l => e ⟨(l.1 + 1) * q, (hidx l).2⟩
  let idx : Fin m → Finset (Fin F.card) := fun l =>
    Finset.univ.filter fun a : Fin F.card => l.1 * q < a.1 ∧ a.1 < (l.1 + 1) * q
  refine ⟨lo, hi, fun l => (idx l).image e, fun l => ⟨hmem _, hmem _⟩, ?_, ?_⟩
  · -- two different blocks are disjoint
    have key (l l' : Fin m) (hll : l.1 < l'.1) :
        Disjoint (block G u (C (lo l)) (C (hi l))) (block G u (C (lo l')) (C (hi l'))) := by
      have hle : (⟨(l.1 + 1) * q, (hidx l).2⟩ : Fin F.card) ≤ ⟨l'.1 * q, (hidx l').1⟩ := by
        change (l.1 + 1) * q ≤ l'.1 * q
        exact Nat.mul_le_mul_right q hll
      have hsides := h.side_subset_of_le e hinj hmem hord hle
      exact Set.disjoint_left.mpr fun x hx hx' => (block_not_adj hsides hx hx').1 rfl
    intro l l' hne
    rcases lt_or_gt_of_ne (fun hv => hne (Fin.ext hv) : l.1 ≠ l'.1) with hlt | hgt
    · exact key l l' hlt
    · exact (key l' l hgt).symm
  · intro l
    refine ⟨?_, ?_, ?_⟩
    · intro k hk
      obtain ⟨a, _, rfl⟩ := Finset.mem_image.mp hk
      exact hmem a
    · rw [Finset.card_image_of_injective _ hinj]
      -- the indices strictly between `l * q` and `(l + 1) * q`
      have hmap : (idx l).map Fin.valEmbedding = Finset.Ioo (l.1 * q) ((l.1 + 1) * q) := by
        ext n
        simp only [idx, Finset.mem_map, Finset.mem_filter, Finset.mem_univ, true_and,
          Fin.valEmbedding_apply, Finset.mem_Ioo]
        constructor
        · rintro ⟨a, ha, rfl⟩
          exact ha
        · intro hn
          exact ⟨⟨n, lt_trans hn.2 (hidx l).2⟩, hn, rfl⟩
      have hc := congrArg Finset.card hmap
      rw [Finset.card_map, Nat.card_Ioo] at hc
      rw [hc]
      have hsucc : (l.1 + 1) * q = l.1 * q + q := Nat.succ_mul l.1 q
      omega
    · intro k hk
      obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hk
      have ha' := (Finset.mem_filter.mp ha).2
      have hlo : (⟨l.1 * q, (hidx l).1⟩ : Fin F.card) < a := ha'.1
      have hhi : a < (⟨(l.1 + 1) * q, (hidx l).2⟩ : Fin F.card) := ha'.2
      exact subset_block h.reach (h.sep _ (hmem _)) (h.conn _ (hmem _))
        (h.sep _ (hmem a)) (h.conn _ (hmem a))
        (h.disj _ (hmem _) _ (hmem a) fun hv => hlo.ne (hinj hv))
        (hord _ _ hlo) (hord _ _ hhi)

end SeparatorFamily

end Erdos1016.PolynomialBound.Separation
