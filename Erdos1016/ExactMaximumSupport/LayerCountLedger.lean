import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Tactic

set_option autoImplicit false

/-!
# Finite counting for thin layers

Each inner layer has at least two vertices. A thicker layer has at most
three times as many vertices as its excess over two.
-/

noncomputable section
open scoped BigOperators
namespace Erdos1016.ExactMaximumSupport.LayerCountLedger

local instance layerCountDecidable (p : Prop) : Decidable p := Classical.propDecidable p

variable {V : Type*} [Fintype V] (level : V → ℕ) (ell : ℕ)

def layer (j : ℕ) : Finset V := Finset.univ.filter fun v => level v = j

def Thin (j : ℕ) : Prop := 0 < j ∧ j < ell ∧ (layer level j).card = 2

def exceptional : Finset V := Finset.univ.filter fun v => ¬ Thin level ell (level v)

/-- The finite layer decomposition counts each vertex exactly once. -/
theorem sum_layer_card :
    ∑ j ∈ Finset.univ.image level, (layer level j).card = Fintype.card V := by
  simpa only [layer, Finset.card_univ] using
    (Finset.card_eq_sum_card_image level (Finset.univ : Finset V)).symm

/-- A condition on the level can be counted one finite fiber at a time. -/
theorem card_filter_eq_sum_layers (p : ℕ → Prop) :
    (Finset.univ.filter fun v => p (level v)).card =
      ∑ j ∈ Finset.univ.image level, if p j then (layer level j).card else 0 := by
  have h := Finset.sum_card_fiberwise_eq_card_filter (Finset.univ : Finset V)
    ((Finset.univ.image level).filter p) level
  have hfilter :
      (Finset.univ.filter fun v => level v ∈ (Finset.univ.image level).filter p) =
        Finset.univ.filter (fun v => p (level v)) := by
    ext v
    have hv : level v ∈ Finset.univ.image level :=
      Finset.mem_image_of_mem level (Finset.mem_univ v)
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, hv]
  rw [hfilter, Finset.sum_filter] at h
  exact h.symm

theorem card_filter_not_eq_sum_layers (p : ℕ → Prop) :
    (Finset.univ.filter fun v => ¬ p (level v)).card =
      ∑ j ∈ Finset.univ.image level, if p j then 0 else (layer level j).card := by
  calc
    _ = ∑ j ∈ Finset.univ.image level, if ¬ p j then (layer level j).card else 0 := by
      convert card_filter_eq_sum_layers level (fun j => ¬ p j) using 1 <;> congr 1
      · ext v
        simp only [Finset.mem_filter]
      · funext j
        by_cases hj : p j <;>
          simp only [hj, not_true_eq_false, not_false_eq_true, ite_true, ite_false]
    _ = _ := by
      apply Finset.sum_congr rfl
      intro j _
      by_cases hj : p j <;> simp only [hj, not_true_eq_false, not_false_eq_true, ite_true, ite_false]

/-- Exceptional vertices and the baseline inner layers fit in three times the total order. -/
theorem exceptional_card_add_baseline_le
    (hlower : ∀ j, 0 < j → j < ell → 2 ≤ (layer level j).card) :
    (exceptional level ell).card + 6 * (ell - 1) ≤ 3 * Fintype.card V := by
  let T := Finset.univ.image level
  have hinner : T.filter (fun j => 0 < j ∧ j < ell) = Finset.Ioo 0 ell := by
    ext j
    simp only [Finset.mem_filter, Finset.mem_Ioo]
    constructor
    · exact fun h => h.2
    · intro hj
      have hp : 0 < (layer level j).card := by
        have := hlower j hj.1 hj.2
        omega
      obtain ⟨v,hv⟩ := Finset.card_pos.mp hp
      exact ⟨Finset.mem_image.mpr ⟨v,Finset.mem_univ _,(Finset.mem_filter.mp hv).2⟩,hj⟩
  have hbase : (∑ j ∈ T, if 0 < j ∧ j < ell then 1 else 0) = ell - 1 := by
    rw [← Finset.sum_filter, Finset.sum_const, hinner]
    simp
  have hbad : (∑ j ∈ T, if Thin level ell j then 0 else (layer level j).card) =
      (exceptional level ell).card := by
    exact (card_filter_not_eq_sum_layers level (Thin level ell)).symm
  have hpoint (j : ℕ) :
      (if Thin level ell j then 0 else (layer level j).card) +
        6 * (if 0 < j ∧ j < ell then 1 else 0) ≤ 3 * (layer level j).card := by
    by_cases hj : 0 < j ∧ j < ell
    · have hc := hlower j hj.1 hj.2
      by_cases heq : (layer level j).card = 2
      · simp [Thin, hj.1, hj.2, heq]
      · have hn : ¬ Thin level ell j := fun h => heq h.2.2
        simp only [if_neg hn, if_pos hj]
        omega
    · have hn : ¬ Thin level ell j := fun h => hj ⟨h.1,h.2.1⟩
      simp only [if_neg hn, if_neg hj, Nat.mul_zero, Nat.add_zero]
      omega
  have hsum := Finset.sum_le_sum (fun j (_ : j ∈ T) => hpoint j)
  rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum,
    hbad, hbase] at hsum
  simpa only [T, sum_layer_card] using hsum

/-- A bounded excess over the two-per-inner-layer baseline bounds exceptional vertices. -/
theorem exceptional_card_le (C : ℕ)
    (hlower : ∀ j, 0 < j → j < ell → 2 ≤ (layer level j).card)
    (horder : Fintype.card V ≤ 2 * (ell + C)) :
    (exceptional level ell).card ≤ 6 * C + 6 := by
  have h := exceptional_card_add_baseline_le level ell hlower
  omega

/-- The same baseline bounds the distance between the two poles. -/
theorem ell_le_rank_add_one (b : ℕ)
    (hlower : ∀ j, 0 < j → j < ell → 2 ≤ (layer level j).card)
    (horder : Fintype.card V = 2 * b) : ell ≤ b + 1 := by
  have h := exceptional_card_add_baseline_le level ell hlower
  omega

/-- Distinct attained levels beyond the inner interval require distinct exceptional vertices. -/
theorem level_le_ell_add_exceptional (v : V)
    (hlevels : ∀ j, j ≤ level v → ∃ w : V, level w = j) :
    level v ≤ ell + (exceptional level ell).card := by
  by_cases hv : level v < ell
  · omega
  let I := Finset.Icc ell (level v)
  have hex (j : I) : ∃ w : V, level w = j.val :=
    hlevels j.val (Finset.mem_Icc.mp j.property).2
  choose f hf using hex
  have hmem (j : I) : f j ∈ exceptional level ell := by
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ _,?_⟩
    intro hthin
    have hlo := (Finset.mem_Icc.mp j.property).1
    rw [hf j] at hthin
    exact (Nat.not_lt_of_ge hlo) hthin.2.1
  let pick : I → exceptional level ell := fun j => ⟨f j,hmem j⟩
  have hinj : Function.Injective pick := by
    intro i j hij
    have h := congrArg (fun x : exceptional level ell => level x.val) hij
    change level (f i) = level (f j) at h
    rw [hf i, hf j] at h
    exact Subtype.ext h
  have hc := Fintype.card_le_of_injective pick hinj
  have hbound : level v + 1 - ell ≤ (exceptional level ell).card := by
    simpa only [I, Fintype.card_coe, Nat.card_Icc] using hc
  omega

/-- Each nonordinary thin layer can be charged to a vertex of a prescribed exceptional set. -/
theorem nonordinary_card_le (ordinary : ℕ → Prop) (bad : Finset V)
    (hbad : ∀ j, Thin level ell j → ¬ ordinary j → ∃ v ∈ bad, level v = j) :
    (Finset.univ.filter fun v => ¬ ordinary (level v)).card ≤
      (exceptional level ell).card + 2 * bad.card := by
  let T := Finset.univ.image level
  have hpoint (j : ℕ) :
      (if ordinary j then 0 else (layer level j).card) ≤
        (if Thin level ell j then 0 else (layer level j).card) +
          2 * (if j ∈ bad.image level then 1 else 0) := by
    by_cases ht : Thin level ell j
    · by_cases ho : ordinary j
      · simp only [if_pos ho, if_pos ht, Nat.zero_add]
        exact Nat.zero_le _
      · obtain ⟨v,hv,hvj⟩ := hbad j ht ho
        have hj : j ∈ bad.image level := Finset.mem_image.mpr ⟨v,hv,hvj⟩
        simp only [if_neg ho, if_pos ht, if_pos hj, ht.2.2]
        decide
    · simp only [if_neg ht]
      by_cases ho : ordinary j
      · rw [if_pos ho]
        exact Nat.zero_le _
      · rw [if_neg ho]
        omega
  have hsum := Finset.sum_le_sum (fun j (_ : j ∈ T) => hpoint j)
  have hleft : (∑ j ∈ T, if ordinary j then 0 else (layer level j).card) =
      (Finset.univ.filter fun v => ¬ ordinary (level v)).card := by
    exact (card_filter_not_eq_sum_layers level ordinary).symm
  have hright : (∑ j ∈ T, if Thin level ell j then 0 else (layer level j).card) =
      (exceptional level ell).card := by
    exact (card_filter_not_eq_sum_layers level (Thin level ell)).symm
  have hindices : (∑ j ∈ T, if j ∈ bad.image level then 1 else 0) ≤ bad.card := by
    have hs : T.filter (fun j => j ∈ bad.image level) ⊆ bad.image level :=
      fun j hj => (Finset.mem_filter.mp hj).2
    have hc := (Finset.card_le_card hs).trans (Finset.card_image_le)
    simpa only [Finset.card_filter] using hc
  rw [Finset.sum_add_distrib, ← Finset.mul_sum, hleft, hright] at hsum
  omega

end Erdos1016.ExactMaximumSupport.LayerCountLedger
