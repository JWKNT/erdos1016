import Erdos1016.ExactMaximumSupport.PolePathRank
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Order.Interval.Finset.Nat

set_option autoImplicit false

/-!
# Order accounted for by ordinary layers

Each ordinary layer lies strictly between the ports and has exactly two
vertices. Thus the ordinary vertices occupy at most twice the number of
interior levels. The actual two-pole order identity converts this count into
a bound on rank by terminal distance and the number of nonordinary vertices.
-/
noncomputable section
open scoped BigOperators
namespace Erdos1016.ExactMaximumSupport.OrdinaryLayerOrder

open BoundaryTrace BoundaryTrace.Network BoundaryDecay
local instance ordinaryOrderDecidable (p : Prop) : Decidable p := Classical.propDecidable p

variable {V E : Type*} [Fintype V] [Fintype E] (N : Network V E) (s t : V)

omit [Fintype E] in
/-- Ordinary vertices occupy at most two vertices per interior distance level.
This uses the actual definition of ordinariness and needs no pole hypothesis. -/
theorem ordinary_vertex_card_le :
    (Finset.univ.filter fun v : V => N.IsOrdinaryLayer s t (N.graph.dist s v)).card ≤
      2 * (N.graph.dist s t - 1) := by
  let level : V → ℕ := N.graph.dist s
  let good : Finset V := Finset.univ.filter fun v => N.IsOrdinaryLayer s t (level v)
  have hfiber (j : ℕ) (hj : j ∈ good.image level) :
      (good.filter fun v => level v = j).card = 2 := by
    obtain ⟨w, hw, hwj⟩ := Finset.mem_image.mp hj
    have hord : N.IsOrdinaryLayer s t j := by
      rw [← hwj]
      exact (Finset.mem_filter.mp hw).2
    have heq : good.filter (fun v => level v = j) =
        Finset.univ.filter (fun v => level v = j) := by
      ext v
      simp only [good, Finset.mem_filter, Finset.mem_univ, true_and]
      constructor
      · exact fun h => h.2
      · intro hv
        exact ⟨hv ▸ hord, hv⟩
    rw [heq]
    have hc := hord.1.2.2
    simpa only [Nat.card_eq_fintype_card, Fintype.card_subtype] using hc
  have hlevels : good.image level ⊆ Finset.Ioo 0 (N.graph.dist s t) := by
    intro j hj
    obtain ⟨v, hv, hvj⟩ := Finset.mem_image.mp hj
    have hord := (Finset.mem_filter.mp hv).2
    exact Finset.mem_Ioo.mpr ⟨hvj ▸ hord.1.1, hvj ▸ hord.1.2.1⟩
  change good.card ≤ _
  calc
    good.card = ∑ j ∈ good.image level, (good.filter fun v => level v = j).card :=
      Finset.card_eq_sum_card_image level good
    _ = ∑ _j ∈ good.image level, 2 := Finset.sum_congr rfl hfiber
    _ = 2 * (good.image level).card := by simp [Nat.mul_comm]
    _ ≤ 2 * (Finset.Ioo 0 (N.graph.dist s t)).card :=
      Nat.mul_le_mul_left 2 (Finset.card_le_card hlevels)
    _ = 2 * (N.graph.dist s t - 1) := by simp

/-- The actual two-pole order is bounded by its two-vertex ordinary layers
and every remaining vertex counted individually. -/
theorem twice_rank_le_inner_layers_add_bad (hN : N.IsBridgelessTwoPole s t) :
    2 * networkRank N ≤ 2 * (N.graph.dist s t - 1) +
      Nat.card {v : V // ¬ N.IsOrdinaryLayer s t (N.graph.dist s v)} := by
  have hgood := ordinary_vertex_card_le N s t
  have hsplit := Finset.filter_card_add_filter_neg_card_eq_card (s := (Finset.univ : Finset V))
    (fun v : V => N.IsOrdinaryLayer s t (N.graph.dist s v))
  have horder := PolePathRank.bridgeless_order N s t hN
  simp only [Nat.card_eq_fintype_card, Fintype.card_subtype]
  simp only [Finset.card_univ] at hsplit
  omega

/-- A bound on all nonordinary vertices bounds rank by distance plus that
same constant. The weaker constant avoids any parity or rounding premise. -/
theorem rank_le_distance_add_bad (hN : N.IsBridgelessTwoPole s t) (C : ℕ)
    (hbad : Nat.card {v : V // ¬ N.IsOrdinaryLayer s t (N.graph.dist s v)} ≤ C) :
    networkRank N ≤ N.graph.dist s t + C := by
  have h := twice_rank_le_inner_layers_add_bad N s t hN
  omega

end Erdos1016.ExactMaximumSupport.OrdinaryLayerOrder
