import Erdos1016.ExactMaximum.PoleLayers
import Erdos1016.ExactMaximumSupport.DistanceFourLayers
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

set_option autoImplicit false

/-!
# Physical edge multiplicities at a network vertex

All multiplicities are literal cardinalities of labelled edges satisfying
`Joins`. Distinct neighbor fibers are disjoint, even in a multigraph.
A positive-distance vertex has a predecessor, leaving at most two physical
labels for two neighbors in the next layer when its degree is at most three.
-/
noncomputable section
open scoped BigOperators
namespace Erdos1016.ExactMaximumSupport.NetworkMultiplicity

open BoundaryTrace BoundaryTrace.Network
local instance multiplicityDecidable (p : Prop) : Decidable p := Classical.propDecidable p

variable {V E : Type*} [Fintype E] (N : Network V E)

omit [Fintype E] in
/-- Reversing the two ends does not change the physical-label multiplicity. -/
theorem joins_card_symm (u v : V) :
    Nat.card {e : E // N.Joins e u v} = Nat.card {e : E // N.Joins e v u} := by
  apply Nat.card_congr
  exact Equiv.subtypeEquivRight (fun _ => ⟨fun h => h.symm, fun h => h.symm⟩)

omit [Fintype E] in
/-- A fixed physical label incident to a fixed first vertex has a unique other end. -/
theorem joins_other_unique {e : E} {u v w : V}
    (hv : N.Joins e u v) (hw : N.Joins e u w) : v = w := by
  rcases hv with ⟨h₁,h₂⟩ | ⟨h₁,h₂⟩ <;>
    rcases hw with ⟨h₃,h₄⟩ | ⟨h₃,h₄⟩
  · exact h₂.symm.trans h₄
  · exact h₂.symm.trans (h₄.trans (h₁.symm.trans h₃))
  · exact h₁.symm.trans (h₃.trans (h₂.symm.trans h₄))
  · exact h₁.symm.trans h₃

/-- A sum over distinct neighbor vertices counts disjoint physical labels,
so it is bounded by the actual degree. -/
theorem sum_joins_card_le_degree (u : V) (R : Finset V) :
    (∑ v ∈ R, Nat.card {e : E // N.Joins e u v}) ≤ N.deg (fun _ => 1) u := by
  let F : V → Finset E := fun v => Finset.univ.filter fun e => N.Joins e u v
  have hdisj : (R : Set V).PairwiseDisjoint F := by
    intro v _ w _ hvw
    apply Finset.disjoint_left.mpr
    intro e hev hew
    exact hvw (joins_other_unique N (Finset.mem_filter.mp hev).2 (Finset.mem_filter.mp hew).2)
  have hsub : R.biUnion F ⊆ Finset.univ.filter
      (fun e => (1 : Bit) ≠ 0 ∧ (N.src e = u ∨ N.dst e = u)) := by
    intro e he
    obtain ⟨v, _, hev⟩ := Finset.mem_biUnion.mp he
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, one_ne_zero,
      (Finset.mem_filter.mp hev).2.at_left⟩
  simp only [Nat.card_eq_fintype_card, Fintype.card_subtype]
  change (∑ v ∈ R, (F v).card) ≤ N.deg (fun _ => 1) u
  rw [← Finset.card_biUnion hdisj]
  exact Finset.card_le_card hsub

/-- Two physical labels with the same ends make both endpoints parallel vertices. -/
theorem onParallel_of_two_le_joins_card (u v : V)
    (hcard : 2 ≤ Nat.card {e : E // N.Joins e u v}) :
    N.OnParallel u ∧ N.OnParallel v := by
  have hc : 1 < (Finset.univ.filter fun e : E => N.Joins e u v).card := by
    simpa only [Nat.card_eq_fintype_card, Fintype.card_subtype] using hcard
  obtain ⟨e, f, he, hf, hef⟩ := Finset.one_lt_card_iff.mp hc
  have he' := (Finset.mem_filter.mp he).2
  have hf' := (Finset.mem_filter.mp hf).2
  exact ⟨⟨e, f, v, hef, he', hf'⟩, ⟨e, f, u, hef, he'.symm, hf'.symm⟩⟩

/-- Actual adjacency gives a positive physical multiplicity. -/
theorem joins_card_pos_of_adj (u v : V) (huv : N.graph.Adj u v) :
    0 < Nat.card {e : E // N.Joins e u v} := by
  obtain ⟨e, he⟩ := huv
  haveI : Nonempty {e : E // N.Joins e u v} := ⟨⟨e, he⟩⟩
  exact Nat.card_pos

/-- At a positive-distance subcubic vertex, an actual predecessor leaves at
most two labels joining any two distinct vertices in the next distance layer. -/
theorem next_layer_pair_count_le_two (s u v w : V) (l : ℕ)
    (hconn : N.graph.Connected) (hlu : N.graph.dist s u = l) (hlpos : 0 < l)
    (hlv : N.graph.dist s v = l+1) (hlw : N.graph.dist s w = l+1)
    (hvw : v ≠ w) (hdegree : N.deg (fun _ => 1) u ≤ 3) :
    Nat.card {e : E // N.Joins e u v} + Nat.card {e : E // N.Joins e u w} ≤ 2 := by
  obtain ⟨q, hqu, hq⟩ := DistanceFourLayers.exists_predecessor N.graph s hconn u (by omega)
  have hqv : q ≠ v := by intro h; subst q; omega
  have hqw : q ≠ w := by intro h; subst q; omega
  have hsum := sum_joins_card_le_degree N u ({v,w,q} : Finset V)
  have hpositive := joins_card_pos_of_adj N u q hqu.symm
  simp only [Finset.sum_insert, Finset.sum_singleton,
    Finset.mem_insert, Finset.mem_singleton, hvw, Ne.symm hqv, hqw, Ne.symm hqw,
    false_or, not_false_eq_true] at hsum
  omega

end Erdos1016.ExactMaximumSupport.NetworkMultiplicity
