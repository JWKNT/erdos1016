import Erdos1016.ExactMaximumSupport.LargeGirth.PackingSelectedSpaces
import Erdos1016.ExactMaximumSupport.LargeGirth.PackingLocalSpacesProbability
import Erdos1016.ExactMaximumSupport.LargeGirth.PackingLocalSpacesRelevance

set_option autoImplicit false

/-!
# Selecting actual marked vertices by their local parity spaces

The two-fifths product threshold supplies a small independent family.
Every other nonzero marked vertex is relevant to that family, and its
physical boundary has the required size bound.
-/

noncomputable section
open scoped BigOperators
namespace Erdos1016.ExactMaximumSupport.LargeGirth.PackingMarkedFamily

open BoundaryDecay PackingLocalSpaces PackingSelectedSpaces

local instance packingMarkedDecidable (p : Prop) : Decidable p := Classical.propDecidable p

theorem penalty_eq_zeroStar (Q : FiniteMultiGraph) (v : Q.Vertex) (x : Q.CycleSpace) :
    penalty (localSpace Q v) x = 1 - indicator (ZeroStar Q v) x / 2 := by
  have he : (fun y : Q.CycleSpace => ∀ f ∈ localSpace Q v, f y = 0) = ZeroStar Q v := by
    funext y
    exact propext (coordinateSpace_zero_iff Q (starEdges Q v) y)
  rw [penalty, he]

/-- The actual cut is bounded by the total degree of the selected vertices. -/
theorem cut_card_le (Q : FiniteMultiGraph) (A : Finset Q.Vertex) (d : ℕ)
    (hdegree : ∀ v ∈ A, Q.degree v ≤ d) : (Q.cutEdges A).card ≤ d * A.card := by
  have hs := Q.sum_region_degree A
  have hu : (∑ v ∈ A, Q.degree v) ≤ A.card * d := by
    calc
      _ ≤ ∑ _v ∈ A, d := Finset.sum_le_sum (fun v hv => hdegree v hv)
      _ = _ := by simp
  nlinarith

/-- This supplies the selected set and all inputs to the strings argument.
The product threshold is on the actual uniform cycle space of the quotient. -/
theorem exists_selected (Q : FiniteMultiGraph) (marks : Finset Q.Vertex)
    (hloop : ∀ e, Q.src e ≠ Q.dst e) (d : ℕ) (hd : 1 ≤ d)
    (hdegree : ∀ v ∈ marks, Q.degree v ≤ d)
    (hprob : (2 / 5 : ℝ) ≤ average (fun x : Q.CycleSpace =>
      ∏ v ∈ marks, (1 - indicator (ZeroStar Q v) x / 2))) :
    ∃ A ⊆ marks, A.SupIndep (localSpace Q) ∧
      (∀ v ∈ A, localSpace Q v ≠ ⊥) ∧ A.card < 2^d ∧
      (Q.cutEdges A).card ≤ d*A.card ∧
      (∀ v ∈ marks, v ∉ A → localSpace Q v = ⊥ ∨ Relevant Q A v) ∧
      (marks.filter fun v => localSpace Q v = ⊥).card ≤ 1 := by
  have hp : (2 / 5 : ℝ) ≤ average (fun x : Q.CycleSpace =>
      ∏ v ∈ marks, penalty (localSpace Q v) x) := by
    simpa only [penalty_eq_zeroStar] using hprob
  have hdim (v : Q.Vertex) (hv : v ∈ marks) :
      Module.finrank F₂ (localSpace Q v) ≤ d - 1 :=
    (localSpace_finrank_le Q v hloop).trans (Nat.sub_le_sub_right (hdegree v hv) 1)
  obtain ⟨A, hA, hind, hnonzero, hcard, hrel, hzero⟩ :=
    PackingSelectedSpaces.exists_selected marks (localSpace Q) d hd hdim hp
  refine ⟨A, hA, hind, hnonzero, hcard,
    cut_card_le Q A d (fun v hv => hdegree v (hA hv)), ?_, hzero⟩
  intro v hv hvA
  rcases hrel v hv hvA with hz | hr
  · exact Or.inl hz
  · apply Or.inr
    unfold Relevant
    rw [markedSpace_eq_sup]
    intro heq
    exact hr (disjoint_iff.mpr heq)

end Erdos1016.ExactMaximumSupport.LargeGirth.PackingMarkedFamily
