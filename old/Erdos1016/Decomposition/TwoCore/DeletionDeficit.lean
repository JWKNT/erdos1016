import Erdos1016.Decomposition.TwoCore.MaximalCore

set_option autoImplicit false

/-!
# Cubic deficit after deleting a vertex set

Deleting `X` from a subcubic physical graph increases the cubic deficit of
what remains by at most three per deleted vertex. This is the finite ledger
needed before passing the FEW remainder to its unsuppressed two-core.
-/

noncomputable section

namespace Erdos1016.Proof.FewDeletedCoreBudget

open Erdos1016.Nonbacktracking.FiniteTwoCore

local instance fewDeletedCoreBudgetDecidable (p : Prop) : Decidable p :=
  Classical.propDecidable p

variable {V : Type*} [Fintype V] [DecidableEq V]
variable (J : SimpleGraph V)

/-- The within-degree on the full vertex set is the ordinary graph degree. -/
theorem degreeWithin_univ_eq_degree (v : V) :
    degreeWithin J Finset.univ v = J.degree v := by
  unfold degreeWithin SimpleGraph.degree
  rw [SimpleGraph.neighborFinset_eq_filter]

private theorem degreeWithin_compl_add (X : Finset V) (v : V) :
    degreeWithin J Xᶜ v + degreeWithin J X v = J.degree v := by
  unfold degreeWithin SimpleGraph.degree
  rw [← Finset.card_union_of_disjoint]
  · congr 1
    ext w
    simp only [Finset.mem_union, Finset.mem_filter, Finset.mem_compl,
      Finset.mem_univ, true_and, SimpleGraph.mem_neighborFinset]
    tauto
  · apply Finset.disjoint_left.2
    intro w hwc hw
    exact (Finset.mem_compl.1 (Finset.mem_filter.1 hwc).1) (Finset.mem_filter.1 hw).1

private theorem deleted_incidence_le (hmax : ∀ v, J.degree v ≤ 3)
    (X : Finset V) :
    (∑ v ∈ Xᶜ, degreeWithin J X v) ≤ 3 * X.card := by
  have hfilter (v : V) :
      degreeWithin J X v = ∑ w ∈ X, if J.Adj v w then 1 else 0 := by
    unfold degreeWithin
    rw [Finset.card_eq_sum_ones, Finset.sum_filter]
  calc
    (∑ v ∈ Xᶜ, degreeWithin J X v) =
        ∑ v ∈ Xᶜ, ∑ w ∈ X, if J.Adj v w then 1 else 0 := by
          apply Finset.sum_congr rfl
          intro v hv
          rw [hfilter]
    _ = ∑ w ∈ X, ∑ v ∈ Xᶜ, if J.Adj v w then 1 else 0 := by
          rw [Finset.sum_comm]
    _ ≤ ∑ w ∈ X, J.degree w := by
          apply Finset.sum_le_sum
          intro w hw
          have hsub : Xᶜ.filter (fun v => J.Adj v w) ⊆ J.neighborFinset w := by
            intro v hv
            exact (SimpleGraph.mem_neighborFinset J w v).2
              (Finset.mem_filter.1 hv).2.symm
          have hcard := Finset.card_le_card hsub
          have hsum : (∑ v ∈ Xᶜ, if J.Adj v w then 1 else 0) =
              (Xᶜ.filter (fun v => J.Adj v w)).card := by
            rw [← Finset.sum_filter]
            simp
          rw [hsum]
          exact hcard
    _ ≤ ∑ _w ∈ X, 3 := by
          apply Finset.sum_le_sum
          intro w hw
          exact hmax w
    _ = 3 * X.card := by simp [Nat.mul_comm]

/-- The cubic deficit of the induced graph on the undeleted vertices is at
most the original deficit plus three times the number deleted. -/
theorem cubicDeficit_compl_le (hmax : ∀ v, J.degree v ≤ 3) (X : Finset V) :
    cubicDeficit J Xᶜ ≤ cubicDeficit J Finset.univ + 3 * X.card := by
  have hfullDegree (v : V) : degreeWithin J Finset.univ v = J.degree v := by
    unfold degreeWithin SimpleGraph.degree
    rw [SimpleGraph.neighborFinset_eq_filter]
  have hdefS : cubicDeficit J Xᶜ =
      ∑ v ∈ Xᶜ, ((3 : ℤ) - (degreeWithin J Xᶜ v : ℤ)) := by
    unfold cubicDeficit
    have hc : 3 * (Xᶜ.card : ℤ) = ∑ _v ∈ Xᶜ, (3 : ℤ) := by
      simp
      ring
    rw [hc, ← Finset.sum_sub_distrib]
  have hdefAll : cubicDeficit J Finset.univ =
      ∑ v, ((3 : ℤ) - (J.degree v : ℤ)) := by
    unfold cubicDeficit
    have hc : 3 * (((Finset.univ : Finset V).card) : ℤ) =
        ∑ _v : V, (3 : ℤ) := by
      simp
      ring
    rw [hc]
    simp_rw [hfullDegree]
    rw [← Finset.sum_sub_distrib]
  have hpoint (v : V) :
      (3 : ℤ) - (degreeWithin J Xᶜ v : ℤ) =
        (3 - (J.degree v : ℤ)) + (degreeWithin J X v : ℤ) := by
    have h := degreeWithin_compl_add J X v
    have h' : (degreeWithin J Xᶜ v : ℤ) + degreeWithin J X v = J.degree v := by
      exact_mod_cast h
    linarith
  have hmain :
      (∑ v ∈ Xᶜ, (3 - (J.degree v : ℤ))) ≤
        ∑ v, (3 - (J.degree v : ℤ)) := by
    apply Finset.sum_le_sum_of_subset_of_nonneg
      (s := Xᶜ) (t := Finset.univ)
    · exact Finset.subset_univ _
    · intro v hv hnot
      have hvX : v ∈ X := by
        by_cases hX : v ∈ X
        · exact hX
        · exact False.elim (hnot (Finset.mem_compl.2 hX))
      have hvdeg := hmax v
      have hcast : (J.degree v : ℤ) ≤ 3 := by exact_mod_cast hvdeg
      linarith
  have hincCast :
      (∑ v ∈ Xᶜ, (degreeWithin J X v : ℤ)) ≤ 3 * (X.card : ℤ) := by
    exact_mod_cast deleted_incidence_le J hmax X
  calc
    cubicDeficit J Xᶜ =
        (∑ v ∈ Xᶜ, ((3 : ℤ) - (degreeWithin J Xᶜ v : ℤ))) := hdefS
    _ =
        (∑ v ∈ Xᶜ, (3 - (J.degree v : ℤ))) +
          ∑ v ∈ Xᶜ, (degreeWithin J X v : ℤ) := by
            simp_rw [hpoint]
            rw [Finset.sum_add_distrib]
    _ ≤ (∑ v, (3 - (J.degree v : ℤ))) + 3 * (X.card : ℤ) :=
          add_le_add hmain hincCast
    _ = cubicDeficit J Finset.univ + 3 * (X.card : ℤ) := by rw [← hdefAll]

/-- For a min-two, subcubic graph, the original cubic deficit is exactly its
degree-two population. -/
theorem cubicDeficit_univ_eq_degreeTwoCount
    (hmin : ∀ v, 2 ≤ J.degree v) (hmax : ∀ v, J.degree v ≤ 3) :
    cubicDeficit J Finset.univ = (degreeTwoCount J Finset.univ : ℤ) := by
  apply cubicDeficit_eq_degreeTwoCount J
  · intro v hv
    rw [degreeWithin_univ_eq_degree]
    exact hmin v
  · intro v
    rw [degreeWithin_univ_eq_degree]
    exact hmax v

/-- The two-core of a subcubic graph after deleting `X` loses at most four
vertices per deleted vertex, plus the original cubic deficit. Its degree-two
population is bounded by the original deficit plus three per deletion.
These are the two finite inequalities used in the paper's FEW order ledger. -/
theorem complement_twoCore_ledger (hmax : ∀ v, J.degree v ≤ 3)
    (X : Finset V) :
    let S := Xᶜ
    let C := vertices J S
    (degreeTwoCount J C : ℤ) ≤ cubicDeficit J Finset.univ + 3 * (X.card : ℤ) ∧
    (Fintype.card V : ℤ) - cubicDeficit J Finset.univ - 4 * (X.card : ℤ) ≤
      (C.card : ℤ) := by
  dsimp only
  let S := Xᶜ
  let C := vertices J S
  have hCS : C ⊆ S := vertices_subset J S
  have hpeel : Peeling J C S := exists_peeling J S S hCS (Finset.Subset.refl _)
  have hdef := cubicDeficit_compl_le J hmax X
  have htwo := degreeTwoCount_core_le_deficit J hpeel
    (vertices_minTwo J S) (vertices_maxDegree J S 3 hmax)
  have hdegree : (degreeTwoCount J C : ℤ) ≤
      cubicDeficit J Finset.univ + 3 * (X.card : ℤ) := by
    exact htwo.trans hdef
  have horder := order_le_core_add_deficit J hpeel hCS hmax
  have hdefS : cubicDeficit J S ≤
      cubicDeficit J Finset.univ + 3 * (X.card : ℤ) := by
    simpa [S] using hdef
  have hcomp : (X.card : ℤ) + (S.card : ℤ) = Fintype.card V := by
    exact_mod_cast Finset.card_add_card_compl X
  have horder' : (S.card : ℤ) ≤
      (C.card : ℤ) + cubicDeficit J Finset.univ + 3 * (X.card : ℤ) := by
    linarith [horder, hdefS]
  refine ⟨hdegree, ?_⟩
  linarith

end Erdos1016.Proof.FewDeletedCoreBudget

end
