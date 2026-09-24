import Erdos1016.Probability.Cylinders.AffinePairs
import Erdos1016.Probability.Cylinders.TripleConstraintIntersection
import Erdos1016.Probability.Cylinders.TripleConstraintRank
import Erdos1016.Probability.Cylinders.ExceptionalPartnerCount

set_option autoImplicit false

/-!
# Graphical exceptional-partner bridge for selected triples

Given the three-vertex star bound, this file supplies the common-rank and
64-exceptional-partner hypotheses required by the selected-triple
second-moment theorem.  The only graph-specific input is the triple-star rank
bound for three distinct vertices.
-/

noncomputable section

namespace Erdos1016.Proof.GraphicalExceptionalPartnerBridge

open Erdos1016
open Erdos1016.Proof.ActiveTripleBridge
open Erdos1016.Proof.AffineCylinderPairs
open Erdos1016.Proof.GraphicalCommonInformation
open Erdos1016.Proof.GraphicalTripleReduction
open Erdos1016.Proof.GraphicalTripleConstraintIntersection
open Erdos1016.Proof.TripleConstraintRank
open Erdos1016.Proof.ExceptionalPartnerCardinality
open Erdos1016.Proof.PartnerCounting

local notation "F₂" => ZMod 2

/-- Two indices are exceptional when they are distinct and their selected
triple constraint spaces share at least two independent constraints. -/
def highCommonPartner (G : PhysicalGraph) {ι : Type*}
    (edges : ι → Fin 3 → G.Edge) (i j : ι) : Prop :=
  i ≠ j ∧ 2 ≤ Module.finrank F₂
    (CommonSubspace (tripleConstraintSpace G (edges i))
      (tripleConstraintSpace G (edges j)))

/-- A pair outside the exceptional relation has common constraint rank at
most one. -/
theorem commonRank_le_one_of_not_highCommonPartner
    (G : PhysicalGraph) {ι : Type*} [Fintype ι] [DecidableEq ι]
    (edges : ι → Fin 3 → G.Edge)
    {i j : ι} (hij : i ≠ j)
    (hnot : ¬ highCommonPartner G edges i j) :
    Module.finrank F₂
      (CommonSubspace (tripleConstraintSpace G (edges i))
        (tripleConstraintSpace G (edges j))) ≤ 1 := by
  classical
  have hlt : Module.finrank F₂
      (CommonSubspace (tripleConstraintSpace G (edges i))
        (tripleConstraintSpace G (edges j))) < 2 := by
    by_contra hge
    have hge' : 2 ≤ Module.finrank F₂
        (CommonSubspace (tripleConstraintSpace G (edges i))
          (tripleConstraintSpace G (edges j))) := by omega
    exact hnot ⟨hij, hge'⟩
  omega

/-- If every three distinct centers have one-dimensional triple-star
intersection, each selected triple has at most 64 exceptional partners. -/
theorem highCommonPartner_count_le_64
    (G : PhysicalGraph) {ι : Type*} [Fintype ι] [DecidableEq ι]
    (edges : ι → Fin 3 → G.Edge)
    [hdec : DecidableRel (highCommonPartner G edges)]
    (centers : ι → G.Vertex)
    (hcenters : Function.Injective centers)
    (hincident : ∀ i k, G.incident (edges i k) (centers i))
    (hstar : ∀ u v w : G.Vertex, u ≠ v → u ≠ w → v ≠ w →
      Module.finrank F₂ (tripleStarSpace G u v w) ≤ 1) :
    ∀ i, Fintype.card {j // highCommonPartner G edges i j} ≤ 64 := by
  classical
  intro i
  let exceptional : ι → Prop := highCommonPartner G edges i
  letI : DecidablePred exceptional := hdec i
  let S : Submodule F₂ (Module.Dual F₂ G.CycleSpace) :=
    tripleConstraintSpace G (edges i)
  let T : ι → Submodule F₂ (Module.Dual F₂ G.CycleSpace) :=
    fun j => tripleConstraintSpace G (edges j)
  have hS : Module.finrank F₂ S ≤ 3 := by
    simpa [S] using tripleConstraintSpace_finrank_le_three G (edges i)
  have hpair : ∀ j, exceptional j →
      2 ≤ Module.finrank F₂ (PairIntersection S (T j)) := by
    intro j hj
    simpa [S, T, exceptional, highCommonPartner, CommonSubspace] using hj.2
  have htriple : ∀ j k, exceptional j → exceptional k → j ≠ k →
      Module.finrank F₂ (TripleIntersection S (T j) (T k)) ≤ 1 := by
    intro j k hj hk hjk
    have huv : centers i ≠ centers j := by
      intro heq
      exact hj.1 (hcenters heq)
    have huw : centers i ≠ centers k := by
      intro heq
      exact hk.1 (hcenters heq)
    have hvw : centers j ≠ centers k := by
      intro heq
      exact hjk (hcenters heq)
    have hgeom := tripleConstraint_intersection_finrank_le_one
      G (edges i) (edges j) (edges k) (centers i) (centers j) (centers k)
      (fun m => hincident i m) (fun m => hincident j m) (fun m => hincident k m)
      (hstar (centers i) (centers j) (centers k) huv huw hvw)
    simpa [S, T] using hgeom
  simpa [exceptional] using
    (exceptional_card_le_64 S T exceptional hS hpair htriple)

/-- In real-valued form, for direct use by the second-moment theorem. -/
theorem highCommonPartner_real_card_le_64
    (G : PhysicalGraph) {ι : Type*} [Fintype ι] [DecidableEq ι]
    (edges : ι → Fin 3 → G.Edge)
    [hdec : DecidableRel (highCommonPartner G edges)]
    (centers : ι → G.Vertex)
    (hcenters : Function.Injective centers)
    (hincident : ∀ i k, G.incident (edges i k) (centers i))
    (hstar : ∀ u v w : G.Vertex, u ≠ v → u ≠ w → v ≠ w →
      Module.finrank F₂ (tripleStarSpace G u v w) ≤ 1) :
    ∀ i, ((Finset.univ.filter (fun j => highCommonPartner G edges i j)).card : ℝ) ≤ 64 := by
  classical
  intro i
  have hcount := highCommonPartner_count_le_64 G edges centers hcenters hincident hstar i
  have hcardSubtype : Fintype.card {j // highCommonPartner G edges i j} =
      (Finset.univ.filter (fun j => highCommonPartner G edges i j)).card := by
    simp [Fintype.card_subtype]
  rw [← hcardSubtype]
  exact_mod_cast hcount

end Erdos1016.Proof.GraphicalExceptionalPartnerBridge
