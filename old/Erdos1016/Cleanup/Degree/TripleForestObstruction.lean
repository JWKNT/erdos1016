import Erdos1016.Probability.Moments.SelectedDegree
import Erdos1016.Probability.Cylinders.IncidentTripleEvents
import Erdos1016.Probability.Cylinders.GraphicalThreshold

set_option autoImplicit false

noncomputable section

namespace Erdos1016.Proof.BadVertexTripleForestBridge

open Erdos1016
open Erdos1016.PhysicalGraph
open Erdos1016.Proof.ActiveDegreeMoment
open Erdos1016.Proof.ActiveTripleBridge
open Erdos1016.Proof.GraphicalThreshold

local notation "F₂" => ZMod 2

/-- Three distinct selected edges outside the witness give restricted degree
at least three at their common vertex. Thus their state cannot be an outside
linear forest. -/
theorem allSelectedTriple_not_outsideLinearForestStates
    (G : PhysicalGraph) (E : Finset G.Edge) (v : G.Vertex)
    (e : Fin 3 → G.Edge) (x : G.CycleSpace)
    (hinj : Function.Injective e)
    (hinc : ∀ i, G.incident (e i) v)
    (houtside : ∀ i, e i ∉ E)
    (hselected : allSelectedTriple G e x) :
    x ∉ G.outsideLinearForestStates E := by
  classical
  let F : Finset G.Edge := Finset.univ.image e
  have hFcard : F.card = 3 := by
    dsimp [F]
    rw [Finset.card_image_of_injective _ hinj]
    simp
  have hFprops : ∀ f ∈ F, f ∈ Eᶜ ∧ G.incident f v := by
    intro f hf
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hf
    exact ⟨by simp [houtside i], hinc i⟩
  have hselectedEdge : ∀ f ∈ F, x.1 f = 1 := by
    intro f hf
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hf
    have h := congrFun hselected i
    simpa [tripleObservation, ActiveEdgeUniform.edgeCoordinate] using h
  have hcount : selectedFamilyCount G F x = (F.card : ℝ) := by
    unfold selectedFamilyCount
    have hsum : (∑ f ∈ F, if x.1 f = 1 then (1 : ℝ) else 0) =
        ∑ f ∈ F, (1 : ℝ) := by
      apply Finset.sum_congr rfl
      intro f hf
      simp [hselectedEdge f hf]
    rw [hsum]
    simp
  have hdegree := selectedFamilyCount_le_restrictedDegree G E F v x hFprops
  have hdegreeLower : (3 : ℝ) ≤
      (G.restrictedSelectedDegree Eᶜ (G.restrictWord Eᶜ x.1) v : ℝ) := by
    have hcardR : (3 : ℝ) = (F.card : ℝ) := by exact_mod_cast hFcard.symm
    rw [hcardR, ← hcount]
    exact hdegree
  intro hxForest
  have hforest : G.IsRestrictedLinearForest Eᶜ
      (G.restrictWord Eᶜ x.1) := by
    simpa [outsideLinearForestStates] using hxForest
  have hdegreeUpper : G.restrictedSelectedDegree Eᶜ
      (G.restrictWord Eᶜ x.1) v ≤ 2 := hforest.2 v
  have hdegreeUpper' :
      (G.restrictedSelectedDegree Eᶜ (G.restrictWord Eᶜ x.1) v : ℝ) ≤ 2 := by
    exact_mod_cast hdegreeUpper
  linarith

/-- Any positive count from a family of feasible triples at distinct marked
vertices forces at least one event to hold; that event already forces degree
three outside the witness. This is the `hcontained` input to the cylinder
threshold theorem. -/
theorem positive_selectedTripleCount_not_outsideLinearForestStates
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (G : PhysicalGraph) (E : Finset G.Edge)
    (v : ι → G.Vertex) (edges : ι → Fin 3 → G.Edge)
    (hinj : ∀ i, Function.Injective (edges i))
    (hinc : ∀ j k, G.incident (edges j k) (v j))
    (houtside : ∀ j k, edges j k ∉ E)
    (x : G.CycleSpace)
    (hcount : 1 ≤ eventCount (fun j y => allSelectedTriple G (edges j) y) x) :
    x ∉ G.outsideLinearForestStates E := by
  classical
  have hexists : ∃ j, allSelectedTriple G (edges j) x := by
    by_contra hnone
    have hno : ∀ j, ¬ allSelectedTriple G (edges j) x := by
      intro j hj
      exact hnone ⟨j, hj⟩
    have hzero : (∑ j,
        (if allSelectedTriple G (edges j) x then (1 : ℝ) else 0)) = 0 :=
      Finset.sum_eq_zero (fun j hj => by simp [hno j])
    have hcountzero : eventCount
        (fun j y => allSelectedTriple G (edges j) y) x = 0 := by
      rw [eventCount]
      exact hzero
    rw [hcountzero] at hcount
    norm_num at hcount
  obtain ⟨j, hj⟩ := hexists
  exact allSelectedTriple_not_outsideLinearForestStates G E (v j) (edges j)
    x (hinj j) (hinc j) (houtside j) hj

end Erdos1016.Proof.BadVertexTripleForestBridge
