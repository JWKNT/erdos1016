import Erdos1016.Probability.Moments.ActiveDegreeExtraction
import Erdos1016.Cleanup.Degree.FeasibleIncidentTriple
import Erdos1016.Probability.Cylinders.SelectedIncidentTriples
import Erdos1016.Probability.Cylinders.GraphicalPartnerCount

set_option autoImplicit false

/-!
# Cardinality bound for vertices with four active outside edges

For each vertex with at least four active edges outside the witness, choose a
feasible incident selected triple. The selected-triple cylinder argument then
bounds the number of such vertices by `520 * R` whenever the outside-forest
probability is strictly above its threshold.

The common-rank and exceptional-partner hypotheses are kept explicit here:
they are the remaining graph-specific inputs to the pair-cylinder estimate.
-/

noncomputable section

namespace Erdos1016.Proof.BadVertexCardinalityBound

open Erdos1016
open Erdos1016.PhysicalGraph
open Erdos1016.Proof.ActiveDegreeExtraction
open Erdos1016.Proof.BadVertexTripleExistence
open Erdos1016.Proof.BadVertexSelectedTriples
open Erdos1016.Proof.ActiveTripleBridge
open Erdos1016.Proof.ActiveEdgeUniform
open Erdos1016.Proof.AffineCylinders
open Erdos1016.Proof.AffineCylinderPairs
open Erdos1016.Proof.GraphicalExceptionalPartnerBridge
open Erdos1016.Proof.GraphicalTripleReduction

local notation "F₂" => ZMod 2

/-- Vertices with at least four active incident edges outside the witness. -/
def badVertexSet (G : PhysicalGraph) (E : Finset G.Edge) : Finset G.Vertex := by
  classical
  exact Finset.univ.filter fun v =>
    4 ≤ (activeOutsideIncidentEdges G E v).card

/-- Finite subtype indexing the vertices in `badVertexSet`. -/
abbrev BadVertexIndex (G : PhysicalGraph) (E : Finset G.Edge) :=
  {v : G.Vertex // v ∈ badVertexSet G E}

/-- The local triple-existence theorem applied to a bad-vertex index. -/
theorem exists_feasible_triple_at_bad_vertex
    (G : PhysicalGraph) (E : Finset G.Edge)
    (i : BadVertexIndex G E) :
    ∃ e : Fin 3 → G.Edge,
      (∀ k, e k ∈ activeOutsideIncidentEdges G E i.1) ∧
      (∀ k, G.incident (e k) i.1) ∧ Function.Injective e ∧
      ∃ x : G.CycleSpace, allSelectedTriple G e x := by
  classical
  have hcard : 4 ≤ (activeOutsideIncidentEdges G E i.1).card := by
    have hi := i.2
    change i.1 ∈ Finset.univ.filter
      (fun v => 4 ≤ (activeOutsideIncidentEdges G E v).card) at hi
    exact (Finset.mem_filter.mp hi).2
  have hinc : ∀ e ∈ activeOutsideIncidentEdges G E i.1,
      G.incident e i.1 := by
    intro e he
    exact (Finset.mem_filter.mp he).2.2.2
  have hactive : ∀ e ∈ activeOutsideIncidentEdges G E i.1,
      ActiveEdge G e := by
    intro e he
    exact (Finset.mem_filter.mp he).2.1
  exact exists_feasible_triple_of_active_edges G i.1
    (activeOutsideIncidentEdges G E i.1) hinc hactive hcard

/-- A canonical feasible selected triple at every bad vertex. -/
noncomputable def selectedTripleAtBadVertex
    (G : PhysicalGraph) (E : Finset G.Edge) (i : BadVertexIndex G E) :
    Fin 3 → G.Edge := Classical.choose (exists_feasible_triple_at_bad_vertex G E i)

/-- The chosen triple's incidence, injectivity, and outside-witness facts. -/
theorem selectedTripleAtBadVertex_spec
    (G : PhysicalGraph) (E : Finset G.Edge) (i : BadVertexIndex G E) :
    (∀ k, selectedTripleAtBadVertex G E i k ∈ activeOutsideIncidentEdges G E i.1) ∧
    (∀ k, G.incident (selectedTripleAtBadVertex G E i k) i.1) ∧
    Function.Injective (selectedTripleAtBadVertex G E i) ∧
    ∃ x : G.CycleSpace, allSelectedTriple G (selectedTripleAtBadVertex G E i) x :=
  Classical.choose_spec (exists_feasible_triple_at_bad_vertex G E i)

/-- A canonical witness certifying feasibility of the chosen triple. -/
noncomputable def selectedTripleWitnessAtBadVertex
    (G : PhysicalGraph) (E : Finset G.Edge) (i : BadVertexIndex G E) :
    G.CycleSpace :=
  Classical.choose (selectedTripleAtBadVertex_spec G E i).2.2.2

/-- The chosen triple is feasible at its canonical witness. -/
theorem selectedTripleWitnessAtBadVertex_feasible
    (G : PhysicalGraph) (E : Finset G.Edge) (i : BadVertexIndex G E) :
    allSelectedTriple G (selectedTripleAtBadVertex G E i)
      (selectedTripleWitnessAtBadVertex G E i) :=
  Classical.choose_spec (selectedTripleAtBadVertex_spec G E i).2.2.2

/-- Under the strict probability-threshold assumption, the set of vertices
with at least four active edges outside the witness has size less than
`520 * R`. The pairwise common-rank and exceptional-neighbour estimates are
explicit assumptions on the selected triples indexed by this set. -/
theorem badVertexSet_card_lt_520_mul
    (G : PhysicalGraph) (E : Finset G.Edge) (R : ℕ)
    (hR : 5 ≤ R)
    (hprob : (1 / 2 : ℝ) + 1 / (R : ℝ) <
      G.outsideLinearForestProbability E)
    (exceptional : BadVertexIndex G E → BadVertexIndex G E → Prop)
    [DecidableRel exceptional]
    (hcommon : ∀ i j, i ≠ j → ¬ exceptional i j →
      Module.finrank F₂
        (CommonSubspace
          (tripleConstraintSpace G (selectedTripleAtBadVertex G E i))
          (tripleConstraintSpace G (selectedTripleAtBadVertex G E j))) ≤ 1)
    (hpartners : ∀ i,
      ((Finset.univ.filter (fun j : BadVertexIndex G E => exceptional i j)).card : ℝ) ≤ 64) :
    (badVertexSet G E).card < 520 * R := by
  classical
  let ι := BadVertexIndex G E
  let edges : ι → Fin 3 → G.Edge := selectedTripleAtBadVertex G E
  let witness : ι → G.CycleSpace := selectedTripleWitnessAtBadVertex G E
  have hfeasible (i : ι) : allSelectedTriple G (edges i) (witness i) :=
    selectedTripleWitnessAtBadVertex_feasible G E i
  have hinjective (i : ι) : Function.Injective (edges i) :=
    (selectedTripleAtBadVertex_spec G E i).2.2.1
  have hincident (i : ι) (k : Fin 3) : G.incident (edges i k) i.1 :=
    (selectedTripleAtBadVertex_spec G E i).2.1 k
  have houtside (i : ι) (k : Fin 3) : edges i k ∉ E := by
    have heF := (selectedTripleAtBadVertex_spec G E i).1 k
    exact (Finset.mem_filter.mp heF).2.2.1
  have hsmall : (badVertexSet G E).card < 520 * R := by
    by_contra hnot
    have hcard : Fintype.card ι = (badVertexSet G E).card := by
      rw [Fintype.card_subtype]
      simp [ι, BadVertexIndex, badVertexSet]
    have hlarge : 520 * R ≤ (Fintype.card ι) := by
      have hlarge' : 520 * R ≤ (badVertexSet G E).card := by omega
      rw [hcard]
      exact hlarge'
    have hfalse := impossible_many_selected_triples
      G E R hR edges witness hfeasible exceptional hcommon hpartners
      (fun i => i.1) hinjective hincident houtside hprob hlarge
    exact hfalse.elim
  exact hsmall

/-- The bad-vertex cardinality estimate with the common-rank and partner
bounds discharged from the triple-star intersection theorem. -/
theorem badVertexSet_card_lt_520_mul_of_tripleStarBound
    (G : PhysicalGraph) (E : Finset G.Edge) (R : ℕ)
    (hR : 5 ≤ R)
    (hprob : (1 / 2 : ℝ) + 1 / (R : ℝ) <
      G.outsideLinearForestProbability E)
    (hstar : ∀ u v w : G.Vertex, u ≠ v → u ≠ w → v ≠ w →
      Module.finrank F₂ (tripleStarSpace G u v w) ≤ 1) :
    (badVertexSet G E).card < 520 * R := by
  classical
  let ι := BadVertexIndex G E
  let edges : ι → Fin 3 → G.Edge := selectedTripleAtBadVertex G E
  let exceptional : ι → ι → Prop := highCommonPartner G edges
  letI : DecidableRel exceptional := Classical.decRel exceptional
  have hcenters : Function.Injective (fun i : ι => i.1) := by
    intro i j hij
    exact Subtype.ext hij
  have hincident : ∀ i k, G.incident (edges i k) i.1 := by
    intro i k
    exact (selectedTripleAtBadVertex_spec G E i).2.1 k
  have hcommon : ∀ i j, i ≠ j → ¬ exceptional i j →
      Module.finrank F₂
        (CommonSubspace (tripleConstraintSpace G (edges i))
          (tripleConstraintSpace G (edges j))) ≤ 1 := by
    intro i j hij hnot
    exact commonRank_le_one_of_not_highCommonPartner G edges hij
      (by simpa [exceptional] using hnot)
  have hpartners : ∀ i,
      ((Finset.univ.filter (fun j : ι => exceptional i j)).card : ℝ) ≤ 64 := by
    simpa [exceptional] using
      (highCommonPartner_real_card_le_64 G edges (fun i : ι => i.1)
        hcenters hincident hstar)
  exact badVertexSet_card_lt_520_mul G E R hR hprob exceptional hcommon hpartners

end Erdos1016.Proof.BadVertexCardinalityBound
