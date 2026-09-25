import Erdos1016.Probability.Cylinders.RegionCycleEvents

set_option autoImplicit false

/-!
# Fixed even seeds and incident-region events

On a zero cut, the internal even coordinates are uniformly distributed.
Prescribing one internal seed contributes the reciprocal internal-cycle-space
cardinality; disjoint regions contribute the product of these factors.
-/

noncomputable section
namespace Erdos1016.FiniteMultiGraph
open BoundaryTrace BoundaryDecay

local instance seedRegionDecidable (p : Prop) : Decidable p := Classical.propDecidable p

/-- Fix every edge incident to the region to its coordinate in the seed. -/
def IncidentSeed (G : FiniteMultiGraph) (U : Finset G.Vertex)
    (seed : G.internalCycleSpace U) (x : G.CycleSpace) : Prop :=
  ∀ e, G.src e ∈ U ∨ G.dst e ∈ U → x.1 e = seed.1.1 e

/-- Incident prescription is exactly a zero cut and the fixed internal word. -/
theorem incidentSeed_iff (G : FiniteMultiGraph) (U : Finset G.Vertex)
    (seed : G.internalCycleSpace U) (x : G.CycleSpace) :
    G.IncidentSeed U seed x ↔ x ∈ G.zeroCutSpace U ∧
      G.restrictEdges (G.internalEdges U) x.1 = seed.1.1 := by
  constructor
  · intro hx
    constructor
    · rw [G.mem_zeroCutSpace_iff]
      intro e he
      have hcut := (Finset.mem_filter.mp he).2
      have hincident : G.src e ∈ U ∨ G.dst e ∈ U := by tauto
      rw [hx e hincident]
      apply seed.2 e
      simp only [internalEdges, Finset.mem_filter, Finset.mem_univ, true_and]
      tauto
    · funext e
      by_cases he : e ∈ G.internalEdges U
      · simpa [restrictEdges, he] using hx e (Or.inl (Finset.mem_filter.mp he).2.1)
      · simp [restrictEdges, he, seed.2 e he]
  · rintro ⟨hzero, hword⟩ e he
    by_cases hin : e ∈ G.internalEdges U
    · have heq := congrFun hword e
      simpa [restrictEdges, hin] using heq
    · have hcut : e ∈ G.cutEdges U := by
        simp only [cutEdges, internalEdges, Finset.mem_filter, Finset.mem_univ, true_and] at hin ⊢
        tauto
      rw [(G.mem_zeroCutSpace_iff U x).mp hzero e hcut, seed.2 e hin]

theorem restrictInternal_eq_iff (G : FiniteMultiGraph) (U : Finset G.Vertex)
    (seed : G.internalCycleSpace U) (x : G.zeroCutSpace U) :
    G.restrictInternal U x = seed ↔ G.restrictEdges (G.internalEdges U) x.1.1 = seed.1.1 := by
  constructor
  · exact fun he => congrArg (fun z : G.internalCycleSpace U => z.1.1) he
  · intro he
    apply Subtype.ext; apply Subtype.ext
    exact he

/-- The exact single-region affine cylinder law. -/
theorem incidentSeed_density (G : FiniteMultiGraph) (U : Finset G.Vertex)
    (seed : G.internalCycleSpace U) :
    Finite.density (G.IncidentSeed U seed) =
      (1 / (Fintype.card (G.internalCycleSpace U) : ℝ)) *
        Finite.density (fun x : G.CycleSpace => x ∈ G.zeroCutSpace U) := by
  have he : G.IncidentSeed U seed = fun x => x ∈ G.zeroCutSpace U ∧
      G.restrictEdges (G.internalEdges U) x.1 = seed.1.1 := by
    funext x
    exact propext (G.incidentSeed_iff U seed x)
  rw [he, Finite.density_and_eq_density_subtype]
  have hrestr : (fun x : G.zeroCutSpace U => G.restrictEdges (G.internalEdges U) x.1.1 = seed.1.1) =
      fun x => G.restrictInternal U x = seed := by
    funext x
    exact propext (G.restrictInternal_eq_iff U seed x).symm
  rw [hrestr, density_surjective_linear (G.restrictInternal U)
    (G.restrictInternal_surjective U) (fun y => y = seed)]
  have hpoint : Finite.density (fun y : G.internalCycleSpace U => y = seed) =
      1 / (Fintype.card (G.internalCycleSpace U) : ℝ) := by
    unfold Finite.density Finite.count
    rw [Finset.sum_eq_single seed]
    · simp
    · intro z hz hne
      simp [hne]
    · simp
  rw [hpoint, mul_comm]

/-- Two disjoint internal seeds give the product of the same single-region
factors. Consequently their correlation is exactly the zero-cut correlation. -/
theorem incidentSeed_pair_density (G : FiniteMultiGraph) (U V : Finset G.Vertex)
    (hUV : Disjoint U V) (seed : G.internalCycleSpace U) (seed' : G.internalCycleSpace V) :
    Finite.density (fun x => G.IncidentSeed U seed x ∧ G.IncidentSeed V seed' x) =
      (1 / (Fintype.card (G.internalCycleSpace U) : ℝ)) *
        (1 / (Fintype.card (G.internalCycleSpace V) : ℝ)) *
          Finite.density (fun x : G.CycleSpace =>
            x ∈ G.zeroCutSpace U ∧ x ∈ G.zeroCutSpace V) := by
  have he : (fun x => G.IncidentSeed U seed x ∧ G.IncidentSeed V seed' x) =
      fun x : G.CycleSpace => x ∈ G.zeroCutSpace U ⊓ G.zeroCutSpace V ∧
        (G.restrictEdges (G.internalEdges U) x.1 = seed.1.1 ∧
         G.restrictEdges (G.internalEdges V) x.1 = seed'.1.1) := by
    funext x
    apply propext
    simp only [G.incidentSeed_iff, Submodule.mem_inf]
    tauto
  rw [he, Finite.density_and_eq_density_subtype]
  have hrestr : (fun x : ↥(G.zeroCutSpace U ⊓ G.zeroCutSpace V) =>
      G.restrictEdges (G.internalEdges U) x.1.1 = seed.1.1 ∧
      G.restrictEdges (G.internalEdges V) x.1.1 = seed'.1.1) =
      fun x => (G.restrictInternalPair U V x).1 = seed ∧
        (G.restrictInternalPair U V x).2 = seed' := by
    funext x
    exact propext (and_congr (G.restrictInternal_eq_iff U seed ⟨x.1, x.2.1⟩).symm
      (G.restrictInternal_eq_iff V seed' ⟨x.1, x.2.2⟩).symm)
  rw [hrestr, density_surjective_linear (G.restrictInternalPair U V)
    (G.restrictInternalPair_surjective U V hUV) (fun y => y.1 = seed ∧ y.2 = seed'),
    Finite.density_prod_and (fun a : G.internalCycleSpace U => a = seed)
      (fun b : G.internalCycleSpace V => b = seed')]
  have hpointU : Finite.density (fun z : G.internalCycleSpace U => z = seed) =
      1 / (Fintype.card (G.internalCycleSpace U) : ℝ) := by
    unfold Finite.density Finite.count
    rw [Finset.sum_eq_single seed]
    · simp
    · intro z hz hne
      simp [hne]
    · simp
  have hpointV : Finite.density (fun z : G.internalCycleSpace V => z = seed') =
      1 / (Fintype.card (G.internalCycleSpace V) : ℝ) := by
    unfold Finite.density Finite.count
    rw [Finset.sum_eq_single seed']
    · simp
    · intro z hz hne
      simp [hne]
    · simp
  rw [hpointU, hpointV]
  change _ = _ * _ * _
  have hpred : (Membership.mem (G.zeroCutSpace U ⊓ G.zeroCutSpace V) : G.CycleSpace → Prop) =
      fun x => x ∈ G.zeroCutSpace U ∧ x ∈ G.zeroCutSpace V := rfl
  rw [hpred]
  ring

theorem incidentSeed_density_pos (G : FiniteMultiGraph) (U : Finset G.Vertex)
    (seed : G.internalCycleSpace U) : 0 < Finite.density (G.IncidentSeed U seed) := by
  rw [G.incidentSeed_density U seed]
  apply mul_pos (by positivity)
  have he : (fun x : G.CycleSpace => x ∈ G.zeroCutSpace U) =
      fun x => ∀ e ∈ G.cutEdges U, x.1 e = 0 := by
    funext x
    exact propext (G.mem_zeroCutSpace_iff U x)
  rw [he]
  exact (by positivity : (0 : ℝ) < 1 / 2 ^ (G.cutEdges U).card).trans_le
    (G.zeroCoordinates_probability_ge (G.cutEdges U))

end Erdos1016.FiniteMultiGraph
