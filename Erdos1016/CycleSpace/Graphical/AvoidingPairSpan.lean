import Erdos1016.CycleSpace.Graphical.LinkFactorizationStarBound

set_option autoImplicit false

noncomputable section

namespace Erdos1016.Proof.GraphicalTripleStarBoundGraphAway

open Erdos1016
open Erdos1016.Proof.GraphicalAbstractLinks
open Erdos1016.Proof.GraphicalLinkMap
open Erdos1016.Proof.GraphicalLinkPairWitnesses
open Erdos1016.Proof.GraphicalTripleStarBoundGraph
open Erdos1016.Proof.GraphicalTripleStarBound
open Erdos1016.Proof.GraphicalCommonInformation

local notation "F₂" => ZMod 2

local instance graphPropDecidable (p : Prop) : Decidable p := Classical.propDecidable p

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Span of pair assignments supported away from the distinguished index. -/
def awayPairSpan (k : ι) : Submodule F₂ (EvenLinkAssignments (ι := ι)) :=
  Submodule.span F₂ {z | ∃ i j, i ≠ j ∧ i ≠ k ∧ j ≠ k ∧
    z.1 = pairAssignment i j}

private theorem two_eq_zero (x : F₂) : x + x = 0 := by
  have h : (2 : F₂) = 0 := ZMod.natCast_self 2
  calc
    x + x = (2 : F₂) * x := by ring
    _ = 0 := by rw [h]; simp

/-- Generic algebra fact: an even assignment with zero k-coordinate is spanned
by pair assignments whose two coordinates both differ from k. -/
theorem evenAssignmentsAway_le_awayPairSpan (k : ι) :
    evenAssignmentsAway (ι := ι) k ≤ awayPairSpan (ι := ι) k := by
  classical
  intro z hz
  change z.1 k = 0 at hz
  by_cases hex : ∃ b : ι, b ≠ k
  · obtain ⟨b, hbk⟩ := hex
    have htotal : ∑ i, z.1 i = 0 := by
      have h := z.2
      change totalLinkParity z.1 = 0 at h
      change (∑ i, z.1 i) = 0 at h
      exact h
    let S := (Finset.univ.erase k).erase b
    have hsumK : (∑ i ∈ Finset.univ.erase k, z.1 i) = 0 := by
      have hs := Finset.sum_erase_add (s := Finset.univ) (a := k)
        (f := z.1) (Finset.mem_univ k)
      rw [hz] at hs
      simpa [htotal] using hs
    have hsplitB := Finset.sum_erase_add (s := Finset.univ.erase k)
      (a := b) (f := z.1) (Finset.mem_erase.mpr ⟨hbk, Finset.mem_univ b⟩)
    have hsumB : (∑ i ∈ S, z.1 i) = z.1 b := by
      have hzero : (∑ i ∈ S, z.1 i) + z.1 b = 0 := by
        calc
          _ = ∑ i ∈ Finset.univ.erase k, z.1 i := hsplitB
          _ = 0 := hsumK
      have := two_eq_zero (z.1 b)
      calc
        (∑ i ∈ S, z.1 i) = (∑ i ∈ S, z.1 i) + 0 := by simp
        _ = (∑ i ∈ S, z.1 i) + (z.1 b + z.1 b) := by rw [this]
        _ = ((∑ i ∈ S, z.1 i) + z.1 b) + z.1 b := by abel
        _ = 0 + z.1 b := by rw [hzero]
        _ = z.1 b := by simp
    have hformula : z.1 = ∑ i ∈ S, z.1 i • pairAssignment i b := by
      ext j
      by_cases hjk : j = k
      · subst j
        have heval : (∑ i ∈ S, z.1 i • pairAssignment i b) k = 0 := by
          rw [Finset.sum_apply]
          apply Finset.sum_eq_zero
          intro i hi
          have hik : i ≠ k := (Finset.mem_erase.mp (Finset.mem_erase.mp hi).2).1
          have hbk' : b ≠ k := hbk
          simp [pairAssignment, hik.symm, hbk.symm]
        simpa [hz] using heval.symm
      · by_cases hjb : j = b
        · subst j
          have heval : (∑ i ∈ S, z.1 i • pairAssignment i b) b =
              ∑ i ∈ S, z.1 i := by
            rw [Finset.sum_apply]
            apply Finset.sum_congr rfl
            intro i hi
            have hib : i ≠ b := (Finset.mem_erase.mp hi).1
            simp [pairAssignment, hib.symm, mul_one]
          rw [heval, hsumB]
        · have hjS : j ∈ S := by
            simp [S, hjk, hjb]
          have heval : (∑ i ∈ S, z.1 i • pairAssignment i b) j = z.1 j := by
            rw [Finset.sum_apply]
            rw [Finset.sum_eq_single j]
            · simp [pairAssignment, hjb]
            · intro i hi hne
              have hji : j ≠ i := fun h => hne h.symm
              simp [pairAssignment, hji, hjb]
            · intro hnot
              exact (hnot hjS).elim
          exact heval.symm
    have hformulaSub : z = ∑ i ∈ S, z.1 i •
        (⟨pairAssignment i b, pairAssignment_mem_even i b⟩ : EvenLinkAssignments (ι := ι)) := by
      apply Subtype.ext
      change z.1 = EvenLinkAssignments.subtype (∑ i ∈ S, z.1 i •
        (⟨pairAssignment i b, pairAssignment_mem_even i b⟩ : EvenLinkAssignments (ι := ι)))
      rw [map_sum]
      simp only [map_smul]
      exact hformula
    rw [hformulaSub]
    apply Submodule.sum_mem
    intro i hi
    apply Submodule.smul_mem
    apply Submodule.subset_span
    refine ⟨i, b, ?_, ?_, hbk, ?_⟩
    · exact (Finset.mem_erase.mp hi).1
    · exact (Finset.mem_erase.mp (Finset.mem_erase.mp hi).2).1
    · rfl
  · have hzero : z = 0 := by
      apply Subtype.ext
      ext j
      have hj : j = k := by
        by_cases h : j = k
        · exact h
        · exact (hex ⟨j, h⟩).elim
      subst j
      exact hz
    rw [hzero]
    exact Submodule.zero_mem _

/-- The component-separation hypothesis lets every off-k pair generator be
realized by a cycle avoiding w, hence the full even subspace with coordinate
k zero lies in the restricted link-map range. -/
theorem evenAssignmentsAway_le_avoiding_range
    (G : PhysicalGraph) (u v w : G.Vertex)
    (huv : u ≠ v) (huw : u ≠ w) (hvw : v ≠ w)
    (k : LinkIndex G u v)
    (hcomp : ∀ c : ComponentLink G u v,
      (Sum.inr c : LinkIndex G u v) ≠ k →
        w ∉ componentVertices G u v c.1) :
    evenAssignmentsAway (ι := LinkIndex G u v) k ≤
      LinearMap.range
        ((linkMapToEven G u v huv).comp (cyclesAvoidingVertex G w).subtype) := by
  classical
  have hspan := evenAssignmentsAway_le_awayPairSpan (ι := LinkIndex G u v) k
  apply le_trans hspan
  apply Submodule.span_le.2
  rintro z ⟨i, j, hij, hik, hjk, hz⟩
  obtain ⟨x, hxavoid, hxmap⟩ :=
    pairLinkMap_cycleWitness_avoiding G u v w huv huw.symm hvw.symm
      k i j hij hik hjk hcomp
  refine ⟨⟨x, hxavoid⟩, ?_⟩
  apply Subtype.ext
  rw [hz]
  exact hxmap

end Erdos1016.Proof.GraphicalTripleStarBoundGraphAway
