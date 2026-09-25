import Erdos1016.Cycles.Counting.LowDegreeVertexMass
import Erdos1016.Cycles.Counting.SimpleRunWeight

set_option autoImplicit false

/-! A finite family of all physical cycles through a length cutoff, with exact
trace-mass and vertex-load identities. The length index introduces no duplicates. -/
noncomputable section
open scoped BigOperators
namespace Erdos1016.Proof.LengthIndexedFamily
open Nonbacktracking BoundaryDecay FixedLengthVertexMass SimpleRunWeight

variable (H : PhysicalGraph)

abbrev Index := Σ ell : ℕ, CycleWordsAtLength H ell

def cycle (i : Index H) : H.CycleWord := i.2.1

def family (L : ℕ) : Finset (Index H) := by
  classical
  exact (Finset.Icc 1 L).sigma (fun ell => Finset.univ)

theorem cycle_injective : Function.Injective (cycle H) := by
  rintro ⟨ell, C⟩ ⟨k, D⟩ h
  have he : ell = k := C.2.symm.trans ((congrArg BoundaryDecay.Cycle.length h).trans D.2)
  subst k
  exact Sigma.ext rfl (heq_of_eq (Subtype.ext h))

@[simp] theorem cycle_length (i : Index H) : BoundaryDecay.Cycle.length (cycle H i) = i.1 := i.2.2

theorem mem_family_iff (L : ℕ) (i : Index H) :
    i ∈ family H L ↔ 1 ≤ i.1 ∧ i.1 ≤ L := by
  classical
  simp [family]

theorem total_weight (L : ℕ) :
    (∑ i ∈ family H L, (1 / (2 : ℝ) ^ BoundaryDecay.Cycle.length (cycle H i))) =
      ∑ ell ∈ Finset.Icc 1 L, cycleWordMassAtLength H ell := by
  classical
  rw [family, Finset.sum_sigma]
  apply Finset.sum_congr rfl
  intro ell hell
  simp only [cycle_length, Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
    cycleWordMassAtLength, one_div, inv_pow]

theorem vertex_weight (L : ℕ) (v : H.Vertex) :
    (∑ i ∈ family H L, if v ∈ Cycle.vertices (cycle H i) then
      (1 / (2 : ℝ) ^ BoundaryDecay.Cycle.length (cycle H i)) else 0) =
      ∑ ell ∈ Finset.Icc 1 L,
        ((cyclesAtVertex H ell v).card : ℝ) * (1 / 2 : ℝ) ^ ell := by
  classical
  rw [family, Finset.sum_sigma]
  apply Finset.sum_congr rfl
  intro ell hell
  rw [← Finset.sum_filter]
  simp only [cycle_length, Finset.sum_const, nsmul_eq_mul, one_div, inv_pow]
  rfl

theorem vertex_weight_le (hmax : ∀ v, H.degree v ≤ 3) (D L s : ℕ)
    (hg : ShortWalks.GirthGreater H.toSimpleGraph D)
    (hs : 0 < s) (hshort : 2 * s ≤ D) (v : H.Vertex) :
    (∑ i ∈ family H L, if v ∈ Cycle.vertices (cycle H i) then
      (1 / (2 : ℝ) ^ BoundaryDecay.Cycle.length (cycle H i)) else 0) ≤
      (3 / 2 : ℝ) * L * (1 / 2 : ℝ) ^ s := by
  rw [vertex_weight]
  exact LowDegreeVertexMass.lengthIndexed_vertex_mass_le H hmax D L s v hg hs hshort

end Erdos1016.Proof.LengthIndexedFamily
