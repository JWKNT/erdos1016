import Erdos1016.CycleSpace.Graphical.TripleStarReduction

set_option autoImplicit false

noncomputable section

namespace Erdos1016.Proof.GraphicalAbstractLinks

open Erdos1016

private theorem double_zero (x : F₂) : x + x = 0 := by
  have h2 : (2 : F₂) = 0 := ZMod.natCast_self 2
  calc
    x + x = (2 : F₂) * x := by ring
    _ = 0 := by rw [h2]; simp

/-- Sum of the link coordinates. -/
def totalLinkParity {ι : Type*} [Fintype ι] : (ι → F₂) →ₗ[F₂] F₂ where
  toFun z := ∑ i, z i
  map_add' x y := by simp [Finset.sum_add_distrib]
  map_smul' a x := by simp [Finset.mul_sum]

/-- The subspace of even link assignments. -/
def EvenLinkAssignments {ι : Type*} [Fintype ι] : Submodule F₂ (ι → F₂) :=
  LinearMap.ker totalLinkParity

/-- The assignment supported on two distinct links. -/
def pairAssignment {ι : Type*} [DecidableEq ι] (i j : ι) : ι → F₂ :=
  fun k => (if k = i then 1 else 0) + (if k = j then 1 else 0)

/-- Span of all pair assignments. -/
def pairAssignmentSpan {ι : Type*} [Fintype ι] [DecidableEq ι] :
    Submodule F₂ (ι → F₂) :=
  Submodule.span F₂ {z | ∃ i j, i ≠ j ∧ z = pairAssignment i j}

theorem pairAssignment_mem_even {ι : Type*} [Fintype ι] [DecidableEq ι]
    (i j : ι) : pairAssignment i j ∈ EvenLinkAssignments (ι := ι) := by
  change totalLinkParity (pairAssignment i j) = 0
  change (Finset.univ.sum (fun k : ι =>
    (if k = i then (1 : F₂) else 0) + (if k = j then (1 : F₂) else 0))) = 0
  rw [Finset.sum_add_distrib]
  have hi : (∑ k : ι, if k = i then (1 : F₂) else 0) = 1 := by simp
  have hj : (∑ k : ι, if k = j then (1 : F₂) else 0) = 1 := by simp
  rw [hi, hj]
  exact double_zero 1

theorem pairAssignmentSpan_le_even {ι : Type*} [Fintype ι] [DecidableEq ι] :
    pairAssignmentSpan (ι := ι) ≤ EvenLinkAssignments (ι := ι) := by
  change Submodule.span F₂ {z : ι → F₂ | ∃ i j, i ≠ j ∧ z = pairAssignment i j} ≤ _
  apply Submodule.span_le.2
  rintro z ⟨i, j, _hij, rfl⟩
  exact pairAssignment_mem_even (ι := ι) i j

/-- The pair assignments generate every even-parity vector. -/
theorem pairAssignmentSpan_eq_even {ι : Type*} [Fintype ι] [DecidableEq ι]
    [Nonempty ι] : pairAssignmentSpan (ι := ι) = EvenLinkAssignments (ι := ι) := by
  apply le_antisymm (pairAssignmentSpan_le_even (ι := ι))
  intro z hz
  classical
  let b : ι := Classical.choice ‹Nonempty ι›
  have htotal : ∑ i, z i = 0 := by
    simpa [EvenLinkAssignments, totalLinkParity] using hz
  have hformula : z = ∑ i ∈ Finset.univ.erase b, z i • pairAssignment i b := by
    ext j
    by_cases hj : j = b
    · subst j
      have hsplit := Finset.sum_erase_add (s := Finset.univ) (a := b) (f := z)
        (Finset.mem_univ b)
      have hsum : (∑ i ∈ Finset.univ.erase b, z i) + z b = 0 :=
        hsplit.trans htotal
      have hsum' : (∑ i ∈ Finset.univ.erase b, z i) = z b := by
        let A := ∑ i ∈ Finset.univ.erase b, z i
        calc
          A = A + 0 := by simp
          _ = A + (z b + z b) := by rw [double_zero]
          _ = (A + z b) + z b := by abel
          _ = 0 + z b := by rw [hsum]
          _ = z b := by simp
      have heval : (∑ i ∈ Finset.univ.erase b,
          z i • pairAssignment i b) b = ∑ i ∈ Finset.univ.erase b, z i := by
        rw [Finset.sum_apply]
        apply Finset.sum_congr rfl
        intro i hi
        have hne : i ≠ b := (Finset.mem_erase.mp hi).1
        simp [pairAssignment, hne, hne.symm]
      exact hsum'.symm.trans heval.symm
    · have hmem : j ∈ Finset.univ.erase b := Finset.mem_erase.mpr ⟨hj, Finset.mem_univ _⟩
      have heval : (∑ i ∈ Finset.univ.erase b,
          z i • pairAssignment i b) j = z j := by
        rw [Finset.sum_apply]
        rw [Finset.sum_eq_single j]
        · simp [pairAssignment, hj]
        · intro i hi hne
          simp [pairAssignment, hj, hne, hne.symm]
        · intro hnot
          exact (hnot hmem).elim
      exact heval.symm
  rw [hformula]
  apply Submodule.sum_mem
  intro i hi
  apply Submodule.smul_mem
  apply Submodule.subset_span
  exact ⟨i, b, (Finset.mem_erase.mp hi).1, rfl⟩

/-- A finite system of link cuts together with pair-path words witnessing every
two-link assignment. `cycleWords` is the cycle subspace of the ambient edge-word
space; the coordinate and parity conditions are the consequences of a partition
of the u-star into link cuts. -/
structure LinkSystem (E ι : Type*) [Fintype E] [Fintype ι] [DecidableEq ι] where
  cuts : ι → Finset E
  cycleWords : Submodule F₂ (E → F₂)
  pairPathWord : ∀ i j, i ≠ j → E → F₂
  pairPathWord_mem : ∀ i j hij, pairPathWord i j hij ∈ cycleWords
  pairPathWord_coordinates : ∀ i j hij k,
    (∑ e ∈ cuts k, pairPathWord i j hij e) = pairAssignment i j k
  every_cycle_even : ∀ x ∈ cycleWords,
    ∑ i, (∑ e ∈ cuts i, x e) = 0









end Erdos1016.Proof.GraphicalAbstractLinks
