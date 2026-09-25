import Erdos1016.Cycles.Counting.TraceCycleMass
import Erdos1016.Cycles.Filtering.ReturnMassLoss

set_option autoImplicit false

noncomputable section

namespace Erdos1016.Proof.LengthPartition

open scoped BigOperators
open Erdos1016.BoundaryDecay
open Erdos1016.Nonbacktracking
open Erdos1016.Proof.RejectedCycleEncoding
open Erdos1016.Proof.ReturnMassLoss
open Erdos1016.Proof.SimpleRunWeight

variable (G : Erdos1016.PhysicalGraph)

local instance cycleWordDecidableEq : DecidableEq G.CycleWord := Classical.decEq _

private def shortSubtype (L : ℕ) :=
  {C : G.CycleWord // C ∈ shortCycleWords G L}

private def indexedSubtype (L : ℕ) :=
  Σ ell : {ell : ℕ // ell ∈ Finset.Icc 1 L}, CycleWordsAtLength G ell.1

private noncomputable instance shortSubtypeFintype (L : ℕ) :
    Fintype (shortSubtype G L) := by
  classical
  exact Fintype.ofInjective Subtype.val Subtype.val_injective

private noncomputable instance lengthSubtypeFintype (L : ℕ) :
    Fintype {ell : ℕ // ell ∈ Finset.Icc 1 L} := by
  apply Fintype.ofInjective
    (fun x : {ell : ℕ // ell ∈ Finset.Icc 1 L} =>
      (⟨x.1, Nat.lt_succ_of_le (Finset.mem_Icc.mp x.2).2⟩ : Fin (L + 1)))
  intro a b hab
  apply Subtype.ext
  exact congrArg Fin.val hab

private noncomputable instance indexedSubtypeFintype (L : ℕ) :
    Fintype (indexedSubtype G L) := by
  classical
  dsimp [indexedSubtype]
  infer_instance

private theorem cycleLength_pos (C : G.CycleWord) :
    0 < Erdos1016.BoundaryDecay.Cycle.length C := by
  have hcard : 0 < (Erdos1016.BoundaryDecay.Cycle.vertices C).card :=
    Finset.card_pos.mpr (Erdos1016.BoundaryDecay.Cycle.vertices_nonempty C)
  have hlen := Erdos1016.BoundaryDecay.Cycle.length_eq_vertices_card C
  rw [hlen]
  exact hcard

private noncomputable def shortToIndexed (L : ℕ) : shortSubtype G L → indexedSubtype G L := by
  intro C
  let ell := Erdos1016.BoundaryDecay.Cycle.length C.1
  have hshort : Erdos1016.BoundaryDecay.Cycle.length C.1 ≤ L := by
    exact (Finset.mem_filter.mp C.2).2
  refine ⟨⟨ell, Finset.mem_Icc.mpr ⟨cycleLength_pos G C.1, hshort⟩⟩,
    ⟨C.1, rfl⟩⟩

private noncomputable def indexedToShort (L : ℕ) : indexedSubtype G L → shortSubtype G L := by
  intro x
  refine ⟨x.2.1, ?_⟩
  apply Finset.mem_filter.mpr
  refine ⟨Finset.mem_univ _, ?_⟩
  exact x.2.2.le.trans (Finset.mem_Icc.mp x.1.2).2

private noncomputable def shortIndexedEquiv (L : ℕ) : shortSubtype G L ≃ indexedSubtype G L where
  toFun := shortToIndexed G L
  invFun := indexedToShort G L
  left_inv C := by
    apply Subtype.ext
    rfl
  right_inv x := by
    rcases x with ⟨⟨ell, hell⟩, ⟨C, hlen⟩⟩
    cases hlen
    rfl

/-- The mass of all cycle words through length `L` is exactly the sum of its
length-indexed fibers. -/
theorem shortCycleMass_eq_lengthIndexedMass (L : ℕ) :
    shortCycleMass G L =
      ∑ ell ∈ Finset.Icc 1 L, cycleWordMassAtLength G ell := by
  classical
  let f : shortSubtype G L → ℝ := fun C =>
    (1 / 2 : ℝ) ^ G.wordLength C.1.1
  have hsource : shortCycleMass G L = ∑ C : shortSubtype G L, f C := by
    unfold shortCycleMass f shortSubtype
    exact Finset.sum_subtype (shortCycleWords G L) (by intro C; rfl)
      (fun C => cycleWordMass G C)
  rw [hsource]
  calc
    (∑ C : shortSubtype G L, f C) =
        ∑ x : indexedSubtype G L, f ((shortIndexedEquiv G L).symm x) := by
          apply Fintype.sum_equiv (shortIndexedEquiv G L)
          intro C
          simp [f, shortIndexedEquiv, shortToIndexed, indexedToShort]
    _ = ∑ ell : {ell : ℕ // ell ∈ Finset.Icc 1 L},
          ∑ C : CycleWordsAtLength G ell.1,
            (1 / 2 : ℝ) ^ G.wordLength C.1.1 := by
          simp only [indexedSubtype, Fintype.sum_sigma]
          apply Fintype.sum_congr
          intro ell
          apply Fintype.sum_congr
          intro C
          simp only [shortIndexedEquiv, Equiv.symm, indexedToShort]
          rfl
    _ = ∑ ell ∈ Finset.Icc 1 L, cycleWordMassAtLength G ell := by
          have hlengthMass (ell : {ell : ℕ // ell ∈ Finset.Icc 1 L}) :
              (∑ C : CycleWordsAtLength G ell.1,
                (1 / 2 : ℝ) ^ G.wordLength C.1.1) =
                cycleWordMassAtLength G ell.1 := by
            unfold cycleWordMassAtLength
            calc
              (∑ C : CycleWordsAtLength G ell.1,
                  (1 / 2 : ℝ) ^ G.wordLength C.1.1) =
                  ∑ C : CycleWordsAtLength G ell.1, (1 / 2 : ℝ) ^ ell.1 := by
                    apply Fintype.sum_congr
                    intro C
                    have hlen : G.wordLength C.1.1 = ell.1 := by
                      simpa [Erdos1016.BoundaryDecay.Cycle.length] using C.2
                    rw [hlen]
              _ = (Fintype.card (CycleWordsAtLength G ell.1) : ℝ) *
                  (1 / 2 : ℝ) ^ ell.1 := by
                    rw [Fintype.card_eq_sum_ones]
                    simp [Finset.sum_mul, mul_comm]
          calc
            (∑ ell : {ell : ℕ // ell ∈ Finset.Icc 1 L},
                ∑ C : CycleWordsAtLength G ell.1,
                  (1 / 2 : ℝ) ^ G.wordLength C.1.1) =
                ∑ ell : {ell : ℕ // ell ∈ Finset.Icc 1 L},
                  cycleWordMassAtLength G ell.1 := by
                    apply Fintype.sum_congr
                    intro ell
                    exact hlengthMass ell
            _ = ∑ ell ∈ Finset.Icc 1 L, cycleWordMassAtLength G ell := by
                    symm
                    exact Finset.sum_subtype (Finset.Icc 1 L) (by intro ell; rfl)
                      (cycleWordMassAtLength G)

/-- Collision charging and the run-to-cycle fiber bound jointly give the
length-indexed lower trace mass, which is the same physical short-cycle mass. -/
theorem shortCycleMass_ge_trace_after_collision (L s D : ℕ)
    (hmin : ∀ v : G.Vertex, 2 ≤ G.degree v)
    (hmax : ∀ v : G.Vertex, G.degree v ≤ 3)
    (hg : ShortWalks.GirthGreater G.toSimpleGraph D)
    (hshort : 2 * s ≤ D) (hs : 0 < s) :
    (1 - (9 / 4 : ℝ) * (L : ℝ) ^ 2 * (1 / 2 : ℝ) ^ s) *
        nonbacktrackingTraceMass (G := G) L ≤ shortCycleMass G L := by
  have hphysical :=
    TraceCycleMass.cycleWordMass_sum_ge_one_sub_collisionError
      G L s D hmin hmax hg hshort hs
  rw [shortCycleMass_eq_lengthIndexedMass G L]
  simpa [SimpleRunWeight.cycleWordMassAtLength] using hphysical



end Erdos1016.Proof.LengthPartition

end
