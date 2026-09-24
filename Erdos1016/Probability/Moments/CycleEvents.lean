import Erdos1016.Cycles.Geometry.Supports

set_option autoImplicit false

/-!
# Exact one-cycle and two-cycle component probabilities

Sources: manuscript (4.3), (4.4), (12.1), (12.2).

The correction includes both actual inter-cycle edges and the change in
ORIGINAL exterior-component counts. Disjoint supports alone do not make the
events independent. All probabilities are on the full homogeneous owner
space; in the final application this is the literal one-apex graph.
-/

noncomputable section
open scoped BigOperators
namespace Erdos1016.BoundaryDecay

open BoundaryTrace SafeCore
local instance exactCycleMomentsDecidable (p : Prop) : Decidable p := Classical.propDecidable p

variable {G : PhysicalGraph}
namespace Cycle

def IsInduced (C : G.CycleWord) : Prop := internalEdges G (vertices C) = edges C

def chordCount (C : G.CycleWord) : ℕ :=
  (internalEdges G (vertices C)).card - length C

theorem internal_card_eq_length_add_chords (C : G.CycleWord) :
    (internalEdges G (vertices C)).card = length C + chordCount C := by
  have h := Finset.card_le_card (edges_subset_internal C)
  change length C ≤ (internalEdges G (vertices C)).card at h
  unfold chordCount
  omega

@[simp] theorem probability_eq_forced (C : G.CycleWord) :
    probability C = forcedProbability G (vertices C) (seed C) := rfl

/-- Allows chords and any positive number of original exterior components. -/
theorem probability_exact (hG : G.IsConnected) (C : G.CycleWord)
    (hc : ∀ v ∈ vertices C, G.degree v = 3) :
    probability C = dyadic
      (-(length C : ℤ) + chordCount C + G.originalExteriorComponents (vertices C) - 1) := by
  rw [probability_eq_forced, cubic_forcedProbability G hG _ hc]
  congr 1
  have h := internal_card_eq_length_add_chords C
  have hl := length_eq_vertices_card C
  omega



/-- Source (4.3): a short cycle's component event is never less likely than
2^{-D}, provided the original complement is nonempty. -/
theorem probability_ge_inverse_pow (hG : G.IsConnected) (C : G.CycleWord)
    (hc : ∀ v ∈ vertices C, G.degree v = 3)
    (v₀ : G.Vertex) (hv₀ : v₀ ∉ vertices C) (D : ℕ) (hD : length C ≤ D) :
    1 / (2 : ℝ) ^ D ≤ probability C := by
  have hcomp := originalExteriorComponents_pos G (vertices C) v₀ hv₀
  rw [probability_exact hG C hc, ← dyadic_neg_nat]
  apply dyadic_mono
  omega

/-- Source (12.1): inducedness and connected original complement give the
unamplified geometric weight exactly. -/
theorem probability_eq_weight (hG : G.IsConnected) (C : G.CycleWord)
    (hc : ∀ v ∈ vertices C, G.degree v = 3) (hi : IsInduced C)
    (hcomp : G.originalExteriorComponents (vertices C) = 1) :
    probability C = 1 / (2 : ℝ) ^ length C := by
  have hj : chordCount C = 0 := by
    unfold chordCount
    rw [hi]
    change (G.edgeSupport C.1).card - G.wordLength C.1 = 0
    rw [PhysicalGraph.wordLength]
    exact Nat.sub_self _
  rw [probability_exact hG C hc, hj, hcomp]
  simpa using dyadic_neg_nat (length C)

/-- The other cycle contributes no bit at an edge incident with a disjoint support. -/
theorem word_zero_at_disjoint_incidence (C D : G.CycleWord)
    (hCD : Disjoint (vertices C) (vertices D)) (e : G.Edge)
    (he : G.src e ∈ vertices C ∨ G.dst e ∈ vertices C) : D.1 e = 0 := by
  rcases he with hs | hd
  · apply word_zero_of_src_not_used D.1 e
    exact fun h => Finset.disjoint_left.1 hCD hs h
  · apply word_zero_of_dst_not_used D.1 e
    exact fun h => Finset.disjoint_left.1 hCD hd h

/-- A simultaneous pair is exactly one forced-region event on the union.
All edge labels between the cycles are required absent, in both descriptions. -/
theorem joint_event_iff_union (C D : G.CycleWord)
    (hCD : Disjoint (vertices C) (vertices D)) (x : G.CycleSpace) :
    (Event C x ∧ Event D x) ↔
      ForcedRegion G.traceNetwork (vertices C ∪ vertices D)
        ((seed C + seed D).1) x.1 := by
  constructor
  · rintro ⟨hC, hD⟩ e he
    change x.1 e = C.1 e + D.1 e
    change G.src e ∈ vertices C ∪ vertices D ∨
      G.dst e ∈ vertices C ∪ vertices D at he
    have hside : (G.src e ∈ vertices C ∨ G.dst e ∈ vertices C) ∨
        (G.src e ∈ vertices D ∨ G.dst e ∈ vertices D) := by
      simp only [Finset.mem_union] at he
      tauto
    rcases hside with hside | hside
    · rw [word_zero_at_disjoint_incidence C D hCD e hside, add_zero]
      exact hC e hside
    · rw [word_zero_at_disjoint_incidence D C hCD.symm e hside, zero_add]
      exact hD e hside
  · intro hu
    constructor
    · intro e he
      have h := hu e (by
        change G.src e ∈ vertices C ∪ vertices D ∨
          G.dst e ∈ vertices C ∪ vertices D
        change G.src e ∈ vertices C ∨ G.dst e ∈ vertices C at he
        simp only [Finset.mem_union]
        tauto)
      change x.1 e = C.1 e + D.1 e at h
      simpa only [word_zero_at_disjoint_incidence C D hCD e he, add_zero] using h
    · intro e he
      have h := hu e (by
        change G.src e ∈ vertices C ∪ vertices D ∨
          G.dst e ∈ vertices C ∪ vertices D
        change G.src e ∈ vertices D ∨ G.dst e ∈ vertices D at he
        simp only [Finset.mem_union]
        tauto)
      change x.1 e = C.1 e + D.1 e at h
      simpa only [word_zero_at_disjoint_incidence D C hCD.symm e he, zero_add] using h

/-- Source (4.4), without dividing by either event probability. It counts
actual inter-cycle edges, even when the rest of the owner has high degree. -/
theorem joint_probability_exact (hG : G.IsConnected) (C D : G.CycleWord)
    (hCD : Disjoint (vertices C) (vertices D))
    (hC : ∀ v ∈ vertices C, G.degree v = 3)
    (hD : ∀ v ∈ vertices D, G.degree v = 3) :
    Finite.density (fun x : G.CycleSpace => Event C x ∧ Event D x) =
      dyadic ((crossSize G (vertices C) (vertices D) : ℤ) +
        G.originalExteriorComponents (vertices C ∪ vertices D) -
        G.originalExteriorComponents (vertices C) -
        G.originalExteriorComponents (vertices D) + 1) * probability C * probability D := by
  have hU : ∀ v ∈ vertices C ∪ vertices D, G.degree v = 3 := by
    intro v hv
    rcases Finset.mem_union.1 hv with hv | hv
    · exact hC v hv
    · exact hD v hv
  have hevents : (fun x : G.CycleSpace => Event C x ∧ Event D x) =
      (fun x => ForcedRegion G.traceNetwork (vertices C ∪ vertices D)
        ((seed C + seed D).1) x.1) := by
    funext x
    exact propext (joint_event_iff_union C D hCD x)
  rw [hevents]
  change forcedProbability G (vertices C ∪ vertices D) (seed C + seed D) = _
  rw [cubic_forcedProbability G hG _ hU,
    probability_eq_forced, cubic_forcedProbability G hG _ hC,
    probability_eq_forced, cubic_forcedProbability G hG _ hD]
  rw [← dyadic_add, ← dyadic_add]
  congr 1
  have hi := internalEdges_union_card G (vertices C) (vertices D) hCD
  have hv := Finset.card_union_of_disjoint hCD
  omega

/-- The component-count compatibility condition required by the MANY branch. -/
theorem pairwise_probability_of_nonconflict (hG : G.IsConnected)
    (C D : G.CycleWord) (hCD : Disjoint (vertices C) (vertices D))
    (hC : ∀ v ∈ vertices C, G.degree v = 3)
    (hD : ∀ v ∈ vertices D, G.degree v = 3)
    (he : crossSize G (vertices C) (vertices D) = 0)
    (hc : G.originalExteriorComponents (vertices C ∪ vertices D) + 1 =
      G.originalExteriorComponents (vertices C) +
        G.originalExteriorComponents (vertices D)) :
    Finite.density (fun x : G.CycleSpace => Event C x ∧ Event D x) =
      probability C * probability D := by
  rw [joint_probability_exact hG C D hCD hC hD]
  have hz : ((crossSize G (vertices C) (vertices D) : ℤ) +
      G.originalExteriorComponents (vertices C ∪ vertices D) -
      G.originalExteriorComponents (vertices C) -
      G.originalExteriorComponents (vertices D) + 1) = 0 := by omega
  rw [hz, dyadic_zero, one_mul]



end Cycle
end Erdos1016.BoundaryDecay
