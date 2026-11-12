import Erdos1016.ExactMaximumSupport.CubicReduction.MinimalCycles
import Erdos1016.Graph.Cubicization.IncidenceRealization

set_option autoImplicit false

/-!
# Individual cycles lift through incidence-path expansion

Projection reads the original edge labels and is injective on even words.
A nonzero even subword of a lifted cycle therefore projects to the whole
original cycle. Minimality, together with the subcubic degree bound, proves
that the lift is one connected cycle.
-/

noncomputable section

namespace Erdos1016.ExactMaximumSupport.CubicReduction

open ShortProof.IncidencePaths

variable (G : PhysicalGraph) (W : Finset G.Edge)

theorem incidence_isCycleWord (C : G.CycleWord) :
    (physical G W).IsCycleWord
      ((physicalCycleSpaceEquiv G W).symm ⟨C.1, C.2.2.1⟩).1 := by
  let c : G.CycleSpace := ⟨C.1, C.2.2.1⟩
  let y := (physicalCycleSpaceEquiv G W).symm c
  apply (asMultigraph_isCycleWord_iff (physical G W) y.1).1
  change (multigraph G W).IsCycleWord y.1
  apply subcubic_isCycleWord_of_minimal (multigraph G W)
    (multigraph_degree_le_three G W) ⟨y.1, y.2⟩
  · intro hy
    have hy' : y = 0 := Subtype.ext hy
    have hc : c = 0 := by
      have he := congrArg (physicalCycleSpaceEquiv G W) hy'
      simpa only [y, LinearEquiv.apply_symm_apply, map_zero] using he
    exact C.2.1 (congrArg (fun z : G.CycleSpace => z.1) hc)
  · intro z hz hsub
    let p := multigraphCycleSpaceEquiv G W z
    have hp : p.1 ≠ 0 := by
      intro hp0
      have hp' : p = 0 := Subtype.ext hp0
      have hz' : z = 0 := (multigraphCycleSpaceEquiv G W).injective
        (by simpa only [map_zero] using hp')
      exact hz (congrArg (fun z : (multigraph G W).CycleSpace => z.1) hz')
    have hpc : p.1 = C.1 := physical_even_subword_eq G C p hp (by
      intro e he
      have h := hsub (edgeLabels G W (Sum.inr e)) he
      change (physicalCycleSpaceEquiv G W y).1 e ≠ 0 at h
      simpa only [y, LinearEquiv.apply_symm_apply] using h)
    have hproj : multigraphCycleSpaceEquiv G W z =
        multigraphCycleSpaceEquiv G W ⟨y.1, y.2⟩ := by
      change p = physicalCycleSpaceEquiv G W y
      rw [show physicalCycleSpaceEquiv G W y = c from
        (physicalCycleSpaceEquiv G W).apply_symm_apply c]
      exact Subtype.ext hpc
    exact congrArg (fun z : (multigraph G W).CycleSpace => z.1)
      ((multigraphCycleSpaceEquiv G W).injective hproj)

def incidenceCycleEmbedding : G.CycleWord ↪ (physical G W).CycleWord where
  toFun C := ⟨_, incidence_isCycleWord G W C⟩
  inj' := by
    intro C D h
    have h' := congrArg Subtype.val h
    have heq := (physicalCycleSpaceEquiv G W).symm.injective (Subtype.ext h')
    apply Subtype.ext
    exact congrArg (fun z : G.CycleSpace => z.1) heq

theorem cycleCount_le_incidence :
    Fintype.card G.CycleWord ≤ Fintype.card (physical G W).CycleWord :=
  Fintype.card_le_of_injective (incidenceCycleEmbedding G W)
    (incidenceCycleEmbedding G W).injective

end Erdos1016.ExactMaximumSupport.CubicReduction
