import Erdos1016.Cycles.Counting.EncodedSuffixSupport
import Erdos1016.Cycles.Geometry.PrunedIncidenceLabels
import Erdos1016.Probability.Conditional.BranchWeights
import Erdos1016.Cycles.Geometry.PhysicalCycleRestriction
import Erdos1016.Probability.Conditional.CycleNeighborhood

set_option autoImplicit false
set_option maxHeartbeats 800000

noncomputable section

namespace Erdos1016.Proof.ResidualCoreCycleLoad

open scoped BigOperators
open Nonbacktracking Nonbacktracking.FiniteTwoCore BoundaryDecay SafeCore
open PhysicalCycleEmbedding CycleExtensionProbability
open ConditionalBranchWeights WeightedCycleLoad WalkPrefix
open FixedLengthVertexMass

local instance (p : Prop) : Decidable p := Classical.propDecidable p

/-- The actual conditional per-vertex load. Walks are counted only on the
ordinary part of the full residual two-core; weights still use full core
degrees. All lost-incidence labels and their spacing are constructed from
the complementary trees. -/
theorem vertexLoad_le
    (G : PhysicalGraph) (J : Finset G.Vertex) (F E : Finset G.CycleWord)
    (K q Δ D s L : ℕ)
    (hK : 2 ≤ K) (hΔ : 0 < Δ) (hΔq : Δ ≤ q - 2 * K + 1)
    (hs : 0 < s) (hshort : 2 * s ≤ D)
    (hcubic : ∀ v ∈ J, G.degree v = 3)
    (hno : CycleSupply.NoShortCycles G J D)
    (hFJ : ∀ C ∈ F, Cycle.vertices C ⊆ J)
    (hFdisj : ∀ C ∈ F, ∀ A ∈ F, C ≠ A → Disjoint (Cycle.vertices C) (Cycle.vertices A))
    (hreturn : ∀ C ∈ F, ExternalReturnFilter.NoShortExternalReturnWithin G J (Cycle.vertices C) q)
    (hEJ : ∀ C ∈ E, Cycle.vertices C ⊆ J)
    (hED : ∀ C ∈ E, Disjoint (tupleVertices F) (Cycle.vertices C))
    (hinduced : ∀ C ∈ E, Cycle.IsInduced C)
    (hlen : ∀ C ∈ E, s < BoundaryDecay.Cycle.length C ∧ BoundaryDecay.Cycle.length C ≤ L)
    (hcomp : ∀ C ∈ E, ∃ B ∈ components G (tupleVertices F ∪ Cycle.vertices C)ᶜ,
      ∀ R ∈ components G (tupleVertices F ∪ Cycle.vertices C)ᶜ, R ≠ B →
        R ⊆ J ∧ (G.toSimpleGraph.induce (↑R : Set G.Vertex)).IsAcyclic ∧
        (∀ v ∈ R, G.degree v = 3) ∧ R.card + 2 ≤ K ∧
        (∀ e f, e ∈ crossing G R (Cycle.vertices C) →
          f ∈ crossing G R (Cycle.vertices C) → e = f))
    (v : G.Vertex) :
    vertexLoad E Cycle.vertices (fun C => conditionalDensity (tupleEvent F) (Cycle.Event C)) v ≤
      6 * L * ((2 : ℝ) ^ (F.card * Nat.ceil (((s - 1 : ℕ) : ℝ) / (Δ : ℝ))) / 2 ^ s) := by
  classical
  let U := tupleVertices F
  let Bcore := vertices G.toSimpleGraph Uᶜ
  let S := Bcore ∩ J
  let P := inducedPhysical G S
  let incl := induced G S
  have hES : ∀ C ∈ E, Cycle.vertices C ⊆ S := by
    intro C hC w hw
    exact Finset.mem_inter.mpr
      ⟨CoreConditionalProbability.cycle_subset_residual_core G U C (hED C hC) hw, hEJ C hC hw⟩
  let A := restrictFamily G S E hES
  let mass : P.CycleWord → ℝ := fun C => conditionalDensity (tupleEvent F) (Cycle.Event (incl.liftCycle C))
  let deg := inducedCoreDegree G Bcore S
  let w : P.Vertex → ℝ := fun v => weight (deg v)
  let b := F.card * Nat.ceil (((s - 1 : ℕ) : ℝ) / (Δ : ℝ))
  have hSK : S ⊆ Bcore := Finset.inter_subset_left
  have hSJ : S ⊆ J := Finset.inter_subset_right
  have hmin := vertices_minTwo G.toSimpleGraph Uᶜ
  have hmaxS : ∀ v ∈ S, G.degree v ≤ 3 := fun v hv => (hcubic v (hSJ hv)).le
  have hdeg := inducedCoreDegree_two_or_three G Bcore S hSK hmin hmaxS
  have hmaxP : ∀ v, P.degree v ≤ 3 := by
    intro v
    change (inducedPhysical G S).degree v ≤ 3
    have h := induced_degree_le_coreDegree G Bcore S hSK v
    rcases hdeg v with hd | hd <;> change inducedCoreDegree G Bcore S v = _ at hd <;> omega
  have hg : ShortWalks.GirthGreater P.toSimpleGraph D :=
    induced_girth_of_noShortCycles G S D (fun C hC => hno C (hC.trans hSJ))
  have hAE : ∀ C ∈ A, incl.liftCycle C ∈ E := by
    intro C hC
    have hh : incl.liftCycle C ∈ incl.liftFamily A := Finset.mem_image.mpr ⟨C, hC, rfl⟩
    rwa [lift_restrictFamily] at hh
  have hmass : ∀ C ∈ A, mass C ≤ ∏ v ∈ Cycle.vertices C, w v := by
    intro C hC
    have hCE := hAE C hC
    obtain ⟨B, hB, hsmall⟩ := hcomp _ hCE
    have h := conditional_mass_le_product G F (incl.liftCycle C) B hFdisj (by
      intro A hA
      apply Finset.disjoint_left.mpr
      intro u hu huC
      exact Finset.disjoint_left.mp (hED _ hCE)
        (Finset.mem_biUnion.mpr ⟨A, hA, hu⟩) huC)
      (hinduced _ hCE) (fun v hv => (hcubic v (hEJ _ hCE hv)).le) hB
      (fun R hR hRB => ⟨(hsmall R hR hRB).2.1, (hsmall R hR hRB).2.2.2.2⟩)
    rw [incl.liftCycle_vertices, Finset.prod_image (fun _ _ _ _ h => incl.vertex.injective h)] at h
    exact h
  have hcount : ∀ ell ∈ Finset.Ioc s L, ∀ u,
      ∀ C : {C : CycleWordsAtLength P ell // C ∈ selectedAtVertex P A ell u}, ∀ orientation : Bool,
      (((runDarts P ((ell - 1) - (ell - s - 1))
        (splitRun P (show ell - s - 1 ≤ ell - 1 by omega)
          (encodeCyclePrefixAtVertex P ell u
            ⟨C.1, selectedAtVertex_subset P A ell u C.2⟩ orientation).1.2.2).2.2).dropLast.map
        (head P)).countP (fun v => decide (deg v = 2))) ≤ 2 + b := by
    intro ell hell u C orientation
    let r := (splitRun P (show ell - s - 1 ≤ ell - 1 by omega)
      (encodeCyclePrefixAtVertex P ell u
        ⟨C.1, selectedAtVertex_subset P A ell u C.2⟩ orientation).1.2.2).2.2
    let p := runWalk P ((ell - 1) - (ell - s - 1)) r
    let pG := p.map incl.graphHom
    have hks : (ell - 1) - (ell - s - 1) = s := by have := (Finset.mem_Ioc.mp hell).1; omega
    have hp : p.IsPath := CycleSuffixGeometry.short_run_isPath P D _ hg (by omega) r
    have hCE := hAE C.1.1 (Finset.mem_filter.mp C.2).2.1
    have hsup : ∀ z ∈ p.support, z ∈ Cycle.vertices C.1.1 :=
      CycleSuffixGeometry.encoded_suffix_support P ell (ell - s - 1) (by omega) u
        ⟨C.1, selectedAtVertex_subset P A ell u C.2⟩ orientation
    have hsupG : ∀ z ∈ pG.support, z ∈ Cycle.vertices (incl.liftCycle C.1.1) := by
      intro z hz
      change z ∈ (p.map incl.graphHom).support at hz
      rw [SimpleGraph.Walk.support_map] at hz
      obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hz
      rw [incl.liftCycle_vertices]
      exact Finset.mem_image.mpr ⟨a, hsup a ha, rfl⟩
    obtain ⟨B, hB, hsmall⟩ := hcomp _ hCE
    have hc := ConditionalDegreeTwoLabels.degreeTwo_internal_walk_count J F id
      (Cycle.vertices (incl.liftCycle C.1.1)) B K q Δ (s - 1) hK hΔ hΔq
      (hED _ hCE) (CoreConditionalProbability.cycle_subset_residual_core G U _ (hED _ hCE))
      (hEJ _ hCE) (fun z hz => hcubic z (hEJ _ hCE hz))
      (fun C hC z hz => hcubic z (hFJ C hC hz)) hreturn hsmall pG
      (by
        rw [SimpleGraph.Walk.isPath_def, SimpleGraph.Walk.support_map]
        exact hp.support_nodup.map incl.vertex.injective)
      (by simp only [pG, p, SimpleGraph.Walk.length_map, runWalk_length, hks]; omega) hsupG
    rw [WalkWindowPositions.run_internal_heads_eq]
    simpa only [pG, SimpleGraph.Walk.support_map, ← List.map_tail, ← List.map_dropLast,
      List.countP_map, Function.comp_apply] using hc
  have hload := WeightedCycleLoad.vertexLoad_le_marked_suffix P w (fun v => deg v = 2)
    (fun v => weight_nonneg _) (fun v => weight_le_one _) (fun v hv => weight_le_half _ hv)
    (induced_core_row_le_one G Bcore S hSK hmin hmaxS) hmaxP D s L b A mass hg hs hshort
    (fun C hC => by simpa only [← incl.liftCycle_length] using hlen _ (hAE C hC))
    (fun C _ => div_nonneg (Finite.density_nonneg _) (Finite.density_nonneg _)) hmass hcount
  have h := CycleNeighborhoodLoad.vertexLoad_image_le A Cycle.vertices mass incl.vertex
    incl.vertex.injective (6 * L * ((2 : ℝ) ^ b / 2 ^ s)) (by positivity) hload v
  change vertexLoad (restrictFamily G S E hES)
    (fun C => (Cycle.vertices C).image (induced G S).vertex)
    (fun C => conditionalDensity (tupleEvent F) (Cycle.Event ((induced G S).liftCycle C))) v ≤ _ at h
  rw [vertexLoad_restrictFamily G S E hES
    (fun C => conditionalDensity (tupleEvent F) (Cycle.Event C)) v] at h
  exact h

end Erdos1016.Proof.ResidualCoreCycleLoad
