import Erdos1016.Probability.Conditional.RegionReveal
import Erdos1016.CycleSpace.CyclicRegionSupport

set_option autoImplicit false
set_option maxHeartbeats 1000000

noncomputable section

namespace Erdos1016.Proof.PhysicalManyRegionConditionalProduct

open Erdos1016
open Erdos1016.Proof.PhysicalManyRegionReveal
open Erdos1016.Proof.RevealedFiberProduct

local notation "𝔽" => F₂

variable (G : PhysicalGraph) {ι : Type*} [Fintype ι]
  (S : ι → Finset G.Vertex)

def regionInternalEdges (i : ι) : Finset G.Edge :=
  regionEdges G S i

def internalEdgeEquiv (i : ι) : InternalEdge G S i ≃
    G.RestrictedEdge (regionInternalEdges G S i) :=
  Equiv.refl _



theorem localBoundary_eq_restrictedBoundary (i : ι)
    (z : InternalEdge G S i → 𝔽) (v : G.Vertex) :
    localBoundary G S i z v =
    G.restrictedBoundary (regionInternalEdges G S i)
        (fun e => z ((internalEdgeEquiv G S i).symm e)) v := by
  classical
  change G.restrictedBoundary (regionEdges G S i) z v =
    G.restrictedBoundary (regionEdges G S i) (fun e => z e) v
  rfl

abbrev LocalKernel (i : ι) :=
  {z : InternalEdge G S i → 𝔽 // ∀ v, localBoundary G S i z v = 0}

def localCycleSpaceEquivLocalKernel (i : ι) :
    G.RestrictedCycleSpace (regionEdges G S i) ≃ LocalKernel G S i where
  toFun z := ⟨z.1, fun v => by
    have hz := congrFun (LinearMap.mem_ker.mp z.2) v
    exact hz⟩
  invFun z := ⟨z.1, LinearMap.mem_ker.mpr (by
    funext v
    exact z.2 v)⟩
  left_inv z := by
    apply Subtype.ext
    rfl
  right_inv z := by
    apply Subtype.ext
    rfl

def localKernelEquivRestrictedCycleSpace (i : ι) :
    LocalKernel G S i ≃ G.RestrictedCycleSpace (regionInternalEdges G S i) where
  toFun z := ⟨fun e => z.1 ((internalEdgeEquiv G S i).symm e), by
    change G.restrictedBoundary (regionInternalEdges G S i)
      (fun e => z.1 ((internalEdgeEquiv G S i).symm e)) = 0
    funext v
    rw [← localBoundary_eq_restrictedBoundary G S i z.1 v]
    exact z.2 v⟩
  invFun z := ⟨fun e => z.1 ((internalEdgeEquiv G S i) e), by
    intro v
    rw [localBoundary_eq_restrictedBoundary G S i
      (fun e => z.1 ((internalEdgeEquiv G S i) e)) v]
    have hz := congrFun z.2 v
    simpa using hz⟩
  left_inv z := by
    apply Subtype.ext
    funext e
    rfl
  right_inv z := by
    apply Subtype.ext
    funext e
    rfl

def affineFactorCycleSpaceEquiv
    (hdisj : ∀ i j, i ≠ j → Disjoint (S i) (S j))
    (y : RevealTarget G S hdisj) (i : ι)
    (hcut : ∀ v, v ∈ S i → outsideBoundary G S y.1 v = 0) :
    AffineFactor G S hdisj y i ≃
      G.RestrictedCycleSpace (regionInternalEdges G S i) := by
  exact (affineFactor_zeroCut_equiv_localCycleSpace G S hdisj y i hcut).trans
    ((localCycleSpaceEquivLocalKernel G S i).trans
      (localKernelEquivRestrictedCycleSpace G S i))

def affineFactorAcyclic
    (hdisj : ∀ i j, i ≠ j → Disjoint (S i) (S j))
    (y : RevealTarget G S hdisj) (i : ι) (z : AffineFactor G S hdisj y i) : Prop :=
  (G.restrictedSelectedGraph (regionInternalEdges G S i)
    (fun e => z.1 ((internalEdgeEquiv G S i).symm e))).IsAcyclic

theorem affineFactorAcyclic_density_le_half
    (hdisj : ∀ i j, i ≠ j → Disjoint (S i) (S j))
    (y : RevealTarget G S hdisj) (i : ι)
    (hcut : ∀ v, v ∈ S i → outsideBoundary G S y.1 v = 0)
    (hcycle : ∃ C : G.CycleWord,
      ∀ e, C.1 e ≠ 0 → e ∈ regionInternalEdges G S i) :
    Finite.density (affineFactorAcyclic G S hdisj y i) ≤ (1 / 2 : ℝ) := by
  let e := affineFactorCycleSpaceEquiv G S hdisj y i hcut
  have heq := Finite.density_equiv e
    (P := affineFactorAcyclic G S hdisj y i)
    (Q := fun z : G.RestrictedCycleSpace (regionInternalEdges G S i) =>
      (G.restrictedSelectedGraph (regionInternalEdges G S i) z.1).IsAcyclic)
    (by
      intro z
      change (G.restrictedSelectedGraph (regionInternalEdges G S i)
          (fun e => z.1 ((internalEdgeEquiv G S i).symm e))).IsAcyclic ↔
        (G.restrictedSelectedGraph (regionInternalEdges G S i) (e z).1).IsAcyclic
      have hword : (e z).1 =
          (fun e => z.1 ((internalEdgeEquiv G S i).symm e)) := by
        funext e'
        simp [e, affineFactorCycleSpaceEquiv,
          localCycleSpaceEquivLocalKernel, localKernelEquivRestrictedCycleSpace,
          affineFactor_zeroCut_equiv_localCycleSpace, internalEdgeEquiv]
      rw [hword])
  rw [heq]
  exact ConditionalRegionProduct.restrictedCycleSpace_forest_density_le_half
    G (regionInternalEdges G S i)
    (ManyRegionsCycleKernelBridge.exists_nonzero_restrictedCycleSpace_of_supported_cycle
      G (regionInternalEdges G S i) hcycle)

theorem splitWord_local_coordinate
    (hdisj : ∀ i j, i ≠ j → Disjoint (S i) (S j))
    (x : G.Word) (i : ι) (e : InternalEdge G S i) :
    (splitWord G S hdisj x).2 i e = x e.1 := by
  classical
  have hpart := (edgePartition G S hdisj).right_inv (Sum.inr ⟨i, e⟩)
  change edgePartition G S hdisj e.1 = Sum.inr ⟨i, e⟩ at hpart
  have hsymm : (edgePartition G S hdisj).symm (Sum.inr ⟨i, e⟩) = e.1 :=
    (Equiv.symm_apply_eq (edgePartition G S hdisj)).2 hpart.symm
  simp [splitWord, ManyRegionsFiberDecomposition.splitWord, hsymm]

theorem outsideForest_fiber_density_le_half_pow_of_zeroCut_regions
    (hdisj : ∀ i j, i ≠ j → Disjoint (S i) (S j))
    (E : Finset G.Edge)
    (hregionsOutside : ∀ i, regionInternalEdges G S i ⊆ Eᶜ)
    (hcycles : ∀ i, ∃ C : G.CycleWord,
      ∀ e, C.1 e ≠ 0 → e ∈ regionInternalEdges G S i)
    (a : ℕ) :
    ∀ y : RevealTarget G S hdisj,
      a ≤ Nat.card {i : ι // PhysicalManyRegionReveal.zeroCut G S i y.1} →
      Finite.density
        (fun x : RevealedFiberProbability.fiber (reveal G S hdisj) y =>
          x.1 ∈ G.outsideLinearForestStates E) ≤ (1 / 2 : ℝ) ^ a := by
  classical
  let A : RevealTarget G S hdisj → ι → Type :=
    fun y i => AffineFactor G S hdisj y i
  let Q : (y : RevealTarget G S hdisj) → (i : ι) → A y i → Prop :=
    fun y i z => affineFactorAcyclic G S hdisj y i z
  let ZC : ι → RevealTarget G S hdisj → Prop :=
    fun i y => PhysicalManyRegionReveal.zeroCut G S i y.1
  have hU : ∀ y (x : RevealedFiberProbability.fiber (reveal G S hdisj) y),
      x.1 ∈ G.outsideLinearForestStates E →
        ∀ i, ZC i y → Q y i
          ((fiberAffineProductEquiv G S hdisj y x) i) := by
    intro y x hx i hcut
    let z := (fiberAffineProductEquiv G S hdisj y x) i
    have hlocal := ConditionalRegionProduct.outsideForest_implies_local_acyclic
      G E (regionInternalEdges G S i) (hregionsOutside i) x.1 hx
    have hword :
        (fun e => z.1 ((internalEdgeEquiv G S i).symm e)) =
          G.restrictWord (regionInternalEdges G S i) x.1.1 := by
      funext e
      have hcoord : z.1 ((internalEdgeEquiv G S i).symm e) =
          x.1.1 (((internalEdgeEquiv G S i).symm e).1) := by
        have h := splitWord_local_coordinate G S hdisj x.1.1 i
          ((internalEdgeEquiv G S i).symm e)
        simpa [z, fiberAffineProductEquiv] using h
      simpa [PhysicalGraph.restrictWord] using hcoord
    change (G.restrictedSelectedGraph (regionInternalEdges G S i)
      (fun e => z.1 ((internalEdgeEquiv G S i).symm e))).IsAcyclic
    rw [hword]
    exact hlocal
  have hhalf : ∀ y i, ZC i y → Finite.density (Q y i) ≤ (1 / 2 : ℝ) := by
    intro y i hcut
    dsimp [Q, A]
    exact affineFactorAcyclic_density_le_half G S hdisj y i hcut (hcycles i)
  exact RevealedFiberProduct.fiber_density_le_half_pow_of_selected_product_implication
    (reveal G S hdisj) A (fun y i => inferInstance)
    (fun y => fiberAffineProductEquiv G S hdisj y)
    (fun x => x ∈ G.outsideLinearForestStates E) Q ZC hU hhalf a

/-- User-facing form: cyclic induced regions provide the internally supported
cycle words needed by the conditional product estimate.  The only extra
geometric input is that every region's internal edges avoid the excluded set
`E`; pairwise vertex-disjointness is the hypothesis used by the reveal
factorization. -/
theorem outsideForest_fiber_density_le_half_pow_of_zeroCut_cyclicRegions
    (hdisj : ∀ i j, i ≠ j → Disjoint (S i) (S j))
    (E : Finset G.Edge)
    (hregionsOutside : ∀ i, regionInternalEdges G S i ⊆ Eᶜ)
    (hcyclic : ∀ i, G.IsCyclicRegion (S i))
    (a : ℕ) :
    ∀ y : RevealTarget G S hdisj,
      a ≤ Nat.card {i : ι // PhysicalManyRegionReveal.zeroCut G S i y.1} →
      Finite.density
        (fun x : RevealedFiberProbability.fiber (reveal G S hdisj) y =>
          x.1 ∈ G.outsideLinearForestStates E) ≤ (1 / 2 : ℝ) ^ a := by
  apply outsideForest_fiber_density_le_half_pow_of_zeroCut_regions
    G S hdisj E hregionsOutside ?_ a
  intro i
  obtain ⟨C, hC⟩ :=
    ManyRegionsCyclicSupport.exists_cycleWord_supported_on_internalEdges_of_IsCyclicRegion
      G (S i) (hcyclic i)
  refine ⟨C, ?_⟩
  intro e he
  have he' := hC e he
  simpa [regionInternalEdges, PhysicalManyRegionReveal.regionEdges,
    Erdos1016.SafeCore.internalEdges] using he'

end Erdos1016.Proof.PhysicalManyRegionConditionalProduct

end
