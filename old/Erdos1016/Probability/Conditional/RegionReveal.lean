import Erdos1016.Probability.Conditional.CoordinateProduct
import Erdos1016.Probability.Conditional.RevealedProduct
import Erdos1016.Probability.Conditional.RegionParityProduct

set_option autoImplicit false
set_option maxHeartbeats 1000000

noncomputable section

namespace Erdos1016.Proof.PhysicalManyRegionReveal

open Erdos1016
open Erdos1016.Proof.ManyRegionsFiberDecomposition

local notation "𝔽" => F₂

variable (G : PhysicalGraph) {ι : Type*} [Fintype ι]
  (S : ι → Finset G.Vertex)

def regionEdges (i : ι) : Finset G.Edge :=
  Finset.univ.filter fun e => G.src e ∈ S i ∧ G.dst e ∈ S i

def allRegionEdges : Finset G.Edge :=
  Finset.univ.biUnion (regionEdges G S)

abbrev InternalEdge (i : ι) :=
  G.RestrictedEdge (regionEdges G S i)

abbrev OutsideEdge :=
  G.OutsideEdge (allRegionEdges G S)

abbrev EdgePart := OutsideEdge G S ⊕ Σ i, InternalEdge G S i

noncomputable instance outsideFintype : Fintype (OutsideEdge G S) :=
  Fintype.ofInjective Subtype.val Subtype.val_injective

noncomputable instance internalFintype (i : ι) : Fintype (InternalEdge G S i) :=
  Fintype.ofInjective Subtype.val Subtype.val_injective

noncomputable instance edgePartFintype : Fintype (EdgePart G S) := by
  classical
  letI : Fintype (Σ i, InternalEdge G S i) := inferInstance
  exact instFintypeSum _ _

def edgeOfPart : EdgePart G S → G.Edge
  | .inl e => e.1
  | .inr ⟨_, e⟩ => e.1

private def classifyEdge (e : G.Edge) : EdgePart G S := by
  classical
  by_cases hex : ∃ i, e ∈ regionEdges G S i
  · exact Sum.inr ⟨Classical.choose hex, ⟨e, Classical.choose_spec hex⟩⟩
  · refine Sum.inl ⟨e, ?_⟩
    intro he
    rcases Finset.mem_biUnion.mp he with ⟨i, -, hi⟩
    exact hex ⟨i, hi⟩





private theorem region_src_mem {i : ι} {e : G.Edge}
    (he : e ∈ regionEdges G S i) : G.src e ∈ S i := by
  change e ∈ Finset.univ.filter (fun e => G.src e ∈ S i ∧ G.dst e ∈ S i) at he
  exact (Finset.mem_filter.mp he).2.1

private theorem region_dst_mem {i : ι} {e : G.Edge}
    (he : e ∈ regionEdges G S i) : G.dst e ∈ S i := by
  change e ∈ Finset.univ.filter (fun e => G.src e ∈ S i ∧ G.dst e ∈ S i) at he
  exact (Finset.mem_filter.mp he).2.2

private theorem internal_region_unique
    (hdisj : ∀ i j, i ≠ j → Disjoint (S i) (S j))
    {e : G.Edge} {i j : ι}
    (hi : e ∈ regionEdges G S i)
    (hj : e ∈ regionEdges G S j) : i = j := by
  by_contra hne
  have hd := Finset.disjoint_left.mp (hdisj i j hne)
  have hisrc : G.src e ∈ S i := (Finset.mem_filter.mp hi).2.1
  have hjsrc : G.src e ∈ S j := (Finset.mem_filter.mp hj).2.1
  exact hd hisrc hjsrc

private theorem subtype_heq_of_index_eq {α : Type*} {κ : Type*}
    (P : κ → α → Prop) {i j : κ} (hij : i = j)
    (x : {a : α // P i a}) (y : {a : α // P j a})
    (hval : x.1 = y.1) : HEq x y := by
  cases hij
  exact heq_of_eq (Subtype.ext hval)

def edgePartition (hdisj : ∀ i j, i ≠ j → Disjoint (S i) (S j)) :
    G.Edge ≃ EdgePart G S := by
  classical
  let f := classifyEdge G S
  have hleft : ∀ e, edgeOfPart G S (f e) = e := by
    intro e
    dsimp [f, classifyEdge]
    split_ifs <;> rfl
  have hinj : Function.Injective f := by
    intro e e' h
    calc
      e = edgeOfPart G S (f e) := (hleft e).symm
      _ = edgeOfPart G S (f e') := congrArg (edgeOfPart G S) h
      _ = e' := hleft e'
  have hsurj : Function.Surjective f := by
    intro q
    cases q with
    | inl e =>
      have hnone : ¬ ∃ i, e.1 ∈ regionEdges G S i := by
        intro h
        obtain ⟨i, hi⟩ := h
        exact e.2 (Finset.mem_biUnion.mpr ⟨i, Finset.mem_univ _, hi⟩)
      refine ⟨e.1, ?_⟩
      simp [f, classifyEdge, hnone]
    | inr ib =>
      rcases ib with ⟨i, e⟩
      have hex : ∃ j, e.1 ∈ regionEdges G S j := ⟨i, e.2⟩
      have hchoose : Classical.choose hex = i := by
        apply internal_region_unique G S hdisj (Classical.choose_spec hex) e.2
      refine ⟨e.1, ?_⟩
      dsimp [f, classifyEdge]
      rw [dif_pos hex]
      apply congrArg Sum.inr
      apply Sigma.ext hchoose
      exact subtype_heq_of_index_eq
        (fun j edge => edge ∈ regionEdges G S j)
        hchoose ⟨e.1, Classical.choose_spec hex⟩ e rfl
  refine Equiv.mk f (edgeOfPart G S) hleft ?_
  intro q
  obtain ⟨e, he⟩ := hsurj q
  calc
    f (edgeOfPart G S q) = f (edgeOfPart G S (f e)) :=
      congrArg f (congrArg (edgeOfPart G S) he.symm)
    _ = f e := congrArg f (hleft e)
    _ = q := he

def splitWord (hdisj : ∀ i j, i ≠ j → Disjoint (S i) (S j))
    (x : G.Word) : (OutsideEdge G S → 𝔽) ×
      ((i : ι) → InternalEdge G S i → 𝔽) :=
  ManyRegionsFiberDecomposition.splitWord (edgePartition G S hdisj) x

def glueWord (hdisj : ∀ i j, i ≠ j → Disjoint (S i) (S j))
    (z : (OutsideEdge G S → 𝔽) ×
      ((i : ι) → InternalEdge G S i → 𝔽)) : G.Word :=
  ManyRegionsFiberDecomposition.glueWord (edgePartition G S hdisj) z

def outsideBoundary (y : OutsideEdge G S → 𝔽) (v : G.Vertex) : 𝔽 :=
  G.outsideBoundary (allRegionEdges G S) y v

def localBoundary (i : ι) (z : InternalEdge G S i → 𝔽) (v : G.Vertex) : 𝔽 :=
  G.restrictedBoundary (regionEdges G S i) z v

private theorem edgePartition_splits_gluedWord
    (hdisj : ∀ i j, i ≠ j → Disjoint (S i) (S j))
    (y : OutsideEdge G S → 𝔽)
    (z : (i : ι) → InternalEdge G S i → 𝔽) :
    glueWord G S hdisj (y, z) =
      G.extendOutsideWord (allRegionEdges G S) y +
        ∑ i, G.extendWord (regionEdges G S i) (z i) := by
  classical
  let ep := edgePartition G S hdisj
  unfold glueWord ManyRegionsFiberDecomposition.glueWord
  funext e
  cases hq : ep e with
  | inl o =>
    have hval : o.1 = e := by
      have hh := ep.left_inv e
      simpa [hq, edgeOfPart] using hh
    have ho : o = ⟨e, by simpa [hval] using o.2⟩ := Subtype.ext hval
    rw [ho]
    have hout : e ∉ allRegionEdges G S := by
      simpa [hval] using o.2
    have hlocals : ∑ i, G.extendWord (regionEdges G S i) (z i) e = 0 := by
      apply Fintype.sum_eq_zero
      intro i
      have hi : e ∉ regionEdges G S i := by
        intro he
        exact hout (Finset.mem_biUnion.mpr ⟨i, Finset.mem_univ _, he⟩)
      simp [PhysicalGraph.extendWord, hi]
    simp [hq, hval, PhysicalGraph.extendOutsideWord, hout, hlocals]
  | inr ib =>
    rcases ib with ⟨i, b⟩
    have hval : b.1 = e := by
      have hh := ep.left_inv e
      simpa [hq, edgeOfPart] using hh
    have hi : e ∈ regionEdges G S i := by simpa [hval] using b.2
    have hout : e ∈ allRegionEdges G S :=
      Finset.mem_biUnion.mpr ⟨i, Finset.mem_univ _, hi⟩
    have hb : b = ⟨e, hi⟩ := Subtype.ext hval
    have hlocals : ∑ j, G.extendWord (regionEdges G S j) (z j) e = z i b := by
      rw [Fintype.sum_eq_single i]
      · simp [PhysicalGraph.extendWord, hi, hval, hb]
      · intro j hji
        have hj : e ∉ regionEdges G S j := by
          intro hj
          have hEq := internal_region_unique G S hdisj hi hj
          exact hji hEq.symm
        simp [PhysicalGraph.extendWord, hj]
    simp only [hq]
    simp only [Pi.add_apply, Finset.sum_apply]
    have houtzero : G.extendOutsideWord (allRegionEdges G S) y e = 0 := by
      simp [PhysicalGraph.extendOutsideWord, hout]
    rw [houtzero, zero_add]
    exact hlocals.symm

theorem boundary_eq_outside_add_locals
    (hdisj : ∀ i j, i ≠ j → Disjoint (S i) (S j))
    (y : OutsideEdge G S → 𝔽)
    (z : (i : ι) → InternalEdge G S i → 𝔽) (v : G.Vertex) :
    G.boundary (glueWord G S hdisj (y, z)) v =
      outsideBoundary G S y v + ∑ i, localBoundary G S i (z i) v := by
  classical
  rw [edgePartition_splits_gluedWord G S hdisj y z]
  change G.boundary
      (G.extendOutsideWord (allRegionEdges G S) y +
        ∑ i, G.extendWord (regionEdges G S i) (z i)) v = _
  rw [map_add, map_sum]
  simp [outsideBoundary, localBoundary, PhysicalGraph.outsideBoundary,
    PhysicalGraph.restrictedBoundary, PhysicalGraph.extendOutsideLinear,
    PhysicalGraph.extendWordLinear, Pi.add_apply, Finset.sum_apply]

theorem localBoundary_eq_zero_of_foreign_region
    (hdisj : ∀ i j, i ≠ j → Disjoint (S i) (S j))
    {i j : ι} (hij : i ≠ j) (z : InternalEdge G S j → 𝔽)
    {v : G.Vertex} (hv : v ∈ S i) : localBoundary G S j z v = 0 := by
  classical
  change (G.restrictedBoundary (regionEdges G S j) z) v = 0
  change G.boundary (G.extendWord (regionEdges G S j) z) v = 0
  change (∑ e : G.Edge,
    ((if G.src e = v then G.extendWord (regionEdges G S j) z e else 0) +
      (if G.dst e = v then G.extendWord (regionEdges G S j) z e else 0))) = 0
  apply Fintype.sum_eq_zero
  intro e
  by_cases he : e ∈ regionEdges G S j
  · have hsrc : G.src e ≠ v := by
      intro h
      exact (Finset.disjoint_left.mp (hdisj i j hij)) hv
        (by simpa [h] using region_src_mem G S he)
    have hdst : G.dst e ≠ v := by
      intro h
      exact (Finset.disjoint_left.mp (hdisj i j hij)) hv
        (by simpa [h] using region_dst_mem G S he)
    simp [PhysicalGraph.extendWord, he, hsrc, hdst]
  · simp [PhysicalGraph.extendWord, he]

theorem localBoundary_eq_zero_of_vertex_outside
    (v : G.Vertex) (hv : ∀ i, v ∉ S i) (i : ι)
    (z : InternalEdge G S i → 𝔽) : localBoundary G S i z v = 0 := by
  classical
  change (G.restrictedBoundary (regionEdges G S i) z) v = 0
  change G.boundary (G.extendWord (regionEdges G S i) z) v = 0
  change (∑ e : G.Edge,
    ((if G.src e = v then G.extendWord (regionEdges G S i) z e else 0) +
      (if G.dst e = v then G.extendWord (regionEdges G S i) z e else 0))) = 0
  apply Fintype.sum_eq_zero
  intro e
  by_cases he : e ∈ regionEdges G S i
  · have hsrc : G.src e ≠ v := by
      intro h
      exact hv i (by simpa [h] using region_src_mem G S he)
    have hdst : G.dst e ≠ v := by
      intro h
      exact hv i (by simpa [h] using region_dst_mem G S he)
    simp [PhysicalGraph.extendWord, he, hsrc, hdst]
  · simp [PhysicalGraph.extendWord, he]

def outsideFeasible (y : OutsideEdge G S → 𝔽) : Prop :=
  ∀ v, (∀ i, v ∉ S i) → outsideBoundary G S y v = 0

def localFeasible (i : ι) (y : OutsideEdge G S → 𝔽)
    (z : InternalEdge G S i → 𝔽) : Prop :=
  ∀ v, v ∈ S i → outsideBoundary G S y v + localBoundary G S i z v = 0

def zeroCut (i : ι) (y : OutsideEdge G S → 𝔽) : Prop :=
  ∀ v, v ∈ S i → outsideBoundary G S y v = 0

abbrev LocalCycleSpace (i : ι) :=
  G.RestrictedCycleSpace (regionEdges G S i)

theorem localBoundary_eq_zero_of_vertex_not_in_region
    (i : ι) (z : InternalEdge G S i → 𝔽) {v : G.Vertex}
    (hv : v ∉ S i) : localBoundary G S i z v = 0 := by
  classical
  change (G.restrictedBoundary (regionEdges G S i) z) v = 0
  change G.boundary (G.extendWord (regionEdges G S i) z) v = 0
  change (∑ e : G.Edge,
    ((if G.src e = v then G.extendWord (regionEdges G S i) z e else 0) +
      (if G.dst e = v then G.extendWord (regionEdges G S i) z e else 0))) = 0
  apply Fintype.sum_eq_zero
  intro e
  by_cases he : e ∈ regionEdges G S i
  · have hsrc : G.src e ≠ v := by
      intro h
      exact hv (by simpa [h] using region_src_mem G S he)
    have hdst : G.dst e ≠ v := by
      intro h
      exact hv (by simpa [h] using region_dst_mem G S he)
    simp [PhysicalGraph.extendWord, he, hsrc, hdst]
  · simp [PhysicalGraph.extendWord, he]

theorem gluedWord_cycle_iff_outside_and_local
    (hdisj : ∀ i j, i ≠ j → Disjoint (S i) (S j))
    (y : OutsideEdge G S → 𝔽)
    (z : (i : ι) → InternalEdge G S i → 𝔽) :
    glueWord G S hdisj (y, z) ∈ G.CycleSpace ↔
      outsideFeasible G S y ∧ ∀ i, localFeasible G S i y (z i) := by
  classical
  rw [LinearMap.mem_ker]
  constructor
  · intro h
    constructor
    · intro v hv
      have hz := congrFun h v
      rw [boundary_eq_outside_add_locals G S hdisj y z v] at hz
      have hsum : ∑ i, localBoundary G S i (z i) v = 0 := by
        apply Fintype.sum_eq_zero
        intro i
        exact localBoundary_eq_zero_of_vertex_outside G S v hv i (z i)
      simpa [hsum] using hz
    · intro i v hv
      have hz := congrFun h v
      rw [boundary_eq_outside_add_locals G S hdisj y z v] at hz
      have hsum : ∑ j, localBoundary G S j (z j) v =
          localBoundary G S i (z i) v := by
        rw [Fintype.sum_eq_single i]
        · intro j hji
          exact localBoundary_eq_zero_of_foreign_region G S hdisj hji.symm
            (z j) hv
      rw [hsum] at hz
      exact hz
  · rintro ⟨hout, hlocal⟩
    funext v
    rw [boundary_eq_outside_add_locals G S hdisj y z v]
    by_cases hv : ∃ i, v ∈ S i
    · obtain ⟨i, hvi⟩ := hv
      have hsum : ∑ j, localBoundary G S j (z j) v =
          localBoundary G S i (z i) v := by
        rw [Fintype.sum_eq_single i]
        · intro j hji
          exact localBoundary_eq_zero_of_foreign_region G S hdisj hji.symm
            (z j) hvi
      rw [hsum]
      exact hlocal i v hvi
    · have hvout : ∀ i, v ∉ S i := by
        intro i hvi
        exact hv ⟨i, hvi⟩
      have hsum : ∑ i, localBoundary G S i (z i) v = 0 := by
        apply Fintype.sum_eq_zero
        intro i
        exact localBoundary_eq_zero_of_vertex_outside G S v hvout i (z i)
      rw [hsum]
      simpa using hout v hvout

def revealValue (hdisj : ∀ i j, i ≠ j → Disjoint (S i) (S j))
    (x : G.CycleSpace) : OutsideEdge G S → 𝔽 :=
  (splitWord G S hdisj x.1).1

abbrev RevealTarget (hdisj : ∀ i j, i ≠ j → Disjoint (S i) (S j)) :=
  {y : OutsideEdge G S → 𝔽 // ∃ x : G.CycleSpace,
    revealValue G S hdisj x = y}

noncomputable instance revealTargetFintype
    (hdisj : ∀ i j, i ≠ j → Disjoint (S i) (S j)) :
    Fintype (RevealTarget G S hdisj) := Fintype.ofInjective
      Subtype.val Subtype.val_injective

def reveal (hdisj : ∀ i j, i ≠ j → Disjoint (S i) (S j)) :
    G.CycleSpace → RevealTarget G S hdisj := fun x =>
  ⟨revealValue G S hdisj x, ⟨x, rfl⟩⟩

abbrev AffineFactor (hdisj : ∀ i j, i ≠ j → Disjoint (S i) (S j))
    (y : RevealTarget G S hdisj) (i : ι) :=
  {z : InternalEdge G S i → 𝔽 // localFeasible G S i y.1 z}

noncomputable instance affineFactorFintype
    (hdisj : ∀ i j, i ≠ j → Disjoint (S i) (S j))
    (y : RevealTarget G S hdisj) (i : ι) :
  Fintype (AffineFactor G S hdisj y i) := Fintype.ofInjective
      Subtype.val Subtype.val_injective

noncomputable def affineFactor_zeroCut_equiv_localCycleSpace
    (hdisj : ∀ i j, i ≠ j → Disjoint (S i) (S j))
    (y : RevealTarget G S hdisj) (i : ι)
    (hzero : zeroCut G S i y.1) : AffineFactor G S hdisj y i ≃
      LocalCycleSpace G S i where
  toFun z := ⟨z.1, LinearMap.mem_ker.mpr (by
    funext v
    change localBoundary G S i z.1 v = 0
    by_cases hv : v ∈ S i
    · have hfeasible := z.2 v hv
      rw [hzero v hv] at hfeasible
      simpa using hfeasible
    · exact localBoundary_eq_zero_of_vertex_not_in_region G S i z.1 hv)⟩
  invFun z := ⟨z.1, fun v hv => by
    have hlocal : localBoundary G S i z.1 v = 0 :=
      congrFun (LinearMap.mem_ker.mp z.2) v
    rw [hzero v hv, hlocal]
    simp⟩
  left_inv z := by apply Subtype.ext; rfl
  right_inv z := by apply Subtype.ext; rfl

theorem outsideFeasible_of_revealTarget
    (hdisj : ∀ i j, i ≠ j → Disjoint (S i) (S j))
    (y : RevealTarget G S hdisj) : outsideFeasible G S y.1 := by
  obtain ⟨x, hx⟩ := y.2
  have hglue : glueWord G S hdisj (splitWord G S hdisj x.1) = x.1 := by
    exact (ManyRegionsFiberDecomposition.splitEquiv
      (edgePartition G S hdisj)).left_inv x.1
  have hcycle :=
    (gluedWord_cycle_iff_outside_and_local G S hdisj
      (splitWord G S hdisj x.1).1 (splitWord G S hdisj x.1).2).1
      (by rw [hglue]; exact x.2)
  have hout : (splitWord G S hdisj x.1).1 = y.1 := hx
  rw [hout] at hcycle
  exact hcycle.1

private def globalFiberToCycleFiber
    (hdisj : ∀ i j, i ≠ j → Disjoint (S i) (S j))
    (y : RevealTarget G S hdisj) :
    ManyRegionsFiberDecomposition.globalFiber
      (edgePartition G S hdisj) (fun w : G.Word => w ∈ G.CycleSpace) y.1 ≃
      RevealedFiberProbability.fiber (reveal G S hdisj) y where
  toFun x := by
    refine ⟨⟨x.1, x.2.1⟩, ?_⟩
    apply Subtype.ext
    change (splitWord G S hdisj x.1).1 = y.1
    exact x.2.2
  invFun x := by
    refine ⟨x.1.1, ?_⟩
    exact ⟨x.1.2, by
      have h := congrArg Subtype.val x.2
      exact h⟩
  left_inv x := by
    apply Subtype.ext
    rfl
  right_inv x := by
    apply Subtype.ext
    rfl

private def localProductToFactors
    (hdisj : ∀ i j, i ≠ j → Disjoint (S i) (S j))
    (y : RevealTarget G S hdisj) :
    ManyRegionsFiberDecomposition.localProductFiber
      (outsideFeasible G S) (localFeasible G S) y.1 ≃
      ((i : ι) → AffineFactor G S hdisj y i) where
  toFun z i := ⟨z.1 i, z.2.2 i⟩
  invFun z := ⟨fun i => (z i).1, outsideFeasible_of_revealTarget G S hdisj y,
    fun i => (z i).2⟩
  left_inv z := by
    apply Subtype.ext
    funext i
    rfl
  right_inv z := by
    funext i
    apply Subtype.ext
    rfl

def fiberAffineProductEquiv
    (hdisj : ∀ i j, i ≠ j → Disjoint (S i) (S j))
    (y : RevealTarget G S hdisj) :
    RevealedFiberProbability.fiber (reveal G S hdisj) y ≃
      ((i : ι) → AffineFactor G S hdisj y i) := by
  let hfactor : ∀ x : G.Word, x ∈ G.CycleSpace ↔
      outsideFeasible G S (splitWord G S hdisj x).1 ∧
        ∀ i, localFeasible G S i (splitWord G S hdisj x).1
          ((splitWord G S hdisj x).2 i) := by
    intro x
    have hglue : glueWord G S hdisj (splitWord G S hdisj x) = x := by
      exact (ManyRegionsFiberDecomposition.splitEquiv
        (edgePartition G S hdisj)).left_inv x
    have hsplit : splitWord G S hdisj (glueWord G S hdisj
        (splitWord G S hdisj x)) = splitWord G S hdisj x := by
      exact (ManyRegionsFiberDecomposition.splitEquiv
        (edgePartition G S hdisj)).right_inv (splitWord G S hdisj x)
    rw [← hglue, hsplit]
    exact gluedWord_cycle_iff_outside_and_local G S hdisj
      (splitWord G S hdisj x).1 (splitWord G S hdisj x).2
  exact (globalFiberToCycleFiber G S hdisj y).symm.trans
    ((ManyRegionsFiberDecomposition.globalFiber_equiv_localProductFiber
      (edgePartition G S hdisj) (fun x : G.Word => x ∈ G.CycleSpace)
      (outsideFeasible G S) (localFeasible G S) hfactor y.1).trans
      (localProductToFactors G S hdisj y))




end Erdos1016.Proof.PhysicalManyRegionReveal
