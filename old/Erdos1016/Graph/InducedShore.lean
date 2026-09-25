import Erdos1016.Decomposition.TwoCore.PhysicalCore
import Erdos1016.Decomposition.TwoCore.LeafPruning

set_option autoImplicit false

/-!
# Finite induced physical graphs for shores

`FiniteTwoCore.inducedPhysical` is the physical realization of the network
whose vertices are the shore and whose edges are exactly the host edges with
both endpoints in it. This module exposes the corresponding degree and
expansion transfers in the shore's native notation.
-/

noncomputable section
namespace Erdos1016.Extremal

open Erdos1016.BoundaryTrace Erdos1016.BoundaryDecay
open Erdos1016.Nonbacktracking.FiniteTwoCore
open Erdos1016.SafeCore

local instance inducedShoreDecidable (p : Prop) : Decidable p := Classical.propDecidable p

/-- The physical graph whose vertices and edges are precisely the induced
network on the actual shore. Its vertices are reindexed by `Fin U.card`. -/
abbrev inducedShoreGraph (G : PhysicalGraph) (U : Finset G.Vertex) : PhysicalGraph :=
  inducedPhysical G U

/-- The shore-to-`Fin` map used by the induced graph realization. -/
def inducedShoreVertexEquiv (G : PhysicalGraph) (U : Finset G.Vertex) :
    Network.Shore.InsideVertex U ≃ (inducedShoreGraph G U).Vertex :=
  Fintype.equivFin (Network.Shore.InsideVertex U)

/-- Reindex any host subset of U into the physical induced graph. -/
def inducedShoreImage (G : PhysicalGraph) (U A : Finset G.Vertex)
    (hAU : A ⊆ U) :
    Finset (inducedShoreGraph G U).Vertex :=
  A.attach.image (fun v => inducedShoreVertexEquiv G U ⟨v.1, hAU v.2⟩)

@[simp] theorem mem_inducedShoreImage
    (G : PhysicalGraph) (U A : Finset G.Vertex) (hAU : A ⊆ U)
    (v : G.Vertex) (hv : v ∈ U) :
    inducedShoreVertexEquiv G U ⟨v, hv⟩ ∈ inducedShoreImage G U A hAU ↔
      v ∈ A := by
  classical
  simp only [inducedShoreImage, Finset.mem_image, Finset.mem_attach]
  constructor
  · rintro ⟨w, hw, heq⟩
    have hvw := (inducedShoreVertexEquiv G U).injective heq
    have hvw' : w.1 = v := congrArg Subtype.val hvw
    exact hvw' ▸ w.2
  · intro hvA
    refine ⟨⟨v, hvA⟩, by simp, ?_⟩
    apply congrArg (inducedShoreVertexEquiv G U)
    apply Subtype.ext
    rfl

/-- Pull a subset of the reindexed induced graph back to original host
vertices. -/
def inducedShorePreimage (G : PhysicalGraph) (U : Finset G.Vertex)
    (B : Finset (inducedShoreGraph G U).Vertex) : Finset G.Vertex :=
  B.image fun w => ((inducedShoreVertexEquiv G U).symm w).1

theorem inducedShorePreimage_subset
    (G : PhysicalGraph) (U : Finset G.Vertex)
    (B : Finset (inducedShoreGraph G U).Vertex) :
    inducedShorePreimage G U B ⊆ U := by
  classical
  intro v hv
  obtain ⟨w, hw, rfl⟩ := Finset.mem_image.1 hv
  exact (inducedShoreVertexEquiv G U).symm w |>.2

theorem mem_inducedShorePreimage
    (G : PhysicalGraph) (U : Finset G.Vertex)
    (B : Finset (inducedShoreGraph G U).Vertex)
    (v : G.Vertex) (hv : v ∈ U) :
    v ∈ inducedShorePreimage G U B ↔
      inducedShoreVertexEquiv G U ⟨v, hv⟩ ∈ B := by
  classical
  constructor
  · intro h
    obtain ⟨w, hw, heq⟩ := Finset.mem_image.1 h
    have heq' : (inducedShoreVertexEquiv G U).symm w = ⟨v, hv⟩ :=
      Subtype.ext heq
    have hpoint : inducedShoreVertexEquiv G U ⟨v, hv⟩ = w := by
      have := congrArg (inducedShoreVertexEquiv G U) heq'
      simpa using this.symm
    simpa [hpoint] using hw
  · intro h
    refine Finset.mem_image.2 ⟨inducedShoreVertexEquiv G U ⟨v, hv⟩, h, ?_⟩
    simp

/-- Exact equivalence between a subset of the reindexed graph and its
original-vertex preimage. -/
def inducedShoreSubsetEquiv
    (G : PhysicalGraph) (U : Finset G.Vertex)
    (B : Finset (inducedShoreGraph G U).Vertex) :
    {v : G.Vertex // v ∈ inducedShorePreimage G U B} ≃
      {w : (inducedShoreGraph G U).Vertex // w ∈ B} where
  toFun v := ⟨inducedShoreVertexEquiv G U ⟨v.1,
    inducedShorePreimage_subset G U B v.2⟩,
    (mem_inducedShorePreimage G U B v.1
      (inducedShorePreimage_subset G U B v.2)).1 v.2⟩
  invFun w := ⟨((inducedShoreVertexEquiv G U).symm w.1).1,
    (mem_inducedShorePreimage G U B _
      ((inducedShoreVertexEquiv G U).symm w.1).2).2 (by
        simpa using w.2)⟩
  left_inv v := by
    apply Subtype.ext
    simp
  right_inv w := by
    apply Subtype.ext
    simp

theorem inducedShore_subset_card_eq
    (G : PhysicalGraph) (U : Finset G.Vertex)
    (B : Finset (inducedShoreGraph G U).Vertex) :
    (inducedShorePreimage G U B).card = B.card := by
  classical
  have h := Fintype.card_congr (inducedShoreSubsetEquiv G U B)
  simpa only [Fintype.card_coe] using h

/-- A subset of the Fin-indexed shore is exactly the image of its original
vertex preimage. -/
theorem inducedShoreImage_preimage_eq
    (G : PhysicalGraph) (U : Finset G.Vertex)
    (B : Finset (inducedShoreGraph G U).Vertex) :
    inducedShoreImage G U (inducedShorePreimage G U B)
      (inducedShorePreimage_subset G U B) = B := by
  classical
  ext w
  constructor
  · intro hw
    obtain ⟨v, hv, hvw⟩ := Finset.mem_image.1 hw
    have hvU := inducedShorePreimage_subset G U B v.2
    have hvB := (mem_inducedShorePreimage G U B v.1 hvU).1 v.2
    exact hvw ▸ hvB
  · intro hw
    let v := (inducedShoreVertexEquiv G U).symm w
    have hvU : v.1 ∈ U := v.2
    have hvA : v.1 ∈ inducedShorePreimage G U B :=
      (mem_inducedShorePreimage G U B v.1 hvU).2 (by simpa [v] using hw)
    refine Finset.mem_image.2 ⟨⟨v.1, hvA⟩, by simp, ?_⟩
    simp [v]

/-- The endpoints of an owner edge crossing A and U\A are both in U. -/
theorem relativeCut_endpoints_in_shore
    (G : PhysicalGraph) (U A : Finset G.Vertex) (hAU : A ⊆ U)
    {e : G.Edge} (he : e ∈ SafeCore.relativeCut G U A) :
    G.src e ∈ U ∧ G.dst e ∈ U := by
  simp only [SafeCore.relativeCut, SafeCore.crossing,
    Finset.mem_filter, Finset.mem_univ, true_and] at he
  rcases he with ⟨hs, ht⟩ | ⟨hs, ht⟩
  · exact ⟨hAU hs, (Finset.mem_sdiff.1 ht).1⟩
  · exact ⟨(Finset.mem_sdiff.1 hs).1, hAU ht⟩

/-- Host relative-cut edge labels are exactly the cut edge labels of the
inside network, with the same original physical edge underneath. -/
def relativeCutInsideEdgeEquiv
    (G : PhysicalGraph) (U A : Finset G.Vertex) (hAU : A ⊆ U) :
    {e : G.Edge // e ∈ SafeCore.relativeCut G U A} ≃
      {e : Network.Shore.InsideEdge G.traceNetwork U //
        ((G.src e.1 ∈ A ∧ G.dst e.1 ∈ U \ A) ∨
          (G.src e.1 ∈ U \ A ∧ G.dst e.1 ∈ A))} where
  toFun e := by
    have hU := relativeCut_endpoints_in_shore G U A hAU e.2
    refine ⟨⟨e.1, hU.1, hU.2⟩, ?_⟩
    simpa only [SafeCore.relativeCut, SafeCore.crossing,
      Finset.mem_filter, Finset.mem_univ, true_and] using e.2
  invFun e := ⟨e.1.1, by
    simpa only [SafeCore.relativeCut, SafeCore.crossing,
      Finset.mem_filter, Finset.mem_univ, true_and] using e.2⟩
  left_inv e := by rfl
  right_inv e := by cases e; rfl



/-- Physicalizing the induced network preserves its exact shore cut edge
labels. -/
def insideNetworkPhysicalCutEquiv
    (G : PhysicalGraph) (U A : Finset G.Vertex) (hAU : A ⊆ U) :
    {e : Network.Shore.InsideEdge G.traceNetwork U //
        ((G.src e.1 ∈ A ∧ G.dst e.1 ∈ U \ A) ∨
          (G.src e.1 ∈ U \ A ∧ G.dst e.1 ∈ A))} ≃
      {f : (inducedShoreGraph G U).Edge //
        f ∈ SafeCore.relativeCut (inducedShoreGraph G U) Finset.univ
          (inducedShoreImage G U A hAU)} := by
  classical
  let N := Network.Shore.inside G.traceNetwork U
  let E := Fintype.equivFin (Network.Shore.InsideEdge G.traceNetwork U)
  let V := inducedShoreVertexEquiv G U
  let B := inducedShoreImage G U A hAU
  refine {
    toFun := fun e => ⟨E e.1, ?_⟩
    invFun := fun f => ⟨E.symm f.1, ?_⟩
    left_inv := ?_
    right_inv := ?_ }
  · have hsrc : (inducedShoreGraph G U).src (E e.1) = V (N.src e.1) := by
      simp [inducedShoreGraph, inducedPhysical, inducedNetwork,
        BoundaryDecay.physicalize, Network.Shore.inside,
        PhysicalGraph.traceNetwork, inducedShoreVertexEquiv, E, V, N]
    have hdst : (inducedShoreGraph G U).dst (E e.1) = V (N.dst e.1) := by
      simp [inducedShoreGraph, inducedPhysical, inducedNetwork,
        BoundaryDecay.physicalize, Network.Shore.inside,
        PhysicalGraph.traceNetwork, inducedShoreVertexEquiv, E, V, N]
    unfold SafeCore.relativeCut SafeCore.crossing
    simp only [Finset.mem_filter, Finset.mem_univ, true_and,
      Finset.mem_sdiff]
    rw [hsrc, hdst]
    have hsrcMem : V (N.src e.1) ∈ B ↔ G.src e.1 ∈ A := by
      simpa [N, Network.Shore.inside, PhysicalGraph.traceNetwork, V, B] using
        mem_inducedShoreImage G U A hAU (G.src e.1) e.1.2.1
    have hdstMem : V (N.dst e.1) ∈ B ↔ G.dst e.1 ∈ A := by
      simpa [N, Network.Shore.inside, PhysicalGraph.traceNetwork, V, B] using
        mem_inducedShoreImage G U A hAU (G.dst e.1) e.1.2.2
    rcases e.2 with h | h
    · left
      exact ⟨hsrcMem.2 h.1,
        fun hb => (Finset.mem_sdiff.1 h.2).2 (hdstMem.1 hb)⟩
    · right
      exact ⟨fun hb => (Finset.mem_sdiff.1 h.1).2 (hsrcMem.1 hb),
        hdstMem.2 h.2⟩
  · let e := E.symm f.1
    have hsrc : (inducedShoreGraph G U).src f.1 = V (N.src e) := by
      simp [inducedShoreGraph, inducedPhysical, inducedNetwork,
        BoundaryDecay.physicalize, Network.Shore.inside,
        PhysicalGraph.traceNetwork, inducedShoreVertexEquiv, E, V, N, e]
    have hdst : (inducedShoreGraph G U).dst f.1 = V (N.dst e) := by
      simp [inducedShoreGraph, inducedPhysical, inducedNetwork,
        BoundaryDecay.physicalize, Network.Shore.inside,
        PhysicalGraph.traceNetwork, inducedShoreVertexEquiv, E, V, N, e]
    have hf := f.2
    unfold SafeCore.relativeCut SafeCore.crossing at hf
    simp only [Finset.mem_filter, Finset.mem_univ, true_and,
      Finset.mem_sdiff] at hf
    rw [hsrc, hdst] at hf
    have hsrcMem : V (N.src e) ∈ B ↔ G.src e.1 ∈ A := by
      simpa [N, Network.Shore.inside, PhysicalGraph.traceNetwork, V, B, e, E] using
        mem_inducedShoreImage G U A hAU (G.src e.1) e.2.1
    have hdstMem : V (N.dst e) ∈ B ↔ G.dst e.1 ∈ A := by
      simpa [N, Network.Shore.inside, PhysicalGraph.traceNetwork, V, B, e, E] using
        mem_inducedShoreImage G U A hAU (G.dst e.1) e.2.2
    rcases hf with h | h
    · left
      refine ⟨hsrcMem.1 h.1, ?_⟩
      exact (Finset.mem_sdiff).2 ⟨e.2.2,
        fun ha => h.2 (hdstMem.2 ha)⟩
    · right
      refine ⟨?_, hdstMem.1 h.2⟩
      exact (Finset.mem_sdiff).2 ⟨e.2.1,
        fun ha => h.1 (hsrcMem.2 ha)⟩
  · intro e
    simp [E]
  · intro f
    simp [E]

/-- Exact relative-cut size correspondence after physicalizing the induced
network. -/
theorem inducedShore_relativeCutSize_eq
    (G : PhysicalGraph) (U A : Finset G.Vertex) (hAU : A ⊆ U) :
    SafeCore.relativeCutSize (inducedShoreGraph G U) Finset.univ
        (inducedShoreImage G U A hAU) =
      SafeCore.relativeCutSize G U A := by
  classical
  let e := (relativeCutInsideEdgeEquiv G U A hAU).trans
    (insideNetworkPhysicalCutEquiv G U A hAU)
  have hc := Fintype.card_congr e
  simpa only [SafeCore.relativeCutSize, SafeCore.relativeCut,
    SafeCore.crossing, Fintype.card_coe] using hc.symm

/-- Shore-relative expansion transfers to the Fin-indexed physical induced
graph. Vertex subsets are handled by the explicit image/preimage equivalence. -/
theorem inducedShore_hasExpansion
    (G : PhysicalGraph) (U : Finset G.Vertex) (h : ℝ)
    (hExp : SafeCore.HasExpansion G U h) :
    SafeCore.HasExpansion (inducedShoreGraph G U) Finset.univ h := by
  intro B hB
  let A := inducedShorePreimage G U B
  have hAU : A ⊆ U := inducedShorePreimage_subset G U B
  have himage : inducedShoreImage G U A hAU = B := by
    exact inducedShoreImage_preimage_eq G U B
  have hcard := inducedShore_subset_card_eq G U B
  have hcomp : inducedShorePreimage G U (Finset.univ \ B) = U \ A := by
    ext v
    constructor
    · intro hv
      have hvU := inducedShorePreimage_subset G U (Finset.univ \ B) hv
      have hvnot := (Finset.mem_sdiff.1
        ((mem_inducedShorePreimage G U (Finset.univ \ B) v hvU).1 hv)).2
      refine Finset.mem_sdiff.2 ⟨hvU, ?_⟩
      intro hvA
      have hvA' : v ∈ inducedShorePreimage G U B := by simpa [A] using hvA
      exact hvnot ((mem_inducedShorePreimage G U B v hvU).1 hvA')
    · intro hv
      have hvU := (Finset.mem_sdiff.1 hv).1
      have hvnot := (Finset.mem_sdiff.1 hv).2
      apply (mem_inducedShorePreimage G U (Finset.univ \ B) v hvU).2
      apply Finset.mem_sdiff.2
      refine ⟨Finset.mem_univ _, ?_⟩
      intro hvB
      have hvA : v ∈ A := by
        simpa [A] using (mem_inducedShorePreimage G U B v hvU).2 hvB
      exact hvnot hvA
  have hcardComp : (U \ A).card = (Finset.univ \ B).card := by
    rw [← hcomp]
    exact inducedShore_subset_card_eq G U (Finset.univ \ B)
  have hcut := inducedShore_relativeCutSize_eq G U A hAU
  have hsource := hExp A hAU
  have hcardImage : (inducedShoreImage G U A hAU).card = A.card := by
    rw [himage]
    exact hcard.symm
  have hcardCompImage :
      (Finset.univ \ inducedShoreImage G U A hAU).card = (U \ A).card := by
    rw [himage]
    exact hcardComp.symm
  rw [← himage, hcardImage, hcardCompImage, hcut]
  exact hsource



/-- The physical induced degree is the host's exact internal labelled-edge
degree. -/
theorem inducedShore_degree_eq_traceInsideDegree
    (G : PhysicalGraph) (U : Finset G.Vertex)
    (v : Network.Shore.InsideVertex U) :
    (inducedShoreGraph G U).degree (inducedShoreVertexEquiv G U v) =
      G.traceInsideDegree U v.1 := by
  let N := Network.Shore.inside G.traceNetwork U
  let hs := inducedNetworkSimple G U
  have hnet : networkDegree N v = G.traceInsideDegree U v.1 := by
    classical
    unfold networkDegree
    unfold PhysicalGraph.traceInsideDegree PhysicalGraph.traceInsideEdgesAt
    apply Finset.card_bij (fun e _ => e.1)
    · intro e he
      simp only [Finset.mem_filter, Finset.mem_univ, true_and,
        Network.Shore.inside, PhysicalGraph.traceNetwork,
        PhysicalGraph.incident] at he ⊢
      rcases he with he | he
      · exact ⟨Or.inl (congrArg Subtype.val he), e.2⟩
      · exact ⟨Or.inr (congrArg Subtype.val he), e.2⟩
    · intro e he f hf h
      exact Subtype.ext h
    · intro e he
      simp only [Finset.mem_filter, Finset.mem_univ, true_and,
        PhysicalGraph.traceInsideEdgesAt, PhysicalGraph.incident] at he
      refine ⟨⟨e, he.2.1, he.2.2⟩, ?_, rfl⟩
      simp only [Finset.mem_filter, Finset.mem_univ, true_and,
        Network.Shore.inside, PhysicalGraph.traceNetwork,
        PhysicalGraph.incident]
      rcases he.1 with he | he
      · exact Or.inl (Subtype.ext he)
      · exact Or.inr (Subtype.ext he)
  have hphys := BoundaryDecay.physical_degree_eq N hs v
  simpa [inducedShoreGraph, inducedPhysical, inducedNetwork, N, hs] using
    hphys.trans hnet

/-- Min-degree two transfers from the shore's inside degree to the induced
physical graph. -/
theorem inducedShore_minTwo
    (G : PhysicalGraph) (U : Finset G.Vertex)
    (hmin : Erdos1016.SafeCore.MinTwo G U) :
    ∀ v : (inducedShoreGraph G U).Vertex,
      2 ≤ (inducedShoreGraph G U).degree v := by
  intro v
  let w := (inducedShoreVertexEquiv G U).symm v
  have hdeg := inducedShore_degree_eq_traceInsideDegree G U w
  have hdeg' : (inducedShoreGraph G U).degree v = G.traceInsideDegree U w.1 := by
    simpa [w] using hdeg
  rw [hdeg']
  exact hmin w.1 w.2

/-- A maximum inside-degree bound transfers in the same coordinates. -/
theorem inducedShore_maxDegree
    (G : PhysicalGraph) (U : Finset G.Vertex)
    (hmax : ∀ v ∈ U, G.traceInsideDegree U v ≤ 3) :
    ∀ v : (inducedShoreGraph G U).Vertex,
      (inducedShoreGraph G U).degree v ≤ 3 := by
  intro v
  let w := (inducedShoreVertexEquiv G U).symm v
  have hdeg := inducedShore_degree_eq_traceInsideDegree G U w
  calc
    (inducedShoreGraph G U).degree v = G.traceInsideDegree U w.1 := by
      simpa [w] using hdeg
    _ ≤ 3 := hmax w.1 w.2

/-- A connected actual shore remains connected after physicalizing its
induced graph. This is the connectivity input needed by the one-apex
boundary-average lemmas. -/
private theorem inReach_induce_reachable
    (G : PhysicalGraph) (U : Finset G.Vertex) {u v : G.Vertex}
    (p : InReach G U u v) :
    (G.toSimpleGraph.induce (↑U : Set G.Vertex)).Reachable
      ⟨u, p.source⟩ ⟨v, p.target⟩ := by
  induction p with
  | refl hu => exact .refl _
  | @step mid last p hw edge ih =>
      have hadj : (G.toSimpleGraph.induce (↑U : Set G.Vertex)).Adj
          ⟨mid, p.target⟩ ⟨last, hw⟩ := edge
      exact ih.trans hadj.reachable

theorem inducedShore_connected_of_connectedRegion
    (G : PhysicalGraph) (U : Finset G.Vertex)
    (hU : ConnectedRegion G U) :
    (inducedShoreGraph G U).IsConnected := by
  let N := Network.Shore.inside G.traceNetwork U
  have hN : N.graph.Connected := by
    rw [SimpleGraph.connected_iff_exists_forall_reachable]
    obtain ⟨root, hroot⟩ := hU.1
    refine ⟨⟨root, hroot⟩, ?_⟩
    intro v
    have hreach : (G.toSimpleGraph.induce (↑U : Set G.Vertex)).Reachable
        ⟨root, hroot⟩ v := by
      exact inReach_induce_reachable G U (hU.2 root hroot v.1 v.2)
    simpa only [N, Network.Shore.inside_graph_eq_induce,
      G.traceNetwork_graph] using hreach
  have hphysical :=
    (physicalReindex N (inducedNetworkSimple G U)).connected_iff.1 hN
  simpa [inducedShoreGraph, inducedPhysical, inducedNetwork, N] using hphysical

end Erdos1016.Extremal
