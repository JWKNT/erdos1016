import Erdos1016.Cleanup.Root.OutsideComponentPartitions

set_option autoImplicit false

noncomputable section
namespace Erdos1016.Proof.OutsideComponentRoot

open Erdos1016
open Erdos1016.Proof.CleanupSpecification
open Erdos1016.Proof.ComponentExtraction
open Erdos1016.Proof.ProtectedExteriorComponents
open Erdos1016.Proof.OutsideComponentPartitions

local instance outsideRootDecidable (p : Prop) : Decidable p :=
  Classical.propDecidable p

private theorem outsideComponent_support_mem
    (Γ : FiniteMultiGraph) (P : Finset Γ.Vertex)
    (c : OutsideComponent Γ P)
    (x : {v : {w : Γ.Vertex // w ∈ (↑(Pᶜ) : Set Γ.Vertex)} // v ∈ c.supp}) :
    x.1.1 ∈ outsideComponentVertices Γ P c := by
  change x.1.1 ∈ Finset.univ.filter _
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  exact ⟨x.1, x.2, rfl⟩

/-- A component of the simple graph outside P is connected as an induced
subgraph of the labelled multigraph's underlying simple graph. The existing
component extraction tracks labels for rank; this lemma exposes the actual
cleanup-root connectedness interface. -/
theorem outsideComponent_induce_connected
    (Γ : FiniteMultiGraph) (P : Finset Γ.Vertex)
    (c : OutsideComponent Γ P) :
    (Γ.toSimpleGraph.induce
      (↑(outsideComponentVertices Γ P c) : Set Γ.Vertex)).Connected := by
  classical
  let Q := Γ.toSimpleGraph.induce (↑(Pᶜ) : Set Γ.Vertex)
  let J := Q.induce c.supp
  let H := outsideComponentVertices Γ P c
  let K := Γ.toSimpleGraph.induce (↑H : Set Γ.Vertex)
  let f : J →g K := {
    toFun := fun x => ⟨x.1.1, outsideComponent_support_mem Γ P c x⟩
    map_rel' := by intro _ _ hadj; exact hadj }
  have hsurj : Function.Surjective f := by
    intro y
    have hdisj := componentVertexSet_disjoint Γ.toSimpleGraph P c
    have hyP : y.1 ∉ P := (Finset.disjoint_left.mp hdisj) y.2
    let q : OutsideVertex Γ P := ⟨y.1, Finset.mem_compl.mpr hyP⟩
    have hcc : Q.connectedComponentMk q = c :=
      (outsideComponentVertex_mem_iff Γ P c y.1 hyP).1 y.2
    have hq : q ∈ c.supp :=
      (SimpleGraph.ConnectedComponent.mem_supp_iff c q).mpr hcc
    refine ⟨⟨q, hq⟩, ?_⟩
    apply Subtype.ext
    rfl
  have hstep : ∀ ⦃u v⦄, J.Adj u v → f u = f v ∨ K.Adj (f u) (f v) := by
    intro u v huv
    right
    exact huv
  exact AssembledCorridorCompression.SimpleGraph.connected_of_surjective_step
    J K f hsurj hstep c.connected_induce_supp

/-- Once loops and parallel labels have been excluded outside P, every whole
connected component of Γ-P is an `IsCleanupRoot`. Connectedness comes from
its component support; simplicity is a separate labelled-edge fact. -/
theorem outsideComponent_isCleanupRoot
    (Γ : FiniteMultiGraph) (P : Finset Γ.Vertex)
    (c : OutsideComponent Γ P)
    (hnoLoop : ∀ e : Γ.Edge, Γ.src e ∉ P → Γ.dst e ∉ P →
      Γ.src e ≠ Γ.dst e)
    (hnoParallel : ∀ e f : Γ.Edge,
      Γ.src e ∉ P → Γ.dst e ∉ P → Γ.src f ∉ P → Γ.dst f ∉ P →
      (((Γ.src e = Γ.src f ∧ Γ.dst e = Γ.dst f) ∨
        (Γ.src e = Γ.dst f ∧ Γ.dst e = Γ.src f))) → e = f) :
    IsCleanupRoot Γ (outsideComponentVertices Γ P c) := by
  classical
  let H := outsideComponentVertices Γ P c
  have hdisj := componentVertexSet_disjoint Γ.toSimpleGraph P c
  have hnotP : ∀ v ∈ H, v ∉ P := by
    intro v hv
    exact (Finset.disjoint_left.mp hdisj) hv
  refine ⟨outsideComponent_induce_connected Γ P c, ?_, ?_⟩
  · intro e hs ht
    exact hnoLoop e (hnotP _ hs) (hnotP _ ht)
  · intro e f hse hte hsf htf hends
    exact hnoParallel e f (hnotP _ hse) (hnotP _ hte)
      (hnotP _ hsf) (hnotP _ htf) hends



end Erdos1016.Proof.OutsideComponentRoot
end
