import Erdos1016.Cleanup.Root.ComponentExtraction

set_option autoImplicit false

noncomputable section

namespace Erdos1016.Proof.OutsideComponentPartitions

open Erdos1016
open Erdos1016.FiniteMultiGraph
open Erdos1016.Proof.ComponentExtraction
open Erdos1016.Proof.CleanupSpecification
open Erdos1016.Proof.ProtectedExteriorComponents

abbrev OutsideGraph (Γ : FiniteMultiGraph) (P : Finset Γ.Vertex) :=
  Γ.toSimpleGraph.induce (↑(Pᶜ) : Set Γ.Vertex)

abbrev OutsideVertex (Γ : FiniteMultiGraph) (P : Finset Γ.Vertex) :=
  {v : Γ.Vertex // v ∈ (↑(Pᶜ) : Set Γ.Vertex)}

abbrev OutsideEdge (Γ : FiniteMultiGraph) (P : Finset Γ.Vertex) :=
  {e : Γ.Edge // Γ.src e ∉ P ∧ Γ.dst e ∉ P}

theorem outsideComponentVertex_mem_iff
    (Γ : FiniteMultiGraph) (P : Finset Γ.Vertex)
    (c : OutsideComponent Γ P) (v : Γ.Vertex) (hv : v ∉ P) :
    v ∈ outsideComponentVertices Γ P c ↔
      (OutsideGraph Γ P).connectedComponentMk ⟨v, Finset.mem_compl.mpr hv⟩ = c := by
  classical
  unfold outsideComponentVertices componentVertexSet
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact (SimpleGraph.ConnectedComponent.mem_supp_iff c x).mp hx
  · intro h
    exact ⟨⟨v, Finset.mem_compl.mpr hv⟩,
      (SimpleGraph.ConnectedComponent.mem_supp_iff c _).mpr h, rfl⟩

noncomputable def outsideVertexPartitionEquiv
    (Γ : FiniteMultiGraph) (P : Finset Γ.Vertex) :
    (Σ c : OutsideComponent Γ P,
      {v : Γ.Vertex // v ∈ outsideComponentVertices Γ P c}) ≃
      OutsideVertex Γ P := by
  classical
  letI : Fintype (OutsideComponent Γ P) := SetLike.instFintype
  refine
    { toFun := fun x =>
        ⟨x.2.1, Finset.mem_compl.mpr ((Finset.disjoint_left.mp
          (componentVertexSet_disjoint Γ.toSimpleGraph P x.1)) x.2.2)⟩
      invFun := fun v =>
        ⟨(OutsideGraph Γ P).connectedComponentMk ⟨v.1, v.2⟩,
          ⟨v.1, (outsideComponentVertex_mem_iff Γ P _ v.1
            (Finset.mem_compl.mp v.2)).2 rfl⟩⟩
      left_inv := by
        intro x
        rcases x with ⟨c, v⟩
        have hc : (OutsideGraph Γ P).connectedComponentMk
            ⟨v.1, Finset.mem_compl.mpr
              ((Finset.disjoint_left.mp
                (componentVertexSet_disjoint Γ.toSimpleGraph P c)) v.2)⟩ = c :=
          (outsideComponentVertex_mem_iff Γ P c v.1
            (Finset.disjoint_left.mp
              (componentVertexSet_disjoint Γ.toSimpleGraph P c) v.2)).1 v.2
        have hsets := congrArg (outsideComponentVertices Γ P) hc
        apply Sigma.ext hc
        exact (Subtype.heq_iff_coe_eq (by intro z; simp [hsets])).2 rfl
      right_inv := by
        intro v
        apply Subtype.ext
        rfl }

theorem sum_outside_component_vertex_card
    (Γ : FiniteMultiGraph) (P : Finset Γ.Vertex) :
    (∑ c : OutsideComponent Γ P,
      (outsideComponentVertices Γ P c).card) = Pᶜ.card := by
  classical
  letI : Fintype (OutsideComponent Γ P) := SetLike.instFintype
  have hcardLocal (c : OutsideComponent Γ P) :
      (outsideComponentVertices Γ P c).card =
        Fintype.card {v : Γ.Vertex // v ∈ outsideComponentVertices Γ P c} := by
    symm
    exact Fintype.card_coe (outsideComponentVertices Γ P c)
  have hsig :
      Fintype.card
        (Σ c : OutsideComponent Γ P,
          {v : Γ.Vertex // v ∈ outsideComponentVertices Γ P c}) =
        ∑ c : OutsideComponent Γ P,
          Fintype.card {v : Γ.Vertex // v ∈ outsideComponentVertices Γ P c} :=
    Fintype.card_sigma
  calc
    (∑ c : OutsideComponent Γ P, (outsideComponentVertices Γ P c).card) =
        ∑ c : OutsideComponent Γ P,
          Fintype.card {v : Γ.Vertex // v ∈ outsideComponentVertices Γ P c} := by
      apply Finset.sum_congr rfl
      intro c hc
      exact hcardLocal c
    _ = Fintype.card
        (Σ c : OutsideComponent Γ P,
          {v : Γ.Vertex // v ∈ outsideComponentVertices Γ P c}) := hsig.symm
    _ = Fintype.card (OutsideVertex Γ P) :=
      Fintype.card_congr (outsideVertexPartitionEquiv Γ P)
    _ = Pᶜ.card := by
      simp [Finset.card_compl]

noncomputable def outsideEdgePartitionEquiv
    (Γ : FiniteMultiGraph) (P : Finset Γ.Vertex) :
    (Σ c : OutsideComponent Γ P,
      {e : Γ.Edge // e ∈ internalEdges Γ (outsideComponentVertices Γ P c)}) ≃
      OutsideEdge Γ P := by
  classical
  letI : Fintype (OutsideComponent Γ P) := SetLike.instFintype
  refine
    { toFun := fun x => ⟨x.2.1, ?_⟩
      invFun := fun e =>
        ⟨(OutsideGraph Γ P).connectedComponentMk
            ⟨Γ.src e.1, Finset.mem_compl.mpr e.2.1⟩,
          ⟨e.1, Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩⟩⟩
      left_inv := ?_
      right_inv := ?_ }
  · have hs := (Finset.mem_filter.mp x.2.2).2.1
    have ht := (Finset.mem_filter.mp x.2.2).2.2
    have hdisj := componentVertexSet_disjoint Γ.toSimpleGraph P x.1
    exact ⟨(Finset.disjoint_left.mp hdisj) hs,
      (Finset.disjoint_left.mp hdisj) ht⟩
  · have hs := e.2.1
    have ht := e.2.2
    let u : OutsideVertex Γ P := ⟨Γ.src e.1, Finset.mem_compl.mpr hs⟩
    let v : OutsideVertex Γ P := ⟨Γ.dst e.1, Finset.mem_compl.mpr ht⟩
    have hcc : (OutsideGraph Γ P).connectedComponentMk u =
        (OutsideGraph Γ P).connectedComponentMk v := by
      by_cases hne : Γ.src e.1 = Γ.dst e.1
      · have huv : u = v := Subtype.ext hne
        exact congrArg (OutsideGraph Γ P).connectedComponentMk huv
      · apply SimpleGraph.ConnectedComponent.connectedComponentMk_eq_of_adj
        exact ⟨hne, e.1, Or.inl ⟨rfl, rfl⟩⟩
    let c : OutsideComponent Γ P := (OutsideGraph Γ P).connectedComponentMk u
    have hsrc : Γ.src e.1 ∈ outsideComponentVertices Γ P c :=
      (outsideComponentVertex_mem_iff Γ P c _ hs).2 rfl
    have hdst : Γ.dst e.1 ∈ outsideComponentVertices Γ P c :=
      (outsideComponentVertex_mem_iff Γ P c _ ht).2 hcc.symm
    exact ⟨hsrc, hdst⟩
  · intro x
    rcases x with ⟨c, e⟩
    have hs := (Finset.mem_filter.mp e.2).2.1
    have hc : (OutsideGraph Γ P).connectedComponentMk
        ⟨Γ.src e.1, Finset.mem_compl.mpr
          ((Finset.disjoint_left.mp
            (componentVertexSet_disjoint Γ.toSimpleGraph P c)) hs)⟩ = c :=
      (outsideComponentVertex_mem_iff Γ P c (Γ.src e.1)
        ((Finset.disjoint_left.mp
          (componentVertexSet_disjoint Γ.toSimpleGraph P c)) hs)).1 hs
    have hsets := congrArg (outsideComponentVertices Γ P) hc
    apply Sigma.ext hc
    exact (Subtype.heq_iff_coe_eq (by intro z; simp [hsets, internalEdges])).2 rfl
  · intro e
    apply Subtype.ext
    rfl

theorem sum_outside_component_internal_edge_card
    (Γ : FiniteMultiGraph) (P : Finset Γ.Vertex) :
    (∑ c : OutsideComponent Γ P,
      (internalEdges Γ (outsideComponentVertices Γ P c)).card) =
        (internalEdges Γ Pᶜ).card := by
  classical
  letI : Fintype (OutsideComponent Γ P) := SetLike.instFintype
  have hcardLocal (c : OutsideComponent Γ P) :
      (internalEdges Γ (outsideComponentVertices Γ P c)).card =
        Fintype.card {e : Γ.Edge // e ∈
          internalEdges Γ (outsideComponentVertices Γ P c)} := by
    symm
    exact Fintype.card_coe _
  have hsig :
      Fintype.card
        (Σ c : OutsideComponent Γ P,
          {e : Γ.Edge // e ∈ internalEdges Γ (outsideComponentVertices Γ P c)}) =
        ∑ c : OutsideComponent Γ P,
          Fintype.card {e : Γ.Edge // e ∈
            internalEdges Γ (outsideComponentVertices Γ P c)} :=
    Fintype.card_sigma
  calc
    (∑ c : OutsideComponent Γ P,
      (internalEdges Γ (outsideComponentVertices Γ P c)).card) =
        ∑ c : OutsideComponent Γ P,
          Fintype.card {e : Γ.Edge // e ∈
            internalEdges Γ (outsideComponentVertices Γ P c)} := by
      apply Finset.sum_congr rfl
      intro c hc
      exact hcardLocal c
    _ = Fintype.card
        (Σ c : OutsideComponent Γ P,
          {e : Γ.Edge // e ∈ internalEdges Γ (outsideComponentVertices Γ P c)}) :=
            hsig.symm
    _ = Fintype.card (OutsideEdge Γ P) :=
      Fintype.card_congr (outsideEdgePartitionEquiv Γ P)
    _ = (internalEdges Γ Pᶜ).card := by
      let e : OutsideEdge Γ P ≃
          {e : Γ.Edge // e ∈ internalEdges Γ Pᶜ} := {
        toFun := fun e => ⟨e.1, by
          change e.1 ∈ Finset.univ.filter _
          simp only [Finset.mem_filter, Finset.mem_univ, true_and]
          simpa [Finset.mem_compl] using e.2⟩
        invFun := fun e => ⟨e.1, by
          have he := Finset.mem_filter.mp e.2
          simpa [OutsideEdge, Finset.mem_compl] using he.2⟩
        left_inv := by intro x; apply Subtype.ext; rfl
        right_inv := by intro x; apply Subtype.ext; rfl }
      calc
        Fintype.card (OutsideEdge Γ P) =
            Fintype.card {e : Γ.Edge // e ∈ internalEdges Γ Pᶜ} :=
          Fintype.card_congr e
        _ = (internalEdges Γ Pᶜ).card := Fintype.card_coe _

end Erdos1016.Proof.OutsideComponentPartitions

end
