import Erdos1016.CycleSpace.Graphical.DisjointRegionCuts
import Erdos1016.ExactMaximumSupport.LargeGirth.PackingLocalSpacesProbability

set_option autoImplicit false
set_option maxHeartbeats 1500000

/-!
# The actual quotient of a cyclic-region packing

Each selected region is one fiber. Each component of its joint exterior is
one further fiber. All crossing physical labels remain separate.
-/
noncomputable section
open scoped BigOperators
namespace Erdos1016.ExactMaximumSupport.LargeGirth.PackingQuotient
open FiniteMultiGraph ConnectedContraction ExceptionalPartners
local instance packingQuotientDecidable (p : Prop) : Decidable p := Classical.propDecidable p

variable (G : FiniteMultiGraph) {ι : Type*} [Fintype ι] (X : ι → Finset G.Vertex)

abbrev OutsideVertex := {v : G.Vertex // ∀i,v∉X i}
def exterior : SimpleGraph (OutsideVertex G X) := G.toSimpleGraph.induce {v | ∀i,v∉X i}
noncomputable instance exteriorComponentFintype : Fintype (exterior G X).ConnectedComponent :=
  Fintype.ofFinite _
abbrev Label := ι ⊕ (exterior G X).ConnectedComponent

def label (v : G.Vertex) : Label G X :=
  if h : ∃i,v∈X i then Sum.inl (Classical.choose h)
  else Sum.inr ((exterior G X).connectedComponentMk ⟨v,by simpa using h⟩)

theorem label_eq_inl_iff (hdisj : Pairwise (fun i j => Disjoint (X i) (X j)))
    (v : G.Vertex) (i : ι) : label G X v=Sum.inl i ↔ v∈X i := by
  unfold label
  split_ifs with h
  · simp only [Sum.inl.injEq]
    constructor
    · intro heq
      exact heq ▸ Classical.choose_spec h
    · intro hi
      by_contra hne
      exact (Finset.disjoint_left.mp (hdisj hne)) (Classical.choose_spec h) hi
  · simp only [reduceCtorEq,false_iff]
    exact fun hi => h ⟨i,hi⟩

theorem label_outside (v : OutsideVertex G X) :
    label G X v.1=Sum.inr ((exterior G X).connectedComponentMk v) := by
  have h : ¬∃i,v.1∈X i := fun ⟨i,hi⟩ => v.2 i hi
  simp [label,h]

theorem label_eq_inr_iff (v : G.Vertex) (c : (exterior G X).ConnectedComponent) :
    label G X v=Sum.inr c ↔ ∃h : ∀i,v∉X i,
      (exterior G X).connectedComponentMk ⟨v,h⟩=c := by
  unfold label
  split_ifs with h
  · simp only [reduceCtorEq,false_iff]
    rintro ⟨hn,_⟩
    obtain ⟨i,hi⟩ := h
    exact hn i hi
  · have hn : ∀i,v∉X i := by simpa using h
    simp only [Sum.inr.injEq]
    exact ⟨fun hh => ⟨hn,hh⟩,fun ⟨_,hh⟩ => hh⟩

/-- Every quotient fiber is an actual connected induced subgraph. -/
theorem connectedFibers (hdisj : Pairwise (fun i j => Disjoint (X i) (X j)))
    (hconn : ∀i,(G.toSimpleGraph.induce (↑(X i):Set G.Vertex)).Connected) :
    ConnectedFibers G (label G X) := by
  intro q
  cases q with
  | inl i =>
      have hs : {v | label G X v=Sum.inl i}=(↑(X i):Set G.Vertex) := by
        ext v
        exact label_eq_inl_iff G X hdisj v i
      exact Eq.mpr (congrArg (fun S : Set G.Vertex => (G.toSimpleGraph.induce S).Connected) hs) (hconn i)
  | inr c =>
      let f : (exterior G X).induce c.supp →g
          G.toSimpleGraph.induce {v | label G X v=Sum.inr c} :=
        { toFun := fun v => ⟨v.1.1,by
            change label G X v.1.1=Sum.inr c
            rw [label_outside]
            exact congrArg Sum.inr v.2⟩
          map_rel' := fun h => h }
      apply c.connected_induce_supp.map f
      intro v
      obtain ⟨hv,hc⟩ := (label_eq_inr_iff G X v.1 c).mp v.2
      exact ⟨⟨⟨v.1,hv⟩,hc⟩,rfl⟩

abbrev graph : FiniteMultiGraph := quotient G (label G X)
def vertex (v : G.Vertex) : (graph G X).Vertex := vertexEquiv (label G X v)
def mark (i : ι) : (graph G X).Vertex := vertexEquiv (Sum.inl i : Label G X)

theorem mark_injective : Function.Injective (mark G X) := by
  intro i j h
  exact Sum.inl_injective (vertexEquiv.injective h)

theorem vertex_eq_mark_iff (hdisj : Pairwise (fun i j => Disjoint (X i) (X j)))
    (v : G.Vertex) (i : ι) : vertex G X v=mark G X i ↔ v∈X i := by
  exact (vertexEquiv.injective.eq_iff).trans (label_eq_inl_iff G X hdisj v i)

theorem graph_noLoops : ∀e,(graph G X).src e≠(graph G X).dst e := by
  intro e h
  exact ((edgeEquiv G (label G X)).symm e).2 (vertexEquiv.injective h)

theorem graph_connected (hG : G.toSimpleGraph.Connected)
    (hdisj : Pairwise (fun i j => Disjoint (X i) (X j)))
    (hconn : ∀i,(G.toSimpleGraph.induce (↑(X i):Set G.Vertex)).Connected) :
    (graph G X).toSimpleGraph.Connected :=
  quotient_connected G (label G X) hG (connectedFibers G X hdisj hconn)

theorem fiberCutSize_eq (hdisj : Pairwise (fun i j => Disjoint (X i) (X j))) (i : ι) :
    fiberCutSize G (label G X) (Sum.inl i)=(G.cutEdges (X i)).card := by
  unfold fiberCutSize FiberCutIncidence
  rw [Nat.card_eq_fintype_card,Fintype.card_subtype]
  unfold cutEdges
  congr 1
  ext e
  simp only [Finset.mem_filter,Finset.mem_univ,true_and,ne_eq,label_eq_inl_iff G X hdisj]
  tauto

/-- The quotient star retains the exact original cut multiplicity. -/
theorem mark_degree (hdisj : Pairwise (fun i j => Disjoint (X i) (X j))) (i : ι) :
    (graph G X).degree (mark G X i)=(G.cutEdges (X i)).card := by
  rw [← PackingLocalSpaces.starEdges_card _ _ (graph_noLoops G X)]
  have he : PackingLocalSpaces.starEdges (graph G X) (mark G X i)=
      Finset.univ.filter (fun e =>
        ((graph G X).src e=mark G X i ∧ (graph G X).dst e≠mark G X i) ∨
        ((graph G X).dst e=mark G X i ∧ (graph G X).src e≠mark G X i)) := by
    ext e
    simp only [PackingLocalSpaces.starEdges,Finset.mem_filter,Finset.mem_univ,true_and]
    have hn : ¬((graph G X).src e=mark G X i ∧ (graph G X).dst e=mark G X i) :=
      fun h => graph_noLoops G X e (h.1.trans h.2.symm)
    tauto
  rw [he]
  change cutSizeAt (graph G X) (mark G X i)=_
  change cutSizeAt (quotient G (label G X)) (vertexEquiv (Sum.inl i : Label G X))=_
  rw [cutSizeAt_quotient,fiberCutSize_eq G X hdisj]

theorem fiberZeroCut_eq (hdisj : Pairwise (fun i j => Disjoint (X i) (X j))) (i : ι) :
    FiberZeroCut G (label G X) (Sum.inl i)=DisjointRegionCuts.ZeroCut G (X i) := by
  funext x
  apply propext
  simp only [FiberZeroCut,FiberCutIncidence,Subtype.forall,DisjointRegionCuts.ZeroCut,cutEdges,
    Finset.mem_filter,Finset.mem_univ,true_and,ne_eq,label_eq_inl_iff G X hdisj]
  aesop

/-- A connected exterior marker is contained in one unmarked fiber. -/
theorem marker_single_fiber (P : Finset G.Vertex)
    (hP : (G.toSimpleGraph.induce (↑P:Set G.Vertex)).Connected)
    (hPX : ∀i,Disjoint P (X i)) :
    ∃ c : (exterior G X).ConnectedComponent, ∀v∈P,label G X v=Sum.inr c := by
  obtain ⟨p⟩ := hP.nonempty
  have hout (v : P) : ∀i,v.1∉X i := fun i hi => (Finset.disjoint_left.mp (hPX i)) v.2 hi
  let f : G.toSimpleGraph.induce (↑P:Set G.Vertex) →g exterior G X :=
    { toFun := fun v => ⟨v.1,hout v⟩
      map_rel' := fun h => h }
  refine ⟨(exterior G X).connectedComponentMk (f p),?_⟩
  intro v hv
  rw [label_outside G X (⟨v,hout ⟨v,hv⟩⟩:OutsideVertex G X)]
  exact congrArg Sum.inr (SimpleGraph.ConnectedComponent.sound
    ((hP.preconnected ⟨v,hv⟩ p).map f))

end Erdos1016.ExactMaximumSupport.LargeGirth.PackingQuotient
