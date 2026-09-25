import Erdos1016.CycleSpace.Graphical.RegionCutLaw
import Erdos1016.Graph.Multigraph.Forest

set_option autoImplicit false

/-!
# Exceptional cuts for a disjoint family of connected regions

The quotient partition is constructed here. Each specified region becomes
one fiber, and every uncovered original vertex is its own singleton fiber.
Thus callers need only the graph and the actual disjoint connected regions.
-/

noncomputable section

namespace Erdos1016.FiniteMultiGraph.DisjointRegionCuts

open ConnectedContraction

variable (G : FiniteMultiGraph) {ι : Type*} [Fintype ι] (U : ι → Finset G.Vertex)

local instance disjointRegionDecidable (p : Prop) : Decidable p := Classical.propDecidable p

abbrev OutsideVertex := {v : G.Vertex // ∀ i, v ∉ U i}
abbrev Label := ι ⊕ OutsideVertex G U

def label : G.Vertex → Label G U := fun v =>
  if h : ∃ i, v ∈ U i then Sum.inl (Classical.choose h)
  else Sum.inr ⟨v, by simpa using h⟩

theorem label_eq_inl_iff (hdisj : Pairwise (fun i j => Disjoint (U i) (U j)))
    (v : G.Vertex) (i : ι) : label G U v = Sum.inl i ↔ v ∈ U i := by
  unfold label
  split_ifs with h
  · simp only [Sum.inl.injEq]
    constructor
    · intro heq
      exact heq ▸ Classical.choose_spec h
    · intro hi
      by_contra hne
      exact (Finset.disjoint_left.mp (hdisj hne)) (Classical.choose_spec h) hi
  · simp only [Sum.inr.injEq, reduceCtorEq, false_iff]
    exact fun hi => h ⟨i, hi⟩

theorem label_eq_inr_iff (v : G.Vertex) (t : OutsideVertex G U) :
    label G U v = Sum.inr t ↔ v = t.1 := by
  unfold label
  split_ifs with h
  · simp only [reduceCtorEq, false_iff]
    intro heq
    exact t.2 (Classical.choose h) (heq ▸ Classical.choose_spec h)
  · simp only [Sum.inr.injEq]
    exact ⟨fun h => congrArg Subtype.val h, fun heq => Subtype.ext heq⟩

/-- All fibers are connected: the selected ones by hypothesis, all others
because they are singletons. -/
theorem connectedFibers (hdisj : Pairwise (fun i j => Disjoint (U i) (U j)))
    (hconn : ∀ i, (G.toSimpleGraph.induce (↑(U i) : Set G.Vertex)).Connected) :
    ConnectedFibers G (label G U) := by
  intro q
  cases q with
  | inl i =>
      have hset : {v | label G U v = Sum.inl i} = (↑(U i) : Set G.Vertex) := by
        ext v
        exact label_eq_inl_iff G U hdisj v i
      exact Eq.mpr (congrArg (fun S : Set G.Vertex => (G.toSimpleGraph.induce S).Connected) hset) (hconn i)
  | inr t =>
      have hset : {v | label G U v = Sum.inr t} = {v | v = t.1} := by
        ext v
        exact label_eq_inr_iff G U v t
      apply Eq.mpr (congrArg (fun S : Set G.Vertex => (G.toSimpleGraph.induce S).Connected) hset)
      letI : Nonempty ↑({v : G.Vertex | v = t.1} : Set G.Vertex) := ⟨⟨t.1, rfl⟩⟩
      refine ⟨?_⟩
      intro u v
      have heq : u = v := Subtype.ext (u.2.trans v.2.symm)
      subst v
      exact .refl _

/-- The original region cut-zero event, on actual edge labels. -/
def ZeroCut (S : Finset G.Vertex) (x : G.CycleSpace) : Prop :=
  ∀ e ∈ G.cutEdges S, x.1 e = 0

theorem fiberZeroCut_eq (hdisj : Pairwise (fun i j => Disjoint (U i) (U j))) (i : ι) :
    FiberZeroCut G (label G U) (Sum.inl i) = ZeroCut G (U i) := by
  funext x
  apply propext
  simp only [FiberZeroCut, FiberCutIncidence, Subtype.forall, ZeroCut, cutEdges,
    Finset.mem_filter, Finset.mem_univ, true_and, ne_eq, label_eq_inl_iff G U hdisj]
  aesop

theorem fiberCutSize_eq (hdisj : Pairwise (fun i j => Disjoint (U i) (U j))) (i : ι) :
    fiberCutSize G (label G U) (Sum.inl i) = (G.cutEdges (U i)).card := by
  unfold fiberCutSize FiberCutIncidence
  rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
  unfold cutEdges
  congr 1
  ext e
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, ne_eq, label_eq_inl_iff G U hdisj]
  tauto

/-- The precise exceptional-cut predicate in the original graph. -/
def Exceptional (i j : ι) : Prop :=
  2 * Finite.density (ZeroCut G (U i)) * Finite.density (ZeroCut G (U j)) <
    Finite.density (fun x => ZeroCut G (U i) x ∧ ZeroCut G (U j) x)

/-- Lemma 1, with the contraction partition and its cut law proved from the
actual disjoint connected regions. -/
theorem exceptional_partner_card_le (hG : G.toSimpleGraph.Connected)
    (hdisj : Pairwise (fun i j => Disjoint (U i) (U j)))
    (hconn : ∀ i, (G.toSimpleGraph.induce (↑(U i) : Set G.Vertex)).Connected)
    (i : ι) (s : Finset ι) :
    (s.filter fun j => j ≠ i ∧ Exceptional G U i j).card ≤ (G.cutEdges (U i)).card := by
  let emb : ι ↪ Label G U := ⟨Sum.inl, Sum.inl_injective⟩
  have h := exceptionalCut_partner_card_le G (label G U) hG
    (connectedFibers G U hdisj hconn) (Sum.inl i) (s.map emb)
  rw [fiberCutSize_eq G U hdisj] at h
  have hexc (j : ι) : ExceptionalCut G (label G U) (Sum.inl i) (Sum.inl j) ↔
      Exceptional G U i j := by
    unfold ExceptionalCut Exceptional
    rw [fiberZeroCut_eq G U hdisj i, fiberZeroCut_eq G U hdisj j]
  simpa only [Finset.filter_map, Finset.card_map, emb, Function.Embedding.coeFn_mk,
    Function.comp_def, ne_eq, Sum.inl.injEq, hexc] using h

end Erdos1016.FiniteMultiGraph.DisjointRegionCuts
