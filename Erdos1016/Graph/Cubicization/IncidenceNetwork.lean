import Erdos1016.Graph.Cubicization.IncidencePaths
import Erdos1016.CycleSpace.Incidence
import Erdos1016.Graph.Multigraph.Basic

set_option autoImplicit false
set_option maxHeartbeats 1000000

/-!
# Labelled edges of the incidence-path expansion

Internal path edges and original physical edges are different labels. This
network realizes the simple graph constructed in `IncidencePaths`; keeping
these labels is necessary to compare its binary cycle space with the original
one.
-/

noncomputable section
open scoped BigOperators

namespace Erdos1016.ShortProof.IncidencePaths

open BoundaryTrace
local instance incidenceNetworkDecidable (p : Prop) : Decidable p := Classical.propDecidable p

variable (G : PhysicalGraph) (W : Finset G.Edge)

abbrev PathEdge := (v : G.Vertex) × Fin (pathSize G W v - 1)

abbrev Edge := PathEdge G W ⊕ G.Edge

def pathSource (e : PathEdge G W) : Vertex G W :=
  ⟨e.1, e.2.castLE (Nat.sub_le _ _)⟩

def pathTarget (e : PathEdge G W) : Vertex G W :=
  ⟨e.1, ⟨e.2.val + 1, by have h := e.2.isLt; omega⟩⟩

lemma pathSource_ne_target (e : PathEdge G W) : pathSource G W e ≠ pathTarget G W e := by
  intro h
  have := congrArg (fun a : Vertex G W => a.2.val) h
  change e.2.val = e.2.val + 1 at this
  omega

def network : Network (Vertex G W) (Edge G W) where
  src := Sum.elim (pathSource G W) (source G W)
  dst := Sum.elim (pathTarget G W) (target G W)
  noLoops := by
    intro e
    cases e with
    | inl e => exact pathSource_ne_target G W e
    | inr e => exact source_ne_target G W e

lemma pathSource_injective : Function.Injective (pathSource G W) := by
  rintro ⟨v, i⟩ ⟨w, j⟩ h
  have hv := congrArg Sigma.fst h
  change v = w at hv
  subst w
  have hi := congrArg (fun a : Vertex G W => a.2.val) h
  exact congrArg (Sigma.mk v) (Fin.ext hi)

lemma path_endpoints_not_reversed (e f : PathEdge G W) :
    ¬ (pathSource G W e = pathTarget G W f ∧ pathTarget G W e = pathSource G W f) := by
  rintro ⟨hs, ht⟩
  have hs' := congrArg (fun a : Vertex G W => a.2.val) hs
  have ht' := congrArg (fun a : Vertex G W => a.2.val) ht
  change e.2.val = f.2.val + 1 at hs'
  change e.2.val + 1 = f.2.val at ht'
  omega

/-- No pair of network edge labels has the same unordered endpoints. -/
theorem network_simple (e f : Edge G W)
    (h : (((network G W).src e = (network G W).src f ∧
      (network G W).dst e = (network G W).dst f) ∨
      ((network G W).src e = (network G W).dst f ∧
      (network G W).dst e = (network G W).src f))) : e = f := by
  cases e with
  | inl e =>
    cases f with
    | inl f =>
      rcases h with h | h
      · exact congrArg Sum.inl (pathSource_injective G W h.1)
      · exact False.elim (path_endpoints_not_reversed G W e f h)
    | inr f =>
      rcases h with h | h
      · have hs := congrArg Sigma.fst h.1
        have ht := congrArg Sigma.fst h.2
        exact False.elim (G.noLoops f (hs.symm.trans ht))
      · have hs := congrArg Sigma.fst h.1
        have ht := congrArg Sigma.fst h.2
        exact False.elim (G.noLoops f (ht.symm.trans hs))
  | inr e =>
    cases f with
    | inl f =>
      rcases h with h | h
      · have hs := congrArg Sigma.fst h.1
        have ht := congrArg Sigma.fst h.2
        exact False.elim (G.noLoops e (hs.trans ht.symm))
      · have hs := congrArg Sigma.fst h.1
        have ht := congrArg Sigma.fst h.2
        exact False.elim (G.noLoops e (hs.trans ht.symm))
    | inr f =>
      rcases h with h | h
      · exact congrArg Sum.inr (incidenceVertex_edge_injective G W h.1)
      · exact congrArg Sum.inr (incidenceVertex_edge_injective G W h.1)

theorem network_graph : (network G W).graph = graph G W := by
  ext a b
  constructor
  · rintro ⟨e, h | h⟩
    · cases e with
      | inl e =>
        rcases h with ⟨rfl, rfl⟩
        exact Or.inl ⟨rfl, Or.inl rfl⟩
      | inr e => exact Or.inr ⟨e, Or.inl ⟨h.1.symm, h.2.symm⟩⟩
    · cases e with
      | inl e =>
        rcases h with ⟨rfl, rfl⟩
        exact Or.inl ⟨rfl, Or.inr rfl⟩
      | inr e => exact Or.inr ⟨e, Or.inr ⟨h.2.symm, h.1.symm⟩⟩
  · rintro (⟨hv, hi⟩ | ⟨e, h | h⟩)
    · rcases a with ⟨v, i⟩
      rcases b with ⟨w, j⟩
      dsimp at hv hi
      subst w
      rcases hi with hi | hi
      · have he : i.val < pathSize G W v - 1 := by have hj := j.isLt; omega
        refine ⟨Sum.inl ⟨v, ⟨i.val, he⟩⟩, Or.inl ⟨rfl, ?_⟩⟩
        exact vertex_ext G W rfl hi
      · have he : j.val < pathSize G W v - 1 := by have hi' := i.isLt; omega
        refine ⟨Sum.inl ⟨v, ⟨j.val, he⟩⟩, Or.inr ⟨rfl, ?_⟩⟩
        exact vertex_ext G W rfl hi
    · exact ⟨Sum.inr e, Or.inl ⟨h.1.symm, h.2.symm⟩⟩
    · exact ⟨Sum.inr e, Or.inr ⟨h.2.symm, h.1.symm⟩⟩

def vertexLabels : Vertex G W ≃ Fin (Fintype.card (Vertex G W)) := Fintype.equivFin _
def edgeLabels : Edge G W ≃ Fin (Fintype.card (Edge G W)) := Fintype.equivFin _

/-- A physical realization of the constructed simple network. -/
def physical : PhysicalGraph where
  vertexCount := Fintype.card (Vertex G W)
  edgeCount := Fintype.card (Edge G W)
  src e := vertexLabels G W ((network G W).src ((edgeLabels G W).symm e))
  dst e := vertexLabels G W ((network G W).dst ((edgeLabels G W).symm e))
  noLoops e h := (network G W).noLoops _ ((vertexLabels G W).injective h)
  simple e f h := by
    apply (edgeLabels G W).symm.injective
    apply network_simple G W
    rcases h with h | h
    · exact Or.inl ⟨(vertexLabels G W).injective h.1, (vertexLabels G W).injective h.2⟩
    · exact Or.inr ⟨(vertexLabels G W).injective h.1, (vertexLabels G W).injective h.2⟩

/-- The same physical realization viewed as a labelled multigraph. -/
def multigraph : FiniteMultiGraph where
  vertexCount := (physical G W).vertexCount
  edgeCount := (physical G W).edgeCount
  src := (physical G W).src
  dst := (physical G W).dst

end Erdos1016.ShortProof.IncidencePaths
