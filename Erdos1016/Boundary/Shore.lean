import Erdos1016.Graph.Reindex
import Erdos1016.Boundary.OwnerAndApex

set_option autoImplicit false

/-!
# The original-exterior theorem for an arbitrary actual vertex shore

This module constructs every part of the ported model from a network and a
vertex set. The local and exterior edges are literally the original edges
with both endpoints on the respective side. The cut labels are the original
crossing edges. No range identification or affine lifting is a hypothesis.

The inequality holds for ANY internal event, hence in particular for forest
restriction. A nonempty exterior is used only to choose the one redundant
component equation that is omitted.
-/

noncomputable section
open scoped BigOperators

namespace Erdos1016.BoundaryTrace

def actualShoreDecidable (p : Prop) : Decidable p := Classical.propDecidable p

local instance actualShoreDecidableInst (p : Prop) : Decidable p :=
  actualShoreDecidable p

namespace Ported

variable {U V EI EO P Q : Type*}
  [Fintype U] [Fintype V] [Fintype EI] [Fintype EO]
  [Fintype P] [Fintype Q]
  {I : Network U EI} {O : Network V EO}

/-- Relabel the pins by a genuine bijection; none is deleted or merged. -/
def relabelPins (L : Ported I O P) (e : P ≃ Q) : Ported I O Q where
  inside := L.inside ∘ e.symm
  outside := L.outside ∘ e.symm

/-- The one-apex networks retain the same physical edges under pin relabelling. -/
def relabelPinsApexReindex (L : Ported I O P) (e : P ≃ Q) :
    Network.Reindex L.apex (L.relabelPins e).apex where
  vertices := Equiv.refl _
  edges := Equiv.sumCongr (Equiv.refl EI) e
  endpoints := by
    intro f
    cases f with
    | inl f => exact Or.inl ⟨rfl, rfl⟩
    | inr p =>
      left
      simp [apex, relabelPins]

/-- Relabelling does not change any event depending on the original inner word. -/
theorem apexFraction_relabelPins (L : Ported I O P) (e : P ≃ Q)
    (Good : I.Word → Prop) :
    (L.relabelPins e).apexFraction Good = L.apexFraction Good := by
  symm
  unfold apexFraction
  apply Finite.density_equiv (L.relabelPinsApexReindex e).cycleEquiv
  intro w
  have hin : ((L.relabelPins e).apexWordEquiv
        ((L.relabelPinsApexReindex e).cycleEquiv w).1).1 =
      (L.apexWordEquiv w.1).1 := by
    funext f
    exact (L.relabelPinsApexReindex e).wordEquiv_apply_edge w.1 (Sum.inl f)
  rw [hin]

end Ported

namespace Network
namespace Shore

variable {V E : Type*} [Fintype V] [Fintype E]

abbrev InsideVertex (S : Finset V) := {v : V // v ∈ S}
abbrev OutsideVertex (S : Finset V) := {v : V // v ∉ S}

abbrev InsideEdge (N : Network V E) (S : Finset V) :=
  {e : E // N.src e ∈ S ∧ N.dst e ∈ S}

abbrev OutsideEdge (N : Network V E) (S : Finset V) :=
  {e : E // N.src e ∉ S ∧ N.dst e ∉ S}

abbrev CutEdge (N : Network V E) (S : Finset V) :=
  {e : E // (N.src e ∈ S ∧ N.dst e ∉ S) ∨
    (N.src e ∉ S ∧ N.dst e ∈ S)}

/-- Named finite instances used by the complete boundary law. Exposing them
lets later relabellings reuse the exact enumeration chosen here. -/
noncomputable def insideVertexFintype (N : Network V E) (S : Finset V) :
    Fintype (InsideVertex S) := by
  exact inferInstance

noncomputable def outsideVertexFintype (N : Network V E) (S : Finset V) :
    Fintype (OutsideVertex S) := by
  exact inferInstance

noncomputable def insideEdgeFintype (N : Network V E) (S : Finset V) :
    Fintype (InsideEdge N S) := by
  exact inferInstance

noncomputable def outsideEdgeFintype (N : Network V E) (S : Finset V) :
    Fintype (OutsideEdge N S) := by
  exact inferInstance

noncomputable def cutEdgeFintype (N : Network V E) (S : Finset V) :
    Fintype (CutEdge N S) := by
  exact inferInstance

def inside (N : Network V E) (S : Finset V) :
    Network (InsideVertex S) (InsideEdge N S) where
  src e := ⟨N.src e.1, e.2.1⟩
  dst e := ⟨N.dst e.1, e.2.2⟩
  noLoops e h := N.noLoops e.1 (congrArg Subtype.val h)

def outside (N : Network V E) (S : Finset V) :
    Network (OutsideVertex S) (OutsideEdge N S) where
  src e := ⟨N.src e.1, e.2.1⟩
  dst e := ⟨N.dst e.1, e.2.2⟩
  noLoops e h := N.noLoops e.1 (congrArg Subtype.val h)

def insidePin (N : Network V E) (S : Finset V) (e : CutEdge N S) : InsideVertex S :=
  if hs : N.src e.1 ∈ S then ⟨N.src e.1, hs⟩
  else ⟨N.dst e.1, by
    rcases e.2 with h | h
    · exact False.elim (hs h.1)
    · exact h.2⟩

def outsidePin (N : Network V E) (S : Finset V) (e : CutEdge N S) : OutsideVertex S :=
  if hs : N.src e.1 ∈ S then ⟨N.dst e.1, by
    rcases e.2 with h | h
    · exact h.2
    · exact False.elim (h.1 hs)⟩
  else ⟨N.src e.1, hs⟩



def ported (N : Network V E) (S : Finset V) :
    Ported (inside N S) (outside N S) (CutEdge N S) where
  inside := insidePin N S
  outside := outsidePin N S

def verticesEquiv (S : Finset V) : InsideVertex S ⊕ OutsideVertex S ≃ V where
  toFun := Sum.elim Subtype.val Subtype.val
  invFun v := if hv : v ∈ S then Sum.inl ⟨v, hv⟩ else Sum.inr ⟨v, hv⟩
  left_inv v := by
    rcases v with v | v
    · simp [v.2]
    · simp [v.2]
  right_inv v := by by_cases hv : v ∈ S <;> simp [hv]

def edgesEquiv (N : Network V E) (S : Finset V) :
    (InsideEdge N S ⊕ CutEdge N S) ⊕ OutsideEdge N S ≃ E where
  toFun := Sum.elim (Sum.elim Subtype.val Subtype.val) Subtype.val
  invFun e :=
    if hs : N.src e ∈ S then
      if hd : N.dst e ∈ S then Sum.inl (Sum.inl ⟨e, hs, hd⟩)
      else Sum.inl (Sum.inr ⟨e, Or.inl ⟨hs, hd⟩⟩)
    else
      if hd : N.dst e ∈ S then Sum.inl (Sum.inr ⟨e, Or.inr ⟨hs, hd⟩⟩)
      else Sum.inr ⟨e, hs, hd⟩
  left_inv e := by
    rcases e with (e | e) | e
    · simp [e.2.1, e.2.2]
    · rcases e.2 with h | h <;> simp [h.1, h.2]
    · simp [e.2.1, e.2.2]
  right_inv e := by
    by_cases hs : N.src e ∈ S <;> by_cases hd : N.dst e ∈ S <;> simp [hs, hd]

/-- A bijection of ACTUAL physical graphs, not a contraction of their kernels. -/
def ownerReindex (N : Network V E) (S : Finset V) :
    Reindex (ported N S).owner N where
  vertices := verticesEquiv S
  edges := edgesEquiv N S
  endpoints := by
    intro e
    rcases e with (e | e) | e
    · exact Or.inl ⟨rfl, rfl⟩
    · by_cases hs : N.src e.1 ∈ S
      · left
        simp [Ported.owner, ported, insidePin, outsidePin,
          verticesEquiv, edgesEquiv, hs]
      · right
        simp [Ported.owner, ported, insidePin, outsidePin,
          verticesEquiv, edgesEquiv, hs]
    · exact Or.inl ⟨rfl, rfl⟩

/-- The local network really is the induced graph on the original shore. -/
theorem inside_graph_eq_induce (N : Network V E) (S : Finset V) :
    (inside N S).graph = N.graph.induce (↑S : Set V) := by
  ext u v
  constructor
  · rintro ⟨e, h | h⟩
    · exact ⟨e.1, Or.inl ⟨congrArg Subtype.val h.1, congrArg Subtype.val h.2⟩⟩
    · exact ⟨e.1, Or.inr ⟨congrArg Subtype.val h.1, congrArg Subtype.val h.2⟩⟩
  · rintro ⟨e, h | h⟩
    · refine ⟨⟨e, h.1.symm ▸ u.2, h.2.symm ▸ v.2⟩, Or.inl ?_⟩
      exact ⟨Subtype.ext h.1, Subtype.ext h.2⟩
    · refine ⟨⟨e, h.1.symm ▸ v.2, h.2.symm ▸ u.2⟩, Or.inr ?_⟩
      exact ⟨Subtype.ext h.1, Subtype.ext h.2⟩

/-- The exterior component count includes every original exterior vertex. -/
theorem outside_graph_eq_induce (N : Network V E) (S : Finset V) :
    (outside N S).graph = N.graph.induce {v | v ∉ S} := by
  ext u v
  constructor
  · rintro ⟨e, h | h⟩
    · exact ⟨e.1, Or.inl ⟨congrArg Subtype.val h.1, congrArg Subtype.val h.2⟩⟩
    · exact ⟨e.1, Or.inr ⟨congrArg Subtype.val h.1, congrArg Subtype.val h.2⟩⟩
  · rintro ⟨e, h | h⟩
    · refine ⟨⟨e, h.1.symm ▸ u.2, h.2.symm ▸ v.2⟩, Or.inl ?_⟩
      exact ⟨Subtype.ext h.1, Subtype.ext h.2⟩
    · refine ⟨⟨e, h.1.symm ▸ v.2, h.2.symm ▸ u.2⟩, Or.inr ?_⟩
      exact ⟨Subtype.ext h.1, Subtype.ext h.2⟩

def restrictInside (N : Network V E) (S : Finset V)
    (x : N.Word) : (inside N S).Word := fun e => x e.1

/-- The actual owner law, uniform on its full cycle space. -/
def originalFraction (N : Network V E) (S : Finset V)
    (Good : (inside N S).Word → Prop) : ℝ :=
  Finite.density (fun x : N.CycleSpace => Good (restrictInside N S x.1))

/-- The complete ONE-APEX boundary law, not a chosen boundary syndrome. -/
def boundaryAverage (N : Network V E) (S : Finset V)
    (Good : (inside N S).Word → Prop) : ℝ :=
  letI : Fintype (InsideVertex S) := insideVertexFintype N S
  letI : Fintype (OutsideVertex S) := outsideVertexFintype N S
  letI : Fintype (InsideEdge N S) := insideEdgeFintype N S
  letI : Fintype (OutsideEdge N S) := outsideEdgeFintype N S
  letI : Fintype (CutEdge N S) := cutEdgeFintype N S
  (ported N S).apexFraction Good

/-- The one-apex law is unchanged when its physical cut-edge pins are bijectively
relabelled. This bridge is stated beside `boundaryAverage` so both sides use
the same hidden finite instances. -/
theorem boundaryAverage_relabelPins {Q : Type*} [Fintype Q]
    (N : Network V E) (S : Finset V) (e : CutEdge N S ≃ Q)
    (Good : (inside N S).Word → Prop) :
    boundaryAverage N S Good = ((ported N S).relabelPins e).apexFraction Good := by
  unfold boundaryAverage
  exact ((ported N S).apexFraction_relabelPins e Good).symm



def exteriorComponentCount (N : Network V E) (S : Finset V) : ℕ :=
  Fintype.card (outside N S).Component

theorem originalFraction_eq_ported (N : Network V E) (S : Finset V)
    (Good : (inside N S).Word → Prop) :
    originalFraction N S Good = (ported N S).ownerFraction Good := by
  unfold originalFraction Ported.ownerFraction
  symm
  apply Finite.density_equiv (ownerReindex N S).cycleEquiv
  intro w
  have hx : restrictInside N S ((ownerReindex N S).cycleEquiv w).1 =
      ((ported N S).ownerWordEquiv w.1).1.1 := by
    funext e
    exact (ownerReindex N S).wordEquiv_apply_edge w.1 (Sum.inl (Sum.inl e))
  rw [hx]



/-- **Original-exterior trace bound**, with no untranslated probabilistic or
graph-lifting hypothesis. The outside vertex ensures that c >= 1. -/
theorem original_exterior_trace_bound (N : Network V E) (S : Finset V)
    (v₀ : OutsideVertex S) (Good : (inside N S).Word → Prop) :
    originalFraction N S Good ≤
      (2 : ℝ) ^ (exteriorComponentCount N S - 1) * boundaryAverage N S Good := by
  rw [originalFraction_eq_ported]
  exact (ported N S).ownerFraction_le_apexFraction
    ((outside N S).component v₀) Good

/-- Forest specialization of the actual original-exterior bound. -/
theorem original_forest_fraction_le (N : Network V E) (S : Finset V)
    (v₀ : OutsideVertex S) :
    originalFraction N S (inside N S).IsForest ≤
      (2 : ℝ) ^ (exteriorComponentCount N S - 1) *
        boundaryAverage N S (inside N S).IsForest :=
  original_exterior_trace_bound N S v₀ (inside N S).IsForest



end Shore
end Network
end Erdos1016.BoundaryTrace
