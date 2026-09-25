import Erdos1016.Boundary.NetworkRealization
import Erdos1016.Cycles.Selection.ConflictThinning

set_option autoImplicit false

/-!
# The finite moment bounds apply to the literal boundary average

A fresh vertex is joined once to EVERY degree-two vertex of the original
min-2/max-3 core. All old edges are retained. No nonbacktracking estimate is
applied to the resulting high-degree apex graph.

The original boundary-average law equals forest restriction in this actual
simple physical graph. This is the measure adapter needed to use the finite
MANY/FEW moment theorems, not an assumed change of probability space.
-/

noncomputable section
open scoped BigOperators
namespace Erdos1016.BoundaryDecay

open BoundaryTrace
local instance apexAverageDecidable (p : Prop) : Decidable p := Classical.propDecidable p

abbrev CorePin (H : PhysicalGraph) := {v : H.Vertex // H.degree v = 2}

def trivialOutside : Network Unit Empty where
  src e := nomatch e
  dst e := nomatch e
  noLoops e := nomatch e

def corePorts (H : PhysicalGraph) : Ported H.traceNetwork trivialOutside (CorePin H) where
  inside := Subtype.val
  outside _ := ()

abbrev coreApexNetwork (H : PhysicalGraph) := (corePorts H).apex

def coreOrdinary (H : PhysicalGraph) : Finset (H.Vertex ⊕ Unit) :=
  Finset.univ.image (Sum.inl : H.Vertex → H.Vertex ⊕ Unit)

@[simp] theorem mem_coreOrdinary_inl (H : PhysicalGraph) (v : H.Vertex) :
    Sum.inl v ∈ coreOrdinary H := by simp [coreOrdinary]

@[simp] theorem not_mem_coreOrdinary_apex (H : PhysicalGraph) :
    Sum.inr () ∉ coreOrdinary H := by simp [coreOrdinary]

theorem coreApex_simple (H : PhysicalGraph) : SimpleNetwork (coreApexNetwork H) := by
  intro e f h
  rcases e with e | e <;> rcases f with f | f
  · apply congrArg (Sum.inl : H.Edge → H.Edge ⊕ CorePin H)
    apply H.simple
    rcases h with h | h
    · exact Or.inl ⟨Sum.inl.inj h.1, Sum.inl.inj h.2⟩
    · exact Or.inr ⟨Sum.inl.inj h.1, Sum.inl.inj h.2⟩
  · rcases h with h | h
    · cases h.2
    · cases h.1
  · rcases h with h | h
    · cases h.2
    · cases h.2
  · apply congrArg (Sum.inr : CorePin H → H.Edge ⊕ CorePin H)
    apply Subtype.ext
    rcases h with h | h
    · exact Sum.inl.inj h.1
    · cases h.1

def coreApexGraph (H : PhysicalGraph) : PhysicalGraph :=
  physicalize (coreApexNetwork H) (coreApex_simple H)

def coreApexInterior (H : PhysicalGraph) : Finset (coreApexGraph H).Vertex :=
  physicalShore (coreApexNetwork H) (coreApex_simple H) (coreOrdinary H)

def coreApexVertex (H : PhysicalGraph) : (coreApexGraph H).Vertex :=
  Fintype.equivFin (H.Vertex ⊕ Unit) (Sum.inr ())



/-- An actual graph map, preserving every internal physical edge. -/
def coreIntoApex (H : PhysicalGraph) : H.traceNetwork.graph →g (coreApexNetwork H).graph where
  toFun := Sum.inl
  map_rel' := by
    intro u v huv
    rcases huv with ⟨e, h | h⟩
    · exact ⟨Sum.inl e, Or.inl ⟨congrArg Sum.inl h.1, congrArg Sum.inl h.2⟩⟩
    · exact ⟨Sum.inl e, Or.inr ⟨congrArg Sum.inl h.1, congrArg Sum.inl h.2⟩⟩

theorem coreApex_connected (H : PhysicalGraph) (hH : H.IsConnected) (p₀ : CorePin H) :
    (coreApexGraph H).IsConnected := by
  have hn : H.traceNetwork.graph.Connected := by
    simpa only [H.traceNetwork_graph] using hH
  have ha : (coreApexNetwork H).graph.Connected := by
    rw [SimpleGraph.connected_iff_exists_forall_reachable]
    refine ⟨Sum.inr (), ?_⟩
    intro v
    rcases v with v | v
    · have he : (coreApexNetwork H).graph.Adj (Sum.inr ()) (Sum.inl p₀.1) :=
        ⟨Sum.inr p₀, Or.inr ⟨rfl, rfl⟩⟩
      exact he.reachable.trans ((hn p₀.1 v).map (coreIntoApex H))
    · cases v
      exact .refl _
  have hp := (physicalReindex (coreApexNetwork H) (coreApex_simple H)).connected_iff.1 ha
  simpa only [PhysicalGraph.traceNetwork_graph] using hp

theorem coreApex_degree_inside (H : PhysicalGraph) (v : H.Vertex) :
    (coreApexGraph H).degree (Fintype.equivFin (H.Vertex ⊕ Unit) (Sum.inl v)) =
      H.degree v + if H.degree v = 2 then 1 else 0 := by
  have hpin : (∑ p : CorePin H, if p.1 = v then (1 : ℕ) else 0) =
      if H.degree v = 2 then 1 else 0 := by
    by_cases hv : H.degree v = 2
    · let p₀ : CorePin H := ⟨v, hv⟩
      have heq (p : CorePin H) : p.1 = v ↔ p = p₀ := by
        constructor
        · intro h
          apply Subtype.ext
          exact h
        · intro h
          subst p
          rfl
      simp [hv, heq]
    · have hne (p : CorePin H) : p.1 ≠ v := by
        intro h
        exact hv (h ▸ p.2)
      simp [hv, hne]
  change (physicalize (coreApexNetwork H) (coreApex_simple H)).degree
      (Fintype.equivFin (H.Vertex ⊕ Unit) (Sum.inl v)) = _
  rw [physical_degree_eq (coreApexNetwork H) (coreApex_simple H) (Sum.inl v)]
  calc
    networkDegree (coreApexNetwork H) (Sum.inl v) =
        networkDegree H.traceNetwork v +
          ∑ p : CorePin H, if p.1 = v then 1 else 0 := by
      simp only [networkDegree, coreApexNetwork, corePorts, Ported.apex,
        Finset.card_filter, Finset.sum_filter, Fintype.sum_sum_type]
      simp [Sum.elim, Function.comp_apply]
      rw [Finset.card_filter]
      apply Fintype.sum_congr
      intro e
      by_cases he : H.traceNetwork.src e = v ∨ H.traceNetwork.dst e = v
      · simp [he]
      · simp [he]
    _ = H.degree v + if H.degree v = 2 then 1 else 0 := by
      rw [hpin]
      have hdeg : networkDegree H.traceNetwork v = H.degree v := by
        unfold networkDegree PhysicalGraph.degree PhysicalGraph.selectedDegree
        apply congrArg Finset.card
        congr 1
        ext e
        simp [PhysicalGraph.traceNetwork, PhysicalGraph.incident]
      rw [hdeg]

theorem coreApex_ordinary_cubic (H : PhysicalGraph)
    (hmin : ∀ v, 2 ≤ H.degree v) (hmax : ∀ v, H.degree v ≤ 3) :
    ∀ v ∈ coreApexInterior H, (coreApexGraph H).degree v = 3 := by
  intro v hv
  obtain ⟨w, hw, rfl⟩ := Finset.mem_image.1 hv
  obtain ⟨u, _, rfl⟩ := Finset.mem_image.1 hw
  rw [coreApex_degree_inside]
  have hlo := hmin u
  have hhi := hmax u
  split_ifs <;> omega

def ordinaryVertexEquiv (H : PhysicalGraph) :
    H.Vertex ≃ {v : H.Vertex ⊕ Unit // v ∈ coreOrdinary H} where
  toFun v := ⟨Sum.inl v, mem_coreOrdinary_inl H v⟩
  invFun v := match v with
    | ⟨Sum.inl u, _⟩ => u
    | ⟨Sum.inr u, h⟩ => False.elim (by cases u; exact not_mem_coreOrdinary_apex H h)
  left_inv _ := rfl
  right_inv v := by
    rcases v with ⟨v | v, hv⟩
    · rfl
    · cases v
      exact False.elim (not_mem_coreOrdinary_apex H hv)

/-- Delete only the new apex from a selected word: the remaining selected
graph is exactly the original inner edge word, including all old isolates. -/
def ordinarySelectedIso (H : PhysicalGraph) (x : (coreApexNetwork H).Word) :
    (H.traceNetwork.selectedGraph (fun e => x (Sum.inl e))) ≃g
      ((coreApexNetwork H).selectedGraph x).induce
        (↑(coreOrdinary H) : Set (H.Vertex ⊕ Unit)) where
  toEquiv := ordinaryVertexEquiv H
  map_rel_iff' := by
    intro u v
    constructor
    · rintro ⟨e | p, hx, h | h⟩
      · exact ⟨e, hx, Or.inl ⟨Sum.inl.inj h.1, Sum.inl.inj h.2⟩⟩
      · exact ⟨e, hx, Or.inr ⟨Sum.inl.inj h.1, Sum.inl.inj h.2⟩⟩
      · cases h.2
      · cases h.2
    · rintro ⟨e, hx, h | h⟩
      · exact ⟨Sum.inl e, hx, Or.inl ⟨congrArg Sum.inl h.1, congrArg Sum.inl h.2⟩⟩
      · exact ⟨Sum.inl e, hx, Or.inr ⟨congrArg Sum.inl h.1, congrArg Sum.inl h.2⟩⟩

/-- Definition on the exact full apex cycle space. The subsequent theorem
identifies it with the complete sector average of manuscript (2.1). -/
def coreBoundaryAverage (H : PhysicalGraph) : ℝ :=
  (corePorts H).apexFraction H.traceNetwork.IsForest

theorem coreBoundaryAverage_eq_physical_fraction (H : PhysicalGraph) :
    coreBoundaryAverage H =
      (coreApexGraph H).originalForestFraction (coreApexInterior H) := by
  change coreBoundaryAverage H =
    (physicalize (coreApexNetwork H) (coreApex_simple H)).originalForestFraction
      (physicalShore (coreApexNetwork H) (coreApex_simple H) (coreOrdinary H))
  rw [physical_forest_fraction_eq (coreApexNetwork H) (coreApex_simple H)
    (coreOrdinary H)]
  unfold coreBoundaryAverage Ported.apexFraction
  have heq : (fun x : (coreApexNetwork H).CycleSpace =>
      H.traceNetwork.IsForest ((corePorts H).apexWordEquiv x.1).1) =
      (fun x : (coreApexNetwork H).CycleSpace =>
        (((coreApexNetwork H).selectedGraph x.1).induce
          (↑(coreOrdinary H) : Set (H.Vertex ⊕ Unit))).IsAcyclic) := by
    funext x
    exact propext (acyclic_iff_of_iso (ordinarySelectedIso H x.1))
  rw [heq]







end Erdos1016.BoundaryDecay
