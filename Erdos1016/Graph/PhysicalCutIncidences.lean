import Erdos1016.Graph.CutPacking
import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Data.Fintype.Card

set_option autoImplicit false
noncomputable section
open scoped BigOperators
namespace Erdos1016.PhysicalGraph
local instance physicalCutIncidencesDecidable (p : Prop) : Decidable p := Classical.propDecidable p

/-- Each simple-graph boundary incidence has its own physical cut label.
This form needs only an injection and is convenient for path-length bounds. -/
theorem boundary_incidences_le_cut (H : PhysicalGraph) (A : Finset H.Vertex) :
    (∑ v ∈ A, (H.toSimpleGraph.neighborFinset v \ A).card) ≤ (H.cutEdges A).card := by
  let I := (v : A) × {w : H.Vertex // w ∈ H.toSimpleGraph.neighborFinset v.1 \ A}
  have hex (p : I) : ∃ e : H.Edge,
      (H.src e = p.1.1 ∧ H.dst e = p.2.1) ∨ (H.src e = p.2.1 ∧ H.dst e = p.1.1) := by
    have ha := (SimpleGraph.mem_neighborFinset _ _ _).mp (Finset.mem_sdiff.mp p.2.2).1
    obtain ⟨e, _, h⟩ := ha
    exact ⟨e, h⟩
  let pick : I → H.Edge := fun p => Classical.choose (hex p)
  have hpick (p : I) :
      (H.src (pick p) = p.1.1 ∧ H.dst (pick p) = p.2.1) ∨
        (H.src (pick p) = p.2.1 ∧ H.dst (pick p) = p.1.1) := Classical.choose_spec (hex p)
  have hcut (p : I) : pick p ∈ H.cutEdges A := by
    have hin := p.1.2
    have hout := (Finset.mem_sdiff.mp p.2.2).2
    rcases hpick p with h | h <;> simp [cutEdges, h.1, h.2, hin, hout]
  let f : I → H.cutEdges A := fun p => ⟨pick p, hcut p⟩
  have hinj : Function.Injective f := by
    intro p q hpq
    have he : pick p = pick q := congrArg Subtype.val hpq
    have hp := hpick p
    rw [he] at hp
    have hq := hpick q
    have hpn := (Finset.mem_sdiff.mp p.2.2).2
    have hqn := (Finset.mem_sdiff.mp q.2.2).2
    rcases hp with hp | hp <;> rcases hq with hq | hq
    · exact Sigma.subtype_ext (Subtype.ext (hp.1.symm.trans hq.1)) (hp.2.symm.trans hq.2)
    · exact (hqn (hp.1.symm.trans hq.1 ▸ p.1.2)).elim
    · exact (hpn (hp.1.symm.trans hq.1 ▸ q.1.2)).elim
    · exact Sigma.subtype_ext (Subtype.ext (hp.2.symm.trans hq.2)) (hp.1.symm.trans hq.1)
  have hc := Fintype.card_le_of_injective f hinj
  simp only [I, Fintype.card_sigma, Fintype.card_coe] at hc
  rw [Finset.sum_coe_sort A (fun v => (H.toSimpleGraph.neighborFinset v \ A).card)] at hc
  exact hc

end Erdos1016.PhysicalGraph
