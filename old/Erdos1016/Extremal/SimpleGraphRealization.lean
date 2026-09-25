import Erdos1016.Graph.PancyclicRank
import Erdos1016.Extremal.Statement

set_option autoImplicit false

/-!
# Finite SimpleGraph to physical-edge bridge

This module gives every community-standard graph on `Fin n` an edge-labelled
`PhysicalGraph` with the same underlying simple graph. It also proves the exact
connected Euler rank formula needed to compare the two edge-excess conventions.
The separate translation from a Mathlib cycle walk to a nonzero kernel word is
not part of this adapter yet.
-/

noncomputable section
namespace Erdos1016.Problem1016

open Erdos1016

local instance simpleGraphEdgeFintype {n : ℕ} (G : SimpleGraph (Fin n)) :
    Fintype G.edgeSet := Fintype.ofFinite _

private def edgeIndexEquiv {n : ℕ} (G : SimpleGraph (Fin n)) :
    Fin (Fintype.card G.edgeSet) ≃ G.edgeSet :=
  (Fintype.equivFin G.edgeSet).symm

/-- Enumerate the unordered edges of a finite simple graph as physical labels.
The endpoint order comes from `Sym2.out`; neither loops nor repeated physical
edges are introduced. -/
def physicalOfSimpleGraph {n : ℕ} (G : SimpleGraph (Fin n)) : PhysicalGraph where
  vertexCount := n
  edgeCount := Fintype.card G.edgeSet
  src e := (edgeIndexEquiv G e).val.out.1
  dst e := (edgeIndexEquiv G e).val.out.2
  noLoops e := by
    intro h
    have hd : Sym2.IsDiag ((edgeIndexEquiv G e).val) := by
      have hm : Sym2.IsDiag (Sym2.mk ((edgeIndexEquiv G e).val.out)) :=
        (Sym2.isDiag_iff_proj_eq _).2 h
      exact (edgeIndexEquiv G e).val.out_eq ▸ hm
    exact G.not_isDiag_of_mem_edgeSet (edgeIndexEquiv G e).property hd
  simple e f h := by
    apply (edgeIndexEquiv G).injective
    apply Subtype.ext
    rw [← (edgeIndexEquiv G e).val.out_eq,
        ← (edgeIndexEquiv G f).val.out_eq]
    rcases h with h | h
    · exact Sym2.mk_eq_mk_iff.mpr (Or.inl (Prod.ext h.1 h.2))
    · exact Sym2.mk_eq_mk_iff.mpr (Or.inr (Prod.ext h.1 h.2))

@[simp] theorem physicalOfSimpleGraph_vertexCount {n : ℕ}
    (G : SimpleGraph (Fin n)) : (physicalOfSimpleGraph G).vertexCount = n := rfl

@[simp] theorem physicalOfSimpleGraph_edgeCount {n : ℕ}
    (G : SimpleGraph (Fin n)) :
    (physicalOfSimpleGraph G).edgeCount = Fintype.card G.edgeSet := rfl

theorem physicalOfSimpleGraph_toSimpleGraph {n : ℕ}
    (G : SimpleGraph (Fin n)) :
    (physicalOfSimpleGraph G).toSimpleGraph = G := by
  classical
  ext u v
  constructor
  · rintro ⟨e, _, h | h⟩
    · let a := edgeIndexEquiv G e
      have hadj : G.Adj a.val.out.1 a.val.out.2 := by
        have he : Sym2.mk a.val.out ∈ G.edgeSet := by
          simpa only [a.val.out_eq] using a.property
        exact G.mem_edgeSet.mp he
      change (edgeIndexEquiv G e).val.out.1 = u ∧
        (edgeIndexEquiv G e).val.out.2 = v at h
      rw [h.1, h.2] at hadj
      exact hadj
    · let a := edgeIndexEquiv G e
      have hadj : G.Adj a.val.out.1 a.val.out.2 := by
        have he : Sym2.mk a.val.out ∈ G.edgeSet := by
          simpa only [a.val.out_eq] using a.property
        exact G.mem_edgeSet.mp he
      change (edgeIndexEquiv G e).val.out.1 = v ∧
        (edgeIndexEquiv G e).val.out.2 = u at h
      rw [h.1, h.2] at hadj
      exact G.symm hadj
  · intro huv
    let a : G.edgeSet := ⟨Sym2.mk (u, v), G.mem_edgeSet.mpr huv⟩
    let e := (edgeIndexEquiv G).symm a
    have hout : a.val.out.1 = u ∧ a.val.out.2 = v ∨
        a.val.out.1 = v ∧ a.val.out.2 = u := by
      have houtEq : Sym2.mk a.val.out = Sym2.mk (u, v) := by
        calc
          Sym2.mk a.val.out = a.val := a.val.out_eq
          _ = Sym2.mk (u, v) := rfl
      rcases Sym2.mk_eq_mk_iff.mp houtEq with hp | hp
      · exact Or.inl ⟨congrArg Prod.fst hp, congrArg Prod.snd hp⟩
      · exact Or.inr ⟨congrArg Prod.fst hp, congrArg Prod.snd hp⟩
    refine ⟨e, one_ne_zero, ?_⟩
    change ((edgeIndexEquiv G e).val.out.1 = u ∧
      (edgeIndexEquiv G e).val.out.2 = v) ∨
      ((edgeIndexEquiv G e).val.out.1 = v ∧
      (edgeIndexEquiv G e).val.out.2 = u)
    have he : edgeIndexEquiv G e = a := by simp [e]
    rw [he]
    rcases hout with ⟨hu, hv⟩ | ⟨hv, hu⟩
    · exact Or.inl ⟨hu, hv⟩
    · exact Or.inr ⟨hv, hu⟩

theorem physicalOfSimpleGraph_connected {n : ℕ} (G : SimpleGraph (Fin n))
    (hG : G.Connected) : (physicalOfSimpleGraph G).IsConnected := by
  change (physicalOfSimpleGraph G).toSimpleGraph.Connected
  rw [physicalOfSimpleGraph_toSimpleGraph]
  exact hG

/-- Connected cycle rank is precisely the community edge excess plus one. -/
theorem physicalOfSimpleGraph_rank_eq_excess_add_one {n : ℕ}
    (G : SimpleGraph (Fin n)) (hG : G.Connected)
    (hn : 3 ≤ n) (hPan : IsPancyclic G) :
    (physicalOfSimpleGraph G).cycleRank = excess n G + 1 := by
  have hEuler := Extremal.connected_rank_euler (physicalOfSimpleGraph G)
    (physicalOfSimpleGraph_connected G hG)
  have hcycle : HasCycleLength G n := by
    apply hPan n
    · exact hn
    · simp
  obtain ⟨v, p, hp, hlen⟩ := hcycle
  have hnEdges : n ≤ Fintype.card G.edgeSet := by
    have h := hp.isTrail.length_le_card_edgeFinset
    simpa [hlen] using h
  have hEuler' : (physicalOfSimpleGraph G).cycleRank + n =
      Fintype.card G.edgeSet + 1 := by
    simpa [physicalOfSimpleGraph] using hEuler
  unfold excess
  change (physicalOfSimpleGraph G).cycleRank = Fintype.card G.edgeSet - n + 1
  omega

end Erdos1016.Problem1016
