import Erdos1016.Graph.Multigraph.EvenForest
import Erdos1016.Graph.Multigraph.BoundaryImage

set_option autoImplicit false

/-! Labelled foresthood is equivalent to absence of a supported nonzero even word. -/

noncomputable section
open scoped BigOperators
namespace Erdos1016.FiniteMultiGraph
open BoundaryTrace BoundaryDecay

local instance forestCriterionDecidable (p : Prop) : Decidable p := Classical.propDecidable p

/-- A selected loop, parallel pair, or ordinary simple cycle supplies a
nonzero even word on selected labels. All three cases are necessary. -/
theorem exists_even_support_of_not_forest (G : FiniteMultiGraph) (x : G.EdgeWord)
    (hf : ¬ G.IsForestWord x) :
    ∃ seed : G.CycleSpace, seed.1 ≠ 0 ∧ ∀ e, seed.1 e ≠ 0 → x e ≠ 0 := by
  classical
  by_cases hl : ∀ e, x e ≠ 0 → G.src e ≠ G.dst e
  · by_cases hp : ∀ e f, x e ≠ 0 → x f ≠ 0 →
        ((G.src e = G.src f ∧ G.dst e = G.dst f) ∨
          (G.src e = G.dst f ∧ G.dst e = G.src f)) → e = f
    · let E := {e : G.Edge // x e ≠ 0}
      let N : Network G.Vertex E := {
        src := fun e => G.src e.1
        dst := fun e => G.dst e.1
        noLoops := fun e => hl e.1 e.2 }
      have hs : SimpleNetwork N := by
        intro e f h
        exact Subtype.ext (hp e.1 f.1 e.2 f.2 h)
      have hg : N.graph = G.selectedGraph x := by
        ext u v
        constructor
        · rintro ⟨e, h | h⟩
          · exact ⟨by intro huv; exact N.noLoops e (h.1.trans (huv.trans h.2.symm)),
              e.1, e.2, Or.inl h⟩
          · exact ⟨by intro huv; exact N.noLoops e (h.1.trans (huv.symm.trans h.2.symm)),
              e.1, e.2, Or.inr h⟩
        · rintro ⟨_, e, he, h⟩
          exact ⟨⟨e, he⟩, h⟩
      let H := physicalize N hs
      let iso : N.graph ≃g H.toSimpleGraph := {
        toEquiv := (physicalReindex N hs).vertices
        map_rel_iff' := by
          intro u v
          simpa only [PhysicalGraph.traceNetwork_graph] using
            (physicalReindex N hs).graph_adj_iff u v }
      have hH : ¬ H.toSimpleGraph.IsAcyclic := by
        intro h
        apply hf
        refine ⟨hl, hp, ?_⟩
        rw [← hg]
        exact (acyclic_iff_of_iso iso).mpr h
      obtain ⟨v, p, hpc⟩ : ∃ v, ∃ p : H.toSimpleGraph.Walk v v, p.IsCycle := by
        by_contra h
        push_neg at h
        exact hH h
      let z := Nonbacktracking.walkWord H p
      have hz := Nonbacktracking.walkWord_isCycleWord H p hpc
      let y : N.CycleSpace := (physicalCycleEquiv N hs).symm ⟨z, hz.2.1⟩
      have hy : y.1 ≠ 0 := by
        intro hzero
        apply hz.1
        funext e
        have he := congrFun hzero ((physicalReindex N hs).edges.symm e)
        simpa [y, physicalCycleEquiv, PhysicalGraph.traceCycleEquiv,
          Network.Reindex.cycleEquiv, Network.Reindex.wordEquiv] using he
      let w : G.EdgeWord := fun e => if he : x e ≠ 0 then y.1 ⟨e, he⟩ else 0
      have hb : G.boundary w = 0 := by
        funext u
        let f : G.Edge → F₂ := fun e =>
          (if G.src e = u then w e else 0) + (if G.dst e = u then w e else 0)
        have hzero : (∑ e : {e : G.Edge // ¬ x e ≠ 0}, f e.1) = 0 := by
          apply Finset.sum_eq_zero
          intro e he
          have hxzero : x e.1 = 0 := not_ne_iff.mp e.2
          simp [f, w, hxzero]
        have hsum := Fintype.sum_subtype_add_sum_subtype (fun e : G.Edge => x e ≠ 0) f
        rw [hzero, add_zero] at hsum
        calc
          _ = ∑ e : E, f e.1 := hsum.symm
          _ = N.boundary y.1 u := by
            rw [Network.boundary_apply, ← Finset.sum_add_distrib]
            apply Finset.sum_congr rfl
            intro e he
            by_cases hsrc : G.src e.1 = u <;> by_cases hdst : G.dst e.1 = u <;>
              simp [N, f, w, e.2, hsrc, hdst]
          _ = 0 := congrFun y.2 u
      refine ⟨⟨w, hb⟩, ?_, ?_⟩
      · intro hw
        apply hy
        funext e
        have he := congrFun hw e.1
        simpa [w, e.2] using he
      · intro e he
        by_contra hxe
        simpa [w, hxe] using he
    · push_neg at hp
      obtain ⟨e, f, he, hf', hends, hne⟩ := hp
      let w : G.EdgeWord := Pi.single e 1 + Pi.single f 1
      have hb : G.boundary w = 0 := by
        rw [map_add, G.boundary_singleEdge, G.boundary_singleEdge]
        rcases hends with h | h
        · rw [h.1, h.2]
          exact word_add_self _
        · rw [h.1, h.2]
          rw [add_comm (G.vertexUnit (G.dst f)) (G.vertexUnit (G.src f))]
          exact word_add_self _
      refine ⟨⟨w, hb⟩, ?_, ?_⟩
      · intro hw
        have hh := congrFun hw e
        simpa [w, Pi.single_apply, hne] using hh
      · intro q hq
        by_cases hqe : q = e
        · simpa [hqe] using he
        · by_cases hqf : q = f
          · simpa [hqf] using hf'
          · simp [w, Pi.single_apply, hqe, hqf] at hq
  · push_neg at hl
    obtain ⟨e, he, hloop⟩ := hl
    have hb : G.boundary (Pi.single e 1) = 0 := by
      rw [G.boundary_singleEdge, hloop, G.vertexUnit_add_self]
    refine ⟨⟨Pi.single e 1, hb⟩, ?_, ?_⟩
    · intro hw
      have hh := congrFun hw e
      simpa using hh
    · intro q hq
      by_cases hqe : q = e
      · simpa [hqe] using he
      · simp [Pi.single_apply, hqe] at hq

/-- Algebraic characterization, useful when transporting forest events along
cycle-space maps without enumerating graph cycles. -/
theorem isForestWord_iff_no_even_support (G : FiniteMultiGraph) (x : G.EdgeWord) :
    G.IsForestWord x ↔ ∀ seed : G.CycleSpace,
      (∀ e, seed.1 e ≠ 0 → x e ≠ 0) → seed.1 = 0 := by
  constructor
  · intro hf seed hsub
    exact G.word_eq_zero_of_boundary_zero_of_forest _ seed.2 (hf.mono hsub)
  · intro h
    by_contra hf
    obtain ⟨seed, hn, hs⟩ := G.exists_even_support_of_not_forest x hf
    exact hn (h seed hs)

end Erdos1016.FiniteMultiGraph
