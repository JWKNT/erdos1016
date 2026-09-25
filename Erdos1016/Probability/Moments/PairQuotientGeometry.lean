import Erdos1016.Probability.Moments.SeedPairCorrelation
import Erdos1016.Graph.ExteriorComponents

set_option autoImplicit false
set_option maxHeartbeats 1500000

/-! The exterior of two contracted regions is the original induced exterior. -/

noncomputable section
namespace Erdos1016.FiniteMultiGraph.SeedPairCorrelation

open ConnectedContraction ExceptionalPartners
local instance pairGeometryDecidable (p : Prop) : Decidable p := Classical.propDecidable p

variable (G : FiniteMultiGraph) (U V : Finset G.Vertex)

lemma pair_regions_disjoint (hUV : Disjoint U V) :
    Pairwise (fun i j => Disjoint (regions G U V i) (regions G U V j)) := by
  intro i j hij
  cases i <;> cases j
  · exact (hij rfl).elim
  · exact hUV
  · exact hUV.symm
  · exact (hij rfl).elim

abbrev ExteriorVertex := {v : G.Vertex // v ∈ (U ∪ V)ᶜ}
abbrev DoubleDeletedVertex := DeletedVertex (secondVertex G U V)
abbrev doubleDeletedGraph := deleted (deleted (pairQuotient G U V).toSimpleGraph
  (firstVertex G U V)) (secondVertex G U V)

def outsideLabel (v : ExteriorVertex G U V) : DisjointRegionCuts.OutsideVertex G (regions G U V) :=
  ⟨v.1, by
    have hv : v.1 ∉ U ∧ v.1 ∉ V := by simpa using v.2
    intro i
    cases i
    · exact hv.1
    · exact hv.2⟩

def exteriorVertex (v : ExteriorVertex G U V) : DoubleDeletedVertex G U V :=
  ⟨⟨vertexEquiv (Sum.inr (outsideLabel G U V v) : PairLabel G U V), by
    intro h
    have h' := vertexEquiv.injective h
    exact Sum.noConfusion h'⟩, by
      intro h
      have h' := vertexEquiv.injective (congrArg Subtype.val h)
      exact Sum.noConfusion h'⟩

lemma exteriorVertex_injective : Function.Injective (exteriorVertex G U V) := by
  intro a b h
  have h' := vertexEquiv.injective (congrArg (fun v => v.1.1) h)
  have hv : outsideLabel G U V a = outsideLabel G U V b := Sum.inr.inj h'
  exact Subtype.ext (congrArg (fun z : DisjointRegionCuts.OutsideVertex G (regions G U V) => z.1) hv)

lemma exteriorVertex_surjective : Function.Surjective (exteriorVertex G U V) := by
  intro q
  let ve : PairLabel G U V ≃ (pairQuotient G U V).Vertex := vertexEquiv
  have hv := ve.apply_symm_apply q.1.1
  cases hl : ve.symm q.1.1 with
  | inl b =>
      rw [hl] at hv
      cases b
      · exact (q.1.2 hv.symm).elim
      · exact (q.2 (Subtype.ext hv.symm)).elim
  | inr v =>
      have hv' : v.1 ∈ (U ∪ V)ᶜ := by
        simp only [Finset.mem_compl, Finset.mem_union, not_or]
        exact ⟨v.2 false, v.2 true⟩
      refine ⟨⟨v.1, hv'⟩, ?_⟩
      apply Subtype.ext
      apply Subtype.ext
      rw [hl] at hv
      exact hv

def exteriorVertexEquiv : ExteriorVertex G U V ≃ DoubleDeletedVertex G U V :=
  Equiv.ofBijective (exteriorVertex G U V)
    ⟨exteriorVertex_injective G U V, exteriorVertex_surjective G U V⟩

lemma quotient_adj_iff (a b : PairLabel G U V) :
    (pairQuotient G U V).toSimpleGraph.Adj (vertexEquiv a) (vertexEquiv b) ↔
      a ≠ b ∧ ∃ e : G.Edge,
        (pairLabel G U V (G.src e) = a ∧ pairLabel G U V (G.dst e) = b) ∨
        (pairLabel G U V (G.src e) = b ∧ pairLabel G U V (G.dst e) = a) := by
  constructor
  · rintro ⟨hab, e, he⟩
    refine ⟨fun h => hab (congrArg vertexEquiv h), ((edgeEquiv G (pairLabel G U V)).symm e).1, ?_⟩
    rcases he with h | h
    · exact Or.inl ⟨vertexEquiv.injective h.1, vertexEquiv.injective h.2⟩
    · exact Or.inr ⟨vertexEquiv.injective h.1, vertexEquiv.injective h.2⟩
  · rintro ⟨hab, e, he⟩
    have hc : pairLabel G U V (G.src e) ≠ pairLabel G U V (G.dst e) := by
      rcases he with h | h
      · exact h.1 ▸ h.2 ▸ hab
      · exact h.1 ▸ h.2 ▸ hab.symm
    refine ⟨fun h => hab (vertexEquiv.injective h), edgeEquiv G (pairLabel G U V) ⟨e, hc⟩, ?_⟩
    simpa only [quotient, Equiv.symm_apply_apply, Equiv.apply_eq_iff_eq] using he

def exteriorGraphIso : ExteriorComponents.graph G (U ∪ V)ᶜ ≃g doubleDeletedGraph G U V where
  toEquiv := exteriorVertexEquiv G U V
  map_rel_iff' := by
    intro a b
    change (pairQuotient G U V).toSimpleGraph.Adj
      (vertexEquiv (Sum.inr (outsideLabel G U V a) : PairLabel G U V))
      (vertexEquiv (Sum.inr (outsideLabel G U V b) : PairLabel G U V)) ↔ G.toSimpleGraph.Adj a.1 b.1
    rw [quotient_adj_iff]
    simp only [ne_eq, Sum.inr.injEq, DisjointRegionCuts.label_eq_inr_iff]
    have hne : outsideLabel G U V a ≠ outsideLabel G U V b ↔ a.1 ≠ b.1 :=
      not_congr Subtype.ext_iff
    exact and_congr hne Iff.rfl

/-- Adjacency to a contracted region is exactly an original edge into it. -/
lemma adj_region_exterior_iff (hUV : Disjoint U V) (i : Bool) (v : ExteriorVertex G U V) :
    (pairQuotient G U V).toSimpleGraph.Adj
      (vertexEquiv (Sum.inl i : PairLabel G U V)) (exteriorVertex G U V v).1.1 ↔
      ∃ u ∈ regions G U V i, G.toSimpleGraph.Adj u v.1 := by
  change (pairQuotient G U V).toSimpleGraph.Adj
      (vertexEquiv (Sum.inl i : PairLabel G U V))
      (vertexEquiv (Sum.inr (outsideLabel G U V v) : PairLabel G U V)) ↔ _
  rw [quotient_adj_iff]
  simp only [ne_eq, reduceCtorEq, not_false_eq_true, true_and,
    DisjointRegionCuts.label_eq_inl_iff G (regions G U V) (pair_regions_disjoint G U V hUV),
    DisjointRegionCuts.label_eq_inr_iff]
  constructor
  · rintro ⟨e, h | h⟩
    · refine ⟨G.src e, h.1, ?_, e, Or.inl ⟨rfl, h.2⟩⟩
      exact fun heq => (outsideLabel G U V v).2 i (heq ▸ h.1)
    · refine ⟨G.dst e, h.2, ?_, e, Or.inr ⟨h.1, rfl⟩⟩
      exact fun heq => (outsideLabel G U V v).2 i (heq ▸ h.2)
  · rintro ⟨u, hu, hne, e, h | h⟩
    · exact ⟨e, Or.inl ⟨h.1 ▸ hu, h.2⟩⟩
    · exact ⟨e, Or.inr ⟨h.1, h.2 ▸ hu⟩⟩

end Erdos1016.FiniteMultiGraph.SeedPairCorrelation
