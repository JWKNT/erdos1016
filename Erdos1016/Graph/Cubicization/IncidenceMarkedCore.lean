import Erdos1016.Graph.Cubicization.IncidenceRealization

set_option autoImplicit false
set_option maxHeartbeats 1000000

/-!
# Marked incidence prefixes have minimum degree two

When every witness vertex has at least two witness incidences, each marked
vertex has one marked path neighbour and one marked original-edge neighbour.
The two neighbours lie in different original rows. This places the entire
marked subgraph inside any maximal induced two-core of the expansion.
-/

noncomputable section

namespace Erdos1016.ShortProof.IncidencePaths

local instance incidenceMarkedDecidable (p : Prop) : Decidable p := Classical.propDecidable p

variable (G : PhysicalGraph) (W : Finset G.Edge)

lemma witnessCount_eq_filter_card (v : G.Vertex) :
    witnessCount G W v = (W.filter (fun e => G.incident e v)).card := by
  let f : WitnessIncidence G W v ≃ {e // e ∈ W.filter (fun e => G.incident e v)} := {
    toFun e := ⟨e.1.1, Finset.mem_filter.mpr ⟨e.2, e.1.2⟩⟩
    invFun e := ⟨⟨e.1, (Finset.mem_filter.mp e.2).2⟩, (Finset.mem_filter.mp e.2).1⟩
    left_inv _ := rfl
    right_inv _ := rfl }
  exact (Fintype.card_congr f).trans (Fintype.card_coe _)

lemma witnessCount_eq_selectedDegree (v : G.Vertex) :
    witnessCount G W v = G.selectedDegree (fun e => if e ∈ W then 1 else 0) v := by
  rw [witnessCount_eq_filter_card]
  unfold PhysicalGraph.selectedDegree
  congr 1
  ext e
  by_cases he : e ∈ W <;> simp [he]

lemma incidenceVertex_eq_endpoint {v : G.Vertex} (e : Incidence G v) :
    incidenceVertex G W v e = source G W e.1 ∨ incidenceVertex G W v e = target G W e.1 := by
  rcases e with ⟨e, hs | ht⟩
  · subst v
    exact Or.inl rfl
  · subst v
    exact Or.inr rfl

/-- Every marked vertex has a marked neighbour across its original edge. -/
theorem marked_external_neighbor (a : MarkedVertex G W) :
    ∃ b : MarkedVertex G W, (markedGraph G W).Adj a b ∧ a.1.1 ≠ b.1.1 := by
  let i : Fin (witnessCount G W a.1.1 + otherCount G W a.1.1) :=
    ⟨a.1.2.val, lt_of_lt_of_le a.2 (Nat.le_add_right _ _)⟩
  let e := (incidenceIndex G W a.1.1).symm i
  have ha : incidenceVertex G W a.1.1 e = a.1 := by
    refine vertex_ext G W (a := incidenceVertex G W a.1.1 e) (b := a.1) rfl ?_
    change (incidenceIndex G W a.1.1 e).val = a.1.2.val
    rw [Equiv.apply_symm_apply]
  have heW : e.1 ∈ W := by
    apply (incidenceVertex_marked_iff G W a.1.1 e).mp
    rw [ha]
    exact a.2
  rcases incidenceVertex_eq_endpoint G W e with hs | ht
  · let b : MarkedVertex G W := ⟨target G W e.1, (target_marked_iff G W e.1).mpr heW⟩
    have hsrc : a.1 = source G W e.1 := ha.symm.trans hs
    refine ⟨b, ?_, ?_⟩
    · exact Or.inr ⟨e.1, Or.inl ⟨hsrc, rfl⟩⟩
    · exact edgeAdj_contract_ne G W ⟨e.1, Or.inl ⟨hsrc, rfl⟩⟩
  · let b : MarkedVertex G W := ⟨source G W e.1, (source_marked_iff G W e.1).mpr heW⟩
    have hdst : a.1 = target G W e.1 := ha.symm.trans ht
    refine ⟨b, ?_, ?_⟩
    · exact Or.inr ⟨e.1, Or.inr ⟨hdst, rfl⟩⟩
    · exact edgeAdj_contract_ne G W ⟨e.1, Or.inr ⟨hdst, rfl⟩⟩

/-- A marked prefix of length at least two gives each of its vertices a
marked path neighbour. -/
theorem marked_path_neighbor (a : MarkedVertex G W)
    (hk : 2 ≤ witnessCount G W a.1.1) :
    ∃ b : MarkedVertex G W, (markedGraph G W).Adj a b ∧ a.1.1 = b.1.1 := by
  rcases a with ⟨⟨v, i⟩, hi⟩
  change i.val < witnessCount G W v at hi
  change 2 ≤ witnessCount G W v at hk
  by_cases hz : i.val = 0
  · have hone : 1 < witnessCount G W v := by omega
    let j : Fin (pathSize G W v) := ⟨1, lt_of_lt_of_le hone (witnessCount_le_pathSize G W v)⟩
    refine ⟨⟨⟨v, j⟩, hone⟩, ?_, rfl⟩
    exact Or.inl ⟨rfl, Or.inl (by change i.val + 1 = 1; omega)⟩
  · have hpred : i.val - 1 < witnessCount G W v := by omega
    let j : Fin (pathSize G W v) := ⟨i.val - 1,
      lt_of_lt_of_le hpred (witnessCount_le_pathSize G W v)⟩
    refine ⟨⟨⟨v, j⟩, hpred⟩, ?_, rfl⟩
    exact Or.inl ⟨rfl, Or.inr (by change i.val - 1 + 1 = i.val; omega)⟩

theorem marked_two_neighbors
    (hW : ∀ v, witnessCount G W v = 0 ∨ 2 ≤ witnessCount G W v)
    (a : MarkedVertex G W) :
    ∃ b c : MarkedVertex G W, (markedGraph G W).Adj a b ∧
      (markedGraph G W).Adj a c ∧ b ≠ c := by
  have hk : 2 ≤ witnessCount G W a.1.1 := by
    rcases hW a.1.1 with h | h
    · have ha := a.2
      change a.1.2.val < witnessCount G W a.1.1 at ha
      omega
    · exact h
  obtain ⟨b, hab, hb⟩ := marked_path_neighbor G W a hk
  obtain ⟨c, hac, hc⟩ := marked_external_neighbor G W a
  refine ⟨b, c, hab, hac, ?_⟩
  intro h
  subst c
  exact hc hb

private lemma degree_ge_two_of_neighbors {V : Type*} [Fintype V]
    (H : SimpleGraph V) {a b c : V} (hab : H.Adj a b) (hac : H.Adj a c) (hbc : b ≠ c) :
    2 ≤ H.degree a := by
  have hsub : ({b, c} : Finset V) ⊆ H.neighborFinset a := by
    intro v hv
    rcases Finset.mem_insert.mp hv with h | h
    · exact (SimpleGraph.mem_neighborFinset H a v).mpr (h.symm ▸ hab)
    · have h' : v = c := Finset.mem_singleton.mp h
      exact (SimpleGraph.mem_neighborFinset H a v).mpr (h'.symm ▸ hac)
  have hcard := Finset.card_le_card hsub
  simpa only [Finset.card_pair hbc, SimpleGraph.card_neighborFinset_eq_degree] using hcard

theorem marked_min_degree_two
    (hW : ∀ v, witnessCount G W v = 0 ∨ 2 ≤ witnessCount G W v)
    (a : MarkedVertex G W) : 2 ≤ (markedGraph G W).degree a := by
  obtain ⟨b, c, hab, hac, hbc⟩ := marked_two_neighbors G W hW a
  exact degree_ge_two_of_neighbors _ hab hac hbc

theorem marked_physical_min_degree_two
    (hW : ∀ v, witnessCount G W v = 0 ∨ 2 ≤ witnessCount G W v)
    (a : {v // v ∈ markedVertices G W}) :
    2 ≤ ((physical G W).toSimpleGraph.induce
      (↑(markedVertices G W) : Set (physical G W).Vertex)).degree a := by
  obtain ⟨a, rfl⟩ := (markedVertexLabels G W).surjective a
  obtain ⟨b, c, hab, hac, hbc⟩ := marked_two_neighbors G W hW a
  exact degree_ge_two_of_neighbors _ ((markedRealizationIso G W).toHom.map_adj hab)
    ((markedRealizationIso G W).toHom.map_adj hac)
    (fun h => hbc ((markedRealizationIso G W).injective h))

end Erdos1016.ShortProof.IncidencePaths
