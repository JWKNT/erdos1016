import Mathlib.Combinatorics.SimpleGraph.Connectivity.WalkCounting
import Erdos1016.Graph.Basic
import Mathlib.Combinatorics.SimpleGraph.Hasse

set_option autoImplicit false
set_option maxHeartbeats 1000000

/-!
# Expansion into incidence paths

Each nonisolated vertex is replaced by a path with one vertex for each of its
edge incidences. An isolated vertex is retained. The original edges join their
two distinct incidence vertices, so the resulting graph is simple and has
maximum degree three. Witness incidences come first along every path.

This construction retains the degree-two path ends. Subsequent pruning and
suppression can remove them; neither operation is part of this module.
-/

noncomputable section
open scoped BigOperators
namespace Erdos1016.ShortProof.IncidencePaths

local instance decidableProposition (p : Prop) : Decidable p := Classical.propDecidable p

variable (G : PhysicalGraph) (W : Finset G.Edge)

abbrev Incidence (v : G.Vertex) := {e : G.Edge // G.incident e v}

abbrev WitnessIncidence (v : G.Vertex) := {e : Incidence G v // e.1 ∈ W}

abbrev OtherIncidence (v : G.Vertex) := {e : Incidence G v // e.1 ∉ W}

def witnessCount (v : G.Vertex) : ℕ := Fintype.card (WitnessIncidence G W v)

def otherCount (v : G.Vertex) : ℕ := Fintype.card (OtherIncidence G W v)

/-- An actual ordering of all incidences, with witness incidences first. -/
def incidenceIndex (v : G.Vertex) :
    Incidence G v ≃ Fin (witnessCount G W v + otherCount G W v) := by
  exact (Equiv.sumCompl (fun e : Incidence G v => e.1 ∈ W)).symm |>.trans
    ((Equiv.sumCongr (Fintype.equivFin _) (Fintype.equivFin _)).trans finSumFinEquiv)

lemma incidenceIndex_lt_iff (v : G.Vertex) (e : Incidence G v) :
    (incidenceIndex G W v e).val < witnessCount G W v ↔ e.1 ∈ W := by
  unfold incidenceIndex
  dsimp only [Equiv.trans_apply, Equiv.sumCompl, Equiv.symm, Equiv.sumCongr,
    Equiv.coe_fn_mk]
  by_cases he : e.1 ∈ W
  · rw [dif_pos he]
    change (Fintype.equivFin (WitnessIncidence G W v) ⟨e, he⟩).val < _ ↔ _
    exact iff_of_true (Fintype.equivFin (WitnessIncidence G W v) ⟨e, he⟩).isLt he
  · rw [dif_neg he]
    change witnessCount G W v + (Fintype.equivFin (OtherIncidence G W v) ⟨e, he⟩).val < _ ↔ _
    simp only [he, iff_false, not_lt]
    omega

def pathSize (v : G.Vertex) : ℕ :=
  max 1 (witnessCount G W v + otherCount G W v)

lemma incidence_count_eq_degree (v : G.Vertex) :
    witnessCount G W v + otherCount G W v = G.degree v := by
  have h := Fintype.card_congr (incidenceIndex G W v)
  rw [Fintype.card_fin] at h
  rw [← h]
  simp [Fintype.card_subtype, PhysicalGraph.degree, PhysicalGraph.selectedDegree]

lemma pathSize_eq_max_degree (v : G.Vertex) : pathSize G W v = max 1 (G.degree v) := by
  rw [pathSize, incidence_count_eq_degree]

abbrev Vertex := (v : G.Vertex) × Fin (pathSize G W v)

def contract (a : Vertex G W) : G.Vertex := a.1

def incidenceVertex (v : G.Vertex) (e : Incidence G v) : Vertex G W :=
  ⟨v, (incidenceIndex G W v e).castLE (Nat.le_max_right _ _)⟩

def source (e : G.Edge) : Vertex G W :=
  incidenceVertex G W (G.src e) ⟨e, Or.inl rfl⟩

def target (e : G.Edge) : Vertex G W :=
  incidenceVertex G W (G.dst e) ⟨e, Or.inr rfl⟩

@[simp] lemma contract_source (e : G.Edge) : contract G W (source G W e) = G.src e := rfl
@[simp] lemma contract_target (e : G.Edge) : contract G W (target G W e) = G.dst e := rfl

lemma vertex_ext {a b : Vertex G W} (hv : a.1 = b.1) (hi : a.2.val = b.2.val) : a = b := by
  rcases a with ⟨v, i⟩
  rcases b with ⟨w, j⟩
  dsimp at hv hi
  subst w
  exact congrArg (Sigma.mk v) (Fin.ext hi)

lemma incidenceVertex_edge_injective {v w : G.Vertex}
    {e : Incidence G v} {f : Incidence G w}
    (h : incidenceVertex G W v e = incidenceVertex G W w f) : e.1 = f.1 := by
  have hv := congrArg Sigma.fst h
  change v = w at hv
  subst w
  have hi := congrArg (fun a : Vertex G W => a.2.val) h
  exact congrArg Subtype.val ((incidenceIndex G W v).injective (Fin.ext hi))

lemma source_ne_target (e : G.Edge) : source G W e ≠ target G W e := by
  intro h
  exact G.noLoops e (congrArg (contract G W) h)

def PathAdj (a b : Vertex G W) : Prop :=
  a.1 = b.1 ∧ (a.2.val + 1 = b.2.val ∨ b.2.val + 1 = a.2.val)

def EdgeAdj (a b : Vertex G W) : Prop :=
  ∃ e : G.Edge, (a = source G W e ∧ b = target G W e) ∨
    (a = target G W e ∧ b = source G W e)

/-- The constructed simple graph; path edges and original edges remain distinct. -/
def graph : SimpleGraph (Vertex G W) where
  Adj a b := PathAdj G W a b ∨ EdgeAdj G W a b
  symm := by
    intro a b h
    rcases h with ⟨hv, hi | hi⟩ | ⟨e, h | h⟩
    · exact Or.inl ⟨hv.symm, Or.inr hi⟩
    · exact Or.inl ⟨hv.symm, Or.inl hi⟩
    · exact Or.inr ⟨e, Or.inr ⟨h.2, h.1⟩⟩
    · exact Or.inr ⟨e, Or.inl ⟨h.2, h.1⟩⟩
  loopless := by
    intro a h
    rcases h with ⟨_, h | h⟩ | ⟨e, h | h⟩
    · omega
    · omega
    · exact source_ne_target G W e (h.1.symm.trans h.2)
    · exact source_ne_target G W e (h.2.symm.trans h.1)

lemma source_adj_target (e : G.Edge) : (graph G W).Adj (source G W e) (target G W e) :=
  Or.inr ⟨e, Or.inl ⟨rfl, rfl⟩⟩

lemma edgeAdj_contract_ne {a b : Vertex G W} (h : EdgeAdj G W a b) : a.1 ≠ b.1 := by
  obtain ⟨e, h | h⟩ := h
  · rcases h with ⟨rfl, rfl⟩
    exact G.noLoops e
  · rcases h with ⟨rfl, rfl⟩
    exact (G.noLoops e).symm

/-- Each expanded vertex is incident to at most one original edge. -/
lemma edgeAdj_unique {a b c : Vertex G W}
    (hb : EdgeAdj G W a b) (hc : EdgeAdj G W a c) : b = c := by
  obtain ⟨e, hb | hb⟩ := hb <;> obtain ⟨f, hc | hc⟩ := hc
  · have hef : e = f := incidenceVertex_edge_injective G W (hb.1.symm.trans hc.1)
    subst f
    exact hb.2.trans hc.2.symm
  · have hef : e = f := incidenceVertex_edge_injective G W (hb.1.symm.trans hc.1)
    subst f
    exact False.elim (source_ne_target G W e (hb.1.symm.trans hc.1))
  · have hef : e = f := incidenceVertex_edge_injective G W (hb.1.symm.trans hc.1)
    subst f
    exact False.elim (source_ne_target G W e (hc.1.symm.trans hb.1))
  · have hef : e = f := incidenceVertex_edge_injective G W (hb.1.symm.trans hc.1)
    subst f
    exact hb.2.trans hc.2.symm

/-- Contraction sends a path edge to a vertex and an original edge to itself. -/
theorem adjacency_contract {a b : Vertex G W} (h : (graph G W).Adj a b) :
    contract G W a = contract G W b ∨
      G.toSimpleGraph.Adj (contract G W a) (contract G W b) := by
  rcases h with h | ⟨e, h | h⟩
  · exact Or.inl h.1
  · exact Or.inr ⟨e, one_ne_zero, Or.inl ⟨congrArg Sigma.fst h.1.symm,
      congrArg Sigma.fst h.2.symm⟩⟩
  · exact Or.inr ⟨e, one_ne_zero, Or.inr ⟨congrArg Sigma.fst h.2.symm,
      congrArg Sigma.fst h.1.symm⟩⟩

/-- The degree bound is proved from the two possible path neighbours and the
single possible original-edge neighbour. -/
theorem degree_le_three (a : Vertex G W) : (graph G W).degree a ≤ 3 := by
  let code : (graph G W).neighborSet a → Fin 3 := fun b =>
    if a.1 = b.1.1 then (if b.1.2.val < a.2.val then 0 else 1) else 2
  have hc : Function.Injective code := by
    intro b c heq
    have hb := b.2
    have hc := c.2
    change PathAdj G W a b.1 ∨ EdgeAdj G W a b.1 at hb
    change PathAdj G W a c.1 ∨ EdgeAdj G W a c.1 at hc
    apply Subtype.ext
    by_cases hba : a.1 = b.1.1 <;> by_cases hca : a.1 = c.1.1
    · have hb' : PathAdj G W a b.1 := hb.resolve_right (fun h => edgeAdj_contract_ne G W h hba)
      have hc' : PathAdj G W a c.1 := hc.resolve_right (fun h => edgeAdj_contract_ne G W h hca)
      apply vertex_ext G W (hba.symm.trans hca)
      simp only [code, if_pos hba, if_pos hca] at heq
      have hs : (b.1.2.val < a.2.val ↔ c.1.2.val < a.2.val) := by
        by_cases hb : b.1.2.val < a.2.val <;> by_cases hc : c.1.2.val < a.2.val
        all_goals simp only [hb, hc, ↓reduceIte] at heq ⊢
        all_goals norm_num at heq
      rcases hb'.2 with hb' | hb' <;> rcases hc'.2 with hc' | hc' <;> omega
    · simp only [code, if_pos hba, if_neg hca] at heq
      split_ifs at heq <;> have := congrArg Fin.val heq <;> norm_num at this
    · simp only [code, if_neg hba, if_pos hca] at heq
      split_ifs at heq <;> have := congrArg Fin.val heq <;> norm_num at this
    · exact edgeAdj_unique G W (hb.resolve_left (fun h => hba h.1))
        (hc.resolve_left (fun h => hca h.1))
  have := Fintype.card_le_of_injective code hc
  simpa only [SimpleGraph.card_neighborSet_eq_degree, Fintype.card_fin] using this


/-- The prefix consisting exactly of the witness incidences. -/
def Marked (a : Vertex G W) : Prop := a.2.val < witnessCount G W a.1

abbrev MarkedVertex := {a : Vertex G W // Marked G W a}

def markedGraph : SimpleGraph (MarkedVertex G W) := (graph G W).induce (Marked G W)

lemma incidenceVertex_marked_iff (v : G.Vertex) (e : Incidence G v) :
    Marked G W (incidenceVertex G W v e) ↔ e.1 ∈ W :=
  incidenceIndex_lt_iff G W v e

lemma source_marked_iff (e : G.Edge) : Marked G W (source G W e) ↔ e ∈ W :=
  incidenceVertex_marked_iff G W _ _

lemma target_marked_iff (e : G.Edge) : Marked G W (target G W e) ↔ e ∈ W :=
  incidenceVertex_marked_iff G W _ _

lemma witnessCount_le_pathSize (v : G.Vertex) : witnessCount G W v ≤ pathSize G W v :=
  (Nat.le_add_right _ _).trans (Nat.le_max_right _ _)

def markedIndexEquiv : MarkedVertex G W ≃ (v : G.Vertex) × Fin (witnessCount G W v) where
  toFun a := ⟨a.1.1, ⟨a.1.2.val, a.2⟩⟩
  invFun a := ⟨⟨a.1, a.2.castLE (witnessCount_le_pathSize G W a.1)⟩, a.2.isLt⟩
  left_inv a := by
    apply Subtype.ext
    exact vertex_ext G W rfl rfl
  right_inv a := by
    rcases a with ⟨v, i⟩
    rfl

/-- The two incidences of every witness edge, counted once each. -/
def witnessEndsEquiv : ((v : G.Vertex) × WitnessIncidence G W v) ≃ {e // e ∈ W} × Bool where
  toFun a := (⟨a.2.1.1, a.2.2⟩, if G.src a.2.1.1 = a.1 then false else true)
  invFun a := if a.2 then
    ⟨G.dst a.1.1, ⟨⟨a.1.1, Or.inr rfl⟩, a.1.2⟩⟩ else
    ⟨G.src a.1.1, ⟨⟨a.1.1, Or.inl rfl⟩, a.1.2⟩⟩
  left_inv a := by
    rcases a with ⟨v, ⟨⟨e, he⟩, hW⟩⟩
    rcases he with he | he
    · subst v
      simp
    · subst v
      simp [G.noLoops e]
  right_inv a := by
    rcases a with ⟨e, b⟩
    cases b <;> simp [G.noLoops]

/-- There are exactly two marked vertices per witness edge. -/
theorem marked_card : Fintype.card (MarkedVertex G W) = 2 * W.card := by
  calc
    Fintype.card (MarkedVertex G W) =
        Fintype.card ((v : G.Vertex) × Fin (witnessCount G W v)) :=
      Fintype.card_congr (markedIndexEquiv G W)
    _ = Fintype.card ((v : G.Vertex) × WitnessIncidence G W v) :=
      Fintype.card_congr (Equiv.sigmaCongrRight fun v =>
        (Fintype.equivFin (WitnessIncidence G W v)).symm)
    _ = Fintype.card ({e // e ∈ W} × Bool) := Fintype.card_congr (witnessEndsEquiv G W)
    _ = 2 * W.card := by simp [Nat.mul_comm]

/-- Every original vertex retains at least one expanded vertex. -/
theorem contract_surjective : Function.Surjective (contract G W) := by
  intro v
  exact ⟨⟨v, ⟨0, lt_of_lt_of_le Nat.zero_lt_one (Nat.le_max_left _ _)⟩⟩, rfl⟩

def representative (v : G.Vertex) : Vertex G W :=
  ⟨v, ⟨0, lt_of_lt_of_le Nat.zero_lt_one (Nat.le_max_left _ _)⟩⟩

/-- A row of the expansion is the actual path graph on its incidence indices. -/
def rowHom (v : G.Vertex) : SimpleGraph.pathGraph (pathSize G W v) →g graph G W where
  toFun i := ⟨v, i⟩
  map_rel' h := Or.inl ⟨rfl, SimpleGraph.pathGraph_adj.mp h⟩

theorem row_reachable {a b : Vertex G W} (h : a.1 = b.1) : (graph G W).Reachable a b := by
  rcases a with ⟨v, i⟩
  rcases b with ⟨w, j⟩
  dsimp at h
  subst w
  exact (SimpleGraph.pathGraph_preconnected _ i j).map (rowHom G W v)

lemma adj_representatives {u v : G.Vertex} (h : G.toSimpleGraph.Adj u v) :
    (graph G W).Reachable (representative G W u) (representative G W v) := by
  obtain ⟨e, _, ⟨hs, ht⟩ | ⟨hs, ht⟩⟩ := h
  · exact (row_reachable G W hs.symm).trans
      ((source_adj_target G W e).reachable.trans (row_reachable G W ht))
  · exact (row_reachable G W ht.symm).trans
      ((source_adj_target G W e).symm.reachable.trans (row_reachable G W hs))

lemma reachable_representatives {u v : G.Vertex} (h : G.toSimpleGraph.Reachable u v) :
    (graph G W).Reachable (representative G W u) (representative G W v) := by
  obtain ⟨p⟩ := h
  induction p with
  | nil => exact SimpleGraph.Reachable.rfl
  | cons h _ ih => exact (adj_representatives G W h).trans ih

theorem reachable_of_contract {a b : Vertex G W}
    (h : G.toSimpleGraph.Reachable (contract G W a) (contract G W b)) :
    (graph G W).Reachable a b :=
  (row_reachable G W (a := a) (b := representative G W a.1) rfl).trans
    ((reachable_representatives G W h).trans
      (row_reachable G W (a := representative G W b.1) (b := b) rfl))

theorem connected (h : G.IsConnected) : (graph G W).Connected where
  preconnected a b := reachable_of_contract G W (h.preconnected a.1 b.1)
  nonempty := h.nonempty.map (representative G W)

/-- The marked prefix itself is connected, without travelling through unmarked
vertices of the expansion. -/
def markedRowHom (v : G.Vertex) :
    SimpleGraph.pathGraph (witnessCount G W v) →g markedGraph G W where
  toFun i := ⟨⟨v, i.castLE (witnessCount_le_pathSize G W v)⟩, i.isLt⟩
  map_rel' := by
    intro i j h
    have hi : i.val + 1 = j.val ∨ j.val + 1 = i.val := SimpleGraph.pathGraph_adj.mp h
    exact Or.inl ⟨rfl, hi⟩

theorem marked_row_reachable {a b : MarkedVertex G W} (h : a.1.1 = b.1.1) :
    (markedGraph G W).Reachable a b := by
  rcases a with ⟨⟨v, i⟩, hi⟩
  rcases b with ⟨⟨w, j⟩, hj⟩
  dsimp at h
  subst w
  exact (SimpleGraph.pathGraph_preconnected _ ⟨i.val, hi⟩ ⟨j.val, hj⟩).map (markedRowHom G W v)

/-- The original witness-support graph, omitting vertices without witness
incidences. In particular, ambient isolated vertices do not count as support
components. -/
def supportGraph : SimpleGraph {v : G.Vertex // 0 < witnessCount G W v} :=
  (G.selectedGraph (fun e => if e ∈ W then 1 else 0)).induce
    {v | 0 < witnessCount G W v}

def markedRepresentative (v : {v : G.Vertex // 0 < witnessCount G W v}) : MarkedVertex G W :=
  ⟨⟨v.1, ⟨0, lt_of_lt_of_le v.2 (witnessCount_le_pathSize G W v.1)⟩⟩, v.2⟩

lemma support_adj_representatives
    {u v : {v : G.Vertex // 0 < witnessCount G W v}}
    (h : (supportGraph G W).Adj u v) :
    (markedGraph G W).Reachable (markedRepresentative G W u) (markedRepresentative G W v) := by
  change ∃ e, (if e ∈ W then (1 : F₂) else 0) ≠ 0 ∧
    ((G.src e = u.1 ∧ G.dst e = v.1) ∨ (G.src e = v.1 ∧ G.dst e = u.1)) at h
  obtain ⟨e, he, hend⟩ := h
  have heW : e ∈ W := by
    by_contra hn
    simp only [hn, ↓reduceIte, ne_eq, not_true_eq_false] at he
  let s : MarkedVertex G W := ⟨source G W e, (source_marked_iff G W e).mpr heW⟩
  let t : MarkedVertex G W := ⟨target G W e, (target_marked_iff G W e).mpr heW⟩
  have hst : (markedGraph G W).Adj s t := source_adj_target G W e
  rcases hend with ⟨hs, ht⟩ | ⟨hs, ht⟩
  · exact (marked_row_reachable G W hs.symm).trans
      (hst.reachable.trans (marked_row_reachable G W ht))
  · exact (marked_row_reachable G W ht.symm).trans
      (hst.symm.reachable.trans (marked_row_reachable G W hs))

lemma support_reachable_representatives
    {u v : {v : G.Vertex // 0 < witnessCount G W v}}
    (h : (supportGraph G W).Reachable u v) :
    (markedGraph G W).Reachable (markedRepresentative G W u) (markedRepresentative G W v) := by
  obtain ⟨p⟩ := h
  induction p with
  | nil => exact SimpleGraph.Reachable.rfl
  | cons h _ ih => exact (support_adj_representatives G W h).trans ih

/-- A concrete map from original support components to marked components. -/
def supportComponentMap : (supportGraph G W).ConnectedComponent →
    (markedGraph G W).ConnectedComponent :=
  SimpleGraph.ConnectedComponent.lift
    (fun v => (markedGraph G W).connectedComponentMk (markedRepresentative G W v))
    (fun _ _ p _ => SimpleGraph.ConnectedComponent.sound
      (support_reachable_representatives G W p.reachable))

lemma supportComponentMap_surjective : Function.Surjective (supportComponentMap G W) := by
  intro c
  refine SimpleGraph.ConnectedComponent.ind ?_ c
  intro a
  let v : {v : G.Vertex // 0 < witnessCount G W v} :=
    ⟨a.1.1, lt_of_le_of_lt (Nat.zero_le _) a.2⟩
  refine ⟨(supportGraph G W).connectedComponentMk v, ?_⟩
  exact SimpleGraph.ConnectedComponent.sound (marked_row_reachable G W rfl)

/-- Replacing witness vertices by connected marked prefixes cannot increase
the number of edge-bearing witness components. -/
theorem marked_component_count_le :
    Nat.card (markedGraph G W).ConnectedComponent ≤ Nat.card (supportGraph G W).ConnectedComponent :=
  Nat.card_le_card_of_surjective (supportComponentMap G W) (supportComponentMap_surjective G W)

end Erdos1016.ShortProof.IncidencePaths
