import Erdos1016.Nonbacktracking.Walks.CycleWords
import Erdos1016.Extremal.Capacity.WitnessOutsideBound

set_option autoImplicit false

/-!
# Adding chords to a finite simple graph

The cycle-count bound applies the forest estimate to a graph with extra
chords. This module adds a list of distinct non-edges to a physical graph. The
vertex set does not change. Old words, cycle words and connectivity lift to
the extended graph, and the cycle rank grows by at most the number of chords.
-/

noncomputable section
open scoped BigOperators

namespace Erdos1016.CycleCount
open PhysicalGraph

/-- Adjacency in the simple graph of `G`, from one physical edge. -/
theorem adj_of_endpoints (G : PhysicalGraph) {u v : G.Vertex} (e : G.Edge)
    (h : (G.src e = u ∧ G.dst e = v) ∨ (G.src e = v ∧ G.dst e = u)) :
    G.toSimpleGraph.Adj u v := ⟨e, one_ne_zero, h⟩

/-- Distinct non-edges of `G`, to be added as new labelled edges. -/
structure Chords (G : PhysicalGraph) where
  count : ℕ
  cs : Fin count → G.Vertex
  cd : Fin count → G.Vertex
  ne : ∀ j, cs j ≠ cd j
  fresh : ∀ j, ¬ G.toSimpleGraph.Adj (cs j) (cd j)
  distinct : ∀ i j, s(cs i, cd i) = s(cs j, cd j) → i = j

variable (G : PhysicalGraph) (C : Chords G)

/-- The graph `G` with the chords added. The vertex set is unchanged. -/
def addChords : PhysicalGraph where
  vertexCount := G.vertexCount
  edgeCount := G.edgeCount + C.count
  src := fun e => Fin.addCases (motive := fun _ => Fin G.vertexCount) G.src C.cs e
  dst := fun e => Fin.addCases (motive := fun _ => Fin G.vertexCount) G.dst C.cd e
  noLoops := by
    intro e
    induction e using Fin.addCases with
    | left e => simpa using G.noLoops e
    | right j => simpa using C.ne j
  simple := by
    intro e f h
    induction e using Fin.addCases with
    | left e =>
      induction f using Fin.addCases with
      | left f =>
        simp only [Fin.addCases_left] at h
        exact congrArg (Fin.castAdd C.count) (G.simple e f h)
      | right j =>
        simp only [Fin.addCases_left, Fin.addCases_right] at h
        exact absurd (adj_of_endpoints G e h) (C.fresh j)
    | right i =>
      induction f using Fin.addCases with
      | left f =>
        simp only [Fin.addCases_left, Fin.addCases_right] at h
        refine absurd (adj_of_endpoints G f ?_) (C.fresh i)
        rcases h with h | h
        · exact Or.inl ⟨h.1.symm, h.2.symm⟩
        · exact Or.inr ⟨h.2.symm, h.1.symm⟩
      | right j =>
        simp only [Fin.addCases_right] at h
        exact congrArg (Fin.natAdd G.edgeCount) (C.distinct i j (Sym2.eq_iff.2 h))

/-- An old edge, as an edge of the extended graph. -/
def oldEdge (e : G.Edge) : (addChords G C).Edge := Fin.castAdd C.count e

/-- A new chord, as an edge of the extended graph. -/
def newEdge (j : Fin C.count) : (addChords G C).Edge := Fin.natAdd G.edgeCount j

@[simp] theorem src_oldEdge (e : G.Edge) :
    (addChords G C).src (oldEdge G C e) = G.src e := by
  simp [addChords, oldEdge]

@[simp] theorem dst_oldEdge (e : G.Edge) :
    (addChords G C).dst (oldEdge G C e) = G.dst e := by
  simp [addChords, oldEdge]

@[simp] theorem src_newEdge (j : Fin C.count) :
    (addChords G C).src (newEdge G C j) = C.cs j := by
  simp [addChords, newEdge]

@[simp] theorem dst_newEdge (j : Fin C.count) :
    (addChords G C).dst (newEdge G C j) = C.cd j := by
  simp [addChords, newEdge]

/-- Every edge of the extended graph is an old edge or a new chord. -/
theorem edge_cases {P : (addChords G C).Edge → Prop}
    (hold : ∀ e, P (oldEdge G C e)) (hnew : ∀ j, P (newEdge G C j)) : ∀ e, P e := by
  show ∀ e : Fin (G.edgeCount + C.count), P e
  intro e
  induction e using Fin.addCases with
  | left e => exact hold e
  | right j => exact hnew j

theorem oldEdge_injective : Function.Injective (oldEdge G C) :=
  Fin.castAdd_injective _ _

theorem oldEdge_ne_newEdge (e : G.Edge) (j : Fin C.count) :
    oldEdge G C e ≠ newEdge G C j := by
  intro h
  have h1 : (oldEdge G C e : ℕ) < G.edgeCount := by simp [oldEdge]
  have h2 : G.edgeCount ≤ (newEdge G C j : ℕ) := by simp [newEdge]
  rw [h] at h1
  omega

/-- Extension of a word by zero on the new chords. -/
def liftWord (x : G.Word) : (addChords G C).Word :=
  fun e => Fin.addCases (motive := fun _ => F₂) x (fun _ => 0) e

@[simp] theorem liftWord_old (x : G.Word) (e : G.Edge) :
    liftWord G C x (oldEdge G C e) = x e := by
  simp [liftWord, oldEdge]

@[simp] theorem liftWord_new (x : G.Word) (j : Fin C.count) :
    liftWord G C x (newEdge G C j) = 0 := by
  simp [liftWord, newEdge]

/-- The boundary of a word of the extended graph, split into old and new edges. -/
theorem boundary_addChords_apply (z : (addChords G C).Word) (v : G.Vertex) :
    (addChords G C).boundary z v =
      (∑ e : G.Edge, ((if G.src e = v then z (oldEdge G C e) else 0) +
        (if G.dst e = v then z (oldEdge G C e) else 0))) +
      ∑ j : Fin C.count, ((if C.cs j = v then z (newEdge G C j) else 0) +
        (if C.cd j = v then z (newEdge G C j) else 0)) := by
  change (∑ e : Fin (G.edgeCount + C.count),
    ((if (addChords G C).src e = v then z e else 0) +
      (if (addChords G C).dst e = v then z e else 0))) = _
  rw [Fin.sum_univ_add]
  change (∑ e : G.Edge,
      ((if (addChords G C).src (oldEdge G C e) = v then z (oldEdge G C e) else 0) +
        (if (addChords G C).dst (oldEdge G C e) = v then z (oldEdge G C e) else 0))) +
    (∑ j : Fin C.count,
      ((if (addChords G C).src (newEdge G C j) = v then z (newEdge G C j) else 0) +
        (if (addChords G C).dst (newEdge G C j) = v then z (newEdge G C j) else 0))) = _
  simp only [src_oldEdge, dst_oldEdge, src_newEdge, dst_newEdge]

/-- Lifting a word does not change its boundary. -/
theorem boundary_liftWord (x : G.Word) :
    (addChords G C).boundary (liftWord G C x) = G.boundary x := by
  funext v
  rw [boundary_addChords_apply]
  simp only [liftWord_old, liftWord_new, ite_self, add_zero, Finset.sum_const_zero]
  rfl

/-- Lifting a word does not change its selected graph. -/
theorem selectedGraph_liftWord (x : G.Word) :
    (addChords G C).selectedGraph (liftWord G C x) = G.selectedGraph x := by
  ext u v
  constructor
  · rintro ⟨e, he, h⟩
    revert he h
    refine edge_cases G C (P := fun e => liftWord G C x e ≠ 0 →
      (((addChords G C).src e = u ∧ (addChords G C).dst e = v) ∨
        ((addChords G C).src e = v ∧ (addChords G C).dst e = u)) →
      (G.selectedGraph x).Adj u v) ?_ ?_ e
    · intro e he h
      exact ⟨e, by simpa using he, by simpa using h⟩
    · intro j he _
      exact absurd (liftWord_new G C x j) he
  · rintro ⟨e, he, h⟩
    exact ⟨oldEdge G C e, by simpa using he, by simpa using h⟩

theorem mem_usedVertices_iff (H : PhysicalGraph) (x : H.Word) (v : H.Vertex) :
    v ∈ H.usedVertices x ↔ ∃ e, x e ≠ 0 ∧ H.incident e v := by
  simp [PhysicalGraph.usedVertices]

/-- Lifting a word does not change its used vertices. -/
theorem usedVertices_liftWord (x : G.Word) :
    (addChords G C).usedVertices (liftWord G C x) = G.usedVertices x := by
  ext v
  rw [mem_usedVertices_iff, mem_usedVertices_iff]
  constructor
  · rintro ⟨e, he, hi⟩
    revert he hi
    refine edge_cases G C (P := fun e => liftWord G C x e ≠ 0 →
      (addChords G C).incident e v → ∃ e, x e ≠ 0 ∧ G.incident e v) ?_ ?_ e
    · intro e he hi
      exact ⟨e, by simpa using he, by simpa [PhysicalGraph.incident] using hi⟩
    · intro j he _
      exact absurd (liftWord_new G C x j) he
  · rintro ⟨e, he, hi⟩
    exact ⟨oldEdge G C e, by simpa using he, by simpa [PhysicalGraph.incident] using hi⟩

/-- Lifting a word does not change its selected degrees. -/
theorem selectedDegree_liftWord (x : G.Word) (v : G.Vertex) :
    (addChords G C).selectedDegree (liftWord G C x) v = G.selectedDegree x v := by
  rw [Nonbacktracking.selectedDegree_eq_neighbor_ncard,
    Nonbacktracking.selectedDegree_eq_neighbor_ncard, selectedGraph_liftWord]

/-- A cycle word of `G` is a cycle word of the extended graph. -/
theorem isCycleWord_liftWord {x : G.Word} (hx : G.IsCycleWord x) :
    (addChords G C).IsCycleWord (liftWord G C x) := by
  obtain ⟨hne, hb, hconn, hdeg⟩ := hx
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro h
    apply hne
    funext e
    have := congrFun h (oldEdge G C e)
    simpa using this
  · rw [boundary_liftWord]
    exact hb
  · rw [selectedGraph_liftWord, usedVertices_liftWord]
    exact hconn
  · intro v hv
    rw [usedVertices_liftWord] at hv
    rw [selectedDegree_liftWord]
    exact hdeg v hv

/-- The lift of a cycle of `G` to the extended graph. -/
def liftCycleWord (c : G.CycleWord) : (addChords G C).CycleWord :=
  ⟨liftWord G C c.1, isCycleWord_liftWord G C c.2⟩

@[simp] theorem liftCycleWord_old (c : G.CycleWord) (e : G.Edge) :
    (liftCycleWord G C c).1 (oldEdge G C e) = c.1 e := liftWord_old G C c.1 e

@[simp] theorem liftCycleWord_new (c : G.CycleWord) (j : Fin C.count) :
    (liftCycleWord G C c).1 (newEdge G C j) = 0 := liftWord_new G C c.1 j

/-- The simple graph of `G` is a subgraph of the simple graph of the extension. -/
theorem toSimpleGraph_le_addChords :
    G.toSimpleGraph ≤ (addChords G C).toSimpleGraph := by
  intro u v h
  obtain ⟨e, _, h⟩ := h
  exact adj_of_endpoints (addChords G C) (oldEdge G C e) (by simpa using h)

/-- Adding chords keeps a connected graph connected. -/
theorem addChords_connected (hG : G.IsConnected) : (addChords G C).IsConnected :=
  SimpleGraph.Connected.mono (toSimpleGraph_le_addChords G C) hG

/-- The two ends of a new chord are adjacent in the extended graph. -/
theorem adj_newEdge (j : Fin C.count) :
    (addChords G C).toSimpleGraph.Adj (C.cs j) (C.cd j) :=
  adj_of_endpoints (addChords G C) (newEdge G C j)
    (Or.inl ⟨src_newEdge G C j, dst_newEdge G C j⟩)

theorem physicalPair_oldEdge (e : G.Edge) :
    Nonbacktracking.physicalPair (addChords G C) (oldEdge G C e) =
      Nonbacktracking.physicalPair G e := by
  simp [Nonbacktracking.physicalPair]

theorem physicalPair_newEdge (j : Fin C.count) :
    Nonbacktracking.physicalPair (addChords G C) (newEdge G C j) = s(C.cs j, C.cd j) := by
  simp [Nonbacktracking.physicalPair]

/-- The lift of a cycle-space element of `G`. -/
def liftCycleSpace (x : G.CycleSpace) : (addChords G C).CycleSpace :=
  ⟨liftWord G C x.1, by
    rw [LinearMap.mem_ker, boundary_liftWord]
    exact LinearMap.mem_ker.mp x.2⟩

theorem liftCycleSpace_injective : Function.Injective (liftCycleSpace G C) := by
  intro x y h
  apply Subtype.ext
  funext e
  have := congrFun (congrArg Subtype.val h) (oldEdge G C e)
  simpa [liftCycleSpace] using this

/-- Adding chords does not lower the cycle rank. -/
theorem cycleRank_le_addChords : G.cycleRank ≤ (addChords G C).cycleRank := by
  have hcard := Fintype.card_le_of_injective _ (liftCycleSpace_injective G C)
  rw [G.cycleSpace_card, (addChords G C).cycleSpace_card] at hcard
  exact (Nat.pow_le_pow_iff_right (by norm_num)).mp hcard

/-- Each chord raises the cycle rank by at most one. -/
theorem cycleRank_addChords_le :
    (addChords G C).cycleRank ≤ G.cycleRank + C.count := by
  classical
  let π : (addChords G C).CycleSpace →ₗ[F₂] (Fin C.count → F₂) :=
    { toFun := fun x j => x.1 (newEdge G C j)
      map_add' := fun x y => rfl
      map_smul' := fun a x => rfl }
  have hsplit := LinearMap.finrank_range_add_finrank_ker π
  have hrange : Module.finrank F₂ (LinearMap.range π) ≤ C.count := by
    have h := Submodule.finrank_le (LinearMap.range π)
    simpa using h
  have hkey : ∀ x : LinearMap.ker π,
      x.1.1 = liftWord G C (fun e => x.1.1 (oldEdge G C e)) := by
    intro x
    funext e
    revert e
    refine edge_cases G C ?_ ?_
    · intro e
      simp
    · intro j
      have h := congrFun (LinearMap.mem_ker.mp x.2) j
      rw [liftWord_new]
      exact h
  let ρ : LinearMap.ker π →ₗ[F₂] G.CycleSpace :=
    { toFun := fun x => ⟨fun e => x.1.1 (oldEdge G C e), by
        rw [LinearMap.mem_ker]
        have hb := LinearMap.mem_ker.mp x.1.2
        rw [hkey x, boundary_liftWord] at hb
        exact hb⟩
      map_add' := fun x y => rfl
      map_smul' := fun a x => rfl }
  have hρ : Function.Injective ρ := by
    intro x y h
    apply Subtype.ext
    apply Subtype.ext
    rw [hkey x, hkey y]
    exact congrArg (liftWord G C) (congrArg Subtype.val h)
  have hker : Module.finrank F₂ (LinearMap.ker π) ≤ G.cycleRank :=
    LinearMap.finrank_le_finrank_of_injective hρ
  have hrank : (addChords G C).cycleRank =
      Module.finrank F₂ (addChords G C).CycleSpace := rfl
  omega

end Erdos1016.CycleCount
