import Erdos1016.ExactMaximumSupport.CubicReduction.PhysicalCycles
import Erdos1016.Nonbacktracking.Walks.CycleWords

set_option autoImplicit false

/-!
# A simple realization of a multigraph with no short cycles

The length-one and length-two cycle words exclude loops and parallel labels.
The physical realization then keeps every vertex, edge, and endpoint label.
This specializes the whole-region induced realization without reindexing.
-/

noncomputable section

namespace Erdos1016.ExactMaximumSupport.LargeGirth

local instance (p : Prop) : Decidable p := Classical.propDecidable p

open ShortProof.CycleCore
open CubicReduction

variable (G : FiniteMultiGraph)

/-- The word supported on one labelled edge. -/
def singletonWord (e : G.Edge) : G.EdgeWord := fun f => if f = e then 1 else 0

theorem singletonWord_support (e : G.Edge) :
    Finset.univ.filter (fun f => singletonWord G e f ≠ 0) = {e} := by
  classical
  ext f
  simp [singletonWord]

theorem singletonWord_degree (e : G.Edge) (v : G.Vertex) :
    G.selectedDegree (singletonWord G e) v =
      (if G.src e = v then 1 else 0) + (if G.dst e = v then 1 else 0) := by
  classical
  unfold FiniteMultiGraph.selectedDegree
  rw [singletonWord_support]
  by_cases hs : G.src e = v <;> by_cases ht : G.dst e = v
    <;> simp [Finset.filter_singleton, hs, ht]

theorem singletonWord_isCycle_of_loop (e : G.Edge) (he : G.src e = G.dst e) :
    G.IsCycleWord (singletonWord G e) := by
  classical
  refine ⟨?_, ?_, ?_⟩
  · intro hz
    have := congrFun hz e
    simp [singletonWord] at this
  · intro v
    rw [singletonWord_degree, ← he]
    by_cases hv : G.src e = v <;> simp [hv]
  · intro u v hu hv
    rw [singletonWord_degree, ← he] at hu hv
    have hu' : G.src e = u := by by_contra h; simp [h] at hu
    have hv' : G.src e = v := by by_contra h; simp [h] at hv
    exact (hu'.symm.trans hv') ▸ SimpleGraph.Reachable.refl u

theorem noLoops_of_no_short_cycle (hshort : ¬ G.HasCycleShorterThan 3) :
    ∀ e, G.src e ≠ G.dst e := by
  intro e he
  apply hshort
  refine ⟨singletonWord G e, singletonWord_isCycle_of_loop G e he, ?_⟩
  unfold FiniteMultiGraph.wordLength
  rw [singletonWord_support]
  simp

/-- The word supported on two distinct physical labels. -/
def pairWord (e f : G.Edge) : G.EdgeWord := fun d => if d = e ∨ d = f then 1 else 0

theorem pairWord_support (e f : G.Edge) :
    Finset.univ.filter (fun d => pairWord G e f d ≠ 0) = {e, f} := by
  classical
  ext d
  by_cases h : d = e <;> simp [pairWord, h]

theorem pairWord_degree (e f : G.Edge) (hef : e ≠ f) (v : G.Vertex) :
    G.selectedDegree (pairWord G e f) v =
      ((if G.src e = v then 1 else 0) + (if G.src f = v then 1 else 0)) +
      ((if G.dst e = v then 1 else 0) + (if G.dst f = v then 1 else 0)) := by
  classical
  unfold FiniteMultiGraph.selectedDegree
  rw [pairWord_support]
  by_cases hse : G.src e = v <;> by_cases hsf : G.src f = v
    <;> by_cases hte : G.dst e = v <;> by_cases htf : G.dst f = v
    <;> simp [Finset.filter_insert, Finset.filter_singleton, hse, hsf, hte, htf, hef]

theorem pairWord_isCycle_of_parallel (e f : G.Edge) (hef : e ≠ f)
    (he : G.src e ≠ G.dst e)
    (hp : (G.src e = G.src f ∧ G.dst e = G.dst f) ∨
      (G.src e = G.dst f ∧ G.dst e = G.src f)) :
    G.IsCycleWord (pairWord G e f) := by
  classical
  have hd (v : G.Vertex) : G.selectedDegree (pairWord G e f) v =
      if v = G.src e ∨ v = G.dst e then 2 else 0 := by
    rw [pairWord_degree G e f hef]
    rcases hp with ⟨hs, ht⟩ | ⟨hs, ht⟩ <;> rw [← hs, ← ht]
      <;> by_cases hv : v = G.src e <;> by_cases hw : v = G.dst e
      <;> simp_all [eq_comm]
  have hadj : (G.selectedGraph (pairWord G e f)).Adj (G.src e) (G.dst e) :=
    ⟨he, e, by simp [pairWord], Or.inl ⟨rfl, rfl⟩⟩
  refine ⟨?_, ?_, ?_⟩
  · intro hz
    have := congrFun hz e
    simp [pairWord] at this
  · intro v
    rw [hd]
    split <;> simp
  · intro u v hu hv
    rw [hd] at hu hv
    have hu' : u = G.src e ∨ u = G.dst e := by by_contra h; simp [h] at hu
    have hv' : v = G.src e ∨ v = G.dst e := by by_contra h; simp [h] at hv
    rcases hu' with rfl | rfl <;> rcases hv' with rfl | rfl
    · exact SimpleGraph.Reachable.refl _
    · exact hadj.reachable
    · exact hadj.symm.reachable
    · exact SimpleGraph.Reachable.refl _

theorem simple_of_no_short_cycle (hshort : ¬ G.HasCycleShorterThan 3) :
    ∀ e f, ((G.src e = G.src f ∧ G.dst e = G.dst f) ∨
      (G.src e = G.dst f ∧ G.dst e = G.src f)) → e = f := by
  intro e f hp
  by_contra hef
  apply hshort
  refine ⟨pairWord G e f, pairWord_isCycle_of_parallel G e f hef
    (noLoops_of_no_short_cycle G hshort e) hp, ?_⟩
  unfold FiniteMultiGraph.wordLength
  rw [pairWord_support]
  simp [hef]

theorem no_short_three_of_le (D : ℕ) (hD : 3 ≤ D)
    (hshort : ¬ G.HasCycleShorterThan D) : ¬ G.HasCycleShorterThan 3 := by
  rintro ⟨x, hx, hlen⟩
  exact hshort ⟨x, hx, hlen.trans_le hD⟩

variable (hshort : ¬ G.HasCycleShorterThan 3)

/-- The original labels give a physical simple graph once short cycles are excluded. -/
def realization : PhysicalGraph where
  vertexCount := G.vertexCount
  edgeCount := G.edgeCount
  src := G.src
  dst := G.dst
  noLoops := noLoops_of_no_short_cycle G hshort
  simple := simple_of_no_short_cycle G hshort

@[simp] theorem realization_asMultigraph : asMultigraph (realization G hshort) = G := rfl

@[simp] theorem realization_boundary : (realization G hshort).boundary = G.boundary := rfl

def realizationCycleSpaceEquiv : (realization G hshort).CycleSpace ≃ₗ[F₂] G.CycleSpace :=
  physicalMultigraphEquiv (realization G hshort)

@[simp] theorem realization_cycleRank : (realization G hshort).cycleRank = G.cycleRank :=
  (realizationCycleSpaceEquiv G hshort).finrank_eq

theorem realization_selectedDegree (x : G.EdgeWord) (v : G.Vertex) :
    (realization G hshort).selectedDegree x v = G.selectedDegree x v :=
  (asMultigraph_selectedDegree (realization G hshort) x v).symm

theorem realization_degree (v : G.Vertex) :
    (realization G hshort).degree v = G.degree v :=
  realization_selectedDegree G hshort (fun _ => 1) v

theorem realization_selectedGraph (x : G.EdgeWord) :
    (realization G hshort).selectedGraph x = G.selectedGraph x :=
  (asMultigraph_selectedGraph (realization G hshort) x).symm

theorem realization_toSimpleGraph :
    (realization G hshort).toSimpleGraph = G.toSimpleGraph := by
  ext u v
  constructor
  · rintro ⟨e, he, h⟩
    refine ⟨?_, e, h⟩
    exact (realization G hshort).toSimpleGraph.ne_of_adj ⟨e, he, h⟩
  · rintro ⟨_, e, h⟩
    exact ⟨e, one_ne_zero, h⟩

theorem realization_connected (hconn : G.toSimpleGraph.Connected) :
    (realization G hshort).IsConnected := by
  unfold PhysicalGraph.IsConnected
  rw [realization_toSimpleGraph]
  exact hconn

theorem realization_cubic (hcub : G.IsCubic) :
    ∀ v, (realization G hshort).degree v = 3 := by
  intro v
  rw [realization_degree]
  exact hcub v

theorem realization_isCycleWord_iff (x : G.EdgeWord) :
    (realization G hshort).IsCycleWord x ↔ G.IsCycleWord x :=
  (asMultigraph_isCycleWord_iff (realization G hshort) x).symm

def realizationCycleEquiv : (realization G hshort).CycleWord ≃
    {x : G.EdgeWord // G.IsCycleWord x} :=
  CubicReduction.physicalCycleEquiv (realization G hshort)

theorem realization_numCycles :
    Fintype.card (realization G hshort).CycleWord = G.numCycles :=
  (asMultigraph_numCycles (realization G hshort)).symm

@[simp] theorem realization_wordLength (x : G.EdgeWord) :
    (realization G hshort).wordLength x = G.wordLength x := rfl

theorem realization_cycleLength_lower_bound (D : ℕ)
    (hD : ¬ G.HasCycleShorterThan D) (C : (realization G hshort).CycleWord) :
    D ≤ (realization G hshort).wordLength C.1 := by
  by_contra h
  apply hD
  exact ⟨C.1, (realization_isCycleWord_iff G hshort C.1).1 C.2,
    Nat.lt_of_not_ge h⟩

/-- The ordinary-walk girth condition follows from the multigraph cycle predicate. -/
theorem realization_girthGreater (D : ℕ)
    (hD : ¬ G.HasCycleShorterThan (D + 1)) :
    Nonbacktracking.ShortWalks.GirthGreater (realization G hshort).toSimpleGraph D := by
  intro u p hp
  have hl := realization_cycleLength_lower_bound G hshort (D + 1) hD
    (Nonbacktracking.cycleWordOfWalk (realization G hshort) p hp)
  have heq := Nonbacktracking.cycleWordOfWalk_length (realization G hshort) p hp
  change (realization G hshort).wordLength
    (Nonbacktracking.cycleWordOfWalk (realization G hshort) p hp).1 = p.length at heq
  rw [heq] at hl
  omega

theorem realization_isForest_iff (x : G.EdgeWord) :
    (realization G hshort).IsForest x ↔ G.IsForestWord x := by
  unfold PhysicalGraph.IsForest
  rw [realization_selectedGraph]
  constructor
  · intro h
    exact ⟨fun e _ => noLoops_of_no_short_cycle G hshort e,
      fun e f _ _ hp => simple_of_no_short_cycle G hshort e f hp, h⟩
  · exact fun h => h.2.2

theorem realization_isLinearForest_iff (x : G.EdgeWord) :
    ((realization G hshort).IsForest x ∧
      ∀ v, (realization G hshort).selectedDegree x v ≤ 2) ↔ G.IsLinearForestWord x := by
  simp only [FiniteMultiGraph.IsLinearForestWord, realization_isForest_iff,
    realization_selectedDegree]
  rfl

/-- All multigraph region-forest probabilities are unchanged, with identical labels. -/
theorem realization_regionForestProbability (U : Finset G.Vertex) :
    (asMultigraph (realization G hshort)).regionForestProbability U =
      G.regionForestProbability U := rfl

/-- The same probability can use physical foresthood on the original retained labels. -/
theorem realization_regionForestProbability_eq (U : Finset G.Vertex) :
    G.regionForestProbability U =
      ((Finset.univ.filter fun x : (realization G hshort).CycleSpace =>
        (realization G hshort).IsForest
          (G.restrictEdges (G.internalEdges U) x.1)).card : ℝ) /
        (2 : ℝ) ^ (realization G hshort).cycleRank := by
  classical
  unfold FiniteMultiGraph.regionForestProbability
  rw [realization_cycleRank]
  congr 2
  apply congrArg Finset.card
  apply Finset.filter_congr
  intro x _
  exact (realization_isForest_iff G hshort _).symm

end Erdos1016.ExactMaximumSupport.LargeGirth
