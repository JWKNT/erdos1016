import Erdos1016.Cycles.Counting.CycleWordRunCount

set_option autoImplicit false

noncomputable section

namespace Erdos1016.Proof.CycleRootChoice

open Erdos1016.Nonbacktracking

variable (G : PhysicalGraph)

/-- Any vertex of a simple closed walk occurs in its support tail. The
initial vertex occurs again at the end, so it is included after dropping the
first support entry. -/
theorem supportTail_of_cycle {a : G.Vertex}
    (p : G.toSimpleGraph.Walk a a) (hp : p.IsCycle)
    (v : G.Vertex) (hv : v ∈ p.support) : v ∈ p.support.tail := by
  cases p with
  | nil => exact False.elim (hp.not_nil (by simp))
  | cons h t =>
      have hv' : v ∈ a :: t.support := by
        simpa [SimpleGraph.Walk.support_cons] using hv
      rcases List.mem_cons.mp hv' with heq | htail
      · subst v
        exact t.end_mem_support
      · exact htail

/-- A physical cycle support vertex can be selected as a root coordinate for
the chosen rooted walk representative. -/
theorem exists_rootChoice_at_vertex {ell : ℕ} {v : G.Vertex}
    (C : CycleWordsAtLength G ell)
    (hC : v ∈ BoundaryDecay.Cycle.vertices C.1) :
    ∃ x : RootChoices (chosenRootedSimpleCycle C).1.2, x.1 = v := by
  let p := (chosenRootedSimpleCycle C).1.2
  let hp := (chosenRootedSimpleCycle C).2.1
  have hvword : v ∈ G.usedVertices (walkWord G p) := by
    have hword : walkWord G p = C.1.1 := by
      exact congrArg Subtype.val (chosenRootedSimpleCycle_word C)
    change v ∈ G.usedVertices C.1.1 at hC
    rw [hword]
    exact hC
  have hsupport : v ∈ p.support :=
    (used_walkWord_iff G p hp v).1 hvword
  exact ⟨⟨v, supportTail_of_cycle G p hp v hsupport⟩, rfl⟩

end Erdos1016.Proof.CycleRootChoice

end
