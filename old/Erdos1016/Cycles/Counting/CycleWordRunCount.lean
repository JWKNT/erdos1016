import Erdos1016.Cycles.Counting.ClosedRunCounting
import Erdos1016.Cycles.Geometry.CycleWalkExistence

set_option autoImplicit false

noncomputable section
namespace Erdos1016.Nonbacktracking
open BoundaryDecay

local instance cycleWordRunLowerBoundDecidable (p : Prop) : Decidable p :=
  Classical.propDecidable p

/-- Physical cycle words having a prescribed edge count. -/
abbrev CycleWordsAtLength (G : PhysicalGraph) (ℓ : ℕ) :=
  {C : G.CycleWord // BoundaryDecay.Cycle.length C = ℓ}

private theorem exists_cycleWord_representation {G : PhysicalGraph} {ℓ : ℕ}
    (C : CycleWordsAtLength G ℓ) :
    ∃ y : Σ a : G.Vertex, G.toSimpleGraph.Walk a a,
      ∃ hp : y.2.IsCycle, cycleWordOfWalk G y.2 hp = C.1 := by
  obtain ⟨u, p, hp, hword⟩ := exists_cycle_walk_of_cycleWord G C.1
  exact ⟨⟨u, p⟩, hp, hword⟩

private noncomputable def chosenCycleRepresentation {G : PhysicalGraph} {ℓ : ℕ}
    (C : CycleWordsAtLength G ℓ) :
    Σ a : G.Vertex, G.toSimpleGraph.Walk a a :=
  Classical.choose (exists_cycleWord_representation C)

private noncomputable def chosenCycleProof {G : PhysicalGraph} {ℓ : ℕ}
    (C : CycleWordsAtLength G ℓ) : (chosenCycleRepresentation C).2.IsCycle :=
  Classical.choose (Classical.choose_spec (exists_cycleWord_representation C))

private theorem chosenCycleWord_eq {G : PhysicalGraph} {ℓ : ℕ}
    (C : CycleWordsAtLength G ℓ) :
    cycleWordOfWalk G (chosenCycleRepresentation C).2 (chosenCycleProof C) = C.1 :=
  Classical.choose_spec (Classical.choose_spec (exists_cycleWord_representation C))



/-- Choose one rooted simple-walk representative for each physical cycle word. -/
noncomputable def chosenRootedSimpleCycle {G : PhysicalGraph} {ℓ : ℕ}
    (C : CycleWordsAtLength G ℓ) : RootedSimpleCycle G ℓ := by
  let y := chosenCycleRepresentation C
  let hp := chosenCycleProof C
  have hword := chosenCycleWord_eq C
  have hlen : y.2.length = ℓ := by
    calc
      y.2.length = BoundaryDecay.Cycle.length (cycleWordOfWalk G y.2 hp) :=
        (cycleWordOfWalk_length G y.2 hp).symm
      _ = BoundaryDecay.Cycle.length C.1 := congrArg BoundaryDecay.Cycle.length hword
      _ = ℓ := C.2
  exact ⟨y, hp, hlen⟩

theorem chosenRootedSimpleCycle_word {G : PhysicalGraph} {ℓ : ℕ}
    (C : CycleWordsAtLength G ℓ) :
    cycleWordOfWalk G (chosenRootedSimpleCycle C).1.2
      (chosenRootedSimpleCycle C).2.1 = C.1 := by
  simpa [chosenRootedSimpleCycle, chosenCycleRepresentation, chosenCycleProof] using
    chosenCycleWord_eq C









end Erdos1016.Nonbacktracking
end
