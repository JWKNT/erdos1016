import Erdos1016.Graph.Suppression.MarkedCorridors
import Erdos1016.Nonbacktracking.Walks.RunGeometry
import Erdos1016.Nonbacktracking.Walks.CycleWords

set_option autoImplicit false

/-!
# Actual physical walks on ordered corridor steps

This file converts linked physical steps into ordinary walks. Distinct
physical edge labels exclude immediate reversal. The conversion preserves
the ordered edge list and its length, including returning corridors.
-/

noncomputable section

namespace Erdos1016.ExactMaximumSupport.LargeGirth.CorridorWalks

open FiniteMultiGraph Proof.SingleCorridorRoute
open Nonbacktracking

variable (G : PhysicalGraph)

abbrev Step := PathStep (routeGraph G)

def adjacent (s : Step G) : G.toSimpleGraph.Adj s.startVertex s.endVertex := by
  refine ⟨s.edge, one_ne_zero, ?_⟩
  rcases s.endpoints with h | h
  · exact Or.inl h
  · exact Or.inr ⟨h.2, h.1⟩

def linked (s t : Step G) : Prop := s.endVertex = t.startVertex

def finish : Step G → List (Step G) → G.Vertex
  | s, [] => s.endVertex
  | _, t :: l => finish t l

/-- Build the walk from the recorded ordered steps, without choosing paths. -/
def walk : (s : Step G) → (l : List (Step G)) →
    List.Chain' (linked G) (s :: l) →
      G.toSimpleGraph.Walk s.startVertex (finish G s l)
  | s, [], _ => .cons (adjacent G s) .nil
  | s, t :: l, h =>
    .cons (adjacent G s)
      ((walk t l (List.chain'_cons.mp h).2).copy (List.chain'_cons.mp h).1.symm rfl)

theorem walk_length (s : Step G) (l : List (Step G))
    (h : List.Chain' (linked G) (s :: l)) : (walk G s l h).length = l.length + 1 := by
  induction l generalizing s with
  | nil => rfl
  | cons t l ih => simp [walk, ih, Nat.add_assoc]

theorem walk_snd (s : Step G) (l : List (Step G))
    (h : List.Chain' (linked G) (s :: l)) : (walk G s l h).snd = s.endVertex := by
  cases l with
  | nil => rfl
  | cons t l =>
    change (SimpleGraph.Walk.cons (adjacent G s)
      ((walk G t l (List.chain'_cons.mp h).2).copy
        (List.chain'_cons.mp h).1.symm rfl)).snd = s.endVertex
    exact SimpleGraph.Walk.snd_cons _ _

theorem step_pair (s : Step G) : physicalPair G s.edge = s(s.startVertex, s.endVertex) := by
  rcases s.endpoints with ⟨hs, ht⟩ | ⟨hs, ht⟩
  · simp only [physicalPair, routeGraph] at hs ht ⊢
    rw [hs, ht]
  · simp only [physicalPair, routeGraph] at hs ht ⊢
    rw [hs, ht]
    exact Sym2.eq_swap

theorem walk_edges (s : Step G) (l : List (Step G))
    (h : List.Chain' (linked G) (s :: l)) :
    (walk G s l h).edges = (s :: l).map (fun t => physicalPair G t.edge) := by
  induction l generalizing s with
  | nil => simp [walk, step_pair]
  | cons t l ih =>
    have hm : s.endVertex = t.startVertex := (List.chain'_cons.mp h).1
    simp [walk, ih, step_pair, hm]

/-- Edge-distinct corridor steps are reduced even when the endpoints coincide. -/
theorem walk_reduced (s : Step G) (l : List (Step G))
    (h : List.Chain' (linked G) (s :: l))
    (hn : ((s :: l).map PathStep.edge).Nodup) : ShortWalks.Reduced (walk G s l h) := by
  induction l generalizing s with
  | nil => simp [walk, ShortWalks.Reduced]
  | cons t l ih =>
    have hnext := (List.chain'_cons.mp h).1
    have htail := (List.chain'_cons.mp h).2
    have hnodup := List.nodup_cons.mp hn
    have hne : s.edge ≠ t.edge := by
      intro he
      apply hnodup.1
      simp [he]
    refine ⟨(ShortWalks.reduced_copy _ _ _).2 (ih t htail hnodup.2), ?_⟩
    intro _ hreturn
    change ((walk G t l htail).copy hnext.symm rfl).snd = s.startVertex at hreturn
    rw [ShortWalks.snd_copy, walk_snd] at hreturn
    apply hne
    apply physicalPair_injective G
    rw [step_pair, step_pair, hreturn, ← hnext]
    exact Sym2.eq_swap

theorem finish_eq_of_getLast (s : Step G) (l : List (Step G)) (t : Step G)
    (h : (s :: l).getLast? = some t) : finish G s l = t.endVertex := by
  induction l generalizing s with
  | nil =>
    have hs : s = t := by simpa using h
    subst t
    rfl
  | cons u l ih =>
    exact ih u (by simpa using h)

/-- A linked list with distinct labels yields an actual reduced walk with
the specified endpoints and the same ordered physical edges. -/
theorem exists_walk_of_steps (l : List (Step G)) (hne : l ≠ [])
    (hchain : List.Chain' (linked G) l) (hn : (l.map PathStep.edge).Nodup)
    (u v : G.Vertex)
    (hstart : ∃ s, l.head? = some s ∧ s.startVertex = u)
    (hfinish : ∃ s, l.getLast? = some s ∧ s.endVertex = v) :
    ∃ p : G.toSimpleGraph.Walk u v,
      p.edges = l.map (fun s => physicalPair G s.edge) ∧
      p.length = l.length ∧ ShortWalks.Reduced p := by
  cases l with
  | nil => exact (hne rfl).elim
  | cons s l =>
    obtain ⟨s', hs', hu⟩ := hstart
    have hss : s = s' := by simpa using hs'
    subst s'
    obtain ⟨t, ht, hv⟩ := hfinish
    have hv' : finish G s l = v := (finish_eq_of_getLast G s l t ht).trans hv
    refine ⟨(walk G s l hchain).copy hu hv', ?_, ?_, ?_⟩
    · simpa only [SimpleGraph.Walk.edges_copy] using walk_edges G s l hchain
    · simpa only [SimpleGraph.Walk.length_copy, List.length_cons] using walk_length G s l hchain
    · exact (ShortWalks.reduced_copy _ _ _).2 (walk_reduced G s l hchain hn)

/-- The existing corridor certificate supplies every premise of the walk construction. -/
theorem exists_corridor_walk (C : Proof.PhysicalPartition.PhysicalCorridor G)
    (hne : C.edges ≠ [])
    (hdegree : Proof.DegreeTwoCorridorRoutes.InternalVerticesDegreeTwo C) :
    ∃ p : G.toSimpleGraph.Walk (corridorStart C) (corridorFinish C),
      p.edges = C.edges.map (physicalPair G) ∧
      p.length = C.edges.length ∧ ShortWalks.Reduced p := by
  let l := corridorSteps C
  have hl : l ≠ [] := Proof.DegreeTwoCorridorRoutes.corridorSteps_ne_nil C hne
  have hc : List.Chain' (linked G) l :=
    (Proof.DegreeTwoCorridorRoutes.corridorSteps_chain_of_internal_degree_two C hdegree).imp
      (fun _ _ h => h.1)
  have hn : (l.map PathStep.edge).Nodup := by
    rw [corridorSteps_edges]
    exact C.edges_nodup
  have hs : ∃ s, l.head? = some s ∧ s.startVertex = corridorStart C := by
    refine ⟨l.head hl, List.head?_eq_head hl, ?_⟩
    exact Proof.DegreeTwoCorridorRoutes.corridorSteps_head_start C hne
  have ht : ∃ s, l.getLast? = some s ∧ s.endVertex = corridorFinish C := by
    refine ⟨l.getLast hl, List.getLast?_eq_getLast_of_ne_nil hl, ?_⟩
    exact Proof.DegreeTwoCorridorRoutes.corridorSteps_last_end C hne
  obtain ⟨p, hp, hlen, hred⟩ := exists_walk_of_steps G l hl hc hn
    (corridorStart C) (corridorFinish C) hs ht
  refine ⟨p, ?_, ?_, hred⟩
  · rw [hp]
    calc
      l.map (fun s => physicalPair G s.edge) =
          (l.map PathStep.edge).map (physicalPair G) := by
        simp only [List.map_map, Function.comp_def]
      _ = C.edges.map (physicalPair G) := by rw [corridorSteps_edges]
  · simpa only [l, corridorSteps_length] using hlen

end Erdos1016.ExactMaximumSupport.LargeGirth.CorridorWalks
