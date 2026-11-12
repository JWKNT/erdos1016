import Erdos1016.ExactMaximum.NetJoin
import Erdos1016.ExactMaximum.NetBridge

set_option autoImplicit false

/-!
# Parallel labels and local simple degrees

Two distinct physical labels with the same ends form a cycle of length two.
At each vertex, the simple degree is at most the physical degree.
The degrees agree when labels joining that vertex to each neighbor are unique.
-/

noncomputable section
namespace Erdos1016.ExactMaximumSupport.NetworkParallel

open BoundaryTrace BoundaryTrace.Network BoundaryDecay

local instance networkParallelDecidable (p : Prop) : Decidable p :=
  Classical.propDecidable p

variable {V E : Type*} [Fintype V] [Fintype E]

/-- Parallel physical labels give a cycle supported at their two ends. -/
theorem exists_cycle_of_parallel (N : Network V E) {e f : E} {u v : V}
    (hef : e ≠ f) (he : N.Joins e u v) (hf : N.Joins f u v) :
    ∃ z : N.Word, N.IsCycleWord z ∧ size z ≤ 2 ∧
      ∀ w, 0 < N.deg z w → w = u ∨ w = v := by
  classical
  let z : N.Word := unitWord e + unitWord f
  have hz : N.IsCycleWord z := by
    apply (N.isPathWord_unitWord he).add_closing hf
    rw [unitWord_apply, if_neg hef]
  have hsize : size z = 2 := by
    have hs : (Finset.univ.filter fun g : E => z g ≠ 0) = {e, f} := by
      ext g
      by_cases hge : g = e
      · subst g
        simp [z, unitWord_apply, hef, Ne.symm hef]
      · by_cases hgf : g = f
        · subst g
          simp [z, unitWord_apply, hef, Ne.symm hef]
        · simp [z, unitWord_apply, hge, hgf, Ne.symm hge, Ne.symm hgf]
    simp [size, hs, hef]
  refine ⟨z, hz, hsize.le, ?_⟩
  intro w hw
  by_contra h
  have hwu : w ≠ u := by intro hwu; exact h (Or.inl hwu)
  have hwv : w ≠ v := by intro hwv; exact h (Or.inr hwv)
  have hd := N.deg_add_le (unitWord e) (unitWord f) w
  rw [N.deg_unitWord_of_joins he hwu hwv,
    N.deg_unitWord_of_joins hf hwu hwv] at hd
  change 0 < N.deg (unitWord e + unitWord f) w at hw
  omega

private def incidentLabels (N : Network V E) (v : V) : Finset E :=
  Finset.univ.filter fun e => N.src e = v ∨ N.dst e = v

private def otherEnd (N : Network V E) (v : V) (e : E) : V :=
  if N.src e = v then N.dst e else N.src e

omit [Fintype V] in
private theorem joins_otherEnd (N : Network V E) (v : V) {e : E}
    (he : e ∈ incidentLabels N v) : N.Joins e v (otherEnd N v e) := by
  have hi := (Finset.mem_filter.mp he).2
  by_cases hs : N.src e = v
  · exact Or.inl ⟨hs, by simp [otherEnd, hs]⟩
  · exact Or.inr ⟨by simp [otherEnd, hs], hi.resolve_left hs⟩

private theorem image_otherEnd (N : Network V E) (v : V) :
    (incidentLabels N v).image (otherEnd N v) = N.graph.neighborFinset v := by
  classical
  ext w
  rw [Finset.mem_image, SimpleGraph.mem_neighborFinset]
  constructor
  · rintro ⟨e, he, rfl⟩
    exact ⟨e, joins_otherEnd N v he⟩
  · rintro ⟨e, h | h⟩
    · refine ⟨e, ?_, ?_⟩
      · simp [incidentLabels, h.1]
      · simp [otherEnd, h.1, h.2]
    · refine ⟨e, ?_, ?_⟩
      · simp [incidentLabels, h.2]
      · have hne : N.src e ≠ v := by
          intro hs
          exact N.noLoops e (hs.trans h.2.symm)
        change (if N.src e = v then N.dst e else N.src e) = w
        rw [if_neg hne, h.1]

/-- Forgetting parallel labels cannot increase a vertex degree. -/
theorem graph_degree_le (N : Network V E) (v : V) :
    N.graph.degree v ≤ N.deg (fun _ => 1) v := by
  classical
  rw [← SimpleGraph.card_neighborFinset_eq_degree, ← image_otherEnd]
  simpa [incidentLabels, deg] using
    (Finset.card_image_le (s := incidentLabels N v) (f := otherEnd N v))

/-- Local label uniqueness suffices for equality of the two degree counts. -/
theorem degree_eq_of_unique_at (N : Network V E) (v : V)
    (hunique : ∀ e f w, N.Joins e v w → N.Joins f v w → e = f) :
    N.deg (fun _ => 1) v = N.graph.degree v := by
  classical
  have hinj : Set.InjOn (otherEnd N v) (incidentLabels N v) := by
    intro e he f hf h
    apply hunique e f (otherEnd N v e) (joins_otherEnd N v he)
    rw [h]
    exact joins_otherEnd N v hf
  have hc := Finset.card_image_of_injOn hinj
  rw [image_otherEnd, SimpleGraph.card_neighborFinset_eq_degree] at hc
  simpa [incidentLabels, deg] using hc.symm

end Erdos1016.ExactMaximumSupport.NetworkParallel
