import Erdos1016.ExactMaximumSupport.LargeGirth.SeparatorWitness

set_option autoImplicit false

/-!
# Deletion on the original vertex labels

Deleted vertices remain isolated. This convention lets the separator-chain
theorems use the original vertex sets without repeated subtype conversions.
All applications start outside the deleted set.
-/

noncomputable section
namespace Erdos1016.ExactMaximumSupport.LargeGirth

open SimpleGraph PolynomialBound.Separation
open PolynomialBound.ParallelLinks FiniteMultiGraph

variable {V : Type*}

/-- Delete all edges incident with `A`, retaining the original vertex type. -/
def deletedGraph (H : SimpleGraph V) (A : Set V) : SimpleGraph V where
  Adj a b := H.Adj a b ∧ a ∉ A ∧ b ∉ A
  symm := fun _ _ h => ⟨h.1.symm, h.2.2, h.2.1⟩
  loopless := fun a h => H.loopless a h.1

def deletedHom (H : SimpleGraph V) (A : Set V) : deletedGraph H A →g H where
  toFun := id
  map_rel' := fun h => h.1

/-- Lift an avoiding walk into the graph with the incident edges deleted. -/
def liftAvoidingWalk (H : SimpleGraph V) (A : Set V) {a b : V}
    (w : H.Walk a b) (hw : ∀ v ∈ w.support, v ∉ A) : (deletedGraph H A).Walk a b := by
  induction w with
  | nil => exact .nil
  | @cons a c b hac q ih =>
      have ha : a ∉ A := hw a (by simp)
      have hc : c ∉ A := hw c (by simp)
      exact .cons ⟨hac, ha, hc⟩ (ih fun v hv => hw v (by simp [hv]))

@[simp] theorem liftAvoidingWalk_support (H : SimpleGraph V) (A : Set V) {a b : V}
    (w : H.Walk a b) (hw : ∀ v ∈ w.support, v ∉ A) :
    (liftAvoidingWalk H A w hw).support = w.support := by
  induction w with
  | nil => rfl
  | @cons a c b hac q ih =>
      change a :: (liftAvoidingWalk H A q (fun v hv => hw v (by simp [hv]))).support = a :: q.support
      rw [ih]

theorem deleted_walk_avoids (H : SimpleGraph V) (A : Set V) {a b : V}
    (w : (deletedGraph H A).Walk a b) (ha : a ∉ A) :
    ∀ v ∈ w.support, v ∉ A := by
  induction w with
  | nil => intro v hv; simpa using (List.mem_singleton.mp hv ▸ ha)
  | @cons a c b hac q ih =>
      intro v hv
      rw [Walk.support_cons, List.mem_cons] at hv
      rcases hv with rfl | hv
      · exact ha
      · exact ih hac.2.2 v hv

/-- Avoiding `B` after deletion of `A` is exactly avoiding their union. -/
theorem avoidReach_deleted_iff (H : SimpleGraph V) (A B : Set V) {a b : V}
    (ha : a ∉ A) :
    AvoidReach (deletedGraph H A) B a b ↔ AvoidReach H (A ∪ B) a b := by
  constructor
  · rintro ⟨w, hw⟩
    refine ⟨w.map (deletedHom H A), ?_⟩
    intro v hv
    have hv' : v ∈ w.support := by
      rw [Walk.support_map, List.mem_map] at hv
      obtain ⟨v', hv', he⟩ := hv
      change v' = v at he
      exact he ▸ hv' 
    exact fun hh => hh.elim (deleted_walk_avoids H A w ha v hv') (hw v hv')
  · rintro ⟨w, hw⟩
    have hwA : ∀ v ∈ w.support, v ∉ A := fun v hv hA => hw v hv (Or.inl hA)
    refine ⟨liftAvoidingWalk H A w hwA, ?_⟩
    intro v hv hB
    rw [liftAvoidingWalk_support] at hv
    exact hw v hv (Or.inr hB)

/-- Reachability after deletion is the original avoiding-reach relation. -/
theorem reachable_deleted_iff (H : SimpleGraph V) (A : Set V) {a b : V}
    (ha : a ∉ A) : (deletedGraph H A).Reachable a b ↔ AvoidReach H A a b := by
  constructor
  · rintro ⟨w⟩
    have hh : AvoidReach (deletedGraph H A) ∅ a b := ⟨w, by simp⟩
    simpa using (avoidReach_deleted_iff H A ∅ ha).mp hh
  · rintro ⟨w, hw⟩
    exact ⟨liftAvoidingWalk H A w hw⟩

/-- Connected supports disjoint from the deleted set stay connected. -/
theorem connectedSet_deleted (H : SimpleGraph V) (A B : Set V)
    (hB : IsConnectedSet H B) (hd : Disjoint B A) :
    IsConnectedSet (deletedGraph H A) B := by
  intro a ha b hb
  obtain ⟨w, hw⟩ := hB a ha b hb
  have hwA : ∀ v ∈ w.support, v ∉ A :=
    fun v hv hvA => Set.disjoint_left.mp hd (hw v hv) hvA
  refine ⟨liftAvoidingWalk H A w hwA, ?_⟩
  intro v hv
  rw [liftAvoidingWalk_support] at hv
  exact hw v hv

/-- A good pair gives a separator in the actual graph with the first
support deleted, ready for the existing separator-chain theorem. -/
theorem goodTwoLink_deleted_separator {ι : Type*} (G : FiniteMultiGraph)
    (U : ι → Finset G.Vertex) (p : G.Vertex) (i j : ι)
    (hB : (G.toSimpleGraph.induce (↑(U j) : Set G.Vertex)).Connected)
    (hp : p ∉ U j) (hgood : goodTwoLink G U p i j = 1) :
    ∃ u ∈ cutOutsideVertices G (U i),
      (deletedGraph G.toSimpleGraph (↑(U i))).Reachable u p ∧
      Separates (deletedGraph G.toSimpleGraph (↑(U i))) (↑(U j)) u p := by
  obtain ⟨u, hu, huB, hup, hsep⟩ := goodTwoLink_separator G U p i j hB hgood
  refine ⟨u, hu, (reachable_deleted_iff _ _ hup.left_not_mem).mpr hup,
    huB, hp, ?_⟩
  intro h
  apply hsep
  simpa only [Finset.coe_union] using (avoidReach_deleted_iff _ _ _ hup.left_not_mem).mp h

end Erdos1016.ExactMaximumSupport.LargeGirth
