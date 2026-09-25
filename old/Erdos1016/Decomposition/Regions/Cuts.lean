import Erdos1016.Decomposition.Regions.Basic

set_option autoImplicit false

/-! # Literal original-cut accounting and cut characterization of connectivity -/

noncomputable section
open scoped BigOperators
namespace Erdos1016.SafeCore
local instance instSafeCoreCutsPropDecidable (p : Prop) : Decidable p := Classical.propDecidable p
variable (G : PhysicalGraph)

theorem crossing_nonempty_iff (S T : Finset G.Vertex) :
    (crossing G S T).Nonempty ↔
      ∃ u ∈ S, ∃ v ∈ T, G.toSimpleGraph.Adj u v := by
  constructor
  · rintro ⟨e, he⟩
    rcases (mem_crossing G S T e).1 he with h | h
    · exact ⟨G.src e, h.1, G.dst e, h.2,
        ⟨e, one_ne_zero, Or.inl ⟨rfl, rfl⟩⟩⟩
    · exact ⟨G.dst e, h.2, G.src e, h.1,
        ⟨e, one_ne_zero, Or.inr ⟨rfl, rfl⟩⟩⟩
  · rintro ⟨u, hu, v, hv, e, _, h | h⟩
    · exact ⟨e, (mem_crossing G S T e).2
        (Or.inl ⟨h.1.symm ▸ hu, h.2.symm ▸ hv⟩)⟩
    · exact ⟨e, (mem_crossing G S T e).2
        (Or.inr ⟨h.1.symm ▸ hv, h.2.symm ▸ hu⟩)⟩

theorem crossing_mono {S S' T T' : Finset G.Vertex}
    (hS : S ⊆ S') (hT : T ⊆ T') : crossing G S T ⊆ crossing G S' T' := by
  intro e he
  rcases (mem_crossing G S T e).1 he with h | h
  · exact (mem_crossing G S' T' e).2 (Or.inl ⟨hS h.1, hT h.2⟩)
  · exact (mem_crossing G S' T' e).2 (Or.inr ⟨hT h.1, hS h.2⟩)





/-- Splitting an induced region charges both copies of every new cut edge. -/
theorem cutSize_union (S T : Finset G.Vertex) (hST : Disjoint S T) :
    cutSize G S + cutSize G T = cutSize G (S ∪ T) + 2 * crossSize G S T := by
  have hdis : ∀ v, ¬(v ∈ S ∧ v ∈ T) := fun v h =>
    Finset.disjoint_left.1 hST h.1 h.2
  have point (e : G.Edge) :
      (if e ∈ ownerCut G S then 1 else 0) +
        (if e ∈ ownerCut G T then 1 else 0) =
      (if e ∈ ownerCut G (S ∪ T) then 1 else 0) +
        2 * (if e ∈ crossing G S T then 1 else 0) := by
    simp only [mem_ownerCut, mem_crossing, Finset.mem_union]
    by_cases hs : G.src e ∈ S <;> by_cases ht : G.src e ∈ T <;>
      by_cases ds : G.dst e ∈ S <;> by_cases dt : G.dst e ∈ T
    all_goals
      have hsrc := hdis (G.src e)
      have hdst := hdis (G.dst e)
      simp_all
  have hsum := congrArg (fun f : G.Edge → ℕ => ∑ e, f e) (funext point)
  have hcard (A : Finset G.Edge) :
      A.card = ∑ e, (if e ∈ A then 1 else 0) := by
    classical
    calc
      A.card = ∑ e ∈ A, (1 : ℕ) := by
        simp
      _ = ∑ e, (if e ∈ A then 1 else 0) := by
        symm
        rw [Finset.sum_ite_mem Finset.univ A]
        simp
  calc
    cutSize G S + cutSize G T =
        (∑ e, (if e ∈ ownerCut G S then 1 else 0)) +
        ∑ e, (if e ∈ ownerCut G T then 1 else 0) := by
      change (ownerCut G S).card + (ownerCut G T).card = _
      rw [hcard, hcard]
    _ = ∑ e, ((if e ∈ ownerCut G S then 1 else 0) +
        (if e ∈ ownerCut G T then 1 else 0)) := by
      rw [← Finset.sum_add_distrib]
    _ = ∑ e, ((if e ∈ ownerCut G (S ∪ T) then 1 else 0) +
        2 * (if e ∈ crossing G S T then 1 else 0)) := hsum
    _ = cutSize G (S ∪ T) + 2 * crossSize G S T := by
      rw [cutSize, crossSize, hcard, hcard]
      rw [Finset.sum_add_distrib]
      congr 1
      exact (Finset.mul_sum Finset.univ
        (fun e : G.Edge => if e ∈ crossing G S T then 1 else 0) 2).symm

/-- A child's original cut is its sibling cut plus its original outside cut. -/
theorem child_cut_partition (S T : Finset G.Vertex) (hST : Disjoint S T) :
    ownerCut G T = crossing G S T ∪ crossing G T (S ∪ T)ᶜ := by
  have hdis : ∀ v, ¬(v ∈ S ∧ v ∈ T) := fun v h =>
    Finset.disjoint_left.1 hST h.1 h.2
  ext e
  simp only [mem_ownerCut, mem_crossing, Finset.mem_union, Finset.mem_compl]
  by_cases hs : G.src e ∈ S <;> by_cases ht : G.src e ∈ T <;>
    by_cases ds : G.dst e ∈ S <;> by_cases dt : G.dst e ∈ T
  all_goals
    have hsrc := hdis (G.src e)
    have hdst := hdis (G.dst e)
    simp_all

theorem child_cut_eq_cross_of_no_outside (S T : Finset G.Vertex)
    (hST : Disjoint S T) (hn : crossing G T (S ∪ T)ᶜ = ∅) :
    cutSize G T = crossSize G S T := by
  unfold cutSize crossSize
  rw [child_cut_partition G S T hST, hn, Finset.union_empty]

/-- The cubic degree budget counts actual owner incidences. -/
theorem degree_eq_endpoint_sum (v : G.Vertex) :
    G.degree v = ∑ e, ((if G.src e = v then 1 else 0) +
      (if G.dst e = v then 1 else 0)) := by
  have hp (e : G.Edge) :
      (if G.incident e v then 1 else 0) =
        (if G.src e = v then 1 else 0) + (if G.dst e = v then 1 else 0) := by
    by_cases hs : G.src e = v <;> by_cases hd : G.dst e = v
    · exact False.elim (G.noLoops e (hs.trans hd.symm))
    · simp [PhysicalGraph.incident, hs, hd]
    · simp [PhysicalGraph.incident, hs, hd]
    · simp [PhysicalGraph.incident, hs, hd]
  simp only [PhysicalGraph.degree, PhysicalGraph.selectedDegree,
    one_ne_zero, true_and, Finset.card_eq_sum_ones, Finset.sum_filter]
  exact Finset.sum_congr rfl fun e _ => by simpa [one_ne_zero] using hp e

theorem degree_sum_region (S : Finset G.Vertex) :
    ∑ v ∈ S, G.degree v = 2 * (internalEdges G S).card + cutSize G S := by
  simp_rw [degree_eq_endpoint_sum G]
  rw [Finset.sum_comm]
  have hp (e : G.Edge) :
      (if G.src e ∈ S then 1 else 0) + (if G.dst e ∈ S then 1 else 0) =
      2 * (if G.src e ∈ S ∧ G.dst e ∈ S then 1 else 0) +
        (if (G.src e ∈ S ∧ G.dst e ∉ S) ∨
          (G.src e ∉ S ∧ G.dst e ∈ S) then 1 else 0) := by
    by_cases hs : G.src e ∈ S <;> by_cases hd : G.dst e ∈ S <;> simp [hs, hd]
  calc
    (∑ e, ∑ v ∈ S, ((if G.src e = v then 1 else 0) +
        (if G.dst e = v then 1 else 0))) =
        ∑ e, ((if G.src e ∈ S then 1 else 0) + (if G.dst e ∈ S then 1 else 0)) := by
      apply Finset.sum_congr rfl
      intro e _
      simp [Finset.sum_add_distrib, eq_comm]
    _ = ∑ e, (2 * (if G.src e ∈ S ∧ G.dst e ∈ S then 1 else 0) +
        (if (G.src e ∈ S ∧ G.dst e ∉ S) ∨
          (G.src e ∉ S ∧ G.dst e ∈ S) then 1 else 0)) :=
      Finset.sum_congr rfl fun e _ => hp e
    _ = _ := by
      simp only [internalEdges, cutSize, Finset.card_eq_sum_ones, ownerCut,
        crossing, Finset.sum_filter, Finset.mem_filter, Finset.mem_univ,
        true_and, Finset.sum_add_distrib, Finset.mul_sum, Finset.mem_compl]

theorem cubic_cut_identity (S : Finset G.Vertex) (hc : ∀ v ∈ S, G.degree v = 3) :
    3 * S.card = 2 * (internalEdges G S).card + cutSize G S := by
  have h := degree_sum_region G S
  have hs : (∑ v ∈ S, G.degree v) = 3 * S.card := by
    calc
      (∑ v ∈ S, G.degree v) = ∑ _v ∈ S, 3 := Finset.sum_congr rfl hc
      _ = 3 * S.card := by simp [Nat.mul_comm]
  rwa [hs] at h

/-- Connectedness is equivalent to positivity of every nontrivial internal cut. -/
theorem connectedRegion_iff_cuts (U : Finset G.Vertex) :
    ConnectedRegion G U ↔ U.Nonempty ∧
      ∀ A ⊆ U, A.Nonempty → (U \ A).Nonempty → (crossing G A (U \ A)).Nonempty := by
  constructor
  · rintro ⟨hne, hconn⟩
    refine ⟨hne, ?_⟩
    intro A hAU hA hUA
    obtain ⟨u, hu⟩ := hA
    obtain ⟨v, hv⟩ := hUA
    by_contra hcut
    have hclosed : ClosedIn G U A := by
      intro x hx y hy hxy
      by_contra hya
      exact hcut ((crossing_nonempty_iff G A (U \ A)).2
        ⟨x, hx, y, Finset.mem_sdiff.2 ⟨hy, hya⟩, hxy⟩)
    have hp := (hconn u (hAU hu) v (Finset.mem_sdiff.1 hv).1).restrict hu hclosed
    exact (Finset.mem_sdiff.1 hv).2 hp.target
  · rintro ⟨hne, hcuts⟩
    refine ⟨hne, ?_⟩
    intro u hu v hv
    by_contra hp
    let A := reachSet G U u
    have hA : A.Nonempty := ⟨u, self_mem_reachSet G hu⟩
    have hUA : (U \ A).Nonempty := by
      refine ⟨v, Finset.mem_sdiff.2 ⟨hv, ?_⟩⟩
      intro h
      exact hp ((mem_reachSet G U u v).1 h).2
    obtain ⟨x, hx, y, hy, hxy⟩ := (crossing_nonempty_iff G A (U \ A)).1
      (hcuts A (reachSet_subset G U u) hA hUA)
    exact (Finset.mem_sdiff.1 hy).2
      (reachSet_closed G U u x hx y (Finset.mem_sdiff.1 hy).1 hxy)

@[simp] theorem connectedRegion_singleton (v : G.Vertex) : ConnectedRegion G {v} := by
  refine ⟨⟨v, Finset.mem_singleton_self _⟩, ?_⟩
  intro u hu w hw
  have hu' : u = v := by simpa using hu
  have hw' : w = v := by simpa using hw
  subst u
  subst w
  exact .refl _ (Finset.mem_singleton_self _)

theorem connected_union_of_edge {S T : Finset G.Vertex}
    (hS : ConnectedRegion G S) (hT : ConnectedRegion G T)
    (he : (crossing G S T).Nonempty) : ConnectedRegion G (S ∪ T) := by
  obtain ⟨s, hs, t, ht, hst⟩ := (crossing_nonempty_iff G S T).1 he
  have hsU : s ∈ S ∪ T := Finset.mem_union_left _ hs
  have htU : t ∈ S ∪ T := Finset.mem_union_right _ ht
  have root : ∀ v ∈ S ∪ T, InReach G (S ∪ T) s v := by
    intro v hv
    rcases Finset.mem_union.1 hv with hv | hv
    · exact (hS.2 s hs v hv).mono Finset.subset_union_left
    · exact (InReach.edge hsU htU hst).trans
        ((hT.2 t ht v hv).mono Finset.subset_union_right)
  exact ⟨⟨s, hsU⟩, fun u hu v hv => (root u hu).symm.trans (root v hv)⟩





/-- Every proper nonempty region of a connected owner has a nonempty actual cut. -/
theorem ownerCut_nonempty (hG : G.IsConnected) {S : Finset G.Vertex}
    (hne : S.Nonempty) (hproper : Sᶜ.Nonempty) : (ownerCut G S).Nonempty := by
  have hu : ConnectedRegion G Finset.univ := by
    change G.toSimpleGraph.Connected at hG
    refine ⟨?_, ?_⟩
    · obtain ⟨v⟩ := hG.nonempty
      exact ⟨v, Finset.mem_univ _⟩
    · intro u _ v _
      obtain ⟨p⟩ := hG u v
      induction p with
      | nil => exact .refl _ (Finset.mem_univ _)
      | @cons u v w huv p ih =>
          exact (InReach.edge (Finset.mem_univ _) (Finset.mem_univ _) huv).trans
            (ih (Finset.mem_univ _) (Finset.mem_univ _))
  have h := (connectedRegion_iff_cuts G _).1 hu
  have hproper' : (Finset.univ \ S).Nonempty := by simpa using hproper
  simpa [ownerCut] using h.2 S (Finset.subset_univ _) hne hproper'

end Erdos1016.SafeCore
