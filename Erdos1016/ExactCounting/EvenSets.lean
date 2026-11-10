import Erdos1016.ExactCounting.EdgeParity

set_option autoImplicit false

/-!
# Even edge sets of acyclic and connected graphs

An acyclic graph has no nonempty even edge set. The proof uses a bridge: an
even set crosses every cut an even number of times, and a bridge is the only
edge of its cut.

A connected graph with `r + n = m + 1`, where `n` is the number of vertices
and `m` is the number of edges, has at most `2^r` even edge sets. The proof
fixes a spanning tree: an even set is determined by its edges outside the tree.
-/

namespace Erdos1016.ExactCounting

open Finset

variable {V : Type*} [Fintype V] [DecidableEq V]

omit [Fintype V] in
/-- The sum of the parities over a vertex set counts the edge ends in this set. -/
theorem sum_par_eq (X : Finset (Sym2 V)) (R : Finset V) :
    ∑ x ∈ R, par X x = ∑ e ∈ X, ((R.filter fun x => x ∈ e).card : ZMod 2) := by
  unfold par
  simp only [Finset.card_filter]
  push_cast
  rw [Finset.sum_comm]

/-- An acyclic graph has no nonempty even edge set. -/
theorem eq_empty_of_subset_acyclic {T : SimpleGraph V} (hT : T.IsAcyclic)
    {Y : Finset (Sym2 V)} (hY : ∀ e ∈ Y, e ∈ T.edgeSet) (hev : IsEven Y) : Y = ∅ := by
  classical
  by_contra hne
  obtain ⟨e, he⟩ := Finset.nonempty_iff_ne_empty.2 hne
  revert he
  refine Sym2.ind (fun a b => ?_) e
  intro he
  have hbridge := (SimpleGraph.isAcyclic_iff_forall_edge_isBridge.1 hT) (hY _ he)
  rw [SimpleGraph.isBridge_iff] at hbridge
  obtain ⟨_, hnr⟩ := hbridge
  let R : Finset V := Finset.univ.filter fun x =>
    (T \ SimpleGraph.fromEdgeSet {s(a, b)}).Reachable a x
  have hR : ∀ x, x ∈ R ↔ (T \ SimpleGraph.fromEdgeSet {s(a, b)}).Reachable a x := by
    intro x
    simp [R]
  have haR : a ∈ R := (hR a).2 (SimpleGraph.Reachable.refl a)
  have hbR : b ∉ R := fun h => hnr ((hR b).1 h)
  have hsum : ∑ x ∈ R, par Y x = 0 := Finset.sum_eq_zero fun x _ => hev x
  rw [sum_par_eq] at hsum
  have hterm : ∀ f ∈ Y, f ≠ s(a, b) → ((R.filter fun x => x ∈ f).card : ZMod 2) = 0 := by
    intro f
    refine Sym2.ind (fun x y => ?_) f
    intro hf hfne
    have hxy : T.Adj x y := hY _ hf
    have hadj : (T \ SimpleGraph.fromEdgeSet {s(a, b)}).Adj x y := by
      rw [SimpleGraph.sdiff_adj]
      refine ⟨hxy, ?_⟩
      rw [SimpleGraph.fromEdgeSet_adj]
      rintro ⟨h1, _⟩
      exact hfne (Set.mem_singleton_iff.1 h1)
    have hiff : x ∈ R ↔ y ∈ R := by
      rw [hR, hR]
      exact ⟨fun h => h.trans hadj.reachable, fun h => h.trans hadj.symm.reachable⟩
    by_cases hx : x ∈ R
    · have hy := hiff.1 hx
      have hfil : (R.filter fun z => z ∈ s(x, y)) = {x, y} := by
        ext z
        simp only [Finset.mem_filter, Sym2.mem_iff, Finset.mem_insert, Finset.mem_singleton]
        constructor
        · exact fun h => h.2
        · rintro (rfl | rfl)
          · exact ⟨hx, Or.inl rfl⟩
          · exact ⟨hy, Or.inr rfl⟩
      rw [hfil, Finset.card_pair hxy.ne]
      decide
    · have hy : y ∉ R := fun h => hx (hiff.2 h)
      have hfil : (R.filter fun z => z ∈ s(x, y)) = ∅ := by
        ext z
        simp only [Finset.mem_filter, Sym2.mem_iff, Finset.not_mem_empty, iff_false, not_and]
        rintro hz (rfl | rfl)
        · exact hx hz
        · exact hy hz
      rw [hfil]
      simp
  have hmain : ((R.filter fun x => x ∈ s(a, b)).card : ZMod 2) = 1 := by
    have hfil : (R.filter fun z => z ∈ s(a, b)) = {a} := by
      ext z
      simp only [Finset.mem_filter, Sym2.mem_iff, Finset.mem_singleton]
      constructor
      · rintro ⟨hz, rfl | rfl⟩
        · rfl
        · exact absurd hz hbR
      · rintro rfl
        exact ⟨haR, Or.inl rfl⟩
    rw [hfil]
    simp
  rw [← Finset.add_sum_erase Y _ he, hmain,
    Finset.sum_eq_zero (fun f hf =>
      hterm f (Finset.mem_of_mem_erase hf) (Finset.ne_of_mem_erase hf)), add_zero] at hsum
  exact one_ne_zero hsum

/-- A connected graph with `r + n = m + 1` has at most `2^r` even edge sets. -/
theorem card_even_le_two_pow {G : SimpleGraph V} (hG : G.Connected) (E : Finset (Sym2 V))
    (hE : ∀ e, e ∈ E ↔ e ∈ G.edgeSet) (r : ℕ) (hr : r + Fintype.card V = E.card + 1) :
    (E.powerset.filter IsEven).card ≤ 2 ^ r := by
  classical
  obtain ⟨T, hTG, hT⟩ := hG.exists_isTree_le
  let TF : Finset (Sym2 V) := E.filter fun e => e ∈ T.edgeSet
  have hTF : TF = T.edgeFinset := by
    ext e
    simp only [TF, Finset.mem_filter, SimpleGraph.mem_edgeFinset, hE]
    exact ⟨fun h => h.2, fun h => ⟨SimpleGraph.edgeSet_subset_edgeSet.2 hTG h, h⟩⟩
  have hTFcard : TF.card + 1 = Fintype.card V := by
    rw [hTF]
    exact hT.card_edgeFinset
  have hsub : TF ⊆ E := Finset.filter_subset _ _
  have hcard : (E \ TF).card = r := by
    rw [Finset.card_sdiff hsub]
    omega
  rw [← hcard, ← Finset.card_powerset]
  apply Finset.card_le_card_of_injOn (fun X => X \ TF)
  · intro X hX
    have hX' := (Finset.mem_filter.1 (Finset.mem_coe.1 hX)).1
    exact Finset.mem_coe.2 (Finset.mem_powerset.2
      (Finset.sdiff_subset_sdiff (Finset.mem_powerset.1 hX') (Finset.Subset.refl _)))
  · intro X hX X' hX' hEq
    have hXe := (Finset.mem_filter.1 (Finset.mem_coe.1 hX)).2
    have hXe' := (Finset.mem_filter.1 (Finset.mem_coe.1 hX')).2
    have hEq' : X \ TF = X' \ TF := hEq
    have hsym : symmDiff X X' = ∅ := by
      apply eq_empty_of_subset_acyclic hT.IsAcyclic _ (hXe.symmDiff hXe')
      intro e he
      have heTF : e ∈ TF := by
        by_contra hnot
        have h1 : e ∈ X ↔ e ∈ X' := by
          have h2 : e ∈ X \ TF ↔ e ∈ X' \ TF := by rw [hEq']
          simpa [Finset.mem_sdiff, hnot] using h2
        rw [Finset.mem_symmDiff] at he
        rcases he with ⟨h, h'⟩ | ⟨h, h'⟩
        · exact h' (h1.1 h)
        · exact h' (h1.2 h)
      exact (Finset.mem_filter.1 heTF).2
    exact symmDiff_eq_bot.1 hsym

end Erdos1016.ExactCounting
