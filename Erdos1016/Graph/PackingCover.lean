import Erdos1016.Graph.Basic

set_option autoImplicit false
noncomputable section
open scoped BigOperators

namespace Erdos1016.PackingCover
variable {ι V : Type*} [DecidableEq ι] [DecidableEq V]
local instance (p : Prop) : Decidable p := Classical.propDecidable p

/-- A maximum disjoint subfamily meets every nonempty member of the family. -/
theorem exists_maximal_disjoint_family (s : Finset ι) (U : ι → Finset V)
    (hne : ∀ i ∈ s, (U i).Nonempty) :
    ∃ F ⊆ s, (∀ i ∈ F, ∀ j ∈ F, i ≠ j → Disjoint (U i) (U j)) ∧
      ∀ i ∈ s, ((F.biUnion U) ∩ U i).Nonempty := by
  let families := s.powerset.filter fun F =>
    ∀ i ∈ F, ∀ j ∈ F, i ≠ j → Disjoint (U i) (U j)
  have he : ∅ ∈ families := by simp [families]
  obtain ⟨F, hF, hmax⟩ := Finset.exists_max_image families Finset.card ⟨∅, he⟩
  have hF' : F ⊆ s ∧ (∀ i ∈ F, ∀ j ∈ F, i ≠ j → Disjoint (U i) (U j)) := by
    simpa only [families, Finset.mem_filter, Finset.mem_powerset] using hF
  have hsub : F ⊆ s := hF'.1
  have hdisj : ∀ i ∈ F, ∀ j ∈ F, i ≠ j → Disjoint (U i) (U j) :=
    hF'.2
  refine ⟨F, hsub, hdisj, ?_⟩
  intro j hjs
  by_contra hhit
  have hjF : j ∉ F := by
    intro hjF
    obtain ⟨v, hv⟩ := hne j hjs
    exact hhit ⟨v, Finset.mem_inter.mpr
      ⟨Finset.mem_biUnion.mpr ⟨j, hjF, hv⟩, hv⟩⟩
  have hd (i : ι) (hi : i ∈ F) : Disjoint (U j) (U i) := by
    apply Finset.disjoint_left.mpr
    intro v hvj hvi
    exact hhit ⟨v, Finset.mem_inter.mpr
      ⟨Finset.mem_biUnion.mpr ⟨i, hi, hvi⟩, hvj⟩⟩
  have hnew : insert j F ∈ families := by
    simp only [families, Finset.mem_filter, Finset.mem_powerset]
    refine ⟨Finset.insert_subset hjs hsub, ?_⟩
    intro a ha b hb hab
    rcases Finset.mem_insert.mp ha with ha' | ha'
    · subst a
      rcases Finset.mem_insert.mp hb with hb' | hb'
      · exact (hab hb'.symm).elim
      · exact hd b hb'
    · rcases Finset.mem_insert.mp hb with hb' | hb'
      · subst b
        exact (hd a ha').symm
      · exact hdisj a ha' b hb' hab
  have hh := hmax (insert j F) hnew
  rw [Finset.card_insert_of_not_mem hjF] at hh
  omega


/-- A packing bound turns a maximal family into a small hitting set. -/
theorem exists_hitting_set (s : Finset ι) (U : ι → Finset V) (d L : ℕ)
    (hne : ∀ i ∈ s, (U i).Nonempty)
    (hsize : ∀ i ∈ s, (U i).card ≤ L)
    (hpack : ∀ F ⊆ s, (∀ i ∈ F, ∀ j ∈ F, i ≠ j → Disjoint (U i) (U j)) →
      F.card ≤ d) :
    ∃ H : Finset V, H.card ≤ d * L ∧ ∀ i ∈ s, (H ∩ U i).Nonempty := by
  obtain ⟨F, hsub, hdisj, hhit⟩ := exists_maximal_disjoint_family s U hne
  refine ⟨F.biUnion U, ?_, hhit⟩
  calc
    (F.biUnion U).card ≤ ∑ i ∈ F, (U i).card := Finset.card_biUnion_le
    _ ≤ ∑ i ∈ F, L := Finset.sum_le_sum (fun i hi => hsize i (hsub hi))
    _ = F.card * L := by simp
    _ ≤ d * L := Nat.mul_le_mul_right L (hpack F hsub hdisj)

omit [DecidableEq ι] in
/-- Summing a nonnegative weight over a covered family is bounded by the
total vertex load of a hitting set. Multiple intersections only overcount. -/
theorem mass_le_vertex_load (s : Finset ι) (U : ι → Finset V) (H : Finset V)
    (a : ι → ℝ) (b : ℝ)
    (ha : ∀ i ∈ s, 0 ≤ a i)
    (hhit : ∀ i ∈ s, (H ∩ U i).Nonempty)
    (hload : ∀ v ∈ H, (∑ i ∈ s, if v ∈ U i then a i else 0) ≤ b) :
    (∑ i ∈ s, a i) ≤ H.card * b := by
  classical
  have hterm (i : ι) (hi : i ∈ s) :
      a i ≤ ∑ v ∈ H, if v ∈ U i then a i else 0 := by
    obtain ⟨v, hv⟩ := hhit i hi
    have hvH := (Finset.mem_inter.mp hv).1
    have hvU := (Finset.mem_inter.mp hv).2
    have ht := Finset.single_le_sum (f := fun w => if w ∈ U i then a i else 0)
      (fun w _ => by dsimp only; split_ifs <;> simp [ha i hi]) hvH
    simpa only [if_pos hvU] using ht
  calc
    _ ≤ ∑ i ∈ s, ∑ v ∈ H, if v ∈ U i then a i else 0 := Finset.sum_le_sum hterm
    _ = ∑ v ∈ H, ∑ i ∈ s, if v ∈ U i then a i else 0 := Finset.sum_comm
    _ ≤ ∑ _v ∈ H, b := Finset.sum_le_sum hload
    _ = _ := by simp

/-- A packing bound and a uniform per-vertex load bound give the aggregate
weight estimate used for exceptional cycle partners. -/
theorem mass_le_of_packing (s : Finset ι) (U : ι → Finset V) (d L : ℕ)
    (hne : ∀ i ∈ s, (U i).Nonempty)
    (hsize : ∀ i ∈ s, (U i).card ≤ L)
    (hpack : ∀ F ⊆ s, (∀ i ∈ F, ∀ j ∈ F, i ≠ j → Disjoint (U i) (U j)) → F.card ≤ d)
    (a : ι → ℝ) (b : ℝ) (hb : 0 ≤ b)
    (ha : ∀ i ∈ s, 0 ≤ a i)
    (hload : ∀ v, (∑ i ∈ s, if v ∈ U i then a i else 0) ≤ b) :
    (∑ i ∈ s, a i) ≤ (d : ℝ) * L * b := by
  obtain ⟨H, hH, hhit⟩ := exists_hitting_set s U d L hne hsize hpack
  have hcard : (H.card : ℝ) ≤ (d : ℝ) * L := by exact_mod_cast hH
  exact (mass_le_vertex_load s U H a b ha hhit (fun v _ => hload v)).trans
    (mul_le_mul_of_nonneg_right hcard hb)

end Erdos1016.PackingCover
