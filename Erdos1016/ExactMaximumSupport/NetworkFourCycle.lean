import Erdos1016.ExactMaximum.NetJoin
import Erdos1016.ExactMaximum.NetBridge

set_option autoImplicit false
set_option maxHeartbeats 1500000

/-!
# Four distinct vertices joined cyclically

Choose one actual physical label for each adjacency. Existing pendant-path
and closing-edge constructions give a cycle using only those four labels.
Parallel ambient edges are allowed and remain distinct.
-/
noncomputable section
namespace Erdos1016.ExactMaximumSupport.NetworkFourCycle
open BoundaryTrace BoundaryTrace.Network

local instance fourCycleDecidable (p : Prop) : Decidable p := Classical.propDecidable p

variable {V E : Type*} [Fintype V] [Fintype E] (N : Network V E)

omit [Fintype V] [Fintype E] in
/-- A fresh endpoint distinguishes actual physical edge labels. -/
theorem edges_ne_of_fresh {e f : E} {a b c d : V}
    (he : N.Joins e a b) (hf : N.Joins f c d) (hca : c ≠ a) (hcb : c ≠ b) : e ≠ f := by
  intro hef
  have hc := hf.at_left
  rw [← hef] at hc
  rcases he with ⟨h1,h2⟩ | ⟨h1,h2⟩
  · rcases hc with h | h
    · exact hca (h.symm.trans h1)
    · exact hcb (h.symm.trans h2)
  · rcases hc with h | h
    · exact hcb (h.symm.trans h1)
    · exact hca (h.symm.trans h2)

/-- The selected four physical labels form an actual cycle. -/
theorem isCycleWord_four {a b c d : V} {e₁ e₂ e₃ e₄ : E}
    (hab : a ≠ b) (hac : a ≠ c) (had : a ≠ d)
    (hbc : b ≠ c) (hbd : b ≠ d) (_hcd : c ≠ d)
    (h₁ : N.Joins e₁ a b) (h₂ : N.Joins e₂ b c)
    (h₃ : N.Joins e₃ c d) (h₄ : N.Joins e₄ d a) :
    N.IsCycleWord (unitWord e₁ + unitWord e₂ + unitWord e₃ + unitWord e₄) := by
  have hP := (N.isPathWord_unitWord h₁).add_pendant h₂
    (N.deg_unitWord_of_joins h₁ hac.symm hbc.symm)
  have hd : N.deg (unitWord e₁ + unitWord e₂) d = 0 := by
    have h := N.deg_add_le (unitWord e₁) (unitWord e₂) d
    rw [N.deg_unitWord_of_joins h₁ had.symm hbd.symm,
      N.deg_unitWord_of_joins h₂ hbd.symm _hcd.symm] at h
    omega
  have hQ := hP.add_pendant h₃ hd
  have h14 := edges_ne_of_fresh N h₁ h₄ had.symm hbd.symm
  have h24 := edges_ne_of_fresh N h₂ h₄.symm hab hac
  have h34 := edges_ne_of_fresh N h₃ h₄.symm hac had
  apply hQ.add_closing h₄.symm
  simp [unitWord_apply,h14,h24,h34]

/-- A sum of four unit words uses at most the four displayed labels. -/
theorem support_four_subset (e₁ e₂ e₃ e₄ : E) :
    (Finset.univ.filter fun e =>
      (unitWord e₁ + unitWord e₂ + unitWord e₃ + unitWord e₄ : E → Bit) e ≠ 0) ⊆
        {e₁,e₂,e₃,e₄} := by
  intro e he
  by_contra hn
  have h1 : e₁ ≠ e := fun h => hn (by simp [h])
  have h2 : e₂ ≠ e := fun h => hn (by simp [h])
  have h3 : e₃ ≠ e := fun h => hn (by simp [h])
  have h4 : e₄ ≠ e := fun h => hn (by simp [h])
  have hh := (Finset.mem_filter.mp he).2
  simp [unitWord_apply,h1,h2,h3,h4] at hh

/-- No extra physical label is used by the constructed cycle. -/
theorem size_four_le (e₁ e₂ e₃ e₄ : E) :
    size (unitWord e₁ + unitWord e₂ + unitWord e₃ + unitWord e₄ : E → Bit) ≤ 4 := by
  have h := Finset.card_le_card (support_four_subset e₁ e₂ e₃ e₄)
  have h4 : ({e₁,e₂,e₃,e₄} : Finset E).card ≤ 4 := by
    calc
      _ ≤ ({e₂,e₃,e₄} : Finset E).card+1 := Finset.card_insert_le _ _
      _ ≤ (({e₃,e₄} : Finset E).card+1)+1 := Nat.add_le_add_right (Finset.card_insert_le _ _) 1
      _ ≤ 4 := by have h' := Finset.card_insert_le e₃ ({e₄} : Finset E); simp at h'; omega
  exact h.trans h4

omit [Fintype V] in
/-- The constructed cycle has no vertex outside the four specified vertices. -/
theorem vertices_four_subset {a b c d : V} {e₁ e₂ e₃ e₄ : E}
    (h₁ : N.Joins e₁ a b) (h₂ : N.Joins e₂ b c)
    (h₃ : N.Joins e₃ c d) (h₄ : N.Joins e₄ d a) :
    ∀ v, 0 < N.deg (unitWord e₁ + unitWord e₂ + unitWord e₃ + unitWord e₄) v →
      v ∈ ({a,b,c,d} : Finset V) := by
  intro v hv
  by_contra hn
  have ha : v ≠ a := fun h => hn (by simp [h])
  have hb : v ≠ b := fun h => hn (by simp [h])
  have hc : v ≠ c := fun h => hn (by simp [h])
  have hd : v ≠ d := fun h => hn (by simp [h])
  have h12 := N.deg_add_le (unitWord e₁) (unitWord e₂) v
  have h123 := N.deg_add_le (unitWord e₁ + unitWord e₂) (unitWord e₃) v
  have h1234 := N.deg_add_le (unitWord e₁ + unitWord e₂ + unitWord e₃) (unitWord e₄) v
  rw [N.deg_unitWord_of_joins h₁ ha hb,N.deg_unitWord_of_joins h₂ hb hc] at h12
  rw [N.deg_unitWord_of_joins h₃ hc hd] at h123
  rw [N.deg_unitWord_of_joins h₄ hd ha] at h1234
  omega

/-- Four distinct cyclically adjacent vertices supply a cycle of size at most four. -/
theorem exists_cycle_of_four_adj (a b c d : V)
    (hab : a ≠ b) (hac : a ≠ c) (had : a ≠ d)
    (hbc : b ≠ c) (hbd : b ≠ d) (hcd : c ≠ d)
    (hab' : N.graph.Adj a b) (hbc' : N.graph.Adj b c)
    (hcd' : N.graph.Adj c d) (hda' : N.graph.Adj d a) :
    ∃ z : N.Word, N.IsCycleWord z ∧ size z ≤ 4 ∧
      ∀ v, 0 < N.deg z v → v ∈ ({a,b,c,d} : Finset V) := by
  obtain ⟨e₁,h₁⟩ := hab'
  obtain ⟨e₂,h₂⟩ := hbc'
  obtain ⟨e₃,h₃⟩ := hcd'
  obtain ⟨e₄,h₄⟩ := hda'
  refine ⟨unitWord e₁ + unitWord e₂ + unitWord e₃ + unitWord e₄,
    isCycleWord_four N hab hac had hbc hbd hcd h₁ h₂ h₃ h₄,
    size_four_le e₁ e₂ e₃ e₄,vertices_four_subset N h₁ h₂ h₃ h₄⟩

end Erdos1016.ExactMaximumSupport.NetworkFourCycle
