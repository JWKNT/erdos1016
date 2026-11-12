import Erdos1016.ExactMaximumSupport.NetworkPathInterior

set_option autoImplicit false
set_option maxHeartbeats 2000000

/-!
# Exact segments of an ordered physical path

Prefix indicators retain the original physical labels. Their boundaries telescope.
Each nonempty interval is an actual path because it is a subword of the original path.
-/
noncomputable section
namespace Erdos1016.ExactMaximumSupport.NetworkPathOrder.Order
open BoundaryTrace BoundaryTrace.Network BoundaryDecay
local instance pathSegmentDecidable (p : Prop) : Decidable p := Classical.propDecidable p
variable {V E : Type*} [Fintype V] [Fintype E] {N : Network V E}
variable {s t : V} {P : N.Word} (O : NetworkPathOrder.Order N s t P)

/-- The physical word before a given position. -/
def prefixWord (k : ℕ) : N.Word := fun e =>
  if ∃ h : Fin (O.innerCount+1), h.val < k ∧ O.edge h = e then 1 else 0

omit [Fintype V] [Fintype E] in
@[simp] theorem prefix_selected (k : ℕ) (e : E) :
    O.prefixWord k e ≠ 0 ↔ ∃ h : Fin (O.innerCount+1), h.val < k ∧ O.edge h = e := by
  simp [prefixWord]

omit [Fintype V] [Fintype E] in
@[simp] theorem prefix_zero : O.prefixWord 0 = 0 := by
  funext e
  simp [prefixWord]

omit [Fintype V] in
/-- A prefix grows by its next original physical label. -/
theorem prefix_succ (k : ℕ) (hk : k < O.innerCount+1) :
    O.prefixWord (k+1) = O.prefixWord k + unitWord (O.edge ⟨k,hk⟩) := by
  funext e
  by_cases h : O.edge ⟨k,hk⟩ = e
  · have hsmall : ¬ ∃ j : Fin (O.innerCount+1), j.val < k ∧ O.edge j = e := by
      rintro ⟨j,hj,hje⟩
      have heq := O.edge_injective (hje.trans h.symm)
      have hv := congrArg Fin.val heq
      change j.val = k at hv
      omega
    have hlarge : ∃ j : Fin (O.innerCount+1), j.val < k+1 ∧ O.edge j = e :=
      ⟨⟨k,hk⟩,Nat.lt_succ_self k,h⟩
    simp [prefixWord,hsmall,hlarge,Pi.add_apply,unitWord_apply,h]
  · have hex : (∃ j : Fin (O.innerCount+1), j.val < k+1 ∧ O.edge j = e) ↔
        ∃ j : Fin (O.innerCount+1), j.val < k ∧ O.edge j = e := by
      constructor
      · rintro ⟨j,hj,hje⟩
        refine ⟨j,?_,hje⟩
        have hne : j.val ≠ k := by
          intro heq
          have heq' : j = ⟨k,hk⟩ := Fin.ext heq
          exact h (heq' ▸ hje)
        omega
      · rintro ⟨j,hj,hje⟩
        exact ⟨j,by omega,hje⟩
    simp [prefixWord,hex,Pi.add_apply,unitWord_apply,h]

/-- The boundary of a prefix consists of its two endpoints. -/
theorem prefix_boundary (k : ℕ) (hk : k < O.innerCount+2) :
    N.boundary (O.prefixWord k) = unitWord (O.vertex 0) + unitWord (O.vertex ⟨k,hk⟩) := by
  induction k with
  | zero =>
    rw [O.prefix_zero,map_zero]
    change 0 = unitWord (O.vertex 0) + unitWord (O.vertex 0)
    rw [word_add_self]
  | succ k ih =>
    have hk' : k < O.innerCount+1 := by omega
    have hk'' : k < O.innerCount+2 := by omega
    rw [O.prefix_succ k hk',map_add,ih hk'',N.boundary_unitWord_of_joins (O.joins ⟨k,hk'⟩)]
    change (unitWord (O.vertex 0) + unitWord (O.vertex ⟨k,hk''⟩)) +
      (unitWord (O.vertex ⟨k,hk''⟩) + unitWord (O.vertex ⟨k+1,hk⟩)) = _
    rw [add_assoc,← add_assoc (unitWord (O.vertex ⟨k,hk''⟩)),word_add_self,zero_add]

/-- The physical word on the half-open interval of label positions. -/
def segment (i j : Fin (O.innerCount+2)) : N.Word := O.prefixWord i.val + O.prefixWord j.val

omit [Fintype V] [Fintype E] in
/-- Exactly the labels between the two positions are selected. -/
theorem segment_selected (i j : Fin (O.innerCount+2)) (hij : i ≤ j) (e : E) :
    O.segment i j e ≠ 0 ↔
      ∃ h : Fin (O.innerCount+1), i.val ≤ h.val ∧ h.val < j.val ∧ O.edge h = e := by
  by_cases hi : ∃ h : Fin (O.innerCount+1), h.val < i.val ∧ O.edge h = e
  · obtain ⟨h,hhi,hhe⟩ := hi
    have hj : ∃ k : Fin (O.innerCount+1), k.val < j.val ∧ O.edge k = e :=
      ⟨h,lt_of_lt_of_le hhi hij,hhe⟩
    have hnone : ¬ ∃ k : Fin (O.innerCount+1), i.val ≤ k.val ∧ k.val < j.val ∧ O.edge k = e := by
      rintro ⟨k,hik,hkj,hke⟩
      have hkh := O.edge_injective (hke.trans hhe.symm)
      subst k
      omega
    have hi : ∃ k : Fin (O.innerCount+1), k.val < i.val ∧ O.edge k = e := ⟨h,hhi,hhe⟩
    simp only [segment,Pi.add_apply,prefixWord,if_pos hi,if_pos hj,bit_add_self,ne_eq,not_true_eq_false]
    exact iff_of_false False.elim hnone
  · have hx : (∃ h : Fin (O.innerCount+1), h.val < j.val ∧ O.edge h = e) ↔
        ∃ h : Fin (O.innerCount+1), i.val ≤ h.val ∧ h.val < j.val ∧ O.edge h = e := by
      constructor
      · rintro ⟨h,hh,hhe⟩
        refine ⟨h,?_,hh,hhe⟩
        exact Nat.le_of_not_lt (fun hlt => hi ⟨h,hlt,hhe⟩)
      · rintro ⟨h,_,hh,hhe⟩
        exact ⟨h,hh,hhe⟩
    simp only [segment,Pi.add_apply,prefixWord,if_neg hi,zero_add]
    simpa using hx

omit [Fintype V] [Fintype E] in
/-- A segment retains only labels selected by the original path. -/
theorem segment_subword (i j : Fin (O.innerCount+2)) (hij : i ≤ j) :
    N.IsSubword (O.segment i j) P := by
  intro e he
  obtain ⟨h,_,_,hh⟩ := (O.segment_selected i j hij e).mp he
  exact (O.edge_support e).mpr ⟨h,hh⟩

/-- The exact two-endpoint boundary of a segment. -/
theorem segment_boundary (i j : Fin (O.innerCount+2)) :
    N.boundary (O.segment i j) = N.pathDemand (O.vertex i) (O.vertex j) := by
  rw [segment,map_add,O.prefix_boundary i.val i.isLt,O.prefix_boundary j.val j.isLt]
  change (unitWord (O.vertex 0) + unitWord (O.vertex i)) +
    (unitWord (O.vertex 0) + unitWord (O.vertex j)) = unitWord (O.vertex i) + unitWord (O.vertex j)
  calc
    _ = (unitWord (O.vertex 0) + unitWord (O.vertex 0)) +
        (unitWord (O.vertex i) + unitWord (O.vertex j)) := by abel
    _ = _ := by rw [word_add_self,zero_add]

/-- A nonempty ordered segment is an actual physical path. -/
theorem segment_isPath (hP : N.IsPathWord s t P)
    (i j : Fin (O.innerCount+2)) (hij : i < j) :
    N.IsPathWord (O.vertex i) (O.vertex j) (O.segment i j) := by
  apply N.isPathWord_of_minimal
  · exact fun h => (ne_of_lt hij) (O.vertex_injective h)
  · exact O.segment_boundary i j
  · intro z hz hzero
    exact hP.minimal z (fun e he => O.segment_subword i j hij.le e (hz e he)) hzero

omit [Fintype V] in
/-- Every position on a nonempty segment has positive selected degree. -/
theorem segment_vertex_pos (i j k : Fin (O.innerCount+2))
    (hij : i < j) (hik : i ≤ k) (hkj : k ≤ j) :
    0 < N.deg (O.segment i j) (O.vertex k) := by
  have hpos (e : E) (he : O.segment i j e ≠ 0)
      (hat : N.src e = O.vertex k ∨ N.dst e = O.vertex k) :
      0 < N.deg (O.segment i j) (O.vertex k) := by
    rcases hat with h | h
    · simpa only [h] using N.deg_src_pos he
    · simpa only [h] using N.deg_dst_pos he
  by_cases hkj' : k < j
  · have hk : k.val < O.innerCount+1 := by have := j.isLt; change k.val < j.val at hkj'; omega
    let h : Fin (O.innerCount+1) := ⟨k.val,hk⟩
    have he : O.segment i j (O.edge h) ≠ 0 :=
      (O.segment_selected i j hij.le _).mpr ⟨h,hik,hkj',rfl⟩
    have hj := (O.joins h).at_left
    exact hpos _ he hj
  · have hkeq : k = j := le_antisymm hkj (le_of_not_gt hkj')
    subst k
    have hjpos : 0 < j.val := by change i.val < j.val at hij; omega
    let h : Fin (O.innerCount+1) := ⟨j.val-1,by have := j.isLt; omega⟩
    have hsj : h.succ = j := by apply Fin.ext; change j.val-1+1=j.val; omega
    have he : O.segment i j (O.edge h) ≠ 0 := by
      apply (O.segment_selected i j hij.le _).mpr
      refine ⟨h,?_,?_,rfl⟩
      · change i.val ≤ j.val-1
        change i.val < j.val at hij
        omega
      · change j.val-1 < j.val
        omega
    have hj := (O.joins h).at_right
    rw [hsj] at hj
    exact hpos _ he hj

omit [Fintype V] in
/-- The positive-degree support of a segment is its closed vertex interval. -/
theorem segment_vertex_support (i j : Fin (O.innerCount+2)) (hij : i < j) (v : V) :
    0 < N.deg (O.segment i j) v ↔
      ∃ k : Fin (O.innerCount+2), i ≤ k ∧ k ≤ j ∧ O.vertex k = v := by
  constructor
  · intro hv
    obtain ⟨e,he,hat⟩ := N.exists_edge_of_deg_pos hv
    obtain ⟨h,hih,hhj,rfl⟩ := (O.segment_selected i j hij.le e).mp he
    have hend : v = O.vertex h.castSucc ∨ v = O.vertex h.succ := by
      rcases O.joins h with ⟨hs,ht⟩ | ⟨hs,ht⟩ <;> rcases hat with hv | hv
      · exact Or.inl (hv.symm.trans hs)
      · exact Or.inr (hv.symm.trans ht)
      · exact Or.inr (hv.symm.trans hs)
      · exact Or.inl (hv.symm.trans ht)
    rcases hend with hv | hv
    · exact ⟨h.castSucc,hih,by change h.val ≤ j.val; omega,hv.symm⟩
    · exact ⟨h.succ,by change i.val ≤ h.val+1; omega,
        by change h.val+1 ≤ j.val; omega,hv.symm⟩
  · rintro ⟨k,hik,hkj,rfl⟩
    exact O.segment_vertex_pos i j k hij hik hkj

omit [Fintype V] in
/-- Separated intervals of one rail have disjoint physical vertex supports. -/
theorem segment_vertexDisjoint (i j k l : Fin (O.innerCount+2))
    (hij : i < j) (hjk : j < k) (hkl : k < l) :
    N.VertexDisjoint (O.segment i j) (O.segment k l) := by
  intro v
  by_cases hzero : N.deg (O.segment i j) v = 0
  · exact Or.inl hzero
  · right
    apply Nat.eq_zero_of_not_pos
    intro hpos
    obtain ⟨a,hia,haj,ha⟩ := (O.segment_vertex_support i j hij v).mp (Nat.pos_of_ne_zero hzero)
    obtain ⟨b,hkb,hbl,hb⟩ := (O.segment_vertex_support k l hkl v).mp hpos
    have hab := O.vertex_injective (ha.trans hb.symm)
    subst b
    exact (not_lt_of_ge haj) (lt_of_lt_of_le hjk hkb)

end Erdos1016.ExactMaximumSupport.NetworkPathOrder.Order
