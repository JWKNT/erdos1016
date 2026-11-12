import Erdos1016.ExactMaximumSupport.MixedCappedSuffixWords

set_option autoImplicit false
set_option maxHeartbeats 2000000
noncomputable section
namespace Erdos1016.ExactMaximumSupport.MixedCappedSuffix
open BoundaryTrace BoundaryTrace.Network MixedTiles
local instance squareCutDecidable (p : Prop) : Decidable p := Classical.propDecidable p

/-- The left side of a square; for a rung both vertices are on its left side. -/
def leftSide : (t : Kind) → t.Vertex → Prop
  | Kind.rung,_ => True
  | Kind.square,v => v.1=false

theorem leftSide_left (t : Kind) (b : Bool) : leftSide t (t.left b) := by
  cases t <;> trivial

theorem not_leftSide_right (t : Kind) (ht : t=Kind.square) (b : Bool) :
    ¬leftSide t (t.right b) := by subst t; simp [leftSide,Kind.right,Kind.dst]

theorem leftSide_src (t : Kind) (e : t.Edge) : leftSide t (t.src e) := by
  cases t <;> trivial

theorem not_leftSide_dst (t : Kind) (ht : t=Kind.square) (e : t.Edge) :
    ¬leftSide t (t.dst e) := by subst t; simp [leftSide,Kind.right,Kind.dst]

variable {k : ℕ} (T : Fin (k+1) → Kind)

/-- A vertex prefix stopped halfway through its final square tile. -/
def halfPrefix (i : Fin (k+1)) : Vertex T → Prop
  | Sum.inl v => v.1.val< i.val ∨ v.1=i ∧ leftSide (T v.1) v.2
  | Sum.inr _ => False

/-- Exactly the local labels of the final square cross this half-prefix. -/
theorem halfPrefix_crosses_inner (i : Fin (k+1)) (hi : T i=Kind.square)
    (j : Fin (k+1)) (e : (T j).Edge) :
    (network T).crosses (halfPrefix T i) (Sum.inl (inner T j e)) ↔ j=i := by
  by_cases hji : j=i
  · subst j
    simp [Network.crosses,network,src,dst,chain,chainSrc,chainDst,MixedTiles.inner,halfPrefix,
      leftSide_src,not_leftSide_dst _ hi]
  · simp [Network.crosses,network,src,dst,chain,chainSrc,chainDst,MixedTiles.inner,halfPrefix,hji]

/-- No chain interface crosses the half-prefix. -/
theorem halfPrefix_not_crosses_link (i : Fin (k+1)) (hi : T i=Kind.square)
    (j : Fin k) (b : Bool) :
    ¬(network T).crosses (halfPrefix T i) (Sum.inl (link T j b)) := by
  by_cases h0 : j.castSucc=i
  · subst i
    simp only [Network.crosses,network,src,dst,chain,chainSrc,chainDst,link,
      halfPrefix,right,left,Fin.coe_castSucc,Fin.val_succ,lt_self_iff_false,
      true_and,false_or,not_leftSide_right _ hi]
    have hn : j.succ≠j.castSucc := (ne_of_lt (Fin.castSucc_lt_succ j)).symm
    simp [hn]
  by_cases h1 : j.succ=i
  · subst i
    simp [Network.crosses,network,src,dst,chain,chainSrc,chainDst,link,halfPrefix,
      right,left,leftSide_left,Fin.coe_castSucc,Fin.val_succ]
  · simp only [Network.crosses,network,src,dst,chain,chainSrc,chainDst,link,
      halfPrefix,right,left,h0,h1,false_and,or_false,Fin.coe_castSucc,Fin.val_succ]
    have h1v : j.val+1≠i.val := fun h => h1 (Fin.ext h)
    omega

/-- The cap lies strictly after the half-prefix. -/
theorem halfPrefix_not_crosses_cap (i : Fin (k+1)) (hi : T i=Kind.square) (b : Bool) :
    ¬(network T).crosses (halfPrefix T i) (Sum.inr b) := by
  by_cases hlast : Fin.last k=i
  · subst i
    simp [Network.crosses,network,src,dst,halfPrefix,right,not_leftSide_right _ hi]
  · have hival:=i.isLt
    simp only [Network.crosses,network,src,dst,halfPrefix,right,hlast,false_and,
      or_false,Fin.val_last,iff_false,not_not]
    omega

/-- A terminal join has odd total parity on the four labels of every square. -/
theorem square_labels_odd (b : Bool) (x : (network T).Word)
    (hx : (network T).boundary x=(network T).pathDemand (entry T b) (cap T))
    (i : Fin (k+1)) (hi : T i=Kind.square) :
    (∑ e : (T i).Edge,tileWord T x i e)=1 := by
  classical
  have hs : halfPrefix T i (entry T b) := by
    change 0< i.val ∨ (0 : Fin (k+1))=i ∧ leftSide (T 0) ((T 0).left b)
    have hl:=leftSide_left (T 0) b
    by_cases h0 : i=0
    · right; exact ⟨h0.symm,hl⟩
    · left; have hv : i.val≠0 := fun h => h0 (Fin.ext h); omega
  have ht : ¬halfPrefix T i (cap T) := by simp [halfPrefix,cap]
  have hh := (network T).cut_parity (halfPrefix T i) x
  rw [hx,(network T).sum_pathDemand,if_pos hs,if_neg ht,add_zero] at hh
  simp only [Fintype.sum_sum_type,Fintype.sum_sigma,Fintype.sum_prod_type] at hh
  have hc (c : Bool) : ¬(network T).crosses (halfPrefix T i) (Sum.inr c) :=
    halfPrefix_not_crosses_cap T i hi c
  have hl (j : Fin k) (c : Bool) :
      ¬(network T).crosses (halfPrefix T i) (Sum.inl (Sum.inr (j,c))) :=
    halfPrefix_not_crosses_link T i hi j c
  have he (j : Fin (k+1)) (e : (T j).Edge) :
      (network T).crosses (halfPrefix T i) (Sum.inl (Sum.inl ⟨j,e⟩)) ↔ j=i :=
    halfPrefix_crosses_inner T i hi j e
  simp only [hc,hl,if_false,Finset.sum_const_zero,he,add_zero] at hh
  have hsum : (∑ j : Fin (k+1),∑ e : (T j).Edge,
      if j=i then x (Sum.inl (Sum.inl ⟨j,e⟩)) else 0)=
      ∑ e : (T i).Edge,x (Sum.inl (Sum.inl ⟨i,e⟩)) := by
    rw [Finset.sum_eq_single i]
    · simp
    · intro j _ hji; simp [hji]
    · simp
  rw [hsum] at hh
  exact hh.symm

/-- A terminal join cannot select all four labels of a square. -/
theorem not_all_square_labels (b : Bool) (x : (network T).Word)
    (hx : (network T).boundary x=(network T).pathDemand (entry T b) (cap T))
    (i : Fin (k+1)) (hi : T i=Kind.square) :
    ¬(∀ e : (T i).Edge,tileWord T x i e=1) := by
  intro hall
  have hh:=square_labels_odd T b x hx i hi
  simp only [hall,Finset.sum_const,Finset.card_univ] at hh
  have he : Fintype.card (T i).Edge=4 := by rw [hi]; decide
  rw [he] at hh
  have hz : (4 : ℕ) • (1 : Bit)=0 := by decide
  rw [hz] at hh
  exact zero_ne_one hh

end Erdos1016.ExactMaximumSupport.MixedCappedSuffix
