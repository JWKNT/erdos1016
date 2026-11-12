import Erdos1016.ExactMaximumSupport.PoleTerminalDeletion
import Erdos1016.ExactMaximumSupport.PoleAdjacentGap
import Mathlib.Data.Fin.Tuple.Basic

set_option autoImplicit false
set_option maxHeartbeats 2000000

/-!
# The order of an actual physical path

Remove its first selected label and induct on its physical support size.
The resulting vertex and label arrays cover the original path exactly.
No ambient shortestness or simple-graph realization is assumed.
-/
noncomputable section
namespace Erdos1016.ExactMaximumSupport.NetworkPathOrder
open BoundaryTrace BoundaryTrace.Network BoundaryDecay
local instance pathOrderDecidable (p : Prop) : Decidable p := Classical.propDecidable p
variable {V E : Type*} [Fintype V] [Fintype E] (N : Network V E)

/-- An ordered path with all vertices and physical labels retained. -/
structure Order (s t : V) (P : N.Word) where
  innerCount : ℕ
  vertex : Fin (innerCount+2) → V
  edge : Fin (innerCount+1) → E
  vertex_injective : Function.Injective vertex
  edge_injective : Function.Injective edge
  first : vertex 0 = s
  last : vertex (Fin.last (innerCount+1)) = t
  joins : ∀ i, N.Joins (edge i) (vertex i.castSucc) (vertex i.succ)
  edge_support : ∀ e, P e ≠ 0 ↔ ∃ i, edge i = e

namespace Order
variable {N} {s t : V} {P : N.Word} (O : Order N s t P)

omit [Fintype V] [Fintype E] in
/-- Every enumerated label is selected by the original word. -/
theorem edge_selected (i : Fin (O.innerCount+1)) : P (O.edge i) ≠ 0 :=
  (O.edge_support _).mpr ⟨i,rfl⟩

omit [Fintype V] in
/-- Every enumerated vertex has positive degree in the original path word. -/
theorem vertex_pos (i : Fin (O.innerCount+2)) : 0 < N.deg P (O.vertex i) := by
  refine Fin.cases ?_ (fun j => ?_) i
  · have hh := O.joins 0
    have hp := O.edge_selected 0
    rcases hh with ⟨hs,ht⟩ | ⟨hs,ht⟩
    · simpa only [hs] using N.deg_src_pos hp
    · simpa only [ht] using N.deg_dst_pos hp
  · have hh := O.joins j
    have hp := O.edge_selected j
    rcases hh with ⟨hs,ht⟩ | ⟨hs,ht⟩
    · simpa only [ht] using N.deg_dst_pos hp
    · simpa only [hs] using N.deg_src_pos hp

omit [Fintype V] in
/-- The enumerated vertices are exactly the vertices of positive selected degree. -/
theorem vertex_support (v : V) : 0 < N.deg P v ↔ ∃ i, O.vertex i = v := by
  constructor
  · intro hv
    obtain ⟨e,he,hat⟩ := N.exists_edge_of_deg_pos hv
    obtain ⟨i,rfl⟩ := (O.edge_support e).mp he
    have hj := O.joins i
    rcases hj with ⟨hs,ht⟩ | ⟨hs,ht⟩ <;> rcases hat with hv | hv
    · exact ⟨i.castSucc,hs.symm.trans hv⟩
    · exact ⟨i.succ,ht.symm.trans hv⟩
    · exact ⟨i.succ,hs.symm.trans hv⟩
    · exact ⟨i.castSucc,ht.symm.trans hv⟩
  · rintro ⟨i,rfl⟩
    exact O.vertex_pos i

omit [Fintype V] in
/-- The physical path size is the exact number of enumerated labels. -/
theorem size_eq : size P = O.innerCount+1 := by
  classical
  have hset : (Finset.univ.filter fun e => P e ≠ 0) = Finset.univ.image O.edge := by
    ext e
    simp only [Finset.mem_filter,Finset.mem_univ,true_and,Finset.mem_image,O.edge_support]
  unfold size
  rw [hset,Finset.card_image_of_injective _ O.edge_injective,Finset.card_univ,Fintype.card_fin]

end Order

omit [Fintype V] in
/-- Deleting a selected label strictly decreases the support size. -/
theorem size_erase_first_lt (P : N.Word) (e : E) (hPe : P e ≠ 0) :
    size (P+unitWord e) < size P := by
  classical
  have hset : (Finset.univ.filter fun g => (P+unitWord e) g ≠ 0) =
      (Finset.univ.filter fun g => P g ≠ 0).erase e := by
    ext g
    by_cases h : g = e
    · subst g
      simp [Finset.mem_filter,Finset.mem_erase,Pi.add_apply,unitWord_apply,
        bit_eq_one_of_ne_zero hPe,bit_add_self]
    · simp [Finset.mem_filter,Finset.mem_erase,Pi.add_apply,unitWord_apply,h,Ne.symm h]
  change (Finset.univ.filter fun g => (P+unitWord e) g ≠ 0).card <
    (Finset.univ.filter fun g => P g ≠ 0).card
  rw [hset]
  exact Finset.card_erase_lt_of_mem (Finset.mem_filter.mpr ⟨Finset.mem_univ _,hPe⟩)

/-- Every actual path admits an exact order of its vertices and physical labels. -/
theorem exists_order {s t : V} {P : N.Word} (hP : N.IsPathWord s t P) :
    Nonempty (Order N s t P) := by
  classical
  have key : ∀ n : ℕ, ∀ (s t : V) (P : N.Word), size P = n → N.IsPathWord s t P →
      Nonempty (Order N s t P) := by
    intro n
    induction n using Nat.strong_induction_on with
    | _ n ih =>
      intro s t P hn hP
      have hs : 0 < N.deg P s := by rw [hP.2.1]; decide
      obtain ⟨e,hPe,hes⟩ := N.exists_edge_of_deg_pos hs
      obtain ⟨x,he⟩ := N.exists_joins hes
      by_cases hxt : x = t
      · subst x
        have hword := PoleAdjacentGap.path_eq_unit_of_selected N he hP hPe
        subst P
        refine ⟨{ innerCount := 0
                  vertex := Fin.cons s (fun _ : Fin 1 => t)
                  edge := fun _ : Fin 1 => e
                  vertex_injective := ?_
                  edge_injective := ?_
                  first := rfl
                  last := rfl
                  joins := ?_
                  edge_support := ?_ }⟩
        · apply Fin.cons_injective_of_injective
          · rintro ⟨i,hi⟩
            exact hP.1 hi.symm
          · intro a b _
            exact Subsingleton.elim _ _
        · intro a b _
          apply Fin.ext
          omega
        · intro i
          have hi : i = 0 := by apply Fin.ext; omega
          subst i
          exact he
        · intro g
          simp [unitWord_apply]
      · obtain ⟨hQ,hw⟩ := PoleTerminalDeletion.erase_first N hP he hxt hPe
        have hlt : size (P+unitWord e) < n := by rw [← hn]; exact size_erase_first_lt N P e hPe
        obtain ⟨O⟩ := ih _ hlt x t (P+unitWord e) rfl hQ
        have hQe : (P+unitWord e) e = 0 := by
          simp only [Pi.add_apply,unitWord_apply,if_pos rfl,bit_eq_one_of_ne_zero hPe]
          exact bit_add_self 1
        have hQs : N.deg (P+unitWord e) s = 0 := by
          apply N.deg_eq_zero_of_forall
          intro g hg
          exact Classical.not_not.mp (fun h => by
            have hh := hw g h
            rcases hg with hg | hg
            · exact hh.1 hg
            · exact hh.2 hg)
        refine ⟨{ innerCount := O.innerCount+1
                  vertex := Fin.cons s O.vertex
                  edge := Fin.cons e O.edge
                  vertex_injective := ?_
                  edge_injective := ?_
                  first := rfl
                  last := ?_
                  joins := ?_
                  edge_support := ?_ }⟩
        · apply Fin.cons_injective_of_injective
          · rintro ⟨i,hi⟩
            have hh := O.vertex_pos i
            rw [hi,hQs] at hh
            omega
          · exact O.vertex_injective
        · apply Fin.cons_injective_of_injective
          · rintro ⟨i,hi⟩
            have hh := O.edge_selected i
            rw [hi,hQe] at hh
            exact hh rfl
          · exact O.edge_injective
        · exact O.last
        · intro i
          refine Fin.cases ?_ (fun j => ?_) i
          · simpa only [Fin.cons_zero,Fin.cons_succ,O.first] using he
          · simpa only [Fin.cons_succ] using O.joins j
        · intro g
          simp only [Fin.exists_fin_succ,Fin.cons_zero,Fin.cons_succ,← O.edge_support]
          by_cases h : e = g
          · subst g
            exact iff_of_true hPe (Or.inl rfl)
          · simp [h,Pi.add_apply,unitWord_apply]
  exact key _ s t P rfl hP

end Erdos1016.ExactMaximumSupport.NetworkPathOrder
