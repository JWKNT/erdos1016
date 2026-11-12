import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Tactic

set_option autoImplicit false
set_option maxHeartbeats 2000000

/-!
# A square in four layers of size two

The proof counts the three interfaces. In the absence of a square each
interface has two or three edges. The middle degree equations force all
three interfaces to have the same size; both possibilities force a square.
-/

noncomputable section
open scoped BigOperators

namespace Erdos1016.ExactMaximumSupport.FourThinLayers

local instance fourLayersDecidable (p : Prop) : Decidable p := Classical.propDecidable p

abbrev Vertex := Fin 4 × Bool

def Square (H : SimpleGraph Vertex) : Prop :=
  ∃ a b c d : Vertex,
    a ≠ b ∧ a ≠ c ∧ a ≠ d ∧ b ≠ c ∧ b ≠ d ∧ c ≠ d ∧
    H.Adj a b ∧ H.Adj b c ∧ H.Adj c d ∧ H.Adj d a

private def edge (H : SimpleGraph Vertex) (u v : Vertex) : ℕ :=
  if H.Adj u v then 1 else 0

private theorem edge_le_one (H : SimpleGraph Vertex) (u v : Vertex) : edge H u v ≤ 1 := by
  classical
  unfold edge
  split_ifs <;> omega

private theorem edge_symm (H : SimpleGraph Vertex) (u v : Vertex) :
    edge H u v = edge H v u := by
  simp only [edge, H.adj_comm]

private theorem edge_one (H : SimpleGraph Vertex) (u v : Vertex) :
    edge H u v = 1 ↔ H.Adj u v := by
  simp [edge]

private theorem no_square_sum (H : SimpleGraph Vertex) (hn : ¬ Square H)
    (a b c d : Vertex) (hab : a ≠ b) (hac : a ≠ c) (had : a ≠ d)
    (hbc : b ≠ c) (hbd : b ≠ d) (hcd : c ≠ d) :
    edge H a b + edge H b c + edge H c d + edge H d a ≤ 3 := by
  by_contra h
  have h1 := edge_le_one H a b
  have h2 := edge_le_one H b c
  have h3 := edge_le_one H c d
  have h4 := edge_le_one H d a
  have hall : edge H a b = 1 ∧ edge H b c = 1 ∧ edge H c d = 1 ∧ edge H d a = 1 := by omega
  exact hn ⟨a,b,c,d,hab,hac,had,hbc,hbd,hcd,
    (edge_one H a b).mp hall.1,(edge_one H b c).mp hall.2.1,
    (edge_one H c d).mp hall.2.2.1,(edge_one H d a).mp hall.2.2.2⟩

private theorem interface_contradiction
    (a b c d e f g h i j k l u v : ℕ)
    (ha : a ≤ 1) (hb : b ≤ 1) (hc : c ≤ 1) (hd : d ≤ 1)
    (he : e ≤ 1) (hf : f ≤ 1) (_hg : g ≤ 1) (_hh : h ≤ 1)
    (hi : i ≤ 1) (hj : j ≤ 1) (_hk : k ≤ 1) (_hl : l ≤ 1)
    (hu : u ≤ 1) (hv : v ≤ 1)
    (hA : a+b+c+d ≤ 3) (hB : e+f+g+h ≤ 3) (hC : i+j+k+l ≤ 3)
    (ha0 : 1 ≤ a+c) (ha1 : 1 ≤ b+d)
    (hb0 : 1 ≤ e+g) (hb1 : 1 ≤ f+h)
    (hc0 : 1 ≤ i+k) (hc1 : 1 ≤ j+l)
    (hd10 : a+c+u+e+f=3) (hd11 : b+d+u+g+h=3)
    (hd20 : e+g+v+i+j=3) (hd21 : f+h+v+k+l=3)
    (hr0 : u+v+e+h≤3) (hr1 : u+v+f+g≤3)
    (hs00 : a+b+e+g≤3) (hs01 : a+b+f+h≤3)
    (hs10 : c+d+e+g≤3) (hs11 : c+d+f+h≤3) : False := by
  have hcases :
      (a+b+c+d=2 ∧ e+f+g+h=2 ∧ i+j+k+l=2 ∧ u=1 ∧ v=1) ∨
      (a+b+c+d=3 ∧ e+f+g+h=3 ∧ i+j+k+l=3 ∧ u=0 ∧ v=0) := by omega
  rcases hcases with htwo | hthree
  · omega
  · omega

private theorem degree_sum (H : SimpleGraph Vertex) (v : Vertex) :
    H.degree v = ∑ w : Vertex, edge H v w := by
  classical
  rw [SimpleGraph.degree, H.neighborFinset_eq_filter, Finset.card_filter]
  rfl

private theorem degree_expand (H : SimpleGraph Vertex) (v : Vertex) :
    H.degree v = edge H v (0,false) + edge H v (0,true) +
      edge H v (1,false) + edge H v (1,true) + edge H v (2,false) + edge H v (2,true) +
      edge H v (3,false) + edge H v (3,true) := by
  rw [degree_sum, Fintype.sum_prod_type]
  simp [Fin.sum_univ_succ, Fintype.sum_bool, Fin.succ]
  omega

private theorem edge_self (H : SimpleGraph Vertex) (v : Vertex) : edge H v v = 0 := by
  simp [edge]

private theorem edge_far (H : SimpleGraph Vertex)
    (hlevel : ∀ u v, H.Adj u v → u.1.val ≤ v.1.val + 1 ∧ v.1.val ≤ u.1.val + 1)
    (u v : Vertex) (hfar : ¬ (u.1.val ≤ v.1.val + 1 ∧ v.1.val ≤ u.1.val + 1)) :
    edge H u v = 0 := by
  exact if_neg (fun h => hfar (hlevel u v h))

private theorem incoming_pos (H : SimpleGraph Vertex)
    (hprev : ∀ v : Vertex, 0 < v.1.val →
      ∃ w : Vertex, H.Adj w v ∧ w.1.val + 1 = v.1.val)
    (i j : Fin 4) (hij : i.val + 1 = j.val) (b : Bool) :
    1 ≤ edge H (i,false) (j,b) + edge H (i,true) (j,b) := by
  obtain ⟨⟨k,c⟩, ha, hk⟩ := hprev (j,b) (by dsimp; omega)
  have hki : k = i := Fin.ext (by dsimp at hk; omega)
  subst k
  cases c with
  | false => have he := (edge_one H (i,false) (j,b)).mpr ha; omega
  | true => have he := (edge_one H (i,true) (j,b)).mpr ha; omega

private theorem no_square_sum_list (H : SimpleGraph Vertex) (hn : ¬ Square H)
    (a b c d : Vertex) (hd : [a,b,c,d].Nodup) :
    edge H a b + edge H b c + edge H c d + edge H d a ≤ 3 := by
  apply no_square_sum H hn a b c d <;> simp_all

/-- Four layers of two vertices with the stated middle degrees contain an actual square. -/
theorem exists_square (H : SimpleGraph Vertex)
    (hlevel : ∀ u v, H.Adj u v → u.1.val ≤ v.1.val + 1 ∧ v.1.val ≤ u.1.val + 1)
    (hmiddle : ∀ v : Vertex, v.1 = 1 ∨ v.1 = 2 → H.degree v = 3)
    (_hfirst : ∀ v : Vertex, v.1 = 0 → H.degree v ≤ 2)
    (_hdegree : ∀ v : Vertex, H.degree v ≤ 3)
    (hprev : ∀ v : Vertex, 0 < v.1.val →
      ∃ w : Vertex, H.Adj w v ∧ w.1.val + 1 = v.1.val) : Square H := by
  by_contra hn
  have hfar1 (a b : Bool) : edge H (1,a) (3,b) = 0 := edge_far H hlevel _ _ (by dsimp; decide)
  have hfar2 (a b : Bool) : edge H (2,a) (0,b) = 0 := edge_far H hlevel _ _ (by dsimp; decide)
  have hd10 := hmiddle (1,false) (Or.inl rfl)
  have hd11 := hmiddle (1,true) (Or.inl rfl)
  have hd20 := hmiddle (2,false) (Or.inr rfl)
  have hd21 := hmiddle (2,true) (Or.inr rfl)
  rw [degree_expand] at hd10 hd11 hd20 hd21
  simp only [hfar1, hfar2, edge_self, Nat.add_zero, Nat.zero_add] at hd10 hd11 hd20 hd21
  have ha0 := incoming_pos H hprev 0 1 (by decide) false
  have ha1 := incoming_pos H hprev 0 1 (by decide) true
  have hb0 := incoming_pos H hprev 1 2 (by decide) false
  have hb1 := incoming_pos H hprev 1 2 (by decide) true
  have hc0 := incoming_pos H hprev 2 3 (by decide) false
  have hc1 := incoming_pos H hprev 2 3 (by decide) true
  have hA := no_square_sum_list H hn (0,false) (1,false) (0,true) (1,true) (by decide)
  have hB := no_square_sum_list H hn (1,false) (2,false) (1,true) (2,true) (by decide)
  have hC := no_square_sum_list H hn (2,false) (3,false) (2,true) (3,true) (by decide)
  have hr0 := no_square_sum_list H hn (1,false) (1,true) (2,true) (2,false) (by decide)
  have hr1 := no_square_sum_list H hn (1,false) (1,true) (2,false) (2,true) (by decide)
  have hs00 := no_square_sum_list H hn (0,false) (1,false) (2,false) (1,true) (by decide)
  have hs01 := no_square_sum_list H hn (0,false) (1,false) (2,true) (1,true) (by decide)
  have hs10 := no_square_sum_list H hn (0,true) (1,false) (2,false) (1,true) (by decide)
  have hs11 := no_square_sum_list H hn (0,true) (1,false) (2,true) (1,true) (by decide)
  apply interface_contradiction
    (edge H (0,false) (1,false)) (edge H (0,false) (1,true))
    (edge H (0,true) (1,false)) (edge H (0,true) (1,true))
    (edge H (1,false) (2,false)) (edge H (1,false) (2,true))
    (edge H (1,true) (2,false)) (edge H (1,true) (2,true))
    (edge H (2,false) (3,false)) (edge H (2,false) (3,true))
    (edge H (2,true) (3,false)) (edge H (2,true) (3,true))
    (edge H (1,false) (1,true)) (edge H (2,false) (2,true))
  all_goals first
    | exact edge_le_one H _ _
    | (simp only [edge_symm] at *; omega)

end Erdos1016.ExactMaximumSupport.FourThinLayers
