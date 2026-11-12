import Erdos1016.ExactMaximumSupport.MixedRingFullStates

set_option autoImplicit false

/-!
# The actual two-strand states of a full-interface tile

The local boundary forces a rung to be unused and a square to use one perfect matching.
Each state therefore carries a literal permutation of the two rails.
-/

noncomputable section
namespace Erdos1016.ExactMaximumSupport.MixedTiles.Kind
open BoundaryTrace BoundaryTrace.Network

/-- The rail permutation read from the actual local word. -/
def railPermutation : (t : Kind) → t.network.Word → Equiv.Perm Bool
  | rung, _ => Equiv.refl Bool
  | square, z => if z (false,false)=1 then Equiv.refl Bool else Equiv.swap false true

/-- The physical local word prescribed by a rail permutation. -/
def matchingWord : (t : Kind) → Equiv.Perm Bool → t.network.Word
  | rung, _ => 0
  | square, p => fun e => if e.2=p e.1 then 1 else 0

/-- A full-boundary local word is exactly its physical rail matching. -/
theorem full_word_eq_matching (t : Kind) (z : t.network.Word)
    (hz : t.network.boundary z=fun _ => fullParity t) :
    z=matchingWord t (railPermutation t z) := by
  cases t
  · apply rung_word_eq_of_boundary
    simpa only [fullParity,matchingWord,map_zero] using hz
  · rcases bit_cases (z (false,false)) with h0 | h1
    · have hp : railPermutation Kind.square z=Equiv.swap false true := by
        simp only [railPermutation,h0,zero_ne_one,if_false]
      have hb : Kind.square.network.boundary (matchingWord Kind.square (railPermutation Kind.square z))=
          fun _ => (1 : Bit) := by
        rw [hp]
        funext v
        rcases v with ⟨a,b⟩
        cases a <;> cases b <;>
          simp [Network.boundary_apply,network,src,dst,matchingWord,Fintype.sum_prod_type] <;> decide
      apply square_word_eq_of_boundary_corner (hz.trans hb.symm)
      simp [hp,matchingWord,h0]
    · have hp : railPermutation Kind.square z=Equiv.refl Bool := by
        simp only [railPermutation,h1,if_true]
      have hb : Kind.square.network.boundary (matchingWord Kind.square (railPermutation Kind.square z))=
          fun _ => (1 : Bit) := by
        rw [hp]
        funext v
        rcases v with ⟨a,b⟩
        cases a <;> cases b <;>
          simp [Network.boundary_apply,network,src,dst,matchingWord,Fintype.sum_prod_type]
      apply square_word_eq_of_boundary_corner (hz.trans hb.symm)
      simp [hp,matchingWord,h1]

/-- Equal rail permutations recover the actual local matching words. -/
theorem full_word_eq_of_railPermutation (t : Kind) {x y : t.network.Word}
    (hx : t.network.boundary x=fun _ => fullParity t)
    (hy : t.network.boundary y=fun _ => fullParity t)
    (hp : railPermutation t x=railPermutation t y) : x=y := by
  rw [full_word_eq_matching t x hx,full_word_eq_matching t y hy,hp]

/-- Pull the two rail colors back from the left and right interfaces. -/
def railColor : (t : Kind) → Equiv.Perm Bool → Equiv.Perm Bool → t.Vertex → Bool
  | rung, before, _, v => before.symm v
  | square, before, after, v => if v.1 then after.symm v.2 else before.symm v.2

theorem railColor_left (t : Kind) (before after : Equiv.Perm Bool) (b : Bool) :
    railColor t before after (t.left b)=before.symm b := by
  cases t <;> rfl

theorem railColor_right (t : Kind) (z : t.network.Word) (before : Equiv.Perm Bool) (b : Bool) :
    railColor t before (railPermutation t z*before) (t.right b)=
      (railPermutation t z*before).symm b := by
  cases t
  · simp [railColor,railPermutation,right]
  · rfl

/-- Every selected local label preserves the propagated rail color. -/
theorem selected_edge_preserves_color (t : Kind) (z : t.network.Word)
    (hz : t.network.boundary z=fun _ => fullParity t)
    (before : Equiv.Perm Bool) (e : t.Edge) (he : z e≠0) :
    railColor t before (railPermutation t z*before) (t.src e)=
      railColor t before (railPermutation t z*before) (t.dst e) := by
  have hw := congrFun (full_word_eq_matching t z hz) e
  cases t
  · exact False.elim (he hw)
  · rcases e with ⟨a,b⟩
    have hp : b=railPermutation Kind.square z a := by
      by_contra h
      exact he (hw.trans (if_neg h))
    simp only [railColor,src,dst,Bool.false_eq_true,if_false,if_true]
    rw [hp]
    apply (railPermutation Kind.square z*before).injective
    simp [Equiv.Perm.mul_apply]

end Erdos1016.ExactMaximumSupport.MixedTiles.Kind
