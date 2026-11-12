import Erdos1016.ExactMaximumSupport.FourCutChains
import Erdos1016.ExactMaximumSupport.FourCutGluedIso
import Erdos1016.ExactMaximumSupport.FourPortCodes
import Erdos1016.ExactMaximumSupport.MixedTileRelabel
import Erdos1016.ExactMaximumSupport.NetworkIsoComposition

set_option autoImplicit false
set_option maxHeartbeats 1500000

/-!
# Glue the actual two full-cross sides

The two unordered port orders determine physical Bool permutations. A uniform
relabeling of the second chain aligns the middle pair; one closing twist remains.
-/
noncomputable section
namespace Erdos1016.ExactMaximumSupport.FourCutGluing
open BoundaryTrace BoundaryTrace.Network BoundaryDecay MixedTiles FourPortCodes
local instance gluingDecidable (p : Prop) : Decidable p := Classical.propDecidable p
variable {V E : Type*} [Fintype V] [Fintype E] (N : Network V E)

omit [Fintype V] in
/-- Two actual side chain isomorphisms give an isomorphism of the original network to the glued model. -/
theorem exists_glued_of_chains (hcubic : N.IsCubic)
    (S : V → Prop) (e : Fin 4 → E) (x y : Fin 4 → V)
    (hcover : ∀g,N.crosses S g → ∃i,g=e i)
    (hjoins : ∀i,N.Joins (e i) (x i) (y i))
    (hx : ∀i,S (x i)) (hy : ∀i,¬S (y i))
    (hxinj : Function.Injective x) (hyinj : Function.Injective y)
    (hX : FourPoleChain.IsChain (N.sub (N.inside S)) (x 0) (x 1) (x 2) (x 3))
    (hY : FourPoleChain.IsChain (N.sub (N.outside S)) (y 2) (y 3) (y 0) (y 1)) :
    ∃ k l : ℕ,∃ T : Fin (k+1) → Kind,∃ U : Fin (l+1) → Kind,
      ∃ twist : Equiv.Perm Bool, Nonempty (NetworkIso (glued T U twist) N) := by
  obtain ⟨k,T,J,hJl,hJr,_⟩ := hX
  obtain ⟨l,U,K,hKl,hKr,_⟩ := hY
  obtain ⟨α,hα⟩ := exists_code (fun b => (J.vertices (left T 0 b)).val) (x 0) (x 1) hJl
  obtain ⟨β,hβ⟩ := exists_code (fun b => (J.vertices (right T (Fin.last k) b)).val) (x 2) (x 3) hJr
  obtain ⟨γ,hγ⟩ := exists_code (fun b => (K.vertices (left U 0 b)).val) (y 2) (y 3) hKl
  obtain ⟨δ,hδ⟩ := exists_code (fun b => (K.vertices (right U (Fin.last l) b)).val) (y 0) (y 1) hKr
  simp only [pair_lower] at hα hδ
  simp only [pair_upper] at hβ hγ
  let p : Equiv.Perm Bool := β.trans γ.symm
  let K' := (railIso U p).trans K
  let twist : Equiv.Perm Bool := (p.trans δ).trans α.symm
  let ρ : (Bool ⊕ Bool) ≃ Fin 4 := (Equiv.sumCongr (p.trans δ) β).trans index
  have hnewleft (b : Bool) : (K'.vertices (left U 0 b)).val=y (upper (β b)) := by
    change (K.vertices ((railIso U p).vertices (left U 0 b))).val=y (upper (β b))
    rw [railIso_left,hγ]
    simp only [p,Equiv.trans_apply,Equiv.apply_symm_apply]
  have hnewright (b : Bool) : (K'.vertices (right U (Fin.last l) b)).val=y (lower (δ (p b))) := by
    change (K.vertices ((railIso U p).vertices (right U (Fin.last l) b))).val=y (lower (δ (p b)))
    rw [railIso_right,hδ]
  have htwist (b : Bool) : α (twist b)=δ (p b) := by
    simp only [twist,Equiv.trans_apply,Equiv.apply_symm_apply]
  have hclosing (b : Bool) : N.Joins (e (ρ (Sum.inl b)))
      (K'.vertices (right U (Fin.last l) b)).val (J.vertices (left T 0 (twist b))).val := by
    change N.Joins (e (lower (δ (p b)))) _ _
    rw [hnewright,hα,htwist]
    exact (hjoins _).symm
  have hcentral (b : Bool) : N.Joins (e (ρ (Sum.inr b)))
      (J.vertices (right T (Fin.last k) b)).val (K'.vertices (left U 0 b)).val := by
    change N.Joins (e (upper (β b))) _ _
    rw [hβ,hnewleft]
    exact hjoins _
  exact ⟨k,l,T,U,twist,⟨FourCutGluedIso.iso N S e x y hcubic hcover hjoins hx hy hxinj hyinj
    T U J K' twist ρ hclosing hcentral⟩⟩

/-- The original full-cross four-cut hypotheses force the actual physical glued-ring model. -/
theorem exists_glued (hcubic : N.IsCubic)
    (hmin : ∀T,N.IsCyclicCut T → 4≤N.cutSize T)
    (S : V → Prop) (e : Fin 4 → E) (x y : Fin 4 → V)
    (hcover : ∀g,N.crosses S g → ∃i,g=e i)
    (hjoins : ∀i,N.Joins (e i) (x i) (y i))
    (hx : ∀i,S (x i)) (hy : ∀i,¬S (y i))
    (hxinj : Function.Injective x) (hyinj : Function.Injective y)
    (hpole : (N.sub (N.inside S)).IsWeakPole)
    (hqole : (N.sub (N.outside S)).IsWeakPole)
    (hfull : ∀i j : Fin 4,i.val<2 → 2≤j.val →
      (N.sub (N.inside S)).IsFullPair (x i) (x j) ∧
      (N.sub (N.outside S)).IsFullPair (y i) (y j)) :
    ∃ k l : ℕ,∃ T : Fin (k+1) → Kind,∃ U : Fin (l+1) → Kind,
      ∃ twist : Equiv.Perm Bool, Nonempty (NetworkIso (glued T U twist) N) := by
  obtain ⟨hX,hY⟩ := FourCutChains.both_sides_reversed N hcubic hmin S e x y hcover hjoins
    hx hy hxinj hyinj hpole hqole hfull
  exact exists_glued_of_chains N hcubic S e x y hcover hjoins hx hy hxinj hyinj hX hY

end Erdos1016.ExactMaximumSupport.FourCutGluing
