import Erdos1016.ExactMaximumSupport.FourPoleChain
import Erdos1016.ExactMaximumSupport.FourPoleBoundary
import Erdos1016.ExactMaximumSupport.FourPoleBridgeLift

set_option autoImplicit false

/-!
# The actual two chains at a full-cross four-cut

The cyclic-cut condition excludes the bridge alternative. The original cubic
degrees supply exactly the four listed ports, with no extra pole certificate.
-/
noncomputable section
namespace Erdos1016.ExactMaximumSupport.FourCutChains
open BoundaryTrace BoundaryTrace.Network BoundaryDecay
local instance chainsDecidable (p : Prop) : Decidable p := Classical.propDecidable p
variable {V E : Type*} [Fintype V] [Fintype E] (N : Network V E)

/-- One full-cross side of the original cubic four-cut is an actual tile chain. -/
theorem side_isChain (hcubic : N.IsCubic)
    (hmin : ∀T,N.IsCyclicCut T → 4≤N.cutSize T)
    (S : V → Prop) (e : Fin 4 → E) (x y : Fin 4 → V)
    (hcover : ∀g,N.crosses S g → ∃i,g=e i)
    (hjoins : ∀i,N.Joins (e i) (x i) (y i))
    (hx : ∀i,S (x i)) (hy : ∀i,¬S (y i)) (hinj : Function.Injective x)
    (hpole : (N.sub (N.inside S)).IsWeakPole)
    (hfull : ∀i j : Fin 4,i.val<2 → 2≤j.val →
      (N.sub (N.inside S)).IsFullPair (x i) (x j)) :
    FourPoleChain.IsChain (N.sub (N.inside S)) (x 0) (x 1) (x 2) (x 3) := by
  have hport := FourPoleBoundary.isPort N S e x y hcover hjoins hx hy hcubic hinj
  have honly : ∀v,(N.sub (N.inside S)).IsPort v →
      v=x 0 ∨ v=x 1 ∨ v=x 2 ∨ v=x 3 := by
    intro v hv
    obtain ⟨i,rfl⟩ := FourPoleBoundary.only N S e x y hcover hjoins hy hcubic v hv
    fin_cases i <;> simp
  have hbl := FourPoleBridgeLift.side_bridgeless N S e x y hmin hcover hjoins hx hy
    hpole (hport 0) (hport 2) hfull
  have hne {i j : Fin 4} (hij : i≠j) : x i≠x j := fun h => hij (hinj h)
  exact FourPoleChain.isChain (N.sub (N.inside S)) (x 0) (x 1) (x 2) (x 3) hpole hbl
    (hne (by decide)) (hne (by decide)) (hne (by decide))
    (hne (by decide)) (hne (by decide)) (hne (by decide))
    (hport 0) (hport 1) (hport 2) (hport 3) honly
    (hfull 0 2 (by decide) (by decide)) (hfull 1 2 (by decide) (by decide))
    (hfull 0 3 (by decide) (by decide)) (hfull 1 3 (by decide) (by decide))

/-- Both sides in the ring-case hypotheses are concrete physical tile chains. -/
theorem both_sides (hcubic : N.IsCubic)
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
    FourPoleChain.IsChain (N.sub (N.inside S)) (x 0) (x 1) (x 2) (x 3) ∧
    FourPoleChain.IsChain (N.sub (N.outside S)) (y 0) (y 1) (y 2) (y 3) := by
  constructor
  · exact side_isChain N hcubic hmin S e x y hcover hjoins hx hy hxinj hpole
      (fun i j hi hj => (hfull i j hi hj).1)
  · exact side_isChain N hcubic hmin (fun v => ¬S v) e y x
      (fun g hg => hcover g ((N.crosses_not_iff S g).mp hg))
      (fun i => (hjoins i).symm) hy (fun i => not_not.mpr (hx i)) hyinj hqole
      (fun i j hi hj => (hfull i j hi hj).2)

/-- Orient the second chain in the reverse port order, ready for physical concatenation. -/
theorem both_sides_reversed (hcubic : N.IsCubic)
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
    FourPoleChain.IsChain (N.sub (N.inside S)) (x 0) (x 1) (x 2) (x 3) ∧
    FourPoleChain.IsChain (N.sub (N.outside S)) (y 2) (y 3) (y 0) (y 1) := by
  refine ⟨side_isChain N hcubic hmin S e x y hcover hjoins hx hy hxinj hpole
    (fun i j hi hj => (hfull i j hi hj).1),?_⟩
  have hc' : ∀g,N.crosses (fun v => ¬S v) g → ∃i,g=e i :=
    fun g hg => hcover g ((N.crosses_not_iff S g).mp hg)
  have hj' := fun i => (hjoins i).symm
  have hx' := fun i => not_not.mpr (hx i)
  have hport := FourPoleBoundary.isPort N (fun v => ¬S v) e y x hc' hj' hy hx' hcubic hyinj
  have hbl := FourPoleBridgeLift.side_bridgeless N (fun v => ¬S v) e y x hmin hc' hj' hy hx'
    hqole (hport 0) (hport 2) (fun i j hi hj => (hfull i j hi hj).2)
  have honly : ∀v,(N.sub (N.outside S)).IsPort v →
      v=y 2 ∨ v=y 3 ∨ v=y 0 ∨ v=y 1 := by
    intro v hv
    obtain ⟨i,rfl⟩ := FourPoleBoundary.only N (fun v => ¬S v) e y x hc' hj' hx' hcubic v hv
    fin_cases i <;> simp
  have hne {i j : Fin 4} (hij : i≠j) : y i≠y j := fun h => hij (hyinj h)
  have hreverse (i j : Fin 4) (hi : i.val<2) (hj : 2≤j.val) :
      (N.sub (N.outside S)).IsFullPair (y j) (y i) := by
    change (N.sub (N.outside S)).numPaths (y j) (y i)=2^networkRank (N.sub (N.outside S))
    rw [ExactMaximum.numPaths_symm]
    exact (hfull i j hi hj).2
  exact FourPoleChain.isChain (N.sub (N.outside S)) (y 2) (y 3) (y 0) (y 1) hqole hbl
    (hne (by decide)) (hne (by decide)) (hne (by decide))
    (hne (by decide)) (hne (by decide)) (hne (by decide))
    (hport 2) (hport 3) (hport 0) (hport 1) honly
    (hreverse 0 2 (by decide) (by decide)) (hreverse 0 3 (by decide) (by decide))
    (hreverse 1 2 (by decide) (by decide)) (hreverse 1 3 (by decide) (by decide))

end Erdos1016.ExactMaximumSupport.FourCutChains
