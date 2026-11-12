import Erdos1016.ExactMaximumSupport.FourPoleChain
import Erdos1016.ExactMaximumSupport.FourPoleBoundary
import Erdos1016.ExactMaximumSupport.Shortening.MinimalCutBridgeless
import Erdos1016.ExactMaximumSupport.FourCutGluing
import Erdos1016.ExactMaximumSupport.MixedChainGlue
import Erdos1016.ExactMaximum.FullPairs

set_option autoImplicit false

/-!
# The ring case from minimum-cut bridgelessness

The shores are bridgeless before any full-pair classification is applied.
The direct minimum-cut lemma replaces the specialized full-pair bridge split
and its ambient bridge-lifting argument. The original physical chain gluing
and ring count are reused unchanged. No paper-length saving is asserted.
-/
noncomputable section
namespace Erdos1016.ExactMaximumSupport.Shortening.BridgelessRingCase
open BoundaryTrace BoundaryTrace.Network BoundaryDecay
local instance chainsDecidable (p : Prop) : Decidable p := Classical.propDecidable p
variable {V E : Type*} [Fintype V] [Fintype E] (N : Network V E)

omit [Fintype V] in
/-- Four covering physical labels bound the actual crossing-label cardinality. -/
theorem cutSize_le_four (S : V → Prop) (e : Fin 4 → E)
    (hcover : ∀g,N.crosses S g → ∃i,g=e i) : N.cutSize S≤4 := by
  classical
  let f : {g : E // N.crosses S g} → Fin 4 :=
    fun g => (hcover g.val g.property).choose
  have hf : Function.Injective f := by
    intro g h heq
    apply Subtype.ext
    exact (hcover g.val g.property).choose_spec.trans
      ((congrArg e heq).trans (hcover h.val h.property).choose_spec.symm)
  simpa only [Network.cutSize,Nat.card_eq_fintype_card,Fintype.card_fin] using
    Nat.card_le_card_of_injective f hf

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
  have hbl := MinimalCutBridgeless.four_cut_shore_bridgeless N S
    (cutSize_le_four N S e hcover) hmin hpole
  have hne {i j : Fin 4} (hij : i≠j) : x i≠x j := fun h => hij (hinj h)
  exact FourPoleChain.isChain (N.sub (N.inside S)) (x 0) (x 1) (x 2) (x 3) hpole hbl
    (hne (by decide)) (hne (by decide)) (hne (by decide))
    (hne (by decide)) (hne (by decide)) (hne (by decide))
    (hport 0) (hport 1) (hport 2) (hport 3) honly
    (hfull 0 2 (by decide) (by decide)) (hfull 1 2 (by decide) (by decide))
    (hfull 0 3 (by decide) (by decide)) (hfull 1 3 (by decide) (by decide))

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
  have hbl := MinimalCutBridgeless.four_cut_shore_bridgeless N (fun v => ¬S v)
    (cutSize_le_four N (fun v => ¬S v) e hc') hmin hqole
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

/-- The actual ring-case endpoint, avoiding the full-pair bridge classification. -/
theorem ringCaseStatement : ExactMaximum.RingCaseStatement := by
  classical
  refine ⟨8,?_⟩
  intro V E _ _ N _ hcubic hmin hr S e x y hcover hjoins hx hy hxinj hyinj hpole hqole hfull
  obtain ⟨hX,hY⟩ := both_sides_reversed N hcubic hmin S e x y hcover hjoins
    hx hy hxinj hyinj hpole hqole hfull
  obtain ⟨k,l,T,U,twist,⟨I⟩⟩ := FourCutGluing.exists_glued_of_chains N hcubic S e x y
    hcover hjoins hx hy hxinj hyinj hX hY
  have h := MixedTiles.glued_numCycles_le_horakKim_rank T U twist
    (by rwa [←I.networkRank_eq])
  rwa [←I.numCycles_eq,←I.networkRank_eq] at h

end Erdos1016.ExactMaximumSupport.Shortening.BridgelessRingCase
