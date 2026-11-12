import Erdos1016.ExactMaximumSupport.FourFullBridge
import Erdos1016.ExactMaximum.NetEmbed

set_option autoImplicit false
set_option maxHeartbeats 1500000

/-!
# A bridge in a full-cross shore gives an ambient cut of at most three

Intersect the bridge shore with the original side. Its only outgoing labels
are the internal bridge and the two original cut labels at its ports.
-/
noncomputable section
namespace Erdos1016.ExactMaximumSupport.FourPoleBridgeLift
open BoundaryTrace BoundaryTrace.Network BoundaryDecay
local instance bridgeLiftDecidable (p : Prop) : Decidable p := Classical.propDecidable p
variable {V E : Type*} [Fintype V] [Fintype E] (N : Network V E)

omit [Fintype E] in
/-- An actual cycle in a nested edge restriction remains a cycle in any containing restriction. -/
theorem cycle_pos_of_nested (p : E → Prop) (q : {e // p e} → Prop) (r : E → Prop)
    [Fintype {e // p e}] [Fintype {e : {e // p e} // q e}] [Fintype {e // r e}]
    (hqr : ∀e,q e → r e.val) (hcyc : 0<((N.sub p).sub q).numCycles) :
    0<(N.sub r).numCycles := by
  classical
  let R : Network.Embed ((N.sub p).sub q) (N.sub r) :=
    { φ := id
      ψ := fun e => ⟨e.val.val,hqr e.val e.property⟩
      φ_inj := Function.injective_id
      ψ_inj := by
        intro e f h
        apply Subtype.ext
        apply Subtype.ext
        exact congrArg (fun e : {e // r e} => e.val) h
      src := fun _ => rfl
      dst := fun _ => rfl }
  obtain ⟨⟨z,hz⟩⟩ := Finite.card_pos_iff.mp hcyc
  haveI : Nonempty {x : (N.sub r).Word // (N.sub r).IsCycleWord x} :=
    ⟨⟨R.push z,(R.isCycleWord_push_iff z).mpr hz⟩⟩
  exact Nat.card_pos

/-- Both cycles of a bridge cut in the first side survive in the ambient intersection cut. -/
theorem cyclic_intersection (S T : V → Prop)
    (hT : (N.sub (N.inside S)).IsCyclicCut T) :
    N.IsCyclicCut (fun v => S v ∧ T v) := by
  classical
  constructor
  · exact cycle_pos_of_nested N (N.inside S) ((N.sub (N.inside S)).inside T)
      (N.inside (fun v => S v ∧ T v))
      (fun e he => ⟨⟨e.property.1,he.1⟩,⟨e.property.2,he.2⟩⟩) hT.1
  · exact cycle_pos_of_nested N (N.inside S) ((N.sub (N.inside S)).outside T)
      (N.outside (fun v => S v ∧ T v))
      (fun _ he => ⟨fun h => he.1 h.2,fun h => he.2 h.2⟩) hT.2

omit [Fintype V] in
/-- An internal one-edge cut meeting only the first two boundary ports has ambient size at most three. -/
theorem intersection_cut_le_three (S T : V → Prop) (e : Fin 4 → E) (x y : Fin 4 → V)
    (hcover : ∀g,N.crosses S g → ∃i,g=e i)
    (hjoins : ∀i,N.Joins (e i) (x i) (y i))
    (hx : ∀i,S (x i)) (hy : ∀i,¬S (y i))
    (hports : ∀i,T (x i) → i=0 ∨ i=1)
    (f : {g // N.inside S g})
    (hf : ∀g,(N.sub (N.inside S)).crosses T g → g=f) :
    N.cutSize (fun v => S v ∧ T v)≤3 := by
  classical
  have hlabels (g : E) (hg : N.crosses (fun v => S v ∧ T v) g) :
      g=f.val ∨ g=e 0 ∨ g=e 1 := by
    by_cases hgi : N.inside S g
    · left
      have ht : (N.sub (N.inside S)).crosses T ⟨g,hgi⟩ := by
        change ¬(T (N.src g) ↔ T (N.dst g))
        change ¬((S (N.src g) ∧ T (N.src g)) ↔ (S (N.dst g) ∧ T (N.dst g))) at hg
        simpa only [hgi.1,hgi.2,true_and] using hg
      exact congrArg Subtype.val (hf ⟨g,hgi⟩ ht)
    · have hcross : N.crosses S g := by
        change ¬(S (N.src g) ↔ S (N.dst g))
        change ¬(S (N.src g) ∧ S (N.dst g)) at hgi
        change ¬((S (N.src g) ∧ T (N.src g)) ↔ (S (N.dst g) ∧ T (N.dst g))) at hg
        tauto
      obtain ⟨i,rfl⟩ := hcover g hcross
      have hTi : T (x i) := by
        rcases hjoins i with ⟨hs,hd⟩ | ⟨hs,hd⟩
        · change ¬((S (N.src (e i)) ∧ T (N.src (e i))) ↔
            (S (N.dst (e i)) ∧ T (N.dst (e i)))) at hg
          simpa only [hs,hd,hx i,hy i,true_and,false_and,iff_false,not_not] using hg
        · change ¬((S (N.src (e i)) ∧ T (N.src (e i))) ↔
            (S (N.dst (e i)) ∧ T (N.dst (e i)))) at hg
          simpa only [hs,hd,hx i,hy i,true_and,false_and,false_iff,not_not] using hg
      rcases hports i hTi with rfl | rfl
      · exact Or.inr (Or.inl rfl)
      · exact Or.inr (Or.inr rfl)
  let B : Finset E := {f.val,e 0,e 1}
  have hmem (g : {g // N.crosses (fun v => S v ∧ T v) g}) : g.val∈B := by
    simpa only [B,Finset.mem_insert,Finset.mem_singleton] using hlabels g.val g.property
  have hbound := Nat.card_le_card_of_injective
    (fun g : {g // N.crosses (fun v => S v ∧ T v) g} => (⟨g.val,hmem g⟩ : {g // g∈B}))
    (by intro g h he; apply Subtype.ext; exact congrArg (fun z : {g // g∈B} => z.val) he)
  have hcard : Nat.card {g // g∈B}=B.card := by simp
  have hthree : B.card≤3 := by
    calc B.card≤({e 0,e 1} : Finset E).card+1 := Finset.card_insert_le _ _
         _≤({e 1} : Finset E).card+1+1 := Nat.add_le_add_right (Finset.card_insert_le _ _) _
         _=3 := by simp
  change Nat.card {g // N.crosses (fun v => S v ∧ T v) g}≤3
  omega

/-- Under the ambient cyclic-cut condition, a full-cross four-pole side is bridgeless. -/
theorem side_bridgeless (S : V → Prop) (e : Fin 4 → E) (x y : Fin 4 → V)
    (hmin : ∀T,N.IsCyclicCut T → 4≤N.cutSize T)
    (hcover : ∀g,N.crosses S g → ∃i,g=e i)
    (hjoins : ∀i,N.Joins (e i) (x i) (y i))
    (hx : ∀i,S (x i)) (hy : ∀i,¬S (y i))
    (hpole : (N.sub (N.inside S)).IsWeakPole)
    (hport₀ : (N.sub (N.inside S)).IsPort (x 0))
    (hport₂ : (N.sub (N.inside S)).IsPort (x 2))
    (hfull : ∀i j : Fin 4,i.val<2 → 2≤j.val →
      (N.sub (N.inside S)).IsFullPair (x i) (x j)) :
    (N.sub (N.inside S)).IsBridgeless := by
  classical
  rcases FourFullBridge.bridgeless_or_cyclic_bridge (N.sub (N.inside S)) hpole hport₀ hport₂
    (hfull 0 2 (by decide) (by decide)) (hfull 1 2 (by decide) (by decide))
    (hfull 0 3 (by decide) (by decide)) with hb | ⟨T,f,hcyc,_,h₀,h₁,h₂,h₃,hf⟩
  · exact hb
  · have hports : ∀i : Fin 4,T (x i) → i=0 ∨ i=1 := by
      intro i hi
      fin_cases i <;> simp_all
    have hsmall := intersection_cut_le_three N S T e x y hcover hjoins hx hy hports f hf
    have hlarge := hmin _ (cyclic_intersection N S T hcyc)
    omega

end Erdos1016.ExactMaximumSupport.FourPoleBridgeLift
