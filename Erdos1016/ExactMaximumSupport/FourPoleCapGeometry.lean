import Erdos1016.ExactMaximumSupport.FourPoleCaps

set_option autoImplicit false
set_option maxHeartbeats 1500000

/-!
# The actual pole and bridge properties of two caps

All original labels remain present. Isolated original vertices are permitted.
-/
noncomputable section
namespace Erdos1016.ExactMaximumSupport.FourPoleCaps
open BoundaryTrace BoundaryTrace.Network BoundaryDecay
variable {V E : Type*} [Fintype V] [Fintype E] (N : Network V E)

/-- An old port survives a cap exactly when it is not one of the capped ports. -/
theorem port_some_iff (a b : V) (hab : a≠b) (ha : N.IsPort a) (hb : N.IsPort b) (v : V) :
    (N.addVertex a b).IsPort (some v) ↔ N.IsPort v ∧ v≠a ∧ v≠b := by
  classical
  change (N.addVertex a b).deg (fun _ => 1) (some v)=2 ↔
    N.deg (fun _ => 1) v=2 ∧ v≠a ∧ v≠b
  rw [N.deg_addVertex_some]
  by_cases hva : v=a
  · subst v
    simp [hab,show N.deg (fun _ => 1) a=2 from ha]
  by_cases hvb : v=b
  · subst v
    simp [Ne.symm hab,show N.deg (fun _ => 1) b=2 from hb]
  simp [hva,hvb]

/-- Adding a cap to the ends of an actual path preserves bridgelessness. -/
theorem bridgeless_addVertex_of_path (a b : V) (hbl : N.IsBridgeless)
    {P : N.Word} (hP : N.IsPathWord a b P) : (N.addVertex a b).IsBridgeless := by
  classical
  intro e
  rcases e with e | c
  · obtain ⟨z,hz,he⟩ := hbl e
    exact ⟨(N.addVertexEmbed a b).push z,
      ((N.addVertexEmbed a b).isCycleWord_push_iff z).mpr hz,
      by simpa only [N.addVertex_push_inl] using he⟩
  · refine ⟨(N.addVertexEmbed a b).push P+unitWord (Sum.inr true)+unitWord (Sum.inr false),
      N.isCycleWord_addVertex a b hP,?_⟩
    cases c <;> simp [Pi.add_apply,N.addVertex_push_inr,unitWord_apply]

/-- Distinct ports of a weak pole are joined by an actual physical path. -/
theorem path_between_ports (a b : V) (hN : N.IsWeakPole) (hab : a≠b)
    (ha : N.IsPort a) (hb : N.IsPort b) : ∃P : N.Word,N.IsPathWord a b P := by
  classical
  have hra := hN.2 a b (by change 0<N.deg (fun _ => 1) a; rw [ha]; omega)
    (by change 0<N.deg (fun _ => 1) b; rw [hb]; omega)
  obtain ⟨P,hP,_⟩ := N.exists_isPathWord_of_reachable (fun _ => True) hab
    (N.reachable_sub_of_forall (fun _ => True.intro) hra)
  exact ⟨P,hP⟩

/-- A physical cap between two distinct ports preserves bridgelessness. -/
theorem bridgeless_addVertex (a b : V) (hN : N.IsWeakPole) (hbl : N.IsBridgeless)
    (hab : a≠b) (ha : N.IsPort a) (hb : N.IsPort b) : (N.addVertex a b).IsBridgeless := by
  obtain ⟨P,hP⟩ := path_between_ports N a b hN hab ha hb
  exact bridgeless_addVertex_of_path N a b hbl hP

/-- Two caps leave precisely their two new vertices as ports. -/
theorem weak_two_pole (a b c d : V) (hN : N.IsWeakPole)
    (hab : a≠b) (hac : a≠c) (had : a≠d) (hbc : b≠c) (hbd : b≠d) (hcd : c≠d)
    (ha : N.IsPort a) (hb : N.IsPort b) (hc : N.IsPort c) (hd : N.IsPort d)
    (honly : ∀v,N.IsPort v → v=a ∨ v=b ∨ v=c ∨ v=d) :
    (capped N a b c d).IsWeakTwoPole left right := by
  classical
  have hc' := N.isPort_addVertex_some a b hac.symm hbc.symm hc
  have hd' := N.isPort_addVertex_some a b had.symm hbd.symm hd
  have hcd' : (some c : Option V)≠some d := fun h => hcd (Option.some.inj h)
  have hN' := N.isWeakPole_addVertex a b hN hab ha hb
  refine ⟨(N.addVertex a b).isWeakPole_addVertex (some c) (some d) hN' hcd' hc' hd',
    ?_,(N.addVertex a b).isPort_addVertex_none (some c) (some d),by simp [left,right],?_⟩
  · exact (N.addVertex a b).isPort_addVertex_some (some c) (some d)
      (by simp) (by simp) (N.isPort_addVertex_none a b)
  · rintro (_ | (_ | v)) hv
    · exact Or.inr rfl
    · exact Or.inl rfl
    · have h₁ := (port_some_iff (N.addVertex a b) (some c) (some d) hcd' hc' hd' (some v)).mp hv
      have h₂ := (port_some_iff N a b hab ha hb v).mp h₁.1
      rcases honly v h₂.1 with h | h | h | h
      · exact (h₂.2.1 h).elim
      · exact (h₂.2.2 h).elim
      · exact (h₁.2.1 (congrArg some h)).elim
      · exact (h₁.2.2 (congrArg some h)).elim

/-- Both actual caps preserve bridgelessness of the original four-pole. -/
theorem capped_bridgeless (a b c d : V) (hN : N.IsWeakPole) (hbl : N.IsBridgeless)
    (hab : a≠b) (hac : a≠c) (had : a≠d) (hbc : b≠c) (hbd : b≠d) (hcd : c≠d)
    (ha : N.IsPort a) (hb : N.IsPort b) (hc : N.IsPort c) (hd : N.IsPort d) :
    (capped N a b c d).IsBridgeless := by
  exact bridgeless_addVertex (N.addVertex a b) (some c) (some d)
    (N.isWeakPole_addVertex a b hN hab ha hb)
    (bridgeless_addVertex N a b hN hbl hab ha hb)
    (fun h => hcd (Option.some.inj h))
    (N.isPort_addVertex_some a b hac.symm hbc.symm hc)
    (N.isPort_addVertex_some a b had.symm hbd.symm hd)

end Erdos1016.ExactMaximumSupport.FourPoleCaps
