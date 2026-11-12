import Erdos1016.ExactMaximumSupport.LargeGirth.PackingLocalSpaces
import Erdos1016.CycleSpace.Graphical.ExceptionalPartners
import Erdos1016.Graph.Multigraph.Forest

set_option autoImplicit false
set_option maxHeartbeats 1500000

/-! Shared local parity forces two actual terminal branches after deletion. -/
noncomputable section
open scoped BigOperators
namespace Erdos1016.ExactMaximumSupport.LargeGirth.PackingLocalSpaces
open FiniteMultiGraph ExceptionalPartners
local instance relevanceDecidable (p : Prop) : Decidable p := Classical.propDecidable p

abbrev Outside (Q : FiniteMultiGraph) (A : Finset Q.Vertex) := {v : Q.Vertex // v∉A}
def exterior (Q : FiniteMultiGraph) (A : Finset Q.Vertex) : SimpleGraph (Outside Q A) :=
  Q.toSimpleGraph.induce {v | v∉A}

def IsFoot (Q : FiniteMultiGraph) (A : Finset Q.Vertex) (u : Q.Vertex) : Prop :=
  u∉A ∧ ∃ a∈A, Q.toSimpleGraph.Adj u a

def feet (Q : FiniteMultiGraph) (A : Finset Q.Vertex) : Finset (Outside Q A) :=
  Finset.univ.filter fun u => IsFoot Q A u.1

def inComponent (Q : FiniteMultiGraph) (A : Finset Q.Vertex) (v : Outside Q A)
    (u : Q.Vertex) : Prop := ∃ hu : u∉A, (exterior Q A).Reachable v ⟨u,hu⟩

theorem inComponent_self (Q : FiniteMultiGraph) (A : Finset Q.Vertex) (v : Outside Q A) :
    inComponent Q A v v.1 := ⟨v.2,SimpleGraph.Reachable.refl _⟩

theorem exterior_edge_reachable (Q : FiniteMultiGraph) (A : Finset Q.Vertex)
    (e : Q.Edge) (hs : Q.src e∉A) (ht : Q.dst e∉A) :
    (exterior Q A).Reachable ⟨Q.src e,hs⟩ ⟨Q.dst e,ht⟩ := by
  by_cases he : Q.src e = Q.dst e
  · have h : (⟨Q.src e,hs⟩ : Outside Q A) = ⟨Q.dst e,ht⟩ := Subtype.ext he
    rw [h]
  · exact (show (exterior Q A).Adj ⟨Q.src e,hs⟩ ⟨Q.dst e,ht⟩ from
      ⟨he,e,Or.inl ⟨rfl,rfl⟩⟩).reachable

theorem inComponent_edge_iff (Q : FiniteMultiGraph) (A : Finset Q.Vertex)
    (v : Outside Q A) (e : Q.Edge) (hs : Q.src e∉A) (ht : Q.dst e∉A) :
    inComponent Q A v (Q.src e) ↔ inComponent Q A v (Q.dst e) := by
  have hr := exterior_edge_reachable Q A e hs ht
  exact ⟨fun ⟨_,h⟩ => ⟨ht,h.trans hr⟩,fun ⟨_,h⟩ => ⟨hs,h.trans hr.symm⟩⟩

def potentialDual (Q : FiniteMultiGraph) (p : Q.Vertex → F₂) : DualWord Q :=
  (∑ v, p v • (LinearMap.proj v : Q.Demand →ₗ[F₂] F₂)).comp Q.boundary

theorem coefficient_potentialDual (Q : FiniteMultiGraph) (p : Q.Vertex → F₂) (e : Q.Edge) :
    coefficient Q (potentialDual Q p) e = p (Q.src e)+p (Q.dst e) := by
  unfold coefficient potentialDual
  rw [LinearMap.comp_apply,Q.boundary_singleEdge,map_add]
  simp [FiniteMultiGraph.vertexUnit,Pi.single_apply]

theorem potentialDual_cycle (Q : FiniteMultiGraph) (p : Q.Vertex → F₂) (x : Q.CycleSpace) :
    potentialDual Q p x.1 = 0 := by
  change (∑ v, p v • (LinearMap.proj v : Q.Demand →ₗ[F₂] F₂)) (Q.boundary x.1) = 0
  rw [x.2,map_zero]

/-- The potential is constant along edges away from both coordinate supports. -/
theorem potential_edge_eq (Q : FiniteMultiGraph) (A : Finset Q.Vertex) (v : Q.Vertex)
    (fv fa : DualWord Q) (p : Q.Vertex → F₂)
    (hfv : ∀ e, e∉starEdges Q v → coefficient Q fv e=0)
    (hfa : ∀ e, e∉touchedEdges Q A → coefficient Q fa e=0)
    (hp : ∀ e, coefficient Q fv e+coefficient Q fa e=p (Q.src e)+p (Q.dst e))
    (e : Q.Edge) (hs : Q.src e∉A) (ht : Q.dst e∉A)
    (hsv : Q.src e≠v) (htv : Q.dst e≠v) : p (Q.src e)=p (Q.dst e) := by
  have h := hp e
  rw [hfv e (by simp [starEdges,hsv,htv]),hfa e (by simp [touchedEdges,hs,ht]),add_zero] at h
  have he := congrArg (fun z => z+p (Q.dst e)) h
  simpa [add_assoc,CharTwo.add_self_eq_zero] using he.symm

/-- Every bit shift of the potential has a nonzero boundary foot in the
component of the relevant vertex. This uses the actual cut annihilator. -/
theorem exists_foot_of_shared_potential (Q : FiniteMultiGraph) (A : Finset Q.Vertex)
    (v : Outside Q A) (hnotfoot : ¬ IsFoot Q A v.1)
    (f : DualCycle Q) (fv fa : DualWord Q) (p : Q.Vertex → F₂)
    (hf : f≠0) (hval : ∀ x : Q.CycleSpace, fv x.1=f x)
    (hfv : ∀ e, e∉starEdges Q v.1 → coefficient Q fv e=0)
    (hfa : ∀ e, e∉touchedEdges Q A → coefficient Q fa e=0)
    (hp : ∀ e, coefficient Q fv e+coefficient Q fa e=p (Q.src e)+p (Q.dst e))
    (c : F₂) :
    ∃ u : Outside Q A, IsFoot Q A u.1 ∧ (exterior Q A).Reachable v u ∧ p u.1+c≠0 := by
  by_contra hnone
  push_neg at hnone
  let σ : Q.Vertex → F₂ := fun u => if inComponent Q A v u then p u+c else 0
  have hzeroA (u : Q.Vertex) (hu : u∈A) : σ u=0 := by
    have h : ¬ inComponent Q A v u := fun ⟨hn,_⟩ => hn hu
    simp [σ,h]
  have hzerofoot (u : Q.Vertex) (hu : IsFoot Q A u) : σ u=0 := by
    by_cases hc : inComponent Q A v u
    · obtain ⟨hn,hr⟩ := hc
      simp only [σ,if_pos (show inComponent Q A v u from ⟨hn,hr⟩)]
      exact hnone ⟨u,hn⟩ hu hr
    · simp [σ,hc]
  have hedge : ∀ e, coefficient Q fv e=σ (Q.src e)+σ (Q.dst e) := by
    intro e
    by_cases hA : e∈touchedEdges Q A
    · have ht : Q.src e∈A ∨ Q.dst e∈A := (Finset.mem_filter.mp hA).2
      have hnstar : e∉starEdges Q v.1 := by
        simp only [starEdges,Finset.mem_filter,Finset.mem_univ,true_and,not_or]
        constructor
        · intro he
          rcases ht with hs | hd
          · exact v.2 (he ▸ hs)
          · apply hnotfoot
            exact ⟨v.2,Q.dst e,hd,⟨fun hv => v.2 (hv ▸ hd),e,Or.inl ⟨he,rfl⟩⟩⟩
        · intro he
          rcases ht with hs | hd
          · apply hnotfoot
            exact ⟨v.2,Q.src e,hs,⟨fun hv => v.2 (hv ▸ hs),e,Or.inr ⟨rfl,he⟩⟩⟩
          · exact v.2 (he ▸ hd)
      rw [hfv e hnstar]
      rcases ht with hs | hd
      · rw [hzeroA _ hs]
        by_cases hd : Q.dst e∈A
        · rw [hzeroA _ hd]; rfl
        · rw [hzerofoot _ ⟨hd,Q.src e,hs,
            ⟨fun he => hd (he ▸ hs),e,Or.inr ⟨rfl,rfl⟩⟩⟩]; rfl
      · rw [hzeroA _ hd]
        by_cases hs : Q.src e∈A
        · rw [hzeroA _ hs]; rfl
        · rw [hzerofoot _ ⟨hs,Q.dst e,hd,
            ⟨fun he => hs (he ▸ hd),e,Or.inl ⟨rfl,rfl⟩⟩⟩]; rfl
    · have hs : Q.src e∉A := by simpa [touchedEdges] using (not_or.mp (by simpa [touchedEdges] using hA)).1
      have ht : Q.dst e∉A := by simpa [touchedEdges] using (not_or.mp (by simpa [touchedEdges] using hA)).2
      have hcoef := hp e
      rw [hfa e hA,add_zero] at hcoef
      have hsame := inComponent_edge_iff Q A v e hs ht
      by_cases hc : inComponent Q A v (Q.src e)
      · rw [hcoef]
        simp only [σ,if_pos hc,if_pos (hsame.mp hc)]
        have hh : c+c=0 := CharTwo.add_self_eq_zero c
        linear_combination -hh
      · have hd : ¬ inComponent Q A v (Q.dst e) := fun h => hc (hsame.mpr h)
        have hsv : Q.src e≠v.1 := fun he => hc (he ▸ inComponent_self Q A v)
        have htv : Q.dst e≠v.1 := fun he => hd (he ▸ inComponent_self Q A v)
        rw [hfv e (by simp [starEdges,hsv,htv])]
        simp [σ,hc,hd]
  have heq : fv=potentialDual Q σ := dualWord_ext Q (fun e =>
    (hedge e).trans (coefficient_potentialDual Q σ e).symm)
  apply hf
  ext x
  rw [← hval x,heq,potentialDual_cycle]
  rfl

/-- The shared potential is constant on each component after deleting `A` and `v`. -/
theorem potential_eq_on_deleted_component (Q : FiniteMultiGraph) (A : Finset Q.Vertex)
    (v : Outside Q A) (fv fa : DualWord Q) (p : Q.Vertex → F₂)
    (hfv : ∀ e, e∉starEdges Q v.1 → coefficient Q fv e=0)
    (hfa : ∀ e, e∉touchedEdges Q A → coefficient Q fa e=0)
    (hp : ∀ e, coefficient Q fv e+coefficient Q fa e=p (Q.src e)+p (Q.dst e))
    {u w : DeletedVertex v}
    (hcomp : (deleted (exterior Q A) v).connectedComponentMk u =
      (deleted (exterior Q A) v).connectedComponentMk w) : p u.1.1=p w.1.1 := by
  have hadj {a b : DeletedVertex v} (hab : (deleted (exterior Q A) v).Adj a b) :
      p a.1.1=p b.1.1 := by
    change Q.toSimpleGraph.Adj a.1.1 b.1.1 at hab
    have ha : a.1.1≠v.1 := fun h => a.2 (Subtype.ext h)
    have hb : b.1.1≠v.1 := fun h => b.2 (Subtype.ext h)
    obtain ⟨_,e,he | he⟩ := hab
    · simpa only [he.1,he.2] using potential_edge_eq Q A v.1 fv fa p hfv hfa hp e
        (by simpa [he.1] using a.1.2) (by simpa [he.2] using b.1.2)
        (by simpa [he.1] using ha) (by simpa [he.2] using hb)
    · symm
      simpa only [he.1,he.2] using potential_edge_eq Q A v.1 fv fa p hfv hfa hp e
        (by simpa [he.1] using b.1.2) (by simpa [he.2] using a.1.2)
        (by simpa [he.1] using hb) (by simpa [he.2] using ha)
  obtain ⟨q⟩ := SimpleGraph.ConnectedComponent.exact hcomp
  induction q with
  | nil => rfl
  | cons h q ih => exact (hadj h).trans (ih (SimpleGraph.ConnectedComponent.sound q.reachable))

/-- Step 1 of Strings, on the actual labelled cycle space. No connectivity
or simplicity hypothesis is needed for this local implication. -/
theorem relevant_terminalBranch_card (Q : FiniteMultiGraph) (A : Finset Q.Vertex)
    (v : Outside Q A) (hr : Relevant Q A v.1) (hnotfoot : ¬ IsFoot Q A v.1) :
    2 ≤ Nat.card (TerminalBranch (exterior Q A) (feet Q A) v) := by
  obtain ⟨f,fv,fa,p,hf,hval,hfv,hfa,hp⟩ := relevant_witness Q A v.1 hr
  obtain ⟨u,hu,hr_u,_⟩ := exists_foot_of_shared_potential Q A v hnotfoot
    f fv fa p hf hval hfv hfa hp 0
  obtain ⟨w,hw,hr_w,hwbit⟩ := exists_foot_of_shared_potential Q A v hnotfoot
    f fv fa p hf hval hfv hfa hp (p u.1)
  have huv : u≠v := fun h => hnotfoot (h ▸ hu)
  have hwv : w≠v := fun h => hnotfoot (h ▸ hw)
  let u' : DeletedVertex v := ⟨u,huv⟩
  let w' : DeletedVertex v := ⟨w,hwv⟩
  let cu : TerminalBranch (exterior Q A) (feet Q A) v :=
    ⟨(deleted (exterior Q A) v).connectedComponentMk u',
      ⟨u',by simp [feet,u',hu],rfl,hr_u⟩⟩
  let cw : TerminalBranch (exterior Q A) (feet Q A) v :=
    ⟨(deleted (exterior Q A) v).connectedComponentMk w',
      ⟨w',by simp [feet,w',hw],rfl,hr_w⟩⟩
  have hne : cu≠cw := by
    intro he
    have hh := potential_eq_on_deleted_component Q A v fv fa p hfv hfa hp
      (congrArg Subtype.val he)
    apply hwbit
    change p u.1=p w.1 at hh
    rw [← hh,CharTwo.add_self_eq_zero]
  letI : Nontrivial (TerminalBranch (exterior Q A) (feet Q A) v) := ⟨⟨cu,cw,hne⟩⟩
  have h := Fintype.one_lt_card_iff_nontrivial.mpr
    (inferInstance : Nontrivial (TerminalBranch (exterior Q A) (feet Q A) v))
  simpa only [Nat.card_eq_fintype_card] using h

/-- Each foot has an actual crossing physical label. -/
theorem foot_edge (Q : FiniteMultiGraph) (A : Finset Q.Vertex) (u : Outside Q A)
    (hu : IsFoot Q A u.1) :
    ∃ e : Q.Edge, e∈Q.cutEdges A ∧ (Q.src e=u.1 ∨ Q.dst e=u.1) := by
  obtain ⟨_,a,ha,_,e,he | he⟩ := hu
  · exact ⟨e,by simp [cutEdges,he.1,he.2,u.2,ha],Or.inl he.1⟩
  · exact ⟨e,by simp [cutEdges,he.1,he.2,u.2,ha],Or.inr he.2⟩

/-- Several parallel terminals may have the same foot. Their physical
multiplicity can only increase the boundary count. -/
theorem feet_card_le_cut (Q : FiniteMultiGraph) (A : Finset Q.Vertex) :
    (feet Q A).card ≤ (Q.cutEdges A).card := by
  let F := {u : Outside Q A // u∈feet Q A}
  have hex (u : F) : ∃ e : Q.Edge, e∈Q.cutEdges A ∧
      (Q.src e=u.1.1 ∨ Q.dst e=u.1.1) :=
    foot_edge Q A u.1 ((Finset.mem_filter.mp u.2).2)
  choose e he hu using hex
  let f : F → {e : Q.Edge // e∈Q.cutEdges A} := fun u => ⟨e u,he u⟩
  have hinj : Function.Injective f := by
    intro u w h
    have hw : e u=e w := congrArg Subtype.val h
    have hc : (Q.src (e u)∈A ∧ Q.dst (e u)∉A) ∨
        (Q.src (e u)∉A ∧ Q.dst (e u)∈A) := (Finset.mem_filter.mp (he u)).2
    have huv := hu u
    have hwv := hu w
    rw [← hw] at hwv
    apply Subtype.ext
    apply Subtype.ext
    rcases huv with hs | ht <;> rcases hwv with hs' | ht'
    · exact hs.symm.trans hs'
    · exfalso
      rcases hc with hc | hc
      · exact u.1.2 (hs ▸ hc.1)
      · exact w.1.2 (ht' ▸ hc.2)
    · exfalso
      rcases hc with hc | hc
      · exact w.1.2 (hs' ▸ hc.1)
      · exact u.1.2 (ht ▸ hc.2)
    · exact ht.symm.trans ht'
  simpa [F] using Fintype.card_le_of_injective f hinj

/-- Interface for maximal direct-sum selection. -/
theorem terminalBranch_card_of_not_disjoint (Q : FiniteMultiGraph) (A : Finset Q.Vertex)
    (v : Outside Q A)
    (hr : ¬ Disjoint (localSpace Q v.1) (A.sup (localSpace Q)))
    (hnotfoot : v∉feet Q A) :
    2 ≤ Nat.card (TerminalBranch (exterior Q A) (feet Q A) v) := by
  apply relevant_terminalBranch_card Q A v
  · rw [← markedSpace_eq_sup] at hr
    exact fun h => hr (disjoint_iff.mpr h)
  · intro hf
    exact hnotfoot (by simp [feet,hf])

end Erdos1016.ExactMaximumSupport.LargeGirth.PackingLocalSpaces
