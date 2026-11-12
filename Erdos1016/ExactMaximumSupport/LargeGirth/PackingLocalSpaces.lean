import Erdos1016.Graph.Multigraph.BoundaryImage
import Erdos1016.Probability.Cylinders.FeasibleSelection
import Mathlib.LinearAlgebra.Dual.Lemmas

set_option autoImplicit false
set_option maxHeartbeats 800000

/-!
# Local parity spaces on labelled multigraphs

The coordinate spaces retain parallel edge labels. The cut-cycle annihilator
is derived from the actual incidence boundary and finite-dimensional duality.
-/
noncomputable section
open scoped BigOperators
namespace Erdos1016.ExactMaximumSupport.LargeGirth.PackingLocalSpaces
open FiniteMultiGraph
local instance localSpacesDecidable (p : Prop) : Decidable p := Classical.propDecidable p

abbrev DualWord (Q : FiniteMultiGraph) := Q.EdgeWord →ₗ[F₂] F₂
abbrev DualCycle (Q : FiniteMultiGraph) := Q.CycleSpace →ₗ[F₂] F₂

/-- The coefficient at a physical edge label. -/
def coefficient (Q : FiniteMultiGraph) (f : DualWord Q) (e : Q.Edge) : F₂ :=
  f (Pi.single e 1)

theorem dualWord_ext (Q : FiniteMultiGraph) {f g : DualWord Q}
    (h : ∀ e, coefficient Q f e = coefficient Q g e) : f = g := by
  apply LinearMap.pi_ext
  intro e a
  have hs : Pi.single e a = a • (Pi.single e (1:F₂) : Q.EdgeWord) := by
    ext i
    simp [Pi.single_apply]
  rw [hs, map_smul, map_smul]
  exact congrArg (fun z : F₂ => a • z) (h e)

/-- Functionals supported on a set of physical coordinates. -/
def supportedDual (Q : FiniteMultiGraph) (S : Finset Q.Edge) : Submodule F₂ (DualWord Q) where
  carrier := {f | ∀ e, e ∉ S → coefficient Q f e = 0}
  zero_mem' := by intro e _; rfl
  add_mem' := by
    intro f g hf hg e he
    change coefficient Q f e + coefficient Q g e = 0
    rw [hf e he,hg e he,add_zero]
  smul_mem' := by
    intro a f hf e he
    change a • coefficient Q f e = 0
    rw [hf e he,smul_zero]

/-- Coordinate functionals restricted to the actual cycle space. -/
def coordinateSpace (Q : FiniteMultiGraph) (S : Finset Q.Edge) : Submodule F₂ (DualCycle Q) :=
  (supportedDual Q S).map Q.CycleSpace.subtype.dualMap

def starEdges (Q : FiniteMultiGraph) (v : Q.Vertex) : Finset Q.Edge :=
  Finset.univ.filter fun e => Q.src e = v ∨ Q.dst e = v

def touchedEdges (Q : FiniteMultiGraph) (A : Finset Q.Vertex) : Finset Q.Edge :=
  Finset.univ.filter fun e => Q.src e ∈ A ∨ Q.dst e ∈ A

abbrev localSpace (Q : FiniteMultiGraph) (v : Q.Vertex) := coordinateSpace Q (starEdges Q v)
abbrev markedSpace (Q : FiniteMultiGraph) (A : Finset Q.Vertex) := coordinateSpace Q (touchedEdges Q A)

def Relevant (Q : FiniteMultiGraph) (A : Finset Q.Vertex) (v : Q.Vertex) : Prop :=
  localSpace Q v ⊓ markedSpace Q A ≠ ⊥

def edgeDual (Q : FiniteMultiGraph) (e : Q.Edge) : DualWord Q := LinearMap.proj e

def edgeCoordinate (Q : FiniteMultiGraph) (e : Q.Edge) : DualCycle Q :=
  Q.CycleSpace.subtype.dualMap (edgeDual Q e)

theorem coefficient_edgeDual (Q : FiniteMultiGraph) (e d : Q.Edge) :
    coefficient Q (edgeDual Q e) d = if e=d then 1 else 0 := by
  simp [coefficient, edgeDual, Pi.single_apply]

theorem dualWord_sum (Q : FiniteMultiGraph) (f : DualWord Q) :
    f = ∑ e, coefficient Q f e • edgeDual Q e := by
  apply dualWord_ext Q
  intro d
  change _ = (∑ e, coefficient Q f e • edgeDual Q e) (Pi.single d 1)
  simp only [LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul]
  change _ = ∑ e, coefficient Q f e * coefficient Q (edgeDual Q e) d
  simp [coefficient_edgeDual]

theorem coordinateSpace_mono (Q : FiniteMultiGraph) {S T : Finset Q.Edge} (h : S⊆T) :
    coordinateSpace Q S ≤ coordinateSpace Q T := by
  rintro f ⟨φ,hφ,rfl⟩
  exact ⟨φ,fun e he => hφ e (fun hs => he (h hs)),rfl⟩

theorem edgeCoordinate_mem (Q : FiniteMultiGraph) (S : Finset Q.Edge)
    (e : Q.Edge) (he : e∈S) : edgeCoordinate Q e ∈ coordinateSpace Q S := by
  refine ⟨edgeDual Q e, ?_, rfl⟩
  intro d hd
  rw [coefficient_edgeDual, if_neg]
  exact fun hed => hd (hed ▸ he)

/-- The construction is exactly the span of the named coordinate functionals. -/
theorem coordinateSpace_eq_span (Q : FiniteMultiGraph) (S : Finset Q.Edge) :
    coordinateSpace Q S = Submodule.span F₂ {f | ∃e∈S,f=edgeCoordinate Q e} := by
  apply le_antisymm
  · rintro f ⟨φ,hφ,hf⟩
    rw [← hf,dualWord_sum Q φ,map_sum]
    apply Submodule.sum_mem
    intro e _
    rw [map_smul]
    by_cases he : e∈S
    · apply Submodule.smul_mem
      exact Submodule.subset_span ⟨e,he,rfl⟩
    · rw [hφ e he,zero_smul]
      exact Submodule.zero_mem _
  · apply Submodule.span_le.mpr
    rintro f ⟨e,he,rfl⟩
    exact edgeCoordinate_mem Q S e he

/-- The marked coordinate space is the sum of the actual local spaces. -/
theorem markedSpace_eq_sup (Q : FiniteMultiGraph) (A : Finset Q.Vertex) :
    markedSpace Q A = A.sup (localSpace Q) := by
  apply le_antisymm
  · rintro f ⟨φ,hφ,hf⟩
    rw [← hf, dualWord_sum Q φ, map_sum]
    apply Submodule.sum_mem
    intro e _
    rw [map_smul]
    by_cases he : e∈touchedEdges Q A
    · have he' : Q.src e∈A ∨ Q.dst e∈A := (Finset.mem_filter.mp he).2
      rcases he' with hs | ht
      · exact (show localSpace Q (Q.src e) ≤ A.sup (localSpace Q) from Finset.le_sup hs) ((localSpace Q (Q.src e)).smul_mem _
          (edgeCoordinate_mem Q _ e (by simp [starEdges])))
      · exact (show localSpace Q (Q.dst e) ≤ A.sup (localSpace Q) from Finset.le_sup ht) ((localSpace Q (Q.dst e)).smul_mem _
          (edgeCoordinate_mem Q _ e (by simp [starEdges])))
    · rw [hφ e he,zero_smul]
      exact Submodule.zero_mem _
  · apply Finset.sup_le
    intro v hv
    apply coordinateSpace_mono Q
    intro e he
    simp only [starEdges,Finset.mem_filter,Finset.mem_univ,true_and] at he
    simp only [touchedEdges,Finset.mem_filter,Finset.mem_univ,true_and]
    rcases he with he | he
    · exact Or.inl (he ▸ hv)
    · exact Or.inr (he ▸ hv)

/-- A linear functional annihilating every even word is an incidence coboundary. -/
theorem exists_potential_of_annihilates (Q : FiniteMultiGraph) (f : DualWord Q)
    (hf : ∀ x : Q.CycleSpace, f x.1 = 0) :
    ∃ p : Q.Vertex → F₂, ∀ e, coefficient Q f e = p (Q.src e) + p (Q.dst e) := by
  have hm : f ∈ (LinearMap.ker Q.boundary).dualAnnihilator := by
    rw [Submodule.mem_dualAnnihilator]
    intro x hx
    exact hf ⟨x,hx⟩
  rw [← LinearMap.range_dualMap_eq_dualAnnihilator_ker] at hm
  obtain ⟨ψ,hψ⟩ := hm
  refine ⟨fun v => ψ (Q.vertexUnit v), ?_⟩
  intro e
  change f (Pi.single e 1) = _
  rw [← hψ]
  change ψ (Q.boundary (Pi.single e 1)) = _
  rw [Q.boundary_singleEdge, map_add]

/-- A nonzero shared local functional supplies an actual cut potential.
Its coefficients vanish away from the two specified coordinate supports. -/
theorem relevant_witness (Q : FiniteMultiGraph) (A : Finset Q.Vertex) (v : Q.Vertex)
    (hr : Relevant Q A v) :
    ∃ f : DualCycle Q, ∃ fv fa : DualWord Q, ∃ p : Q.Vertex → F₂,
      f ≠ 0 ∧
      (∀ x : Q.CycleSpace, fv x.1 = f x) ∧
      (∀ e, e ∉ starEdges Q v → coefficient Q fv e = 0) ∧
      (∀ e, e ∉ touchedEdges Q A → coefficient Q fa e = 0) ∧
      (∀ e, coefficient Q fv e + coefficient Q fa e = p (Q.src e) + p (Q.dst e)) := by
  obtain ⟨f,hf,hne⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hr
  obtain ⟨fv,hfv,heqv⟩ := hf.1
  obtain ⟨fa,hfa,heqa⟩ := hf.2
  have hv (x : Q.CycleSpace) : fv x.1 = f x := congrArg (fun z : DualCycle Q => z x) heqv
  have ha (x : Q.CycleSpace) : fa x.1 = f x := congrArg (fun z : DualCycle Q => z x) heqa
  obtain ⟨p,hp⟩ := exists_potential_of_annihilates Q (fv+fa) (by
    intro x
    change fv x.1 + fa x.1 = 0
    rw [hv,ha]
    exact CharTwo.add_self_eq_zero _)
  exact ⟨f,fv,fa,p,hne,hv,hfv,hfa,hp⟩

end Erdos1016.ExactMaximumSupport.LargeGirth.PackingLocalSpaces
