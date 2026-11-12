import Erdos1016.ExactMaximumSupport.LargeGirth.PackingLocalSpaces
import Erdos1016.Graph.Multigraph.RegionDegrees
import Erdos1016.CycleSpace.Graphical.MultigraphCutCorrelation

set_option autoImplicit false
set_option maxHeartbeats 1000000

/-! Exact zero-coordinate probabilities and the local parity dimension bound. -/
noncomputable section
open scoped BigOperators
namespace Erdos1016.ExactMaximumSupport.LargeGirth.PackingLocalSpaces
open FiniteMultiGraph
local instance localProbabilityDecidable (p : Prop) : Decidable p := Classical.propDecidable p

def restrictWord (Q : FiniteMultiGraph) (S : Finset Q.Edge) :
    Q.EdgeWord →ₗ[F₂] (S → F₂) where
  toFun x e := x e.1
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem coordinateSpace_eq_dual_range (Q : FiniteMultiGraph) (S : Finset Q.Edge) :
    coordinateSpace Q S = LinearMap.range (Q.observeEdges S).dualMap := by
  apply le_antisymm
  · rw [LinearMap.range_dualMap_eq_dualAnnihilator_ker]
    rintro f ⟨φ,hφ,hf⟩
    rw [Submodule.mem_dualAnnihilator]
    intro x hx
    have hx' (e : S) : x.1 e.1=0 := congrFun hx e
    rw [← hf]
    change φ x.1=0
    rw [dualWord_sum Q φ]
    simp only [LinearMap.sum_apply,LinearMap.smul_apply]
    apply Finset.sum_eq_zero
    intro e _
    by_cases he : e∈S
    · change coefficient Q φ e • x.1 e=0
      rw [hx' ⟨e,he⟩,smul_zero]
    · rw [hφ e he,zero_smul]
  · rintro f ⟨ψ,rfl⟩
    refine ⟨ψ.comp (restrictWord Q S),?_,rfl⟩
    intro e he
    change ψ (restrictWord Q S (Pi.single e 1))=0
    have hz : restrictWord Q S (Pi.single e 1)=0 := by
      ext d
      change (Pi.single e (1:F₂) : Q.EdgeWord) d.1=0
      exact Pi.single_eq_of_ne (fun h : d.1=e => he (h ▸ d.2)) _
    rw [hz,map_zero]

theorem coordinateSpace_finrank (Q : FiniteMultiGraph) (S : Finset Q.Edge) :
    Module.finrank F₂ (coordinateSpace Q S) =
      Module.finrank F₂ (LinearMap.range (Q.observeEdges S)) := by
  rw [coordinateSpace_eq_dual_range,LinearMap.finrank_range_dualMap_eq_finrank_range]

/-- Vanishing of the dual space is exactly the literal zero-coordinate event. -/
theorem coordinateSpace_zero_iff (Q : FiniteMultiGraph) (S : Finset Q.Edge) (x : Q.CycleSpace) :
    (∀ f∈coordinateSpace Q S, f x=0) ↔ ∀e∈S,x.1 e=0 := by
  constructor
  · intro h e he
    exact h (edgeCoordinate Q e) (edgeCoordinate_mem Q S e he)
  · intro h f hf
    rw [coordinateSpace_eq_dual_range] at hf
    obtain ⟨ψ,rfl⟩ := hf
    change ψ (Q.observeEdges S x)=0
    have hz : Q.observeEdges S x=0 := by ext e; exact h e.1 e.2
    rw [hz,map_zero]

theorem zeroCoordinates_probability (Q : FiniteMultiGraph) (S : Finset Q.Edge) :
    Finite.density (fun x : Q.CycleSpace => ∀e∈S,x.1 e=0) =
      1/(2:ℝ)^Module.finrank F₂ (coordinateSpace Q S) := by
  rw [coordinateSpace_finrank]
  have he : Q.MatchesSeed S 0 = fun x : Q.CycleSpace => ∀e∈S,x.1 e=0 := by
    funext x
    apply propext
    constructor
    · intro h e he
      exact congrFun h ⟨e,he⟩
    · intro h
      ext e
      exact h e.1 e.2
  simpa only [he] using Q.matchesSeed_probability S 0

def ZeroStar (Q : FiniteMultiGraph) (v : Q.Vertex) (x : Q.CycleSpace) : Prop :=
  ∀e∈starEdges Q v,x.1 e=0

theorem zeroStar_probability (Q : FiniteMultiGraph) (v : Q.Vertex) :
    Finite.density (ZeroStar Q v) = 1/(2:ℝ)^Module.finrank F₂ (localSpace Q v) :=
  zeroCoordinates_probability Q (starEdges Q v)

theorem starEdges_card (Q : FiniteMultiGraph) (v : Q.Vertex)
    (hloop : ∀e,Q.src e≠Q.dst e) : (starEdges Q v).card=Q.degree v := by
  have hi : Q.internalEdges {v}=∅ := by
    ext e
    simp only [internalEdges,Finset.mem_filter,Finset.mem_univ,true_and,
      Finset.mem_singleton,Finset.not_mem_empty,iff_false,not_and]
    intro hs hd
    exact hloop e (hs.trans hd.symm)
  have hc : Q.cutEdges {v}=starEdges Q v := by
    ext e
    simp only [cutEdges,starEdges,Finset.mem_filter,Finset.mem_univ,true_and,Finset.mem_singleton]
    have hh : ¬(Q.src e=v ∧ Q.dst e=v) := fun h => hloop e (h.1.trans h.2.symm)
    tauto
  have hd := Q.sum_region_degree {v}
  simpa [hi,hc] using hd.symm

def starTotal (Q : FiniteMultiGraph) (v : Q.Vertex) : (starEdges Q v → F₂) →ₗ[F₂] F₂ :=
  ∑ e, LinearMap.proj e

theorem observe_star_total (Q : FiniteMultiGraph) (v : Q.Vertex)
    (hloop : ∀e,Q.src e≠Q.dst e) (x : Q.CycleSpace) :
    starTotal Q v (Q.observeEdges (starEdges Q v) x)=0 := by
  have hb := congrFun x.2 v
  change (∑ e, ((if Q.src e=v then x.1 e else 0)+
    (if Q.dst e=v then x.1 e else 0)))=0 at hb
  change (∑ e, (LinearMap.proj e : (starEdges Q v → F₂) →ₗ[F₂] F₂))
    (Q.observeEdges (starEdges Q v) x)=0
  simp only [LinearMap.sum_apply,LinearMap.proj_apply,observeEdges,LinearMap.coe_mk,AddHom.coe_mk]
  rw [Finset.sum_coe_sort]
  change (∑ e∈starEdges Q v,x.1 e)=0
  rw [show (∑ e∈starEdges Q v,x.1 e)=
      ∑ e, ((if Q.src e=v then x.1 e else 0)+(if Q.dst e=v then x.1 e else 0)) by
    simp only [starEdges,Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro e _
    have hh : ¬(Q.src e=v ∧ Q.dst e=v) := fun h => hloop e (h.1.trans h.2.symm)
    by_cases hs:Q.src e=v <;> by_cases hd:Q.dst e=v <;> simp_all]
  exact hb

/-- One parity equation removes one independent star coordinate. -/
theorem localSpace_finrank_le (Q : FiniteMultiGraph) (v : Q.Vertex)
    (hloop : ∀e,Q.src e≠Q.dst e) :
    Module.finrank F₂ (localSpace Q v) ≤ Q.degree v-1 := by
  rw [coordinateSpace_finrank,← starEdges_card Q v hloop]
  have hle : LinearMap.range (Q.observeEdges (starEdges Q v)) ≤
      LinearMap.ker (starTotal Q v) := by
    rintro y ⟨x,rfl⟩
    exact observe_star_total Q v hloop x
  have hd := Submodule.finrank_mono hle
  by_cases hn : (starEdges Q v).Nonempty
  · obtain ⟨e,he⟩ := hn
    have hnonzero : starTotal Q v≠0 := by
      intro hz
      have hh := congrArg (fun f : (starEdges Q v → F₂) →ₗ[F₂] F₂ =>
        f (Pi.single ⟨e,he⟩ 1)) hz
      simp [starTotal,Pi.single_apply] at hh
    have hk := Module.Dual.finrank_ker_add_one_of_ne_zero hnonzero
    have hk' : Module.finrank F₂ (LinearMap.ker (starTotal Q v))+1=(starEdges Q v).card := by
      simpa using hk
    omega
  · have hz : starEdges Q v=∅ := Finset.not_nonempty_iff_eq_empty.mp hn
    have hb : Module.finrank F₂ (LinearMap.range (Q.observeEdges (starEdges Q v))) ≤
        (starEdges Q v).card := by
      simpa using Submodule.finrank_le (LinearMap.range (Q.observeEdges (starEdges Q v)))
    simp only [hz,Finset.card_empty,Nat.zero_sub] at hb ⊢
    exact hb

theorem zeroStar_probability_ge (Q : FiniteMultiGraph) (v : Q.Vertex)
    (hloop : ∀e,Q.src e≠Q.dst e) :
    1/(2:ℝ)^(Q.degree v-1) ≤ Finite.density (ZeroStar Q v) := by
  rw [zeroStar_probability]
  exact one_div_le_one_div_of_le (by positivity)
    (pow_le_pow_right₀ (by norm_num) (localSpace_finrank_le Q v hloop))

/-- Compatibility with the existing physical singleton-cut event. -/
theorem zeroStar_iff_zeroCutAt (Q : FiniteMultiGraph) (v : Q.Vertex)
    (hloop : ∀e,Q.src e≠Q.dst e) (x : Q.CycleSpace) :
    ZeroStar Q v x ↔ LinkCorrelation.ZeroCutAt Q v x := by
  constructor
  · intro h e
    apply h e.1
    simp only [starEdges,Finset.mem_filter,Finset.mem_univ,true_and]
    rcases e.2 with he | he
    · exact Or.inl he.1
    · exact Or.inr he.1
  · intro h e he
    apply h ⟨e,?_⟩
    have hs : Q.src e=v ∨ Q.dst e=v := (Finset.mem_filter.mp he).2
    rcases hs with hs | ht
    · exact Or.inl ⟨hs,fun ht => hloop e (hs.trans ht.symm)⟩
    · exact Or.inr ⟨ht,fun hs => hloop e (hs.trans ht.symm)⟩

theorem zeroCutAt_iff_localSpace_zero (Q : FiniteMultiGraph) (v : Q.Vertex)
    (hloop : ∀e,Q.src e≠Q.dst e) (x : Q.CycleSpace) :
    LinkCorrelation.ZeroCutAt Q v x ↔ ∀ f∈localSpace Q v,f x=0 := by
  rw [← zeroStar_iff_zeroCutAt Q v hloop x,coordinateSpace_zero_iff]
  rfl

end Erdos1016.ExactMaximumSupport.LargeGirth.PackingLocalSpaces
