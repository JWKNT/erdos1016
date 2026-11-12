import Erdos1016.ExactMaximumSupport.LargeGirth.PieceCore
import Erdos1016.Probability.Cylinders.RegionCycleEvents
import Erdos1016.Graph.Multigraph.ForestCharacterization

set_option autoImplicit false
set_option maxHeartbeats 1500000

/-!
# Exact word transport for labelled induced multigraphs

Internal edge labels are retained, including loops and parallel edges.
Extension by zero identifies the induced cycle space with the actual
ambient internal cycle space. Foresthood is transported through even supports.
-/
noncomputable section
open scoped BigOperators
namespace Erdos1016.ExactMaximumSupport.LargeGirth.PoleProduct
open FiniteMultiGraph PieceCore.Induced

local instance poleProductDecidable (p : Prop) : Decidable p := Classical.propDecidable p

variable (G : FiniteMultiGraph) (X : Finset G.Vertex)

def projectWord : G.EdgeWord →ₗ[F₂] (graph G X).EdgeWord where
  toFun x e := x (edge G X e)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

def extendWord : (graph G X).EdgeWord →ₗ[F₂] G.EdgeWord where
  toFun y e := if h : e ∈ G.internalEdges X then y (edges G X ⟨e,h⟩) else 0
  map_add' x y := by ext e; simp only [Pi.add_apply]; split_ifs <;> rfl
  map_smul' a x := by ext e; simp only [Pi.smul_apply]; split_ifs <;> simp

@[simp] theorem extend_edge (y : (graph G X).EdgeWord) (e : (graph G X).Edge) :
    extendWord G X y (edge G X e) = y e := by
  simp [extendWord, edge, ((edges G X).symm e).2]

@[simp] theorem project_extend (y : (graph G X).EdgeWord) :
    projectWord G X (extendWord G X y) = y := by
  ext e
  simp [projectWord, extendWord, edge, ((edges G X).symm e).2]

@[simp] theorem extend_project (x : G.EdgeWord) :
    extendWord G X (projectWord G X x) = G.restrictEdges (G.internalEdges X) x := by
  ext e
  by_cases he : e ∈ G.internalEdges X <;> simp [extendWord, projectWord, edge, restrictEdges, he]

theorem extend_injective : Function.Injective (extendWord G X) := by
  intro x y h
  have hh := congrArg (projectWord G X) h
  simpa only [project_extend] using hh

theorem sum_edges {A : Type*} [AddCommMonoid A] (f : G.Edge → A) :
    (∑ e : (graph G X).Edge, f (edge G X e)) = ∑ e ∈ G.internalEdges X, f e := by
  calc
    _ = ∑ e : Edge G X, f e.1 :=
      Fintype.sum_equiv (edges G X).symm _ _ (fun _ => rfl)
    _ = _ := Finset.sum_coe_sort _ _

theorem boundary_extend_at (y : (graph G X).EdgeWord) (v : (graph G X).Vertex) :
    G.boundary (extendWord G X y) (vertex G X v) = (graph G X).boundary y v := by
  let f : G.Edge → F₂ := fun e =>
    (if G.src e = vertex G X v then extendWord G X y e else 0) +
    (if G.dst e = vertex G X v then extendWord G X y e else 0)
  change (∑ e : G.Edge, f e) = _
  have hs : (∑ e : G.Edge, f e) = ∑ e ∈ G.internalEdges X, f e := by
    symm
    apply Finset.sum_subset (Finset.subset_univ _)
    intro e _ he
    simp [f, extendWord, he]
  rw [hs, ← sum_edges]
  change (∑ e : (graph G X).Edge, f (edge G X e)) = ∑ e : (graph G X).Edge, _
  apply Finset.sum_congr rfl
  intro e _
  dsimp [f]
  rw [extend_edge, ← vertex_src, ← vertex_dst]
  simp only [(vertex_injective G X).eq_iff]

theorem boundary_extend_outside (y : (graph G X).EdgeWord) (v : G.Vertex) (hv : v ∉ X) :
    G.boundary (extendWord G X y) v = 0 := by
  change (∑ e : G.Edge, _) = 0
  apply Finset.sum_eq_zero
  intro e _
  by_cases he : e ∈ G.internalEdges X
  · have hh := (Finset.mem_filter.mp he).2
    have hs : G.src e ≠ v := fun h => hv (h ▸ hh.1)
    have ht : G.dst e ≠ v := fun h => hv (h ▸ hh.2)
    simp [hs, ht]
  · simp [extendWord, he]

theorem boundary_extend_zero (y : (graph G X).EdgeWord) (hy : (graph G X).boundary y = 0) :
    G.boundary (extendWord G X y) = 0 := by
  ext v
  by_cases hv : v ∈ X
  · have hh := boundary_extend_at G X y (vertices G X ⟨v,hv⟩)
    simpa only [vertex_vertices, hy, Pi.zero_apply] using hh
  · exact boundary_extend_outside G X y v hv

def extendCycle : (graph G X).CycleSpace →ₗ[F₂] G.internalCycleSpace X where
  toFun y := ⟨⟨extendWord G X y.1, boundary_extend_zero G X y.1 y.2⟩, by
    intro e he; simp [extendWord, he]⟩
  map_add' _ _ := by apply Subtype.ext; apply Subtype.ext; exact map_add _ _ _
  map_smul' _ _ := by apply Subtype.ext; apply Subtype.ext; exact map_smul _ _ _

theorem extend_project_internal (x : G.internalCycleSpace X) :
    extendWord G X (projectWord G X x.1.1) = x.1.1 := by
  rw [extend_project]
  ext e
  by_cases he : e ∈ G.internalEdges X <;> simp [restrictEdges, he, x.2 e]

def projectCycle : G.internalCycleSpace X →ₗ[F₂] (graph G X).CycleSpace where
  toFun x := ⟨projectWord G X x.1.1, by
    ext v
    rw [← boundary_extend_at, extend_project_internal]
    exact congrFun x.1.2 (vertex G X v)⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- Exact cycle-space identification; no exterior connectedness is required. -/
def cycleEquiv : (graph G X).CycleSpace ≃ₗ[F₂] G.internalCycleSpace X where
  toLinearMap := extendCycle G X
  invFun := projectCycle G X
  left_inv y := by apply Subtype.ext; exact project_extend G X y.1
  right_inv x := by apply Subtype.ext; apply Subtype.ext; exact extend_project_internal G X x

/-- Physical foresthood, including loop and digon obstructions, is exact. -/
theorem forest_extend_iff (y : (graph G X).EdgeWord) :
    G.IsForestWord (extendWord G X y) ↔ (graph G X).IsForestWord y := by
  rw [G.isForestWord_iff_no_even_support, (graph G X).isForestWord_iff_no_even_support]
  constructor
  · intro h z hz
    apply extend_injective G X
    rw [map_zero]
    apply h (extendCycle G X z).1
    intro e he
    by_cases hm : e ∈ G.internalEdges X
    · have hval : z.1 (edges G X ⟨e,hm⟩) ≠ 0 := by simpa [extendCycle, extendWord, hm] using he
      simpa [extendWord, hm] using hz _ hval
    · simp [extendCycle, extendWord, hm] at he
  · intro h z hz
    have hi : z ∈ G.internalCycleSpace X := by
      intro e he
      by_contra hne
      have hy := hz e hne
      simp [extendWord, he] at hy
    let a : G.internalCycleSpace X := ⟨z,hi⟩
    have hzero : (projectCycle G X a).1 = 0 := by
      apply h
      intro e he
      have hval : z.1 (edge G X e) ≠ 0 := he
      have hy := hz _ hval
      simpa [extendWord, edge, ((edges G X).symm e).2] using hy
    have heq := extend_project_internal G X a
    rw [show projectWord G X a.1.1 = 0 from hzero, map_zero] at heq
    exact heq.symm

end Erdos1016.ExactMaximumSupport.LargeGirth.PoleProduct
