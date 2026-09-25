import Erdos1016.Graph.Multigraph.InducedSimpleRealization
import Erdos1016.Graph.Multigraph.RegionDegrees

set_option autoImplicit false

/-!
# Extending even words from the actual simple induced graph

The extension is zero on every omitted physical label. Its boundary and
incidence degrees are preserved at each retained vertex, giving an injective
linear map from the retained graph's cycle space to the ambient multigraph.
-/

noncomputable section
open scoped BigOperators
namespace Erdos1016.FiniteMultiGraph.InducedSimpleRealization

local instance inducedCycleSpaceDecidable (p : Prop) : Decidable p := Classical.propDecidable p

variable (G : FiniteMultiGraph) (R : Finset G.Vertex)
  (hloop : ∀ e ∈ G.internalEdges R, G.src e ≠ G.dst e)
  (hsimple : ∀ e ∈ G.internalEdges R, ∀ f ∈ G.internalEdges R,
    ((G.src e = G.src f ∧ G.dst e = G.dst f) ∨
      (G.src e = G.dst f ∧ G.dst e = G.src f)) → e = f)

/-- Extend an induced physical edge word by zero on omitted ambient labels. -/
def liftWord : (graph G R hloop hsimple).Word →ₗ[F₂] G.EdgeWord where
  toFun x e := if he : e ∈ G.internalEdges R then x (edgeEquiv G R ⟨e, he⟩) else 0
  map_add' x y := by
    funext e
    by_cases he : e ∈ G.internalEdges R <;> simp [he]
  map_smul' a x := by
    funext e
    by_cases he : e ∈ G.internalEdges R <;> simp [he]

@[simp] theorem liftWord_edge (x : (graph G R hloop hsimple).Word)
    (e : (graph G R hloop hsimple).Edge) :
    liftWord G R hloop hsimple x (edge G R hloop hsimple e) = x e := by
  simp [liftWord, edge, ((edgeEquiv G R).symm e).2]

theorem liftWord_zero_outside (x : (graph G R hloop hsimple).Word)
    (e : G.Edge) (he : e ∉ G.internalEdges R) : liftWord G R hloop hsimple x e = 0 := by
  simp [liftWord, he]

theorem liftWord_injective : Function.Injective (liftWord G R hloop hsimple) := by
  intro x y hxy
  funext e
  simpa only [liftWord_edge] using congrFun hxy (edge G R hloop hsimple e)

/-- Sum a function supported on retained physical labels by using the actual
edge reindexing. -/
theorem sum_retained {A : Type*} [AddCommMonoid A] (f : G.Edge → A)
    (hf : ∀ e, e ∉ G.internalEdges R → f e = 0) :
    (∑ e : G.Edge, f e) = ∑ e : (graph G R hloop hsimple).Edge, f (edge G R hloop hsimple e) := by
  have hzero : (∑ e : {e : G.Edge // e ∉ G.internalEdges R}, f e.1) = 0 := by
    apply Finset.sum_eq_zero
    intro e he
    exact hf e.1 e.2
  have hsum := Fintype.sum_subtype_add_sum_subtype (fun e => e ∈ G.internalEdges R) f
  rw [hzero, add_zero] at hsum
  calc
    _ = ∑ e : RetainedEdge G R, f e.1 := by
      convert hsum.symm using 1 <;> congr
      exact Subsingleton.elim _ _
    _ = _ := Fintype.sum_equiv (edgeEquiv G R) _ _ (by intro e; simp [edge])

theorem boundary_liftWord (x : (graph G R hloop hsimple).Word)
    (v : (graph G R hloop hsimple).Vertex) :
    G.boundary (liftWord G R hloop hsimple x) (vertex G R hloop hsimple v) =
      (graph G R hloop hsimple).boundary x v := by
  change (∑ e : G.Edge, _) = _
  rw [sum_retained G R hloop hsimple (A := F₂) _ (by
    intro e he
    rw [liftWord_zero_outside G R hloop hsimple x e he]
    simp)]
  change _ = ∑ e : (graph G R hloop hsimple).Edge,
    ((if (graph G R hloop hsimple).src e = v then x e else 0) +
      (if (graph G R hloop hsimple).dst e = v then x e else 0))
  apply Finset.sum_congr rfl
  intro e he
  rw [liftWord_edge, ← vertex_src, ← vertex_dst]
  simp only [(vertex_injective G R hloop hsimple).eq_iff]

theorem boundary_liftWord_outside (x : (graph G R hloop hsimple).Word)
    (v : G.Vertex) (hv : v ∉ R) : G.boundary (liftWord G R hloop hsimple x) v = 0 := by
  change (∑ e : G.Edge, _) = 0
  apply Finset.sum_eq_zero
  intro e he
  by_cases hmem : e ∈ G.internalEdges R
  · have hs : G.src e ≠ v := fun h => hv (h ▸ (Finset.mem_filter.mp hmem).2.1)
    have ht : G.dst e ≠ v := fun h => hv (h ▸ (Finset.mem_filter.mp hmem).2.2)
    simp [hs, ht]
  · rw [liftWord_zero_outside G R hloop hsimple x e hmem]
    simp

/-- The actual ambient even word obtained by zero extension. -/
def liftCycleSpace : (graph G R hloop hsimple).CycleSpace →ₗ[F₂] G.CycleSpace where
  toFun x := ⟨liftWord G R hloop hsimple x.1, by
    rw [LinearMap.mem_ker]
    funext v
    by_cases hv : v ∈ R
    · have h := boundary_liftWord G R hloop hsimple x.1 (vertexEquiv G R ⟨v, hv⟩)
      have hz := congrFun x.2 (vertexEquiv G R ⟨v, hv⟩)
      simpa [vertex] using h.trans hz
    · exact boundary_liftWord_outside G R hloop hsimple x.1 v hv⟩
  map_add' _ _ := by apply Subtype.ext; exact map_add _ _ _
  map_smul' _ _ := by apply Subtype.ext; exact map_smul _ _ _

theorem liftCycleSpace_injective : Function.Injective (liftCycleSpace G R hloop hsimple) := by
  intro x y hxy
  apply Subtype.ext
  exact liftWord_injective G R hloop hsimple (congrArg Subtype.val hxy)

private theorem physical_selectedDegree_endpoints (H : PhysicalGraph) (x : H.Word) (v : H.Vertex) :
    H.selectedDegree x v = ∑ e, if x e ≠ 0 then
      (if H.src e = v then 1 else 0) + (if H.dst e = v then 1 else 0) else 0 := by
  unfold PhysicalGraph.selectedDegree
  rw [Finset.card_eq_sum_ones, Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro e he
  by_cases hx : x e = 0 <;> by_cases hs : H.src e = v <;> by_cases ht : H.dst e = v
  all_goals try simp [hx, hs, ht, PhysicalGraph.incident]
  exact (H.noLoops e (hs.trans ht.symm)).elim

/-- The selected incidence degree is preserved, even though ambient vertices
may have additional omitted edges or loops. -/
theorem selectedDegree_liftWord (x : (graph G R hloop hsimple).Word)
    (v : (graph G R hloop hsimple).Vertex) :
    G.selectedDegree (liftWord G R hloop hsimple x) (vertex G R hloop hsimple v) =
      (graph G R hloop hsimple).selectedDegree x v := by
  rw [G.selectedDegree_eq_sum_endpoints, physical_selectedDegree_endpoints]
  rw [sum_retained G R hloop hsimple (A := ℕ) _ (by
    intro e he
    rw [liftWord_zero_outside G R hloop hsimple x e he]
    simp)]
  apply Finset.sum_congr rfl
  intro e he
  rw [liftWord_edge, ← vertex_src, ← vertex_dst]
  simp only [(vertex_injective G R hloop hsimple).eq_iff]

end Erdos1016.FiniteMultiGraph.InducedSimpleRealization
