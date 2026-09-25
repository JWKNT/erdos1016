import Erdos1016.CycleSpace.Incidence

set_option autoImplicit false

/-!
# Reindexing physical vertices and edges

Each edge is carried by a bijection. Reversing its storage orientation is
allowed; deleting it, merging it, or replacing it by an abstract direction is
not. The complete cycle-space bijection is proved from the endpoint identity.
-/

noncomputable section
open scoped BigOperators

namespace Erdos1016.BoundaryTrace

local instance reindexDecidable (p : Prop) : Decidable p :=
  Classical.propDecidable p

namespace Network

variable {V₁ E₁ V₂ E₂ : Type*}
  [Fintype V₁] [Fintype E₁] [Fintype V₂] [Fintype E₂]

structure Reindex (N₁ : Network V₁ E₁) (N₂ : Network V₂ E₂) where
  vertices : V₁ ≃ V₂
  edges : E₁ ≃ E₂
  endpoints : ∀ e,
    (vertices (N₁.src e) = N₂.src (edges e) ∧
      vertices (N₁.dst e) = N₂.dst (edges e)) ∨
    (vertices (N₁.src e) = N₂.dst (edges e) ∧
      vertices (N₁.dst e) = N₂.src (edges e))

namespace Reindex

variable {N₁ : Network V₁ E₁} {N₂ : Network V₂ E₂}

def wordEquiv (r : Reindex N₁ N₂) : N₁.Word ≃ N₂.Word where
  toFun x e := x (r.edges.symm e)
  invFun x e := x (r.edges e)
  left_inv x := by funext e; simp
  right_inv x := by funext e; simp

@[simp] theorem wordEquiv_apply_edge (r : Reindex N₁ N₂)
    (x : N₁.Word) (e : E₁) : r.wordEquiv x (r.edges e) = x e := by
  simp [wordEquiv]

theorem wordEquiv_eq_push (r : Reindex N₁ N₂) (x : N₁.Word) :
    r.wordEquiv x = push r.edges x := by
  funext e
  have heq : ∀ e', r.edges e' = e ↔ e' = r.edges.symm e := by
    intro e'
    constructor
    · intro h
      simpa only [Equiv.symm_apply_apply] using congrArg r.edges.symm h
    · intro h
      rw [h, Equiv.apply_symm_apply]
  simp [wordEquiv, push_apply, heq]

/-- Boundary commutes with a physical reindexing, including orientation flips. -/
theorem boundary_wordEquiv (r : Reindex N₁ N₂) (x : N₁.Word) :
    N₂.boundary (r.wordEquiv x) = push r.vertices (N₁.boundary x) := by
  rw [r.wordEquiv_eq_push]
  change push N₂.src (push r.edges x) + push N₂.dst (push r.edges x) =
    push r.vertices (push N₁.src x + push N₁.dst x)
  rw [push_comp, push_comp, map_add, push_comp, push_comp]
  change (∑ e, x e • unitWord (N₂.src (r.edges e))) +
      (∑ e, x e • unitWord (N₂.dst (r.edges e))) =
    (∑ e, x e • unitWord (r.vertices (N₁.src e))) +
      (∑ e, x e • unitWord (r.vertices (N₁.dst e)))
  rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro e _
  rcases r.endpoints e with h | h
  · rw [h.1, h.2]
  · rw [h.1, h.2, add_comm]

theorem boundary_zero_iff (r : Reindex N₁ N₂) (x : N₁.Word) :
    N₂.boundary (r.wordEquiv x) = 0 ↔ N₁.boundary x = 0 := by
  rw [r.boundary_wordEquiv]
  constructor
  · intro h
    apply push_injective r.vertices r.vertices.injective
    simpa only [map_zero] using h
  · intro h
    rw [h, map_zero]

/-- Physical reindexing preserves adjacency in both directions. -/
theorem graph_adj_iff (r : Reindex N₁ N₂) (u v : V₁) :
    N₂.graph.Adj (r.vertices u) (r.vertices v) ↔ N₁.graph.Adj u v := by
  constructor
  · rintro ⟨f, hf⟩
    let e := r.edges.symm f
    have he := r.endpoints e
    have hef : r.edges e = f := r.edges.apply_symm_apply f
    rw [hef] at he
    refine ⟨e, ?_⟩
    rcases he with he | he <;> rcases hf with hf | hf
    · exact Or.inl ⟨r.vertices.injective (he.1.trans hf.1),
        r.vertices.injective (he.2.trans hf.2)⟩
    · exact Or.inr ⟨r.vertices.injective (he.1.trans hf.1),
        r.vertices.injective (he.2.trans hf.2)⟩
    · exact Or.inr ⟨r.vertices.injective (he.1.trans hf.2),
        r.vertices.injective (he.2.trans hf.1)⟩
    · exact Or.inl ⟨r.vertices.injective (he.1.trans hf.2),
        r.vertices.injective (he.2.trans hf.1)⟩
  · rintro ⟨e, h⟩
    refine ⟨r.edges e, ?_⟩
    rcases r.endpoints e with he | he <;> rcases h with h | h
    · exact Or.inl ⟨he.1.symm.trans (congrArg r.vertices h.1),
        he.2.symm.trans (congrArg r.vertices h.2)⟩
    · exact Or.inr ⟨he.1.symm.trans (congrArg r.vertices h.1),
        he.2.symm.trans (congrArg r.vertices h.2)⟩
    · exact Or.inr ⟨he.2.symm.trans (congrArg r.vertices h.2),
        he.1.symm.trans (congrArg r.vertices h.1)⟩
    · exact Or.inl ⟨he.2.symm.trans (congrArg r.vertices h.2),
        he.1.symm.trans (congrArg r.vertices h.1)⟩

def graphHom (r : Reindex N₁ N₂) : N₁.graph →g N₂.graph where
  toFun := r.vertices
  map_rel' := fun {u v} h => (r.graph_adj_iff u v).2 h

def inverseGraphHom (r : Reindex N₁ N₂) : N₂.graph →g N₁.graph where
  toFun := r.vertices.symm
  map_rel' := by
    intro u v h
    apply (r.graph_adj_iff (r.vertices.symm u) (r.vertices.symm v)).1
    simpa only [Equiv.apply_symm_apply] using h

/-- Connectedness is transported by the actual vertex/edge bijection. -/
theorem connected_iff (r : Reindex N₁ N₂) :
    N₁.graph.Connected ↔ N₂.graph.Connected :=
  ⟨fun h => h.map r.graphHom r.vertices.surjective,
   fun h => h.map r.inverseGraphHom r.vertices.symm.surjective⟩

def cycleEquiv (r : Reindex N₁ N₂) : N₁.CycleSpace ≃ N₂.CycleSpace where
  toFun x := ⟨r.wordEquiv x.1, (r.boundary_zero_iff x.1).2 x.2⟩
  invFun x := ⟨r.wordEquiv.symm x.1, (r.boundary_zero_iff _).1 (by
    rw [Equiv.apply_symm_apply]
    exact x.2)⟩
  left_inv x := Subtype.ext (r.wordEquiv.symm_apply_apply x.1)
  right_inv x := Subtype.ext (r.wordEquiv.apply_symm_apply x.1)

end Reindex
end Network
end Erdos1016.BoundaryTrace
