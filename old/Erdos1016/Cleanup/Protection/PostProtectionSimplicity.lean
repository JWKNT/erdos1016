import Erdos1016.Cleanup.Root.ComponentExtraction

set_option autoImplicit false

/-!
# The deterministic part of post-protection simplicity

Protecting every endpoint of a parallel pair outside the initial protected
set removes all parallel labels from the remaining induced graph.  This
isolates the purely combinatorial step from the probabilistic argument which
must first rule out auxiliary loops.
-/

noncomputable section
namespace Erdos1016.Proof.PostProtectionSimplicity

open Erdos1016

def parallelOutside (Γ : FiniteMultiGraph) (P₀ : Finset Γ.Vertex)
    (e f : Γ.Edge) : Prop :=
  e ≠ f ∧ Γ.src e ∉ P₀ ∧ Γ.dst e ∉ P₀ ∧
    Γ.src f ∉ P₀ ∧ Γ.dst f ∉ P₀ ∧
    ((Γ.src e = Γ.src f ∧ Γ.dst e = Γ.dst f) ∨
      (Γ.src e = Γ.dst f ∧ Γ.dst e = Γ.src f))

/-- The set P₁ in the paper: endpoints of every parallel pair whose endpoints
were both outside P₀. -/
def protectParallelEndpoints (Γ : FiniteMultiGraph) (P₀ : Finset Γ.Vertex) :
    Finset Γ.Vertex := by
  classical
  exact Finset.univ.filter fun v =>
    ∃ e f, parallelOutside Γ P₀ e f ∧
      (v = Γ.src e ∨ v = Γ.dst e ∨ v = Γ.src f ∨ v = Γ.dst f)

theorem no_parallel_outside_protected_union
    (Γ : FiniteMultiGraph) (P₀ : Finset Γ.Vertex)
    (e f : Γ.Edge)
    (he : Γ.src e ∉ P₀ ∪ protectParallelEndpoints Γ P₀)
    (hte : Γ.dst e ∉ P₀ ∪ protectParallelEndpoints Γ P₀)
    (hf : Γ.src f ∉ P₀ ∪ protectParallelEndpoints Γ P₀)
    (htf : Γ.dst f ∉ P₀ ∪ protectParallelEndpoints Γ P₀)
    (hparallel :
      ((Γ.src e = Γ.src f ∧ Γ.dst e = Γ.dst f) ∨
        (Γ.src e = Γ.dst f ∧ Γ.dst e = Γ.src f))) : e = f := by
  classical
  by_contra hne
  have he₀ : Γ.src e ∉ P₀ := by
    intro h
    exact he (Finset.mem_union_left _ h)
  have hte₀ : Γ.dst e ∉ P₀ := by
    intro h
    exact hte (Finset.mem_union_left _ h)
  have hf₀ : Γ.src f ∉ P₀ := by
    intro h
    exact hf (Finset.mem_union_left _ h)
  have htf₀ : Γ.dst f ∉ P₀ := by
    intro h
    exact htf (Finset.mem_union_left _ h)
  have hpair : parallelOutside Γ P₀ e f :=
    ⟨hne, he₀, hte₀, hf₀, htf₀, hparallel⟩
  have hprot : Γ.src e ∈ protectParallelEndpoints Γ P₀ := by
    simp [protectParallelEndpoints]
    exact ⟨e, f, hpair, Or.inl rfl⟩
  exact he (Finset.mem_union_right P₀ hprot)



end Erdos1016.Proof.PostProtectionSimplicity
end
