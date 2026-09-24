import Erdos1016.Cleanup.Root.ProtectedExteriorComponents
import Mathlib.Data.Fintype.Card

set_option autoImplicit false

noncomputable section

namespace Erdos1016.Proof.ClosedEmbeddingComponentCount

/-- A vertex embedding whose image is a union of components does not create
extra connected components when the ambient graph is pulled back. -/
theorem component_count_le
    {α β : Type*} [Fintype α] [Fintype β]
    (K : SimpleGraph β) (f : α → β) (hinj : Function.Injective f)
    (hclosed : ∀ a b, K.Adj (f a) b → ∃ a', f a' = b) :
    Nat.card (K.comap f).ConnectedComponent ≤ Nat.card K.ConnectedComponent := by
  classical
  let J := K.comap f
  have lift : ∀ {x y : β}, K.Walk x y →
      ∀ a, f a = x → ∃ b, f b = y ∧ J.Reachable a b := by
    intro x y p
    induction p with
    | nil =>
        intro a ha
        exact ⟨a, ha, SimpleGraph.Reachable.refl a⟩
    | @cons x y z hxy p ih =>
        intro a ha
        obtain ⟨b, hb⟩ := hclosed a y (by simpa [ha] using hxy)
        obtain ⟨c, hc, hbc⟩ := ih b hb
        refine ⟨c, hc, ?_⟩
        have hab : J.Adj a b := by
          change K.Adj (f a) (f b)
          simpa [ha, hb] using hxy
        exact hab.reachable.trans hbc
  have lift_reachable : ∀ a b, K.Reachable (f a) (f b) → J.Reachable a b := by
    intro a b h
    obtain ⟨p⟩ := h
    obtain ⟨b', hb', hreach⟩ := lift p a rfl
    exact hinj hb' ▸ hreach
  let representative (c : J.ConnectedComponent) : α :=
    Classical.choose c.nonempty_supp
  have hrep (c : J.ConnectedComponent) : representative c ∈ c.supp :=
    Classical.choose_spec c.nonempty_supp
  let g : J.ConnectedComponent → K.ConnectedComponent :=
    fun c => K.connectedComponentMk (f (representative c))
  have hg : Function.Injective g := by
    intro c d h
    have hreach := lift_reachable (representative c) (representative d)
      (SimpleGraph.ConnectedComponent.exact h)
    have hc := (c.mem_supp_iff (representative c)).mp (hrep c)
    have hd := (d.mem_supp_iff (representative d)).mp (hrep d)
    exact hc.symm.trans ((SimpleGraph.ConnectedComponent.sound hreach).trans hd)
  exact Nat.card_le_card_of_injective g hg

end Erdos1016.Proof.ClosedEmbeddingComponentCount

end
