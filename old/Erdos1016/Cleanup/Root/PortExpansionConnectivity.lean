import Erdos1016.Cleanup.Root.PortExteriorComponentEquivalence

set_option autoImplicit false

noncomputable section

namespace Erdos1016.Proof.PortExpansionConnectivity

open Erdos1016 CleanupSpecification PortExpansion
open PortExpansionCycleSpace
open PortExteriorComponentEquivalence

/-- Subdividing exterior edges and replacing exterior loops by triangles
preserves connectivity of the complete ambient graph. -/
theorem connected (M : FiniteMultiGraph) (S : Finset M.Vertex)
    (h : IsCleanupRoot M S) (hM : M.toSimpleGraph.Connected) :
    (graph M S h).IsConnected := by
  classical
  have haux : (AuxOutsideGraph M ∅).Connected := by
    let f : M.toSimpleGraph →g AuxOutsideGraph M ∅ :=
      { toFun v := ⟨v, by simp⟩, map_rel' := fun h => h }
    exact hM.map f (fun v => ⟨v.1, Subtype.ext rfl⟩)
  letI : Subsingleton (AuxOutsideGraph M ∅).ConnectedComponent :=
    haux.preconnected.subsingleton_connectedComponent
  have hsurj := (exteriorComponentMap_bijective M S ∅ h (Finset.empty_subset _)).2
  letI : Subsingleton (PortOutsideGraph M S ∅ h).ConnectedComponent :=
    Function.Surjective.subsingleton hsurj
  have hpre : (PortOutsideGraph M S ∅ h).Preconnected := by
    intro u v
    exact SimpleGraph.ConnectedComponent.exact (Subsingleton.elim _ _)
  letI hnonempty : Nonempty (PortOutside M S ∅ h) := by
    obtain ⟨v⟩ := hM.nonempty
    exact ⟨⟨oldVertex M S v, by simp [oldVertexImage]⟩⟩
  have hp : (PortOutsideGraph M S ∅ h).Connected :=
    @SimpleGraph.Connected.mk _ _ hpre hnonempty
  let f : PortOutsideGraph M S ∅ h →g (graph M S h).toSimpleGraph :=
    { toFun := Subtype.val, map_rel' := fun h => h }
  exact hp.map f (fun v => ⟨⟨v, by simp [oldVertexImage]⟩, rfl⟩)

end Erdos1016.Proof.PortExpansionConnectivity

end
