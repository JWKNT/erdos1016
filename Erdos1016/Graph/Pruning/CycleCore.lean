import Mathlib.Combinatorics.SimpleGraph.Metric
import Erdos1016.Graph.Pruning.EvenSupport
import Erdos1016.Graph.Pruning.PathConvexity
import Erdos1016.Decomposition.TwoCore.PhysicalCore

set_option autoImplicit false

/-! Pruning to the full two-core preserves the entire binary cycle space. -/

noncomputable section
open scoped BigOperators
namespace Erdos1016.ShortProof.CycleCore
open BoundaryTrace BoundaryDecay Nonbacktracking.FiniteTwoCore

local instance cycleCoreDecidable (p : Prop) : Decidable p := Classical.propDecidable p

variable (G : PhysicalGraph)

abbrev core : Finset G.Vertex := maximalPhysicalCore G
abbrev coreNetwork := inducedNetwork G (core G)
abbrev corePhysical := inducedPhysical G (core G)

theorem nonzero_edge_in_core (x : G.CycleSpace) (e : G.Edge) (he : x.1 e ≠ 0) :
    G.src e ∈ core G ∧ G.dst e ∈ core G := by
  have h := Proof.CoreCycleSpace.usedVertices_subset_core G x
  exact ⟨h ((mem_usedVertices x.1 _).mpr ⟨e, he, Or.inl rfl⟩),
    h ((mem_usedVertices x.1 _).mpr ⟨e, he, Or.inr rfl⟩)⟩

/-- Restriction uses the original edge label beneath each induced edge. -/
def restrictCycle : G.CycleSpace →ₗ[F₂] (coreNetwork G).CycleSpace where
  toFun x := ⟨fun e => x.1 e.1, by
    rw [LinearMap.mem_ker]
    funext v
    let f : G.Edge → F₂ := fun e =>
      (if G.src e = v.1 then x.1 e else 0) + (if G.dst e = v.1 then x.1 e else 0)
    have hzero : (∑ e : {e : G.Edge // ¬ (G.src e ∈ core G ∧ G.dst e ∈ core G)}, f e.1) = 0 := by
      apply Finset.sum_eq_zero
      intro e he
      have hx : x.1 e.1 = 0 := by
        by_contra hx
        exact e.2 (nonzero_edge_in_core G x e.1 hx)
      simp [f, hx]
    have hsum := Fintype.sum_subtype_add_sum_subtype
      (fun e : G.Edge => G.src e ∈ core G ∧ G.dst e ∈ core G) f
    rw [hzero, add_zero] at hsum
    rw [Network.boundary_apply, ← Finset.sum_add_distrib]
    calc
      _ = ∑ e : Network.Shore.InsideEdge G.traceNetwork (core G), f e.1 := by
        apply Finset.sum_congr rfl
        intro e he
        simp [coreNetwork, inducedNetwork, Network.Shore.inside,
          PhysicalGraph.traceNetwork, Subtype.ext_iff, f]
      _ = G.boundary x.1 v.1 := hsum
      _ = 0 := congrFun x.2 v.1⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- Extend an induced edge word by zero on deleted edge labels. -/
def extendWord (y : (coreNetwork G).Word) : G.Word := fun e =>
  if he : G.src e ∈ core G ∧ G.dst e ∈ core G then y ⟨e, he⟩ else 0

theorem extendWord_even (y : (coreNetwork G).CycleSpace) : G.boundary (extendWord G y.1) = 0 := by
  funext v
  let f : G.Edge → F₂ := fun e =>
    (if G.src e = v then extendWord G y.1 e else 0) +
    (if G.dst e = v then extendWord G y.1 e else 0)
  have hzero : (∑ e : {e : G.Edge // ¬ (G.src e ∈ core G ∧ G.dst e ∈ core G)}, f e.1) = 0 := by
    apply Finset.sum_eq_zero
    intro e he
    simp [f, extendWord, e.2]
  have hsum := Fintype.sum_subtype_add_sum_subtype
    (fun e : G.Edge => G.src e ∈ core G ∧ G.dst e ∈ core G) f
  rw [hzero, add_zero] at hsum
  change (∑ e, f e) = 0
  rw [← hsum]
  by_cases hv : v ∈ core G
  · calc
      _ = (coreNetwork G).boundary y.1 ⟨v, hv⟩ := by
        rw [Network.boundary_apply, ← Finset.sum_add_distrib]
        apply Finset.sum_congr rfl
        intro e he
        simp [f, extendWord, e.2, coreNetwork, inducedNetwork,
          Network.Shore.inside, PhysicalGraph.traceNetwork, Subtype.ext_iff]
      _ = 0 := congrFun y.2 ⟨v, hv⟩
  · apply Finset.sum_eq_zero
    intro e he
    have hs : G.src e.1 ≠ v := by intro h; exact hv (h ▸ e.2.1)
    have hd : G.dst e.1 ≠ v := by intro h; exact hv (h ▸ e.2.2)
    simp [f, hs, hd]

/-- The full two-core loses neither even words nor uniform probability mass. -/
def networkCycleEquiv : G.CycleSpace ≃ₗ[F₂] (coreNetwork G).CycleSpace where
  toFun := restrictCycle G
  invFun y := ⟨extendWord G y.1, extendWord_even G y⟩
  left_inv x := by
    apply Subtype.ext; funext e
    change (if he : G.src e ∈ core G ∧ G.dst e ∈ core G then x.1 e else 0) = x.1 e
    split_ifs with he
    · rfl
    · by_contra hn
      exact he (nonzero_edge_in_core G x e (Ne.symm hn))
  right_inv y := by
    apply Subtype.ext; funext e
    change (if he : G.src e.1 ∈ core G ∧ G.dst e.1 ∈ core G then y.1 ⟨e.1, he⟩ else 0) = y.1 e
    split_ifs with he
    · rfl
    · exact (he e.2).elim
  map_add' := (restrictCycle G).map_add
  map_smul' := (restrictCycle G).map_smul

def realizationCycleEquiv : (coreNetwork G).CycleSpace ≃ₗ[F₂] (corePhysical G).CycleSpace where
  toEquiv := physicalCycleEquiv (coreNetwork G) (inducedNetworkSimple G (core G))
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

def physicalCycleEquiv : G.CycleSpace ≃ₗ[F₂] (corePhysical G).CycleSpace :=
  (networkCycleEquiv G).trans (realizationCycleEquiv G)

theorem cycleRank_preserved : (corePhysical G).cycleRank = G.cycleRank :=
  (physicalCycleEquiv G).symm.finrank_eq

theorem density_preserved (P : (corePhysical G).CycleSpace → Prop) :
    Finite.density (fun x : G.CycleSpace => P (physicalCycleEquiv G x)) = Finite.density P :=
  Finite.density_equiv (physicalCycleEquiv G).toEquiv (fun _ => Iff.rfl)

/-- Connectedness survives full leaf pruning when the core is nonempty. -/
theorem core_connected (hG : G.IsConnected) (hne : (core G).Nonempty) :
    (G.toSimpleGraph.induce (↑(core G) : Set G.Vertex)).Connected := by
  refine { nonempty := ⟨⟨hne.choose, hne.choose_spec⟩⟩, preconnected := ?_ }
  intro u v
  obtain ⟨p, hp, _⟩ := hG.exists_path_of_dist u.1 v.1
  have hs := Proof.TwoCorePathGeometry.path_support_subset_twoCore
    G.toSimpleGraph Finset.univ p hp u.2 v.2 (fun _ _ => Finset.mem_univ _)
  let f : G.toSimpleGraph.induce {z | z ∈ p.support} →g
      G.toSimpleGraph.induce (↑(core G) : Set G.Vertex) := {
    toFun := fun z => ⟨z.1, hs z.1 z.2⟩
    map_rel' := fun h => h }
  exact (p.connected_induce_support.preconnected
    ⟨u.1, p.start_mem_support⟩ ⟨v.1, p.end_mem_support⟩).map f

theorem physical_connected (hG : G.IsConnected) (hne : (core G).Nonempty) :
    (corePhysical G).IsConnected := by
  have h := core_connected G hG hne
  have hn : (coreNetwork G).graph.Connected := by
    simpa only [coreNetwork, inducedNetwork, Network.Shore.inside_graph_eq_induce,
      PhysicalGraph.traceNetwork_graph] using h
  exact hn.map (inducedPhysicalGraphIso G (core G)).toHom
    (inducedPhysicalGraphIso G (core G)).surjective

/-- Any marked minimum-degree-two subgraph is untouched by pruning. -/
theorem marked_subset_core (P : Finset G.Vertex) (hP : MinTwo G.toSimpleGraph P) :
    P ⊆ core G := maximal G.toSimpleGraph Finset.univ P (Finset.subset_univ _) hP

end Erdos1016.ShortProof.CycleCore
