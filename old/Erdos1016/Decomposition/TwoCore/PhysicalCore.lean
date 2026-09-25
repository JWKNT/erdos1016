import Erdos1016.Decomposition.TwoCore.MaximalCore
import Erdos1016.Nonbacktracking.Girth.MooreBounds
import Erdos1016.Boundary.NetworkRealization

set_option autoImplicit false

/-!
# Physical realization of the induced finite 2-core

The maximal core is first constructed in the owner simple graph. Its induced
actual-edge network is then relabelled as a `PhysicalGraph`, so the existing
girth/Moore theorem can be applied without suppressing degree-two vertices.
-/

noncomputable section
open Erdos1016.BoundaryTrace Erdos1016.BoundaryDecay
namespace Erdos1016.Nonbacktracking.FiniteTwoCore

local instance finiteTwoCorePhysicalDecidable (p : Prop) : Decidable p :=
  Classical.propDecidable p

variable {V E : Type*} [Fintype V] [Fintype E]

def insideSimple (N : Network V E) (S : Finset V)
    (hs : BoundaryDecay.SimpleNetwork N) :
    BoundaryDecay.SimpleNetwork (Network.Shore.inside N S) := by
  intro e f h
  rcases h with h | h
  · have hef := hs e.1 f.1
      (Or.inl ⟨congrArg Subtype.val h.1, congrArg Subtype.val h.2⟩)
    exact Subtype.ext hef
  · have hef := hs e.1 f.1
      (Or.inr ⟨congrArg Subtype.val h.1, congrArg Subtype.val h.2⟩)
    exact Subtype.ext hef

def inducedNetwork (G : PhysicalGraph) (S : Finset G.Vertex) :=
  Network.Shore.inside G.traceNetwork S

def inducedNetworkSimple (G : PhysicalGraph) (S : Finset G.Vertex) :
    BoundaryDecay.SimpleNetwork (inducedNetwork G S) :=
  insideSimple G.traceNetwork S (by
    intro e f h
    apply G.simple e f
    rcases h with h | h
    · exact Or.inl ⟨h.1, h.2⟩
    · exact Or.inr ⟨h.1, h.2⟩)

def inducedPhysical (G : PhysicalGraph) (S : Finset G.Vertex) : PhysicalGraph :=
  BoundaryDecay.physicalize (inducedNetwork G S) (inducedNetworkSimple G S)

theorem original_degree_eq_graph_degree (G : PhysicalGraph) (v : G.Vertex) :
    G.degree v = G.toSimpleGraph.degree v := by
  rw [← G.traceNetwork_graph]
  have hs : BoundaryDecay.SimpleNetwork G.traceNetwork :=
    fun e f h => G.simple e f h
  have hnet :
      BoundaryDecay.networkDegree G.traceNetwork v = G.traceNetwork.graph.degree v :=
    BoundaryDecay.networkDegree_eq_graph_degree G.traceNetwork hs v
  have hdeg : G.degree v = BoundaryDecay.networkDegree G.traceNetwork v := by
    unfold BoundaryDecay.networkDegree PhysicalGraph.degree PhysicalGraph.selectedDegree
    apply congrArg Finset.card
    congr 1
    ext e
    simp [PhysicalGraph.traceNetwork, PhysicalGraph.incident]
  exact hdeg.trans hnet

theorem inducedPhysical_degree_eq (G : PhysicalGraph) (S : Finset G.Vertex)
    (v : Network.Shore.InsideVertex S) :
    (inducedPhysical G S).degree
      (Fintype.equivFin (Network.Shore.InsideVertex S) v) =
        degreeWithin G.toSimpleGraph S v.1 := by
  let N := inducedNetwork G S
  let hs := inducedNetworkSimple G S
  have hphys := BoundaryDecay.physical_degree_eq N hs v
  have hnet := BoundaryDecay.networkDegree_eq_graph_degree N hs v
  have hgraph : N.graph = G.toSimpleGraph.induce (↑S : Set G.Vertex) := by
    rw [← G.traceNetwork_graph]
    exact Network.Shore.inside_graph_eq_induce G.traceNetwork S
  change (BoundaryDecay.physicalize N hs).degree _ = _
  rw [hphys, hnet, hgraph]
  exact induce_degree_eq_degreeWithin G.toSimpleGraph S v.1 v.2

theorem inducedPhysical_degreeTwoCount_eq (G : PhysicalGraph) (S : Finset G.Vertex) :
    Nonbacktracking.degreeTwoCount (inducedPhysical G S) =
      degreeTwoCount G.toSimpleGraph S := by
  classical
  let H := inducedPhysical G S
  let e := Fintype.equivFin (Network.Shore.InsideVertex S)
  let A := {w : H.Vertex // H.degree w = 2}
  let B := {v : Network.Shore.InsideVertex S //
    degreeWithin G.toSimpleGraph S v.1 = 2}
  have hA : Nonbacktracking.degreeTwoCount H = Fintype.card A := by
    unfold Nonbacktracking.degreeTwoCount A
    symm
    exact Fintype.card_subtype (fun w : H.Vertex => H.degree w = 2)
  have hB : degreeTwoCount G.toSimpleGraph S = Fintype.card B := by
    unfold degreeTwoCount B
    symm
    let p : G.Vertex → Prop := fun v => v ∈ S ∧ degreeWithin G.toSimpleGraph S v = 2
    have hp : ∀ v, v ∈ S.filter (fun v => degreeWithin G.toSimpleGraph S v = 2) ↔ p v := by
      intro v
      simp [p]
    have hc := Fintype.card_of_subtype
      (S.filter (fun v => degreeWithin G.toSimpleGraph S v = 2)) hp
    have heq : Fintype.card {v : G.Vertex // p v} = Fintype.card B := by
      apply Fintype.card_congr
      exact {
        toFun := fun x => ⟨⟨x.1, x.2.1⟩, x.2.2⟩
        invFun := fun x => ⟨x.1.1, x.1.2, x.2⟩
        left_inv := by intro x; rfl
        right_inv := by intro x; cases x; rfl }
    exact heq.symm.trans hc
  let ab : A ≃ B := {
    toFun := fun w => by
      let v := e.symm w.1
      have hdeg := inducedPhysical_degree_eq G S v
      have hval : H.degree (e v) = degreeWithin G.toSimpleGraph S v.1 := by
        simpa [H, e] using hdeg
      have heq : e v = w.1 := by simp [v]
      exact ⟨v, hval.symm.trans (heq ▸ w.2)⟩
    invFun := fun v => by
      let w := e v.1
      have hdeg := inducedPhysical_degree_eq G S v.1
      have hval : H.degree (e v.1) = degreeWithin G.toSimpleGraph S v.1 := by
        simpa [H, e] using hdeg
      exact ⟨w, hval.trans v.2⟩
    left_inv := fun w => by
      apply Subtype.ext
      simp [e]
    right_inv := fun v => by
      apply Subtype.ext
      apply Subtype.ext
      simp [e] }
  calc
    Nonbacktracking.degreeTwoCount H = Fintype.card A := hA
    _ = Fintype.card B := Fintype.card_congr ab
    _ = degreeTwoCount G.toSimpleGraph S := hB.symm

def maximalPhysicalCore (G : PhysicalGraph) : Finset G.Vertex :=
  vertices G.toSimpleGraph Finset.univ





theorem girthGreater_graphIso {A B : Type*} [Fintype A] [Fintype B]
    {J : SimpleGraph A} {K : SimpleGraph B} (e : J ≃g K) (D : ℕ)
    (hg : ShortWalks.GirthGreater J D) : ShortWalks.GirthGreater K D := by
  intro v p hp
  let q := p.map e.symm.toHom
  have hq : q.IsCycle :=
    (SimpleGraph.Walk.map_isCycle_iff_of_injective e.symm.injective).2 hp
  have hlen : q.length = p.length := by simp [q]
  rw [← hlen]
  exact hg _ q hq

def inducedPhysicalGraphIso (G : PhysicalGraph) (S : Finset G.Vertex) :
    (inducedNetwork G S).graph ≃g (inducedPhysical G S).toSimpleGraph where
  toEquiv := (BoundaryDecay.physicalReindex (inducedNetwork G S)
    (inducedNetworkSimple G S)).vertices
  map_rel_iff' := by
    intro u v
    rw [← PhysicalGraph.traceNetwork_graph]
    exact (BoundaryDecay.physicalReindex (inducedNetwork G S)
      (inducedNetworkSimple G S)).graph_adj_iff u v

theorem maximalPhysicalCore_girthGreater (G : PhysicalGraph) (D : ℕ)
    (hg : ShortWalks.GirthGreater G.toSimpleGraph D) :
    ShortWalks.GirthGreater
      (inducedPhysical G (maximalPhysicalCore G)).toSimpleGraph D := by
  apply girthGreater_graphIso (inducedPhysicalGraphIso G (maximalPhysicalCore G))
  change ShortWalks.GirthGreater
    (Network.Shore.inside G.traceNetwork (maximalPhysicalCore G)).graph D
  rw [Network.Shore.inside_graph_eq_induce, G.traceNetwork_graph]
  intro v p hp
  let incl : G.toSimpleGraph.induce (↑(maximalPhysicalCore G) : Set G.Vertex) →g
      G.toSimpleGraph :=
    { toFun := Subtype.val, map_rel' := fun hab => hab }
  let q := p.map incl
  have hq : q.IsCycle :=
    (SimpleGraph.Walk.map_isCycle_iff_of_injective Subtype.val_injective).2 hp
  have hlen : q.length = p.length := by simp [q]
  rw [← hlen]
  exact hg _ q hq

theorem inducedPhysical_vertexCount_eq_card (G : PhysicalGraph)
    (S : Finset G.Vertex) : (inducedPhysical G S).vertexCount = S.card := by
  simp [inducedPhysical, inducedNetwork, BoundaryDecay.physicalize,
    Fintype.card_coe]

theorem maximalPhysicalCore_minDegree (G : PhysicalGraph) :
    ∀ v, 2 ≤ (inducedPhysical G (maximalPhysicalCore G)).degree v := by
  intro w
  let e := Fintype.equivFin (Network.Shore.InsideVertex (maximalPhysicalCore G))
  let v := e.symm w
  have hdeg := inducedPhysical_degree_eq G (maximalPhysicalCore G) v
  have hmin : 2 ≤ degreeWithin G.toSimpleGraph (maximalPhysicalCore G) v.1 := by
    simpa [maximalPhysicalCore] using
      vertices_minTwo G.toSimpleGraph Finset.univ v.1 v.2
  rw [← hdeg] at hmin
  simpa [e, v] using hmin

theorem maximalPhysicalCore_degree_le_three (G : PhysicalGraph)
    (hmax : ∀ v, G.degree v ≤ 3) :
    ∀ v, (inducedPhysical G (maximalPhysicalCore G)).degree v ≤ 3 := by
  intro w
  let e := Fintype.equivFin (Network.Shore.InsideVertex (maximalPhysicalCore G))
  let v := e.symm w
  have hdeg := inducedPhysical_degree_eq G (maximalPhysicalCore G) v
  have hcore := degreeWithin_le_degree G.toSimpleGraph (maximalPhysicalCore G) v.1
  have hbound : degreeWithin G.toSimpleGraph (maximalPhysicalCore G) v.1 ≤ 3 := by
    calc
      degreeWithin G.toSimpleGraph (maximalPhysicalCore G) v.1 ≤
          G.toSimpleGraph.degree v.1 := hcore
      _ = G.degree v.1 := (original_degree_eq_graph_degree G v.1).symm
      _ ≤ 3 := hmax v.1
  rw [← hdeg] at hbound
  simpa [e, v] using hbound

theorem maximalPhysicalCore_peeling (G : PhysicalGraph) :
    Peeling G.toSimpleGraph (maximalPhysicalCore G) Finset.univ := by
  apply exists_peeling G.toSimpleGraph Finset.univ Finset.univ
  · exact vertices_subset G.toSimpleGraph Finset.univ
  · exact Finset.Subset.refl _

/-- The generic peeling ledger with the original physical order and degree
bound made explicit. -/
theorem physicalOrder_le_core_add_cubicDeficit (G : PhysicalGraph)
    (hmax : ∀ v, G.degree v ≤ 3) :
    (G.vertexCount : ℤ) ≤ (maximalPhysicalCore G).card +
      cubicDeficit G.toSimpleGraph Finset.univ := by
  have hmaxGraph : ∀ v, G.toSimpleGraph.degree v ≤ 3 := by
    intro v
    rw [← original_degree_eq_graph_degree G v]
    exact hmax v
  have h := order_le_core_add_deficit G.toSimpleGraph
    (maximalPhysicalCore_peeling G)
    (vertices_subset G.toSimpleGraph Finset.univ) hmaxGraph
  simpa [maximalPhysicalCore] using h

/-- Every degree-two vertex that survives pruning is paid for by the original
physical cubic deficit. -/
theorem maximalPhysicalCore_degreeTwo_le_cubicDeficit (G : PhysicalGraph)
    (hmax : ∀ v, G.degree v ≤ 3) :
    (degreeTwoCount G.toSimpleGraph (maximalPhysicalCore G) : ℤ) ≤
      cubicDeficit G.toSimpleGraph Finset.univ := by
  have hmaxGraph : ∀ v, G.toSimpleGraph.degree v ≤ 3 := by
    intro v
    rw [← original_degree_eq_graph_degree G v]
    exact hmax v
  have h := degreeTwoCount_core_le_deficit G.toSimpleGraph
    (maximalPhysicalCore_peeling G)
    (vertices_minTwo G.toSimpleGraph Finset.univ)
    (fun v => vertices_maxDegree G.toSimpleGraph Finset.univ 3 hmaxGraph v)
  simpa [maximalPhysicalCore] using h
