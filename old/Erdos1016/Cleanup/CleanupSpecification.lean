import Erdos1016.Graph.Multigraph.Components
import Erdos1016.Extremal.Capacity.CompositionProbability
import Erdos1016.Cleanup.Corridors.PhysicalPartition

set_option autoImplicit false

/-!
# Section 10 witness-preserving cleanup interface

This file formalizes the statement and certificate shape of Proposition
`prop:cleanup`, constructed in `CleanupConstruction`. Its
output records an actual exterior component count, a surjective linear
marginal (which gives the exact uniform cycle-space marginal), and a linear
section lifting test cycles to the original graph.
-/

noncomputable section
open scoped BigOperators

namespace Erdos1016.Proof.CleanupSpecification

open Erdos1016
open Erdos1016.Proof.PhysicalPartition

/-- An edge is active when some cycle-space word has a nonzero coordinate on it. -/
def ActiveEdge (G : PhysicalGraph) (e : G.Edge) : Prop :=
  ∃ x : G.CycleSpace, x.1 e ≠ 0

/-- The simple graph carried by the witness edges and vertices. -/
def witnessGraph (G : PhysicalGraph) (V : Finset G.Vertex)
    (W : Finset G.Edge) : SimpleGraph G.Vertex where
  Adj u v := u ∈ V ∧ v ∈ V ∧ u ≠ v ∧ ∃ e ∈ W,
    (G.src e = u ∧ G.dst e = v) ∨ (G.src e = v ∧ G.dst e = u)
  symm := by
    intro u v h
    rcases h with ⟨hu, hv, hne, e, he, h | h⟩
    · exact ⟨hv, hu, hne.symm, e, he, Or.inr h⟩
    · exact ⟨hv, hu, hne.symm, e, he, Or.inl h⟩
  loopless := by
    intro v h
    exact h.2.2.1 rfl

/-- The number of connected components of the witness subgraph. -/
noncomputable def witnessComponentCount (G : PhysicalGraph)
    (V : Finset G.Vertex) (W : Finset G.Edge) : ℕ := by
  classical
  exact Fintype.card ((witnessGraph G V W).induce (↑V : Set G.Vertex)).ConnectedComponent

/-- Exact input data for Proposition `prop:cleanup`. The values `Cext` and
`Rred` are deliberately left for the theorem's uniform existential choice. -/
structure CleanupInput (G : PhysicalGraph) where
  R : ℕ
  r : ℕ
  witnessEdges : Finset G.Edge
  witnessVertices : Finset G.Vertex
  rank_large : 2 ^ (8 * R) ≤ r
  graph_rank : G.cycleRank = r
  graph_connected : G.IsConnected
  witness_nonempty : witnessEdges.Nonempty
  witness_endpoints : ∀ e ∈ witnessEdges, G.src e ∈ witnessVertices ∧ G.dst e ∈ witnessVertices
  witness_vertices_exact : ∀ v, v ∈ witnessVertices ↔ ∃ e ∈ witnessEdges, G.src e = v ∨ G.dst e = v
  witness_edges_active : ∀ e ∈ witnessEdges, ActiveEdge G e
  vertices_le_edges : witnessVertices.card ≤ witnessEdges.card
  witness_edges_budget : witnessEdges.card + 1 ≤ 2 ^ (4 * R)
  witness_components : witnessComponentCount G witnessVertices witnessEdges < 5 * R
  outside_probability : (1 / 2 : ℝ) + 1 / (R : ℝ) <
    G.outsideLinearForestProbability witnessEdges

/-- The underlying simple graph selected by a multigraph word. -/
def selectedGraph (Γ : FiniteMultiGraph) (x : Γ.EdgeWord) : SimpleGraph Γ.Vertex where
  Adj u v := u ≠ v ∧ ∃ e, x e ≠ 0 ∧ ((Γ.src e = u ∧ Γ.dst e = v) ∨ (Γ.src e = v ∧ Γ.dst e = u))
  symm := by
    intro u v h
    rcases h with ⟨hne, e, hx, h | h⟩
    · exact ⟨hne.symm, e, hx, Or.inr h⟩
    · exact ⟨hne.symm, e, hx, Or.inl h⟩
  loopless := by
    intro v h
    exact h.1 rfl

/-- Number of selected incidences at a vertex; a selected loop counts twice. -/
def selectedDegree (Γ : FiniteMultiGraph) (x : Γ.EdgeWord) (v : Γ.Vertex) : ℕ := by
  classical
  let S := Finset.univ.filter fun e : Γ.Edge => x e ≠ 0
  exact (S.filter fun e => Γ.src e = v).card + (S.filter fun e => Γ.dst e = v).card

/-- The labelled selected subgraph is a linear forest: it has no loops or
parallel pair, its underlying selected graph is acyclic, and every incidence
degree is at most two. -/
def IsLinearForestWord (Γ : FiniteMultiGraph) (x : Γ.EdgeWord) : Prop :=
  (∀ e, x e ≠ 0 → Γ.src e ≠ Γ.dst e) ∧
  (∀ e f, e ≠ f → x e ≠ 0 → x f ≠ 0 →
    ((Γ.src e = Γ.src f ∧ Γ.dst e = Γ.dst f) ∨
     (Γ.src e = Γ.dst f ∧ Γ.dst e = Γ.src f)) → False) ∧
  (selectedGraph Γ x).IsAcyclic ∧
  (∀ v, selectedDegree Γ x v ≤ 2)

/-- Labelled auxiliary edges internal to a vertex region. -/
def internalEdges (Γ : FiniteMultiGraph) (H : Finset Γ.Vertex) : Finset Γ.Edge := by
  classical
  exact Finset.univ.filter fun e => Γ.src e ∈ H ∧ Γ.dst e ∈ H

/-- Probability that the cycle-space restriction to the edges internal to `H`
is a linear forest. This is the auxiliary probability denoted `P_Γ(H)` in the
paper. -/
def regionForestProbability (Γ : FiniteMultiGraph) (H : Finset Γ.Vertex) : ℝ := by
  classical
  exact (Finset.univ.filter fun x : Γ.CycleSpace =>
    IsLinearForestWord Γ (fun e => if e ∈ internalEdges Γ H then x.1 e else 0)).card /
      (2 : ℝ) ^ Γ.cycleRank

/-- The source event in the cleanup comparison: the witness-complement
restriction of a global cycle is a linear forest. -/
def originalCleanupGood (G : PhysicalGraph) (I : CleanupInput G)
    (x : G.CycleSpace) : Prop :=
  G.IsRestrictedLinearForest I.witnessEdgesᶜ
    (G.restrictWord I.witnessEdgesᶜ x.1)

/-- The target event in the cleanup comparison: the auxiliary cycle's
restriction to the root-internal edges is a linear forest. -/
def auxiliaryCleanupGood (Γ : FiniteMultiGraph) (H : Finset Γ.Vertex)
    (y : Γ.CycleSpace) : Prop :=
  IsLinearForestWord Γ
    (fun e => if e ∈ internalEdges Γ H then y.1 e else 0)

/-- Root properties: connected induced simple region. -/
def IsCleanupRoot (Γ : FiniteMultiGraph) (H : Finset Γ.Vertex) : Prop :=
  (Γ.toSimpleGraph.induce (↑H : Set Γ.Vertex)).Connected ∧
  (∀ e : Γ.Edge, Γ.src e ∈ H → Γ.dst e ∈ H → Γ.src e ≠ Γ.dst e) ∧
  (∀ e f : Γ.Edge,
    Γ.src e ∈ H → Γ.dst e ∈ H → Γ.src f ∈ H → Γ.dst f ∈ H →
    ((Γ.src e = Γ.src f ∧ Γ.dst e = Γ.dst f) ∨
     (Γ.src e = Γ.dst f ∧ Γ.dst e = Γ.src f)) → e = f)

/-- Ambient degree counts labelled edge incidences, including both incidences
of a loop. -/
def ambientDegree (Γ : FiniteMultiGraph) (v : Γ.Vertex) : ℕ :=
  (Finset.univ.filter (fun e : Γ.Edge => Γ.src e = v)).card +
    (Finset.univ.filter (fun e : Γ.Edge => Γ.dst e = v)).card

/-- Labelled auxiliary edges crossing a vertex set. -/
def cutEdges (Γ : FiniteMultiGraph) (S : Finset Γ.Vertex) : Finset Γ.Edge := by
  classical
  exact Finset.univ.filter fun e =>
    (Γ.src e ∈ S ∧ Γ.dst e ∉ S) ∨ (Γ.src e ∉ S ∧ Γ.dst e ∈ S)

/-- Number of components in the actual exterior induced subgraph. -/
noncomputable def exteriorComponentCount (Γ : FiniteMultiGraph)
    (H : Finset Γ.Vertex) : ℕ := by
  classical
  exact Fintype.card
    ((Γ.toSimpleGraph.induce (↑(Hᶜ) : Set Γ.Vertex)).ConnectedComponent)

/-- Concrete certificates for the witness-preserving reduction. The surjective
linear marginal has equal-size fibers, so a uniform source cycle induces the
uniform cycle-space law on `Γ`. `liftCycles` is a section of that marginal.
The test-edge support fields state that every tested cycle lifts inside the
original complement of the witness. -/
structure CleanupOutput {G : PhysicalGraph} (I : CleanupInput G) where
  Γ : FiniteMultiGraph
  root : Finset Γ.Vertex
  testEdges : Finset Γ.Edge
  marginal : G.CycleSpace →ₗ[F₂] Γ.CycleSpace
  marginal_surjective : Function.Surjective marginal
  liftCycles : Γ.CycleSpace →ₗ[F₂] G.CycleSpace
  vertexMap : Γ.Vertex → G.Vertex
  edgePath : Γ.Edge → PhysicalCorridor G
  edgeRepresentative : ∀ e : Γ.Edge, G.Edge
  edgeRepresentative_mem : ∀ e, edgeRepresentative e ∈ (edgePath e).support
  marginal_reads_representatives : ∀ x : G.CycleSpace, ∀ e : Γ.Edge,
    (marginal x).1 e = x.1 (edgeRepresentative e)
  edgePaths_disjoint : ∀ e f, e ≠ f →
    Disjoint (edgePath e).support (edgePath f).support
  path_endpoints : ∀ e,
    (((edgePath e).vertices.head? = some (vertexMap (Γ.src e)) ∧
       (edgePath e).vertices.getLast? = some (vertexMap (Γ.dst e))) ∨
      ((edgePath e).vertices.head? = some (vertexMap (Γ.dst e)) ∧
       (edgePath e).vertices.getLast? = some (vertexMap (Γ.src e))))
  path_active : ∀ e p, p ∈ (edgePath e).support → ActiveEdge G p
  lift_is_path_expansion : ∀ x : Γ.CycleSpace, ∀ p : G.Edge,
    (liftCycles x).1 p =
      if ∃ e, x.1 e ≠ 0 ∧ p ∈ (edgePath e).support then 1 else 0
  marginal_lift : ∀ x, marginal (liftCycles x) = x
  testEdges_internal : testEdges = internalEdges Γ root
  tested_paths_in_complement : ∀ e ∈ testEdges,
    ∀ p ∈ (edgePath e).support, p ∉ I.witnessEdges
  /-- Pointwise transport of the good event is the combinatorial content
  needed for the paper's probability comparison. It records what the series
  path construction must establish for every source cycle. -/
  good_event_maps : ∀ x : G.CycleSpace,
    originalCleanupGood G I x →
      auxiliaryCleanupGood Γ root (marginal x)
  auxiliary_connected : Γ.toSimpleGraph.Connected
  root_proper : root.card < Γ.vertexCount
  root_structure : IsCleanupRoot Γ root
  root_cubic_ambient_degree : ∀ v ∈ root, ambientDegree Γ v = 3
  root_order : I.r ≤ root.card * 2 ^ (8 * I.R)
  root_cut_bound : (cutEdges Γ root).card ≤ 2 ^ (5 * I.R)
  exterior_nonempty : 1 ≤ exteriorComponentCount Γ root
  exterior_bound : ∃ Cext : ℕ, exteriorComponentCount Γ root ≤ Cext * I.R ^ 2
namespace CleanupOutput

variable {G : PhysicalGraph} {I : CleanupInput G}

/-- A surjective linear marginal sends uniform cycle-space mass to the uniform
law on the auxiliary cycle space. -/
theorem exact_uniform_marginal (O : CleanupOutput I) (P : O.Γ.CycleSpace → Prop) :
    Erdos1016.Finite.density (fun x : G.CycleSpace => P (O.marginal x)) =
      Erdos1016.Finite.density P := by
  exact Erdos1016.BoundaryTrace.density_surjective_linear O.marginal
    O.marginal_surjective P

/-- Pointwise event transport plus the exact uniform marginal prove the
probability inequality required by the cleanup proposition. -/
theorem probability_domination (O : CleanupOutput I) :
    G.outsideLinearForestProbability I.witnessEdges ≤
      regionForestProbability O.Γ O.root := by
  classical
  have hcount :
      Finite.count (originalCleanupGood G I) ≤
        Finite.count (fun x : G.CycleSpace =>
          auxiliaryCleanupGood O.Γ O.root (O.marginal x)) := by
    apply Finite.count_mono
    intro x hx
    exact O.good_event_maps x hx
  have hsourceCard :
      (Fintype.card G.CycleSpace : ℝ) = (2 : ℝ) ^ G.cycleRank := by
    exact_mod_cast G.cycleSpace_card
  have htargetCard :
      (Fintype.card O.Γ.CycleSpace : ℝ) = (2 : ℝ) ^ O.Γ.cycleRank := by
    exact_mod_cast O.Γ.cycleSpace_card
  have houtside :
      G.outsideLinearForestProbability I.witnessEdges =
        Erdos1016.Finite.density (originalCleanupGood G I) := by
    unfold PhysicalGraph.outsideLinearForestProbability
      PhysicalGraph.outsideLinearForestStates Erdos1016.Finite.density
      Erdos1016.Finite.count originalCleanupGood
    rw [hsourceCard]
    simp [Finset.sum_boole]
  have hregion :
      regionForestProbability O.Γ O.root =
        Erdos1016.Finite.density (auxiliaryCleanupGood O.Γ O.root) := by
    unfold regionForestProbability Erdos1016.Finite.density
      Erdos1016.Finite.count auxiliaryCleanupGood
    rw [htargetCard]
    simp [Finset.sum_boole]
  have hden : (0 : ℝ) < Fintype.card G.CycleSpace := by positivity
  have hdensity :
      Erdos1016.Finite.density (originalCleanupGood G I) ≤
        Erdos1016.Finite.density (fun x : G.CycleSpace =>
          auxiliaryCleanupGood O.Γ O.root (O.marginal x)) := by
    unfold Erdos1016.Finite.density
    exact (div_le_div_iff_of_pos_right hden).2 hcount
  calc
    G.outsideLinearForestProbability I.witnessEdges =
        Erdos1016.Finite.density (originalCleanupGood G I) := houtside
    _ ≤ Erdos1016.Finite.density (fun x : G.CycleSpace =>
        auxiliaryCleanupGood O.Γ O.root (O.marginal x)) := hdensity
    _ = Erdos1016.Finite.density (auxiliaryCleanupGood O.Γ O.root) :=
        O.exact_uniform_marginal (auxiliaryCleanupGood O.Γ O.root)
    _ = regionForestProbability O.Γ O.root := hregion.symm









end CleanupOutput

/-- Strong uniform statement of Proposition `prop:cleanup`. Its two constants
are uniform in the input graph and witness, as in the paper. An instance is
proved in `CleanupConstruction.cleanupProposition`. -/
def CleanupProposition : Prop :=
  ∃ Cext Rred : ℕ, 5 ≤ Rred ∧
    ∀ (G : PhysicalGraph) (I : CleanupInput G),
      Rred ≤ I.R →
      (∃ O : CleanupOutput I, exteriorComponentCount O.Γ O.root ≤ Cext * I.R ^ 2)

end Erdos1016.Proof.CleanupSpecification

end
