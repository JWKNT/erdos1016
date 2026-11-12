import Erdos1016.ExactMaximum.NetRealization

set_option autoImplicit false
set_option maxHeartbeats 1500000

/-!
# A finite network as a labelled multigraph

The construction reindexes vertices and physical edges separately.
Parallel edges remain distinct. The network's loopless condition is retained.
The canonical maps allow affine events to use the same constructed graph.
-/

noncomputable section
open scoped BigOperators

namespace Erdos1016.ExactMaximumSupport.NetworkMultigraph
open BoundaryTrace BoundaryTrace.Network BoundaryDecay FiniteMultiGraph

local instance networkMultigraphDecidable (p : Prop) : Decidable p := Classical.propDecidable p

variable {V E : Type*} [Fintype V] [Fintype E] (N : Network V E)

def graph : FiniteMultiGraph where
  vertexCount := Fintype.card V
  edgeCount := Fintype.card E
  src e := Fintype.equivFin V (N.src ((Fintype.equivFin E).symm e))
  dst e := Fintype.equivFin V (N.dst ((Fintype.equivFin E).symm e))

def vertices : V ≃ (graph N).Vertex := Fintype.equivFin V
def edges : E ≃ (graph N).Edge := Fintype.equivFin E

@[simp] theorem src_edges (e : E) : (graph N).src (edges N e) = vertices N (N.src e) := by
  simp [graph, edges, vertices]

@[simp] theorem dst_edges (e : E) : (graph N).dst (edges N e) = vertices N (N.dst e) := by
  simp [graph, edges, vertices]

theorem isLoopless : (graph N).IsLoopless := by
  intro e he
  exact N.noLoops ((edges N).symm e) ((vertices N).injective he)

theorem not_hasLoop : ¬ (graph N).HasLoop :=
  (graph N).isLoopless_iff_not_hasLoop.mp (isLoopless N)

def relabel : Relabel N (looplessNetwork (graph N)) where
  φ := vertices N
  ψ := (edges N).trans (Equiv.subtypeUnivEquiv (isLoopless N)).symm
  src e := src_edges N e
  dst e := dst_edges N e

@[simp] theorem cycleRank : (graph N).cycleRank = networkRank N := by
  rw [(graph N).cycleRank_eq_networkRank (isLoopless N)]
  exact (relabel N).networkRank_eq

@[simp] theorem numCycles : (graph N).numCycles = N.numCycles := by
  rw [(graph N).numCycles_eq_looplessNetwork (isLoopless N)]
  exact (relabel N).numCycles_eq

section RelabelTransport
variable {V' E' : Type*} [Fintype V'] [Fintype E']
  {N : Network V E} {N' : Network V' E'} (R : Relabel N N')

omit [Fintype V] [Fintype V'] in
/-- Selected incidence degrees are unchanged under a labelled relabelling. -/
theorem degree_push (x : N.Word) (v : V) :
    N'.deg (R.push x) (R.φ v) = N.deg x v := by
  rw [N'.deg_eq_sum, N.deg_eq_sum, ← Equiv.sum_comp R.ψ]
  apply Finset.sum_congr rfl
  intro e _
  rw [R.push_apply, R.src, R.dst]
  simp only [R.φ.injective.eq_iff]

/-- The selected simple adjacency graphs are exactly isomorphic. -/
def selectedGraphIso (x : N.Word) :
    N.selectedGraph x ≃g N'.selectedGraph (R.push x) where
  toEquiv := R.φ
  map_rel_iff' := by
    intro u v
    constructor
    · rintro ⟨e, he, hend⟩
      refine ⟨R.ψ.symm e, he, ?_⟩
      have hs := R.src (R.ψ.symm e)
      have ht := R.dst (R.ψ.symm e)
      simp only [Equiv.apply_symm_apply] at hs ht
      rcases hend with h | h
      · exact Or.inl ⟨R.φ.injective (hs.symm.trans h.1),
          R.φ.injective (ht.symm.trans h.2)⟩
      · exact Or.inr ⟨R.φ.injective (hs.symm.trans h.1),
          R.φ.injective (ht.symm.trans h.2)⟩
    · rintro ⟨e, he, h | h⟩
      · refine ⟨R.ψ e, ?_, Or.inl ?_⟩
        · simpa only [R.push_apply] using he
        · exact ⟨(R.src e).trans (congrArg R.φ h.1),
            (R.dst e).trans (congrArg R.φ h.2)⟩
      · refine ⟨R.ψ e, ?_, Or.inr ?_⟩
        · simpa only [R.push_apply] using he
        · exact ⟨(R.src e).trans (congrArg R.φ h.1),
            (R.dst e).trans (congrArg R.φ h.2)⟩

omit [Fintype V] [Fintype V'] in
/-- Endpoint-labelled path words are unchanged under relabelling. -/
theorem isPathWord_push {s t : V} {x : N.Word} (hx : N.IsPathWord s t x) :
    N'.IsPathWord (R.φ s) (R.φ t) (R.push x) := by
  refine ⟨fun h => hx.1 (R.φ.injective h), ?_, ?_, ?_, ?_⟩
  · rw [degree_push]
    exact hx.2.1
  · rw [degree_push]
    exact hx.2.2.1
  · intro v hvs hvt
    obtain ⟨u, rfl⟩ := R.φ.surjective v
    rw [degree_push]
    exact hx.2.2.2.1 u (fun h => hvs (congrArg R.φ h))
      (fun h => hvt (congrArg R.φ h))
  · intro v hv
    obtain ⟨u, rfl⟩ := R.φ.surjective v
    rw [degree_push] at hv
    exact (hx.2.2.2.2 u hv).map (selectedGraphIso R x).toHom

omit [Fintype V] [Fintype V'] in
/-- Path counts preserve both designated endpoints and all physical edge labels. -/
theorem numPaths_relabel (s t : V) : N'.numPaths (R.φ s) (R.φ t) = N.numPaths s t := by
  let f : {x : N.Word // N.IsPathWord s t x} →
      {y : N'.Word // N'.IsPathWord (R.φ s) (R.φ t) y} :=
    fun x => ⟨R.push x.1, isPathWord_push R x.2⟩
  have hf : Function.Bijective f := by
    constructor
    · intro x y h
      exact Subtype.ext (R.push_injective (congrArg Subtype.val h))
    · intro y
      have hy := isPathWord_push R.symm y.2
      simp only [Relabel.symm, Equiv.symm_apply_apply] at hy
      exact ⟨⟨R.symm.push y.1, hy⟩, Subtype.ext (R.push_symm_push y.1)⟩
  exact (Nat.card_eq_of_bijective f hf).symm

omit [Fintype V] [Fintype E] in
private theorem selectedGraph_one (N : Network V E) :
    N.selectedGraph (fun _ => 1) = N.graph := by
  ext u v
  simp [Network.selectedGraph, Network.graph]

def networkGraphIso : N.graph ≃g N'.graph where
  toEquiv := R.φ
  map_rel_iff' := by
    intro u v
    have h := (selectedGraphIso R (fun _ => 1)).map_adj_iff (v := u) (w := v)
    have hp : R.push (fun _ => 1) = fun _ => 1 := rfl
    simpa only [hp, selectedGraph_one] using h

end RelabelTransport

/-- The actual multigraph and original network have the same simple adjacency. -/
def graphIso : N.graph ≃g (graph N).toSimpleGraph where
  toEquiv := vertices N
  map_rel_iff' := by
    intro u v
    have h := (networkGraphIso (relabel N)).map_adj_iff (v := u) (w := v)
    simpa only [looplessNetwork_graph] using h

@[simp] theorem graphIso_apply (v : V) : graphIso N v = vertices N v := rfl

theorem connected_iff : (graph N).toSimpleGraph.Connected ↔ N.graph.Connected :=
  (graphIso N).connected_iff.symm

theorem connected (hN : N.graph.Connected) : (graph N).toSimpleGraph.Connected :=
  (connected_iff N).mpr hN

@[simp] theorem degree (v : V) :
    (graph N).degree (vertices N v) = N.deg (fun _ => 1) v := by
  rw [(graph N).degree_eq_deg (isLoopless N)]
  exact degree_push (relabel N) (fun _ => 1) v

/-- Path counts on the canonical loopless network agree exactly. -/
@[simp] theorem numPaths (s t : V) :
    (looplessNetwork (graph N)).numPaths (vertices N s) (vertices N t) = N.numPaths s t :=
  numPaths_relabel (relabel N) s t

/-- Reindexing the full physical word keeps all parallel edge coordinates. -/
def wordEquiv : N.Word ≃ₗ[F₂] (graph N).EdgeWord where
  toFun x e := x ((edges N).symm e)
  invFun x e := x (edges N e)
  left_inv x := by ext e; simp
  right_inv x := by ext e; simp
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

@[simp] theorem wordEquiv_apply (x : N.Word) (e : E) :
    wordEquiv N x (edges N e) = x e := by simp [wordEquiv]

theorem nonloop_wordEquiv (x : N.Word) :
    nonloopWord (graph N) (wordEquiv N x) = (relabel N).push x := rfl

/-- The physical parity boundary is the original boundary at the reindexed vertex. -/
@[simp] theorem boundary_wordEquiv (x : N.Word) (v : V) :
    (graph N).boundary (wordEquiv N x) (vertices N v) = N.boundary x v := by
  rw [← nonloopWord_boundary, nonloop_wordEquiv]
  exact (relabel N).boundary_push x v

@[simp] theorem selectedDegree_wordEquiv (x : N.Word) (v : V) :
    (graph N).selectedDegree (wordEquiv N x) (vertices N v) = N.deg x v := by
  rw [(graph N).selectedDegree_eq_deg _ (fun e he => (isLoopless N e he).elim),
    nonloop_wordEquiv]
  exact degree_push (relabel N) x v

end Erdos1016.ExactMaximumSupport.NetworkMultigraph
