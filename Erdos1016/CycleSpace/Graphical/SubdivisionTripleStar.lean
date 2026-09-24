import Erdos1016.CycleSpace.Graphical.ConnectedStarBound
import Erdos1016.Graph.Multigraph.Components
import Erdos1016.CycleSpace.Graphical.MultigraphCutFunctionals

set_option autoImplicit false
set_option maxHeartbeats 2000000

/-!
# Triple-star rank for loopless multigraphs by subdivision

Parallel labelled edges are separated by distinct degree-two vertices. The
resulting physical graph is simple, and its cycle space is identified with
the original multigraph cycle space by requiring the two half-edge values at
each new vertex to agree.
-/

noncomputable section

namespace Erdos1016.Proof.MultigraphSubdivisionTripleStar

open Erdos1016
open Erdos1016.Proof.GraphicalCommonInformation
open Erdos1016.Proof.GraphicalTripleReduction
open Erdos1016.Proof.GraphicalTripleStarBoundGraphConnected
open Erdos1016.Proof.GraphicalActualCutMultigraphBridge
open Erdos1016.Proof.GraphicalRegionContraction

local notation "𝔽" => ZMod 2

/-- Subdivision vertices are either original vertices or one fresh midpoint
for each labelled edge. -/
def subdivisionVertexEquiv (M : FiniteMultiGraph) :
    (Sum M.Vertex M.Edge) ≃ Fin (Fintype.card (Sum M.Vertex M.Edge)) :=
  Fintype.equivFin _

/-- The two half-edges of each labelled multigraph edge. -/
def subdivisionEdgeEquiv (M : FiniteMultiGraph) :
    (M.Edge × Bool) ≃ Fin (Fintype.card (M.Edge × Bool)) :=
  Fintype.equivFin _

/-- The simple physical subdivision of a multigraph. Half-edge sources are
midpoints; destinations are the corresponding original endpoints. -/
def subdivide (M : FiniteMultiGraph)
    (hloopless : ∀ e : M.Edge, M.src e ≠ M.dst e) : PhysicalGraph where
  vertexCount := Fintype.card (Sum M.Vertex M.Edge)
  edgeCount := Fintype.card (M.Edge × Bool)
  src e := subdivisionVertexEquiv M
    (.inr ((subdivisionEdgeEquiv M).symm e).1)
  dst e := by
    let p := (subdivisionEdgeEquiv M).symm e
    exact subdivisionVertexEquiv M (.inl (if p.2 then M.dst p.1 else M.src p.1))
  noLoops := by
    intro e
    intro h
    have h' := (subdivisionVertexEquiv M).injective h
    cases h'
  simple := by
    intro e f h
    let p := (subdivisionEdgeEquiv M).symm e
    let q := (subdivisionEdgeEquiv M).symm f
    change ((subdivisionVertexEquiv M (.inr p.1) =
        subdivisionVertexEquiv M (.inr q.1) ∧
      subdivisionVertexEquiv M (.inl (if p.2 then M.dst p.1 else M.src p.1)) =
        subdivisionVertexEquiv M (.inl (if q.2 then M.dst q.1 else M.src q.1))) ∨
      (subdivisionVertexEquiv M (.inr p.1) =
        subdivisionVertexEquiv M (.inl (if q.2 then M.dst q.1 else M.src q.1)) ∧
      subdivisionVertexEquiv M (.inl (if p.2 then M.dst p.1 else M.src p.1)) =
        subdivisionVertexEquiv M (.inr q.1))) at h
    rcases h with h | h
    · have hsrc := (subdivisionVertexEquiv M).injective h.1
      have he : p.1 = q.1 := by simpa using hsrc
      have hdst := (subdivisionVertexEquiv M).injective h.2
      have hb : p.2 = q.2 := by
        cases hp : p.2 <;> cases hq : q.2
        · rfl
        · simp [hp, hq, he] at hdst
          exact False.elim (hloopless q.1 hdst)
        · simp [hp, hq, he] at hdst
          exact False.elim (hloopless q.1 hdst.symm)
        · rfl
      have hpair : p = q := Prod.ext he hb
      exact (subdivisionEdgeEquiv M).symm.injective (by
        simpa [p, q] using hpair)
    · have hcross := (subdivisionVertexEquiv M).injective h.1
      cases hcross

/-- The old vertex of the subdivision corresponding to `v`. -/
def oldVertex (M : FiniteMultiGraph) (hloopless : ∀ e : M.Edge,
    M.src e ≠ M.dst e) (v : M.Vertex) : (subdivide M hloopless).Vertex :=
  subdivisionVertexEquiv M (.inl v)

/-- The midpoint corresponding to a labelled edge. -/
def edgeMidpoint (M : FiniteMultiGraph) (hloopless : ∀ e : M.Edge,
    M.src e ≠ M.dst e) (e : M.Edge) : (subdivide M hloopless).Vertex :=
  subdivisionVertexEquiv M (.inr e)

def halfEdge (M : FiniteMultiGraph) (hloopless : ∀ e : M.Edge,
    M.src e ≠ M.dst e) (e : M.Edge) (side : Bool) : (subdivide M hloopless).Edge :=
  subdivisionEdgeEquiv M (e, side)

def expandWord (M : FiniteMultiGraph) (hloopless : ∀ e : M.Edge,
    M.src e ≠ M.dst e) (x : M.EdgeWord) : (subdivide M hloopless).Word :=
  fun f => x ((subdivisionEdgeEquiv M).symm f).1

private theorem subdivisionBoundary_reindexed
    (M : FiniteMultiGraph) (hloopless : ∀ e : M.Edge,
      M.src e ≠ M.dst e) (x : (subdivide M hloopless).Word)
    (v : (subdivide M hloopless).Vertex) :
    (subdivide M hloopless).boundary x v =
      ∑ e : M.Edge, ∑ b : Bool,
        ((if (subdivide M hloopless).src (halfEdge M hloopless e b) = v
          then x (halfEdge M hloopless e b) else 0) +
         (if (subdivide M hloopless).dst (halfEdge M hloopless e b) = v
          then x (halfEdge M hloopless e b) else 0)) := by
  classical
  unfold PhysicalGraph.boundary
  calc
    (∑ f : (subdivide M hloopless).Edge,
        ((if (subdivide M hloopless).src f = v then x f else 0) +
         (if (subdivide M hloopless).dst f = v then x f else 0))) =
      ∑ p : M.Edge × Bool,
        ((if (subdivide M hloopless).src (subdivisionEdgeEquiv M p) = v
          then x (subdivisionEdgeEquiv M p) else 0) +
         (if (subdivide M hloopless).dst (subdivisionEdgeEquiv M p) = v
          then x (subdivisionEdgeEquiv M p) else 0)) := by
      apply Fintype.sum_equiv (subdivisionEdgeEquiv M).symm
      intro f
      simp
    _ = _ := by
      simp only [Fintype.sum_prod_type]
      apply Finset.sum_congr rfl
      intro e _
      apply Finset.sum_congr rfl
      intro b _
      rfl

theorem subdivisionBoundary_midpoint
    (M : FiniteMultiGraph) (hloopless : ∀ e : M.Edge,
      M.src e ≠ M.dst e) (x : (subdivide M hloopless).Word)
    (e : M.Edge) :
    (subdivide M hloopless).boundary x (edgeMidpoint M hloopless e) =
      x (halfEdge M hloopless e false) +
        x (halfEdge M hloopless e true) := by
  classical
  rw [subdivisionBoundary_reindexed]
  simp [halfEdge, edgeMidpoint, subdivide,
    subdivisionVertexEquiv, subdivisionEdgeEquiv, Finset.sum_ite_eq,
    Fintype.sum_bool]
  <;> ring

theorem subdivisionCycle_halves_equal
    (M : FiniteMultiGraph) (hloopless : ∀ e : M.Edge,
      M.src e ≠ M.dst e) (x : (subdivide M hloopless).CycleSpace)
    (e : M.Edge) :
    x.1 (halfEdge M hloopless e false) =
      x.1 (halfEdge M hloopless e true) := by
  have hcycle : (subdivide M hloopless).boundary x.1 = 0 := x.2
  have h := congrArg (fun d : (subdivide M hloopless).Demand =>
    d (edgeMidpoint M hloopless e)) hcycle
  change (subdivide M hloopless).boundary x.1
      (edgeMidpoint M hloopless e) = 0 at h
  rw [subdivisionBoundary_midpoint] at h
  have hzero : x.1 (halfEdge M hloopless e false) +
      x.1 (halfEdge M hloopless e true) = 0 := by simpa using h
  exact (add_eq_zero_iff_eq_neg.mp hzero).trans (by simp)

def restrictWord (M : FiniteMultiGraph) (hloopless : ∀ e : M.Edge,
    M.src e ≠ M.dst e) (x : (subdivide M hloopless).Word) : M.EdgeWord :=
  fun e => x (halfEdge M hloopless e false)

private theorem subdivisionBoundary_old_eq_restrict
    (M : FiniteMultiGraph) (hloopless : ∀ e : M.Edge,
      M.src e ≠ M.dst e) (x : (subdivide M hloopless).CycleSpace)
    (v : M.Vertex) :
    (subdivide M hloopless).boundary x.1 (oldVertex M hloopless v) =
      M.boundary (restrictWord M hloopless x.1) v := by
  classical
  rw [subdivisionBoundary_reindexed]
  have hcoord : ∀ e : M.Edge,
      x.1 (halfEdge M hloopless e true) =
        x.1 (halfEdge M hloopless e false) := by
    intro e
    exact (subdivisionCycle_halves_equal M hloopless x e).symm
  simp [halfEdge, oldVertex, restrictWord, subdivide,
    subdivisionVertexEquiv, subdivisionEdgeEquiv, Finset.sum_add_distrib,
    Finset.sum_ite_eq, Fintype.sum_bool, FiniteMultiGraph.boundary, hcoord]
  have hsum :
      (∑ e : M.Edge, if M.dst e = v then
        x.1 (halfEdge M hloopless e true) else 0) =
      (∑ e : M.Edge, if M.dst e = v then
        x.1 (halfEdge M hloopless e false) else 0) := by
    apply Finset.sum_congr rfl
    intro e _
    by_cases hv : M.dst e = v <;> simp [hv, hcoord]
  simp [halfEdge, subdivisionEdgeEquiv] at hsum
  rw [hsum]
  <;> abel

theorem expandWord_boundary_old
    (M : FiniteMultiGraph) (hloopless : ∀ e : M.Edge,
      M.src e ≠ M.dst e) (x : M.EdgeWord) (v : M.Vertex) :
    (subdivide M hloopless).boundary (expandWord M hloopless x)
      (oldVertex M hloopless v) = M.boundary x v := by
  classical
  rw [subdivisionBoundary_reindexed]
  simp [halfEdge, oldVertex, expandWord, subdivide,
    subdivisionVertexEquiv, subdivisionEdgeEquiv, Finset.sum_add_distrib,
    Finset.sum_ite_eq, Fintype.sum_bool, FiniteMultiGraph.boundary,
    add_comm]

theorem expandWord_boundary_midpoint
    (M : FiniteMultiGraph) (hloopless : ∀ e : M.Edge,
      M.src e ≠ M.dst e) (x : M.EdgeWord) (e : M.Edge) :
    (subdivide M hloopless).boundary (expandWord M hloopless x)
      (edgeMidpoint M hloopless e) = x e + x e := by
  classical
  rw [subdivisionBoundary_reindexed]
  simp [halfEdge, edgeMidpoint, expandWord, subdivide,
    subdivisionVertexEquiv, subdivisionEdgeEquiv, Finset.sum_ite_eq,
    Fintype.sum_bool]
  <;> ring

def restrictCycles (M : FiniteMultiGraph) (hloopless : ∀ e : M.Edge,
    M.src e ≠ M.dst e) :
    (subdivide M hloopless).CycleSpace →ₗ[𝔽] M.CycleSpace where
  toFun x := ⟨restrictWord M hloopless x.1, by
    change M.boundary (restrictWord M hloopless x.1) = 0
    funext v
    have hcycle : (subdivide M hloopless).boundary x.1 = 0 := x.2
    have h := congrArg (fun d : (subdivide M hloopless).Demand =>
      d (oldVertex M hloopless v)) hcycle
    change (subdivide M hloopless).boundary x.1
      (oldVertex M hloopless v) = 0 at h
    rw [subdivisionBoundary_old_eq_restrict] at h
    exact h⟩
  map_add' x y := by apply Subtype.ext; rfl
  map_smul' a x := by apply Subtype.ext; rfl

def expandCycles (M : FiniteMultiGraph) (hloopless : ∀ e : M.Edge,
    M.src e ≠ M.dst e) :
    M.CycleSpace →ₗ[𝔽] (subdivide M hloopless).CycleSpace where
  toFun x := ⟨expandWord M hloopless x.1, by
    change (subdivide M hloopless).boundary
      (expandWord M hloopless x.1) = 0
    funext q
    cases hz : (subdivisionVertexEquiv M).symm q with
    | inl v =>
      have hq : subdivisionVertexEquiv M (.inl v) = q := by
        rw [← hz]
        exact (subdivisionVertexEquiv M).apply_symm_apply q
      have h := expandWord_boundary_old M hloopless x.1 v
      have hq' : oldVertex M hloopless v = q := by simpa [oldVertex] using hq
      rw [← hq']
      rw [h]
      exact congrArg (fun d : M.Demand => d v) x.2
    | inr e =>
      have hq : subdivisionVertexEquiv M (.inr e) = q := by
        rw [← hz]
        exact (subdivisionVertexEquiv M).apply_symm_apply q
      have h := expandWord_boundary_midpoint M hloopless x.1 e
      have hq' : edgeMidpoint M hloopless e = q := by simpa [edgeMidpoint] using hq
      rw [← hq']
      rw [h]
      calc
        x.1 e + x.1 e = (2 : 𝔽) * x.1 e := by ring
        _ = 0 := by
          have htwo : (2 : 𝔽) = 0 := by decide
          rw [htwo, zero_mul]⟩
  map_add' x y := by apply Subtype.ext; rfl
  map_smul' a x := by apply Subtype.ext; rfl

theorem restrict_expandCycles (M : FiniteMultiGraph)
    (hloopless : ∀ e : M.Edge, M.src e ≠ M.dst e)
    (x : M.CycleSpace) : restrictCycles M hloopless (expandCycles M hloopless x) = x := by
  apply Subtype.ext
  funext e
  simp [restrictCycles, expandCycles, restrictWord, expandWord, halfEdge]

theorem restrictCycles_surjective (M : FiniteMultiGraph)
    (hloopless : ∀ e : M.Edge, M.src e ≠ M.dst e) :
    Function.Surjective (restrictCycles M hloopless) := by
  intro x
  exact ⟨expandCycles M hloopless x, restrict_expandCycles M hloopless x⟩

private theorem oldVertex_adj_midpoint_src (M : FiniteMultiGraph)
    (hloopless : ∀ e : M.Edge, M.src e ≠ M.dst e) (e : M.Edge) :
    (subdivide M hloopless).toSimpleGraph.Adj
      (oldVertex M hloopless (M.src e)) (edgeMidpoint M hloopless e) := by
  change ∃ f, (1 : 𝔽) ≠ 0 ∧
    (( (subdivide M hloopless).src f = oldVertex M hloopless (M.src e) ∧
        (subdivide M hloopless).dst f = edgeMidpoint M hloopless e) ∨
      ((subdivide M hloopless).src f = edgeMidpoint M hloopless e ∧
        (subdivide M hloopless).dst f = oldVertex M hloopless (M.src e)))
  refine ⟨halfEdge M hloopless e false, one_ne_zero, Or.inr ?_⟩
  simp [halfEdge, edgeMidpoint, oldVertex, subdivide,
    subdivisionVertexEquiv, subdivisionEdgeEquiv]

private theorem midpoint_adj_oldVertex_dst (M : FiniteMultiGraph)
    (hloopless : ∀ e : M.Edge, M.src e ≠ M.dst e) (e : M.Edge) :
    (subdivide M hloopless).toSimpleGraph.Adj
      (edgeMidpoint M hloopless e)
      (oldVertex M hloopless (M.dst e)) := by
  change ∃ f, (1 : 𝔽) ≠ 0 ∧
    (( (subdivide M hloopless).src f = edgeMidpoint M hloopless e ∧
        (subdivide M hloopless).dst f = oldVertex M hloopless (M.dst e)) ∨
      ((subdivide M hloopless).src f = oldVertex M hloopless (M.dst e) ∧
        (subdivide M hloopless).dst f = edgeMidpoint M hloopless e))
  refine ⟨halfEdge M hloopless e true, one_ne_zero, Or.inl ?_⟩
  simp [halfEdge, edgeMidpoint, oldVertex, subdivide,
    subdivisionVertexEquiv, subdivisionEdgeEquiv]

private theorem edgeEndpoints_reachable (M : FiniteMultiGraph)
    (hloopless : ∀ e : M.Edge, M.src e ≠ M.dst e) (e : M.Edge) :
    (subdivide M hloopless).toSimpleGraph.Reachable
      (oldVertex M hloopless (M.src e))
      (oldVertex M hloopless (M.dst e)) := by
  exact ((SimpleGraph.Walk.cons
    (oldVertex_adj_midpoint_src M hloopless e)
    (SimpleGraph.Walk.cons (midpoint_adj_oldVertex_dst M hloopless e)
      SimpleGraph.Walk.nil)).reachable)

private theorem adjacentOld_reachable (M : FiniteMultiGraph)
    (hloopless : ∀ e : M.Edge, M.src e ≠ M.dst e)
    {u v : M.Vertex} (hadj : M.toSimpleGraph.Adj u v) :
    (subdivide M hloopless).toSimpleGraph.Reachable
      (oldVertex M hloopless u) (oldVertex M hloopless v) := by
  rcases hadj with ⟨_, e, h | h⟩
  · have hp := edgeEndpoints_reachable M hloopless e
    simpa [h.1, h.2] using hp
  · have hp := (edgeEndpoints_reachable M hloopless e).symm
    simpa [h.1, h.2] using hp

/-- Subdivision preserves connectedness of the underlying multigraph. -/
theorem subdivide_connected (M : FiniteMultiGraph)
    (hloopless : ∀ e : M.Edge, M.src e ≠ M.dst e)
    (hconn : M.toSimpleGraph.Connected) :
    (subdivide M hloopless).IsConnected := by
  classical
  change (subdivide M hloopless).toSimpleGraph.Connected
  let root : M.Vertex := Classical.choice hconn.nonempty
  let root' := oldVertex M hloopless root
  letI : Nonempty (subdivide M hloopless).Vertex := ⟨root'⟩
  have hlift : ∀ {u v : M.Vertex}, M.toSimpleGraph.Reachable u v →
      (subdivide M hloopless).toSimpleGraph.Reachable
        (oldVertex M hloopless u) (oldVertex M hloopless v) := by
    intro u v hp
    obtain ⟨p⟩ := hp
    induction p with
    | nil => exact SimpleGraph.Reachable.refl _
    | @cons u v w huv p ih =>
        exact (adjacentOld_reachable M hloopless huv).trans ih
  have hroot : ∀ v : M.Vertex,
      (subdivide M hloopless).toSimpleGraph.Reachable root'
        (oldVertex M hloopless v) := by
    intro v
    exact hlift (hconn.preconnected root v)
  have hmid : ∀ e : M.Edge,
      (subdivide M hloopless).toSimpleGraph.Reachable root'
        (edgeMidpoint M hloopless e) := by
    intro e
    exact (hroot (M.src e)).trans
      (SimpleGraph.Walk.cons (oldVertex_adj_midpoint_src M hloopless e)
        SimpleGraph.Walk.nil).reachable
  refine ⟨?_⟩
  intro a b
  let za := (subdivisionVertexEquiv M).symm a
  let zb := (subdivisionVertexEquiv M).symm b
  have ha : subdivisionVertexEquiv M za = a :=
    (subdivisionVertexEquiv M).apply_symm_apply a
  have hb : subdivisionVertexEquiv M zb = b :=
    (subdivisionVertexEquiv M).apply_symm_apply b
  have haroot : (subdivide M hloopless).toSimpleGraph.Reachable root' a := by
    cases ha' : za with
    | inl v =>
      have hEq : oldVertex M hloopless v = a := by
        simpa [oldVertex, ha'] using ha
      rw [← hEq]
      exact hroot v
    | inr e =>
      have hEq : edgeMidpoint M hloopless e = a := by
        simpa [edgeMidpoint, ha'] using ha
      rw [← hEq]
      exact hmid e
  have hbroot : (subdivide M hloopless).toSimpleGraph.Reachable root' b := by
    cases hb' : zb with
    | inl v =>
      have hEq : oldVertex M hloopless v = b := by
        simpa [oldVertex, hb'] using hb
      rw [← hEq]
      exact hroot v
    | inr e =>
      have hEq : edgeMidpoint M hloopless e = b := by
        simpa [edgeMidpoint, hb'] using hb
      rw [← hEq]
      exact hmid e
  exact haroot.symm.trans hbroot

private theorem multiEdgeCoordinate_pullback_false (M : FiniteMultiGraph)
    (hloopless : ∀ e : M.Edge, M.src e ≠ M.dst e) (e : M.Edge) :
    dualPullback (restrictCycles M hloopless) (multiEdgeCoordinate M e) =
      edgeCoordinate (subdivide M hloopless) (halfEdge M hloopless e false) := by
  ext x
  rfl

private theorem halfEdge_true_coordinate_eq_false (M : FiniteMultiGraph)
    (hloopless : ∀ e : M.Edge, M.src e ≠ M.dst e) (e : M.Edge) :
    edgeCoordinate (subdivide M hloopless) (halfEdge M hloopless e true) =
      edgeCoordinate (subdivide M hloopless) (halfEdge M hloopless e false) := by
  ext x
  exact (subdivisionCycle_halves_equal M hloopless x e).symm

/-- Pullback of each multigraph vertex star is exactly the old-vertex star
in the simple subdivision. -/
theorem map_multiVertexStar_eq_subdivisionStar (M : FiniteMultiGraph)
    (hloopless : ∀ e : M.Edge, M.src e ≠ M.dst e) (v : M.Vertex) :
    (multiVertexStarSpace M v).map
      (dualPullback (restrictCycles M hloopless)) =
        vertexStarSpace (subdivide M hloopless) (oldVertex M hloopless v) := by
  classical
  let pull : (M.CycleSpace →ₗ[𝔽] 𝔽) →ₗ[𝔽]
      ((subdivide M hloopless).CycleSpace →ₗ[𝔽] 𝔽) :=
    dualPullback (restrictCycles M hloopless)
  change (multiVertexStarSpace M v).map pull = _
  rw [multiVertexStarSpace, Submodule.map_span]
  apply congrArg (Submodule.span 𝔽)
  simp only [pull]
  ext f
  constructor
  · rintro ⟨g, ⟨e, he, rfl⟩, rfl⟩
    rcases he with hs | ht
    · change dualPullback (restrictCycles M hloopless)
        (multiEdgeCoordinate M e) ∈ _
      rw [multiEdgeCoordinate_pullback_false]
      have hi : (subdivide M hloopless).incident
          (halfEdge M hloopless e false) (oldVertex M hloopless v) := by
        change (subdivide M hloopless).src (halfEdge M hloopless e false) =
            oldVertex M hloopless v ∨
          (subdivide M hloopless).dst (halfEdge M hloopless e false) =
            oldVertex M hloopless v
        simp [halfEdge, oldVertex, subdivide, subdivisionVertexEquiv,
          subdivisionEdgeEquiv, hs]
      exact ⟨_, hi, rfl⟩
    · change dualPullback (restrictCycles M hloopless)
        (multiEdgeCoordinate M e) ∈ _
      rw [multiEdgeCoordinate_pullback_false]
      rw [(halfEdge_true_coordinate_eq_false M hloopless e).symm]
      have hi : (subdivide M hloopless).incident
          (halfEdge M hloopless e true) (oldVertex M hloopless v) := by
        change (subdivide M hloopless).src (halfEdge M hloopless e true) =
            oldVertex M hloopless v ∨
          (subdivide M hloopless).dst (halfEdge M hloopless e true) =
            oldVertex M hloopless v
        simp [halfEdge, oldVertex, subdivide, subdivisionVertexEquiv,
          subdivisionEdgeEquiv, ht]
      exact ⟨_, hi, rfl⟩
  · intro hf
    change f ∈ {g | ∃ e, (subdivide M hloopless).incident e
      (oldVertex M hloopless v) ∧
        g = edgeCoordinate (subdivide M hloopless) e} at hf
    rcases hf with ⟨fedge, hinc, rfl⟩
    let p := (subdivisionEdgeEquiv M).symm fedge
    have hp : subdivisionEdgeEquiv M p = fedge := by
      dsimp [p]
      exact (subdivisionEdgeEquiv M).apply_symm_apply fedge
    have hdest : (if p.2 then M.dst p.1 else M.src p.1) = v := by
      rcases hinc with hs | hd
      · have heq := (subdivisionVertexEquiv M).injective hs
        cases heq
      · have heq := (subdivisionVertexEquiv M).injective hd
        simpa [oldVertex, subdivide, subdivisionVertexEquiv,
          subdivisionEdgeEquiv, p] using heq
    cases hb : p.2
    · refine ⟨multiEdgeCoordinate M p.1, ?_, ?_⟩
      · simp [hb] at hdest
        exact ⟨p.1, Or.inl hdest, rfl⟩
      · change dualPullback (restrictCycles M hloopless)
          (multiEdgeCoordinate M p.1) = _
        rw [multiEdgeCoordinate_pullback_false]
        change edgeCoordinate (subdivide M hloopless)
          (halfEdge M hloopless p.1 false) =
            edgeCoordinate (subdivide M hloopless) fedge
        rw [show halfEdge M hloopless p.1 false = fedge by
          unfold halfEdge
          rw [← hb]
          exact hp]
    · refine ⟨multiEdgeCoordinate M p.1, ?_, ?_⟩
      · simp [hb] at hdest
        exact ⟨p.1, Or.inr hdest, rfl⟩
      · change dualPullback (restrictCycles M hloopless)
          (multiEdgeCoordinate M p.1) = _
        rw [multiEdgeCoordinate_pullback_false]
        rw [(halfEdge_true_coordinate_eq_false M hloopless p.1).symm]
        change edgeCoordinate (subdivide M hloopless)
          (halfEdge M hloopless p.1 true) =
            edgeCoordinate (subdivide M hloopless) fedge
        rw [show halfEdge M hloopless p.1 true = fedge by
          unfold halfEdge
          rw [← hb]
          exact hp]

private theorem map_subspaceInter_eq
    {F X Y : Type*} [Field F] [AddCommGroup X] [Module F X]
    [AddCommGroup Y] [Module F Y]
    (f : X →ₗ[F] Y) (hf : Function.Injective f)
    (A B : Submodule F X) :
    (subspaceInter A B).map f = subspaceInter (A.map f) (B.map f) := by
  ext y
  constructor
  · intro hy
    change ∃ x, x ∈ subspaceInter A B ∧ f x = y at hy
    rcases hy with ⟨x, hx, rfl⟩
    exact ⟨⟨x, hx.1, rfl⟩, ⟨x, hx.2, rfl⟩⟩
  · intro hy
    rcases hy with ⟨hyA, hyB⟩
    change ∃ x, x ∈ A ∧ f x = y at hyA
    change ∃ z, z ∈ B ∧ f z = y at hyB
    rcases hyA with ⟨x, hx, hxy⟩
    rcases hyB with ⟨z, hz, hzy⟩
    have hxz : x = z := hf (hxy.trans hzy.symm)
    subst z
    change ∃ t, t ∈ subspaceInter A B ∧ f t = y
    exact ⟨x, ⟨hx, hz⟩, hxy⟩

private theorem map_multiTripleStar_eq
    (M : FiniteMultiGraph) (G : PhysicalGraph)
    (f : (M.CycleSpace →ₗ[𝔽] 𝔽) →ₗ[𝔽] (G.CycleSpace →ₗ[𝔽] 𝔽))
    (hf : Function.Injective f) (u v w : M.Vertex) :
    (multiTripleStarSpace M u v w).map f =
      subspaceInter (subspaceInter ((multiVertexStarSpace M u).map f)
        ((multiVertexStarSpace M v).map f))
        ((multiVertexStarSpace M w).map f) := by
  unfold multiTripleStarSpace
  rw [map_subspaceInter_eq f hf]
  rw [map_subspaceInter_eq f hf]

/-- A connected loopless multigraph's triple-star rank bound, proved by
subdividing every labelled edge into two physical edges. -/
theorem multiTripleStarSpace_finrank_le_one
    (M : FiniteMultiGraph)
    (hloopless : ∀ e : M.Edge, M.src e ≠ M.dst e)
    (hconn : M.toSimpleGraph.Connected)
    (u v w : M.Vertex) (huv : u ≠ v) (huw : u ≠ w) (hvw : v ≠ w) :
    Module.finrank 𝔽 (multiTripleStarSpace M u v w) ≤ 1 := by
  let G := subdivide M hloopless
  let r := restrictCycles M hloopless
  let pull : (M.CycleSpace →ₗ[𝔽] 𝔽) →ₗ[𝔽] (G.CycleSpace →ₗ[𝔽] 𝔽) :=
    dualPullback r
  have hpull : Function.Injective pull :=
    dualPullback_injective r (restrictCycles_surjective M hloopless)
  have hu' : oldVertex M hloopless u ≠ oldVertex M hloopless v := by
    intro h
    exact huv (Sum.inl.inj ((subdivisionVertexEquiv M).injective h))
  have hw' : oldVertex M hloopless u ≠ oldVertex M hloopless w := by
    intro h
    exact huw (Sum.inl.inj ((subdivisionVertexEquiv M).injective h))
  have hv' : oldVertex M hloopless v ≠ oldVertex M hloopless w := by
    intro h
    exact hvw (Sum.inl.inj ((subdivisionVertexEquiv M).injective h))
  have hspaces :
      (multiTripleStarSpace M u v w).map pull =
        tripleStarSpace G (oldVertex M hloopless u)
          (oldVertex M hloopless v) (oldVertex M hloopless w) := by
    rw [map_multiTripleStar_eq M G pull hpull]
    rw [map_multiVertexStar_eq_subdivisionStar M hloopless u]
    rw [map_multiVertexStar_eq_subdivisionStar M hloopless v]
    rw [map_multiVertexStar_eq_subdivisionStar M hloopless w]
    rfl
  have hdim := (Submodule.equivMapOfInjective pull hpull
    (multiTripleStarSpace M u v w)).finrank_eq
  calc
    Module.finrank 𝔽 (multiTripleStarSpace M u v w) =
        Module.finrank 𝔽 ((multiTripleStarSpace M u v w).map pull) := hdim
    _ = Module.finrank 𝔽
        (tripleStarSpace G (oldVertex M hloopless u)
          (oldVertex M hloopless v) (oldVertex M hloopless w)) := by rw [hspaces]
    _ ≤ 1 := tripleStar_finrank_le_one_of_connected G
      (oldVertex M hloopless u) (oldVertex M hloopless v)
      (oldVertex M hloopless w) (subdivide_connected M hloopless hconn)
      hu' hw' hv'

end Erdos1016.Proof.MultigraphSubdivisionTripleStar

end
