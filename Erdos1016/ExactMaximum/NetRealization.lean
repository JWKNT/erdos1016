import Erdos1016.ExactMaximum.LooplessBridge
import Erdos1016.ExactMaximumSupport.PhysicalCycleCount
import Erdos1016.Graph.RankNormalization

set_option autoImplicit false

/-!
# A network without parallel edges as a simple graph

The lower bound of the exact maximum is a statement about `SimpleGraph (Fin n)`, with cycles
counted by their edge sets. The ring is a `Network` on its own types of vertices and edges. This
file moves the count from one to the other.

* A relabelling of a network keeps the number of cycles and the rank (`Relabel.numCycles_eq`,
  `Relabel.networkRank_eq`). The proof uses the description of a cycle as a minimal nonzero even
  word, which a relabelling keeps.
* A network without parallel edges, with its vertices and edges numbered, is a `PhysicalGraph`.
  Its simple graph has the same number of cycles and the same cyclomatic number
  (`exists_simpleGraph_of_network`). The step from cycle words to cycles of the simple graph is
  `CycleCount.numCycles_toSimpleGraph_eq_asMultigraph`, proved by Astra.
-/

noncomputable section
open scoped BigOperators

namespace Erdos1016.BoundaryTrace.Network

open BoundaryDecay

local instance netRealizationDecidable (p : Prop) : Decidable p := Classical.propDecidable p

universe u₁ u₂ u₃ u₄

variable {V : Type u₁} {E : Type u₂} {V' : Type u₃} {E' : Type u₄}

/-- A relabelling of the vertices and the edges of a network. -/
structure Relabel (N : Network V E) (N' : Network V' E') where
  /-- The relabelling of the vertices. -/
  φ : V ≃ V'
  /-- The relabelling of the edges. -/
  ψ : E ≃ E'
  src : ∀ e, N'.src (ψ e) = φ (N.src e)
  dst : ∀ e, N'.dst (ψ e) = φ (N.dst e)

namespace Relabel

variable {N : Network V E} {N' : Network V' E'} (R : Relabel N N')

/-- The inverse relabelling. -/
def symm : Relabel N' N where
  φ := R.φ.symm
  ψ := R.ψ.symm
  src e' := by
    have h := R.src (R.ψ.symm e')
    rw [Equiv.apply_symm_apply] at h
    rw [h, Equiv.symm_apply_apply]
  dst e' := by
    have h := R.dst (R.ψ.symm e')
    rw [Equiv.apply_symm_apply] at h
    rw [h, Equiv.symm_apply_apply]

/-- The word of the relabelled network. -/
def push (x : E → Bit) : E' → Bit := fun e' => x (R.ψ.symm e')

theorem push_apply (x : E → Bit) (e : E) : R.push x (R.ψ e) = x e := by
  show x (R.ψ.symm (R.ψ e)) = x e
  rw [Equiv.symm_apply_apply]

theorem symm_push_push (x : E → Bit) : R.symm.push (R.push x) = x := by
  funext e
  show x (R.ψ.symm (R.symm.ψ.symm e)) = x e
  show x (R.ψ.symm (R.ψ e)) = x e
  rw [Equiv.symm_apply_apply]

theorem push_symm_push (y : E' → Bit) : R.push (R.symm.push y) = y := by
  funext e'
  show y (R.symm.ψ.symm (R.ψ.symm e')) = y e'
  show y (R.ψ (R.ψ.symm e')) = y e'
  rw [Equiv.apply_symm_apply]

theorem push_zero : R.push (0 : E → Bit) = 0 := rfl

theorem push_injective : Function.Injective R.push := by
  intro x y h
  rw [← R.symm_push_push x, ← R.symm_push_push y, h]

theorem push_ne_zero {x : E → Bit} (h : x ≠ 0) : R.push x ≠ 0 := by
  intro h0
  apply h
  apply R.push_injective
  rw [h0, push_zero]

theorem isSubword_push {x y : E → Bit} (h : N.IsSubword y x) :
    N'.IsSubword (R.push y) (R.push x) := fun e' he' => h (R.ψ.symm e') he'

variable [Fintype V] [Fintype E] [Fintype V'] [Fintype E']

/-- A relabelling commutes with the boundary. -/
theorem boundary_push (x : E → Bit) (v : V) :
    N'.boundary (R.push x) (R.φ v) = N.boundary x v := by
  rw [boundary_apply, boundary_apply]
  have h1 : (∑ e', if N'.src e' = R.φ v then R.push x e' else 0) =
      ∑ e, if N.src e = v then x e else 0 := by
    rw [← Equiv.sum_comp R.ψ]
    apply Finset.sum_congr rfl
    intro e _
    rw [R.src, R.push_apply]
    by_cases h : N.src e = v
    · rw [if_pos h, if_pos (by rw [h])]
    · rw [if_neg h, if_neg (fun h' => h (R.φ.injective h'))]
  have h2 : (∑ e', if N'.dst e' = R.φ v then R.push x e' else 0) =
      ∑ e, if N.dst e = v then x e else 0 := by
    rw [← Equiv.sum_comp R.ψ]
    apply Finset.sum_congr rfl
    intro e _
    rw [R.dst, R.push_apply]
    by_cases h : N.dst e = v
    · rw [if_pos h, if_pos (by rw [h])]
    · rw [if_neg h, if_neg (fun h' => h (R.φ.injective h'))]
  rw [h1, h2]

theorem boundary_push_eq_zero {x : E → Bit} (h : N.boundary x = 0) :
    N'.boundary (R.push x) = 0 := by
  funext v'
  have h1 := R.boundary_push x (R.φ.symm v')
  rw [Equiv.apply_symm_apply] at h1
  rw [h1, h]
  rfl

/-- A relabelled cycle is a cycle. -/
theorem isCycleWord_push {x : E → Bit} (hx : N.IsCycleWord x) :
    N'.IsCycleWord (R.push x) := by
  obtain ⟨h1, h2, h3⟩ := (N.isCycleWord_iff_minimal x).1 hx
  apply N'.isCycleWord_of_minimal (R.push_ne_zero h1) (R.boundary_push_eq_zero h2)
  intro y' hsub hy'
  -- pull the sub-word back
  have hsub' : N.IsSubword (R.symm.push y') x := by
    have h := R.symm.isSubword_push hsub
    rw [R.symm_push_push] at h
    exact h
  rcases h3 (R.symm.push y') hsub' (R.symm.boundary_push_eq_zero hy') with h | h
  · left
    rw [← R.push_symm_push y', h, push_zero]
  · right
    rw [← R.push_symm_push y', h]

/-- **A relabelling keeps the number of cycles.** -/
theorem numCycles_eq (R : Relabel N N') : N'.numCycles = N.numCycles := by
  let f : {x : N.Word // N.IsCycleWord x} → {y : N'.Word // N'.IsCycleWord y} := fun x =>
    ⟨R.push x.1, R.isCycleWord_push x.2⟩
  have hf : Function.Bijective f := by
    constructor
    · intro a b hab
      have h' : (f a).1 = (f b).1 := congrArg Subtype.val hab
      exact Subtype.ext (R.push_injective h')
    · rintro ⟨y, hy⟩
      refine ⟨⟨R.symm.push y, ?_⟩, ?_⟩
      · exact R.symm.isCycleWord_push hy
      · exact Subtype.ext (R.push_symm_push y)
  exact (Nat.card_eq_of_bijective f hf).symm

/-- **A relabelling keeps the rank.** -/
theorem networkRank_eq (R : Relabel N N') : networkRank N' = networkRank N := by
  let f : N.CycleSpace → N'.CycleSpace := fun x =>
    ⟨R.push x.1, LinearMap.mem_ker.2 (R.boundary_push_eq_zero (LinearMap.mem_ker.1 x.2))⟩
  have hf : Function.Bijective f := by
    constructor
    · intro a b hab
      have h' : (f a).1 = (f b).1 := congrArg Subtype.val hab
      exact Subtype.ext (R.push_injective h')
    · rintro ⟨y, hy⟩
      refine ⟨⟨R.symm.push y,
        LinearMap.mem_ker.2 (R.symm.boundary_push_eq_zero (LinearMap.mem_ker.1 hy))⟩, ?_⟩
      exact Subtype.ext (R.push_symm_push y)
  have hcard := Fintype.card_of_bijective hf
  rw [cycleSpace_card_network, cycleSpace_card_network] at hcard
  exact (Nat.pow_right_injective (le_refl 2) hcard).symm

end Relabel

/-! ### The simple graph of a network without parallel edges -/

variable [Fintype V] [Fintype E]

/-- **A network without parallel edges is a simple graph.** Let no two edges of the network `N`
have the same two ends. Then some simple graph on `Fin n` has the cyclomatic number
`networkRank N` and exactly `N.numCycles` cycles. -/
theorem exists_simpleGraph_of_network (N : Network V E)
    (hsimple : ∀ e f, N.Joins e (N.src f) (N.dst f) → e = f) :
    ∃ (n : ℕ) (G : SimpleGraph (Fin n)),
      networkRank N + n = Nat.card G.edgeSet + Nat.card G.ConnectedComponent ∧
        CycleCount.numCycles G = N.numCycles := by
  obtain ⟨ev⟩ : Nonempty (V ≃ Fin (Fintype.card V)) := ⟨Fintype.equivFin V⟩
  obtain ⟨ee⟩ : Nonempty (E ≃ Fin (Fintype.card E)) := ⟨Fintype.equivFin E⟩
  -- the physical graph
  obtain ⟨P, hPv, hPsrc, hPdst⟩ : ∃ P : PhysicalGraph, ∃ hv : P.vertexCount = Fintype.card V,
      ∃ he : P.edgeCount = Fintype.card E,
        (∀ e : E, P.src (Fin.cast he.symm (ee e)) = Fin.cast hv.symm (ev (N.src e))) ∧
        (∀ e : E, P.dst (Fin.cast he.symm (ee e)) = Fin.cast hv.symm (ev (N.dst e))) := by
    refine ⟨⟨Fintype.card V, Fintype.card E, fun j => ev (N.src (ee.symm j)),
      fun j => ev (N.dst (ee.symm j)), ?_, ?_⟩, rfl, rfl, ?_, ?_⟩
    · intro j h
      exact N.noLoops _ (ev.injective h)
    · intro e f h
      have hj : N.Joins (ee.symm e) (N.src (ee.symm f)) (N.dst (ee.symm f)) := by
        rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩
        · exact Or.inl ⟨ev.injective h1, ev.injective h2⟩
        · exact Or.inr ⟨ev.injective h1, ev.injective h2⟩
      exact ee.symm.injective (hsimple _ _ hj)
    · intro e
      show ev (N.src (ee.symm (ee e))) = ev (N.src e)
      rw [Equiv.symm_apply_apply]
    · intro e
      show ev (N.dst (ee.symm (ee e))) = ev (N.dst e)
      rw [Equiv.symm_apply_apply]
  obtain ⟨hv, he, hsrc, hdst⟩ : ∃ hv : P.vertexCount = Fintype.card V,
      ∃ he : P.edgeCount = Fintype.card E,
        (∀ e : E, P.src (Fin.cast he.symm (ee e)) = Fin.cast hv.symm (ev (N.src e))) ∧
        (∀ e : E, P.dst (Fin.cast he.symm (ee e)) = Fin.cast hv.symm (ev (N.dst e))) :=
    ⟨hPv, hPsrc, hPdst⟩
  -- the relabelling of the vertices and of the edges
  let φ : V ≃ Fin P.vertexCount := ev.trans (finCongr hv.symm)
  let ψ : E ≃ Fin P.edgeCount := ee.trans (finCongr he.symm)
  have hφ : ∀ v, φ v = Fin.cast hv.symm (ev v) := fun _ => rfl
  have hψ : ∀ e, ψ e = Fin.cast he.symm (ee e) := fun _ => rfl
  -- the relabelling to the trace network: the rank
  let R₁ : Relabel N P.traceNetwork :=
    ⟨φ, ψ, fun e => by rw [hψ, hφ]; exact hsrc e, fun e => by rw [hψ, hφ]; exact hdst e⟩
  have hrank : P.cycleRank = networkRank N := by
    rw [← BoundaryDecay.rank_traceNetwork P]
    exact R₁.networkRank_eq
  -- the relabelling to the network of the multigraph: the cycles
  have hloop : (ShortProof.CycleCore.asMultigraph P).IsLoopless := fun e => P.noLoops e
  let ψ₂ : E ≃ FiniteMultiGraph.NonloopEdge (ShortProof.CycleCore.asMultigraph P) :=
    ψ.trans (Equiv.subtypeUnivEquiv hloop).symm
  let R₂ : Relabel N (FiniteMultiGraph.looplessNetwork (ShortProof.CycleCore.asMultigraph P)) :=
    ⟨φ, ψ₂, fun e => by
        show P.src (ψ e) = φ (N.src e)
        rw [hψ, hφ]
        exact hsrc e, fun e => by
        show P.dst (ψ e) = φ (N.dst e)
        rw [hψ, hφ]
        exact hdst e⟩
  have hcycles : CycleCount.numCycles P.toSimpleGraph = N.numCycles := by
    rw [CycleCount.numCycles_toSimpleGraph_eq_asMultigraph,
      FiniteMultiGraph.numCycles_eq_looplessNetwork hloop]
    exact R₂.numCycles_eq
  -- the edges of the simple graph
  have hedges : Nat.card P.toSimpleGraph.edgeSet = P.edgeCount := by
    let f : Fin P.edgeCount → P.toSimpleGraph.edgeSet := fun e =>
      ⟨s(P.src e, P.dst e), (SimpleGraph.mem_edgeSet _).2 ⟨e, one_ne_zero, Or.inl ⟨rfl, rfl⟩⟩⟩
    have hf : Function.Bijective f := by
      constructor
      · intro a b hab
        have h' : (f a).1 = (f b).1 := congrArg Subtype.val hab
        exact P.simple a b (Sym2.eq_iff.1 h')
      · rintro ⟨a, ha⟩
        revert ha
        refine Sym2.inductionOn a ?_
        intro u v huv
        obtain ⟨e, _, h | h⟩ := (SimpleGraph.mem_edgeSet _).1 huv
        · exact ⟨e, Subtype.ext (Sym2.eq_iff.2 (Or.inl h))⟩
        · exact ⟨e, Subtype.ext (Sym2.eq_iff.2 (Or.inr h))⟩
    rw [← Nat.card_eq_of_bijective f hf, Nat.card_eq_fintype_card, Fintype.card_fin]
  -- the components of the simple graph
  have hcomp : Fintype.card P.traceNetwork.Component =
      Nat.card P.toSimpleGraph.ConnectedComponent := by
    rw [← Nat.card_eq_fintype_card]
    exact Nat.card_congr (Equiv.cast
      (congrArg (fun Q : SimpleGraph (Fin P.vertexCount) => Q.ConnectedComponent)
        (PhysicalGraph.traceNetwork_graph P)))
  refine ⟨P.vertexCount, P.toSimpleGraph, ?_, hcycles⟩
  have hEuler := PhysicalGraph.cycleRank_euler_components P
  rw [hrank, hcomp] at hEuler
  rw [hedges]
  exact hEuler

end Erdos1016.BoundaryTrace.Network
