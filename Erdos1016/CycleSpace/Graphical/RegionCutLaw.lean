import Erdos1016.Graph.Multigraph.ConnectedContraction
import Erdos1016.CycleSpace.Graphical.MultigraphCutCorrelation

set_option autoImplicit false

/-!
# Joint cut laws for connected regions

A finite fiber labeling describes disjoint connected induced regions; the
remaining vertices may be singleton fibers. Contracting these regions gives
the exact vertex-cut law, with physical crossing-edge multiplicities intact.
-/

noncomputable section

namespace Erdos1016.FiniteMultiGraph.ConnectedContraction

open ExceptionalPartners LinkCorrelation

variable (G : FiniteMultiGraph) {Q : Type*} [Fintype Q] (fiber : G.Vertex → Q)

local instance regionCutDecidable (p : Prop) : Decidable p := Classical.propDecidable p

abbrev FiberCutIncidence (q : Q) :=
  {e : G.Edge // (fiber (G.src e) = q ∧ fiber (G.dst e) ≠ q) ∨
    (fiber (G.dst e) = q ∧ fiber (G.src e) ≠ q)}

def fiberCutSize (q : Q) : ℕ := Nat.card (FiberCutIncidence G fiber q)

/-- Exact identification of the original region cut with the contracted
vertex cut, one physical edge label at a time. -/
def cutIncidenceEquiv (q : Q) :
    FiberCutIncidence G fiber q ≃ CutIncidence (quotient G fiber) (vertexEquiv q) where
  toFun e := ⟨edgeEquiv G fiber ⟨e.1, by
      rcases e.2 with h | h
      · exact fun he => h.2 (he.symm.trans h.1)
      · exact fun he => h.2 (he.trans h.1)⟩, by
    simpa [quotient] using e.2⟩
  invFun e := ⟨((edgeEquiv G fiber).symm e.1).1, by
    have he := e.2
    simpa only [quotient, ne_eq, Equiv.apply_eq_iff_eq] using he⟩
  left_inv e := by
    apply Subtype.ext
    simp
  right_inv e := by
    apply Subtype.ext
    simp

theorem cutSizeAt_quotient (q : Q) :
    cutSizeAt (quotient G fiber) (vertexEquiv q) = fiberCutSize G fiber q := by
  rw [← cutIncidence_card, ← Nat.card_eq_fintype_card]
  exact (Nat.card_congr (cutIncidenceEquiv G fiber q)).symm

def FiberZeroCut (q : Q) (x : G.CycleSpace) : Prop :=
  ∀ e : FiberCutIncidence G fiber q, x.1 e.1 = 0

/-- Contracting a connected region preserves its actual zero-cut event. -/
theorem fiberZeroCut_iff (q : Q) (x : G.CycleSpace) :
    FiberZeroCut G fiber q x ↔
      ZeroCutAt (quotient G fiber) (vertexEquiv q) (project G fiber x) := by
  constructor
  · intro h e
    exact h ((cutIncidenceEquiv G fiber q).symm e)
  · intro h e
    have he := h (cutIncidenceEquiv G fiber q e)
    simpa [cutIncidenceEquiv, project, projectWord] using he

/-- Uniform contraction preserves the full joint law of any collection of
region-cut indicators. -/
theorem fiberZeroCut_joint_density (h : ConnectedFibers G fiber)
    (P : (Q → Prop) → Prop) :
    Finite.density (fun x : G.CycleSpace => P (fun q => FiberZeroCut G fiber q x)) =
      Finite.density (fun y : (quotient G fiber).CycleSpace =>
        P (fun q => ZeroCutAt (quotient G fiber) (vertexEquiv q) y)) := by
  have he : (fun x : G.CycleSpace => P (fun q => FiberZeroCut G fiber q x)) =
      fun x => P (fun q => ZeroCutAt (quotient G fiber) (vertexEquiv q) (project G fiber x)) := by
    funext x
    congr 1
    funext q
    exact propext (fiberZeroCut_iff G fiber q x)
  rw [he]
  exact density_project G fiber h (fun y =>
    P (fun q => ZeroCutAt (quotient G fiber) (vertexEquiv q) y))

theorem fiberZeroCut_density (h : ConnectedFibers G fiber) (q : Q) :
    Finite.density (FiberZeroCut G fiber q) =
      Finite.density (ZeroCutAt (quotient G fiber) (vertexEquiv q)) :=
  fiberZeroCut_joint_density G fiber h (fun P => P q)

theorem fiberZeroCut_pair_density (h : ConnectedFibers G fiber) (q r : Q) :
    Finite.density (fun x => FiberZeroCut G fiber q x ∧ FiberZeroCut G fiber r x) =
      Finite.density (fun x => ZeroCutAt (quotient G fiber) (vertexEquiv q) x ∧
        ZeroCutAt (quotient G fiber) (vertexEquiv r) x) :=
  fiberZeroCut_joint_density G fiber h (fun P => P q ∧ P r)

/-- The exceptional partners are defined by the actual joint law in the
original graph, rather than by a supplied combinatorial certificate. -/
def ExceptionalCut (q r : Q) : Prop :=
  2 * Finite.density (FiberZeroCut G fiber q) * Finite.density (FiberZeroCut G fiber r) <
    Finite.density (fun x => FiberZeroCut G fiber q x ∧ FiberZeroCut G fiber r x)

/-- Lemma 1 for arbitrary connected fibers: no distinct family of genuinely
exceptional cut events exceeds the original physical cut size. -/
theorem exceptionalCut_partner_card_le (hG : G.toSimpleGraph.Connected)
    (h : ConnectedFibers G fiber) (q : Q) (s : Finset Q) :
    (s.filter fun r => r ≠ q ∧ ExceptionalCut G fiber q r).card ≤ fiberCutSize G fiber q := by
  let S := s.filter fun r => r ≠ q ∧ ExceptionalCut G fiber q r
  let vertex : S → DeletedVertex (vertexEquiv q) := fun r =>
    ⟨vertexEquiv r.1, fun heq => (Finset.mem_filter.mp r.2).2.1 (vertexEquiv.injective heq)⟩
  have hinj : Function.Injective vertex := by
    intro r t heq
    apply Subtype.ext
    exact vertexEquiv.injective (congrArg Subtype.val heq)
  have hlinks (r : S) :
      3 ≤ Nat.card (MultigraphLink (quotient G fiber) (vertexEquiv q) (vertex r)) := by
    by_contra hn
    have hn' : Nat.card (MultigraphLink (quotient G fiber) (vertexEquiv q) (vertex r)) ≤ 2 := by omega
    have hpair := multigraph_zeroCut_pair_le_two (quotient G fiber)
      (quotient_connected G fiber hG h) (vertexEquiv q) (vertex r) hn'
    change Finite.density (fun x => ZeroCutAt (quotient G fiber) (vertexEquiv q) x ∧
      ZeroCutAt (quotient G fiber) (vertexEquiv r.1) x) ≤ _ at hpair
    rw [← fiberZeroCut_pair_density G fiber h q r.1,
      ← fiberZeroCut_density G fiber h q, ← fiberZeroCut_density G fiber h r.1] at hpair
    exact (not_lt_of_ge hpair) (Finset.mem_filter.mp r.2).2.2
  have hcount := multigraph_family_card_le_cut (Finset.univ : Finset S)
    (quotient G fiber) (vertexEquiv q) vertex (fun _ _ _ _ heq => hinj heq)
    (fun r _ => hlinks r)
  rw [cutSizeAt_quotient] at hcount
  simpa only [Finset.card_univ, Fintype.card_coe] using hcount

end Erdos1016.FiniteMultiGraph.ConnectedContraction
