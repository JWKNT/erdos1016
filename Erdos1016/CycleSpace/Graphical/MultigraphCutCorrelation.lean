import Erdos1016.CycleSpace.Graphical.LinkCorrelation
import Erdos1016.Graph.Multigraph.LoopDecomposition

set_option autoImplicit false

/-!
# Exact vertex-cut correlations in labelled multigraphs

Loop coordinates are independent and irrelevant to cuts. Parallel nonloop
edges remain separate links. The link type here is exactly the one whose
exceptional partners are bounded by the terminal-forest argument.
-/

noncomputable section

namespace Erdos1016.LinkCorrelation

open ExceptionalPartners BoundaryTrace BoundaryDecay
open FiniteMultiGraph

local instance multigraphCorrelationDecidable (p : Prop) : Decidable p :=
  Classical.propDecidable p

/-- The attachment vertices of the cut incidences are exactly the neighbors
of the deleted vertex. -/
theorem mem_attachmentVertices_iff (M : FiniteMultiGraph) (v : M.Vertex)
    (x : DeletedVertex v) :
    x ∈ attachmentVertices (otherEndpoint M v) ↔ M.toSimpleGraph.Adj v x.1 := by
  simp only [attachmentVertices, Finset.mem_image, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨e, he⟩
    have h := (otherEndpoint_eq_iff M v e x).mp (congrArg Subtype.val he)
    refine ⟨x.2.symm, e.1, ?_⟩
    rcases h with h | h
    · exact Or.inl h
    · exact Or.inr ⟨h.2, h.1⟩
  · rintro ⟨hvx, e, h | h⟩
    · let i : CutIncidence M v := ⟨e, Or.inl ⟨h.1, by simpa [h.2] using x.2⟩⟩
      refine ⟨i, Subtype.ext ?_⟩
      exact (otherEndpoint_eq_iff M v i x).mpr (Or.inl h)
    · let i : CutIncidence M v := ⟨e, Or.inr ⟨h.2, by simpa [h.1] using x.2⟩⟩
      refine ⟨i, Subtype.ext ?_⟩
      exact (otherEndpoint_eq_iff M v i x).mpr (Or.inr ⟨h.2, h.1⟩)

/-- The terminal-branch predicate is precisely attachment to both deleted
vertices, expressed on the same double-deletion component. -/
def terminalBranchEquiv (M : FiniteMultiGraph) (v : M.Vertex) (w : DeletedVertex v) :
    TerminalBranch (deleted M.toSimpleGraph v) (attachmentVertices (otherEndpoint M v)) w ≃
      {c : (deleted (deleted M.toSimpleGraph v) w).ConnectedComponent //
        AttachedFirst M.toSimpleGraph v w c ∧ AttachedSecond M.toSimpleGraph v w c} := by
  apply Equiv.subtypeEquivRight
  intro c
  rw [terminalBranch_condition_iff, attachedFirst_iff, attachedSecond_iff]
  simp only [mem_attachmentVertices_iff]
  rfl

/-- Direct links correspond one-for-one to their nonloop physical edge labels. -/
def directIncidenceEquiv (M : FiniteMultiGraph) (v : M.Vertex) (w : DeletedVertex v) :
    {i : CutIncidence M v // otherEndpoint M v i = w} ≃
      DirectEdge (looplessNetwork M) v w.1 where
  toFun i := ⟨⟨i.1.1, by
      have h := (otherEndpoint_eq_iff M v i.1 w).mp (congrArg Subtype.val i.2)
      rcases h with h | h
      · exact fun he => w.2 (h.2.symm.trans (he.symm.trans h.1))
      · exact fun he => w.2 (h.2.symm.trans (he.trans h.1))⟩, by
    have h := (otherEndpoint_eq_iff M v i.1 w).mp (congrArg Subtype.val i.2)
    rcases h with h | h
    · exact Or.inl h
    · exact Or.inr ⟨h.2, h.1⟩⟩
  invFun e := ⟨⟨e.1.1, by
      rcases e.2 with h | h
      · exact Or.inl ⟨h.1, fun hd => w.2 (h.2.symm.trans hd)⟩
      · exact Or.inr ⟨h.2, fun hs => w.2 (h.1.symm.trans hs)⟩⟩, by
    apply Subtype.ext
    apply (otherEndpoint_eq_iff M v _ w).mpr
    rcases e.2 with h | h
    · exact Or.inl h
    · exact Or.inr ⟨h.2, h.1⟩⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-- Both definitions count the same physical links, including all parallel
edges and all components incident to both vertices. -/
theorem multigraphLink_card (M : FiniteMultiGraph) (v : M.Vertex) (w : DeletedVertex v) :
    Nat.card (MultigraphLink M v w) = Nat.card (NetworkLink (looplessNetwork M) v w) := by
  change Nat.card ({i : CutIncidence M v // otherEndpoint M v i = w} ⊕
    TerminalBranch (deleted M.toSimpleGraph v) (attachmentVertices (otherEndpoint M v)) w) = _
  rw [Nat.card_sum]
  change _ = Nat.card (DirectEdge (looplessNetwork M) v w.1 ⊕ _)
  rw [Nat.card_sum, Nat.card_congr (directIncidenceEquiv M v w),
    Nat.card_congr (terminalBranchEquiv M v w), looplessNetwork_graph]

/-- No physical edge crossing the singleton cut is selected. Loops at the
vertex are deliberately unrestricted. -/
def ZeroCutAt (M : FiniteMultiGraph) (v : M.Vertex) (x : M.CycleSpace) : Prop :=
  ∀ e : CutIncidence M v, x.1 e.1 = 0

/-- Exact event transport through the independent loop-coordinate factor. -/
theorem zeroCutAt_iff_projection (M : FiniteMultiGraph) (v : M.Vertex) (x : M.CycleSpace) :
    ZeroCutAt M v x ↔ ZeroAt (looplessNetwork M) v ((loopCycleSpaceEquiv M x).2) := by
  constructor
  · intro h e he
    apply h ⟨e.1, ?_⟩
    rcases he with he | he
    · exact Or.inl ⟨he, fun hd => e.2 (he.trans hd.symm)⟩
    · exact Or.inr ⟨he, fun hs => e.2 (hs.trans he.symm)⟩
  · intro h e
    have hn : M.src e.1 ≠ M.dst e.1 := by
      rcases e.2 with he | he
      · exact fun heq => he.2 (heq.symm.trans he.1)
      · exact fun heq => he.2 (heq.trans he.1)
    apply h ⟨e.1, hn⟩
    rcases e.2 with he | he
    · exact Or.inl he.1
    · exact Or.inr he.1

/-- The claimed exact link-correlation formula, now for the actual labelled
multigraph and the same link type used in the exceptional-partner bound. -/
theorem multigraph_zeroCut_pair (M : FiniteMultiGraph) (hM : M.toSimpleGraph.Connected)
    (v : M.Vertex) (w : DeletedVertex v) :
    Finite.density (fun x : M.CycleSpace => ZeroCutAt M v x ∧ ZeroCutAt M w.1 x) =
      dyadic ((Nat.card (MultigraphLink M v w) : ℤ) - 1) *
        Finite.density (ZeroCutAt M v) * Finite.density (ZeroCutAt M w.1) := by
  have hsingle (u : M.Vertex) : Finite.density (ZeroCutAt M u) =
      Finite.density (ZeroAt (looplessNetwork M) u) := by
    have he : ZeroCutAt M u = fun x =>
        ZeroAt (looplessNetwork M) u ((loopCycleSpaceEquiv M x).2) := by
      funext x
      exact propext (zeroCutAt_iff_projection M u x)
    rw [he, density_loopless_projection]
  have hpair : Finite.density (fun x : M.CycleSpace => ZeroCutAt M v x ∧ ZeroCutAt M w.1 x) =
      Finite.density (fun x : (looplessNetwork M).CycleSpace =>
        ZeroAt (looplessNetwork M) v x ∧ ZeroAt (looplessNetwork M) w.1 x) := by
    have he : (fun x : M.CycleSpace => ZeroCutAt M v x ∧ ZeroCutAt M w.1 x) =
        fun x => ZeroAt (looplessNetwork M) v ((loopCycleSpaceEquiv M x).2) ∧
          ZeroAt (looplessNetwork M) w.1 ((loopCycleSpaceEquiv M x).2) := by
      funext x
      exact propext (and_congr (zeroCutAt_iff_projection M v x)
        (zeroCutAt_iff_projection M w.1 x))
    rw [he]
    exact density_loopless_projection M (fun x =>
      ZeroAt (looplessNetwork M) v x ∧ ZeroAt (looplessNetwork M) w.1 x)
  rw [hpair, hsingle v, hsingle w.1, multigraphLink_card]
  exact network_zeroCut_pair (looplessNetwork M) (by simpa only [looplessNetwork_graph] using hM) v w

/-- Every nonexceptional pair has correlation at most two. -/
theorem multigraph_zeroCut_pair_le_two (M : FiniteMultiGraph)
    (hM : M.toSimpleGraph.Connected) (v : M.Vertex) (w : DeletedVertex v)
    (hlinks : Nat.card (MultigraphLink M v w) ≤ 2) :
    Finite.density (fun x : M.CycleSpace => ZeroCutAt M v x ∧ ZeroCutAt M w.1 x) ≤
      2 * Finite.density (ZeroCutAt M v) * Finite.density (ZeroCutAt M w.1) := by
  rw [multigraph_zeroCut_pair M hM v w]
  have hfactor : dyadic ((Nat.card (MultigraphLink M v w) : ℤ) - 1) ≤ 2 := by
    have h := dyadic_mono (show (Nat.card (MultigraphLink M v w) : ℤ) - 1 ≤ 1 by omega)
    simpa [dyadic] using h
  exact mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right hfactor (Finite.density_nonneg _)) (Finite.density_nonneg _)

end Erdos1016.LinkCorrelation
