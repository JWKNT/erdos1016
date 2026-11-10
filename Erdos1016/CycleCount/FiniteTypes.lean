import Erdos1016.CycleCount.Asymptotic

set_option autoImplicit false

/-!
# The cycle-count bound on any finite vertex type

The target statement uses graphs on `Fin n`. A graph isomorphism preserves
the number of edges, the number of components, and the number of cycles.
Hence the bound holds for simple graphs on every finite vertex type.
-/

noncomputable section

namespace Erdos1016.CycleCount

/-- A graph isomorphism does not lose a cycle. -/
theorem numCycles_le_of_iso {V W : Type*} [Fintype W] {G : SimpleGraph V}
    {H : SimpleGraph W} (φ : G ≃g H) : numCycles G ≤ numCycles H := by
  classical
  have hmaps : ∀ s ∈ cycleEdgeSets G, (Sym2.map φ) '' s ∈ cycleEdgeSets H := by
    rintro s ⟨v, p, hp, rfl⟩
    refine ⟨φ v, p.map φ.toHom, ?_, ?_⟩
    · exact (SimpleGraph.Walk.map_isCycle_iff_of_injective φ.injective).2 hp
    · ext a
      simp only [Set.mem_image, Set.mem_setOf_eq, SimpleGraph.Walk.edges_map, List.mem_map]
      rfl
  have hinj : Set.InjOn (fun s : Set (Sym2 V) => (Sym2.map φ) '' s) (cycleEdgeSets G) := by
    intro s _ t _ h
    exact (Set.image_injective.mpr (Sym2.map.injective φ.injective)) h
  have hfin : (cycleEdgeSets H).Finite := Set.toFinite _
  unfold numCycles
  calc (cycleEdgeSets G).ncard
      = ((fun s : Set (Sym2 V) => (Sym2.map φ) '' s) '' cycleEdgeSets G).ncard :=
        (Set.ncard_image_of_injOn hinj).symm
    _ ≤ (cycleEdgeSets H).ncard := by
        refine Set.ncard_le_ncard ?_ hfin
        rintro _ ⟨s, hs, rfl⟩
        exact hmaps s hs

/-- The cycle-count bound for simple graphs on any finite vertex type. -/
def GeneralCycleCountStatement : Prop :=
  ∃ r₁ : ℕ, ∀ (V : Type) [Fintype V] (G : SimpleGraph V) (r : ℕ),
    r + Fintype.card V = Nat.card G.edgeSet + Nat.card G.ConnectedComponent → r₁ ≤ r →
    (numCycles G : ℝ) ≤
      (1 / 2 + 21 / Real.logb 2 (Real.logb 2 (Real.logb 2 (r : ℝ)))) * 2 ^ r

/-- The statement on `Fin n` implies the statement on every finite type. -/
theorem generalCycleCountStatement_of_statement (h : CycleCountStatement) :
    GeneralCycleCountStatement := by
  obtain ⟨r₁, h₁⟩ := h
  refine ⟨r₁, ?_⟩
  intro V _ G r hr hrr
  classical
  let φ : G ≃g G.map (Fintype.equivFin V).toEmbedding :=
    SimpleGraph.Iso.map (Fintype.equivFin V) G
  have hE : Nat.card (G.map (Fintype.equivFin V).toEmbedding).edgeSet =
      Nat.card G.edgeSet := Nat.card_congr φ.mapEdgeSet.symm
  have hC : Nat.card (G.map (Fintype.equivFin V).toEmbedding).ConnectedComponent =
      Nat.card G.ConnectedComponent := Nat.card_congr φ.connectedComponentEquiv.symm
  have hb := h₁ (Fintype.card V) (G.map (Fintype.equivFin V).toEmbedding) r
    (by rw [hE, hC]; exact hr) hrr
  have hle : (numCycles G : ℝ) ≤
      (numCycles (G.map (Fintype.equivFin V).toEmbedding) : ℝ) := by
    exact_mod_cast numCycles_le_of_iso φ
  exact hle.trans hb

end Erdos1016.CycleCount
