import Erdos1016.Graph.Basic

set_option autoImplicit false

/-!
# Local capacity of linear forests

For a prescribed odd-vertex demand, count the distinct edge counts of
acyclic, maximum-degree-two physical edge sets realizing that demand. The
normalization is by the size of a cycle-space fiber, `2 ^ cycleRank`.
-/

noncomputable section

namespace Erdos1016.PhysicalGraph

/-- An edge word is a linear forest when its selected graph is acyclic and
has maximum degree at most two. -/
def IsLinearForest (G : PhysicalGraph) (x : G.Word) : Prop :=
  G.IsForest x ∧ ∀ v, G.selectedDegree x v ≤ 2

/-- Words whose boundary is the demand and whose support is a linear forest. -/
def LinearForestWord (G : PhysicalGraph) (t : G.Demand) :=
  {x : G.Word // G.boundary x = t ∧ G.IsLinearForest x}

noncomputable instance linearForestWordFintype (G : PhysicalGraph) (t : G.Demand) :
    Fintype (G.LinearForestWord t) := by
  classical
  letI : Fintype G.Word := inferInstance
  haveI : Finite (G.LinearForestWord t) :=
    Finite.of_injective (fun x : G.LinearForestWord t => x.1) (by
      intro x y h
      exact Subtype.ext h)
  exact Fintype.ofFinite _

/-- Distinct lengths of linear forests realizing `t`. -/
def linearForestLengths (G : PhysicalGraph) (t : G.Demand) : Finset ℕ :=
  Finset.univ.image fun x : G.LinearForestWord t => G.wordLength x.1

/-- The paper's local multiplicity `μ_F(t)`. -/
def linearForestMultiplicity (G : PhysicalGraph) (t : G.Demand) : ℕ :=
  (G.linearForestLengths t).card

theorem wordLength_mem_range (G : PhysicalGraph) (x : G.Word) :
    G.wordLength x ∈ Finset.range (G.edgeCount + 1) :=
  Finset.mem_range.mpr (Nat.lt_succ_of_le (G.wordLength_le x))

theorem linearForestMultiplicity_le_edgeCount_add_one
    (G : PhysicalGraph) (t : G.Demand) :
    G.linearForestMultiplicity t ≤ G.edgeCount + 1 := by
  unfold linearForestMultiplicity linearForestLengths
  calc
    (Finset.univ.image fun x : G.LinearForestWord t => G.wordLength x.1).card ≤
        (Finset.range (G.edgeCount + 1)).card := by
      apply Finset.card_le_card
      intro n hn
      rcases Finset.mem_image.mp hn with ⟨x, _, rfl⟩
      exact G.wordLength_mem_range x.1
    _ = G.edgeCount + 1 := Finset.card_range _

theorem zero_isLinearForest (G : PhysicalGraph) : G.IsLinearForest 0 := by
  constructor
  · have hbot : G.selectedGraph 0 = (⊥ : SimpleGraph G.Vertex) := by
      ext u v
      simp [PhysicalGraph.selectedGraph]
    rw [PhysicalGraph.IsForest, hbot]
    exact SimpleGraph.isAcyclic_bot
  · intro v
    simp [PhysicalGraph.selectedDegree, PhysicalGraph.incident]

theorem emptyDemand_zero_mem_linearForestLengths (G : PhysicalGraph) :
    0 ∈ G.linearForestLengths 0 := by
  unfold linearForestLengths
  apply Finset.mem_image.mpr
  refine ⟨⟨0, ?_⟩, Finset.mem_univ _, ?_⟩
  · simp
    exact G.zero_isLinearForest
  · simp [PhysicalGraph.wordLength_zero]

theorem one_le_emptyDemand_multiplicity (G : PhysicalGraph) :
    1 ≤ G.linearForestMultiplicity 0 := by
  unfold linearForestMultiplicity
  have h := Finset.card_pos.mpr ⟨0, G.emptyDemand_zero_mem_linearForestLengths⟩
  omega

/-- Maximum number of distinct linear-forest lengths over all demands. -/
def maxLinearForestMultiplicity (G : PhysicalGraph) : ℕ :=
  Finset.univ.sup G.linearForestMultiplicity

theorem linearForestMultiplicity_le_max (G : PhysicalGraph) (t : G.Demand) :
    G.linearForestMultiplicity t ≤ G.maxLinearForestMultiplicity := by
  unfold maxLinearForestMultiplicity
  exact Finset.le_sup (Finset.mem_univ t)

theorem one_le_maxLinearForestMultiplicity (G : PhysicalGraph) :
    1 ≤ G.maxLinearForestMultiplicity := by
  exact (G.one_le_emptyDemand_multiplicity).trans
    (G.linearForestMultiplicity_le_max 0)

/-- The local capacity `a(F) = 2^{-β(F)} max_t μ_F(t)`, written as division
by the cardinality `2^β` of each feasible boundary fiber. -/
def normalizedLinearForestCapacity (G : PhysicalGraph) : ℝ :=
  (G.maxLinearForestMultiplicity : ℝ) / (2 : ℝ) ^ G.cycleRank

theorem maxLinearForestMultiplicity_le_cycleSpaceCard (G : PhysicalGraph) :
    G.maxLinearForestMultiplicity ≤ 2 ^ G.cycleRank := by
  classical
  unfold maxLinearForestMultiplicity
  apply Finset.sup_le
  intro t _
  let f : G.LinearForestWord t → G.TJoin t := fun x => ⟨x.1, x.2.1⟩
  have hf : Function.Injective f := by
    intro x y h
    apply Subtype.ext
    exact congrArg (fun z : G.TJoin t => (z.1 : G.Word)) h
  have hwords : Fintype.card (G.LinearForestWord t) ≤ Fintype.card (G.TJoin t) :=
    Fintype.card_le_of_injective f hf
  have hlen : G.linearForestMultiplicity t ≤ Fintype.card (G.LinearForestWord t) := by
    unfold linearForestMultiplicity linearForestLengths
    exact Finset.card_image_le
  by_cases hne : Nonempty (G.LinearForestWord t)
  · obtain ⟨x⟩ := hne
    have ht := G.tjoin_natCard (t := t) ⟨x.1, x.2.1⟩
    have hcard : Fintype.card (G.TJoin t) = 2 ^ G.cycleRank := by
      simpa [Nat.card_eq_fintype_card] using ht
    exact hlen.trans (hwords.trans (by rw [hcard]))
  · have hzero : G.linearForestMultiplicity t = 0 := by
      haveI : IsEmpty (G.LinearForestWord t) := not_nonempty_iff.mp hne
      have hcard : Fintype.card (G.LinearForestWord t) = 0 := Fintype.card_eq_zero
      omega
    rw [hzero]
    exact Nat.zero_le _

theorem normalizedLinearForestCapacity_pos (G : PhysicalGraph) :
    0 < G.normalizedLinearForestCapacity := by
  unfold normalizedLinearForestCapacity
  have hnum : (0 : ℝ) < G.maxLinearForestMultiplicity := by
    exact_mod_cast (Nat.lt_of_lt_of_le Nat.zero_lt_one
      G.one_le_maxLinearForestMultiplicity)
  positivity

theorem normalizedLinearForestCapacity_le_one (G : PhysicalGraph) :
    G.normalizedLinearForestCapacity ≤ 1 := by
  unfold normalizedLinearForestCapacity
  have hnum : (G.maxLinearForestMultiplicity : ℝ) ≤
      (2 : ℝ) ^ G.cycleRank := by
    exact_mod_cast G.maxLinearForestMultiplicity_le_cycleSpaceCard
  have hden : 0 < (2 : ℝ) ^ G.cycleRank := by positivity
  exact (div_le_one hden).2 hnum

end Erdos1016.PhysicalGraph
