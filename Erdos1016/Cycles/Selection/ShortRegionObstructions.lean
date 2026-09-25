import Erdos1016.Cycles.Selection.ShortRegionPacking
import Erdos1016.Graph.Multigraph.ForestCharacterization
import Erdos1016.Graph.Multigraph.RegionDegrees

set_option autoImplicit false
noncomputable section
open scoped BigOperators
namespace Erdos1016.FiniteMultiGraph
local instance (p : Prop) : Decidable p := Classical.propDecidable p

/-- A labelled nonforest internal region contains a nonzero internal even word,
including when the obstruction is a loop or a parallel pair. -/
theorem internalCycleSpace_nontrivial_of_not_forest (G : FiniteMultiGraph)
    (U : Finset G.Vertex)
    (h : ¬ G.IsForestWord (G.restrictEdges (G.internalEdges U) (fun _ => 1))) :
    ∃ z : G.internalCycleSpace U, z ≠ 0 := by
  obtain ⟨z, hn, hs⟩ := G.exists_even_support_of_not_forest _ h
  have hz : z ∈ G.internalCycleSpace U := by
    intro e he
    by_contra hne
    have hh := hs e hne
    simp [restrictEdges, he] at hh
  refine ⟨⟨z, hz⟩, ?_⟩
  intro hzero
  exact hn (congrArg (fun w : G.internalCycleSpace U => w.1.1) hzero)

/-- A connected cyclic region with at least one internal labelled edge per
vertex has small cut in a subcubic graph. -/
theorem shortCyclicRegion_of_internal_card (G : FiniteMultiGraph)
    (P U : Finset G.Vertex) (D : ℕ) (hout : U ⊆ Pᶜ) (hsize : U.card ≤ D)
    (hconn : (G.toSimpleGraph.induce (↑U : Set G.Vertex)).Connected)
    (hcyc : ¬ G.IsForestWord (G.restrictEdges (G.internalEdges U) (fun _ => 1)))
    (hedges : U.card ≤ (G.internalEdges U).card)
    (hmax : ∀ v ∈ U, G.degree v ≤ 3) : G.ShortCyclicRegion P D U := by
  refine ⟨hout, hsize, hconn, G.internalCycleSpace_nontrivial_of_not_forest U hcyc, ?_⟩
  have hsum := G.sum_region_degree U
  have hb : (∑ v ∈ U, G.degree v) ≤ 3 * U.card := by
    calc
      _ ≤ ∑ _v ∈ U, 3 := Finset.sum_le_sum hmax
      _ = _ := by simp [Nat.mul_comm]
  omega

/-- Every retained loop is a short cyclic region of one vertex. -/
theorem loop_shortCyclicRegion (G : FiniteMultiGraph) (P : Finset G.Vertex)
    (D : ℕ) (hD : 1 ≤ D) (e : G.Edge) (he : G.src e = G.dst e)
    (hout : G.src e ∉ P) (hmax : G.degree (G.src e) ≤ 3) :
    G.ShortCyclicRegion P D {G.src e} := by
  have hei : e ∈ G.internalEdges {G.src e} := by simp [internalEdges, ← he]
  apply G.shortCyclicRegion_of_internal_card P {G.src e} D
  · simpa using hout
  · simpa using hD
  · rw [SimpleGraph.connected_iff_exists_forall_reachable]
    refine ⟨⟨G.src e, by simp⟩, ?_⟩
    intro v
    have hv : v = ⟨G.src e, by simp⟩ := Subtype.ext (Finset.mem_singleton.mp v.2)
    subst v
    rfl
  · intro hf
    exact hf.1 e (by simp [restrictEdges, hei]) he
  · simpa using Finset.card_pos.mpr ⟨e, hei⟩
  · intro v hv
    simpa only [Finset.mem_singleton.mp hv] using hmax

/-- Every pair of distinct parallel nonloop labels is a short cyclic region
of two vertices. Parallel labels are never silently identified. -/
theorem parallel_shortCyclicRegion (G : FiniteMultiGraph) (P : Finset G.Vertex)
    (D : ℕ) (hD : 2 ≤ D) (e f : G.Edge) (hef : e ≠ f)
    (hloop : G.src e ≠ G.dst e)
    (hends : (G.src e = G.src f ∧ G.dst e = G.dst f) ∨
      (G.src e = G.dst f ∧ G.dst e = G.src f))
    (hout : G.src e ∉ P ∧ G.dst e ∉ P)
    (hmax : ∀ v ∈ ({G.src e, G.dst e} : Finset G.Vertex), G.degree v ≤ 3) :
    G.ShortCyclicRegion P D {G.src e, G.dst e} := by
  have hei : e ∈ G.internalEdges {G.src e, G.dst e} := by simp [internalEdges]
  have hfi : f ∈ G.internalEdges {G.src e, G.dst e} := by
    rcases hends with h | h <;> simp [internalEdges, ← h.1, ← h.2]
  have hcard : ({G.src e, G.dst e} : Finset G.Vertex).card = 2 := by simp [hloop]
  apply G.shortCyclicRegion_of_internal_card P {G.src e, G.dst e} D
  · intro v hv
    simp only [Finset.mem_insert, Finset.mem_singleton] at hv
    rcases hv with rfl | rfl <;> simp [hout]
  · omega
  · rw [SimpleGraph.connected_iff_exists_forall_reachable]
    refine ⟨⟨G.src e, by simp⟩, ?_⟩
    rintro ⟨v, hv⟩
    simp only [Finset.mem_coe, Finset.mem_insert, Finset.mem_singleton] at hv
    rcases hv with rfl | rfl
    · rfl
    · apply SimpleGraph.Adj.reachable
      exact ⟨hloop, e, Or.inl ⟨rfl, rfl⟩⟩
  · intro hf
    exact hef (hf.2.1 e f (by simp [restrictEdges, hei]) (by simp [restrictEdges, hfi]) hends)
  · have hsub : ({e, f} : Finset G.Edge) ⊆ G.internalEdges {G.src e, G.dst e} := by
      intro q hq
      simp only [Finset.mem_insert, Finset.mem_singleton] at hq
      rcases hq with rfl | rfl <;> assumption
    have h := Finset.card_le_card hsub
    simpa [hef, hcard] using h
  · exact hmax

/-- A hitting union for short cyclic regions removes all loops. -/
theorem retained_no_loops (G : FiniteMultiGraph) (P S : Finset G.Vertex)
    (D : ℕ) (hD : 1 ≤ D) (hmax : ∀ v, G.degree v ≤ 3)
    (hhit : ∀ U, G.ShortCyclicRegion P D U → (S ∩ U).Nonempty) :
    ∀ e ∈ G.internalEdges (P ∪ S)ᶜ, G.src e ≠ G.dst e := by
  intro e he hl
  have hsrc := (Finset.mem_filter.mp he).2.1
  have hn : G.src e ∉ P ∧ G.src e ∉ S := by simpa using hsrc
  obtain ⟨v, hv⟩ := hhit _ (G.loop_shortCyclicRegion P D hD e hl hn.1 (hmax _))
  have h := Finset.mem_inter.mp hv
  exact hn.2 (Finset.mem_singleton.mp h.2 ▸ h.1)

/-- The same hitting property removes every parallel pair from the retained
physical labels. -/
theorem retained_simple (G : FiniteMultiGraph) (P S : Finset G.Vertex)
    (D : ℕ) (hD : 2 ≤ D) (hmax : ∀ v, G.degree v ≤ 3)
    (hhit : ∀ U, G.ShortCyclicRegion P D U → (S ∩ U).Nonempty) :
    ∀ e ∈ G.internalEdges (P ∪ S)ᶜ, ∀ f ∈ G.internalEdges (P ∪ S)ᶜ,
      ((G.src e = G.src f ∧ G.dst e = G.dst f) ∨
        (G.src e = G.dst f ∧ G.dst e = G.src f)) → e = f := by
  intro e he f hf hends
  by_contra hne
  have hs := (Finset.mem_filter.mp he).2.1
  have ht := (Finset.mem_filter.mp he).2.2
  have hsn : G.src e ∉ P ∧ G.src e ∉ S := by simpa using hs
  have htn : G.dst e ∉ P ∧ G.dst e ∉ S := by simpa using ht
  have hl := G.retained_no_loops P S D (by omega) hmax hhit e he
  obtain ⟨v, hv⟩ := hhit _ (G.parallel_shortCyclicRegion P D hD e f hne hl hends
    ⟨hsn.1, htn.1⟩ (fun v _ => hmax v))
  have h := Finset.mem_inter.mp hv
  rcases Finset.mem_insert.mp h.2 with hv | hv
  · exact hsn.2 (hv ▸ h.1)
  · exact htn.2 (Finset.mem_singleton.mp hv ▸ h.1)

end Erdos1016.FiniteMultiGraph
