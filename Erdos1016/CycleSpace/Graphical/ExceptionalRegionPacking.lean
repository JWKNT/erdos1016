import Erdos1016.CycleSpace.Graphical.DisjointRegionCuts
import Erdos1016.Graph.Multigraph.RegionDegrees

set_option autoImplicit false

/-!
# Packing exceptional regions around one fixed cycle

Only the candidate subfamily is required disjoint. Other candidate regions
may overlap. The anchor region is explicitly added to the contraction
partition, so the bound is the anchor's physical cut size.
-/

noncomputable section
namespace Erdos1016.FiniteMultiGraph

local instance exceptionalRegionPackingDecidable (p : Prop) : Decidable p :=
  Classical.propDecidable p

open DisjointRegionCuts

/-- The anchor version of Lemma 1, suited to packing bounds in a family
whose other members need not be pairwise disjoint. -/
theorem exceptional_region_packing_card_le {ι : Type*} (G : FiniteMultiGraph)
    (U₀ : Finset G.Vertex) (U : ι → Finset G.Vertex) (s : Finset ι)
    (hG : G.toSimpleGraph.Connected)
    (hconn₀ : (G.toSimpleGraph.induce (↑U₀ : Set G.Vertex)).Connected)
    (hconn : ∀ i ∈ s, (G.toSimpleGraph.induce (↑(U i) : Set G.Vertex)).Connected)
    (hanchor : ∀ i ∈ s, Disjoint U₀ (U i))
    (hdisj : ∀ i ∈ s, ∀ j ∈ s, i ≠ j → Disjoint (U i) (U j))
    (hexceptional : ∀ i ∈ s,
      2 * Finite.density (ZeroCut G U₀) * Finite.density (ZeroCut G (U i)) <
        Finite.density (fun x => ZeroCut G U₀ x ∧ ZeroCut G (U i) x)) :
    s.card ≤ (G.cutEdges U₀).card := by
  classical
  let R : Option s → Finset G.Vertex := fun q => q.elim U₀ (fun i => U i.1)
  have hR : Pairwise (fun i j => Disjoint (R i) (R j)) := by
    intro i j hij
    cases i with
    | none =>
        cases j with
        | none => exact (hij rfl).elim
        | some j => exact hanchor j.1 j.2
    | some i =>
        cases j with
        | none => exact (hanchor i.1 i.2).symm
        | some j =>
            apply hdisj i.1 i.2 j.1 j.2
            exact fun heq => hij (congrArg Option.some (Subtype.ext heq))
  have hconnected : ∀ q, (G.toSimpleGraph.induce (↑(R q) : Set G.Vertex)).Connected := by
    intro q
    cases q with
    | none => exact hconn₀
    | some i => exact hconn i.1 i.2
  let emb : s ↪ Option s := ⟨Option.some, Option.some_injective _⟩
  let T : Finset (Option s) := Finset.univ.map emb
  have hall : ∀ q ∈ T, q ≠ none ∧ Exceptional G R none q := by
    intro q hq
    obtain ⟨i, hi, rfl⟩ := Finset.mem_map.mp hq
    exact ⟨Option.some_ne_none _, hexceptional i.1 i.2⟩
  have h := exceptional_partner_card_le G R hG hR hconnected none T
  rw [Finset.filter_congr_decidable] at h
  have h' : T.card ≤ (G.cutEdges (R none)).card :=
    (Finset.card_le_card (fun q hq => Finset.mem_filter.mpr ⟨hq, hall q hq⟩)).trans h
  simpa only [T, Finset.card_map, Finset.card_univ, Fintype.card_coe] using h'

/-- For a two-regular anchor in a subcubic multigraph, the packing number of
its genuinely exceptional disjoint partners is at most its vertex count. -/
theorem exceptional_cycle_packing_card_le {ι : Type*} (G : FiniteMultiGraph)
    (U₀ : Finset G.Vertex) (seed : G.EdgeWord)
    (htwo : ∀ v ∈ U₀, G.selectedDegree seed v = 2)
    (hsupport : ∀ e, e ∉ G.internalEdges U₀ → seed e = 0)
    (hdegree : ∀ v ∈ U₀, G.degree v ≤ 3)
    (U : ι → Finset G.Vertex) (s : Finset ι)
    (hG : G.toSimpleGraph.Connected)
    (hconn₀ : (G.toSimpleGraph.induce (↑U₀ : Set G.Vertex)).Connected)
    (hconn : ∀ i ∈ s, (G.toSimpleGraph.induce (↑(U i) : Set G.Vertex)).Connected)
    (hanchor : ∀ i ∈ s, Disjoint U₀ (U i))
    (hdisj : ∀ i ∈ s, ∀ j ∈ s, i ≠ j → Disjoint (U i) (U j))
    (hexceptional : ∀ i ∈ s,
      2 * Finite.density (ZeroCut G U₀) * Finite.density (ZeroCut G (U i)) <
        Finite.density (fun x => ZeroCut G U₀ x ∧ ZeroCut G (U i) x)) :
    s.card ≤ U₀.card :=
  (G.exceptional_region_packing_card_le U₀ U s hG hconn₀ hconn hanchor hdisj hexceptional).trans
    (G.cutEdges_card_le_of_two_regular U₀ seed htwo hsupport hdegree)

end Erdos1016.FiniteMultiGraph
