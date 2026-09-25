import Erdos1016.Probability.Conditional.CycleNeighborhood
import Erdos1016.Cycles.Geometry.OrdinaryProximity

set_option autoImplicit false

noncomputable section

namespace Erdos1016.Proof.OrdinaryCycleNeighborhood

open scoped BigOperators
open BoundaryDecay Nonbacktracking.FiniteTwoCore
open GraphBalls

local instance (p : Prop) : Decidable p := Classical.propDecidable p

theorem closeWithin_iff_ball (G : PhysicalGraph) (J : Finset G.Vertex) (q : ℕ)
    (C D : G.CycleWord) :
    CycleProximity.Near G J q C D ↔
      ∃ v ∈ graphBall (G.toSimpleGraph.induce (↑J : Set G.Vertex))
        ((Cycle.vertices C).subtype (fun z => z ∈ J)) q,
        v ∈ (Cycle.vertices D).subtype (fun z => z ∈ J) := by
  constructor
  · rintro ⟨u, v, hu, hv, p, hp⟩
    refine ⟨v, (graphBall_iff _ _ q v).mpr ⟨u, Finset.mem_subtype.mpr hu, ⟨p⟩, ?_⟩,
      Finset.mem_subtype.mpr hv⟩
    exact (SimpleGraph.dist_le p).trans hp
  · rintro ⟨v, hv, hvD⟩
    obtain ⟨u, hu, hr, hd⟩ := (graphBall_iff _ _ q v).mp hv
    obtain ⟨p, hp⟩ := hr.exists_walk_length_eq_dist
    exact ⟨u, v, Finset.mem_subtype.mp hu, Finset.mem_subtype.mp hvD, p, hp.trans_le hd⟩

/-- Transfer the conditional vertex count to the original ordinary graph,
where the radius ball may contain vertices that were removed from the core. -/
theorem neighbor_mass_le (G : PhysicalGraph) (J : Finset G.Vertex)
    (F : Finset G.CycleWord) (mass : G.CycleWord → ℝ)
    (q L : ℕ) (A : ℝ) (hA : 0 ≤ A)
    (hdegree : ∀ v ∈ J, G.degree v ≤ 3)
    (hload : ∀ v, vertexLoad F Cycle.vertices mass v ≤ A)
    (hmass : ∀ C ∈ F, 0 ≤ mass C)
    (C : G.CycleWord) (hC : BoundaryDecay.Cycle.length C ≤ L) :
    (∑ D ∈ F, if CycleProximity.Near G J q C D then mass D else 0) ≤
      (3 : ℝ) * L * 2 ^ q * A := by
  classical
  let P := G.toSimpleGraph.induce (↑J : Set G.Vertex)
  let support := fun D : G.CycleWord => (Cycle.vertices D).subtype (fun v => v ∈ J)
  have hdeg : ∀ v, P.degree v ≤ 3 := by
    intro v
    have hd : P.degree v ≤ G.degree v.1 := by
      rw [original_degree_eq_graph_degree]
      rw [← SimpleGraph.card_neighborSet_eq_degree, ← SimpleGraph.card_neighborSet_eq_degree]
      exact Fintype.card_le_of_injective (fun w => ⟨w.1.1, w.2⟩)
        (fun a b hab => Subtype.ext (Subtype.ext (congrArg (fun z => z.1) hab)))
    exact hd.trans (hdegree v.1 v.2)
  have hloadJ : ∀ v, vertexLoad F support mass v ≤ A := by
    intro v
    have heq : vertexLoad F support mass v = vertexLoad F Cycle.vertices mass v.1 := by
      unfold vertexLoad
      apply Finset.sum_congr rfl
      intro D _
      by_cases hv : v.1 ∈ Cycle.vertices D
      · simp only [if_pos hv, if_pos (show v ∈ support D from Finset.mem_subtype.mpr hv)]
      · simp only [if_neg hv, if_neg (show v ∉ support D from fun h => hv (Finset.mem_subtype.mp h))]
    exact heq.trans_le (hload v.1)
  have hanchor : (support C).card ≤ L := by
    calc
      (support C).card = ((Cycle.vertices C).filter (fun v => v ∈ J)).card := Finset.card_subtype _ _
      _ ≤ (Cycle.vertices C).card := Finset.card_filter_le _ _
      _ = BoundaryDecay.Cycle.length C := (Cycle.length_eq_vertices_card C).symm
      _ ≤ L := hC
  have h := CycleNeighborhoodLoad.anchor_neighbor_mass_le P F support mass (support C)
    q L A hA hdeg hloadJ hmass hanchor
  convert h using 1
  apply Finset.sum_congr rfl
  intro D _
  exact if_congr (closeWithin_iff_ball G J q C D) rfl rfl

theorem neighbor_mass_le_conditional_bound (G : PhysicalGraph) (J : Finset G.Vertex)
    (F : Finset G.CycleWord) (mass : G.CycleWord → ℝ)
    (q L s b : ℕ)
    (hdegree : ∀ v ∈ J, G.degree v ≤ 3)
    (hload : ∀ v, vertexLoad F Cycle.vertices mass v ≤ 6 * L * ((2 : ℝ) ^ b / 2 ^ s))
    (hmass : ∀ C ∈ F, 0 ≤ mass C)
    (C : G.CycleWord) (hC : BoundaryDecay.Cycle.length C ≤ L) :
    (∑ D ∈ F, if CycleProximity.Near G J q C D then mass D else 0) ≤
      18 * (2 : ℝ) ^ q * L ^ 2 * ((2 : ℝ) ^ b / 2 ^ s) := by
  have h := neighbor_mass_le G J F mass q L (6 * L * ((2 : ℝ) ^ b / 2 ^ s))
    (by positivity) hdegree hload hmass C hC
  convert h using 1
  ring

end Erdos1016.Proof.OrdinaryCycleNeighborhood
