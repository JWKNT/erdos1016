import Erdos1016.Graph.ConnectedHubExtension
import Erdos1016.Extremal.Capacity.ActualRankTail

set_option autoImplicit false

/-!
# Connected realizers of actual-rank coverage

Joining the components to a fresh hub adds only bridges. The existing cycle
rank is unchanged, and each original cycle retains its length. Consequently,
a bound proved for connected graphs controls the actual-rank tail over all
finite simple graphs.
-/

noncomputable section
namespace Erdos1016.ShortProof
open PhysicalGraph

/-- The hub construction retains the original cycle length exactly. -/
theorem liftHubCycleWord_length (G : PhysicalGraph) (C : G.CycleWord) :
    (connectByHub G).wordLength (liftHubCycleWord G C).1 = G.wordLength C.1 := by
  classical
  have hs : (connectByHub G).edgeSupport (liftHubCycleWord G C).1 =
      (G.edgeSupport C.1).image (hubOldEdgeEmbedding G) := by
    ext e
    constructor
    · intro he
      have hne : (liftHubCycleWord G C).1 e ≠ 0 := (Finset.mem_filter.mp he).2
      cases hdec : (Fintype.equivFin (G.Edge ⊕ HubComponent G)).symm e with
      | inl f =>
        have hedge : e = hubOldEdgeEmbedding G f := by
          dsimp [hubOldEdgeEmbedding]
          rw [← hdec]
          exact ((Fintype.equivFin (G.Edge ⊕ HubComponent G)).apply_symm_apply e).symm
        subst e
        exact Finset.mem_image.mpr ⟨f,
          Finset.mem_filter.mpr ⟨Finset.mem_univ _, by simpa using hne⟩, rfl⟩
      | inr c =>
        have hedge : e = hubSpokeEmbedding G c := by
          dsimp [hubSpokeEmbedding]
          rw [← hdec]
          exact ((Fintype.equivFin (G.Edge ⊕ HubComponent G)).apply_symm_apply e).symm
        subst e
        exact False.elim (hne (liftHubCycleWord_spoke G C c))
    · rintro he
      obtain ⟨f, hf, rfl⟩ := Finset.mem_image.mp he
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, by
        simpa using (Finset.mem_filter.mp hf).2⟩
  have hinj : Function.Injective (hubOldEdgeEmbedding G) := by
    intro e f h
    apply Sum.inl.inj
    exact (Fintype.equivFin (G.Edge ⊕ HubComponent G)).injective h
  unfold wordLength
  rw [hs, Finset.card_image_of_injective _ hinj]

/-- Every covered length remains covered after connecting the components. -/
theorem initialCoverage_connectByHub (G : PhysicalGraph) {L : ℕ}
    (hL : G.InitialCoverage L) : (connectByHub G).InitialCoverage L := by
  classical
  intro l hl
  obtain ⟨C, _, hC⟩ := Finset.mem_image.mp (hL hl)
  exact Finset.mem_image.mpr ⟨liftHubCycleWord G C, Finset.mem_univ _,
    (liftHubCycleWord_length G C).trans hC⟩

/-- Bridge insertion preserves the normalized initial-coverage density. -/
theorem coverageDensity_connectByHub (G : PhysicalGraph) (L : ℕ) :
    coverageDensity (connectByHub G) L = coverageDensity G L := by
  simp only [coverageDensity, cycleRank_connectByHub]

/-- It suffices to bound actual coverage densities in connected realizers. -/
theorem actualRankTail_le_of_connected {R : ℕ} {B : ℝ} (hB : 0 ≤ B)
    (hgraphs : ∀ (G : PhysicalGraph) (L : ℕ), G.IsConnected →
      R ≤ G.cycleRank → G.InitialCoverage L → coverageDensity G L ≤ B) :
    actualRankTail R ≤ B := by
  apply actualRankTail_le hB
  intro G L hR hL
  have h := hgraphs (connectByHub G) L (connectByHub_connected G)
    (by simpa only [cycleRank_connectByHub] using hR)
    (initialCoverage_connectByHub G hL)
  simpa only [coverageDensity_connectByHub] using h

end Erdos1016.ShortProof
