import Erdos1016.ExactMaximumSupport.Shortening.BoundedPortShortCycle
import Erdos1016.ExactMaximumSupport.Shortening.PotentialGirth

set_option autoImplicit false
set_option maxHeartbeats 2000000

/-! The short-cycle case with one-mark suppression and the additive bridge potential.
The original physical exit/count lemmas are reused with the new rank threshold. -/
noncomputable section
namespace Erdos1016.ExactMaximumSupport.Shortening.PotentialShortCycle
open BoundaryTrace BoundaryTrace.Network BoundaryDecay ExactMaximum
local instance (priority := 100) propDecidable (p : Prop) : Decidable p := Classical.propDecidable p

theorem shortCycleStatement : ShortCycleStatement := by
  intro D₀
  obtain ⟨B₁, hB₁⟩ := PotentialGirth.exists_bound (D₀ + 2) (12 * D₀)
  obtain ⟨B₂, hB₂⟩ := numCycles_le_of_large_rank_margin (D₀ + 2)
  refine ⟨D₀ + (D₀ + 2) + B₁ + B₂ + 12, ?_⟩
  rintro M hconn hcubic hloop hR hno4 ⟨x, hx, hlen⟩
  have hl : M.IsLoopless := M.isLoopless_iff_not_hasLoop.2 hloop
  have hN : M.looplessNetwork.graph.Connected := M.connected_iff_looplessNetwork.1 hconn
  have hcub : M.looplessNetwork.IsCubic := by
    intro v
    rw [← M.degree_eq_deg hl v]
    exact hcubic v
  have hrank : D₀ + (D₀ + 2) + B₁ + B₂ + 12 ≤ networkRank M.looplessNetwork := by
    rw [← M.cycleRank_eq_networkRank hl]
    exact hR
  -- the cut edges of a vertex set are the crossing edges
  have hcutcard : ∀ W : Finset M.Vertex,
      (M.cutEdges W).card = M.looplessNetwork.cutSize (fun v => v ∈ W) := by
    intro W
    have h2 : Nat.card {e : M.Edge // e ∈ M.cutEdges W} = (M.cutEdges W).card := by
      rw [Nat.card_eq_fintype_card, Fintype.card_coe]
    have h3 : M.looplessNetwork.cutSize (fun v => v ∈ W) =
        Nat.card {e : M.NonloopEdge // M.looplessNetwork.crosses (fun v => v ∈ W) e} := rfl
    obtain ⟨f, hf⟩ : ∃ f : {e : M.NonloopEdge // M.looplessNetwork.crosses (fun v => v ∈ W) e} →
        {e : M.Edge // e ∈ M.cutEdges W}, ∀ a, (f a).1 = a.1.1 :=
      ⟨fun e => ⟨e.1.1, (M.mem_cutEdges_iff_crosses W e.1).2 e.2⟩, fun _ => rfl⟩
    have hbij : Function.Bijective f := by
      constructor
      · intro a b hab
        have h1 : a.1.1 = b.1.1 := by rw [← hf a, ← hf b, hab]
        exact Subtype.ext (Subtype.ext h1)
      · intro b
        refine ⟨⟨⟨b.1, hl b.1⟩, (M.mem_cutEdges_iff_crosses W ⟨b.1, hl b.1⟩).1 b.2⟩, ?_⟩
        apply Subtype.ext
        rw [hf]
    have h1 := Nat.card_eq_of_bijective f hbij
    omega
  -- every cyclic cut of the network has at least five crossing edges
  have hcut : ∀ S : M.Vertex → Prop, M.looplessNetwork.IsCyclicCut S →
      5 ≤ M.looplessNetwork.cutSize S := by
    intro S hS
    obtain ⟨W, hW⟩ : ∃ W : Finset M.Vertex, (fun v => v ∈ W) = S :=
      ⟨Finset.univ.filter S, funext fun v => propext (by
        rw [Finset.mem_filter]
        exact ⟨fun h => h.2, fun h => ⟨Finset.mem_univ v, h⟩⟩)⟩
    subst hW
    refine Nat.le_of_not_lt fun hlt => ?_
    apply hno4
    refine ⟨W, ⟨?_, ?_⟩, ?_⟩
    · have h := hS.1
      rw [numCycles_sub] at h
      obtain ⟨⟨z, hz, hw⟩⟩ := Finite.card_pos_iff.1 h
      exact (M.hasCycleIn_iff_looplessNetwork hl W).2 ⟨z, hz, hw⟩
    · have h := hS.2
      rw [numCycles_sub] at h
      obtain ⟨⟨z, hz, hw⟩⟩ := Finite.card_pos_iff.1 h
      exact (M.hasCycleIn_iff_looplessNetwork hl Wᶜ).2 ⟨z, hz, fun g hg =>
        ⟨Finset.mem_compl.2 (hw g hg).1, Finset.mem_compl.2 (hw g hg).2⟩⟩
    · rw [hcutcard W]
      omega
  -- the short cycle of the multigraph is a short cycle of the network
  have hy : M.looplessNetwork.IsCycleWord (M.nonloopWord x) :=
    (M.isCycleWord_iff_looplessNetwork x (hl.word x)).1 hx
  have hysize : size (M.nonloopWord x) ≤ M.wordLength x := by
    unfold size FiniteMultiGraph.wordLength
    apply Finset.card_le_card_of_injOn (fun g : M.NonloopEdge => g.1)
    · intro g hg
      exact Finset.mem_filter.2 ⟨Finset.mem_univ g.1, (Finset.mem_filter.1 hg).2⟩
    · intro g _ g' _ hgg
      exact Subtype.ext hgg
  -- a shortest cycle of the network
  have hex : ∃ n, ∃ z : M.looplessNetwork.Word, M.looplessNetwork.IsCycleWord z ∧ size z = n :=
    ⟨_, M.nonloopWord x, hy, rfl⟩
  obtain ⟨C, hC, hCsize⟩ := Nat.find_spec hex
  have hmin : ∀ z : M.looplessNetwork.Word, M.looplessNetwork.IsCycleWord z →
      size C ≤ size z := by
    intro z hz
    rw [hCsize]
    exact Nat.find_min' hex ⟨z, hz, rfl⟩
  have hCD : size C < D₀ := lt_of_le_of_lt (hmin _ hy) (lt_of_le_of_lt hysize hlen)
  have h5 : 5 ≤ size C :=
    ExactMaximumSupport.NetworkShortCycleCut.four_lt_size_of_cyclic_cut_lower_bound
      M.looplessNetwork (fun v => le_of_eq (hcub v)) (by omega) hcut C hC
  have h := numCycles_lt_of_short_cycle_of_girth hB₁ hB₂ M.looplessNetwork hN hcub C hC hmin h5
    (by omega) (by omega) (by omega)
  rw [M.numCycles_eq_looplessNetwork hl, M.cycleRank_eq_networkRank hl]
  exact h


end Erdos1016.ExactMaximumSupport.Shortening.PotentialShortCycle
