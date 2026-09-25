import Erdos1016.Cleanup.Packing.PairedPathRegions
import Erdos1016.Probability.Regions.TripleCutPackingBound

set_option autoImplicit false

/-!
# Paired-path counting with local degree and arbitrary witness edges

Only degrees within the selected regions affect their two-edge boundaries.
The witness is an edge set; it need not be presented as a family of cycles.
These are the forms needed by the actual support-local cleanup construction.
-/

noncomputable section

namespace Erdos1016.Proof.LocalPairedPathBound

open Erdos1016
open PairedPathRegions
open PhysicalActualCutTriplePackingAdapter

open PhysicalManyRegionConditionalProduct
open PhysicalManyRegionProbabilityBridge

local instance (G : PhysicalGraph) (v : G.Vertex) :
    Fintype (G.toSimpleGraph.neighborSet v) :=
  PhysicalSimpleGraphDegreeBridge.neighborFintype G v

/-- Count disjoint paired paths using only degrees in their vertex regions.
Protected vertices elsewhere may have arbitrarily large witness degree. -/
theorem card_le_160_mul_sq
    (G : PhysicalGraph) {ι : Type*} [Fintype ι] [DecidableEq ι]
    (U : ι → Finset G.Vertex)
    (hcert : ∀ i, PairedPathCertificate G (U i))
    (hdisj : ∀ i j, i ≠ j → Disjoint (U i) (U j))
    (hmax : ∀ i v, v ∈ U i → G.degree v ≤ 3)
    (hdegree : ∀ i v, v ∈ U i → v ≠ (hcert i).source.1 →
      v ≠ (hcert i).target.1 → G.degree v = 2)
    (W : Finset G.Edge)
    (havoids : ∀ i e, e ∈ SafeCore.internalEdges G (U i) → e ∉ W)
    (hGconn : G.IsConnected)
    (R : ℕ) (hR : 5 ≤ R)
    (hprob : (1 / 2 : ℝ) + 1 / (R : ℝ) <
      G.outsideLinearForestProbability W) :
    Fintype.card ι ≤ 160 * R ^ 2 := by
  classical
  let regions : Finset (Finset G.Vertex) := Finset.univ.image U
  have hinj : Function.Injective U := by
    intro i j hij
    by_contra hne
    exact (Finset.disjoint_left.mp (hdisj i j hne))
      (hcert i).source.2 (by simpa [hij] using (hcert i).source.2)
  have hcard : regions.card = Fintype.card ι := by
    simp [regions, Finset.card_image_of_injective, hinj]
  have hprops : ∀ S ∈ regions, G.IsCyclicRegion S ∧ G.actualCut S ≤ 2 := by
    intro S hS
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hS
    exact ⟨(hcert i).isCyclicRegion,
      (hcert i).actualCut_le_two_of_paths (hmax i) (hdegree i)⟩
  have hpairwise : (regions : Set (Finset G.Vertex)).Pairwise Disjoint := by
    intro S hS T hT hne
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hS
    obtain ⟨j, _, rfl⟩ := Finset.mem_image.mp hT
    exact hdisj i j (fun hij => hne (congrArg U hij))
  have hbound := card_lt_manyRegionThreshold_of_connectedRegions
    G W R 2 hR regions hGconn
    (by
      intro S hS
      obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hS
      intro e he
      exact Finset.mem_compl.mpr (havoids i e he))
    hprops hpairwise hprob
  rw [hcard] at hbound
  have hpow : 4 * R ≤ 2 ^ R := by
    suffices h : ∀ n : ℕ, 5 ≤ n → 4 * n ≤ 2 ^ n from h R hR
    intro n hn
    induction n, hn using Nat.le_induction with
    | base => norm_num
    | succ R hR ih =>
        rw [pow_succ]
        have : 4 ≤ 2 ^ R := by omega
        nlinarith
  have hlog : dyadicRegionCutoffExponent R ≤ R := by
    apply (Nat.le_pow_iff_clog_le Nat.one_lt_two).mp
    simpa [dyadicRegionCutoffExponent] using hpow
  have hsmall : 16 + dyadicRegionCutoffExponent R ≤ 5 * R := by omega
  norm_num at hbound
  nlinarith

end Erdos1016.Proof.LocalPairedPathBound

end
