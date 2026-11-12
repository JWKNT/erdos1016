import Erdos1016.ExactMaximumSupport.LargeGirth.PackingCoverCount
import Erdos1016.ExactMaximumSupport.LargeGirth.PackingQuotientProbability
import Erdos1016.ExactMaximumSupport.LargeGirth.PackingStringLift

set_option autoImplicit false
set_option maxHeartbeats 1500000

/-!
# The fixed-probability packing theorem

The bound concerns actual disjoint cyclic regions of the original cubic
multigraph. The proof constructs the quotient, parity selection, strings,
and lifted pieces. No geometric or probabilistic model certificate is assumed.
-/
noncomputable section
namespace Erdos1016.ExactMaximumSupport.LargeGirth.Packing
open FiniteMultiGraph
local instance packingDecidable (p : Prop) : Decidable p := Classical.propDecidable p

/-- The packing cutoff is uniform in the ambient graph and all region families. -/
theorem exists_cutoff :
    ∃ D : ℕ,256≤D ∧
    ∀ (G : FiniteMultiGraph) {ι : Type*} [Fintype ι] (X : ι→Finset G.Vertex)
      (P S : Finset G.Vertex) (g d : ℕ),
      G.toSimpleGraph.Connected → (∀v,G.degree v=3) → D≤g → 2≤d → d≤2*g →
      (P=∅ ∨ (G.toSimpleGraph.induce (↑P : Set G.Vertex)).Connected) →
      ¬(PieceCore.Induced.graph G (P∪S)ᶜ).HasCycleShorterThan g →
      (2/5:ℝ)≤G.regionForestProbability (P∪S)ᶜ →
      Pairwise (fun i j => Disjoint (X i) (X j)) →
      (∀i,(G.toSimpleGraph.induce (↑(X i) : Set G.Vertex)).Connected) →
      (∀i,X i⊆(P∪S)ᶜ) → (∀i,∃z:G.internalCycleSpace (X i),z≠0) →
      (∀i,(G.cutEdges (X i)).card≤d) →
      Fintype.card ι≤1551*d*(S.card+1)*2^d := by
  obtain ⟨D,hD,hlen⟩ := PackingStringLift.exists_length_cutoff
  refine ⟨D,hD,?_⟩
  intro G ι _ X P S g d hG hcubic hg hd hdg hP hshort hprob hdisj hconn hXP hcyc hcut
  let Q := PackingQuotient.graph G X
  let marks := PackingQuotient.marks G X
  have hdegree : ∀v∈marks,Q.degree v≤d := by
    intro v hv
    obtain ⟨i,_,rfl⟩ := Finset.mem_image.mp hv
    rw [PackingQuotient.mark_degree G X hdisj]
    exact hcut i
  have hmarkprob := hprob.trans (PackingQuotient.region_forest_le_mark_product
    G X hdisj hconn hcyc (P∪S)ᶜ hXP)
  obtain ⟨A,hA,hind,hnonzero,hcard,hboundary,hrel,hzero⟩ :=
    PackingMarkedFamily.exists_selected Q marks (PackingQuotient.graph_noLoops G X)
      d (by omega) hdegree hmarkprob
  obtain ⟨E,hEsub,hE,n,hn,s,hcover⟩ := PackingStrings.exists_strings Q A marks hrel
  have hlength (c : Fin n) : (s c).length≤258*(S.card+3) := by
    apply (hlen G X P S g d hG hcubic hg hdg hP hshort hprob hdisj hconn hXP hcyc hcut
      (marks\A) ?_ (s c)).le
    intro v hv
    obtain ⟨i,_,he⟩ := Finset.mem_image.mp (Finset.mem_sdiff.mp hv).1
    exact ⟨i,he⟩
  have hcount := PackingCoverCount.card_le_of_short_strings Q marks A E n d S.card s
    hd hcard hboundary hzero hE hn hcover hlength
  calc
    Fintype.card ι = (PackingQuotient.marks G X).card := (PackingQuotient.marks_card G X).symm
    _ ≤ _ := hcount

/-- The finite-set form applies directly to the recursively selected packings. -/
theorem exists_finset_cutoff :
    ∃ D : ℕ,256≤D ∧
    ∀ (G : FiniteMultiGraph) (P S : Finset G.Vertex) (g d : ℕ)
      (F : Finset (Finset G.Vertex)),
      G.toSimpleGraph.Connected → (∀v,G.degree v=3) → D≤g → 2≤d → d≤2*g →
      (P=∅ ∨ (G.toSimpleGraph.induce (↑P : Set G.Vertex)).Connected) →
      ¬(PieceCore.Induced.graph G (P∪S)ᶜ).HasCycleShorterThan g →
      (2/5:ℝ)≤G.regionForestProbability (P∪S)ᶜ →
      (∀U∈F,∀V∈F,U≠V→Disjoint U V) →
      (∀U∈F,(G.toSimpleGraph.induce (↑U : Set G.Vertex)).Connected) →
      (∀U∈F,U⊆(P∪S)ᶜ) → (∀U∈F,∃z:G.internalCycleSpace U,z≠0) →
      (∀U∈F,(G.cutEdges U).card≤d) → F.card≤1551*d*(S.card+1)*2^d := by
  obtain ⟨D,hD,hbound⟩ := exists_cutoff
  refine ⟨D,hD,?_⟩
  intro G P S g d F hG hcubic hg hd hdg hP hshort hprob hdisj hconn hXP hcyc hcut
  have hh := hbound G (fun U : F => U.1) P S g d hG hcubic hg hd hdg hP hshort hprob
    (fun U V hne => hdisj U.1 U.2 V.1 V.2 (fun he => hne (Subtype.ext he)))
    (fun U => hconn U.1 U.2) (fun U => hXP U.1 U.2)
    (fun U => hcyc U.1 U.2) (fun U => hcut U.1 U.2)
  simpa only [Fintype.card_coe] using hh

end Erdos1016.ExactMaximumSupport.LargeGirth.Packing
