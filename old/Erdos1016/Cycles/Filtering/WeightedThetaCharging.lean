import Erdos1016.Cycles.Filtering.ThetaLengthAccounting
import Erdos1016.Cycles.Filtering.RejectedReturnWitness

set_option autoImplicit false
set_option maxHeartbeats 1000000

noncomputable section

namespace Erdos1016.Proof.WeightedThetaCharging

open scoped BigOperators
open Erdos1016.BoundaryDecay
open Erdos1016.Nonbacktracking
open Erdos1016.Proof.PhysicalThetaCandidates
open Erdos1016.Proof.ThetaMassFiberBridge
open Erdos1016.Proof.RejectedCycleEncoding

open Erdos1016.Proof.ExternalReturnTheta
open Erdos1016.Proof.PhysicalThetaPairRelabel
open Erdos1016.Proof.MinimumPairArcTransport
open Erdos1016.Proof.ThetaArcUniqueness
open Erdos1016.Proof.ThetaSupportArcUniqueness
open Erdos1016.Proof.RejectedCycleEncoding
open Erdos1016.Proof.RejectedReturnWitness
open Erdos1016.Proof.ExternalReturnFilter

variable (G : Erdos1016.PhysicalGraph)

local instance cycleWordDecidableEq : DecidableEq G.CycleWord := Classical.decEq _

private theorem pairArcCorr_of_base_and_external {u v : G.Vertex}
    (t t' : ThetaPaths G.toSimpleGraph u v) (tag : Fin 3)
    (hbase : ArcPairCorrespondence G t.left t.right t'.left t'.right)
    (hext : t.external.edges.toFinset = t'.external.edges.toFinset) :
    ∃ targetTag : Fin 3,
      ArcPairCorrespondence G
        (thetaPairPaths G t tag).1 (thetaPairPaths G t tag).2
        (thetaPairPaths G t' targetTag).1 (thetaPairPaths G t' targetTag).2 := by
  fin_cases tag
  · exact ⟨0, by simpa [thetaPairPaths] using hbase⟩
  · rcases hbase with ⟨hl, hr⟩ | ⟨hl, hr⟩
    · exact ⟨1, by simpa [thetaPairPaths] using
        (Or.inl ⟨hl, hext⟩ : ArcPairCorrespondence G t.left t.external t'.left t'.external)⟩
    · exact ⟨2, by simpa [thetaPairPaths] using
        (Or.inr ⟨hl, hext⟩ : ArcPairCorrespondence G t.left t.external t'.external t'.right)⟩
  · rcases hbase with ⟨hl, hr⟩ | ⟨hl, hr⟩
    · exact ⟨2, by simpa [thetaPairPaths] using
        (Or.inl ⟨hext, hr⟩ : ArcPairCorrespondence G t.external t.right t'.external t'.right)⟩
    · exact ⟨1, by simpa [thetaPairPaths] using
        (Or.inr ⟨hext, hr⟩ : ArcPairCorrespondence G t.external t.right t'.left t'.external)⟩

private theorem arcCorr_trans {u v : G.Vertex} {p q p' q' p'' q'' :
    G.toSimpleGraph.Walk u v}
    (h₁ : ArcPairCorrespondence G p q p' q')
    (h₂ : ArcPairCorrespondence G p' q' p'' q'') :
    ArcPairCorrespondence G p q p'' q'' := by
  rcases h₁ with ⟨hp, hq⟩ | ⟨hp, hq⟩ <;>
    rcases h₂ with ⟨hp', hq'⟩ | ⟨hp', hq'⟩
  · exact Or.inl ⟨hp.trans hp', hq.trans hq'⟩
  · exact Or.inr ⟨hp.trans hp', hq.trans hq'⟩
  · exact Or.inr ⟨hp.trans hq', hq.trans hp'⟩
  · exact Or.inl ⟨hp.trans hq', hq.trans hp'⟩

private theorem cycleWord_eq_of_walk_eq {u : G.Vertex}
    {p q : G.toSimpleGraph.Walk u u} (hp : p.IsCycle) (hq : q.IsCycle)
    (h : p = q) : cycleWordOfWalk G p hp = cycleWordOfWalk G q hq := by
  cases h
  rfl

def cycleWordMassWeight (C : G.CycleWord) : ℝ :=
  (1 / 2 : ℝ) ^ G.wordLength C.1

def realizableThetaMassWeight {bases : Finset G.CycleWord} {s L : ℕ}
    (w : RealizableCandidate G bases s L) : ℝ :=
  candidateKeyWeight G w.1

/-- The exact exponent condition for charging a recovered constituent to its
realizable theta candidate. In theta applications it follows by cancelling
the common branches: tag 0 leaves the external branch, tag 1 leaves the
candidate's right base arc, and tag 2 leaves its left base arc. -/
theorem recovered_cycle_weight_le_candidate_weight
    {bases : Finset G.CycleWord} {s L q : ℕ}
    (code : RealizableCandidate G bases s L × Fin 3)
    (hcharge : G.wordLength (candidateCycle G code.1.1).1 +
        candidateBranchLength G code.1.1 ≤
        q + G.wordLength (recoverThetaTagCycle G code).1) :
    cycleWordMassWeight G (recoverThetaTagCycle G code) ≤
      (2 : ℝ) ^ q * realizableThetaMassWeight G code.1 := by
  let a := G.wordLength (candidateCycle G code.1.1).1
  let b := candidateBranchLength G code.1.1
  let n := a + b
  let m := G.wordLength (recoverThetaTagCycle G code).1
  have hnm : n ≤ q + m := by dsimp [n, a, b, m]; exact hcharge
  have hpowNat : 2 ^ n ≤ 2 ^ (q + m) := Nat.pow_le_pow_right (by omega) hnm
  have hpow : (2 : ℝ) ^ n ≤ (2 : ℝ) ^ q * (2 : ℝ) ^ m := by
    have hpowNat' : 2 ^ n ≤ 2 ^ q * 2 ^ m := by
      simpa only [Nat.pow_add] using hpowNat
    exact_mod_cast hpowNat'
  have hratio : (1 / 2 : ℝ) ^ m ≤ (2 : ℝ) ^ q / (2 : ℝ) ^ n := by
    rw [one_div_pow, le_div_iff₀ (by positivity)]
    field_simp
    exact (div_le_iff₀ (by positivity)).2 hpow
  have hcandidate : realizableThetaMassWeight G code.1 =
      (1 / 2 : ℝ) ^ a * (1 / 2 : ℝ) ^ b := by
    rfl
  unfold cycleWordMassWeight
  rw [hcandidate]
  calc
    (1 / 2 : ℝ) ^ m ≤ (2 : ℝ) ^ q / (2 : ℝ) ^ n := hratio
    _ = (2 : ℝ) ^ q * ((1 / 2 : ℝ) ^ a * (1 / 2 : ℝ) ^ b) := by
      rw [← pow_add, one_div_pow]
      simp only [show n = a + b by rfl]
      ring

/-- Weighted finite charging through the recovery injection. The per-cycle
selected-code existence and the theta branch-length charge are explicit
hypotheses; once supplied, recovery injectivity gives the factor of three
from the constituent tag and no additional fiber loss. -/
theorem excluded_cycle_mass_le_three_pow_q_candidate_mass
    {bases : Finset G.CycleWord} {s L q : ℕ}
    (excluded : Finset G.CycleWord)
    (hcode : ∀ C ∈ excluded,
      ∃ code : RealizableCandidate G bases s L × Fin 3,
        recoverThetaTagCycle G code = C ∧
        G.wordLength (candidateCycle G code.1.1).1 +
          candidateBranchLength G code.1.1 ≤
          q + G.wordLength (recoverThetaTagCycle G code).1)
    : (∑ C ∈ excluded, cycleWordMassWeight G C) ≤
        3 * (2 : ℝ) ^ q *
          (∑ w : RealizableCandidate G bases s L, realizableThetaMassWeight G w) := by
  classical
  let Source := {C : G.CycleWord // C ∈ excluded}
  let encode : Source → RealizableCandidate G bases s L × Fin 3 := fun C =>
    Classical.choose (hcode C.1 C.2)
  have hspec (C : Source) := Classical.choose_spec (hcode C.1 C.2)
  have hrecover (C : Source) : recoverThetaTagCycle G (encode C) = C.1 :=
    (hspec C).1
  have hexp (C : Source) :
      G.wordLength (candidateCycle G (encode C).1.1).1 +
        candidateBranchLength G (encode C).1.1 ≤
        q + G.wordLength (recoverThetaTagCycle G (encode C)).1 :=
    (hspec C).2
  have hinj : Function.Injective encode := by
    intro C D h
    apply Subtype.ext
    calc
      C.1 = recoverThetaTagCycle G (encode C) := (hrecover C).symm
      _ = recoverThetaTagCycle G (encode D) := congrArg (recoverThetaTagCycle G) h
      _ = D.1 := hrecover D
  let sources : Finset Source := Finset.univ
  let codes := sources.image encode
  have hweight (C : Source) :
      cycleWordMassWeight G C.1 ≤
        (2 : ℝ) ^ q * realizableThetaMassWeight G (encode C).1 := by
    rw [← hrecover C]
    exact recovered_cycle_weight_le_candidate_weight G (encode C)
      (hexp C)
  have hsourceSum :
    (∑ C ∈ excluded, cycleWordMassWeight G C) =
        ∑ C ∈ sources, cycleWordMassWeight G C.1 := by
    unfold sources Source
    exact Finset.sum_subtype excluded (by intro C; rfl) (cycleWordMassWeight G)
  have hreindex :
      (∑ code ∈ codes, realizableThetaMassWeight G code.1) =
        ∑ C ∈ sources, realizableThetaMassWeight G (encode C).1 := by
    unfold codes sources
    exact Finset.sum_image (f := fun code : RealizableCandidate G bases s L × Fin 3 =>
      realizableThetaMassWeight G code.1) (g := encode) (by
        intro C hC D hD hCD
        exact hinj hCD)
  have hcharge :
      (∑ C ∈ sources, cycleWordMassWeight G C.1) ≤
        (2 : ℝ) ^ q * (∑ code ∈ codes, realizableThetaMassWeight G code.1) := by
    calc
      (∑ C ∈ sources, cycleWordMassWeight G C.1) ≤
          ∑ C ∈ sources, (2 : ℝ) ^ q * realizableThetaMassWeight G (encode C).1 :=
        Finset.sum_le_sum fun C hC => hweight C
      _ = (2 : ℝ) ^ q * (∑ C ∈ sources,
          realizableThetaMassWeight G (encode C).1) := by rw [Finset.mul_sum]
      _ = (2 : ℝ) ^ q * (∑ code ∈ codes,
          realizableThetaMassWeight G code.1) := by rw [hreindex]
  have hcodesub : codes ⊆ Finset.univ := Finset.subset_univ _
  have hnonneg : ∀ code : RealizableCandidate G bases s L × Fin 3,
      code ∈ Finset.univ → code ∉ codes →
      0 ≤ realizableThetaMassWeight G code.1 := by
    intro code _ _
    simp [realizableThetaMassWeight, candidateKeyWeight]
  have hall :
      (∑ code ∈ codes, realizableThetaMassWeight G code.1) ≤
        ∑ code : RealizableCandidate G bases s L × Fin 3,
          realizableThetaMassWeight G code.1 :=
    Finset.sum_le_sum_of_subset_of_nonneg hcodesub hnonneg
  have htag :
      (∑ code : RealizableCandidate G bases s L × Fin 3,
        realizableThetaMassWeight G code.1) =
        3 * (∑ w : RealizableCandidate G bases s L,
          realizableThetaMassWeight G w) := by
    rw [Fintype.sum_prod_type]
    simp [Finset.sum_const, nsmul_eq_mul, realizableThetaMassWeight,
      Finset.mul_sum]
  calc
    (∑ C ∈ excluded, cycleWordMassWeight G C) =
        ∑ C ∈ sources, cycleWordMassWeight G C.1 := hsourceSum
    _ ≤ (2 : ℝ) ^ q * (∑ code ∈ codes, realizableThetaMassWeight G code.1) := hcharge
    _ ≤ (2 : ℝ) ^ q *
        (∑ code : RealizableCandidate G bases s L × Fin 3,
          realizableThetaMassWeight G code.1) := by
          exact mul_le_mul_of_nonneg_left hall (by positivity)
    _ = 3 * (2 : ℝ) ^ q *
        (∑ w : RealizableCandidate G bases s L, realizableThetaMassWeight G w) := by
          rw [htag]
          ring

/-- Weighted strengthening of the source-theta selector. It returns the
same selected candidate/tag as recovery, together with the exact base-plus-
branch exponent relation. The inequality is permutation-invariant in the
constituent tag: the candidate base and omitted branch partition all three
theta branches, while the recovered source is the left-right constituent. -/
theorem source_theta_yields_weighted_recovering_code
    {bases : Finset G.CycleWord} {s L q : ℕ} {u v : G.Vertex}
    (sourceTheta : ThetaPaths G.toSimpleGraph u v) (huv : u ≠ v)
    (p : ThetaPair)
    (hbase : cycleWordOfWalk G
      (leftRightCycle G.toSimpleGraph (thetaAtPair sourceTheta p))
      (leftRightCycle_isCycle G.toSimpleGraph (thetaAtPair sourceTheta p) huv) ∈ bases)
    (hs : s < (thetaAtPair sourceTheta p).external.length)
    (hL : (thetaAtPair sourceTheta p).external.length ≤ L)
    (hcharge : pairLength G.toSimpleGraph sourceTheta p +
        omittedBranchLength G.toSimpleGraph sourceTheta p ≤
        q + pairLength G.toSimpleGraph sourceTheta .leftRight) :
    ∃ code : RealizableCandidate G bases s L × Fin 3,
      recoverThetaTagCycle G code = thetaPairWord G sourceTheta huv 0 ∧
      G.wordLength (candidateCycle G code.1.1).1 + candidateBranchLength G code.1.1 ≤
        q + G.wordLength (thetaPairWord G sourceTheta huv 0).1 := by
  classical
  let relabelled := thetaAtPair sourceTheta p
  let w := candidateOfSourceTheta G bases s L relabelled huv .leftRight hbase hs hL
  have hword : cycleWordOfWalk G (leftRightCycle G.toSimpleGraph relabelled)
      (leftRightCycle_isCycle G.toSimpleGraph relabelled huv) = candidateCycle G w := by
    exact (candidateOfSourceTheta_cycle_eq G bases s L relabelled huv .leftRight
      hbase hs hL).symm
  have hpath : candidatePath G w = relabelled.external := by
    exact (candidateOfSourceTheta_path_eq G bases s L relabelled huv .leftRight
      hbase hs hL).symm
  let R := candidateRealizationOfSourceTheta G w relabelled .leftRight huv hword hpath
  let rw : RealizableCandidate G bases s L := ⟨w, ⟨R⟩⟩
  let tag := sourceLeftRightTag p
  let R' := chosenCandidateRealization G rw
  have hbaseWord : cycleWordOfWalk G (leftRightCycle G.toSimpleGraph relabelled)
      (leftRightCycle_isCycle G.toSimpleGraph relabelled huv) =
      cycleWordOfWalk G (leftRightCycle G.toSimpleGraph (chosenThetaPaths G R'))
        (leftRightCycle_isCycle G.toSimpleGraph (chosenThetaPaths G R') R'.endpoints_ne) := by
    calc
      _ = candidateCycle G w := hword
      _ = candidateCycle G rw.1 := rfl
      _ = cycleWordOfWalk G R'.baseWalk R'.base_isCycle := R'.word_eq.symm
      _ = cycleWordOfWalk G (R'.baseWalk.rotate R'.left_on_base)
          (R'.base_isCycle.rotate R'.left_on_base) :=
          (cycleWordOfWalk_rotate_eq G R'.baseWalk R'.base_isCycle R'.left_on_base).symm
      _ = _ := cycleWord_eq_of_walk_eq G
        (R'.base_isCycle.rotate R'.left_on_base)
        (leftRightCycle_isCycle G.toSimpleGraph (chosenThetaPaths G R') R'.endpoints_ne)
        (chosenThetaPaths_spec G R').1.symm
  have hbaseArcs := arcCorrespondence_of_equal_base_cycleWord G relabelled
    (chosenThetaPaths G R') huv hbaseWord
  have hext : relabelled.external = (chosenThetaPaths G R').external := by
    calc
      _ = candidatePath G w := hpath.symm
      _ = candidatePath G rw.1 := rfl
      _ = (chosenThetaPaths G R').external := (chosenThetaPaths_spec G R').2.2.2.2.2.symm
  have hrelabeled := sourceLeftRight_arcPairCorrespondence G sourceTheta p
  obtain ⟨targetTag, hbaseTag⟩ := pairArcCorr_of_base_and_external G relabelled
    (chosenThetaPaths G R') tag hbaseArcs (congrArg (fun z => z.edges.toFinset) hext)
  have harcs := arcCorr_trans G hrelabeled hbaseTag
  have hrec := selectedThetaCode_recovery_of_arcCorrespondence G R' sourceTheta
    huv 0 targetTag (thetaPairWord G sourceTheta huv 0) rfl harcs
  have hbaseLen : G.wordLength (candidateCycle G w).1 =
      pairLength G.toSimpleGraph sourceTheta p := by
    calc
      G.wordLength (candidateCycle G w).1 =
          (leftRightCycle G.toSimpleGraph relabelled).length :=
        candidate_cycle_walk_length_eq G bases s L w
          (leftRightCycle G.toSimpleGraph relabelled)
          (leftRightCycle_isCycle G.toSimpleGraph relabelled huv) hword
      _ = pairLength G.toSimpleGraph sourceTheta p := by
        calc
          (leftRightCycle G.toSimpleGraph relabelled).length =
              (pairCycle sourceTheta p).length :=
            congrArg SimpleGraph.Walk.length (thetaAtPair_base_eq sourceTheta p)
          _ = pairLength G.toSimpleGraph sourceTheta p := by
            cases p <;> simp [pairCycle, pairLength, leftRightCycle,
              leftExternalCycle, externalRightCycle, SimpleGraph.Walk.length_append]
  have hbranchLen : candidateBranchLength G w =
      omittedBranchLength G.toSimpleGraph sourceTheta p := by
    change (thetaAtPair sourceTheta p).external.length = _
    rw [thetaAtPair_external_eq]
    cases p <;> rfl
  have hsourceLen : G.wordLength (thetaPairWord G sourceTheta huv 0).1 =
      pairLength G.toSimpleGraph sourceTheta .leftRight := by
    calc
      G.wordLength (thetaPairWord G sourceTheta huv 0).1 =
          (thetaPairWalk G sourceTheta 0).length :=
        cycleWordOfWalk_length G (thetaPairWalk G sourceTheta 0)
          (thetaPairWalk_isCycle G sourceTheta huv 0)
      _ = pairLength G.toSimpleGraph sourceTheta .leftRight := by
        simp [thetaPairWalk, thetaPairPaths, pairLength, leftRightCycle]
  refine ⟨(rw, targetTag), ?_, ?_⟩
  · simpa [rw, recoverThetaTagCycle, R'] using hrec.symm
  · change G.wordLength (candidateCycle G w).1 + candidateBranchLength G w ≤
      q + G.wordLength (thetaPairWord G sourceTheta huv 0).1
    rw [hbaseLen, hbranchLen, hsourceLen]
    exact hcharge

/-- A concrete short external return yields a selected recovering code with
the exponent charge required above. This is the end-to-end bridge from a
rejected short cycle's return path to the finite weighted sum. -/
theorem short_external_return_yields_weighted_code
    (D s q L : ℕ)
    (hgirth : ShortWalks.GirthGreater G.toSimpleGraph D)
    (hs : 2 * s ≤ D) (hqL : q ≤ L)
    {x u v : G.Vertex} (c : G.toSimpleGraph.Walk x x) (hc : c.IsCycle)
    (hclen : c.length ≤ L)
    (hu : u ∈ c.support) (hv : v ∈ c.support) (huv : u ≠ v)
    (r : G.toSimpleGraph.Walk u v) (hr : r.IsPath) (hrlen : r.length ≤ q)
    (hinterior : ∀ z, z ∈ r.support → z ≠ u → z ≠ v → z ∉ c.support)
    (hedges : ∀ e, e ∈ r.edges → e ∉ c.edges) :
    ∃ code : RealizableCandidate G (shortCycleWords G L) s L × Fin 3,
      recoverThetaTagCycle G code = cycleWordOfWalk G c hc ∧
      G.wordLength (candidateCycle G code.1.1).1 +
        candidateBranchLength G code.1.1 ≤
        q + G.wordLength (cycleWordOfWalk G c hc).1 := by
  classical
  obtain ⟨t, hbase, hbaseCycle, hleftExt, hrightExt, hlenLR, hlenLE,
    hlenER, hext⟩ := ExternalReturnTheta.externalReturn_theta G.toSimpleGraph
      c hc hu hv huv r hr hinterior hedges
  have hLR : D < pairLength G.toSimpleGraph t .leftRight := by
    simpa [pairLength, leftRightCycle_length] using
      hgirth u (leftRightCycle G.toSimpleGraph t) hbaseCycle
  have hLE : D < pairLength G.toSimpleGraph t .leftExternal := by
    simpa [pairLength, leftExternalCycle_length] using
      hgirth u (leftExternalCycle G.toSimpleGraph t) hleftExt
  have hER : D < pairLength G.toSimpleGraph t .externalRight := by
    simpa [pairLength, externalRightCycle_length] using
      hgirth u (externalRightCycle G.toSimpleGraph t) hrightExt
  have hrotateLen : (c.rotate hu).length = c.length := by
    have hs' := SimpleGraph.Walk.take_spec c hu
    have hlen := congrArg SimpleGraph.Walk.length hs'
    simp only [SimpleGraph.Walk.length_append, SimpleGraph.Walk.rotate] at hlen ⊢
    omega
  have hsourceWalkLen : (leftRightCycle G.toSimpleGraph t).length ≤ L := by
    calc
      (leftRightCycle G.toSimpleGraph t).length = (c.rotate hu).length := congrArg
        SimpleGraph.Walk.length hbase
      _ = c.length := hrotateLen
      _ ≤ L := hclen
  have hsourceLen : pairLength G.toSimpleGraph t .leftRight ≤ L := by
    calc
      pairLength G.toSimpleGraph t .leftRight =
          (leftRightCycle G.toSimpleGraph t).length := by simp [pairLength, hlenLR]
      _ ≤ L := hsourceWalkLen
  have hmin := minimumPair_girth_length_bounds G.toSimpleGraph t D s L q
    hsourceLen (by simpa [hext] using hrlen) hqL hLR hLE hER hs
  let p := minimumPair G.toSimpleGraph t
  let relabelled := thetaAtPair t p
  have hwordLen : G.wordLength
      (cycleWordOfWalk G (leftRightCycle G.toSimpleGraph relabelled)
        (leftRightCycle_isCycle G.toSimpleGraph relabelled huv)).1 =
      pairLength G.toSimpleGraph t p := by
    have hpairWordLength : ∀ q : ThetaPair,
        G.wordLength
          (cycleWordOfWalk G
            (leftRightCycle G.toSimpleGraph (thetaAtPair t q))
            (leftRightCycle_isCycle G.toSimpleGraph (thetaAtPair t q) huv)).1 =
          pairLength G.toSimpleGraph t q := by
      intro q
      change BoundaryDecay.Cycle.length
        (cycleWordOfWalk G
          (leftRightCycle G.toSimpleGraph (thetaAtPair t q))
          (leftRightCycle_isCycle G.toSimpleGraph (thetaAtPair t q) huv)) = _
      cases q with
      | leftRight => simpa [thetaAtPair, pairLength] using
          ExternalReturnTheta.leftRightCycleWord_length G t huv
      | leftExternal => simpa [thetaAtPair, leftRightCycle, leftExternalCycle, pairLength] using
          ExternalReturnTheta.leftExternalCycleWord_length G t huv
      | externalRight => simpa [thetaAtPair, leftRightCycle, externalRightCycle, pairLength] using
          ExternalReturnTheta.externalRightCycleWord_length G t huv
    simpa [relabelled] using hpairWordLength p
  have hbaseMem : cycleWordOfWalk G (leftRightCycle G.toSimpleGraph relabelled)
      (leftRightCycle_isCycle G.toSimpleGraph relabelled huv) ∈ shortCycleWords G L := by
    have hlen : G.wordLength (cycleWordOfWalk G (leftRightCycle G.toSimpleGraph relabelled)
        (leftRightCycle_isCycle G.toSimpleGraph relabelled huv)).1 ≤ L := by
      rw [hwordLen]
      exact hmin.1
    simp [shortCycleWords, hlen]
  have hs' : s < relabelled.external.length := by
    change s < (thetaAtPair t (minimumPair G.toSimpleGraph t)).external.length
    rw [thetaAtPair_external_eq]
    cases hpair : minimumPair G.toSimpleGraph t <;>
      simpa [hpair, omittedBranchLength, omittedBranch] using hmin.2.1
  have hL' : relabelled.external.length ≤ L := by
    change (thetaAtPair t (minimumPair G.toSimpleGraph t)).external.length ≤ L
    rw [thetaAtPair_external_eq]
    cases hpair : minimumPair G.toSimpleGraph t with
    | leftRight => simpa [hpair, omittedBranchLength, omittedBranch] using hmin.2.2.2.2
    | leftExternal => simpa [hpair, omittedBranchLength, omittedBranch] using hmin.2.2.2.1
    | externalRight => simpa [hpair, omittedBranchLength, omittedBranch] using hmin.2.2.1
  have hsource : cycleWordOfWalk G c hc = thetaPairWord G t huv 0 := by
    have hw := sourceCycleWord_eq_externalReturn_base G c hc hu huv t hbase
    simpa [thetaPairWord, thetaPairWalk, thetaPairPaths, leftRightCycle] using hw
  have hcharge : pairLength G.toSimpleGraph t p + omittedBranchLength G.toSimpleGraph t p ≤
      q + pairLength G.toSimpleGraph t .leftRight :=
    by
      have hcharge' := ThetaLengthAccounting.minimum_pair_charge_bound
        t q (by simpa [hext] using hrlen)
      simpa [p, Nat.add_comm] using hcharge'
  obtain ⟨code, hrecover, hchargeCode⟩ := source_theta_yields_weighted_recovering_code
    G t huv p hbaseMem hs' hL' hcharge
  refine ⟨code, ?_, ?_⟩
  · exact hrecover.trans hsource.symm
  · simpa only [hsource] using hchargeCode





end Erdos1016.Proof.WeightedThetaCharging

end
