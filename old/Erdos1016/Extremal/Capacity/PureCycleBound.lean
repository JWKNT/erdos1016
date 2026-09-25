import Erdos1016.Extremal.Capacity.EdgePartitionRank

set_option autoImplicit false

/-!
# Pure cycles on one side of an edge partition

A cycle supported wholly by `E` is a nonzero element of the restricted cycle
space. This gives the restricted analogue of the basic cycle-state bound.
-/

noncomputable section

namespace Erdos1016.PhysicalGraph

/-- A host cycle whose word vanishes on every edge outside `E`. -/
abbrev PureCycleWord (G : PhysicalGraph) (E : Finset G.Edge) :=
  {C : G.CycleWord // ∀ e, e ∉ E → C.1 e = 0}

/-- The set of distinct lengths attained by cycles supported entirely in `E`. -/
def pureCycleLengths (G : PhysicalGraph) (E : Finset G.Edge) : Finset ℕ := by
  classical
  exact Finset.univ.image fun C : G.PureCycleWord E => G.wordLength C.1.1

private def pureCycleRestriction (G : PhysicalGraph) (E : Finset G.Edge) :
    G.PureCycleWord E → {x : G.RestrictedCycleSpace E // x ≠ 0} := fun C =>
  ⟨⟨G.restrictWord E C.1.1, by
      change G.restrictedBoundary E (G.restrictWord E C.1.1) = 0
      change G.boundary (G.extendWord E (G.restrictWord E C.1.1)) = 0
      rw [G.extend_restrict_of_outside_zero E C.1.1 C.2]
      exact C.1.2.2.1⟩,
    by
      intro hz
      apply C.1.2.1
      have hword : G.restrictWord E C.1.1 = 0 := congrArg Subtype.val hz
      funext e
      by_cases he : e ∈ E
      · have h := congrFun hword ⟨e, he⟩
        simpa [restrictWord] using h
      · exact C.2 e he⟩

noncomputable instance restrictedCycleSpaceFintype (G : PhysicalGraph)
    (E : Finset G.Edge) : Fintype (G.RestrictedCycleSpace E) := by
  classical
  letI : Fintype (G.RestrictedEdge E) := Fintype.ofFinite _
  letI : Fintype (G.RestrictedWord E) := Fintype.ofFinite _
  haveI : Finite (G.RestrictedCycleSpace E) :=
    Finite.of_injective (fun x : G.RestrictedCycleSpace E => x.1) (by
      intro x y h
      exact Subtype.ext h)
  exact Fintype.ofFinite _

private theorem pureCycleRestriction_injective (G : PhysicalGraph)
    (E : Finset G.Edge) : Function.Injective (pureCycleRestriction G E) := by
  intro C D h
  apply Subtype.ext
  apply Subtype.ext
  have hrestr : G.restrictWord E C.1.1 = G.restrictWord E D.1.1 :=
    congrArg (fun z : {x : G.RestrictedCycleSpace E // x ≠ 0} => z.1.1) h
  have hC := G.extend_restrict_of_outside_zero E C.1.1 C.2
  have hD := G.extend_restrict_of_outside_zero E D.1.1 D.2
  calc
    C.1.1 = G.extendWord E (G.restrictWord E C.1.1) := hC.symm
    _ = G.extendWord E (G.restrictWord E D.1.1) := congrArg (G.extendWord E) hrestr
    _ = D.1.1 := hD

/-- The restricted cycle space has `2 ^ restrictedCycleRank E` elements. -/
lemma restrictedCycleSpace_card (G : PhysicalGraph) (E : Finset G.Edge) :
    Fintype.card (G.RestrictedCycleSpace E) = 2 ^ G.restrictedCycleRank E := by
  classical
  have h := Module.card_eq_pow_finrank (K := F₂) (V := G.RestrictedCycleSpace E)
  simpa [F₂, restrictedCycleRank] using h

/-- There are at most `2 ^ restrictedCycleRank E - 1` distinct lengths of
cycles supported wholly in `E`. -/
theorem pureCycleLengths_card_le (G : PhysicalGraph) (E : Finset G.Edge) :
    (G.pureCycleLengths E).card ≤ 2 ^ G.restrictedCycleRank E - 1 := by
  classical
  have hinj := Fintype.card_le_of_injective
    (pureCycleRestriction G E) (pureCycleRestriction_injective G E)
  have hnz : Fintype.card {z : G.RestrictedCycleSpace E // z ≠ 0} =
      Fintype.card (G.RestrictedCycleSpace E) - 1 := by
    rw [Fintype.card_of_subtype (Finset.univ.erase 0)
      (by intro z; simp)]
    rw [Finset.card_erase_of_mem (Finset.mem_univ (0 : G.RestrictedCycleSpace E)),
      Finset.card_univ]
  rw [hnz, G.restrictedCycleSpace_card] at hinj
  have hcycle : Fintype.card (G.PureCycleWord E) ≤
      2 ^ G.restrictedCycleRank E - 1 := hinj
  unfold pureCycleLengths
  calc
    (Finset.univ.image (fun C : G.PureCycleWord E => G.wordLength C.1.1)).card ≤
        (Finset.univ : Finset (G.PureCycleWord E)).card := Finset.card_image_le
    _ = Fintype.card (G.PureCycleWord E) := Finset.card_univ
    _ ≤ 2 ^ G.restrictedCycleRank E - 1 := hcycle

end Erdos1016.PhysicalGraph
