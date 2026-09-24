import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Data.Finset.Powerset
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Tactic

set_option autoImplicit false

/-!
# The maximal finite 2-core

The construction chooses the largest vertex set whose induced graph has
minimum degree at least two. This is the canonical unsuppressed 2-core and
works without a connectivity assumption. -/

noncomputable section
namespace Erdos1016.Nonbacktracking.FiniteTwoCore

local instance twoCoreDecidable (p : Prop) : Decidable p := Classical.propDecidable p

variable {V : Type*} [Fintype V] [DecidableEq V] (J : SimpleGraph V)

/-- Degree in the graph induced by a finite set of vertices. -/
def degreeWithin (S : Finset V) (v : V) : ℕ :=
  (S.filter fun w => J.Adj v w).card

/-- Cubic deficit of the induced subgraph, written using its degree sum. -/
def cubicDeficit (S : Finset V) : ℤ :=
  3 * (S.card : ℤ) - ∑ v ∈ S, (degreeWithin J S v : ℤ)

/-- Vertices of degree two in the induced graph on a finite set. -/
def degreeTwoCount (S : Finset V) : ℕ :=
  (S.filter fun v => degreeWithin J S v = 2).card

theorem degreeWithin_le_degree (S : Finset V) (v : V) :
    degreeWithin J S v ≤ J.degree v := by
  unfold degreeWithin
  apply Finset.card_le_card
  intro w hw
  exact (SimpleGraph.mem_neighborFinset J v w).2 (Finset.mem_filter.1 hw).2

/-- The degree of a vertex in the induced graph is the induced degree used by
the finite core construction. -/
theorem induce_degree_eq_degreeWithin (S : Finset V) (v : V) (hv : v ∈ S) :
    (J.induce (↑S : Set V)).degree ⟨v, hv⟩ = degreeWithin J S v := by
  classical
  unfold degreeWithin SimpleGraph.degree
  simp only [SimpleGraph.neighborFinset_eq_filter, SimpleGraph.induce]
  apply Finset.card_bij (fun w _ => w.1)
  · intro w hw
    simp only [Finset.mem_filter, Finset.mem_attach] at hw
    rcases hw with ⟨_, hadj⟩
    simp only [Finset.mem_filter]
    exact ⟨w.2, by simpa [SimpleGraph.induce] using hadj⟩
  · intro a ha b hb hab
    exact Subtype.ext hab
  · intro w hw
    rcases Finset.mem_filter.1 hw with ⟨hwS, hadj⟩
    refine ⟨⟨w, hwS⟩, ?_, rfl⟩
    simp only [Finset.mem_filter, Finset.mem_attach]
    exact ⟨Finset.mem_univ _, by simpa [SimpleGraph.induce] using hadj⟩

private theorem degreeWithin_erase_add {S : Finset V} {v w : V}
    (hv : v ∈ S) (hw : w ∈ S.erase v) :
    degreeWithin J S w = degreeWithin J (S.erase v) w +
      (if J.Adj w v then 1 else 0) := by
  have hwS : w ∈ S := (Finset.mem_erase.1 hw).2
  have hwv : w ≠ v := (Finset.mem_erase.1 hw).1
  unfold degreeWithin
  rw [← Finset.insert_erase hv]
  rw [Finset.filter_insert]
  by_cases hadj : J.Adj w v
  · simp [hadj, Finset.card_insert_of_not_mem, Finset.not_mem_erase]
  · simp [hadj]

private theorem adjacency_sum_erase {S : Finset V} {v : V} :
    (∑ w ∈ S.erase v, if J.Adj w v then 1 else 0) = degreeWithin J S v := by
  have hset : (S.erase v).filter (fun w => J.Adj w v) =
      S.filter (fun w => J.Adj v w) := by
    ext w
    simp only [Finset.mem_filter, Finset.mem_erase]
    constructor
    · rintro ⟨⟨hne, hwS⟩, hadj⟩
      exact ⟨hwS, hadj.symm⟩
    · rintro ⟨hwS, hadj⟩
      refine ⟨⟨?_, hwS⟩, hadj.symm⟩
      intro heq
      subst w
      exact J.loopless v hadj
  unfold degreeWithin
  rw [Finset.sum_boole, hset]
  simp

private theorem degreeWithin_sum_erase {S : Finset V} {v : V} (hv : v ∈ S) :
    (∑ w ∈ S, degreeWithin J S w) =
      (∑ w ∈ S.erase v, degreeWithin J (S.erase v) w) +
        2 * degreeWithin J S v := by
  have hsum := Finset.sum_erase_add S (fun w => degreeWithin J S w) hv
  have hrest : (∑ w ∈ S.erase v, degreeWithin J S w) =
      (∑ w ∈ S.erase v, degreeWithin J (S.erase v) w) +
        (∑ w ∈ S.erase v, if J.Adj w v then 1 else 0) := by
    calc
      _ = ∑ w ∈ S.erase v,
          (degreeWithin J (S.erase v) w + if J.Adj w v then 1 else 0) := by
            apply Finset.sum_congr rfl
            intro w hw
            rw [degreeWithin_erase_add J hv hw]
      _ = _ := by rw [Finset.sum_add_distrib]
  rw [adjacency_sum_erase J] at hrest
  calc
    _ = (∑ w ∈ S.erase v, degreeWithin J S w) + degreeWithin J S v := hsum.symm
    _ = ((∑ w ∈ S.erase v, degreeWithin J (S.erase v) w) +
          degreeWithin J S v) + degreeWithin J S v := by rw [hrest]
    _ = _ := by omega

/-- Deleting a vertex of degree at most one drops cubic deficit by at least
one. This is the exact integer potential used by the finite peeling. -/
theorem cubicDeficit_step {S : Finset V} {v : V} (hv : v ∈ S)
    (hdeg : degreeWithin J S v < 2) :
    cubicDeficit J (S.erase v) + 1 ≤ cubicDeficit J S := by
  have hstep : cubicDeficit J S = cubicDeficit J (S.erase v) + 3 -
      2 * (degreeWithin J S v : ℤ) := by
    have hsum : (∑ w ∈ S, (degreeWithin J S w : ℤ)) =
        (∑ w ∈ S.erase v, (degreeWithin J (S.erase v) w : ℤ)) +
          2 * (degreeWithin J S v : ℤ) := by
      exact_mod_cast degreeWithin_sum_erase J hv
    unfold cubicDeficit
    rw [Finset.card_erase_of_mem hv, hsum]
    have hcard : 1 ≤ S.card := by
      have := Finset.card_pos.2 ⟨v, hv⟩
      omega
    rw [Nat.cast_sub hcard]
    ring
  have hdeg' : (degreeWithin J S v : ℤ) ≤ 1 := by
    exact_mod_cast (by omega : degreeWithin J S v ≤ 1)
  rw [hstep]
  linarith

theorem cubicDeficit_nonneg (S : Finset V) (hmax : ∀ v, J.degree v ≤ 3) :
    0 ≤ cubicDeficit J S := by
  have hsum : (∑ v ∈ S, degreeWithin J S v) ≤ 3 * S.card := by
    calc
      _ ≤ ∑ _v ∈ S, 3 := Finset.sum_le_sum fun v hv =>
        degreeWithin_le_degree J S v |>.trans (hmax v)
      _ = 3 * S.card := by simp [Nat.mul_comm]
  have hsum' : (∑ v ∈ S, (degreeWithin J S v : ℤ)) ≤
      3 * (S.card : ℤ) := by exact_mod_cast hsum
  unfold cubicDeficit
  linarith

/-- An induced vertex set has minimum degree at least two. -/
def MinTwo (S : Finset V) : Prop :=
  ∀ v ∈ S, 2 ≤ degreeWithin J S v

private theorem degreeWithin_mono {A B : Finset V} (hAB : A ⊆ B) (v : V) :
    degreeWithin J A v ≤ degreeWithin J B v := by
  unfold degreeWithin
  apply Finset.card_le_card
  intro w hw
  rcases Finset.mem_filter.1 hw with ⟨hwA, hadj⟩
  exact Finset.mem_filter.2 ⟨hAB hwA, hadj⟩

private theorem minTwo_union {A B : Finset V}
    (hA : MinTwo J A) (hB : MinTwo J B) : MinTwo J (A ∪ B) := by
  intro v hv
  rcases Finset.mem_union.1 hv with hvA | hvB
  · exact (hA v hvA).trans (degreeWithin_mono J (Finset.subset_union_left) v)
  · exact (hB v hvB).trans (degreeWithin_mono J (Finset.subset_union_right) v)

/-- Existence and maximality of the full finite 2-core. -/
theorem exists_maximal (U : Finset V) :
    ∃ C ⊆ U, MinTwo J C ∧ ∀ A ⊆ U, MinTwo J A → A ⊆ C := by
  let candidates := U.powerset.filter (MinTwo J)
  have hne : candidates.Nonempty := by
    refine ⟨∅, ?_⟩
    simp [candidates, MinTwo]
  obtain ⟨C, hC, hmax⟩ := Finset.exists_max_image candidates Finset.card hne
  have hC' := Finset.mem_filter.1 hC
  have hCU : C ⊆ U := Finset.mem_powerset.1 hC'.1
  have hmin : MinTwo J C := hC'.2
  refine ⟨C, hCU, hmin, ?_⟩
  intro A hAU hA
  have hAcan : A ∈ candidates := Finset.mem_filter.2
    ⟨Finset.mem_powerset.2 hAU, hA⟩
  have hUnionCan : A ∪ C ∈ candidates := Finset.mem_filter.2
    ⟨Finset.mem_powerset.2 (Finset.union_subset hAU hCU), minTwo_union J hA hmin⟩
  have hsize : (A ∪ C).card ≤ C.card := hmax (A ∪ C) hUnionCan
  have hEq : C = A ∪ C :=
    Finset.eq_of_subset_of_card_le Finset.subset_union_right hsize
  intro v hv
  have : v ∈ A ∪ C := Finset.mem_union_left C hv
  rw [hEq]
  exact this

/-- A named finite 2-core, obtained from the maximality theorem. -/
def vertices (U : Finset V) : Finset V :=
  Classical.choose (exists_maximal J U)

theorem vertices_subset (U : Finset V) : vertices J U ⊆ U :=
  (Classical.choose_spec (exists_maximal J U)).1

theorem vertices_minTwo (U : Finset V) : MinTwo J (vertices J U) :=
  (Classical.choose_spec (exists_maximal J U)).2.1

theorem maximal (U A : Finset V) (hAU : A ⊆ U) (hA : MinTwo J A) :
    A ⊆ vertices J U :=
  (Classical.choose_spec (exists_maximal J U)).2.2 A hAU hA



/-- Ambient maximum degree is inherited by the induced 2-core. -/
theorem vertices_maxDegree (U : Finset V) (B : ℕ)
    (hmax : ∀ v, J.degree v ≤ B) (v : V) :
    degreeWithin J (vertices J U) v ≤ B :=
  (degreeWithin_le_degree J _ _).trans (hmax v)

/-- A finite leaf-peeling certificate from a vertex set down to its core. -/
inductive Peeling (C : Finset V) : Finset V → Prop
  | done : Peeling C C
  | remove {S : Finset V} {v : V}
      (hvc : v ∉ C) (hv : v ∈ S) (hdeg : degreeWithin J S v < 2)
      (tail : Peeling C (S.erase v)) : Peeling C S

/-- Every intermediate superset of the full core can be reduced by repeatedly
removing a vertex of current degree at most one. -/
theorem exists_peeling (U S : Finset V) (hCU : vertices J U ⊆ S)
    (hSU : S ⊆ U) : Peeling J (vertices J U) S := by
  classical
  let C := vertices J U
  have aux : ∀ m : ℕ, ∀ S : Finset V, C ⊆ S → S ⊆ U →
      (S \ C).card = m → Peeling J C S := by
    intro m
    induction m using Nat.strong_induction_on with
    | h m ih =>
      intro T hCT hTU hm
      by_cases heq : T = C
      · subst T
        exact Peeling.done
      · have hlow : ∃ v ∈ T \ C, degreeWithin J T v < 2 := by
          by_contra hnot
          push_neg at hnot
          have hlarge : ∀ v ∈ T \ C, 2 ≤ degreeWithin J T v := by
            intro v hv
            exact hnot v hv
          have hTmin : MinTwo J T := by
            intro v hv
            by_cases hvC : v ∈ C
            · exact (vertices_minTwo J U v hvC).trans
                (degreeWithin_mono J hCT v)
            · exact hlarge v (Finset.mem_sdiff.mpr ⟨hv, hvC⟩)
          have hTC := maximal J U T hTU hTmin
          exact heq (Finset.Subset.antisymm hTC hCT)
        obtain ⟨v, hvTC, hdeg⟩ := hlow
        have hvT : v ∈ T := (Finset.mem_sdiff.1 hvTC).1
        have hvC : v ∉ C := (Finset.mem_sdiff.1 hvTC).2
        have hCerase : C ⊆ T.erase v := by
          intro x hx
          exact Finset.mem_erase.2 ⟨fun h => hvC (h ▸ hx), hCT hx⟩
        have hTerase : T.erase v ⊆ U := (Finset.erase_subset _ _).trans hTU
        have hdiff : (T.erase v \ C) = (T \ C).erase v := by
          ext x
          simp only [Finset.mem_sdiff, Finset.mem_erase]
          simp [and_assoc, and_left_comm, and_comm]
        have hvDiff : v ∈ T \ C := hvTC
        have hmpos : 0 < m := by
          rw [← hm]
          exact Finset.card_pos.2 ⟨v, hvDiff⟩
        have hm' : (T.erase v \ C).card < m := by
          rw [hdiff, Finset.card_erase_of_mem hvDiff, hm]
          exact Nat.sub_lt hmpos (by decide)
        refine Peeling.remove hvC hvT hdeg (ih (T.erase v \ C).card hm' (T.erase v)
          hCerase hTerase rfl)
  exact aux (S \ C).card S (by simpa [C] using hCU) hSU rfl

/-- Cubic deficit is monotone from a peeled remainder to its full 2-core. -/
theorem cubicDeficit_core_le {C S : Finset V} (h : Peeling J C S) :
    cubicDeficit J C ≤ cubicDeficit J S := by
  cases h with
  | done => exact le_rfl
  | @remove S v hvc hv hdeg tail =>
      have htail := cubicDeficit_core_le tail
      have hstep := cubicDeficit_step J hv hdeg
      linarith
termination_by S.card
decreasing_by
  simp_wf
  subst S
  exact Finset.card_erase_lt_of_mem hv

/-- The number of vertices removed by full leaf peeling is at most the
initial cubic deficit. This supplies the order-loss half of the 2-core ledger. -/
theorem peeled_card_le_deficit {C S : Finset V} (h : Peeling J C S)
    (hCS : C ⊆ S) (hmax : ∀ v, J.degree v ≤ 3) :
    ((S \ C).card : ℤ) ≤ cubicDeficit J S := by
  cases h with
  | done =>
      simpa using cubicDeficit_nonneg J C hmax
  | @remove S v hvc hv hdeg tail =>
      have hCS' : C ⊆ S.erase v := by
        intro x hx
        exact Finset.mem_erase.2 ⟨fun heq => hvc (heq ▸ hx), hCS hx⟩
      have hvSC : v ∈ S \ C := Finset.mem_sdiff.mpr ⟨hv, hvc⟩
      have hdiff : (S.erase v \ C) = (S \ C).erase v := by
        ext x
        simp only [Finset.mem_sdiff, Finset.mem_erase]
        simp [and_assoc, and_left_comm, and_comm]
      have hcard : (S \ C).card = (S.erase v \ C).card + 1 := by
        rw [hdiff, Finset.card_erase_of_mem hvSC]
        have hpos : 0 < (S \ C).card := Finset.card_pos.2 ⟨v, hvSC⟩
        omega
      have hcard' : ((S \ C).card : ℤ) =
          ((S.erase v \ C).card : ℤ) + 1 := by exact_mod_cast hcard
      have hstep := cubicDeficit_step J hv hdeg
      have htail := peeled_card_le_deficit tail hCS' hmax
      linarith
termination_by S.card
decreasing_by
  simp_wf
  subst S
  exact Finset.card_erase_lt_of_mem hv

/-- In a subcubic induced 2-core, the cubic deficit is exactly the number of
degree-two vertices. Degree-three vertices contribute zero to the deficit. -/
theorem cubicDeficit_eq_degreeTwoCount {C : Finset V}
    (hmin : MinTwo J C) (hmax : ∀ v, degreeWithin J C v ≤ 3) :
    cubicDeficit J C = (degreeTwoCount J C : ℤ) := by
  have hterm (v : V) (hv : v ∈ C) :
      (3 : ℤ) - (degreeWithin J C v : ℤ) =
        if degreeWithin J C v = 2 then 1 else 0 := by
    have hlo := hmin v hv
    have hhi := hmax v
    by_cases htwo : degreeWithin J C v = 2
    · simp [htwo]
    · have hthree : degreeWithin J C v = 3 := by omega
      simp [htwo, hthree]
  have hsum :
      (∑ v ∈ C, ((3 : ℤ) - (degreeWithin J C v : ℤ))) =
        ∑ v ∈ C, (if degreeWithin J C v = 2 then (1 : ℤ) else 0) := by
    apply Finset.sum_congr rfl
    intro v hv
    exact hterm v hv
  have hcount :
      (degreeTwoCount J C : ℤ) =
        ∑ v ∈ C, (if degreeWithin J C v = 2 then (1 : ℤ) else 0) := by
    unfold degreeTwoCount
    rw [← Finset.sum_boole]
  have hconst : (∑ v ∈ C, (3 : ℤ)) = 3 * (C.card : ℤ) := by simp; ring
  calc
    cubicDeficit J C =
        (∑ v ∈ C, (3 : ℤ)) - ∑ v ∈ C, (degreeWithin J C v : ℤ) := by
          simp [cubicDeficit, hconst]
    _ = ∑ v ∈ C, ((3 : ℤ) - (degreeWithin J C v : ℤ)) := by
          rw [Finset.sum_sub_distrib]
    _ = ∑ v ∈ C, (if degreeWithin J C v = 2 then (1 : ℤ) else 0) := hsum
    _ = (degreeTwoCount J C : ℤ) := hcount.symm

/-- Ledger for finite peeling: the original order is at most the order of the
2-core plus the original cubic deficit. -/
theorem order_le_core_add_deficit {C S : Finset V} (h : Peeling J C S)
    (hCS : C ⊆ S) (hmax : ∀ v, J.degree v ≤ 3) :
    (S.card : ℤ) ≤ (C.card : ℤ) + cubicDeficit J S := by
  have hpartition : S.card = C.card + (S \ C).card := by
    have h := Finset.card_sdiff_add_card_eq_card hCS
    omega
  have hremoved := peeled_card_le_deficit J h hCS hmax
  rw [hpartition]
  push_cast
  linarith

theorem degreeTwoCount_core_le_deficit {C S : Finset V} (h : Peeling J C S)
    (hminCore : MinTwo J C) (hcoreMax : ∀ v, degreeWithin J C v ≤ 3) :
    (degreeTwoCount J C : ℤ) ≤ cubicDeficit J S := by
  have hdef := cubicDeficit_eq_degreeTwoCount J hminCore hcoreMax
  rw [← hdef]
  exact cubicDeficit_core_le J h

end Erdos1016.Nonbacktracking.FiniteTwoCore
end
