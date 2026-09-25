import Erdos1016.Expansion.BondMinimizer
import Erdos1016.Decomposition.Descent.ConcaveBudget
import Erdos1016.Decomposition.Regions.Cyclicity

set_option autoImplicit false

/-! # Potential decrease and the actual controlled descent (source Lemma 14.1) -/
noncomputable section
namespace Erdos1016.SafeCore
local instance instSafeCoreDescentPropDecidable (p : Prop) : Decidable p := Classical.propDecidable p
variable (G : PhysicalGraph) (P : CutParameters)

def budget (U : Finset G.Vertex) : ℝ := P.B * (U.card : ℝ) ^ P.p

def potential (U : Finset G.Vertex) : ℝ := (cutSize G U : ℝ) - budget G P U

def Low (U : Finset G.Vertex) : Prop := (cutSize G U : ℝ) ≤ budget G P U

def Expanded (U : Finset G.Vertex) : Prop :=
  HasExpansion G U (P.epsilon * (U.card : ℝ) ^ (P.p - 1))

def GoodRegion (U : Finset G.Vertex) : Prop :=
  ConnectedRegion G U ∧ Expanded G P U ∧ Low G P U

def Cheap {U : Finset G.Vertex} (s : BondSplit G U) : Prop :=
  (crossSize G s.left s.right : ℝ) <
    P.epsilon * (min s.left.card s.right.card : ℕ) * (U.card : ℝ) ^ (P.p - 1)

@[simp] theorem low_iff_potential_nonpos (U : Finset G.Vertex) :
    Low G P U ↔ potential G P U ≤ 0 := by
  unfold Low potential
  exact (sub_nonpos).symm

theorem exists_cheap_bond {U : Finset G.Vertex}
    (hU : ConnectedRegion G U) (hn : ¬ Expanded G P U) :
    ∃ s : BondSplit G U, Cheap G P s := by
  obtain ⟨s, hs⟩ := exists_bond_of_not_expands G hU hn
  refine ⟨s, ?_⟩
  unfold Cheap
  convert hs using 1 <;> ring

theorem cheap_symm {U : Finset G.Vertex} {s : BondSplit G U}
    (h : Cheap G P s) : Cheap G P s.symm := by
  simpa only [Cheap, BondSplit.symm, crossSize_comm, min_comm] using h

/-- Exact cut splitting and the concavity inequality pay the entire new cut. -/
theorem potential_split_le {U : Finset G.Vertex} {s : BondSplit G U}
    (hcheap : Cheap G P s) :
    potential G P s.left + potential G P s.right ≤ potential G P U := by
  have hL : 0 < (s.left.card : ℝ) := by exact_mod_cast Finset.card_pos.2 s.left_connected.1
  have hR : 0 < (s.right.card : ℝ) := by exact_mod_cast Finset.card_pos.2 s.right_connected.1
  have hn : (s.left.card : ℝ) + s.right.card = U.card := by exact_mod_cast s.card_add
  have hgap := power_gap P.p_pos P.p_lt_one.le hL hR
  rw [hn, ← Nat.cast_min] at hgap
  let z : ℝ := (min s.left.card s.right.card : ℕ) * (U.card : ℝ) ^ (P.p - 1)
  have hz : 0 ≤ z := by dsimp [z]; positivity
  have hbudget := mul_le_mul_of_nonneg_left hgap P.B_pos.le
  have hpay := mul_le_mul_of_nonneg_right P.pays_split hz
  have hcut : 2 * (crossSize G s.left s.right : ℝ) ≤
      P.B * ((s.left.card : ℝ) ^ P.p + (s.right.card : ℝ) ^ P.p - (U.card : ℝ) ^ P.p) := by
    have hcheap' : (crossSize G s.left s.right : ℝ) < P.epsilon * z := by
      simpa only [Cheap, z, mul_assoc] using hcheap
    calc
      2 * (crossSize G s.left s.right : ℝ) ≤ 2 * (P.epsilon * z) := by linarith
      _ ≤ P.B * (gapConstant P.p * (min s.left.card s.right.card : ℕ) *
          (U.card : ℝ) ^ (P.p - 1)) := by
        dsimp [z] at hpay ⊢
        nlinarith only [hpay]
      _ ≤ _ := hbudget
  have hident : (cutSize G s.left : ℝ) + cutSize G s.right =
      (cutSize G U : ℝ) + 2 * crossSize G s.left s.right := by
    have h := cutSize_union G s.left s.right s.disjoint
    rw [s.union_eq] at h
    exact_mod_cast h
  unfold potential budget
  linarith





/-- A nonempty proper region has at least one ORIGINAL exterior component. -/
theorem exteriorCount_pos {U : Finset G.Vertex} (hp : Uᶜ.Nonempty) :
    0 < exteriorCount G U := by
  obtain ⟨v, hv⟩ := hp
  obtain ⟨C, hC, _⟩ := components_cover G hv
  exact Finset.card_pos.2 ⟨C, hC⟩

theorem proper_of_subset {U S : Finset G.Vertex} (hp : Uᶜ.Nonempty) (hSU : S ⊆ U) :
    Sᶜ.Nonempty := by
  obtain ⟨v, hv⟩ := hp
  exact ⟨v, Finset.mem_compl.2 fun hs => (Finset.mem_compl.1 hv) (hSU hs)⟩





end Erdos1016.SafeCore
