import Erdos1016.Cycles.Selection.RootedConflictDegree
import Erdos1016.Expansion.SmallComponents
import Erdos1016.Boundary.ApexLaw

set_option autoImplicit false

/-!
# MANY geometry and decay from expansion and an actual protector

This is manuscript Lemma 4.2 and (4.5), with the conflict graph CONSTRUCTED
from the physical supports. Neither its degree bound nor the original
complement-count identity is a theorem input.

The positive exponent requirement a < 1/4 and the construction of a small
protector are used later in the asymptotic application, not hidden here.
-/

noncomputable section
open scoped BigOperators
namespace Erdos1016.CycleSupply
open SafeCore BoundaryDecay
local instance cycleSupplyProtectedCyclesDecidable (p : Prop) : Decidable p := Classical.propDecidable p
variable (G : PhysicalGraph)

def manyCycleConflictBound (κ : ℝ) (D : ℕ) : ℕ :=
  D * (Nat.ceil ((2 * (D : ℝ)) / κ) + 2) +
    2 * Nat.ceil ((D : ℝ) / κ) + 1

private theorem real_le_natCeil (x : ℝ) : x ≤ (Nat.ceil x : ℝ) :=
  (Nat.ceil_le).1 (le_refl (Nat.ceil x))

/-- All off-root budgets in the auxiliary data are proved from expansion,
not chosen from a selected subset of parity states. -/
def protectedCycleFamily
    (κ : ℝ) (hκ : 0 < κ) (hExp : HasExpansion G Finset.univ κ)
    (W : Finset G.Vertex) (hW : ConnectedRegion G W)
    (w : G.Vertex) (hw : w ∈ W)
    (F : Finset G.CycleWord) (D : ℕ)
    (hL : ∀ C ∈ F, BoundaryDecay.Cycle.length C ≤ D)
    (hc : ∀ C ∈ F, ∀ v ∈ Cycle.vertices C, G.degree v = 3)
    (hdis : ∀ C ∈ F, ∀ E ∈ F, C ≠ E → Disjoint (Cycle.vertices C) (Cycle.vertices E))
    (havoid : ∀ C ∈ F, Disjoint (Cycle.vertices C) W)
    (hroom : 2 * (D : ℝ) + (2 * (D : ℝ)) / κ < G.vertexCount)
    (hlarge : (2 * (D : ℝ)) / κ < W.card) : RootedFamily G G.CycleWord where
  family := F
  region := Cycle.vertices
  root := w
  cutBound := D
  singleBudget := Nat.ceil ((D : ℝ) / κ)
  jointBudget := Nat.ceil ((2 * (D : ℝ)) / κ)
  connected := fun C _ => cycle_vertices_connected G C
  disjoint := hdis
  root_avoids := fun C hC hwC => Finset.disjoint_left.1 (havoid C hC) hwC hw
  cut_le := fun C hC => (cycle_cut_le_length G C (hc C hC)).trans (hL C hC)
  single_le := by
    intro C hC
    have horder : (Cycle.vertices C).card ≤ D := by
      simpa only [← BoundaryDecay.Cycle.length_eq_vertices_card] using hL C hC
    have hcut := (cycle_cut_le_length G C (hc C hC)).trans (hL C hC)
    have hWS : W ⊆ (Cycle.vertices C)ᶜ := by
      intro v hv
      exact Finset.mem_compl.2 fun hvC => Finset.disjoint_left.1 (havoid C hC) hvC hv
    have hd : (D : ℝ) / κ ≤ (2 * (D : ℝ)) / κ := by
      apply div_le_div_of_nonneg_right _ hκ.le
      have hn := Nat.cast_nonneg (α := ℝ) D
      linarith
    have hn := Nat.cast_nonneg (α := ℝ) D
    have hb := root_small_bound_of_budget G κ hκ hExp (Cycle.vertices C) W D
      horder hcut (by linarith) hW hWS (hd.trans_lt hlarge) w hw
    have hf := hb.trans (real_le_natCeil ((D : ℝ) / κ))
    exact_mod_cast hf
  joint_le := by
    intro C hC E hE hne
    have hd := hdis C hC E hE hne
    have horder : (Cycle.vertices C ∪ Cycle.vertices E).card ≤ 2 * D := by
      rw [Finset.card_union_of_disjoint hd,
        ← BoundaryDecay.Cycle.length_eq_vertices_card,
        ← BoundaryDecay.Cycle.length_eq_vertices_card]
      have h1 := hL C hC
      have h2 := hL E hE
      omega
    have hcut : cutSize G (Cycle.vertices C ∪ Cycle.vertices E) ≤ 2 * D := by
      have h := two_cycle_cut_le G hd (hc C hC) (hc E hE)
      have h1 := hL C hC
      have h2 := hL E hE
      omega
    have hWS : W ⊆ (Cycle.vertices C ∪ Cycle.vertices E)ᶜ := by
      intro v hv
      apply Finset.mem_compl.2
      intro h
      rcases Finset.mem_union.1 h with h | h
      · exact Finset.disjoint_left.1 (havoid C hC) h hv
      · exact Finset.disjoint_left.1 (havoid E hE) h hv
    have hroom' : ((2 * D : ℕ) : ℝ) + ((2 * D : ℕ) : ℝ) / κ < G.vertexCount := by
      simpa only [Nat.cast_mul, Nat.cast_ofNat] using hroom
    have hlarge' : ((2 * D : ℕ) : ℝ) / κ < W.card := by
      simpa only [Nat.cast_mul, Nat.cast_ofNat] using hlarge
    have hb := root_small_bound_of_budget G κ hκ hExp
      (Cycle.vertices C ∪ Cycle.vertices E) W (2 * D) horder hcut hroom' hW hWS
      hlarge' w hw
    have hb' : ((offRootVertices G (Cycle.vertices C ∪ Cycle.vertices E)ᶜ w).card : ℝ)
        ≤ (2 * (D : ℝ)) / κ := by
      simpa only [Nat.cast_mul, Nat.cast_ofNat] using hb
    exact_mod_cast hb'.trans (real_le_natCeil ((2 * (D : ℝ)) / κ))



/-- The complete finite MANY bound from actual expansion, short-cycle
packing, and a connected protector. No supplied conflict graph remains. -/
theorem forest_fraction_le_protected_cycle_bound (hG : G.IsConnected)
    (κ : ℝ) (hκ : 0 < κ) (hExp : HasExpansion G Finset.univ κ)
    (U W : Finset G.Vertex) (hW : ConnectedRegion G W)
    (F : Finset G.CycleWord) (hFne : F.Nonempty) (D : ℕ)
    (hFU : ∀ C ∈ F, Cycle.vertices C ⊆ U)
    (hL : ∀ C ∈ F, BoundaryDecay.Cycle.length C ≤ D)
    (hc : ∀ C ∈ F, ∀ v ∈ Cycle.vertices C, G.degree v = 3)
    (hdis : ∀ C ∈ F, ∀ E ∈ F, C ≠ E → Disjoint (Cycle.vertices C) (Cycle.vertices E))
    (havoid : ∀ C ∈ F, Disjoint (Cycle.vertices C) W)
    (hroom : 2 * (D : ℝ) + (2 * (D : ℝ)) / κ < G.vertexCount)
    (hlarge : (2 * (D : ℝ)) / κ < W.card) :
    G.originalForestFraction U ≤
      (2 : ℝ) ^ D * (manyCycleConflictBound κ D + 1) / F.card := by
  obtain ⟨w, hw⟩ := hW.1
  let P := protectedCycleFamily G κ hκ hExp W hW w hw F D hL hc hdis havoid hroom hlarge
  exact forest_fraction_le_conflict_bound hG U F hFne hFU D
    (manyCycleConflictBound κ D) hL hc w (fun C hC => P.root_avoids C hC)
    P.Conflict P.conflict_symmetric (fun C hC => P.conflict_degree_le hG C hC)
    (fun C hC E hE hne hn => P.nonconflict_component_identity hG C E hC hE hne hn)

/-- The SAME geometric theorem on the complete boundary-average law.
Expansion and protector are properties of the literal apex graph, not a
spectral surrogate. Apex degree is absent from the support estimates. -/
theorem boundaryAverage_le_protected_cycle_bound
    (H : PhysicalGraph) (hH : H.IsConnected) (p₀ : CorePin H)
    (hmin : ∀ v, 2 ≤ H.degree v) (hmax : ∀ v, H.degree v ≤ 3)
    (κ : ℝ) (hκ : 0 < κ)
    (hExp : HasExpansion (coreApexGraph H) Finset.univ κ)
    (W : Finset (coreApexGraph H).Vertex)
    (hW : ConnectedRegion (coreApexGraph H) W)
    (F : Finset (coreApexGraph H).CycleWord) (hFne : F.Nonempty) (D : ℕ)
    (hFU : ∀ C ∈ F, Cycle.vertices C ⊆ coreApexInterior H)
    (hL : ∀ C ∈ F, BoundaryDecay.Cycle.length C ≤ D)
    (hdis : ∀ C ∈ F, ∀ E ∈ F, C ≠ E → Disjoint (Cycle.vertices C) (Cycle.vertices E))
    (havoid : ∀ C ∈ F, Disjoint (Cycle.vertices C) W)
    (hroom : 2 * (D : ℝ) + (2 * (D : ℝ)) / κ < (coreApexGraph H).vertexCount)
    (hlarge : (2 * (D : ℝ)) / κ < W.card) :
    coreBoundaryAverage H ≤
      (2 : ℝ) ^ D * (manyCycleConflictBound κ D + 1) / F.card := by
  rw [coreBoundaryAverage_eq_physical_fraction]
  exact forest_fraction_le_protected_cycle_bound (coreApexGraph H)
    (coreApex_connected H hH p₀) κ hκ hExp (coreApexInterior H) W hW F hFne D
    hFU hL
    (fun C hC v hv => coreApex_ordinary_cubic H hmin hmax v (hFU C hC hv))
    hdis havoid hroom hlarge

end Erdos1016.CycleSupply
