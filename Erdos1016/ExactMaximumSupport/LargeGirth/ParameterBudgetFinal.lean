import Erdos1016.ExactMaximumSupport.LargeGirth.ParameterBudgetChoices

set_option autoImplicit false
set_option maxHeartbeats 1500000

/-!
# Derived finite budgets for the graph contradiction

The theorem constructs every scalar premise from the explicit choices.
Its remaining premises are the actual vertex ledger and proved packing sizes.
-/
noncomputable section
open Filter
open scoped Topology
namespace Erdos1016.ExactMaximumSupport.LargeGirth.ParameterBudget

/-- These are conclusions of `eventually_budgets`, not additional analytic assumptions. -/
structure FiniteBudgets (C x : ℝ) (D d v deleted lowDeleted : ℕ) : Prop where
  large_girth : 8 ≤ D
  cutoff_ge : D ≤ cutoff x
  depth_pos : 1 ≤ parallelDepth x
  link_geometry : 2*(parallelDepth x+2*(D/8)) ≤ D
  trace_pos : 0 < traceStart x
  trace_interval : traceStart x ≤ halfCutoff x+1
  cutoff_pos : 4 ≤ cutoff x
  radius_pos : 0 < D/2
  radius_girth : 2*(D/2) ≤ D
  order_pos : 0 < v
  deficit_lt : 3*(deleted : ℝ) < v
  trace_main : 3*(deleted : ℝ)*(halfCutoff x : ℝ)/v ≤ 1/200
  trace_error : 3*(v : ℝ)/(2 : ℝ)^traceStart x ≤ 1/200
  collision : (9/4 : ℝ)*(cutoff x : ℝ)^2*(1/2 : ℝ)^(D/2) ≤ 1/100
  trace_log : 123 ≤ Real.log (((halfCutoff x+1 : ℕ) : ℝ)/traceStart x)
  joined_load : (cutoff x : ℝ)*((3/2 : ℝ)*cutoff x*(1/2 : ℝ)^(D/2)) ≤ 1/2
  link_load : (2 : ℝ)^(1+2*(cutoff x : ℝ)/(parallelDepth x+1)+
    (3*(2 : ℝ)^parallelDepth x+1)+578*((cutoff x : ℝ)/D)^2)*cutoff x*cutoff x*
    ((3/2 : ℝ)*cutoff x*(1/2 : ℝ)^(D/2)) ≤ 1/2
  clean_chain : (((cutoff x+lowDeleted+2)*blockSpan x : ℕ) : ℝ)*(3/2 : ℝ)*
    (cutoff x : ℝ)^3*(1/2 : ℝ)^(D/2) ≤ 8
  block_width : 8*(cutoff x)^2 ≤ (blockSpan x-1)*(D+1)
  small_girth : 3 ≤ d+1
  small_log : C*Real.logb 2 ((cutoff x : ℝ)+2) ≤ d+1

/-- Actual packing sizes and the cubic vertex ledger imply all finite budgets. -/
theorem eventually_budgets (D₀ : ℕ) (hD₀ : 0<D₀) (C : ℝ) (hC : 0≤C) :
    ∀ᶠ (x : ℝ) in atTop,
    let d := GirthRaiseBounds.scale D₀ (scaleIndex D₀ (Real.sqrt x))
    let D := GirthRaiseBounds.scale D₀ (scaleIndex D₀ (x/16))
    ∀ p S T v : ℕ, (p : ℝ)≤3*x →
      S+1≤2^(deletionExponent D) → T+1≤2^(deletionExponent d) →
      (v : ℝ)+p+S+2=2*(2 : ℝ)^x →
      FiniteBudgets C x D d v (p+S) T := by
  filter_upwards [eventually_scale_choices D₀ hD₀, eventually_deletion_exponents,
    eventually_link_geometry,eventually_link_budget,eventually_load_budgets,
    eventually_clean_chain_budget,eventually_supply_budgets,eventually_removed_plus_two,
    eventually_low_girth_budget C hC,eventually_trace_log_budget,eventually_cutoff_bounds,
    eventually_ge_atTop (1 : ℝ)] with x hscale hexp hgeom hlink hload hchain hsupply
      hremoved hlow hlog hcut hx
  dsimp only
  let d := GirthRaiseBounds.scale D₀ (scaleIndex D₀ (Real.sqrt x))
  let D := GirthRaiseBounds.scale D₀ (scaleIndex D₀ (x/16))
  change _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ at hscale
  have hdpos : 0<d := by dsimp [d,GirthRaiseBounds.scale]; positivity
  have hDpos : 0<D := by dsimp [D,GirthRaiseBounds.scale]; positivity
  have hdlo : Real.sqrt x ≤ d := hscale.2.1
  have hdhi : (d : ℝ)≤2*Real.sqrt x := hscale.2.2.1.le
  have hDlo : x/16≤D := hscale.2.2.2.1
  have hDhi : (D : ℝ)≤x/8 := hscale.2.2.2.2.1.le
  intro p S T v hp hS hT hv
  have hSr : (S : ℝ)≤(2 : ℝ)^(x/3) :=
    packing_size_to_real S (deletionExponent D) (x/3) hS (hexp.2 D hDpos hDhi)
  have hTr : (T : ℝ)≤(2 : ℝ)^(x/128) :=
    packing_size_to_real T (deletionExponent d) (x/128) hT (hexp.1 d hdpos hdhi)
  have hvlo : (2 : ℝ)^x≤v := by linarith
  have hvhi : (v : ℝ)≤(2 : ℝ)^(x+1) := by
    rw [Real.rpow_add (by norm_num),Real.rpow_one]
    have hp0 : (0 : ℝ)≤p := Nat.cast_nonneg p
    have hS0 : (0 : ℝ)≤S := Nat.cast_nonneg S
    linarith
  obtain ⟨h8,hDL,ht,hlinkgeom,hs,hshort⟩ := hgeom D hDlo hDhi
  obtain ⟨hn,hM,hMK,hdef,hmain,herr⟩ := hsupply p S v hp hSr hvlo hvhi
  obtain ⟨hcollision,hjoined,hη⟩ := hload D hDlo
  refine {
    large_girth := h8
    cutoff_ge := hDL
    depth_pos := ht
    link_geometry := hlinkgeom
    trace_pos := hM
    trace_interval := hMK
    cutoff_pos := hcut.1
    radius_pos := hs
    radius_girth := hshort
    order_pos := hn
    deficit_lt := hdef
    trace_main := hmain
    trace_error := herr
    collision := hcollision
    trace_log := hlog
    joined_load := hjoined
    link_load := hη _ (hlink D hDlo)
    clean_chain := hchain D T hDlo hTr
    block_width := blockSpan_size x hx D hDlo hcut.2.1
    small_girth := by have hh := hscale.2.2.2.2.2; omega
    small_log := ?_ }
  have hh : (d : ℝ)≤((d+1 : ℕ) : ℝ) := by push_cast; linarith
  simpa only [Nat.cast_add,Nat.cast_one] using hlow.trans (hdlo.trans hh)

/-- The same derived package is eventual in the actual natural cycle rank. -/
theorem exists_rank_threshold (D₀ : ℕ) (hD₀ : 0<D₀) (C : ℝ) (hC : 0≤C) :
    ∃ R : ℕ, ∀ r : ℕ, R≤r →
    let x := Real.logb 2 (r : ℝ)
    let d := GirthRaiseBounds.scale D₀ (scaleIndex D₀ (Real.sqrt x))
    let D := GirthRaiseBounds.scale D₀ (scaleIndex D₀ (x/16))
    ∀ p S T v : ℕ, (p : ℝ)≤3*x →
      S+1≤2^(deletionExponent D) → T+1≤2^(deletionExponent d) →
      (v : ℝ)+p+S+2=2*(2 : ℝ)^x →
      FiniteBudgets C x D d v (p+S) T := by
  have ht : Tendsto (fun r : ℕ => Real.logb 2 (r : ℝ)) atTop atTop :=
    (Real.tendsto_logb_atTop (by norm_num)).comp tendsto_natCast_atTop_atTop
  exact eventually_atTop.mp (ht.eventually (eventually_budgets D₀ hD₀ C hC))

end Erdos1016.ExactMaximumSupport.LargeGirth.ParameterBudget
