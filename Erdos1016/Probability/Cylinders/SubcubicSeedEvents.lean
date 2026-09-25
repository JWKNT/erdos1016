import Erdos1016.Probability.Cylinders.SeedRegionLaw

set_option autoImplicit false

/-!
# Cycle selection in a subcubic labelled multigraph

For a two-regular even seed, selecting all its edges forces every incident
coordinate to equal the seed. The proof uses actual incidence degrees and
parity, retaining both incidences of a loop and each parallel edge label.
-/

noncomputable section
open scoped BigOperators
namespace Erdos1016.FiniteMultiGraph

local instance subcubicSeedDecidable (p : Prop) : Decidable p := Classical.propDecidable p

theorem boundary_eq_selectedDegree_cast (G : FiniteMultiGraph) (x : G.EdgeWord) (v : G.Vertex) :
    G.boundary x v = (G.selectedDegree x v : F₂) := by
  have binary (a : F₂) : a = 0 ∨ a = 1 := by fin_cases a <;> simp
  change (∑ e, ((if G.src e = v then x e else 0) +
    (if G.dst e = v then x e else 0))) = _
  unfold selectedDegree
  simp only [Finset.card_eq_sum_ones, Finset.sum_filter]
  push_cast
  rw [Finset.sum_add_distrib]
  congr 1 <;> apply Finset.sum_congr rfl <;> intro e he
  all_goals rcases binary (x e) with h | h <;> simp [h]

theorem selectedDegree_mono (G : FiniteMultiGraph) {x y : G.EdgeWord}
    (hsub : ∀ e, x e ≠ 0 → y e ≠ 0) (v : G.Vertex) :
    G.selectedDegree x v ≤ G.selectedDegree y v := by
  unfold selectedDegree
  apply Nat.add_le_add <;> apply Finset.card_le_card <;> intro e he
  all_goals
    rcases Finset.mem_filter.mp he with ⟨hsel, hend⟩
    exact Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr
      ⟨Finset.mem_univ _, hsub e (Finset.mem_filter.mp hsel).2⟩, hend⟩

theorem selectedDegree_le_degree (G : FiniteMultiGraph) (x : G.EdgeWord) (v : G.Vertex) :
    G.selectedDegree x v ≤ G.degree v :=
  G.selectedDegree_mono (fun _ _ => one_ne_zero) v

/-- Equality of incidence degrees under support inclusion means no extra
selected edge can occur at this vertex. -/
theorem incident_coordinate_eq_of_degree_eq (G : FiniteMultiGraph) {x y : G.EdgeWord}
    (hsub : ∀ e, x e ≠ 0 → y e ≠ 0) (v : G.Vertex)
    (hdegree : G.selectedDegree x v = G.selectedDegree y v)
    (e : G.Edge) (he : G.src e = v ∨ G.dst e = v) : x e = y e := by
  let A (z : G.EdgeWord) := (Finset.univ.filter fun e => z e ≠ 0).filter fun e => G.src e = v
  let B (z : G.EdgeWord) := (Finset.univ.filter fun e => z e ≠ 0).filter fun e => G.dst e = v
  have hA : A x ⊆ A y := by
    intro e he
    simp only [A, Finset.mem_filter, Finset.mem_univ, true_and] at he ⊢
    exact ⟨hsub e he.1, he.2⟩
  have hB : B x ⊆ B y := by
    intro e he
    simp only [B, Finset.mem_filter, Finset.mem_univ, true_and] at he ⊢
    exact ⟨hsub e he.1, he.2⟩
  have hcA := Finset.card_le_card hA
  have hcB := Finset.card_le_card hB
  change (A x).card + (B x).card = (A y).card + (B y).card at hdegree
  have heqA : A x = A y := Finset.eq_of_subset_of_card_le hA (by omega)
  have heqB : B x = B y := Finset.eq_of_subset_of_card_le hB (by omega)
  have hiff : x e ≠ 0 ↔ y e ≠ 0 := by
    constructor
    · exact hsub e
    · intro hy
      rcases he with he | he
      · have hm : e ∈ A y := by simp [A, hy, he]
        rw [← heqA] at hm
        exact (Finset.mem_filter.mp (Finset.mem_filter.mp hm).1).2
      · have hm : e ∈ B y := by simp [B, hy, he]
        rw [← heqB] at hm
        exact (Finset.mem_filter.mp (Finset.mem_filter.mp hm).1).2
  have binary (a : F₂) : a = 0 ∨ a = 1 := by fin_cases a <;> simp
  rcases binary (x e) with hx | hx <;> rcases binary (y e) with hy | hy <;> simp_all

/-- In degree at most three, the parity constraint leaves no spare selected
incidence after a two-regular seed has been selected. -/
theorem selectedSeed_iff_incidentSeed (G : FiniteMultiGraph) (U : Finset G.Vertex)
    (seed : G.internalCycleSpace U)
    (hseed : ∀ v ∈ U, G.selectedDegree seed.1.1 v = 2)
    (hdegree : ∀ v ∈ U, G.degree v ≤ 3) (x : G.CycleSpace) :
    G.SelectedSeed seed.1 x ↔ G.IncidentSeed U seed x := by
  constructor
  · intro hselected e he
    obtain ⟨v, hv, he⟩ : ∃ v ∈ U, G.src e = v ∨ G.dst e = v := by
      rcases he with he | he
      · exact ⟨G.src e, he, Or.inl rfl⟩
      · exact ⟨G.dst e, he, Or.inr rfl⟩
    have hlow : 2 ≤ G.selectedDegree x.1 v := by
      simpa only [hseed v hv] using G.selectedDegree_mono hselected v
    have hupp : G.selectedDegree x.1 v ≤ 3 := (G.selectedDegree_le_degree x.1 v).trans (hdegree v hv)
    have heven : 2 ∣ G.selectedDegree x.1 v := by
      apply (ZMod.natCast_zmod_eq_zero_iff_dvd _ 2).mp
      rw [← G.boundary_eq_selectedDegree_cast]
      exact congrFun x.2 v
    have hxdeg : G.selectedDegree x.1 v = 2 := by omega
    exact (G.incident_coordinate_eq_of_degree_eq hselected v ((hseed v hv).trans hxdeg.symm) e he).symm
  · intro hincident e he
    have hin : e ∈ G.internalEdges U := by
      exact Classical.byContradiction (fun hn => he (seed.2 e hn))
    rw [hincident e (Or.inl (Finset.mem_filter.mp hin).2.1)]
    exact he

/-- Every selected edge of the seed remains selected under its incident event. -/
theorem incidentSeed_selectedSeed (G : FiniteMultiGraph) (U : Finset G.Vertex)
    (seed : G.internalCycleSpace U) (x : G.CycleSpace) (hx : G.IncidentSeed U seed x) :
    G.SelectedSeed seed.1 x := by
  intro e he
  have hin : e ∈ G.internalEdges U := Classical.byContradiction (fun hn => he (seed.2 e hn))
  rw [hx e (Or.inl (Finset.mem_filter.mp hin).2.1)]
  exact he

/-- Under an incident event, its region is closed under selected adjacency. -/
theorem incidentSeed_support_closed (G : FiniteMultiGraph) (U : Finset G.Vertex)
    (seed : G.internalCycleSpace U) (x : G.CycleSpace) (hx : G.IncidentSeed U seed x)
    {u v : G.Vertex} (hu : u ∈ U) (huv : (G.selectedGraph x.1).Adj u v) : v ∈ U := by
  rcases huv with ⟨hne, e, he, h | h⟩
  · have hs : seed.1.1 e ≠ 0 := by rwa [hx e (Or.inl (h.1.symm ▸ hu))] at he
    have hin : e ∈ G.internalEdges U := Classical.byContradiction (fun hn => hs (seed.2 e hn))
    exact h.2 ▸ (Finset.mem_filter.mp hin).2.2
  · have hs : seed.1.1 e ≠ 0 := by rwa [hx e (Or.inr (h.2.symm ▸ hu))] at he
    have hin : e ∈ G.internalEdges U := Classical.byContradiction (fun hn => hs (seed.2 e hn))
    exact h.1 ▸ (Finset.mem_filter.mp hin).2.1

/-- A connected seed overlapping a second incident component lies wholly
inside that component. -/
theorem incidentSeed_subset_of_overlap (G : FiniteMultiGraph) (U V : Finset G.Vertex)
    (seed : G.internalCycleSpace U) (seed' : G.internalCycleSpace V)
    (hconn : ((G.selectedGraph seed.1.1).induce (↑U : Set G.Vertex)).Connected)
    (x : G.CycleSpace) (hx : G.IncidentSeed U seed x) (hx' : G.IncidentSeed V seed' x)
    (v₀ : G.Vertex) (hv₀ : v₀ ∈ U) (hv₀' : v₀ ∈ V) : U ⊆ V := by
  have hselected := G.incidentSeed_selectedSeed U seed x hx
  intro v hv
  obtain ⟨p⟩ := hconn.preconnected ⟨v₀, hv₀⟩ ⟨v, hv⟩
  have hwalk : ∀ {a b : (↑U : Set G.Vertex)},
      ((G.selectedGraph seed.1.1).induce (↑U : Set G.Vertex)).Walk a b → a.1 ∈ V → b.1 ∈ V := by
    intro a b p
    induction p with
    | nil => exact id
    | @cons a b c hab p ih =>
        intro ha
        apply ih
        apply G.incidentSeed_support_closed V seed' x hx' ha
        rcases hab with ⟨hne, e, he, hend⟩
        exact ⟨hne, e, hselected e he, hend⟩
  exact hwalk p hv₀'

/-- Distinct connected seed components cannot coexist when they overlap. -/
theorem incidentSeed_eq_of_joint_overlap (G : FiniteMultiGraph) (U V : Finset G.Vertex)
    (seed : G.internalCycleSpace U) (seed' : G.internalCycleSpace V)
    (hU : ((G.selectedGraph seed.1.1).induce (↑U : Set G.Vertex)).Connected)
    (hV : ((G.selectedGraph seed'.1.1).induce (↑V : Set G.Vertex)).Connected)
    (x : G.CycleSpace) (hx : G.IncidentSeed U seed x) (hx' : G.IncidentSeed V seed' x)
    (v₀ : G.Vertex) (hv₀ : v₀ ∈ U) (hv₀' : v₀ ∈ V) : seed.1 = seed'.1 := by
  have hUV := G.incidentSeed_subset_of_overlap U V seed seed' hU x hx hx' v₀ hv₀ hv₀'
  have hVU := G.incidentSeed_subset_of_overlap V U seed' seed hV x hx' hx v₀ hv₀' hv₀
  apply Subtype.ext
  funext e
  by_cases hs : G.src e ∈ U
  · exact (hx e (Or.inl hs)).symm.trans (hx' e (Or.inl (hUV hs)))
  · have hu : e ∉ G.internalEdges U := by simp [internalEdges, hs]
    have hv : e ∉ G.internalEdges V := by
      simp only [internalEdges, Finset.mem_filter, Finset.mem_univ, true_and]
      exact fun h => hs (hVU h.1)
    rw [seed.2 e hu, seed'.2 e hv]

/-- Overlapping distinct cycles are incompatible in a subcubic ambient
multigraph, with loops and parallel labels included. -/
theorem selectedSeed_overlap_incompatible (G : FiniteMultiGraph) (U V : Finset G.Vertex)
    (seed : G.internalCycleSpace U) (seed' : G.internalCycleSpace V)
    (hU : ((G.selectedGraph seed.1.1).induce (↑U : Set G.Vertex)).Connected)
    (hV : ((G.selectedGraph seed'.1.1).induce (↑V : Set G.Vertex)).Connected)
    (hdU : ∀ v ∈ U, G.selectedDegree seed.1.1 v = 2)
    (hdV : ∀ v ∈ V, G.selectedDegree seed'.1.1 v = 2)
    (hdegreeU : ∀ v ∈ U, G.degree v ≤ 3) (hdegreeV : ∀ v ∈ V, G.degree v ≤ 3)
    (hne : seed.1 ≠ seed'.1) (hoverlap : ¬ Disjoint U V) (x : G.CycleSpace) :
    ¬ (G.SelectedSeed seed.1 x ∧ G.SelectedSeed seed'.1 x) := by
  rintro ⟨hx, hx'⟩
  obtain ⟨v₀, hv₀, hv₀'⟩ := Finset.not_disjoint_iff.mp hoverlap
  apply hne
  exact G.incidentSeed_eq_of_joint_overlap U V seed seed' hU hV x
    ((G.selectedSeed_iff_incidentSeed U seed hdU hdegreeU x).mp hx)
    ((G.selectedSeed_iff_incidentSeed V seed' hdV hdegreeV x).mp hx') v₀ hv₀ hv₀'

end Erdos1016.FiniteMultiGraph
