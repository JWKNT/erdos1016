import Erdos1016.ExactMaximum.PoleMatchings
import Erdos1016.ExactMaximumSupport.NetworkFourCycle
import Erdos1016.ExactMaximumSupport.NetworkMultiplicity

set_option autoImplicit false
set_option maxHeartbeats 1500000

/-!
# Exact physical matching counts between two thin layers

The two matching patterns retain every choice of physical labels.
No degree, connectedness, or simplicity hypothesis is needed.
-/
noncomputable section
namespace Erdos1016.ExactMaximumSupport.LayerMatchingCount
open BoundaryTrace BoundaryTrace.Network

local instance matchingDecidable (p : Prop) : Decidable p := Classical.propDecidable p

variable {V E : Type*} [Fintype E] (N : Network V E)

/-- Two selected labels incident at a degree-one vertex are equal. -/
theorem selected_eq_of_degree_one {m : N.Word} {v : V} (hdeg : N.deg m v = 1)
    {e f : E} (he : m e ≠ 0) (hf : m f ≠ 0)
    (hev : N.src e = v ∨ N.dst e = v) (hfv : N.src f = v ∨ N.dst f = v) : e = f := by
  have hcard : (Finset.univ.filter fun g =>
      m g ≠ 0 ∧ (N.src g = v ∨ N.dst g = v)).card ≤ 1 := hdeg.le
  exact Finset.card_le_one.mp hcard e
    (by simp only [Finset.mem_filter, Finset.mem_univ, true_and]; exact ⟨he,hev⟩) f
    (by simp only [Finset.mem_filter, Finset.mem_univ, true_and]; exact ⟨hf,hfv⟩)

/-- Distinct unit labels have exactly their two-element support. -/
theorem pair_selected_iff {e f g : E} (hef : e ≠ f) :
    (unitWord e + unitWord f : E → Bit) g ≠ 0 ↔ g = e ∨ g = f := by
  by_cases hge : g = e
  · subst g; simp [Pi.add_apply, unitWord_apply, hef.symm]
  by_cases hgf : g = f
  · subst g; simp [Pi.add_apply, unitWord_apply, hef]
  simp [Pi.add_apply, unitWord_apply, hge, hgf, Ne.symm hge, Ne.symm hgf]

theorem pair_matching {s a b c d : V} {l : ℕ} {e f : E}
    (hab : a ≠ b) (hac : a ≠ c) (had : a ≠ d)
    (hbc : b ≠ c) (hbd : b ≠ d) (hcd : c ≠ d)
    (hleft : ∀ v, N.graph.dist s v = l ↔ v = a ∨ v = b)
    (hright : ∀ v, N.graph.dist s v = l + 1 ↔ v = c ∨ v = d)
    (he : N.Joins e a c) (hf : N.Joins f b d) :
    N.IsLayerMatching s l (unitWord e + unitWord f) := by
  have hef := NetworkFourCycle.edges_ne_of_fresh N he hf hab.symm hbc
  have hdis : ∀ g, (unitWord e : E → Bit) g ≠ 0 → (unitWord f : E → Bit) g = 0 := by
    intro g hg
    have heg : e = g := by by_contra h; simp [unitWord_apply,h] at hg
    subst g
    simp [unitWord_apply,hef.symm]
  have ha := (hleft a).mpr (Or.inl rfl)
  have hb := (hleft b).mpr (Or.inr rfl)
  have hc := (hright c).mpr (Or.inl rfl)
  have hd := (hright d).mpr (Or.inr rfl)
  constructor
  · intro g hg
    rcases (pair_selected_iff hef).mp hg with rfl | rfl
    · rcases he with ⟨h1,h2⟩ | ⟨h1,h2⟩
      · exact Or.inl ⟨h1 ▸ ha,h2 ▸ hc⟩
      · exact Or.inr ⟨h1 ▸ hc,h2 ▸ ha⟩
    · rcases hf with ⟨h1,h2⟩ | ⟨h1,h2⟩
      · exact Or.inl ⟨h1 ▸ hb,h2 ▸ hd⟩
      · exact Or.inr ⟨h1 ▸ hd,h2 ▸ hb⟩
  · intro v hv
    rw [N.deg_add_of_disjoint hdis]
    rcases hv with hv | hv
    · rcases (hleft v).mp hv with rfl | rfl
      · rw [N.deg_unitWord_eq_one he.at_left,
          N.deg_unitWord_of_joins hf hab had]
      · rw [N.deg_unitWord_of_joins he hab.symm hbc,
          N.deg_unitWord_eq_one hf.at_left]
    · rcases (hright v).mp hv with rfl | rfl
      · rw [N.deg_unitWord_eq_one he.at_right,
          N.deg_unitWord_of_joins hf hbc.symm hcd]
      · rw [N.deg_unitWord_of_joins he had.symm hcd.symm,
          N.deg_unitWord_eq_one hf.at_right]

omit [Fintype E] in
/-- An incident layer label joins its lower endpoint to the upper layer. -/
theorem joins_right_of_layer_edge {s u c d : V} {l : ℕ} {e : E}
    (hu : N.graph.dist s u = l) (he : N.IsLayerEdge s l e)
    (hv : N.src e = u ∨ N.dst e = u)
    (hright : ∀ v, N.graph.dist s v = l+1 ↔ v=c ∨ v=d) :
    N.Joins e u c ∨ N.Joins e u d := by
  obtain ⟨w,hw⟩ := N.exists_joins hv
  have hwl : N.graph.dist s w = l+1 := by
    rcases hw with ⟨h1,h2⟩ | ⟨h1,h2⟩ <;>
      rcases he with ⟨he1,he2⟩ | ⟨he1,he2⟩ <;>
      simp only [h1,h2] at he1 he2 <;> omega
  rcases (hright w).mp hwl with rfl | rfl
  · exact Or.inl hw
  · exact Or.inr hw

/-- A matching is determined by its selected labels at the two lower vertices. -/
theorem matching_eq_pair {s a b : V} {l : ℕ} {m : N.Word} {e f : E}
    (hm : N.IsLayerMatching s l m)
    (hleft : ∀ v, N.graph.dist s v = l ↔ v = a ∨ v = b)
    (hef : e ≠ f) (he : m e ≠ 0) (hf : m f ≠ 0)
    (hea : N.src e = a ∨ N.dst e = a) (hfb : N.src f = b ∨ N.dst f = b) :
    m = unitWord e + unitWord f := by
  have ha := hm.2 a (Or.inl ((hleft a).mpr (Or.inl rfl)))
  have hb := hm.2 b (Or.inl ((hleft b).mpr (Or.inr rfl)))
  apply word_eq_of_support
  · intro g hg
    have hgLayer := hm.1 g hg
    have hor : (N.src g = a ∨ N.dst g = a) ∨ (N.src g = b ∨ N.dst g = b) := by
      rcases hgLayer with ⟨h1,_⟩ | ⟨_,h2⟩
      · rcases (hleft _).mp h1 with h | h
        · exact Or.inl (Or.inl h)
        · exact Or.inr (Or.inl h)
      · rcases (hleft _).mp h2 with h | h
        · exact Or.inl (Or.inr h)
        · exact Or.inr (Or.inr h)
    apply (pair_selected_iff hef).mpr
    rcases hor with hga | hgb
    · exact Or.inl (selected_eq_of_degree_one N ha hg he hga hea)
    · exact Or.inr (selected_eq_of_degree_one N hb hg hf hgb hfb)
  · intro g hg
    rcases (pair_selected_iff hef).mp hg with rfl | rfl
    · exact he
    · exact hf

/-- Physical label choices for the two possible matching patterns. -/
abbrev Choice (a b c d : V) :=
  ({e : E // N.Joins e a c} × {f : E // N.Joins f b d}) ⊕
    ({e : E // N.Joins e a d} × {f : E // N.Joins f b c})

def firstLabel {a b c d : V} : Choice N a b c d → E
  | Sum.inl q => q.1.val
  | Sum.inr q => q.1.val

def secondLabel {a b c d : V} : Choice N a b c d → E
  | Sum.inl q => q.2.val
  | Sum.inr q => q.2.val

def choiceWord {a b c d : V} (q : Choice N a b c d) : N.Word :=
  unitWord (firstLabel N q) + unitWord (secondLabel N q)

omit [Fintype E] in
theorem choice_labels_ne {a b c d : V} (hab : a ≠ b) (hbc : b ≠ c) (hbd : b ≠ d)
    (q : Choice N a b c d) : firstLabel N q ≠ secondLabel N q := by
  cases q with
  | inl q => exact NetworkFourCycle.edges_ne_of_fresh N q.1.property q.2.property hab.symm hbc
  | inr q => exact NetworkFourCycle.edges_ne_of_fresh N q.1.property q.2.property hab.symm hbd

omit [Fintype E] in
theorem choice_first_incident {a b c d : V} (q : Choice N a b c d) :
    N.src (firstLabel N q) = a ∨ N.dst (firstLabel N q) = a := by
  cases q with
  | inl q => exact q.1.property.at_left
  | inr q => exact q.1.property.at_left

omit [Fintype E] in
theorem choice_second_incident {a b c d : V} (q : Choice N a b c d) :
    N.src (secondLabel N q) = b ∨ N.dst (secondLabel N q) = b := by
  cases q with
  | inl q => exact q.2.property.at_left
  | inr q => exact q.2.property.at_left

section FourVertices
variable {s a b c d : V} {l : ℕ}
variable (hab : a ≠ b) (hac : a ≠ c) (had : a ≠ d)
  (hbc : b ≠ c) (hbd : b ≠ d) (hcd : c ≠ d)
  (hleft : ∀ v, N.graph.dist s v = l ↔ v = a ∨ v = b)
  (hright : ∀ v, N.graph.dist s v = l+1 ↔ v = c ∨ v = d)

include hab hac had hbc hbd hcd hleft hright

theorem choiceWord_matching (q : Choice N a b c d) :
    N.IsLayerMatching s l (choiceWord N q) := by
  cases q with
  | inl q => exact pair_matching N hab hac had hbc hbd hcd hleft hright q.1.property q.2.property
  | inr q =>
    exact pair_matching N hab had hac hbd hbc hcd.symm hleft
      (fun v => (hright v).trans or_comm) q.1.property q.2.property

omit hac had hcd in
/-- Every actual matching has one of the two physical label patterns. -/
theorem choiceWord_surjective (m : N.Word) (hm : N.IsLayerMatching s l m) :
    ∃ q : Choice N a b c d, choiceWord N q = m := by
  have ha := hm.2 a (Or.inl ((hleft a).mpr (Or.inl rfl)))
  have hb := hm.2 b (Or.inl ((hleft b).mpr (Or.inr rfl)))
  have hc := hm.2 c (Or.inr ((hright c).mpr (Or.inl rfl)))
  have hd := hm.2 d (Or.inr ((hright d).mpr (Or.inr rfl)))
  obtain ⟨e,he,hea⟩ := N.exists_edge_of_deg_pos (by omega : 0 < N.deg m a)
  obtain ⟨f,hf,hfb⟩ := N.exists_edge_of_deg_pos (by omega : 0 < N.deg m b)
  have her := joins_right_of_layer_edge N ((hleft a).mpr (Or.inl rfl)) (hm.1 e he) hea hright
  have hfr := joins_right_of_layer_edge N ((hleft b).mpr (Or.inr rfl)) (hm.1 f hf) hfb hright
  rcases her with hec | hed <;> rcases hfr with hfc | hfd
  · have hef := NetworkFourCycle.edges_ne_of_fresh N hec hfc hab.symm hbc
    exact False.elim (hef (selected_eq_of_degree_one N hc he hf hec.at_right hfc.at_right))
  · have hef := NetworkFourCycle.edges_ne_of_fresh N hec hfd hab.symm hbc
    exact ⟨Sum.inl (⟨e,hec⟩,⟨f,hfd⟩),
      (matching_eq_pair N hm hleft hef he hf hea hfb).symm⟩
  · have hef := NetworkFourCycle.edges_ne_of_fresh N hed hfc hab.symm hbd
    exact ⟨Sum.inr (⟨e,hed⟩,⟨f,hfc⟩),
      (matching_eq_pair N hm hleft hef he hf hea hfb).symm⟩
  · have hef := NetworkFourCycle.edges_ne_of_fresh N hed hfd hab.symm hbd
    exact False.elim (hef (selected_eq_of_degree_one N hd he hf hed.at_right hfd.at_right))

/-- Equal matching words retain both physical labels and the matching pattern. -/
theorem choiceWord_injective : Function.Injective (choiceWord N (a:=a) (b:=b) (c:=c) (d:=d)) := by
  intro q q' heq
  have hq := choiceWord_matching N hab hac had hbc hbd hcd hleft hright q
  have hne := choice_labels_ne N hab hbc hbd q
  have hne' := choice_labels_ne N hab hbc hbd q'
  have hfirst : firstLabel N q = firstLabel N q' := by
    apply selected_eq_of_degree_one N (hq.2 a (Or.inl ((hleft a).mpr (Or.inl rfl))))
      ((pair_selected_iff hne).mpr (Or.inl rfl))
    · rw [heq]
      exact (pair_selected_iff hne').mpr (Or.inl rfl)
    · exact choice_first_incident N q
    · exact choice_first_incident N q'
  have hsecond : secondLabel N q = secondLabel N q' := by
    apply selected_eq_of_degree_one N (hq.2 b (Or.inl ((hleft b).mpr (Or.inr rfl))))
      ((pair_selected_iff hne).mpr (Or.inr rfl))
    · rw [heq]
      exact (pair_selected_iff hne').mpr (Or.inr rfl)
    · exact choice_second_incident N q
    · exact choice_second_incident N q'
  cases q with
  | inl q =>
    cases q' with
    | inl q' => exact congrArg Sum.inl (Prod.ext (Subtype.ext hfirst) (Subtype.ext hsecond))
    | inr q' =>
      have hd' : N.Joins q.1.val a d := by
        change q.1.val = q'.1.val at hfirst
        rw [hfirst]
        exact q'.1.property
      exact False.elim (hcd (NetworkMultiplicity.joins_other_unique N q.1.property hd'))
  | inr q =>
    cases q' with
    | inl q' =>
      have hc' : N.Joins q.1.val a c := by
        change q.1.val = q'.1.val at hfirst
        rw [hfirst]
        exact q'.1.property
      exact False.elim (hcd (NetworkMultiplicity.joins_other_unique N hc' q.1.property))
    | inr q' => exact congrArg Sum.inr (Prod.ext (Subtype.ext hfirst) (Subtype.ext hsecond))

/-- The labelled matching patterns are equivalent to actual matching words. -/
def matchingEquiv : Choice N a b c d ≃ {m : N.Word // N.IsLayerMatching s l m} :=
  Equiv.ofBijective
    (fun q => ⟨choiceWord N q,choiceWord_matching N hab hac had hbc hbd hcd hleft hright q⟩)
    ⟨fun q q' h => choiceWord_injective N hab hac had hbc hbd hcd hleft hright
      (congrArg Subtype.val h),
     fun m => by
       obtain ⟨q,hq⟩ := choiceWord_surjective N hab hbc hbd hleft hright m.val m.property
       exact ⟨q,Subtype.ext hq⟩⟩

end FourVertices

/-- Exact permanent formula for two consecutive two-vertex layers. -/
theorem card_layerMatching (s : V) (l : ℕ) (a b c d : V)
    (hab : a ≠ b) (hac : a ≠ c) (had : a ≠ d)
    (hbc : b ≠ c) (hbd : b ≠ d) (hcd : c ≠ d)
    (hleft : ∀ v, N.graph.dist s v = l ↔ v = a ∨ v = b)
    (hright : ∀ v, N.graph.dist s v = l+1 ↔ v = c ∨ v = d) :
    Nat.card {m : N.Word // N.IsLayerMatching s l m} =
      Nat.card {e : E // N.Joins e a c} * Nat.card {e : E // N.Joins e b d} +
        Nat.card {e : E // N.Joins e a d} * Nat.card {e : E // N.Joins e b c} := by
  rw [← Nat.card_congr (matchingEquiv N hab hac had hbc hbd hcd hleft hright)]
  simp only [Choice, Nat.card_sum, Nat.card_prod]

end Erdos1016.ExactMaximumSupport.LayerMatchingCount
