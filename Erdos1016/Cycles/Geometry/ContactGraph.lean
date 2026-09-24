import Erdos1016.Nonbacktracking.Girth.CollisionGeometry
import Mathlib.Combinatorics.SimpleGraph.Metric

set_option autoImplicit false

/-!
# Short repeated labels in a connected boundary-contact graph

The boundary tokens of a small complementary component are close to every
vertex. Joining tokens whose bases have distance at most `2r+1` therefore
gives a connected graph. If there are only `K` labels and some label repeats,
two equally labelled tokens can be joined in at most `K` steps. This is the
contact-graph step of the manuscript's Lemma 5.1, before the component is
known to be a tree.
-/

noncomputable section

namespace Erdos1016.Proof.ConditionalContactGraph

open SimpleGraph
open Erdos1016.Proof.CyclicRunCollisionGeometry

/-- In a connected graph labelled by a finite type, a repeated label occurs
at distance at most the number of labels. No bound on graph order is needed. -/
theorem exists_close_equal_labels
    {V ι : Type*} [Fintype ι] (H : SimpleGraph V) (hH : H.Connected)
    (label : V → ι) (hnot : ¬ Function.Injective label) :
    ∃ a b, a ≠ b ∧ label a = label b ∧ H.dist a b ≤ Fintype.card ι := by
  classical
  have hex : ∃ n : ℕ, ∃ a b, a ≠ b ∧ label a = label b ∧ H.dist a b = n := by
    obtain ⟨a, b, hab, hne⟩ := Function.not_injective_iff.mp hnot
    exact ⟨H.dist a b, a, b, hne, hab, rfl⟩
  let n := Nat.find hex
  obtain ⟨a, b, hab, hlabel, hdist⟩ := Nat.find_spec hex
  obtain ⟨p, hp, hlen⟩ := hH.exists_path_of_dist a b
  have hpn : p.length = n := hlen.trans hdist
  let f : Fin n → ι := fun i => label (p.getVert i.val)
  have hf : Function.Injective f := by
    intro i j hij
    have hordered : ∀ i j : Fin n, i.val < j.val → f i = f j → False := by
      intro i j hlt heq
      have hvertices : p.getVert i.val ≠ p.getVert j.val := by
        intro he
        have := hp.getVert_injOn (by simp only [Set.mem_setOf_eq]; omega)
          (by simp only [Set.mem_setOf_eq]; omega) he
        omega
      let seg₀ := (p.drop i.val).take (j.val - i.val)
      have hend : (p.drop i.val).getVert (j.val - i.val) = p.getVert j.val := by
        rw [getVert_drop_at_index]
        congr 1
        omega
      let seg : H.Walk (p.getVert i.val) (p.getVert j.val) := seg₀.copy rfl hend
      have hseg : seg.length = j.val - i.val := by
        simp only [seg, Walk.length_copy, seg₀, take_length_at_index,
          drop_length_at_index, hpn]
        omega
      have hmin : n ≤ H.dist (p.getVert i.val) (p.getVert j.val) :=
        Nat.find_min' hex ⟨p.getVert i.val, p.getVert j.val, hvertices, heq, rfl⟩
      have hupper := SimpleGraph.dist_le seg
      rw [hseg] at hupper
      omega
    apply Fin.ext
    by_contra hne
    rcases lt_or_gt_of_ne hne with hlt | hgt
    · exact hordered i j hlt hij
    · exact hordered j i hgt hij.symm
  have hcard : n ≤ Fintype.card ι := by
    simpa using Fintype.card_le_of_injective f hf
  exact ⟨a, b, hab, hlabel, hdist ▸ hcard⟩

/-- Tokens are adjacent when their bases are at distance at most `2r+1`.
Distinct tokens based at the same vertex are adjacent, as required when a
vertex has more than one outgoing incidence. -/
def contactGraph {V T : Type*} (H : SimpleGraph V) (base : T → V)
    (r : ℕ) : SimpleGraph T where
  Adj a b := a ≠ b ∧ H.dist (base a) (base b) ≤ 2 * r + 1
  symm := by
    intro a b hab
    exact ⟨hab.1.symm, by simpa only [SimpleGraph.dist_comm] using hab.2⟩
  loopless := by intro a h; exact h.1 rfl

theorem contactGraph_connected
    {V T : Type*} (H : SimpleGraph V) (hH : H.Connected)
    (base : T → V) (r : ℕ)
    (hcover : ∀ v, ∃ t, H.dist v (base t) ≤ r) :
    (contactGraph H base r).Connected := by
  classical
  let chooseToken : V → T := fun v => Classical.choose (hcover v)
  have hchoice : ∀ v, H.dist v (base (chooseToken v)) ≤ r :=
    fun v => Classical.choose_spec (hcover v)
  have near_reachable (a b : T) (hd : H.dist (base a) (base b) ≤ 2 * r + 1) :
      (contactGraph H base r).Reachable a b := by
    by_cases hab : a = b
    · subst b; exact .refl a
    · exact (show (contactGraph H base r).Adj a b from ⟨hab, hd⟩).reachable
  have hstep {u v : V} (huv : H.Adj u v) :
      (contactGraph H base r).Reachable (chooseToken u) (chooseToken v) := by
    apply near_reachable
    have hleft : H.dist (base (chooseToken u)) u ≤ r := by
      simpa only [SimpleGraph.dist_comm] using hchoice u
    have hright := hchoice v
    have hdist : H.dist u v = 1 := SimpleGraph.dist_eq_one_iff_adj.mpr huv
    have ht₁ : H.dist (base (chooseToken u)) v ≤
        H.dist (base (chooseToken u)) u + H.dist u v := hH.dist_triangle
    have ht₂ : H.dist (base (chooseToken u)) (base (chooseToken v)) ≤
        H.dist (base (chooseToken u)) v + H.dist v (base (chooseToken v)) :=
      hH.dist_triangle
    omega
  have hwalk {u v : V} (p : H.Walk u v) :
      (contactGraph H base r).Reachable (chooseToken u) (chooseToken v) := by
    induction p with
    | nil => exact .refl _
    | cons h p ih => exact (hstep h).trans ih
  letI : Nonempty T := hH.nonempty.map chooseToken
  refine ⟨?_⟩
  intro a b
  obtain ⟨p⟩ := hH (base a) (base b)
  exact (near_reachable a (chooseToken (base a)) (by
    have := hchoice (base a); omega)).trans
      ((hwalk p).trans (near_reachable b (chooseToken (base b)) (by
        have := hchoice (base b); omega)).symm)

/-- A token path of `k` steps gives an internal path distance at most
`k(2r+1)` between its endpoint bases. -/
theorem base_distance_le_contact_walk
    {V T : Type*} (H : SimpleGraph V) (hH : H.Connected)
    (base : T → V) (r : ℕ) {a b : T}
    (p : (contactGraph H base r).Walk a b) :
    H.dist (base a) (base b) ≤ p.length * (2 * r + 1) := by
  induction p with
  | nil => simp
  | @cons a b c hab p ih =>
    have hstep : H.dist (base a) (base b) ≤ 2 * r + 1 := hab.2
    have htri : H.dist (base a) (base c) ≤
        H.dist (base a) (base b) + H.dist (base b) (base c) := hH.dist_triangle
    simp only [Walk.length_cons]
    nlinarith

/-- Repeated boundary labels have close bases when all vertices are within
radius `r` of some boundary base. This supplies the short internal route
used to contradict the retained-cycle external-return filter. -/
theorem exists_close_equal_labels_of_cover
    {V T ι : Type*} [Fintype ι]
    (H : SimpleGraph V) (hH : H.Connected)
    (base : T → V) (label : T → ι) (r : ℕ)
    (hcover : ∀ v, ∃ t, H.dist v (base t) ≤ r)
    (hnot : ¬ Function.Injective label) :
    ∃ a b, a ≠ b ∧ label a = label b ∧
      H.dist (base a) (base b) ≤ Fintype.card ι * (2 * r + 1) := by
  have hcontact := contactGraph_connected H hH base r hcover
  obtain ⟨a, b, hab, hlabel, hdist⟩ := exists_close_equal_labels
    (contactGraph H base r) hcontact label hnot
  obtain ⟨p, hlen⟩ := hcontact.exists_walk_length_eq_dist a b
  have hbase := base_distance_le_contact_walk H hH base r p
  rw [hlen] at hbase
  exact ⟨a, b, hab, hlabel, hbase.trans (Nat.mul_le_mul_right _ hdist)⟩

end Erdos1016.Proof.ConditionalContactGraph

end
