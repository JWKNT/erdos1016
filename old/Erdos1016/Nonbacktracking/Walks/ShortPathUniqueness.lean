import Mathlib.Combinatorics.SimpleGraph.Girth
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Subgraph
import Mathlib.Data.Finset.Card

set_option autoImplicit false

/-!
# Girth forces short nonbacktracking vertex walks to be unique

The girth condition is stated directly for actual `SimpleGraph.Walk.IsCycle`
objects. `Reduced` excludes adjacent reverse steps, and makes no simplicity
assumption. First we prove a reduced walk in an acyclic graph is a path.
Then we apply acyclicity to the union of the two walks' **edge supports**.
This supplies endpoint uniqueness without assuming it as a new oracle.
-/

noncomputable section
namespace Erdos1016.Nonbacktracking.ShortWalks
local instance shortWalksDecidable (p : Prop) : Decidable p := Classical.propDecidable p

variable {V : Type*} {G : SimpleGraph V}

/-- No ordinary cycle has length at most D. This includes acyclic graphs. -/
def GirthGreater (G : SimpleGraph V) (D : ℕ) : Prop :=
  ∀ (u : V) (p : G.Walk u u), p.IsCycle → D < p.length

/-- No immediate reversal. A closed reduced walk may still have a reversed
cyclic seam, just as in the ordinary-walk counts in source Section 6. -/
def Reduced : {u v : V} → G.Walk u v → Prop
  | _, _, .nil => True
  | u, _, .cons _ p => Reduced p ∧ (¬p.Nil → p.getVert 1 ≠ u)

@[simp] theorem reduced_nil (u : V) : Reduced (G := G) (.nil : G.Walk u u) := trivial

@[simp] theorem reduced_cons {u v w : V} (h : G.Adj u v) (p : G.Walk v w) :
    Reduced (.cons h p) ↔ Reduced p ∧ (¬p.Nil → p.getVert 1 ≠ u) := Iff.rfl

@[simp] theorem reduced_copy {u v u' v' : V} (p : G.Walk u v)
    (hu : u = u') (hv : v = v') : Reduced (p.copy hu hv) ↔ Reduced p := by
  subst u'
  subst v'
  rfl

@[simp] theorem snd_copy {u v u' v' : V} (p : G.Walk u v)
    (hu : u = u') (hv : v = v') : (p.copy hu hv).snd = p.snd := by
  subst u'
  subst v'
  rfl

@[simp] theorem mapLe_nil_iff {H : SimpleGraph V} (h : G ≤ H)
    {u v : V} (p : G.Walk u v) : (p.mapLe h).Nil ↔ p.Nil := by
  cases p <;> simp [SimpleGraph.Walk.mapLe, SimpleGraph.Walk.map]

@[simp] theorem mapLe_snd_eq {H : SimpleGraph V} (h : G ≤ H)
    {u v : V} (p : G.Walk u v) : (p.mapLe h).snd = p.snd := by
  cases p <;> simp [SimpleGraph.Walk.mapLe, SimpleGraph.Walk.snd]

@[simp] theorem mapLe_getVert {H : SimpleGraph V} (h : G ≤ H)
    {u v : V} (p : G.Walk u v) (n : ℕ) : (p.mapLe h).getVert n = p.getVert n := by
  induction p generalizing n with
  | nil => simp
  | @cons u v w huv p ih => cases n <;> simp [ih]

@[simp] theorem reduced_mapLe {H : SimpleGraph V} (h : G ≤ H)
    {u v : V} (p : G.Walk u v) : Reduced (p.mapLe h) ↔ Reduced p := by
  induction p with
  | nil => rfl
  | @cons u v w hab p ih =>
      change (Reduced (p.mapLe h) ∧ (¬(p.mapLe h).Nil → (p.mapLe h).getVert 1 ≠ u)) ↔
        (Reduced p ∧ (¬p.Nil → p.getVert 1 ≠ u))
      rw [ih, mapLe_nil_iff, mapLe_getVert]

/-- A reduced walk in a forest has no repeated vertices. The proof uses path
uniqueness in the forest only AFTER induction has made its suffix a path. -/
theorem reduced_isPath_of_acyclic (hG : G.IsAcyclic)
    {u v : V} (p : G.Walk u v) (hp : Reduced p) : p.IsPath := by
  classical
  induction p with
  | nil => exact SimpleGraph.Walk.IsPath.nil
  | @cons u v w huv p ih =>
      obtain ⟨hp, hreturn⟩ := hp
      have hpPath := ih hp
      apply (SimpleGraph.Walk.cons_isPath_iff huv p).2
      refine ⟨hpPath, ?_⟩
      intro hu
      let q := p.takeUntil u hu
      have hq : q.IsPath := hpPath.takeUntil hu
      have he : (.cons huv.symm .nil : G.Walk v u).IsPath := by
        simp [SimpleGraph.Walk.cons_isPath_iff, huv.ne, Ne.symm huv.ne]
      have heq : q = (.cons huv.symm .nil : G.Walk v u) :=
        congrArg Subtype.val (hG.path_unique ⟨q, hq⟩ ⟨_, he⟩)
      have hlen : 1 ≤ p.length := by
        have h := p.length_takeUntil_le hu
        change q.length ≤ p.length at h
        rw [heq] at h
        simpa using h
      have hnot : ¬p.Nil := SimpleGraph.Walk.not_nil_iff_lt_length.2 (by omega)
      have hlenq : q.length = 1 := by rw [heq]; simp
      have hfirst : p.getVert 1 = u := by
        have ht := p.getVert_takeUntil hu (by omega : 1 ≤ q.length)
        change q.getVert 1 = p.getVert 1 at ht
        rw [heq] at ht
        simpa using ht.symm
      exact hreturn hnot hfirst

section EdgeSpan
variable [DecidableEq V]

/-- Retain precisely the listed original edges, with all original vertices.
This is not an induced graph and is used only in the short-walk argument. -/
def edgeSpan (G : SimpleGraph V) (S : Finset (Sym2 V)) : SimpleGraph V where
  Adj u v := G.Adj u v ∧ s(u, v) ∈ S
  symm := by
    intro u v h
    exact ⟨h.1.symm, by simpa only [Sym2.eq_swap] using h.2⟩
  loopless := by intro v h; exact G.loopless v h.1

@[simp] theorem edgeSpan_adj (S : Finset (Sym2 V)) (u v : V) :
    (edgeSpan G S).Adj u v ↔ G.Adj u v ∧ s(u, v) ∈ S := Iff.rfl

theorem edgeSpan_le (S : Finset (Sym2 V)) : edgeSpan G S ≤ G :=
  fun _ _ h => h.1

/-- Every traversed physical unordered edge is one of the retained edges. -/
theorem walk_edges_mem_span (S : Finset (Sym2 V))
    {u v : V} (p : (edgeSpan G S).Walk u v) :
    ∀ e ∈ p.edges, e ∈ S := by
  induction p with
  | nil => simp
  | cons h p ih =>
      intro e he
      rcases List.mem_cons.1 he with rfl | he
      · exact h.2
      · exact ih e he

/-- A small edge support is acyclic under the actual cycle-length condition. -/
theorem edgeSpan_acyclic (D : ℕ) (hg : GirthGreater G D)
    (S : Finset (Sym2 V)) (hS : S.card ≤ D) :
    (edgeSpan G S).IsAcyclic := by
  intro u p hp
  let q := p.mapLe (edgeSpan_le (G := G) S)
  have hq : q.IsCycle := hp.mapLe _
  have hlen : p.length ≤ S.card := by
    have he : p.edges.toFinset ⊆ S := by
      intro e he
      exact walk_edges_mem_span S p e (List.mem_toFinset.1 he)
    have hc := Finset.card_le_card he
    rw [List.toFinset_card_of_nodup hp.1.1.edges_nodup,
      SimpleGraph.Walk.length_edges] at hc
    exact hc
  have hlong := hg u q hq
  have hlength : q.length = p.length := by simp [q]
  omega

/-- Restrict a walk to its supplied edge support, without changing vertices
or deleting steps. The support inclusion is checked at every constructor. -/
def restrictWalk (S : Finset (Sym2 V)) :
    {u v : V} → (p : G.Walk u v) →
      (∀ e ∈ p.edges, e ∈ S) → (edgeSpan G S).Walk u v
  | _, _, .nil, _ => .nil
  | _, _, .cons h p, hs =>
      .cons ⟨h, hs _ (by simp)⟩
        (restrictWalk S p (fun e he => hs e (by simp [he])))

@[simp] theorem restrictWalk_mapLe (S : Finset (Sym2 V))
    {u v : V} (p : G.Walk u v) :
    ∀ (hs : ∀ e ∈ p.edges, e ∈ S),
      (restrictWalk S p hs).mapLe (edgeSpan_le S) = p := by
  induction p with
  | nil => intro hs; rfl
  | cons h p ih =>
      intro hs
      simp only [restrictWalk, SimpleGraph.Walk.mapLe, SimpleGraph.Walk.map]
      congr 1
      exact ih _

/-- The restriction keeps the nonbacktracking condition as well. -/
theorem reduced_restrictWalk (S : Finset (Sym2 V))
    {u v : V} (p : G.Walk u v) (hs : ∀ e ∈ p.edges, e ∈ S)
    (hp : Reduced p) : Reduced (restrictWalk S p hs) := by
  apply (reduced_mapLe (edgeSpan_le S) _).1
  simpa only [restrictWalk_mapLe] using hp

/-- A reduced walk of length <=D is simple when no cycle has length <=D. -/
theorem reduced_isPath_of_girth (D : ℕ) (hg : GirthGreater G D)
    {u v : V} (p : G.Walk u v) (hp : Reduced p) (hlen : p.length ≤ D) :
    p.IsPath := by
  let S := p.edges.toFinset
  have hs : ∀ e ∈ p.edges, e ∈ S := by intro e he; exact List.mem_toFinset.2 he
  have hS : S.card ≤ D :=
    (List.toFinset_card_le p.edges).trans (by simpa using hlen)
  have hforest := edgeSpan_acyclic D hg S hS
  have hpath := reduced_isPath_of_acyclic hforest (restrictWalk S p hs)
    (reduced_restrictWalk S p hs hp)
  have hmap := hpath.mapLe (edgeSpan_le S)
  simpa only [restrictWalk_mapLe] using hmap

/-- Two reduced walks with the same endpoints are identical if the SUM of
their lengths is below the girth. No bounded degree or connectedness is used. -/
theorem reduced_walk_unique_of_girth (D : ℕ) (hg : GirthGreater G D)
    {u v : V} (p q : G.Walk u v) (hp : Reduced p) (hq : Reduced q)
    (hlen : p.length + q.length ≤ D) : p = q := by
  let S := p.edges.toFinset ∪ q.edges.toFinset
  have hpS : ∀ e ∈ p.edges, e ∈ S := by
    intro e he
    exact Finset.mem_union_left _ (List.mem_toFinset.2 he)
  have hqS : ∀ e ∈ q.edges, e ∈ S := by
    intro e he
    exact Finset.mem_union_right _ (List.mem_toFinset.2 he)
  have hS : S.card ≤ D := by
    calc
      _ ≤ p.edges.toFinset.card + q.edges.toFinset.card := Finset.card_union_le _ _
      _ ≤ p.edges.length + q.edges.length :=
        Nat.add_le_add (List.toFinset_card_le _) (List.toFinset_card_le _)
      _ ≤ D := by simpa using hlen
  have hforest := edgeSpan_acyclic D hg S hS
  let p' := restrictWalk S p hpS
  let q' := restrictWalk S q hqS
  have hp' : p'.IsPath := reduced_isPath_of_acyclic hforest p'
    (reduced_restrictWalk S p hpS hp)
  have hq' : q'.IsPath := reduced_isPath_of_acyclic hforest q'
    (reduced_restrictWalk S q hqS hq)
  have heq : p' = q' := congrArg Subtype.val (hforest.path_unique ⟨p', hp'⟩ ⟨q', hq'⟩)
  have hm := congrArg (fun w : (edgeSpan G S).Walk u v =>
    w.mapLe (edgeSpan_le S)) heq
  simpa only [p', q', restrictWalk_mapLe] using hm

end EdgeSpan
end Erdos1016.Nonbacktracking.ShortWalks
