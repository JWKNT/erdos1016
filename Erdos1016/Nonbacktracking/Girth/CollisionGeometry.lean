import Erdos1016.Nonbacktracking.Girth.CollisionSlices

set_option autoImplicit false

/-!
# Structural geometry for the cyclic-run collision split

These walk-level facts are the local pieces needed to split a nonsimple
cyclic run at a repeated vertex before applying the fixed-endpoint suffix
bound. The global split encoding/count remains in the collision-slice layer.
-/

noncomputable section
namespace Erdos1016.Proof.CyclicRunCollisionGeometry

open Erdos1016.Nonbacktracking
open Erdos1016.Proof.CyclicRunCollisionSlice

local instance cyclicRunCollisionGeometryDecidable (p : Prop) : Decidable p :=
  Classical.propDecidable p

variable {V : Type*} {G : SimpleGraph V}



/-- Split at a specified vertex index, preserving the occurrence even when
the same vertex appeared earlier. -/
theorem take_append_drop_at_index {u v : V} (p : G.Walk u v) (i : ℕ) :
    (p.take i).append (p.drop i) = p := by
  induction p generalizing i with
  | nil => cases i <;> rfl
  | @cons a b c h q ih =>
      cases i with
      | zero => simp [SimpleGraph.Walk.take, SimpleGraph.Walk.drop]
      | succ i => simpa [SimpleGraph.Walk.take, SimpleGraph.Walk.drop] using
          congrArg (fun r : G.Walk b c => SimpleGraph.Walk.cons h r) (ih i)

/-- Exact length of the prefix selected by a vertex index. -/
theorem take_length_at_index {u v : V} (p : G.Walk u v) (i : ℕ) :
    (p.take i).length = min i p.length := by
  induction p generalizing i with
  | nil => cases i <;> simp [SimpleGraph.Walk.take]
  | @cons a b c h q ih =>
      cases i with
      | zero => simp [SimpleGraph.Walk.take]
      | succ i =>
          simp only [SimpleGraph.Walk.take, SimpleGraph.Walk.length_cons]
          rw [ih]
          omega

/-- Exact length of the suffix after the selected vertex index. -/
theorem drop_length_at_index {u v : V} (p : G.Walk u v) (i : ℕ) :
    (p.drop i).length = p.length - i := by
  induction p generalizing i with
  | nil => cases i <;> simp [SimpleGraph.Walk.drop]
  | @cons a b c h q ih =>
      cases i with
      | zero => simp [SimpleGraph.Walk.drop]
      | succ i =>
          simp only [SimpleGraph.Walk.drop, SimpleGraph.Walk.length_cons]
          rw [ih]
          omega

/-- Looking `j` steps into the suffix after dropping `i` steps is the same
as looking `i + j` steps into the original walk. -/
theorem getVert_drop_at_index {u v : V} (p : G.Walk u v) (i j : ℕ) :
    (p.drop i).getVert j = p.getVert (i + j) := by
  induction p generalizing i j with
  | nil => simp [SimpleGraph.Walk.drop, SimpleGraph.Walk.getVert]
  | @cons a b c h q ih =>
      cases i with
      | zero => simp [SimpleGraph.Walk.drop]
      | succ i =>
          simp only [SimpleGraph.Walk.drop, SimpleGraph.Walk.getVert]
          rw [ih]
          rw [show i + 1 + j = (i + j) + 1 by omega,
            SimpleGraph.Walk.getVert]

/-- The ordered endpoint pairs traversed by a walk. This is a graph-generic
serialization of its oriented edge word. -/
def walkSteps {u v : V} : G.Walk u v → List (V × V)
  | .nil => []
  | .cons h q => (u, q.getVert 0) :: walkSteps q

theorem walkSteps_copy {u v u' v' : V} (p : G.Walk u v)
    (hu : u = u') (hv : v = v') :
    walkSteps (p.copy hu hv) = walkSteps p := by
  subst u'
  subst v'
  rfl

theorem walkSteps_take {u v : V} (p : G.Walk u v) (i : ℕ) :
    walkSteps (p.take i) = (walkSteps p).take i := by
  induction p generalizing i with
  | nil => cases i <;> simp [SimpleGraph.Walk.take, walkSteps]
  | cons h q ih =>
      cases i with
      | zero => simp [SimpleGraph.Walk.take, walkSteps]
      | succ i => simp [SimpleGraph.Walk.take, walkSteps, SimpleGraph.Walk.support_cons,
          ih]

theorem walkSteps_drop {u v : V} (p : G.Walk u v) (i : ℕ) :
    walkSteps (p.drop i) = (walkSteps p).drop i := by
  induction p generalizing i with
  | nil => cases i <;> simp [SimpleGraph.Walk.drop, walkSteps]
  | cons h q ih =>
      cases i with
      | zero => simp [SimpleGraph.Walk.drop, walkSteps]
      | succ i => simp [SimpleGraph.Walk.drop, walkSteps, SimpleGraph.Walk.support_cons,
          ih]

theorem walkSteps_append {u v w : V} (p : G.Walk u v) (q : G.Walk v w) :
    walkSteps (p.append q) = walkSteps p ++ walkSteps q := by
  induction p with
  | nil => simp [SimpleGraph.Walk.append, walkSteps]
  | cons h p ih => simp [SimpleGraph.Walk.append, walkSteps, SimpleGraph.Walk.support_cons,
      ih]

/-- An oriented vertex-step word uniquely determines a walk with fixed
endpoints in a simple graph. -/
theorem eq_of_walkSteps {u v : V} (p q : G.Walk u v)
    (hsteps : walkSteps p = walkSteps q) : p = q := by
  induction p with
  | nil =>
      cases q with
      | nil => rfl
      | cons h q => simp [walkSteps] at hsteps
  | @cons a b c h p ih =>
      cases q with
      | nil => simp [walkSteps] at hsteps
      | @cons _ b' _ h' q =>
          have hparts := List.cons.inj hsteps
          have hnext : b = b' := by
            have h := congrArg Prod.snd hparts.1
            simpa using h
          subst b'
          have hadj : h = h' := Subsingleton.elim _ _
          subst h'
          have htail : walkSteps p = walkSteps q := hparts.2
          have hwalk : p = q := ih q htail
          subst q
          rfl

/-- A list is recovered from its rotation and the cut position used to make
that rotation. -/
theorem list_eq_of_drop_take_rotation {α : Type*} (l : List α) (n : ℕ)
    (hn : n ≤ l.length) :
    l = (l.drop n ++ l.take n).drop (l.length - n) ++
      (l.drop n ++ l.take n).take (l.length - n) := by
  have hrotate : l.rotate n = l.drop n ++ l.take n :=
    List.rotate_eq_drop_append_take hn
  have hback : (l.rotate n).rotate (l.length - n) = l := by
    rw [List.rotate_rotate]
    have hindex : n + (l.length - n) = l.length := by omega
    rw [hindex, List.rotate_length]
  rw [← hrotate]
  rw [← List.rotate_eq_drop_append_take
    (by rw [List.length_rotate]; omega : l.length - n ≤ (l.rotate n).length)]
  exact hback.symm

theorem list_eq_of_same_drop_take_rotation {α : Type*}
    (l₁ l₂ : List α) (n : ℕ) (hlen : l₁.length = l₂.length)
    (hn : n ≤ l₁.length)
    (hrot : l₁.drop n ++ l₁.take n = l₂.drop n ++ l₂.take n) :
    l₁ = l₂ := by
  have hn₂ : n ≤ l₂.length := by omega
  calc
    l₁ = (l₁.drop n ++ l₁.take n).drop (l₁.length - n) ++
        (l₁.drop n ++ l₁.take n).take (l₁.length - n) :=
      list_eq_of_drop_take_rotation l₁ n hn
    _ = (l₂.drop n ++ l₂.take n).drop (l₂.length - n) ++
        (l₂.drop n ++ l₂.take n).take (l₂.length - n) := by rw [hrot, hlen]
    _ = l₂ := (list_eq_of_drop_take_rotation l₂ n hn₂).symm

/-- Taking an initial segment preserves reducedness. -/
theorem reduced_take_at_index {u v : V} (p : G.Walk u v)
    (hp : ShortWalks.Reduced p) (i : ℕ) :
    ShortWalks.Reduced (p.take i) := by
  induction p generalizing i with
  | nil => cases i <;> simp [SimpleGraph.Walk.take, ShortWalks.Reduced]
  | @cons a b c h q ih =>
      cases i with
      | zero => simp [SimpleGraph.Walk.take, ShortWalks.Reduced]
      | succ i =>
          cases i with
          | zero => cases q <;> simp [SimpleGraph.Walk.take, ShortWalks.Reduced]
          | succ i =>
              have ⟨hq, hret⟩ := (ShortWalks.reduced_cons h q).mp hp
              simp only [SimpleGraph.Walk.take, ShortWalks.reduced_cons]
              refine ⟨ih hq (i + 1), ?_⟩
              intro hnil
              cases q with
              | nil => simp [SimpleGraph.Walk.take] at hnil
              | cons hq' r =>
                  have hfirst : ((SimpleGraph.Walk.cons hq' r).take (i + 1)).getVert 1 =
                      (SimpleGraph.Walk.cons hq' r).getVert 1 := by
                    simp [SimpleGraph.Walk.take, SimpleGraph.Walk.getVert]
                  exact fun h => hret (by simp) (hfirst.symm.trans h)

/-- Dropping an initial segment preserves reducedness. -/
theorem reduced_drop_at_index {u v : V} (p : G.Walk u v)
    (hp : ShortWalks.Reduced p) (i : ℕ) :
    ShortWalks.Reduced (p.drop i) := by
  induction p generalizing i with
  | nil => cases i <;> simp [SimpleGraph.Walk.drop, ShortWalks.Reduced]
  | @cons a b c h q ih =>
      cases i with
      | zero => simpa [SimpleGraph.Walk.drop] using hp
      | succ i =>
          have hq := (ShortWalks.reduced_cons h q).mp hp |>.1
          simpa [SimpleGraph.Walk.drop] using ih hq i

/-- Concatenating reduced walks preserves reducedness when the turn at the
join is not an immediate reversal. -/
theorem reduced_append_of_seam {u v w : V}
    (p : G.Walk u v) (q : G.Walk v w)
    (hp : ShortWalks.Reduced p) (hq : ShortWalks.Reduced q)
    (hseam : ¬ p.Nil → ¬ q.Nil → q.getVert 1 ≠ p.penultimate) :
    ShortWalks.Reduced (p.append q) := by
  induction p with
  | nil => simpa [SimpleGraph.Walk.append] using hq
  | @cons a b c h r ih =>
      have ⟨hr, hreturn⟩ := (ShortWalks.reduced_cons h r).mp hp
      cases r with
      | nil =>
          change ShortWalks.Reduced (SimpleGraph.Walk.cons h q)
          refine ⟨hq, ?_⟩
          intro hqnon
          have hs := hseam (by simp) hqnon
          simpa [SimpleGraph.Walk.penultimate_cons_nil] using hs
      | cons h₂ t =>
          have htailSeam : ¬ (SimpleGraph.Walk.cons h₂ t).Nil →
              ¬ q.Nil → q.getVert 1 ≠ (SimpleGraph.Walk.cons h₂ t).penultimate := by
            intro _ hqnon
            have hpnon : ¬ (SimpleGraph.Walk.cons h (SimpleGraph.Walk.cons h₂ t)).Nil := by
              simp
            have hs := hseam hpnon hqnon
            simpa using hs
          have hrec := ih q hr hq htailSeam
          change ShortWalks.Reduced
            (SimpleGraph.Walk.cons h ((SimpleGraph.Walk.cons h₂ t).append q))
          refine ⟨hrec, ?_⟩
          intro _
          have hret := hreturn (by simp : ¬ (SimpleGraph.Walk.cons h₂ t).Nil)
          simpa [SimpleGraph.Walk.append, SimpleGraph.Walk.getVert] using hret

/-- Taking a nonempty prefix leaves the first successor vertex unchanged. -/
theorem getVert_one_take_of_pos {u v : V} (p : G.Walk u v) (i : ℕ)
    (hi : 0 < i) : (p.take i).getVert 1 = p.getVert 1 := by
  cases p with
  | nil => simp [SimpleGraph.Walk.take]
  | cons h q =>
      cases i with
      | zero => omega
      | succ i => simp [SimpleGraph.Walk.take, SimpleGraph.Walk.getVert]

/-- A position in `support.tail` is the corresponding positive vertex index
of the walk. -/
theorem support_tail_get_eq_getVert {u v : V} (p : G.Walk u v)
    (i : Fin p.support.tail.length) :
    p.support.tail.get i = p.getVert (i.val + 1) := by
  have htailLength : p.support.tail.length = p.length := by
    simp [SimpleGraph.Walk.length_support]
  have hi : i.val + 1 ≤ p.length := by rw [← htailLength]; omega
  have hvalid : i.val + 1 < p.support.length := by
    rw [SimpleGraph.Walk.length_support]
    omega
  have hget : p.getVert (i.val + 1) =
      p.support.get ⟨i.val + 1, hvalid⟩ := by
    have h := SimpleGraph.Walk.getVert_eq_support_get? p hi
    rw [List.getElem?_eq_getElem hvalid] at h
    simpa using Option.some.inj h
  have htail := List.get_tail p.support i.val i.isLt hvalid
  calc
    p.support.tail.get i = p.support.get ⟨i.val + 1, hvalid⟩ := htail
    _ = p.getVert (i.val + 1) := hget.symm

/-- A nonempty linearly reduced walk determines the corresponding
nonbacktracking dart run. This is the run encoding needed to count the two
closed arcs created by a repeated vertex. -/
theorem reduced_walk_has_dart_run (G : PhysicalGraph) :
    ∀ {a b : G.Vertex} (p : G.toSimpleGraph.Walk a b),
      ShortWalks.Reduced p → 0 < p.length →
      ∃ d e : Dart G, tail G d = a ∧ head G d = p.snd ∧
        tail G e = p.penultimate ∧ head G e = b ∧
        ∃ r : Run G (p.length - 1) d e,
          runDarts G (p.length - 1) r = walkDarts G p := by
  intro a b p
  induction p with
  | nil => intro hp hl; simp at hl
  | @cons a b c hab q ih =>
      intro hp hl
      have ⟨hqred, hreturn⟩ := (ShortWalks.reduced_cons hab q).mp hp
      let d := dartOfAdj G hab
      have htail : tail G d = a := tail_dartOfAdj G hab
      have hhead : head G d = b := head_dartOfAdj G hab
      cases q with
      | nil =>
          simp only [SimpleGraph.Walk.length_cons, SimpleGraph.Walk.length_nil] at hl ⊢
          refine ⟨d, d, htail, ?_, ?_, hhead, ?_⟩
          · simpa using hhead
          · exact htail
          · refine ⟨⟨(), rfl⟩, ?_⟩
            simp [runDarts, walkDarts, d]
      | @cons b c t hbc r =>
          have hqpos : 0 < (SimpleGraph.Walk.cons hbc r).length := by simp
          obtain ⟨e, f, htailE, hheadE, htailF, hheadF, rr, hrr⟩ :=
            ih hqred hqpos
          have hnoreturn : head G e ≠ a := by
            intro h
            apply hreturn (by simp)
            calc
              (SimpleGraph.Walk.cons hbc r).getVert 1 = head G e := by
                simpa [SimpleGraph.Walk.getVert] using hheadE.symm
              _ = a := h
          have hnext : Next G d e := by
            refine ⟨?_, ?_⟩
            · rw [hhead, htailE]
            · intro hrev
              apply hnoreturn
              rw [hrev, head_reverse, htail]
          have hlen : (SimpleGraph.Walk.cons hab
              (SimpleGraph.Walk.cons hbc r)).length - 1 =
              (SimpleGraph.Walk.cons hbc r).length := by simp
          have hqidx : (SimpleGraph.Walk.cons hbc r).length - 1 = r.length := by simp
          let rr' : Run G r.length e f := hqidx ▸ rr
          have hrr' : runDarts G r.length rr' =
              walkDarts G (SimpleGraph.Walk.cons hbc r) := by
            simpa [rr', hqidx] using hrr
          let rrnew : Run G (r.length + 1) d f := ⟨e, ⟨(), hnext⟩, rr'⟩
          have hlist : runDarts G (r.length + 1) rrnew =
              walkDarts G (SimpleGraph.Walk.cons hab
                (SimpleGraph.Walk.cons hbc r)) := by
            simp [rrnew, runDarts, walkDarts, d, hrr']
          refine ⟨d, f, htail, ?_, ?_, hheadF, ?_⟩
          · simpa using hhead
          · simpa [SimpleGraph.Walk.penultimate] using htailF
          rw [hlen]
          exact ⟨rrnew, hlist⟩



/-- Dart serialization commutes with taking a vertex-indexed prefix. -/
theorem walkDarts_take_at_index (G : PhysicalGraph) {u v : G.Vertex}
    (p : G.toSimpleGraph.Walk u v) (i : ℕ) :
    walkDarts G (p.take i) = (walkDarts G p).take i := by
  induction p generalizing i with
  | nil => cases i <;> simp [SimpleGraph.Walk.take, walkDarts]
  | cons h q ih =>
      cases i with
      | zero => simp [SimpleGraph.Walk.take, walkDarts]
      | succ i => simp [SimpleGraph.Walk.take, walkDarts, ih]

/-- Dart serialization commutes with taking a vertex-indexed suffix. -/
theorem walkDarts_drop_at_index (G : PhysicalGraph) {u v : G.Vertex}
    (p : G.toSimpleGraph.Walk u v) (i : ℕ) :
    walkDarts G (p.drop i) = (walkDarts G p).drop i := by
  induction p generalizing i with
  | nil => cases i <;> simp [SimpleGraph.Walk.drop, walkDarts]
  | cons h q ih =>
      cases i with
      | zero => simp [SimpleGraph.Walk.drop, walkDarts]
      | succ i => simp [SimpleGraph.Walk.drop, walkDarts, ih]

/-- Dart serialization of an appended walk is the concatenation of the two
dart words. -/
theorem walkDarts_append (G : PhysicalGraph) {u v w : G.Vertex}
    (p : G.toSimpleGraph.Walk u v) (q : G.toSimpleGraph.Walk v w) :
    walkDarts G (p.append q) = walkDarts G p ++ walkDarts G q := by
  induction p with
  | nil => simp [SimpleGraph.Walk.append, walkDarts]
  | cons h p ih => simp [SimpleGraph.Walk.append, walkDarts, ih]

theorem walkDarts_length (G : PhysicalGraph) {u v : G.Vertex}
    (p : G.toSimpleGraph.Walk u v) : (walkDarts G p).length = p.length := by
  induction p with
  | nil => rfl
  | cons h p ih => simp [walkDarts, ih]

/-- Two equal vertices at ordered positions in the support tail cut a closed
walk into the intervening arc and the complementary wraparound arc. Their
lengths add to the original walk length. -/
theorem closed_arcs_of_repeated_support_indices {u : V}
    (p : G.Walk u u) (i j : Fin p.support.tail.length)
    (hp : ShortWalks.Reduced p)
    (hseam : p.getVert 1 ≠ p.penultimate)
    (hij : i.val < j.val)
    (hrep : p.support.tail.get i = p.support.tail.get j) :
    ∃ q r : G.Walk (p.getVert (i.val + 1)) (p.getVert (i.val + 1)),
      q.length = j.val - i.val ∧
        r.length = p.length - (j.val - i.val) ∧
        ShortWalks.Reduced q ∧ ShortWalks.Reduced r ∧
        0 < q.length ∧ 0 < r.length ∧ q.length + r.length = p.length ∧
        q.append r = (p.drop (i.val + 1)).append (p.take (i.val + 1)) := by
  let I := i.val + 1
  let J := j.val + 1
  have htailLength : p.support.tail.length = p.length := by
    simp [SimpleGraph.Walk.length_support]
  have hIle : I ≤ p.length := by dsimp [I]; rw [← htailLength]; omega
  have hJle : J ≤ p.length := by dsimp [J]; rw [← htailLength]; omega
  have hIJ : I ≤ J := by dsimp [I, J]; omega
  have hvertex : p.getVert I = p.getVert J := by
    dsimp [I, J]
    calc
      p.getVert (i.val + 1) = p.support.tail.get i :=
        (support_tail_get_eq_getVert p i).symm
      _ = p.support.tail.get j := hrep
      _ = p.getVert (j.val + 1) := support_tail_get_eq_getVert p j
  have hqEnd : (p.drop I).getVert (J - I) = p.getVert J := by
    rw [getVert_drop_at_index]
    congr 1
    omega
  let qRaw := (p.drop I).take (J - I)
  let q := qRaw.copy rfl (hqEnd.trans hvertex.symm)
  let rRaw := (p.drop J).append (p.take I)
  let r := rRaw.copy hvertex.symm rfl
  have hqLength : q.length = J - I := by
    dsimp [q, qRaw]
    rw [SimpleGraph.Walk.length_copy, take_length_at_index,
      drop_length_at_index]
    have hmin : J - I ≤ p.length - I := by omega
    simp [Nat.min_eq_left hmin]
  have hrLength : r.length = p.length - (J - I) := by
    dsimp [r, rRaw]
    rw [SimpleGraph.Walk.length_copy, SimpleGraph.Walk.length_append,
      drop_length_at_index, take_length_at_index]
    have hmin : I ≤ p.length := hIle
    simp only [Nat.min_eq_left hmin]
    omega
  have hqReduced : ShortWalks.Reduced q := by
    dsimp [q, qRaw]
    exact (ShortWalks.reduced_copy _ _ _).2
      (reduced_take_at_index (p.drop I) (reduced_drop_at_index p hp I) (J - I))
  have hrReduced : ShortWalks.Reduced r := by
    dsimp [r, rRaw]
    apply (ShortWalks.reduced_copy _ _ _).2
    apply reduced_append_of_seam (p.drop J) (p.take I)
    · exact reduced_drop_at_index p hp J
    · exact reduced_take_at_index p hp I
    · intro hdrop htake
      have htakePos : 0 < I := by dsimp [I]; omega
      have hfirst : (p.take I).getVert 1 = p.getVert 1 :=
        getVert_one_take_of_pos p I htakePos
      have hdropPos : 0 < (p.drop J).length := by
        exact (SimpleGraph.Walk.not_nil_iff_lt_length).mp hdrop
      have hterminal : (p.drop J).penultimate = p.penultimate := by
        rw [SimpleGraph.Walk.penultimate, getVert_drop_at_index,
          drop_length_at_index]
        rw [drop_length_at_index] at hdropPos
        congr 1
        omega
      rw [hfirst, hterminal]
      exact hseam
  have hrotSteps : walkSteps (q.append r) =
      (walkSteps p).drop I ++ (walkSteps p).take I := by
    dsimp [q, r]
    simp only [walkSteps_append, walkSteps_copy, walkSteps_take,
      walkSteps_drop, qRaw, rRaw]
    have hdropdrop : ((walkSteps p).drop I).drop (J - I) =
        (walkSteps p).drop J := by
      rw [List.drop_drop]
      congr 1
      omega
    have hsplit := List.take_append_drop (J - I) ((walkSteps p).drop I)
    rw [hdropdrop] at hsplit
    calc
      _ = (((walkSteps p).drop I).take (J - I) ++
          (walkSteps p).drop J) ++ (walkSteps p).take I := by
            simp [List.append_assoc]
      _ = (walkSteps p).drop I ++ (walkSteps p).take I := by rw [hsplit]
  refine ⟨q, r, ?_, ?_, hqReduced, hrReduced, ?_, ?_, ?_, ?_⟩
  · rw [hqLength]
    dsimp [I, J]
    omega
  · rw [hrLength]
    dsimp [I, J]
    omega
  · rw [hqLength]
    dsimp [I, J]
    omega
  · rw [hrLength]
    dsimp [I, J]
    omega
  · rw [hqLength, hrLength]
    omega
  · apply eq_of_walkSteps
    calc
      walkSteps (q.append r) =
          (walkSteps p).drop I ++ (walkSteps p).take I := hrotSteps
      _ = walkSteps ((p.drop I).append (p.take I)) := by
        have h := walkSteps_append (p.drop I) (p.take I)
        rw [walkSteps_drop, walkSteps_take] at h
        exact h.symm

/-- If a path joins two vertices and also uses the edge joining its
endpoints, that edge must be the path's only edge. -/
theorem endpoint_edge_mem_path_length_one {a b : V}
    (q : G.Walk b a) (hq : q.support.Nodup)
    (he : s(a, b) ∈ q.edges) : q.length = 1 := by
  cases q with
  | nil => simp at he
  | @cons _ mid _ hadj r =>
      simp only [SimpleGraph.Walk.edges_cons, List.mem_cons] at he
      simp only [SimpleGraph.Walk.support_cons, List.nodup_cons] at hq
      rcases he with heHead | heTail
      · have heEq : s(a, b) = s(b, mid) := heHead
        rcases Sym2.eq_iff.mp heEq with ⟨hab, hbm⟩ | ⟨ham, hbb⟩
        · have hloop : G.Adj b b := by simpa [hab, hbm] using hadj
          have hfalse : False := G.ne_of_adj hloop rfl
          exact hfalse.elim
        · subst mid
          have hrpath : r.IsPath := by
            exact SimpleGraph.Walk.IsPath.mk' hq.2
          have hrnil : r = SimpleGraph.Walk.nil :=
            (SimpleGraph.Walk.isPath_iff_eq_nil r).mp hrpath
          simp [hrnil]
      · have hb : b ∈ r.support := r.snd_mem_support_of_mem_edges heTail
        exact (hq.1 hb).elim

/-- A cyclically reduced closed walk with no repeated vertices in its
cyclic support tail is an ordinary simple cycle. -/
theorem cyclic_reduced_support_tail_nodup_isCycle {u : V}
    (p : G.Walk u u) (hp : ShortWalks.Reduced p)
    (hnil : p ≠ SimpleGraph.Walk.nil)
    (hs : p.support.tail.Nodup) : p.IsCycle := by
  cases p with
  | nil => exact (hnil rfl).elim
  | @cons _ mid _ hadj q =>
      have hq : q.support.Nodup := by
        simpa [SimpleGraph.Walk.support_cons] using hs
      have hred := (ShortWalks.reduced_cons hadj q).mp hp
      have hseam : s(u, mid) ∉ q.edges := by
        intro hedge
        have hlen := endpoint_edge_mem_path_length_one q hq hedge
        have hnotnil : ¬ q.Nil :=
          (SimpleGraph.Walk.not_nil_iff_lt_length).2 (by omega)
        have hget : q.getVert 1 = u := by
          simpa [hlen] using q.getVert_length
        exact hred.2 hnotnil hget
      rw [SimpleGraph.Walk.cons_isCycle_iff]
      exact ⟨SimpleGraph.Walk.IsPath.mk' hq, hseam⟩

/-- A non-cycle cyclically reduced closed walk has two distinct positions in
its tail support list occupied by the same vertex. -/
theorem exists_repeated_support_indices_of_not_cycle {u : V}
    (p : G.Walk u u) (hp : ShortWalks.Reduced p)
    (hnil : p ≠ SimpleGraph.Walk.nil)
    (hbad : ¬ p.IsCycle) :
    ∃ i j : Fin p.support.tail.length,
      i ≠ j ∧ p.support.tail.get i = p.support.tail.get j := by
  have hnotnodup : ¬ p.support.tail.Nodup := by
    intro hnodup
    exact hbad (cyclic_reduced_support_tail_nodup_isCycle p hp hnil hnodup)
  have hnotinj :
      ¬ Function.Injective (fun i : Fin p.support.tail.length => p.support.tail[i.1]) := by
    intro hinj
    exact hnotnodup (List.nodup_iff_injective_getElem.mpr hinj)
  obtain ⟨i, j, heq, hne⟩ := Function.not_injective_iff.mp hnotinj
  exact ⟨i, j, hne, heq⟩

/-- Under girth greater than `D`, a nonempty reduced closed walk has length
greater than `D`. This is the arc-length fact used for both pieces created
by a repeated-vertex split. -/
theorem reduced_closed_nonempty_length_gt (D : ℕ)
    (hg : ShortWalks.GirthGreater G D) {u : V}
    (p : G.Walk u u) (hp : ShortWalks.Reduced p) (hnil : ¬ p.Nil) :
    D < p.length := by
  by_contra h
  have hlen : p.length ≤ D := by omega
  have hpath := ShortWalks.reduced_isPath_of_girth D hg p hp hlen
  have hpEq : p = SimpleGraph.Walk.nil :=
    (SimpleGraph.Walk.isPath_iff_eq_nil p).1 hpath
  exact hnil (by rw [hpEq]; simp)

/-- A cyclic run's ordinary walk remains linearly reduced; the cyclic seam
condition is an additional property carried separately by `CyclicRuns`. -/
theorem cyclicRunWalk_reduced (G : PhysicalGraph) (ell : ℕ)
    (p : CyclicRuns G ell) :
    ShortWalks.Reduced (cyclicRunWalk G ell p) := by
  unfold cyclicRunWalk
  exact (ShortWalks.reduced_copy _ _ _).2
    (runWalk_reduced G (ell - 1) p.1.1.2.2)

theorem cyclicRunWalk_length (G : PhysicalGraph) (ell : ℕ)
    (hell : 0 < ell) (p : CyclicRuns G ell) :
    (cyclicRunWalk G ell p).length = ell := by
  unfold cyclicRunWalk
  rw [SimpleGraph.Walk.length_copy, runWalk_length]
  omega

/-- The closed vertex walk of a cyclic run serializes to its underlying
physical dart run. -/
theorem cyclicRunWalk_darts (G : PhysicalGraph) (ell : ℕ)
    (hell : 0 < ell) (p : CyclicRuns G ell) :
    walkDarts G (cyclicRunWalk G ell p) =
      runDarts G (ell - 1) p.1.1.2.2 := by
  unfold cyclicRunWalk
  simp [walkDarts_runWalk]

/-- A rooted cyclic run is determined by its dart word, even if that word
is compared after the same cyclic rotation on both sides. -/
theorem cyclicRuns_eq_of_same_rotated_dart_word
    (G : PhysicalGraph) (ell m : ℕ) (hell : 0 < ell) (hm : m ≤ ell)
    {p p' : CyclicRuns G ell}
    (hrot :
      (walkDarts G (cyclicRunWalk G ell p)).drop m ++
          (walkDarts G (cyclicRunWalk G ell p)).take m =
        (walkDarts G (cyclicRunWalk G ell p')).drop m ++
          (walkDarts G (cyclicRunWalk G ell p')).take m) :
    p = p' := by
  have hpLen : (walkDarts G (cyclicRunWalk G ell p)).length = ell := by
    rw [walkDarts_length, cyclicRunWalk_length G ell hell p]
  have hp'Len : (walkDarts G (cyclicRunWalk G ell p')).length = ell := by
    rw [walkDarts_length, cyclicRunWalk_length G ell hell p']
  have hword : walkDarts G (cyclicRunWalk G ell p) =
      walkDarts G (cyclicRunWalk G ell p') :=
    list_eq_of_same_drop_take_rotation _ _ m (by omega) (by omega) hrot
  rw [cyclicRunWalk_darts G ell hell p,
    cyclicRunWalk_darts G ell hell p'] at hword
  have hrun : p.1.1 = p'.1.1 :=
    allRuns_darts_injective G (ell - 1) hword
  apply Subtype.ext
  apply Subtype.ext
  exact hrun

/-- Reconstruction from two endpoint-run arc words and a common root
offset: equality of the concatenated arc serializations forces equality of
the original rooted cyclic runs. -/
theorem cyclicRuns_eq_of_equal_arc_run_words
    (G : PhysicalGraph) (ell m : ℕ) (hell : 0 < ell) (hm : m ≤ ell)
    {p p' : CyclicRuns G ell}
    {left right left' right' : List (Dart G)}
    (hp : left ++ right =
      (walkDarts G (cyclicRunWalk G ell p)).drop m ++
        (walkDarts G (cyclicRunWalk G ell p)).take m)
    (hp' : left' ++ right' =
      (walkDarts G (cyclicRunWalk G ell p')).drop m ++
        (walkDarts G (cyclicRunWalk G ell p')).take m)
    (harcs : left ++ right = left' ++ right') :
    p = p' := by
  apply cyclicRuns_eq_of_same_rotated_dart_word G ell m hell hm
  calc
    _ = left ++ right := hp.symm
    _ = left' ++ right' := harcs
    _ = _ := hp'

/-- The penultimate vertex of a run walk is the tail of its terminal dart. -/
theorem runWalk_penultimate (G : PhysicalGraph) : ∀ (k : ℕ) {d e : Dart G}
    (r : Run G k d e), (runWalk G k r).penultimate = tail G e := by
  intro k
  induction k with
  | zero =>
      intro d e r
      have hde : d = e := r.2
      subst e
      simp [runWalk]
  | succ k ih =>
      intro d e r
      rcases r with ⟨u, hdu, rest⟩
      change (SimpleGraph.Walk.cons (dart_adj G d)
        ((runWalk G k rest).copy hdu.2.1.symm rfl)).penultimate = tail G e
      have hnon : ¬ ((runWalk G k rest).copy hdu.2.1.symm rfl).Nil := by
        apply (SimpleGraph.Walk.not_nil_iff_lt_length).2
        simp [SimpleGraph.Walk.length_copy, runWalk_length]
      rw [SimpleGraph.Walk.penultimate_cons_of_not_nil _ _ hnon]
      have hcopy : ((runWalk G k rest).copy hdu.2.1.symm rfl).penultimate =
          (runWalk G k rest).penultimate := by
        simp [SimpleGraph.Walk.penultimate]
      rw [hcopy]
      exact ih rest

/-- The cyclic seam condition on a dart run rules out a vertex reversal
between the last and first steps of its associated closed walk. -/
theorem cyclicRunWalk_seam_no_return (G : PhysicalGraph) (ell : ℕ)
    (p : Erdos1016.Proof.CyclicRunCollisionSlice.CyclicRuns G ell) :
    (cyclicRunWalk G ell p).snd ≠ (cyclicRunWalk G ell p).penultimate := by
  have hseam : Next G p.1.1.2.1 p.1.1.1 := p.2
  unfold cyclicRunWalk
  simp only [ShortWalks.snd_copy, SimpleGraph.Walk.length_copy,
    SimpleGraph.Walk.getVert_copy, runWalk_snd, runWalk_penultimate]
  exact next_no_return G hseam

/-- A non-cycle member of the paper's cyclic-run slice has an explicit
repeated pair in its cyclic support list. -/
theorem cyclicRun_exists_repeated_support_indices
    (G : PhysicalGraph) (ell : ℕ) (hell : 0 < ell)
    (p : CyclicRuns G ell)
    (hbad : ¬ (cyclicRunWalk G ell p).IsCycle) :
    ∃ i j : Fin (cyclicRunWalk G ell p).support.tail.length,
      i ≠ j ∧
        (cyclicRunWalk G ell p).support.tail.get i =
          (cyclicRunWalk G ell p).support.tail.get j := by
  have hnonil : cyclicRunWalk G ell p ≠ SimpleGraph.Walk.nil := by
    intro hnil
    have hlen := cyclicRunWalk_length G ell hell p
    rw [hnil] at hlen
    simp at hlen
    omega
  exact exists_repeated_support_indices_of_not_cycle
    (cyclicRunWalk G ell p) (cyclicRunWalk_reduced G ell p) hnonil hbad



/-- The selected reduced arcs serialize as one cyclic rotation of the
original oriented edge word. The offset `m` is the number of initial darts
removed from the chosen rooting. -/
theorem cyclicRun_exists_rotated_dart_arcs_of_not_cycle
    (G : PhysicalGraph) (ell : ℕ) (hell : 0 < ell)
    (p : CyclicRuns G ell)
    (hbad : ¬ (cyclicRunWalk G ell p).IsCycle) :
    ∃ m : ℕ, ∃ a : G.Vertex, ∃ q r : G.toSimpleGraph.Walk a a,
      0 < m ∧ m ≤ ell ∧ ShortWalks.Reduced q ∧ ShortWalks.Reduced r ∧
        0 < q.length ∧ 0 < r.length ∧ q.length + r.length = ell ∧
        walkDarts G (q.append r) =
          (walkDarts G (cyclicRunWalk G ell p)).drop m ++
            (walkDarts G (cyclicRunWalk G ell p)).take m := by
  obtain ⟨i, j, hne, hrep⟩ := cyclicRun_exists_repeated_support_indices G ell hell p hbad
  rcases lt_or_gt_of_ne (Fin.val_ne_of_ne hne) with hij | hji
  · obtain ⟨q, r, hqlen, hrlen, hqr, hrr, hqpos, hrpos, htotal, hrotate⟩ :=
      closed_arcs_of_repeated_support_indices
        (cyclicRunWalk G ell p) i j (cyclicRunWalk_reduced G ell p)
        (cyclicRunWalk_seam_no_return G ell p) hij hrep
    let m := i.val + 1
    have hmpos : 0 < m := by dsimp [m]; omega
    have htail : (cyclicRunWalk G ell p).support.tail.length = ell := by
      simpa [SimpleGraph.Walk.length_support] using
        cyclicRunWalk_length G ell hell p
    have hmle : m ≤ ell := by
      dsimp [m]
      omega
    have hrotDarts : walkDarts G (q.append r) =
        (walkDarts G (cyclicRunWalk G ell p)).drop m ++
          (walkDarts G (cyclicRunWalk G ell p)).take m := by
      calc
        _ = walkDarts G (((cyclicRunWalk G ell p).drop m).append
              ((cyclicRunWalk G ell p).take m)) := congrArg (walkDarts G) hrotate
        _ = walkDarts G ((cyclicRunWalk G ell p).drop m) ++
              walkDarts G ((cyclicRunWalk G ell p).take m) :=
            walkDarts_append G _ _
        _ = _ := by rw [walkDarts_drop_at_index, walkDarts_take_at_index]
    refine ⟨m, _, q, r, hmpos, hmle, hqr, hrr, hqpos, hrpos, ?_, hrotDarts⟩
    simpa [cyclicRunWalk_length G ell hell p] using htotal

  · obtain ⟨q, r, hqlen, hrlen, hqr, hrr, hqpos, hrpos, htotal, hrotate⟩ :=
      closed_arcs_of_repeated_support_indices
        (cyclicRunWalk G ell p) j i (cyclicRunWalk_reduced G ell p)
        (cyclicRunWalk_seam_no_return G ell p) hji hrep.symm
    let m := j.val + 1
    have hmpos : 0 < m := by dsimp [m]; omega
    have htail : (cyclicRunWalk G ell p).support.tail.length = ell := by
      simpa [SimpleGraph.Walk.length_support] using
        cyclicRunWalk_length G ell hell p
    have hmle : m ≤ ell := by
      dsimp [m]
      omega
    have hrotDarts : walkDarts G (q.append r) =
        (walkDarts G (cyclicRunWalk G ell p)).drop m ++
          (walkDarts G (cyclicRunWalk G ell p)).take m := by
      calc
        _ = walkDarts G (((cyclicRunWalk G ell p).drop m).append
              ((cyclicRunWalk G ell p).take m)) := congrArg (walkDarts G) hrotate
        _ = walkDarts G ((cyclicRunWalk G ell p).drop m) ++
              walkDarts G ((cyclicRunWalk G ell p).take m) :=
            walkDarts_append G _ _
        _ = _ := by rw [walkDarts_drop_at_index, walkDarts_take_at_index]
    refine ⟨m, _, q, r, hmpos, hmle, hqr, hrr, hqpos, hrpos, ?_, hrotDarts⟩
    simpa [cyclicRunWalk_length G ell hell p] using htotal





end Erdos1016.Proof.CyclicRunCollisionGeometry
end
