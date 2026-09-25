import Erdos1016.Nonbacktracking.Walks.RunCountBasics
import Erdos1016.Nonbacktracking.Walks.ShortPathUniqueness

set_option autoImplicit false

/-!
# From labelled dart runs to ordinary reduced vertex walks

Every k-transition Run becomes an actual vertex walk of k+1 graph edges.
A serialization by physical darts proves that no runs are silently
identified. Hence the girth theorem applies to the SAME endpoint map whose
cardinality enters the entropy argument.
-/

noncomputable section
namespace Erdos1016.Nonbacktracking
local instance runGeometryDecidable (p : Prop) : Decidable p := Classical.propDecidable p

variable (G : PhysicalGraph)

/-- Simplicity of the physical graph makes an oriented edge unique. -/
theorem dart_eq_of_endpoints {d e : Dart G}
    (ht : tail G d = tail G e) (hh : head G d = head G e) : d = e := by
  rcases d with ⟨i, b⟩
  rcases e with ⟨j, c⟩
  cases b <;> cases c
  · simp only [tail, head, Bool.false_eq_true, if_false] at ht hh
    have he : i = j := G.simple i j (Or.inl ⟨hh, ht⟩)
    subst j
    rfl
  · simp only [tail, head, Bool.false_eq_true, if_false, if_true] at ht hh
    have he : i = j := G.simple i j (Or.inr ⟨hh, ht⟩)
    subst j
    exact False.elim (G.noLoops i hh)
  · simp only [tail, head, Bool.false_eq_true, if_false, if_true] at ht hh
    have he : i = j := G.simple i j (Or.inr ⟨ht, hh⟩)
    subst j
    exact False.elim (G.noLoops i ht)
  · simp only [tail, head, if_true] at ht hh
    have he : i = j := G.simple i j (Or.inl ⟨ht, hh⟩)
    subst j
    rfl



/-- Each physical dart is an actual adjacency, not a chosen virtual edge. -/
theorem dart_adj (d : Dart G) : G.toSimpleGraph.Adj (tail G d) (head G d) := by
  rcases d with ⟨e, b⟩
  cases b
  · exact ⟨e, one_ne_zero, Or.inr ⟨rfl, rfl⟩⟩
  · exact ⟨e, one_ne_zero, Or.inl ⟨rfl, rfl⟩⟩

theorem next_no_return {d e : Dart G} (h : Next G d e) : head G e ≠ tail G d := by
  intro he
  apply h.2
  apply dart_eq_of_endpoints G
  · simpa using h.1.symm
  · simpa using he

private theorem exists_dart_of_adj {u v : G.Vertex} (h : G.toSimpleGraph.Adj u v) :
    ∃ d : Dart G, tail G d = u ∧ head G d = v := by
  rcases h with ⟨e, _, h | h⟩
  · exact ⟨(e, true), h⟩
  · exact ⟨(e, false), h.2, h.1⟩

/-- The unique oriented physical edge underlying an actual adjacency. -/
def dartOfAdj {u v : G.Vertex} (h : G.toSimpleGraph.Adj u v) : Dart G :=
  Classical.choose (exists_dart_of_adj G h)

@[simp] theorem tail_dartOfAdj {u v : G.Vertex} (h : G.toSimpleGraph.Adj u v) :
    tail G (dartOfAdj G h) = u := (Classical.choose_spec (exists_dart_of_adj G h)).1

@[simp] theorem head_dartOfAdj {u v : G.Vertex} (h : G.toSimpleGraph.Adj u v) :
    head G (dartOfAdj G h) = v := (Classical.choose_spec (exists_dart_of_adj G h)).2

@[simp] theorem dartOfAdj_dart_adj (d : Dart G) : dartOfAdj G (dart_adj G d) = d :=
  dart_eq_of_endpoints G (tail_dartOfAdj G _) (head_dartOfAdj G _)

/-- Exact oriented-edge serialization of an ordinary vertex walk. -/
def walkDarts : {u v : G.Vertex} → G.toSimpleGraph.Walk u v → List (Dart G)
  | _, _, .nil => []
  | _, _, .cons h p => dartOfAdj G h :: walkDarts p

@[simp] theorem walkDarts_copy {u v u' v' : G.Vertex}
    (p : G.toSimpleGraph.Walk u v) (hu : u = u') (hv : v = v') :
    walkDarts G (p.copy hu hv) = walkDarts G p := by
  subst u'
  subst v'
  rfl

/-- A Run contains its initial dart, followed by k transitions. -/
def runDarts : (k : ℕ) → {d e : Dart G} → Run G k d e → List (Dart G)
  | 0, d, _, _ => [d]
  | k + 1, d, _, r => d :: runDarts k r.2.2

/-- The literal vertex walk corresponding to an actual run. -/
def runWalk : (k : ℕ) → {d e : Dart G} → Run G k d e →
    G.toSimpleGraph.Walk (tail G d) (head G e)
  | 0, d, _, r =>
      (SimpleGraph.Walk.cons (dart_adj G d) SimpleGraph.Walk.nil).copy rfl
        (congrArg (head G) r.2)
  | k + 1, d, _, r =>
      .cons (dart_adj G d)
        ((runWalk k r.2.2).copy r.2.1.2.1.symm rfl)

@[simp] theorem runWalk_length (k : ℕ) {d e : Dart G} (r : Run G k d e) :
    (runWalk G k r).length = k + 1 := by
  induction k generalizing d e with
  | zero => simp [runWalk]
  | succ k ih => simp [runWalk, ih, Nat.add_assoc]

@[simp] theorem runWalk_snd (k : ℕ) {d e : Dart G} (r : Run G k d e) :
    (runWalk G k r).snd = head G d := by
  cases k with
  | zero =>
      have h : d = e := r.2
      subst e
      rfl
  | succ k =>
      rcases r with ⟨u, h, r⟩
      change (SimpleGraph.Walk.cons (dart_adj G d)
        ((runWalk G k r).copy h.2.1.symm rfl)).snd = head G d
      exact SimpleGraph.Walk.snd_cons _ _

/-- Every actual dart run is reduced in the vertex-walk sense. -/
theorem runWalk_reduced (k : ℕ) {d e : Dart G} (r : Run G k d e) :
    ShortWalks.Reduced (runWalk G k r) := by
  induction k generalizing d e with
  | zero =>
      have h : d = e := r.2
      subst e
      simp [runWalk, ShortWalks.Reduced]
  | succ k ih =>
      rcases r with ⟨u, h, r⟩
      change ShortWalks.Reduced (.cons (dart_adj G d)
        ((runWalk G k r).copy h.2.1.symm rfl))
      refine ⟨(ShortWalks.reduced_copy _ _ _).2 (ih r), ?_⟩
      intro _
      change ¬((runWalk G k r).copy h.2.1.symm rfl).snd = tail G d
      rw [ShortWalks.snd_copy, runWalk_snd]
      exact next_no_return G h.2

@[simp] theorem walkDarts_runWalk (k : ℕ) {d e : Dart G} (r : Run G k d e) :
    walkDarts G (runWalk G k r) = runDarts G k r := by
  induction k generalizing d e with
  | zero =>
      have h : d = e := r.2
      subst e
      simp [runWalk, walkDarts, runDarts]
  | succ k ih =>
      rcases r with ⟨u, h, r⟩
      change dartOfAdj G (dart_adj G d) ::
        walkDarts G ((runWalk G k r).copy h.2.1.symm rfl) =
        d :: runDarts G k r
      rw [dartOfAdj_dart_adj, walkDarts_copy, ih]

/-- Every proof-relevant Run is determined by its physical dart list.
Flags carry no additional states: their proof fields are propositionally
irrelevant. Both endpoint darts are recovered from the list. -/
theorem allRuns_darts_injective (k : ℕ) :
    Function.Injective (fun p : AllRuns G k => runDarts G k p.2.2) := by
  induction k with
  | zero =>
      rintro ⟨d, e, r⟩ ⟨u, v, s⟩ heq
      have hre : d = e := r.2
      have hsv : u = v := s.2
      subst e
      subst v
      have hdu : d = u := by simpa [runDarts] using heq
      subst u
      have hrs : r = s := by
        apply Subtype.ext
        exact Subsingleton.elim _ _
      cases hrs
      rfl
  | succ k ih =>
      rintro ⟨d, e, ⟨u, h, r⟩⟩ ⟨d', e', ⟨u', h', r'⟩⟩ heq
      have hh := List.cons.inj heq
      have hd : d = d' := hh.1
      subst d'
      have hs : (⟨u, e, r⟩ : AllRuns G k) = ⟨u', e', r'⟩ := ih hh.2
      cases hs
      have hh : h = h' := by
        apply Subtype.ext
        exact Subsingleton.elim _ _
      cases hh
      rfl

/-- The hypothesis formerly left in `EntropyMoore` is now derived from
ordinary graph girth, with the correct k+1-edge length convention. -/
theorem endpoints_injective_of_girth (D k : ℕ)
    (hg : ShortWalks.GirthGreater G.toSimpleGraph D)
    (hshort : 2 * (k + 1) ≤ D) :
    Function.Injective (endpoints G k) := by
  intro p q he
  have ht : tail G p.1 = tail G q.1 := congrArg Prod.fst he
  have hh : head G p.2.1 = head G q.2.1 := congrArg Prod.snd he
  let wp := runWalk G k p.2.2
  let wq := (runWalk G k q.2.2).copy ht.symm hh.symm
  have hp : ShortWalks.Reduced wp := runWalk_reduced G k p.2.2
  have hq : ShortWalks.Reduced wq :=
    (ShortWalks.reduced_copy _ _ _).2 (runWalk_reduced G k q.2.2)
  have hl : wp.length + wq.length ≤ D := by
    simpa [wp, wq, two_mul] using hshort
  have hw : wp = wq := ShortWalks.reduced_walk_unique_of_girth D hg wp wq hp hq hl
  have hd := congrArg (fun w => walkDarts G w) hw
  apply allRuns_darts_injective G k
  simpa only [wp, wq, walkDarts_copy, walkDarts_runWalk] using hd

end Erdos1016.Nonbacktracking
