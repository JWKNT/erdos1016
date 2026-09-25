import Erdos1016.Nonbacktracking.Girth.CollisionGeometry
import Erdos1016.Nonbacktracking.Walks.SplitRunCoordinates
import Erdos1016.Cycles.Counting.CollisionSplitCodes

set_option autoImplicit false

noncomputable section
namespace Erdos1016.Proof.CollisionTailReconstruction

open Erdos1016.Nonbacktracking
open Erdos1016.Proof.WalkPrefix
open Erdos1016.Proof.CollisionSliceInstantiation
open Erdos1016.Proof.CyclicRunCollisionGeometry
open Erdos1016.Proof.CyclicRunCollisionSlice
open Erdos1016.Proof.CollisionSplitCodes

variable (G : PhysicalGraph)

/-- The endpoint-run representation of a positive reduced closed walk keeps
the actual root vertex as well as its dart serialization. -/
theorem reduced_closed_walk_has_rooted_endpoint_run {base : G.Vertex}
    (p : G.toSimpleGraph.Walk base base) (hp : ShortWalks.Reduced p)
    (hpos : 0 < p.length) :
    ∃ r : ClosedEndpointRuns (G := G) (p.length - 1),
      runDarts G (p.length - 1) r.1.2.2 = walkDarts G p ∧
      tail G r.1.1 = base ∧ head G r.1.2.1 = base := by
  obtain ⟨d, e, htail, _, _, hhead, r, hr⟩ :=
    reduced_walk_has_dart_run G p hp hpos
  refine ⟨⟨⟨d, e, r⟩, ?_⟩, hr, htail, hhead⟩
  change tail G d = head G e
  exact htail.trans hhead.symm

private theorem dropFirstRun_terminal {n : ℕ} (hn : 0 < n)
    {d e : Dart G} (r : Run G n d e) :
    (dropFirstRun G hn r).2.1 = e := by
  cases n with
  | zero => omega
  | succ k => cases r; rfl

private theorem runDarts_dropFirstRun {n : ℕ} (hn : 0 < n)
    {d e : Dart G} (r : Run G n d e) :
    runDarts G (n - 1) (dropFirstRun G hn r).2.2 =
      (runDarts G n r).tail := by
  cases n with
  | zero => omega
  | succ k => cases r <;> simp [dropFirstRun, runDarts]



private theorem dropFirstRun_first {n : ℕ} (hn : 0 < n)
    {d e : Dart G} (r : Run G n d e) :
    Next G d (dropFirstRun G hn r).1 := by
  cases n with
  | zero => omega
  | succ k =>
      rcases r with ⟨u, h, rest⟩
      change Next G d u
      exact h.2

def closedRunSplit {s b : ℕ} (hsb : s < b) {d e : Dart G}
    (r : Run G (b - 1) d e) :=
  splitRun G (Nat.sub_le_sub_right (Nat.le_of_lt hsb) 1) r

def closedRunRemainder {s b : ℕ} (hs : 0 < s) (hsb : s < b) {d e : Dart G}
    (r : Run G (b - 1) d e) :
    Run G (b - s) (closedRunSplit G hsb r).1 e := by
  have hs' : s - 1 + 1 = s := Nat.sub_add_cancel (by omega)
  have hsum : 1 + (s - 1) = s := by omega
  have hlen : (b - 1) - (s - 1) = b - s := by
    rw [Nat.sub_sub, hsum]
  exact hlen ▸ (closedRunSplit G hsb r).2.2

private theorem closedRunRemainder_darts {s b : ℕ} (hs : 0 < s)
    (hsb : s < b) {d e : Dart G} (r : Run G (b - 1) d e) :
    runDarts G (b - s) (closedRunRemainder G hs hsb r) =
      runDarts G ((b - 1) - (s - 1)) (closedRunSplit G hsb r).2.2 := by
  unfold closedRunRemainder
  have hlen : (b - 1) - (s - 1) = b - s := by
    have hsum : 1 + (s - 1) = s := by omega
    rw [Nat.sub_sub, hsum]
  exact runDarts_cast hlen (closedRunSplit G hsb r).2.2

def closedRunDroppedTail {s b : ℕ} (hs : 0 < s) (hsb : s < b)
    {d e : Dart G} (r : Run G (b - 1) d e) : AllRuns G (b - s - 1) :=
  dropFirstRun G (by omega : 0 < b - s) (closedRunRemainder G hs hsb r)

/-- Reverse the final `b-s` darts of a closed run. `splitRun` shares the
boundary dart, and `dropFirstRun` removes that shared dart before reversal. -/
def reverseClosedRunTail (s b : ℕ) (hs : 0 < s) (hsb : s < b) {base : G.Vertex}
    {d e : Dart G} (r : Run G (b - 1) d e) (he : head G e = base) :
    StartingRuns G (b - s - 1) base := by
  let dropped := closedRunDroppedTail G hs hsb r
  let rev : Run G (b - s - 1) (reverse G dropped.2.1) (reverse G dropped.1) :=
    reverseRun dropped.2.2
  refine ⟨⟨reverse G dropped.2.1, ?_⟩, ⟨reverse G dropped.1, rev⟩⟩
  have hterm : dropped.2.1 = e := by
    exact dropFirstRun_terminal G (by omega) (closedRunRemainder G hs hsb r)
  simpa [hterm, he] using tail_reverse G e

/-- The suffix extraction equation at the level of dart words. -/
theorem reverseClosedRunTail_darts (s b : ℕ) (hs : 0 < s) (hsb : s < b)
    {base : G.Vertex} {d e : Dart G} (r : Run G (b - 1) d e)
    (he : head G e = base) :
    let dropped := closedRunDroppedTail G hs hsb r
    runDarts G (b - s - 1) (reverseClosedRunTail G s b hs hsb r he).2.2 =
      (runDarts G (b - s - 1) dropped.2.2).reverse.map (reverse G) := by
  dsimp
  simp [reverseClosedRunTail, closedRunDroppedTail, runDarts_reverseRun]



/-- The cyclic split data retain one shared vertex, so the short and long
arc run encodings can be paired at that root. -/
theorem cyclicRun_exists_rooted_run_arcs_of_not_cycle
    (G : PhysicalGraph) (ell s D : ℕ) (hell : 0 < ell)
    (hg : ShortWalks.GirthGreater G.toSimpleGraph D)
    (hshort : 2 * s ≤ D) (hs : 0 < s)
    (p : CyclicRuns G ell)
    (hbad : ¬ (cyclicRunWalk G ell p).IsCycle) :
    ∃ m a b : ℕ, ∃ base : G.Vertex,
      ∃ u : ClosedEndpointRuns (G := G) (a - 1),
      ∃ v : ClosedEndpointRuns (G := G) (b - 1),
        0 < m ∧ m ≤ ell ∧ D < a ∧ D < b ∧ s < b ∧ a + b = ell ∧
        tail G u.1.1 = base ∧ head G u.1.2.1 = base ∧
        tail G v.1.1 = base ∧ head G v.1.2.1 = base ∧
        runDarts G (a - 1) u.1.2.2 ++ runDarts G (b - 1) v.1.2.2 =
          (walkDarts G (cyclicRunWalk G ell p)).drop m ++
            (walkDarts G (cyclicRunWalk G ell p)).take m := by
  obtain ⟨m, base, q, r, hmpos, hmle, hqred, hrred, hqpos, hrpos,
      hsum, hrotate⟩ := cyclicRun_exists_rotated_dart_arcs_of_not_cycle
        G ell hell p hbad
  have hqgirth : D < q.length :=
    reduced_closed_nonempty_length_gt (G := G.toSimpleGraph) D hg q hqred
      ((SimpleGraph.Walk.not_nil_iff_lt_length).2 hqpos)
  have hrgirth : D < r.length :=
    reduced_closed_nonempty_length_gt (G := G.toSimpleGraph) D hg r hrred
      ((SimpleGraph.Walk.not_nil_iff_lt_length).2 hrpos)
  obtain ⟨u, hu, huTail, huHead⟩ :=
    reduced_closed_walk_has_rooted_endpoint_run G q hqred hqpos
  obtain ⟨v, hv, hvTail, hvHead⟩ :=
    reduced_closed_walk_has_rooted_endpoint_run G r hrred hrpos
  have hsD : s ≤ D := by omega
  have hsb : s < r.length := hsD.trans_lt hrgirth
  refine ⟨m, q.length, r.length, base, u, v, hmpos, hmle, hqgirth, hrgirth,
    hsb, hsum, huTail, huHead, hvTail, hvHead, ?_⟩
  calc
    _ = walkDarts G q ++ walkDarts G r := by rw [hu, hv]
    _ = _ := by rw [walkDarts_append] at hrotate; exact hrotate

/-- Finite collision code: root offset, first closed arc, and reversed tail
of the complementary arc. -/
abbrev CyclicCollisionCode (G : PhysicalGraph) (ell s : ℕ) :=
  Σ offset : Fin ell, Σ shortLength : Fin ell,
      Σ longLength : {b : Fin ell // shortLength.val + b.val = ell ∧ s < b.val},
        Σ shortArc : ClosedEndpointRuns (G := G) (shortLength.val - 1),
        StartingRuns G (longLength.1.val - s - 1) (tail G shortArc.1.1)

/-- Translate the explicit long-length code into the positioned split-code
fiber used by the arithmetic estimate. -/
def toPositionedSplitCode (G : PhysicalGraph) (ell s : ℕ)
    (c : CyclicCollisionCode G ell s)
    (hshort : 1 ≤ c.2.1.val) :
    Σ a : SplitLength ell s, PositionedSplitCodeFiber G ell s a := by
  let a : SplitLength ell s := ⟨c.2.1, by
    constructor
    · exact hshort
    · have hsum := c.2.2.1.2.1
      have htail := c.2.2.1.2.2
      omega⟩
  have hlen : ell - a.val.val - s - 1 = c.2.2.1.1.val - s - 1 := by
    have hsum := c.2.2.1.2.1
    dsimp [a]
    omega
  let suffix : StartingRuns G (ell - a.val.val - s - 1)
      (tail G c.2.2.2.1.1.1) := hlen.symm ▸ c.2.2.2.2
  exact ⟨a, ⟨c.1, ⟨c.2.2.2.1, suffix⟩⟩⟩

noncomputable instance cyclicCollisionCodeFintype (G : PhysicalGraph)
    (ell s : ℕ) : Fintype (CyclicCollisionCode G ell s) := by
  classical
  letI : Fintype (Dart G) := inferInstance
  letI (k : ℕ) (d e : Dart G) : Fintype (Run G k d e) := Fintype.ofFinite _
  letI (k : ℕ) : Fintype (AllRuns G k) := inferInstance
  letI (a : Fin ell) : Fintype (ClosedEndpointRuns (G := G) (a.val - 1)) :=
    Fintype.subtype (Finset.univ.filter fun x : AllRuns G (a.val - 1) =>
      tail G x.1 = head G x.2.1)
      (by intro x; simp [ClosedEndpointRuns])
  letI (a : Fin ell) (b : {b : Fin ell // a.val + b.val = ell ∧ s < b.val}) :
      ∀ u : ClosedEndpointRuns (G := G) (a.val - 1),
        Fintype (StartingRuns G (b.1.val - s - 1) (tail G u.1.1)) := by
    intro u
    exact Fintype.ofFinite _
  infer_instance

/-- Every bad cyclic run has finite collision code data, together with its
full complementary arc and the word equation witnessed by the split. -/
theorem exists_cyclicCollisionCode_realization
    (G : PhysicalGraph) (ell s D : ℕ) (hell : 0 < ell)
    (hg : ShortWalks.GirthGreater G.toSimpleGraph D)
    (hshort : 2 * s ≤ D) (hs : 0 < s)
    (p : CyclicRuns G ell)
    (hbad : ¬ (cyclicRunWalk G ell p).IsCycle) :
    ∃ c : CyclicCollisionCode G ell s,
      ∃ v : ClosedEndpointRuns (G := G) (c.2.2.1.1.val - 1),
        ∃ hroot : head G v.1.2.1 = tail G c.2.2.2.1.1.1,
          c.1.val + 1 ≤ ell ∧
          1 ≤ c.2.1.val ∧
          reverseClosedRunTail G s c.2.2.1.1.val hs
            c.2.2.1.2.2 v.1.2.2 hroot = c.2.2.2.2 ∧
          runDarts G (c.2.1.val - 1) c.2.2.2.1.1.2.2 ++
            runDarts G (c.2.2.1.1.val - 1) v.1.2.2 =
              (walkDarts G (cyclicRunWalk G ell p)).drop (c.1.val + 1) ++
                (walkDarts G (cyclicRunWalk G ell p)).take (c.1.val + 1) := by
  classical
  obtain ⟨m, a, b, base, u, v, hmpos, hmle, hqa, hrb, hsb, hsum,
      huTail, huHead, hvTail, hvHead, hword⟩ :=
    cyclicRun_exists_rooted_run_arcs_of_not_cycle G ell s D hell hg hshort hs p hbad
  let mf : Fin ell := ⟨m - 1, by omega⟩
  let af : Fin ell := ⟨a, by omega⟩
  let bf : Fin ell := ⟨b, by omega⟩
  let tBase := reverseClosedRunTail G s b hs hsb v.1.2.2 hvHead
  let t : StartingRuns G (b - s - 1) (tail G u.1.1) := huTail.symm ▸ tBase
  let code : CyclicCollisionCode G ell s :=
    ⟨mf, af, ⟨bf, hsum, hsb⟩, u, t⟩
  refine ⟨code, v, hvHead.trans huTail.symm, ?_, ?_, ?_, ?_⟩
  · dsimp [code, mf]
    omega
  · dsimp [code, af]
    omega
  · cases huTail
    simp [code, t, tBase, bf, reverseClosedRunTail]
  · have hmf : mf.val + 1 = m := by dsimp [mf]; omega
    simpa [code, mf, af, bf, hmf] using hword

/-- Equality of two reverse-tail codes recovers the entire dropped tail
after the shared boundary dart. -/
theorem droppedTail_eq_of_reverseClosedRunTail_eq
    (s b : ℕ) (hs : 0 < s) (hsb : s < b) {base : G.Vertex}
    {d₁ d₂ e₁ e₂ : Dart G} (r₁ : Run G (b - 1) d₁ e₁)
    (r₂ : Run G (b - 1) d₂ e₂)
    (he₁ : head G e₁ = base) (he₂ : head G e₂ = base)
    (hcode : reverseClosedRunTail G s b hs hsb r₁ he₁ =
      reverseClosedRunTail G s b hs hsb r₂ he₂) :
    closedRunDroppedTail G hs hsb r₁ = closedRunDroppedTail G hs hsb r₂ := by
  have hwords := congrArg
    (fun x : StartingRuns G (b - s - 1) base =>
      runDarts G (b - s - 1) x.2.2) hcode
  change runDarts G (b - s - 1)
      (reverseClosedRunTail G s b hs hsb r₁ he₁).2.2 =
    runDarts G (b - s - 1)
      (reverseClosedRunTail G s b hs hsb r₂ he₂).2.2 at hwords
  rw [reverseClosedRunTail_darts G s b hs hsb r₁ he₁,
    reverseClosedRunTail_darts G s b hs hsb r₂ he₂] at hwords
  have hmaps :
      (runDarts G (b - s - 1)
        (closedRunDroppedTail G hs hsb r₁).2.2).reverse.map (reverse G) =
      (runDarts G (b - s - 1)
        (closedRunDroppedTail G hs hsb r₂).2.2).reverse.map (reverse G) := by
    simpa using hwords
  have hrev :
      (runDarts G (b - s - 1)
        (closedRunDroppedTail G hs hsb r₁).2.2).reverse =
      (runDarts G (b - s - 1)
        (closedRunDroppedTail G hs hsb r₂).2.2).reverse :=
    (List.map_injective_iff.mpr (reverseEquiv G).injective) hmaps
  exact allRuns_darts_injective G (b - s - 1)
    (List.reverse_injective hrev)

/-- Once the first `s` darts are uniquely determined by their endpoints
under girth, the reverse-tail code reconstructs the entire closed run. -/
theorem allRuns_eq_of_same_reverseClosedRunTail
    (D b s : ℕ) (hs : 0 < s) (hsb : s < b)
    (hg : ShortWalks.GirthGreater G.toSimpleGraph D)
    (hshort : 2 * s ≤ D) {base : G.Vertex}
    {d₁ d₂ e₁ e₂ : Dart G} (r₁ : Run G (b - 1) d₁ e₁)
    (r₂ : Run G (b - 1) d₂ e₂)
    (hd₁ : tail G d₁ = base) (hd₂ : tail G d₂ = base)
    (he₁ : head G e₁ = base) (he₂ : head G e₂ = base)
    (hcode : reverseClosedRunTail G s b hs hsb r₁ he₁ =
      reverseClosedRunTail G s b hs hsb r₂ he₂) :
    (⟨d₁, e₁, r₁⟩ : AllRuns G (b - 1)) = ⟨d₂, e₂, r₂⟩ := by
  let z₁ := closedRunSplit G hsb r₁
  let z₂ := closedRunSplit G hsb r₂
  let rest₁ := closedRunRemainder G hs hsb r₁
  let rest₂ := closedRunRemainder G hs hsb r₂
  let t₁ := closedRunDroppedTail G hs hsb r₁
  let t₂ := closedRunDroppedTail G hs hsb r₂
  have ht : t₁ = t₂ := by
    exact droppedTail_eq_of_reverseClosedRunTail_eq G s b hs hsb r₁ r₂ he₁ he₂ hcode
  have hnext₁ : Next G z₁.1 t₁.1 := by
    simpa [z₁, t₁, rest₁, closedRunDroppedTail] using
      dropFirstRun_first G (by omega : 0 < b - s) rest₁
  have hnext₂ : Next G z₂.1 t₂.1 := by
    simpa [z₂, t₂, rest₂, closedRunDroppedTail] using
      dropFirstRun_first G (by omega : 0 < b - s) rest₂
  have hboundary : head G z₁.1 = head G z₂.1 := by
    calc
      head G z₁.1 = tail G t₁.1 := hnext₁.1
      _ = tail G t₂.1 := by rw [ht]
      _ = head G z₂.1 := hnext₂.1.symm
  have hprefixEndpoints :
      endpoints G (s - 1) ⟨d₁, z₁.1, z₁.2.1⟩ =
        endpoints G (s - 1) ⟨d₂, z₂.1, z₂.2.1⟩ := by
    apply Prod.ext
    · exact hd₁.trans hd₂.symm
    · exact hboundary
  have hprefix :
      (⟨d₁, z₁.1, z₁.2.1⟩ : AllRuns G (s - 1)) =
        ⟨d₂, z₂.1, z₂.2.1⟩ :=
    endpoints_injective_of_girth G D (s - 1) hg (by omega) hprefixEndpoints
  have hprefixDarts : runDarts G (s - 1) z₁.2.1 =
      runDarts G (s - 1) z₂.2.1 := by
    exact congrArg (fun x : AllRuns G (s - 1) => runDarts G (s - 1) x.2.2) hprefix
  have htailDarts : (runDarts G (b - s) rest₁).tail =
      (runDarts G (b - s) rest₂).tail := by
    have hdropDarts := congrArg (fun x : AllRuns G (b - s - 1) =>
      runDarts G (b - s - 1) x.2.2) ht
    have hleft := runDarts_dropFirstRun G (by omega : 0 < b - s) rest₁
    have hright := runDarts_dropFirstRun G (by omega : 0 < b - s) rest₂
    exact hleft.symm.trans (hdropDarts.trans hright)
  have hfullDarts : runDarts G (b - 1) r₁ = runDarts G (b - 1) r₂ := by
    have hsplit₁ := runDarts_splitRun G (by omega : s - 1 ≤ b - 1) r₁
    have hsplit₂ := runDarts_splitRun G (by omega : s - 1 ≤ b - 1) r₂
    have hsplit₁' : runDarts G (b - 1) r₁ = runDarts G (s - 1) z₁.2.1 ++
        (runDarts G (b - s) rest₁).tail := by
      rw [closedRunRemainder_darts G hs hsb r₁]
      simpa [z₁, closedRunSplit] using hsplit₁
    have hsplit₂' : runDarts G (b - 1) r₂ = runDarts G (s - 1) z₂.2.1 ++
        (runDarts G (b - s) rest₂).tail := by
      rw [closedRunRemainder_darts G hs hsb r₂]
      simpa [z₂, closedRunSplit] using hsplit₂
    calc
      runDarts G (b - 1) r₁ = runDarts G (s - 1) z₁.2.1 ++
          (runDarts G (b - s) rest₁).tail := hsplit₁'
      _ = runDarts G (s - 1) z₂.2.1 ++
          (runDarts G (b - s) rest₂).tail := by rw [hprefixDarts, htailDarts]
      _ = runDarts G (b - 1) r₂ := by
        exact hsplit₂'.symm
  exact allRuns_darts_injective G (b - 1) hfullDarts

/-- A fixed collision code can represent at most one rooted cyclic run.
The short arc is stored in the code, while the girth-unique prefix of the
long arc is recovered from its encoded reverse tail. -/
theorem cyclicRuns_eq_of_common_collision_realization
    (G : PhysicalGraph) (ell s D : ℕ) (hs : 0 < s)
    (hg : ShortWalks.GirthGreater G.toSimpleGraph D)
    (hshort : 2 * s ≤ D)
    {p p' : CyclicRuns G ell} (hell : 0 < ell)
    (c : CyclicCollisionCode G ell s)
    (v v' : ClosedEndpointRuns (G := G) (c.2.2.1.1.val - 1))
    (hr : head G v.1.2.1 = tail G c.2.2.2.1.1.1)
    (hr' : head G v'.1.2.1 = tail G c.2.2.2.1.1.1)
    (hcode : reverseClosedRunTail G s c.2.2.1.1.val hs
      c.2.2.1.2.2 v.1.2.2 hr = c.2.2.2.2)
    (hcode' : reverseClosedRunTail G s c.2.2.1.1.val hs
      c.2.2.1.2.2 v'.1.2.2 hr' = c.2.2.2.2)
    (hword : runDarts G (c.2.1.val - 1) c.2.2.2.1.1.2.2 ++
      runDarts G (c.2.2.1.1.val - 1) v.1.2.2 =
        (walkDarts G (cyclicRunWalk G ell p)).drop (c.1.val + 1) ++
          (walkDarts G (cyclicRunWalk G ell p)).take (c.1.val + 1))
    (hword' : runDarts G (c.2.1.val - 1) c.2.2.2.1.1.2.2 ++
      runDarts G (c.2.2.1.1.val - 1) v'.1.2.2 =
        (walkDarts G (cyclicRunWalk G ell p')).drop (c.1.val + 1) ++
          (walkDarts G (cyclicRunWalk G ell p')).take (c.1.val + 1)) :
    p = p' := by
  have htails := hcode.trans hcode'.symm
  have hrun : v.1 = v'.1 :=
    allRuns_eq_of_same_reverseClosedRunTail (G := G) D
      c.2.2.1.1.val s hs c.2.2.1.2.2 hg hshort
      (base := tail G c.2.2.2.1.1.1)
      (d₁ := v.1.1) (d₂ := v'.1.1)
      (e₁ := v.1.2.1) (e₂ := v'.1.2.1)
      (r₁ := v.1.2.2) (r₂ := v'.1.2.2)
      (hd₁ := v.2.trans hr) (hd₂ := v'.2.trans hr')
      hr hr' htails
  have harcs :
      runDarts G (c.2.1.val - 1) c.2.2.2.1.1.2.2 ++
        runDarts G (c.2.2.1.1.val - 1) v.1.2.2 =
      runDarts G (c.2.1.val - 1) c.2.2.2.1.1.2.2 ++
        runDarts G (c.2.2.1.1.val - 1) v'.1.2.2 := by
    rw [hrun]
  apply cyclicRuns_eq_of_equal_arc_run_words G ell (c.1.val + 1) hell
    (by have := c.2.1.isLt; omega) hword hword' harcs



/-- Select one collision code for each nonsimple cyclic run. -/
noncomputable def chosenCyclicCollisionCode
    (G : PhysicalGraph) (ell s D : ℕ) (hell : 0 < ell)
    (hg : ShortWalks.GirthGreater G.toSimpleGraph D)
    (hshort : 2 * s ≤ D) (hs : 0 < s)
    (p : NonsimpleCyclicRuns G ell) : CyclicCollisionCode G ell s :=
  Classical.choose (exists_cyclicCollisionCode_realization G ell s D hell hg
    hshort hs p.1 p.2)

theorem chosenCyclicCollisionCode_spec
    (G : PhysicalGraph) (ell s D : ℕ) (hell : 0 < ell)
    (hg : ShortWalks.GirthGreater G.toSimpleGraph D)
    (hshort : 2 * s ≤ D) (hs : 0 < s)
    (p : NonsimpleCyclicRuns G ell) :
    ∃ v : ClosedEndpointRuns (G := G)
        ((chosenCyclicCollisionCode G ell s D hell hg hshort hs p).2.2.1.1.val - 1),
      ∃ hroot : head G v.1.2.1 =
        tail G (chosenCyclicCollisionCode G ell s D hell hg hshort hs p).2.2.2.1.1.1,
        (chosenCyclicCollisionCode G ell s D hell hg hshort hs p).1.val + 1 ≤ ell ∧
        1 ≤ (chosenCyclicCollisionCode G ell s D hell hg hshort hs p).2.1.val ∧
        reverseClosedRunTail G s
          (chosenCyclicCollisionCode G ell s D hell hg hshort hs p).2.2.1.1.val hs
          (chosenCyclicCollisionCode G ell s D hell hg hshort hs p).2.2.1.2.2
          v.1.2.2 hroot =
            (chosenCyclicCollisionCode G ell s D hell hg hshort hs p).2.2.2.2 ∧
        runDarts G
            ((chosenCyclicCollisionCode G ell s D hell hg hshort hs p).2.1.val - 1)
            (chosenCyclicCollisionCode G ell s D hell hg hshort hs p).2.2.2.1.1.2.2 ++
          runDarts G
            ((chosenCyclicCollisionCode G ell s D hell hg hshort hs p).2.2.1.1.val - 1)
            v.1.2.2 =
          (walkDarts G (cyclicRunWalk G ell p.1)).drop
              ((chosenCyclicCollisionCode G ell s D hell hg hshort hs p).1.val + 1) ++
            (walkDarts G (cyclicRunWalk G ell p.1)).take
              ((chosenCyclicCollisionCode G ell s D hell hg hshort hs p).1.val + 1) := by
  exact Classical.choose_spec (exists_cyclicCollisionCode_realization G ell s D hell hg
    hshort hs p.1 p.2)

/-- The deterministic collision-code selection is injective. -/
theorem chosenCyclicCollisionCode_injective
    (G : PhysicalGraph) (ell s D : ℕ) (hell : 0 < ell)
    (hg : ShortWalks.GirthGreater G.toSimpleGraph D)
    (hshort : 2 * s ≤ D) (hs : 0 < s)
    {p p' : NonsimpleCyclicRuns G ell}
    (hcode : chosenCyclicCollisionCode G ell s D hell hg hshort hs p =
      chosenCyclicCollisionCode G ell s D hell hg hshort hs p') : p = p' := by
  have hp := chosenCyclicCollisionCode_spec G ell s D hell hg hshort hs p
  have hp' := chosenCyclicCollisionCode_spec G ell s D hell hg hshort hs p'
  rw [← hcode] at hp'
  rcases hp with ⟨v, hr, _, _, hc, hw⟩
  rcases hp' with ⟨v', hr', _, _, hc', hw'⟩
  have hruns := cyclicRuns_eq_of_common_collision_realization G ell s D hs hg
    hshort hell (chosenCyclicCollisionCode G ell s D hell hg hshort hs p)
    v v' hr hr' hc hc' hw hw'
  exact Subtype.ext hruns

end Erdos1016.Proof.CollisionTailReconstruction
end
