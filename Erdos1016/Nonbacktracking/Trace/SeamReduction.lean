import Erdos1016.Cycles.Counting.RootedRunEncoding

set_option autoImplicit false

noncomputable section
namespace Erdos1016.Nonbacktracking

variable {G : PhysicalGraph}
local instance seamStripDecidable (p : Prop) : Decidable p := Classical.propDecidable p



/-- Reverse a nonbacktracking run, including its transition proofs. -/
def reverseRun : ∀ {k : ℕ} {d e : Dart G}, Run G k d e →
    Run G k (reverse G e) (reverse G d)
  | 0, d, e, r => ⟨(), congrArg (reverse G) r.2.symm⟩
  | k + 1, d, e, r => by
      rcases r with ⟨u, hu, rest⟩
      exact run_append_step k (reverseRun rest)
        ((next_reverse G d u).mp hu.2)

theorem runDarts_reverseRun : ∀ {k : ℕ} {d e : Dart G}
    (r : Run G k d e),
    runDarts G k (reverseRun r) =
      (runDarts G k r).reverse.map (reverse G) := by
  intro k
  induction k with
  | zero =>
      intro d e r
      have hde : d = e := r.2
      subst e
      simp [reverseRun, runDarts]
  | succ k ih =>
      intro d e r
      rcases r with ⟨u, hu, rest⟩
      simp only [reverseRun]
      rw [run_append_step_darts, ih]
      simp [runDarts, List.map_append]









theorem runDarts_castStart (k : ℕ) {d d' e : Dart G}
    (hd : d = d') (r : Run G k d e) :
    runDarts G k (cast (congrArg (fun x : Dart G => Run G k x e) hd) r) =
      runDarts G k r := by
  cases hd
  rfl

/-- Strip the first dart and the reversed-seam last dart from a run whose
terminal dart is the reverse of its initial dart. The output retains the
entire middle as an ordinary run, with two fewer transitions. -/
def seamStrip (n : ℕ) {d : Dart G}
    (r : Run G (n + 2) d (reverse G d)) : AllRuns G n :=
  let rr := reverseRun r.2.2
  let hstart : reverse G (reverse G r.1) = r.1 := reverse_reverse G r.1
  ⟨r.1, reverse G rr.1,
    cast (congrArg (fun x : Dart G => Run G n x (reverse G rr.1)) hstart)
      (reverseRun rr.2.2)⟩

theorem seamStrip_darts (n : ℕ) {d : Dart G}
    (r : Run G (n + 2) d (reverse G d)) :
    runDarts G (n + 2) r =
      [d] ++ runDarts G n (seamStrip n r).2.2 ++ [reverse G d] := by
  rcases r with ⟨u, hu, rest⟩
  let rr := reverseRun rest
  have hcore : runDarts G n (seamStrip n ⟨u, hu, rest⟩).2.2 =
      runDarts G n (reverseRun rr.2.2) := by
    dsimp [seamStrip]
    exact runDarts_castStart n (reverse_reverse G u) _
  have hreverse : runDarts G (n + 1) rr =
      (runDarts G (n + 1) rest).reverse.map (reverse G) := by
    simpa [rr] using runDarts_reverseRun rest
  have hsplit : runDarts G (n + 1) rr = d :: runDarts G n rr.2.2 := by
    simp [runDarts, rr, reverse_reverse]
  rw [hsplit] at hreverse
  have htail : runDarts G (n + 1) rest =
      runDarts G n (reverseRun rr.2.2) ++ [reverse G d] := by
    have h := congrArg (fun xs : List (Dart G) => xs.reverse.map (reverse G)) hreverse
    have h0 : runDarts G (n + 1) rest =
        (runDarts G n rr.2.2).reverse.map (reverse G) ++ [reverse G d] := by
      simpa [Function.comp_def] using h.symm
    rw [runDarts_reverseRun]
    exact h0
  rw [hcore]
  change d :: runDarts G (n + 1) rest =
    [d] ++ runDarts G n (reverseRun rr.2.2) ++ [reverse G d]
  rw [htail]
  simp [List.append_assoc]

/-- Runs with a reversed cyclic seam, with the initial dart recorded as a tail choice. -/
abbrev SeamRuns (n : ℕ) :=
  Σ d : Dart G, Run G (n + 2) d (reverse G d)

/-- Encode a seam run by its first dart and the result of stripping its seam. -/
def seamCoreEncoding (n : ℕ) : SeamRuns (G := G) n → Σ d : Dart G, AllRuns G n
  | ⟨d, r⟩ => ⟨d, seamStrip n r⟩

theorem seamCoreEncoding_injective (n : ℕ) :
    Function.Injective (seamCoreEncoding (G := G) n) := by
  intro p q hpq
  rcases p with ⟨d, r⟩
  rcases q with ⟨e, s⟩
  change (⟨d, seamStrip n r⟩ : Σ d : Dart G, AllRuns G n) =
    ⟨e, seamStrip n s⟩ at hpq
  have hde : d = e := congrArg Sigma.fst hpq
  subst e
  have hcore : seamStrip n r = seamStrip n s := congrArg Sigma.snd hpq
  have hcoreDarts := congrArg (fun p : AllRuns G n => runDarts G n p.2.2) hcore
  change runDarts G n (seamStrip n r).2.2 =
    runDarts G n (seamStrip n s).2.2 at hcoreDarts
  have hlist : runDarts G (n + 2) r = runDarts G (n + 2) s := by
    rw [seamStrip_darts, seamStrip_darts, hcoreDarts]
  have hall : (⟨d, reverse G d, r⟩ : AllRuns G (n + 2)) =
      ⟨d, reverse G d, s⟩ :=
    (allRuns_darts_injective (G := G) (n + 2)) hlist
  cases hall
  rfl

/-- Incoming allowed darts at a fixed dart are reversals of ordinary successors. -/
def seamPredecessorEquiv (e : Dart G) :
    {d : Dart G // Next G d e} ≃ {f : Dart G // Next G (reverse G e) f} where
  toFun d := ⟨reverse G d.1, (next_reverse G d.1 e).mp d.2⟩
  invFun f := ⟨reverse G f.1, by
    have hf : Next G (reverse G e) (reverse G (reverse G f.1)) := by
      simpa using f.2
    exact (next_reverse G (reverse G f.1) e).mpr hf⟩
  left_inv d := by simp
  right_inv f := by simp

theorem seamPredecessor_card_eq (e : Dart G) :
    Fintype.card {d : Dart G // Next G d e} =
      (successors G (reverse G e)).card := by
  calc
    Fintype.card {d : Dart G // Next G d e} =
        Fintype.card {f : Dart G // Next G (reverse G e) f} :=
      Fintype.card_congr (seamPredecessorEquiv (G := G) e)
    _ = (successors G (reverse G e)).card := by
      classical
      simpa [successors] using
        (Fintype.card_subtype (fun f : Dart G => Next G (reverse G e) f))

theorem seamPredecessor_card_le_two (hmax : ∀ v, G.degree v ≤ 3) (e : Dart G) :
    Fintype.card {d : Dart G // Next G d e} ≤ 2 := by
  rw [seamPredecessor_card_eq]
  rw [successors_card]
  have h := hmax (tail G e)
  simpa [head_reverse] using Nat.sub_le_sub_right h 1

theorem seamStrip_boundary_steps (n : ℕ) {d : Dart G}
    (r : Run G (n + 2) d (reverse G d)) :
    Next G d (seamStrip n r).1 ∧
      Next G (seamStrip n r).2.1 (reverse G d) := by
  let rr := reverseRun r.2.2
  change Next G d r.1 ∧ Next G (reverse G rr.1) (reverse G d)
  have hrr : Next G d rr.1 := by simpa using rr.2.1.2
  exact ⟨r.2.1.2, (next_reverse G d rr.1).mp hrr⟩







/-- The middle left after removing a reversed seam is again a closed
endpoint run. Its internal nonbacktracking condition is carried by the
`Run` structure in the output. -/
theorem seamStrip_preserves_closed_endpoints (n : ℕ) {d : Dart G}
    (r : Run G (n + 2) d (reverse G d)) :
    tail G (seamStrip n r).1 = head G (seamStrip n r).2.1 := by
  have hsteps := seamStrip_boundary_steps (G := G) n r
  rcases hsteps with ⟨hfirst, hlast⟩
  calc
    tail G (seamStrip n r).1 = head G d := hfirst.1.symm
    _ = tail G (reverse G d) := by simp
    _ = head G (seamStrip n r).2.1 := hlast.1.symm

/-- All nonbacktracking runs whose endpoint vertices are closed. -/
abbrev ClosedEndpointRuns (k : ℕ) :=
  {p : AllRuns G k // tail G p.1 = head G p.2.1}

/-- Closed runs whose cyclic seam is a reversed dart pair. -/
abbrev SeamedClosedEndpointRuns (k : ℕ) :=
  {p : ClosedEndpointRuns (G := G) k // p.1.2.1 = reverse G p.1.1}

/-- Closed runs of length `n+2` whose cyclic seam is a reversed dart pair. -/
abbrev ClosedSeamRuns (n : ℕ) := SeamedClosedEndpointRuns (G := G) (n + 2)

def seamClosedEquiv (n : ℕ) : SeamRuns (G := G) n ≃ ClosedSeamRuns (G := G) n where
  toFun x := by
    rcases x with ⟨d, r⟩
    exact ⟨⟨⟨d, reverse G d, r⟩, by simp⟩, rfl⟩
  invFun z := by
    rcases z with ⟨⟨⟨d, e, r⟩, hclosed⟩, hseam⟩
    exact ⟨d, hseam ▸ r⟩
  left_inv x := by
    rcases x with ⟨d, r⟩
    rfl
  right_inv z := by
    rcases z with ⟨⟨⟨d, e, r⟩, hclosed⟩, hseam⟩
    change e = reverse G d at hseam
    subst e
    apply Subtype.ext
    apply Subtype.ext
    rfl







/-- Runs whose cyclic seam does not cancel by a reversed dart pair. -/
abbrev ReducedClosedEndpointRuns (k : ℕ) :=
  {p : ClosedEndpointRuns (G := G) k // p.1.2.1 ≠ reverse G p.1.1}

theorem reverse_ne_self (d : Dart G) : reverse G d ≠ d := by
  rcases d with ⟨e, b⟩
  cases b <;> simp [reverse]

theorem run_zero_seam_impossible {d e : Dart G} (r : Run G 0 d e) :
    e ≠ reverse G d := by
  intro h
  have hde : d = e := r.2
  exact reverse_ne_self (G := G) d (hde.trans h).symm

theorem run_one_seam_impossible {d e : Dart G} (r : Run G 1 d e) :
    e ≠ reverse G d := by
  intro h
  rcases r with ⟨u, hu, rest⟩
  have heu : u = e := rest.2
  have hnext : Next G d (reverse G d) := by simpa [heu, h] using hu.2
  exact hnext.2 rfl











theorem closedEndpointRuns_card_le_reduced_add_seamed (k : ℕ) :
    Fintype.card (ClosedEndpointRuns (G := G) k) ≤
      Fintype.card (ReducedClosedEndpointRuns (G := G) k) +
        Fintype.card (SeamedClosedEndpointRuns (G := G) k) := by
  classical
  let reduced : ClosedEndpointRuns (G := G) k → Prop :=
    fun p => p.1.2.1 ≠ reverse G p.1.1
  let seamed : ClosedEndpointRuns (G := G) k → Prop :=
    fun p => p.1.2.1 = reverse G p.1.1
  have hcover : ∀ p, reduced p ∨ seamed p := by
    intro p
    rcases Classical.em (seamed p) with hs | hr
    · exact Or.inr hs
    · exact Or.inl hr
  have hinj : Function.Injective (fun p : ClosedEndpointRuns (G := G) k =>
      (⟨p, hcover p⟩ : {p : ClosedEndpointRuns (G := G) k // reduced p ∨ seamed p})) := by
    intro p q h
    exact congrArg Subtype.val h
  calc
    Fintype.card (ClosedEndpointRuns (G := G) k) ≤
        Fintype.card {p : ClosedEndpointRuns (G := G) k // reduced p ∨ seamed p} :=
      Fintype.card_le_of_injective _ hinj
    _ ≤ Fintype.card {p : ClosedEndpointRuns (G := G) k // reduced p} +
        Fintype.card {p : ClosedEndpointRuns (G := G) k // seamed p} :=
      Fintype.card_subtype_or reduced seamed



/-- The iterated seam-stripping count bound. The terminal core has length zero
or one; at every larger length it is either already seam-reduced or strips
one reversed pair and recurses. -/
def seamCoreCountBound : ℕ → ℕ
  | 0 => Fintype.card (ReducedClosedEndpointRuns (G := G) 0)
  | 1 => Fintype.card (ReducedClosedEndpointRuns (G := G) 1)
  | n + 2 => Fintype.card (ReducedClosedEndpointRuns (G := G) (n + 2)) +
      2 * seamCoreCountBound n


















end Erdos1016.Nonbacktracking
end
