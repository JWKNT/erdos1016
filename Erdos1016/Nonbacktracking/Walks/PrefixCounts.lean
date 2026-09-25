import Erdos1016.Nonbacktracking.Walks.RunGeometry

/-!
# Subcubic counts for finite nonbacktracking prefixes

An `r`-edge prefix consists of one initial dart followed by `r-1`
nonbacktracking transitions. The initial dart has at most three choices in a
subcubic graph, and each later transition has at most two choices.
-/

set_option autoImplicit false

noncomputable section
namespace Erdos1016.Proof.WalkPrefix

open Erdos1016.Nonbacktracking

variable (G : PhysicalGraph)

/-- All dart runs with `k` transitions and a prescribed initial vertex.
The terminal dart is unrestricted. -/
abbrev StartingRuns (k : ℕ) (v : G.Vertex) :=
  Σ d : {d : Dart G // tail G d = v}, Σ e : Dart G, Run G k d.1 e

abbrev EndpointRuns (k : ℕ) (u v : G.Vertex) :=
  {p : AllRuns G k // endpoints G k p = (u, v)}

/-- A continuation of `s` transitions after a fixed boundary dart is uniquely
determined by its terminal vertex when `2*s` is below the girth. The shared
boundary dart is removed, leaving two runs of `s-1` transitions to which the
existing endpoint-injectivity theorem applies. -/
def dropFirstRun : ∀ {s : ℕ}, 0 < s → {d e : Dart G} →
    Run G s d e → AllRuns G (s - 1)
  | _ + 1, _, _, e, ⟨u, _, rest⟩ => ⟨u, e, rest⟩

theorem dropFirstRun_eq_of_same_boundary_and_endpoint (s D : ℕ)
    (hs : 0 < s) (hg : ShortWalks.GirthGreater G.toSimpleGraph D)
    (hshort : 2 * s ≤ D) {d e₁ e₂ : Dart G}
    (r₁ : Run G s d e₁) (r₂ : Run G s d e₂)
    (hend : head G e₁ = head G e₂) :
    dropFirstRun G hs r₁ = dropFirstRun G hs r₂ := by
  cases s with
  | zero => omega
  | succ k =>
      rcases r₁ with ⟨u₁, hu₁, r₁'⟩
      rcases r₂ with ⟨u₂, hu₂, r₂'⟩
      let p₁ : AllRuns G k := ⟨u₁, e₁, r₁'⟩
      let p₂ : AllRuns G k := ⟨u₂, e₂, r₂'⟩
      have he : endpoints G k p₁ = endpoints G k p₂ := by
        apply Prod.ext
        · exact hu₁.2.1.symm.trans hu₂.2.1
        · exact hend
      have hshort' : 2 * (k + 1) ≤ D := by simpa using hshort
      exact (endpoints_injective_of_girth G D k hg hshort') he

/-- A positive-length run is reconstructed from its first transition and the
run left after dropping that transition. In particular, equality of the
`dropFirstRun` encodings forces equality of the terminal dart and of the
original runs after transporting that endpoint. -/
theorem eq_of_dropFirstRun_eq {s : ℕ} (hs : 0 < s) {d e₁ e₂ : Dart G}
    (r₁ : Run G s d e₁) (r₂ : Run G s d e₂)
    (h : dropFirstRun G hs r₁ = dropFirstRun G hs r₂) :
    ∃ he : e₁ = e₂, he ▸ r₁ = r₂ := by
  cases s with
  | zero => omega
  | succ k =>
      rcases r₁ with ⟨u₁, hu₁, r₁'⟩
      rcases r₂ with ⟨u₂, hu₂, r₂'⟩
      simp [dropFirstRun] at h
      rcases h with ⟨hu, htail⟩
      subst u₂
      cases htail
      have hflag : hu₁ = hu₂ := by
        apply Subtype.ext
        exact Subsingleton.elim _ _
      subst hu₂
      exact ⟨rfl, rfl⟩



/-- Split a run after its first `j` transitions. The boundary dart belongs to
both pieces, which is the dart analogue of retaining the last prefix edge. -/
def splitRun : ∀ {j k : ℕ}, j ≤ k → {d e : Dart G} → Run G k d e →
    Σ f : Dart G, Run G j d f × Run G (k - j) f e
  | 0, k, _, d, e, r => ⟨d, ⟨⟨(), rfl⟩, r⟩⟩
  | j + 1, 0, h, d, e, r => by
      omega
  | j + 1, k + 1, h, d, e, r => by
      rcases r with ⟨u, hu, rest⟩
      let pieces := splitRun (Nat.le_of_succ_le_succ h) rest
      refine ⟨pieces.1, ⟨⟨u, ⟨hu, pieces.2.1⟩⟩, ?_⟩⟩
      simpa using pieces.2.2
termination_by j _ _ _ _ _ => j

/-- The oriented darts leaving a vertex are in bijection with its physical
incidences, so their count is its degree. -/
theorem card_starting_darts (v : G.Vertex) :
    Fintype.card {d : Dart G // tail G d = v} = G.degree v := by
  have hout := outgoing_one (K := ℤ) G v
  unfold outgoing at hout
  have hcard :
      (Fintype.card {d : Dart G // tail G d = v} : ℤ) =
        ∑ d : Dart G, if tail G d = v then 1 else 0 := by
    rw [Fintype.card_subtype]
    rw [Finset.card_eq_sum_ones, Finset.sum_filter]
    simp
  exact_mod_cast hcard.trans hout

/-- Direct counting works even when some successor sets are empty. -/
theorem runCount_le_of_max_degree (hmax : ∀ v, G.degree v ≤ 3)
    (k : ℕ) (d : Dart G) :
    (∑ e : Dart G, Fintype.card (Run G k d e)) ≤ 2 ^ k := by
  induction k generalizing d with
  | zero =>
      simp_rw [card_run]
      simp [pow_zero, Matrix.one_apply]
  | succ k ih =>
      have hrec : (∑ e : Dart G, Fintype.card (Run G (k + 1) d e)) =
          ∑ j ∈ successors G d, ∑ e : Dart G, Fintype.card (Run G k j e) := by
        simp_rw [card_run, pow_succ', Matrix.mul_apply]
        rw [Finset.sum_comm]
        simp [matrix, successors, Finset.sum_filter, ite_mul]
      rw [hrec]
      calc
        _ ≤ ∑ _j ∈ successors G d, 2 ^ k := by
          apply Finset.sum_le_sum
          intro j hj
          exact ih j
        _ = (successors G d).card * 2 ^ k := by simp
        _ ≤ 2 * 2 ^ k := by
          apply Nat.mul_le_mul_right
          rw [successors_card]
          have h := hmax (head G d)
          omega
        _ = 2 ^ (k + 1) := by rw [pow_succ]; ring

/-- No minimum degree is required for the subcubic prefix bound. -/
theorem startingRuns_card_le_of_max_degree (hmax : ∀ v, G.degree v ≤ 3)
    (k : ℕ) (v : G.Vertex) :
    Fintype.card (StartingRuns G k v) ≤ 3 * 2 ^ k := by
  simp only [StartingRuns, Fintype.card_sigma]
  calc
    _ ≤ ∑ _d : {d : Dart G // tail G d = v}, 2 ^ k := by
      apply Finset.sum_le_sum
      intro d hd
      exact runCount_le_of_max_degree G hmax k d.1
    _ = Fintype.card {d : Dart G // tail G d = v} * 2 ^ k := by simp
    _ = G.degree v * 2 ^ k := by rw [card_starting_darts]
    _ ≤ 3 * 2 ^ k := Nat.mul_le_mul_right _ (hmax v)

/-- Exact subcubic prefix budget. For `r ≥ 1`, the number of dart walks of
`r` edges starting at `v` is at most `3 * 2^(r-1)`. The unrestricted final
dart means this counts every possible length-`r` prefix. -/
theorem startingRuns_card_le (_hmin : ∀ v, 2 ≤ G.degree v)
    (hmax : ∀ v, G.degree v ≤ 3) (r : ℕ) (v : G.Vertex) :
    Fintype.card (StartingRuns G (r - 1) v) ≤ 3 * 2 ^ (r - 1) :=
  startingRuns_card_le_of_max_degree G hmax (r - 1) v

/-- Prefix budget in the paper's `a,s` parameters. -/
theorem startingRuns_card_le_suffix_budget (hmin : ∀ v, 2 ≤ G.degree v)
    (hmax : ∀ v, G.degree v ≤ 3) (a s : ℕ) (v : G.Vertex) :
    Fintype.card (StartingRuns G (a - s - 1) v) ≤
      3 * 2 ^ (a - s - 1) := by
  exact startingRuns_card_le G hmin hmax (a - s) v

/-- Prefix extraction from a fixed-endpoint run. -/
def fixedEndpointPrefix {j k : ℕ} (hjk : j ≤ k) (u v : G.Vertex)
    (p : EndpointRuns G k u v) : StartingRuns G j u := by
  let z := splitRun G hjk p.1.2.2
  exact ⟨⟨p.1.1, by simpa [endpoints] using congrArg Prod.fst p.2⟩,
    ⟨z.1, z.2.1⟩⟩






end Erdos1016.Proof.WalkPrefix
end
