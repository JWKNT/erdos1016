import Erdos1016.Cycles.Counting.RootedRunEncoding
import Erdos1016.Nonbacktracking.Walks.PrefixCounts

set_option autoImplicit false

noncomputable section
namespace Erdos1016.Proof.PathEndpointRunInjection

open Erdos1016.Nonbacktracking
open Erdos1016.Proof.WalkPrefix

variable (G : PhysicalGraph)

/-- At fixed endpoints, the oriented physical-dart serialization determines
the entire ordinary vertex walk. -/
theorem walkDarts_injective_fixedEndpoints {u v : G.Vertex} :
    Function.Injective (walkDarts G : G.toSimpleGraph.Walk u v → List (Dart G)) := by
  intro p
  induction p with
  | nil =>
      intro q h
      cases q with
      | nil => rfl
      | @cons a b c hab q => simp [walkDarts] at h
  | @cons a b c hab p ih =>
      intro q h
      cases q with
      | nil => simp [walkDarts] at h
      | @cons a' b' c' hab' q =>
          have hcons :
              dartOfAdj G hab :: walkDarts G p =
                dartOfAdj G hab' :: walkDarts G q := h
          have hparts := List.cons.inj hcons
          have hhead : b = b' := by
            have hh := congrArg (head G) hparts.1
            simpa using hh
          subst b'
          have htail : walkDarts G p = walkDarts G q := hparts.2
          have hpq := ih htail
          subst q
          have hAdj : hab = hab' := Subsingleton.elim _ _
          subst hab'
          rfl

/-- A fixed-endpoint simple path with `a` edges, encoded as its unique
`(a-1)`-transition endpoint run. -/
abbrev FixedEndpointSimplePaths (a : ℕ) (u v : G.Vertex) :=
  {p : G.toSimpleGraph.Walk u v // p.IsPath ∧ p.length = a ∧ 0 < a}

private theorem exists_endpointRun_of_simplePath (a : ℕ) (ha : 0 < a)
    {u v : G.Vertex} (p : G.toSimpleGraph.Walk u v)
    (hp : p.IsPath) (hlen : p.length = a) :
    ∃ r : EndpointRuns G (a - 1) u v,
      runDarts G (a - 1) r.1.2.2 = walkDarts G p := by
  have hpos : 0 < p.length := by omega
  obtain ⟨d, e, htail, _, _, hhead, r, hr⟩ :=
    path_has_dart_run p hp hpos
  have hidx : p.length - 1 = a - 1 := congrArg (fun n => n - 1) hlen
  let r' : Run G (a - 1) d e := hidx ▸ r
  let all : AllRuns G (a - 1) := ⟨d, e, r'⟩
  have hendpoints : endpoints G (a - 1) all = (u, v) := by
    change (tail G d, head G e) = (u, v)
    exact Prod.ext htail hhead
  refine ⟨⟨all, hendpoints⟩, ?_⟩
  change runDarts G (a - 1) r' = walkDarts G p
  calc
    runDarts G (a - 1) r' = runDarts G (p.length - 1) r :=
      runDarts_cast hidx r
    _ = walkDarts G p := hr

private noncomputable def encodeSimplePath (a : ℕ) (ha : 0 < a)
    {u v : G.Vertex} (p : G.toSimpleGraph.Walk u v)
    (hp : p.IsPath) (hlen : p.length = a) : EndpointRuns G (a - 1) u v :=
  Classical.choose (exists_endpointRun_of_simplePath G a ha p hp hlen)

private theorem encodeSimplePath_darts (a : ℕ) (ha : 0 < a)
    {u v : G.Vertex} (p : G.toSimpleGraph.Walk u v)
    (hp : p.IsPath) (hlen : p.length = a) :
    runDarts G (a - 1)
      (encodeSimplePath G a ha p hp hlen).1.2.2 = walkDarts G p :=
  Classical.choose_spec (exists_endpointRun_of_simplePath G a ha p hp hlen)

/-- The path-to-run encoding is injective and therefore gives the exact
fixed-endpoint path-count input for the suffix bound. -/
theorem encodeSimplePath_injective (a : ℕ)
    {u v : G.Vertex} :
    Function.Injective (fun p : FixedEndpointSimplePaths G a u v =>
      encodeSimplePath G a p.2.2.2 p.1 p.2.1 p.2.2.1) := by
  intro p q hpq
  apply Subtype.ext
  have hrun :
      runDarts G (a - 1)
          (encodeSimplePath G a p.2.2.2 p.1 p.2.1 p.2.2.1).1.2.2 =
        runDarts G (a - 1)
          (encodeSimplePath G a q.2.2.2 q.1 q.2.1 q.2.2.1).1.2.2 := by
    exact congrArg
      (fun r : EndpointRuns G (a - 1) u v => runDarts G (a - 1) r.1.2.2) hpq
  have hwalk : walkDarts G p.1 = walkDarts G q.1 := by
    calc
      walkDarts G p.1 =
          runDarts G (a - 1)
            (encodeSimplePath G a p.2.2.2 p.1 p.2.1 p.2.2.1).1.2.2 :=
        (encodeSimplePath_darts G a p.2.2.2 p.1 p.2.1 p.2.2.1).symm
      _ = runDarts G (a - 1)
          (encodeSimplePath G a q.2.2.2 q.1 q.2.1 q.2.2.1).1.2.2 := hrun
      _ = walkDarts G q.1 :=
        encodeSimplePath_darts G a q.2.2.2 q.1 q.2.1 q.2.2.1
  exact walkDarts_injective_fixedEndpoints G hwalk

/-- The subtype of simple `a`-edge paths is finite because it injects into
the finite family of endpoint runs. -/
noncomputable instance fixedEndpointSimplePathsFintype (a : ℕ)
    (u v : G.Vertex) : Fintype (FixedEndpointSimplePaths G a u v) :=
  Fintype.ofInjective (fun p : FixedEndpointSimplePaths G a u v =>
    encodeSimplePath G a p.2.2.2 p.1 p.2.1 p.2.2.1)
    (encodeSimplePath_injective G a)

/-- Exact cardinal bound for fixed-endpoint simple paths by the endpoint-run
family counted in the paper's suffix argument. -/
theorem fixedEndpointSimplePaths_card_le_endpointRuns (a : ℕ)
    (u v : G.Vertex) :
    Fintype.card (FixedEndpointSimplePaths G a u v) ≤
      Fintype.card (EndpointRuns G (a - 1) u v) :=
  Fintype.card_le_of_injective (fun p : FixedEndpointSimplePaths G a u v =>
    encodeSimplePath G a p.2.2.2 p.1 p.2.1 p.2.2.1)
    (encodeSimplePath_injective G a)

end Erdos1016.Proof.PathEndpointRunInjection
end
