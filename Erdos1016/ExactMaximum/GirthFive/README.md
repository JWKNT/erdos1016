# Theorem 7.1 at girth five: the formal proof

Owner: Fable 5.2. Written on 12 November 2026.

```lean
theorem Erdos1016.ExactMaximum.girthForestStatement_five : GirthForestStatement 5
```

In words: there is `R` such that, for every connected cubic multigraph `G` of rank `r ≥ R` and
every set `P` of at most `3 log₂ r` vertices such that `G[P]` is connected, if `G - P` has no
cycle of length less than five, then `q(G,P) < 2/5`. Here `q(G,P)` is the probability that the
edges without an end in `P` of a uniformly random even subgraph form a forest. This is
Theorem 7.1 of the paper "The maximum number of cycles in a graph of large rank"
(`paper/minimal/exact-maximum/`). The statement `GirthForestStatement` is in
`Erdos1016/ExactMaximum/GirthFive.lean`.

The kernel accepts the proof with the axioms `propext`, `Classical.choice` and `Quot.sound`.
`audits/ExactMaximumThreeCasesAudit.lean` prints the axioms and checks the parts.

## The files

The order is the order of the imports.

| File | Main statements | Used by |
|---|---|---|
| `RailBound.lean` | `rail_bound`: no seven integers `p_0, ..., p_6` are pairwise different with `\|p_k - p_l\| ≤ (l - k) + 2` and `\|p_k - p_{k+1}\| ≥ 2` | `GeodesicRails` |
| `GeodesicRails.lean` | For a shortest walk `A` in a graph of girth at least five: `attach_unique` (a vertex outside `A` has at most one neighbour on `A`), `no_rail` (no path of seven vertices outside `A` such that each vertex has a neighbour at an inner position of `A`) | `TwoTerminal` |
| `TwoTerminal.lean` | `two_terminal_card_le`: the count `\|B\| ≤ 400 (\|D\| + 2)` | `TwoTerminalRegion` |
| `RegionWords.lean` | Words of a multigraph and its simple graph: `girthGreater_toSimpleGraph`, `card_internalEdges_le`, `sum_card_nbrs_le`, `exists_word_of_sides_even` | `TwoTerminalRegion`, `RegionRigidity` |
| `TwoTerminalRegion.lean` | `two_terminal_region`: if every word of `B` with boundary `x + y` is a forest, then `\|B\| ≤ 400 (\|D\| + 2)` | `RegionRigidity` |
| `RegionRigidity.lean` | `exists_word_two_terminals`, `side_of_other_slab`, `region_not_rigid`: a region with many slabs is not rigid | `LevelRegions` |
| `LevelRegions.lean` | Level regions and the spine; `window_not_rigid`: a window of cubic levels is not rigid | `Pieces` |
| `ManyRegions.lean` | `affine_forest_density_le_prod`: the product law for a family of disjoint regions and a fixed base word | `Pieces` |
| `Pieces.lean` | `exists_affine_bound_girth_five`: pieces at girth five (Lemma 7.6 of the text) | `BasePacking` |
| `BasePacking.lean` | `exists_block_bound` (two blocks), `exists_row_bound`, `exists_base_packing`, `exists_base_finset_packing` | `ForestProbability` |
| `ForestProbability.lean` | `shifted_size_bound`, `girthForestStatement_five` | `MainThreeCases` |

The proof also uses these files of Astra without a change: the thin layers
(`Probability/Avoidance/PoleMarker.lean`), the extraction of a core
(`ExactMaximumSupport/LargeGirth/PieceExtraction.lean`, `PieceCore.lean`), the product of two
regions (`PoleProduct.lean`), the chain of separators
(`ExactMaximumSupport/Shortening/DisjointRegionChain.lean`, `ChainPackingMoment.lean`), the
packing bound at large girth (`ChainPacking.lean`), the sequence of deleted sets
(`LargeGirth/RegionPackingSequence.lean`, `RaisedGirth.lean`), and the last step
(`Shortening/LargeOrderChain.lean`, `LargeGirth/ParameterBudgetFinal.lean`).

## The proof and the text

The text proves Theorem 7.1 in Section 7 with these parts: forest proportions at large girth
and the product (Lemmas 7.2, 7.3), the pieces at girth five (Lemmas 7.4, 7.5, 7.6 and
Corollary 7.7), separators and the chain (Lemma 7.8 to Proposition 7.11), the packing of short
cycles (Proposition 7.12), and a second-moment count with the cycles of one scale.

The formal proof has the same statement. Two parts are proved in another way.

1. **Lemma 7.6 (pieces at girth five).** The formal statement is
   `exists_affine_bound_girth_five`. The outer steps are those of the text: thin layers, groups
   of consecutive layers without a boundary vertex, and the product over the groups. The text
   shows with Lemma 7.5 (rigid sets, by a tree through the set and capped ladders) that the
   region of a group is not rigid. The formal proof shows it with slabs and a bound for two
   terminals (below). It does not use Lemmas 7.4 and 7.5 and no ladder.
2. **The count at the end.** The formal proof deletes maximal families of short cyclic regions
   at the scales `D, 2D, 4D, ...` and ends as the formal proof for large girth does
   (`Shortening/ChainForestProbability.lean`). The only new step is the bound for the first
   family, which needs girth five only (`exists_base_finset_packing`). The text counts the
   cycles at one scale.

## The new mathematics, with proofs

All graphs are finite. `N` is a multigraph with all degrees at most three and without a cycle
of length less than five. A *word* is a set of edges; its *boundary* is the set of the vertices
of odd degree; an *even word* has an empty boundary.

**Rail lemma** (`rail_bound`). No integers `p_0, ..., p_6` satisfy: `p_k ≠ p_l` for `k < l`;
`|p_k - p_l| ≤ (l - k) + 2`; and `|p_k - p_{k+1}| ≥ 2`.
*Proof.* A case distinction on the signs of the six steps; each case is linear arithmetic.
(An exhaustive search shows that the longest such sequence has six terms: `5, 2, 4, 1, 3, 0`.)

**Lemma A** (`attach_unique`, `no_rail`). Let `A` be a shortest path between two vertices in a
graph `K` of girth at least five.
(a) A vertex outside `A` has at most one neighbour on `A`.
(b) There is no path `v_0, ..., v_6` outside `A` such that each `v_k` has a neighbour
`A(p_k)` with `0 < p_k < |A|`, if no vertex has four neighbours.
*Proof.* (a) Two neighbours at the positions `i < j` give `j - i ≤ 2`, because `A` is shortest,
and then a cycle of length three or four. (b) The positions satisfy the conditions of the rail
lemma: the walk `A(p_k), v_k, ..., v_l, A(p_l)` has `(l - k) + 2` edges, so
`|p_k - p_l| ≤ (l - k) + 2`. If `p_k = p_l`, the vertex `A(p_k)` has four neighbours: `v_k`,
`v_l` and two vertices of `A`. If `|p_k - p_{k+1}| = 1`, there is a cycle of length four.

**Lemma B, two terminals** (`two_terminal_card_le`, `two_terminal_region`). Let `B` be a
connected set of vertices of `N`, `x ≠ y` two vertices of `B`, and `D ⊆ B` a set that contains
every vertex of `B` that has degree less than three or a neighbour outside `B`. Suppose that
every word on the internal edges of `B` with boundary `{x, y}` is a forest. Then
`|B| ≤ 400 (|D| + 2)`.
*Proof.* Let `A` be a shortest path from `x` to `y` in `N[B]`, and `F = B - V(A)`. A nonzero
even word in `F`, added to `A`, is a word with boundary `{x, y}` that is not a forest. So
`N[F]` is a forest, with at most `|F|` edges. By Lemma A (a) a vertex of `F` has at most one
neighbour on `A`. A vertex of `F - D` without a neighbour on `A` has three neighbours in `F`,
and a vertex of `F - D` with a neighbour on `A` has two; a count of edge ends gives at most
`2 |D|` vertices of the first kind. Let `E` be the set of the vertices of `F` that are in `D`,
have no neighbour on `A`, or are adjacent to `x` or `y`. Then `|E| ≤ 3 |D| + 6`. Let `w` be a
vertex of `F` at distance more than three from `E` in `N[F]`. The walk in `F` through `w` with
three steps in each direction has seven different vertices (the graph `N[F]` is a forest and
the inner vertices have exactly two neighbours in `F`), and each of them has a neighbour at an
inner position of `A`. Lemma A (b) excludes this. So every vertex of `F` is within distance
three of `E`, and `|F| ≤ 64 |E|`. Every vertex of `A` outside `D` has a neighbour in `F`, and
a vertex of `F` has at most one neighbour on `A`; so `|V(A)| ≤ |D| + |F|`. Together:
`|B| ≤ |D| + 2 |F| ≤ |D| + 128 (3 |D| + 6) ≤ 400 (|D| + 2)`.

**Lemma C, words outside a set** (`exists_word_of_sides_even`, `exists_word_two_terminals`).
Let `X` be a set of vertices and `b` a demand (a set of vertices) disjoint from `X`.
(a) If every component of `N - X` contains an even number of vertices of `b`, then `b` is the
boundary of a word in `N - X`.
(b) Let `b` have even size, and let `s`, `t` be vertices outside `X`. If every component of
`N - X` that contains neither `s` nor `t` has an even number of vertices of `b`, then `b` or
`b + s + t` is the boundary of a word in `N - X`.
*Proof.* (a) Induction on `|b|`: join two vertices of `b` in one component by a path.
(b) Let `p`, `q` be the parities of `b` in the components of `s` and of `t`. If the components
are equal, `p = 0` by the total parity. If they are different, `p = q` by the total parity. In
both cases (a) applies to `b`, or to `b + s + t`.

**Lemma D, a region with slabs** (`region_not_rigid`). Let `R` be a connected set of vertices
and `w` a word on the internal edges of `R` with boundary `b`. Let `B_1, ..., B_n` be pairwise
disjoint connected subsets of `R`, disjoint from `b`, with `n > |b|`. For each `i` let `D_i` be
as in Lemma B, with `|B_i| > 400 (|D_i| + 2)`, and let `s_i`, `t_i` be vertices of `R - B_i`
with neighbours `x_i ≠ y_i` in `B_i`. Suppose that for `j ≠ i` every vertex of `B_j` is joined
to `s_i` or to `t_i` by a walk in `R - B_i`. Then there is an even word `z` on the internal
edges of `R` such that `w + z` is not a forest.
*Proof.* Call a component of `R - B_i` a *side component* if it contains neither `s_i` nor
`t_i`. Let `u` be a vertex of a side component of `B_i`, and `j ≠ i`. A walk in `R` from `u`
to `B_i` reaches `B_i` first at a vertex `v`; before `v` it stays in the side component, which
does not meet `B_j`. From `v` a walk in `R - B_j` leads to `s_j` or `t_j`. So `u` is not in a
side component of `B_j`. Hence every vertex of `b` is in a side component for at most one `i`,
and for some `i` no side component of `B_i` has an odd number of vertices of `b`. By Lemma C (b)
with `X = (V - R) ∪ B_i`, there is a word `w_0` in `R - B_i` with boundary `b`, or with
boundary `b + s_i + t_i`.
In the first case take a nonzero even word `c` in `B_i`; it exists because `N[B_i]` has more
edges than vertices. Then `w_0 + c = w + z` for an even word `z`, and it is not a forest.
In the second case suppose that all words `w + z` are forests. For every word `j` in `B_i`
with boundary `{x_i, y_i}`, the word `w_0 + s_i x_i + t_i y_i + j` has boundary `b`, so it is a
forest, and `j` is a forest. Lemma B gives `|B_i| ≤ 400 (|D_i| + 2)`, a contradiction.

**Lemma E, a window** (`window_not_rigid`). Let `N` be connected, `o` a vertex, and suppose
that every distance level from `o` has at most `W` vertices. Let `A` be a shortest path from
`o`. Let the levels `a, ..., c` contain only cubic vertices, where `c = a + n τ + 1`,
`n > 2 W` and `τ > 400 (2 W + 2)`. Let `R` be the set of the vertices that a walk through these
levels joins to `A(a)`, and `w` a word on the internal edges of `R` whose boundary has no
vertex at the levels `a + 1, ..., c - 1`. Then some `w + z` is not a forest.
*Proof.* Lemma D with the slabs `B_i` = the vertices that a walk through the levels
`a + (i-1) τ + 1, ..., a + i τ` joins to `A`, for `i = 1, ..., n`. The boundary of `w` has at
most `2 W` vertices. `D_i` is the set of the vertices of `B_i` in its first and last level, so
`|D_i| ≤ 2 W`, and `|B_i| ≥ τ`. The vertices `s_i`, `t_i` are the vertices of `A` below and
above the slab, and the path `A` joins the other slabs to them.

**Pieces at girth five** (`exists_affine_bound_girth_five`). For every `k` there is `F` such
that for every connected `N` as above with cubic deficit at most `k` and rank at least `F`,
every demand on the vertices of degree less than three has forest proportion at most `3/5`.
*Proof.* Suppose that a demand has forest proportion more than `3/5`. By the theorem on thin
layers (`exists_supported_demand_layer_bound`) every level from a vertex `o` has at most
`W = B (k + 2)² + 1` vertices. Put `n = 2 W + 1`, `τ = 400 (2 W + 2) + 1`, `h = n τ + 2` and
`m = 2^(2 h W)`. If the rank is large, there are `m + k` disjoint windows of `h` levels, and at
least `m` of them have only cubic vertices. By Lemma E every parity class of the region of
such a window has a word that is not a forest, so its forest proportion is at most `1 - 1/m`
(the region has at most `h W` vertices and at most `2^(2 h W)` even words). The product law
gives `(1 - 1/m)^m ≤ 1/2 < 3/5`.

**Two blocks** (`exists_block_bound`). For every `d` there is `F` such that two disjoint sets
with at least `F` vertices and at most `2 d` cut edges, outside a set `Q` such that `G - Q` has
girth at least five, give `q(G,Q) < 2/5`.
*Proof.* Each set has a component of large rank, and the component has a core with degrees two
and three, the same rank and cubic deficit at most `2 d`. The pieces theorem and the product of
two regions give `q ≤ 9/25`.

**The first family** (`exists_base_finset_packing`). For every `d ≥ 2` there is `q` such that
a family of pairwise disjoint connected cyclic regions with at most `d` cut edges outside
`P ∪ S` has at most `(3 d (d + |S| + 2) q + 6 d) 2^d` members, if `G - (P ∪ S)` has girth at
least five and `q(G, P ∪ S) ≥ 2/5`.
*Proof.* As for large girth: a good row of the two-link matrix gives a long chain of
separators, and a long chain gives two clean blocks; the blocks have at least `q - 1` regions
each, so they are large, and "two blocks" applies.

**The end** (`shifted_size_bound`, `girthForestStatement_five`). Let `D ≥ 256` be the constant
of the packing bound at large girth, and let `S_n` be the deleted set after the stages
`D, 2 D, ..., 2^(n-1) D`. The first family has at most `K_0` regions with at most `D` vertices
each, by the bound above. After the stage `n ≥ 1` the graph outside `P ∪ S_n` has no cycle of
length at most `2^(n-1) D`, so the packing bound at large girth applies to the stage `n`. The
size bound `|S_{m+1}| + 1 ≤ 2^(2 · 2^m D + 6 (log 2^m D)²)` of the proof for large girth has
room for the factor `2^c ≥ K_0 D + 1` from the stage `m = c` on. The stages `c, c + 1, ...` are
a sequence of the kind that the last step of the proof for large girth takes, at the base scale
`2^c D`.
