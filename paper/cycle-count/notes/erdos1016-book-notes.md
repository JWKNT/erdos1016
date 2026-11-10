# Erdős #1016 — notes toward a Book proof

Paper studied: KNT, *The minimum number of edges in a pancyclic graph* (Sept 2026), and its web exposition.
Labels: **[proved]** = full argument given here, **[checked]** = brute-force verified on small cases, **[open]** = not proved.

## 0. Bottom line after the second search

1. I still have no complete elementary replacement for the paper's forest estimate (Theorem 1.2). I now think the route of §4–§5 cannot give one by itself; §5.6 says why.
2. Theorem 1.2 implies the asymptotic Entringer–Slater conjecture (§3). With the Lean development confirmed, that corollary is a theorem. The paper does not state it.
3. §4: an elementary description of what a counterexample to the halving step must look like. The ratio (edges)/2^rank of the greedy witnesses can only decrease, so all but O(1/ε) steps are "perfect"; a perfect step is forced to have the shape of Bondy's construction; and an edge born late can never lie on almost all cycle lengths. No probability is used.
4. §5.4–5.5: the *exact* case has Book proofs. If no combination of the new ears is wasted, the number of binary digits gained is at most the number of edges of the shortest bypass (one line), and if no outside word is wasted then r − t ≤ 2|V(W)| + 3 (five lines). Bondy's necklace, the Wheatstone bridge and K₃,₃ minus an edge are equality cases of the first. In the bead model (§5.1) the idea survives small defects and gives the halving after m + O(1/ε) further ranks (the paper's recurrence uses about m^128).
5. What is missing is robustness: going from "nothing wasted" to "less than half wasted". The exact lemmas degrade exponentially, and the nearly exact windows that §4 produces force exactly the high-girth outside structure that the paper treats with its second-moment argument (§5.6). **[open]** The one robust statement I have that survives at the level of "half wasted" is a counting identity for the rank a cycle leaves untouched (§5.7); it shows that ears cannot keep attaching to recent ears, but it does not bound r − t.
6. §2 collects the cases where the factor ½ needs no probability at all.

## 1. The paper in three moves

β(G) is the cycle rank; Φ(R) = sup (L−2)/2^β(G) over graphs of rank ≥ R with cycles of every length 3..L. Goal: Φ(r) = O(2^(−log* r)).

- **Witness.** Add, one at a time, a cycle of the least missing length until the union W has rank t ≥ 2R. Then (m+1)/2^t ≤ Φ(R) + 2^(1−R), where m = |E(W)|.
- **Restriction.** Z(G) restricted to the edges outside W has 2^(r−t) equally likely "outside words"; one word supports at most m+1 lengths; a cycle meeting both sides leaves a forest outside. So (L−2)/2^r ≤ (m+1)/2^t · P(forest outside) + 2^(−t) + m/2^r.
- **Forest estimate.** If m ≤ √r and W has few components, P(forest outside) ≤ ½ + 20/log log log r. Five of the paper's six pages: cubic reduction, short-cycle packing, non-backtracking spectrum, second moment.

## 2. Where the ½ is free

Let W ⊆ G, G′ = G − E(W), and let the *ports* be the vertices meeting both. A *T-join* is an edge set whose odd-degree vertices are exactly T.

**Lemma G (gluing). [proved]** Z(G) is the disjoint union over T of (T-joins of W) × (T-joins of G′); the feasible T form a group 𝒯, and 2^r = |𝒯|·2^t·2^β(G′). A cycle meeting both sides splits into two systems of disjoint paths with the same end set T ≠ ∅. *Proof:* an edge set is even iff its two parts have the same odd vertices. ∎

**(a) Two classes. [proved]** If |𝒯| = 2 (e.g. two ports), then L−2 ≤ m + 2^β(G′) + m·2^β(G′) and 2^r = 2·2^t·2^β(G′), so (L−2)/2^r ≤ ½·(m+1)/2^t + m/2^r. The extremal construction is iterated two-port gluing.

**(b) Two classes above the witness. [proved]** Let W ⊆ W⁺ ⊆ G and H = G − E(W⁺), and suppose the port group of (W⁺, H) has order 2. Restricting an outside word of (G, W) to E(H) is linear and onto the 2^(β(H)+1) outside words of (G, W⁺); half of those are even subgraphs of H, and a word containing a nonempty even subgraph of H is not part of a cycle through W. Hence
  (L−2)/2^r ≤ (½ + 2^(−β(H)−1))·(m+1)/2^t + 2^(−t) + m/2^r.
So lengths can be counted with a small witness while the ½ comes from any 2-separation higher up. In particular a counterexample has no piece of large rank attached to the rest at two vertices.

**(c) Port counting. [proved]** Let W be connected with bridges 𝒯₁,…,𝒯_k having x₁,…,x_k ≥ 2 ports. For a uniform outside word the odd-port sets T_i ⊆ X_i are independent and uniform over even subsets. In a cycle every vertex of W has degree ≤ 2, so Σ|T_i| ≤ 2|V(W)|, while E Σ|T_i| = Σx_i/2 and Var ≤ Σx_i. By Chebyshev, if Σx_i ≥ 8|V(W)| + 64 then at most a quarter of the words are usable. So in a counterexample Σx_i < 8|V(W)| + 64, and all but about 8m of the outside rank consists of cycles avoiding V(W) altogether. (When every bridge is a single path this is "a forest on V(W) has fewer than |V(W)| edges".)

**(d) The inside cannot do the work. [checked]** In a closed binary necklace with k beads and three consecutive vertices a, c, b on the closing path, each of the pairs ab, bc, ac has 2^k + 1 path lengths out of about 2^k edges (k ≤ 6). With a three-port bridge attached there, the count closes only if #paths(a,b) + #paths(b,c) + #paths(a,c) ≤ (2+o(1))·2^β in the bridge. Joining a new vertex to a, b, c turns this into "at most (½+o(1))·2^β cycles through a vertex of degree 3", so it is an instance of the Entringer–Slater bound of §3; with four or more ports the same step asks about several cycles through one vertex, which §3 does not cover.

## 3. The forest estimate is an Entringer–Slater theorem

**Corollary (not in the paper). [proved from Theorem 1.2]** Every graph with cycle rank r has at most (½ + O(1/log log log r))·2^r cycles.

*Proof.* Cycles are unchanged by joining components at a vertex, deleting pendant trees, suppressing degree-2 vertices and subdividing edges; so take a connected multigraph K of rank r with minimum degree ≥ 3 and let G be K with every edge subdivided twice. Put t = ⌊(log₂ r)/100⌋. For i = 1..t let C_i be a shortest cycle of K − {e₁,…,e_{i−1}} and pick e_i ∈ C_i. Deleting i−1 edges leaves at most 2(i−1) vertices of degree 2 in the 2-core, so by the Moore bound C_i has at most (2i−1)(2 log₂(2r)+1) edges, and the C_i are independent (e_i ∈ C_i, e_j ∉ C_i for j < i). So W = C₁ ∪ … ∪ C_t in G is a union of cycles of rank ≥ t with ≤ t components and O(log³ r) ≤ √r edges. A cycle meeting E(W) restricts to a forest on M = E(G) \ E(W); a cycle avoiding E(W) lies in Z(G − E(W)), of dimension ≤ r − t. Hence #cycles ≤ 2^r·P(ξ ∩ M forest) + 2^(r−t) ≤ (½ + 20/log log log r + 2r^(−1/100))·2^r. ∎

Entringer and Slater (1981) conjectured max ~ 2^(r−1); the best earlier bound I found is (15/16)·2^r (Aldred–Thomassen). So Theorem 1.2 is the paper's strongest statement, and any proof of #1016 through an estimate of this strength re-proves that conjecture.

## 4. Anatomy of a counterexample **[proved]**

**Setup.** G has cycles of every length 3..L, β(G) = r, E := (L−2)/2^r. Greedy sequence: C_q is a cycle of the least length ℓ_q missing from W_q, and W_{q+1} = W_q ∪ C_q (replace G by the final union). Write m_q, t_q for edges and rank of W_q, N_q for its number of cycle lengths, P_q = E(C_q) \ E(W_q), and
  ρ_q = (m_q+2)/2^(t_q),  ν_q = N_q/2^(t_q).

**4.1 Ratio lemma.** For every subgraph H ⊆ G: E ≤ (e(H)+2)/2^β(H) + e(H)/2^r. (Three-way count of §1 with H in place of W.)

**4.2 The ratio only decreases.** N_q ≤ m_q (a cycle in a union of cycles is no longer than the number of edges), ℓ_q ≤ N_q + 3, m_{q+1} ≤ m_q + ℓ_q, t_{q+1} ≥ t_q + 1. Hence ν_q ≤ ρ_q and
  ρ_{q+1} ≤ (ρ_q + ν_q)/2 + 3·2^(−t_q−1).

**4.3 Rigidity.** Let φ = Φ(R), let q₀ be the first step with t_{q₀} ≥ 2R (so ρ_{q₀} ≤ φ + 2^(2−R)), and suppose E > (½+ε)φ with 0 < ε ≤ ¼ and 2^(3−R) ≤ ε²φ. Call a step *early* if m_q ≤ ε²φ·2^r (all steps of rank ≤ r − 2 log₂(1/ε) − 1). For early steps q ≥ q₀:

- (a) (½+ε−ε²)φ ≤ ρ_q ≤ (1+ε²)φ. *Upper:* 4.2. *Lower:* 4.1.
- (b) Each step raises the rank by exactly one (a jump would halve ρ, contradicting (a)). So every cycle of W_{q+1} not in W_q contains all of P_q.
- (c) Put η_q = 1 − N_q/(m_q+2) and κ_q = 1 − |P_q|/(m_q+2). Then ρ_q − ρ_{q+1} = κ_q ρ_q/2 exactly, so Σκ_q < 2, and η_q ≤ κ_q + 3/(m_q+2), so Ση_q < 2 + o(1). The defects are *summable*: for any η, all but at most 6/η early steps are **η-perfect** (η_q, κ_q, η_{q+1} ≤ η).
- (d) At an η-perfect step: W_q has at least (1−η)(m_q+2) cycle lengths; the new part P_q has at least (1−η)(m_q+2) edges, so it doubles the graph; C_q has at most η(m_q+2) edges inside W_q; and if P_q is one path with ends c, d (always, when W_q is connected), the c–d paths of W_q realise all but 3η(m_q+2) of the lengths 1..m_q−1. In particular W_q is a single c–d path through all but 3η(m_q+2)+1 of its edges, plus a light remainder that carries the whole cycle rank.

So a counterexample is, at almost every scale, a long cycle with light chords in which the next ear closes across a short chord: Bondy's shape is forced, not chosen.

**4.4 Birth bound.** If e ∈ E(W_q) \ E(W_i), then the cycles of W_q through e have at most 2^(t_q − t_i − 1)·(m_i+1) lengths. *Proof:* Z(W_q) restricted to the edges outside W_i takes 2^(t_q−t_i) values, at most half of them contain e, and cycles with the same outside part have at most m_i+1 lengths. ∎

**4.5 Core criterion.** In the situation of 4.3, at an η-perfect step with η ≤ ε/4, every edge of W_q born after step q₀ lies on fewer than (1 − ε/2)·N_q cycle lengths. (By 4.4 the fraction is at most ρ_{q₀}/(2(1−η)ρ_q) ≤ (1+ε²)/((1−η)(1+2ε−2ε²)) < 1 − ε/2.)
Equivalently: **the halving step, and with it the lower bound, follows as soon as one perfect step has an edge born after q₀ that lies on at least (1−ε/2)·N_q cycle lengths.** Call such heavily used edges *core*; in a counterexample all core edges live in the fixed graph W_{q₀}, which has only m_{q₀} ≤ (φ+2^(2−R))·2^(t_{q₀}) edges.

**4.6 Where the next ear can attach.** Let P_q be a path with ends c, d.
- (i) If c, d ∈ V(W_j) for some j < q, every c–d path of W_q shorter than min over j ≤ i < q of |P_i| lies in W_j. (Take the last ear P_i the path touches; its inner vertices have degree 2 in W_{i+1} and are not ends of the path, so the path contains all of P_i.) So c, d already had those path lengths in W_j.
- (ii) If steps q−1 and q are η-perfect with η ≤ 1/10, then c and d are not both inner vertices of P_{q−1}. (Otherwise the c–d paths of W_q are a piece of P_{q−1}, or the rest of P_{q−1} plus a path of W_{q−1}: at most m_{q−1}+1 lengths, but 4.3(d) needs about 1.3·m_{q−1}.)

## 5. Core edges get used up: what is proved and what remains

**5.1 Bead model. [proved]** Call a step a *bead step* if C_q has exactly one edge e_q = cd inside W_q. Assume that every (ε/8)-perfect early step is a bead step and that no later ear ends in the interior of an earlier ear. Then there is no counterexample with r > t_{q₀} + m_{q₀} + 50/ε + 2 log₂(1/ε).

*Proof.* At a perfect bead step every c–d path other than e_q closes up with e_q, so by 4.3(d) e_q lies on at least (1−4η)N_q cycle lengths, and 4.5 forces e_q ∈ E(W_{q₀}). If e_q = e_{q′} for q < q′, then at step q′ a cycle through e that meets P_q is P_q ∪ e itself (P_q is still a path of degree-2 vertices), and the others avoid P_q, so as in 4.4 they have at most 2^(t_{q′}−t_q−1)(m_q+1) lengths, fewer than (1−ε/2)N_{q′}; contradiction. So perfect steps use distinct edges of W_{q₀}, and there are at most 48/ε other early steps. ∎

In this model the halving happens within m + O(1/ε) ranks of a witness with m edges. That is the true order (Bondy's graph does exactly this) and far below the paper's m ≤ √r.

**5.2 The construction does this. [checked]** Greedy witnesses of Bondy's graph with 8 shortcut chords (rank 12, 727 cycles), listing threads that lie on ≥ 75% of the cycle lengths:

| rank | edges | lengths | ρ | ν | heavily used threads |
|---|---|---|---|---|---|
| 7 | 30 | 22 | .250 | .172 | 5, all born at rank 5 |
| 8 | 47 | 38 | .191 | .148 | 4 |
| 9 | 80 | 70 | .160 | .137 | 3 |
| 10 | 145 | 134 | .144 | .131 | 2 |
| 11 | 274 | 262 | .135 | .128 | 1 |
| 12 | 532 | 519 | .130 | .127 | 0 |

One core edge is consumed per step; ρ and ν converge as 4.2 predicts; the inequality of 4.2 and the bound of 4.4 held in every instance tested.

**5.3 A variant with an ear ending inside an ear. [checked]** Replace two neighbouring beads of Bondy's graph, on core edges zc and cd, by an ear from c to d and an ear from the point of that ear next to d to z (a Wheatstone bridge: K₄ minus an edge). For k = 8 the graph still has rank 12 and every cycle length 3..n (728 cycles). The heavily used threads are again all born at rank 5 and again run out exactly at the last step, in the order 5, 4, 2, 2, 1, 0 or 5, 4, 3, 1, 1, 0 over ranks 7–12 (the two positions tried). Two are used up in one step and none in the next: "one core edge per perfect step" holds only on average, and the edge used up is not simply the chord of the new ear.

**5.4 Exact doubling: the two-terminal lemma. [proved; checked for all connected graphs on 4–6 labelled vertices]**

*Lemma T.* Let N be a connected graph with vertices s ≠ t in which every {s,t}-join is a path (equivalently: N has 2^β(N) paths from s to t, the largest possible number). Then N − E(A) is a forest for every s–t path A. In particular β(N) ≤ dist_N(s,t).

*Proof.* A cycle C of N − E(A) would make A + C = A ∪ C a join that is not a path. Deleting the edges of a shortest path A lowers the rank by at most |A| and leaves rank 0. ∎

Reading: let the edge f = st stand for everything built so far and N for what is added across it. "Every combination of the new ears closes to a cycle through f" is the hypothesis; β(N) is the number of binary digits gained; the lemma bounds it by the length of the shortest bypass, however the ears are attached (to the base, to each other, nested or crossing). Equality holds for Bondy's necklace, for the Wheatstone bridge (2 digits, bypass 2) and for K₃,₃ minus an edge (3 digits, bypass 3). As length gadgets the last two are no cheaper than beads: the Wheatstone bridge needs 3 short threads for its 2 digits, and K₃,₃ minus an edge needs 5 for its 3 digits (unit threads along a Hamiltonian path, long threads B, 2B, 4B; the eight path lengths are 5 and jB + 1, 2 or 3 for j = 1..7 **[checked]**). So in the exact regime neither a long bypass nor ears ending inside ears helps.

The same proof works relative to a witness: if every class of {c,d}-joins of W_q modulo Z(W_j) contains a path, then W_q − V(W_j) − E(A) is a forest for every c–d path A, so q − j is at most the number of edges outside W_j at V(W_j) plus |A \ E(W_j)|.

**5.5 Exact restriction count. [proved]**

*Lemma X.* Let G be 2-connected and W ⊆ G a connected subgraph containing a cycle. If every coset of Z(W) in Z(G) contains a cycle (no outside word is wasted), then β(G) − β(W) ≤ 2|V(W)| + 3.

*Proof.* (i) Every vertex v of W meets at most two edges outside W. Otherwise take outside edges e₁, e₂, e₃ and an edge e₄ of W at v, a cycle through e₁, e₂ and a cycle through e₃, e₄ (2-connectedness); their sum has outside degree ≥ 3 at v, and so does every member of its coset, which therefore contains no cycle. (ii) A nonzero even subgraph z of G − V(W) is the outside part of every member of its coset, and a cycle containing z equals z. So G − V(W) has no two edge-disjoint cycles, hence rank at most 4 (Erdős–Pósa: n+4 edges force two edge-disjoint cycles; K₃,₃ is extremal). (iii) Counting edges and vertices, β(G) − β(W) = #(edges outside W meeting V(W)) + β(G − V(W)) − #(components of G − V(W)) ≤ 2|V(W)| + 3. ∎

So the trivial count L − 2 ≤ 2^(r−t)·(m+1) can be attained only while r − t ≤ 2m + 3. Theorem 1.2 is the statement that for r − t ≥ m² half of it is lost.

**5.6 What is missing is robustness. [open]** In a counterexample the fraction of words of W_q wasted relative to an earlier witness W_j is at most δ = η_q + ½·Σ_{j ≤ i < q} κ_i, and Σκ < 2 (4.3), so almost every window is nearly exact. The robust forms of 5.4–5.5 that I can prove are these:

- If δ < 2^(−(q−j)), nothing is wasted and 5.4–5.5 apply to the pair (W_q, W_j).
- A cycle of W_q that avoids V(W_j) and consists of g threads wastes at least a fraction 2^(−g) − 2^(−(q−j)) of the words: an even subgraph contains a thread entirely or not at all, so the words containing the cycle form a coset of codimension ≤ g, and only one of them is a cycle. Hence in a window with waste δ every such cycle has at least min(q−j, log₂(1/2δ)) threads.
- A bridge of W_j with p ports and positive rank wastes about 2^(−p): its port set is empty with probability 2^(1−p), and then its part of the word must be empty (cf. 2(b)).

Each of these loses a factor exponential in the size of the configuration, and I do not think that is an artefact. An argument that exhibits wasted words one configuration at a time gets a fraction 2^(−g) per configuration, so it needs configurations of total weight Σ 2^(−g) ≳ 1. Nearly exact windows force the opposite: outside the base, a forest or a kernel of large girth. Weighing the overlapping long cycles of such a kernel is what the paper's non-backtracking count and second moment do. From the bounds above I get only "at least one wasted word, a fraction 2^(−2m−4), once r − t reaches 2m + 4"; and even a constant waste c every O(m) ranks would give only h(n) ≥ log₂ n + c′·log* n.

What a proof along §4–§5 would need is a quantity, the amount of *core* (edges on almost all cycle lengths, 4.5), that perfect steps use up and that only a full halving can replenish. 5.1 and 5.4 prove the first half when nothing is wasted. The second half is open. It holds in the examples: k beads placed inside an old bead of the necklace are usable only when that bead is used, so the usable fraction falls to (1+2^k)/2^(k+1) → ½, the same price as Bondy's extra chord.

**5.7 The leftover-rank identity, and one bound that does not lose exponentially. [proved]** Let H = G − V(W). An outside word x splits uniquely as x° ⊔ x^c, where x° consists of the components of x that meet V(W) and x^c is an even subgraph of H − V(x°); conversely any even subgraph of H − V(y) can be added to a word y with y^c = ∅. Hence

  2^(r−t) = Σ_y 2^β(H − V(y))  (sum over the words y with y^c = ∅),

and a word is usable only if x^c = ∅ or x° = ∅. So if a fraction u of the words is usable, then, apart from the at most 2^β(H) cycles avoiding W, the usable cycles Γ satisfy E[2^b(Γ)] ≤ 1/u on average, where b(Γ) = β(G − V(W) − V(Γ)) is the rank that Γ leaves untouched outside W. For u = 1 this is the forest property of 5.4. For u > ½ a usable cycle leaves a forest with probability at least 2u − 1.

*Lemma P.* In the situation of 4.3 put π(a) = (r − t_a) − β(G − V(W_a)); this is the number of edges outside W_a that meet V(W_a), minus the number of components of G − V(W_a). Then Σ 2^(−π(a)) ≤ 16/3, the sum being over the early steps a > q₀ with κ_{a−1} + 2η_a ≤ ¼ (all but at most 25 early steps).

*Proof.* Let y be the word of a cycle of W_a through an edge of P_{a−1}, and z an even subgraph of G − V(W_a). The words y ⊔ z are distinct for distinct (a, y, z). For equal a, y is the part of y ⊔ z in E(W_a). If y ⊔ z = y′ ⊔ z′ with a < a′, then y′ = y ⊔ (z ∩ E(W_{a′})), and the second piece is a nonempty even subgraph (it contains an edge of P_{a′−1}); but the outside part of a cycle contains no nonempty even subgraph other than itself, and y ≠ ∅. Such cycles carry N_a − N_{a−1} ≥ ¾(m_{a−1}+2) lengths, at most m+1 per word, so by 4.3(a) there are at least (3/16)·2^(t_a − t) words y at step a, each with 2^(r − t_a − π(a)) choices of z. There are 2^(r−t) words in all. ∎

So for all but about 2^(j+3) steps the later ears send at least j edges, beyond one per component, into V(W_a). Growth by ears attached only to recent ears is impossible: on average the vertex at which an ear is attached is at least about ½·log₂(r − t) steps old. This is the loss of 2(b) summed over all stages with the right weights; it does not bound r − t.

Why I think nothing simpler closes the gap **[heuristic]**: for a random even subgraph x of a cubic graph, a vertex is off x with probability ¼, and then each of its neighbours is off x with probability ½. Each kept vertex has two further neighbours, so the vertices left untouched by x form *critical* percolation clusters, and the expected number of cycles among them is a harmonic sum Σ 1/(2g) over lengths g. It diverges, which is the theorem, but only logarithmically. That would explain both the slow rate in Theorem 1.2 and why arguments using boundedly many configurations fall short.

## 6. Remark: Hamiltonian cycle plus chords **[proved; checked on 20,000 random instances]**

A pancyclic graph is a Hamiltonian cycle H plus chords. For a set S of chords there are exactly two even subgraphs using precisely the chords of S (complementary sets of arcs). If they have c₁ and c₂ components, then c₁ + c₂ ≤ |S| + 1, with equality iff no two chords of S cross. (H ∪ S on the chord ends is a 3-edge-coloured cubic graph; the three two-coloured families are H and the two subgraphs; Euler's formula.) So a non-crossing chord set gives at most one cycle, and a Hamiltonian graph with h chords has at most 2^h + #{S : both subgraphs are single cycles} cycles. Bondy's chords are non-crossing within a level; the extra chords are what cross.

## 7. What looks forced inside the paper's proof

- The ½ is one shared parity bit: for two disjoint regions, P(both cuts empty) = 2^(links−1) · product **[checked]**.
- Disjoint short cycles cannot suffice in a cubic graph of girth > log₂ r; one needs overlapping cycles, whose total weight is a harmonic sum that diverges only in near-cubic graphs. Hence the vertex splitting and the non-backtracking count.
- §4 does not remove the high-girth case. In a nearly exact window short cycles outside the base are what is excluded (5.6), so a forest or a high-girth kernel is what remains, and for the latter I found no way round the paper's estimate.

## 8. What I checked

- Re-derived Lemma 2.1, Corollary 2.2, the spectral bound, the link bound and the recurrence of the paper; found no gap.
- Brute force over cycle spaces: cut-correlation identity; cycle fractions of prisms and rings of diamonds; three-terminal necklace; greedy witnesses, ratio inequality and birth bound on Bondy's graph (k = 7, 8); the chord identity of §6.
- Second search: the Wheatstone variant of Bondy's graph (5.3); Lemma T on every connected graph with 4, 5 or 6 labelled vertices (no violation; equality occurs up to rank 3); the path lengths of K₃,₃ minus an edge (5.4); the identity of 5.7 on 300 random graphs with W a cycle; the counting inequality in the proof of Lemma P on Bondy's graph and its Wheatstone variant (63 ≤ 64 from the rank-6 witness, where every one of the 64 words is usable; 150 ≤ 256 from the rank-4 witness); the two local probabilities ¼ and ½ of 5.7 on the Petersen graph; Lemma X and steps (i), (ii) of its proof on 2138 random 2-connected graphs with no wasted word (W a cycle, 5–9 vertices; these have r − t ≤ 4, so the final bound is not tested near equality).
- Not checked by machine: the proofs of §4 and §5.1, and Lemma P as stated (hand proofs; the inequalities of 4.2 and 4.4 and the counting step of Lemma P were tested numerically on Bondy's graph, which is not a counterexample, so the parts that use the counterexample hypothesis were not exercised).
