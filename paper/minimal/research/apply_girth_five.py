# Writes the last case without bounded girth into a copy of the manuscript:
# Section 8 for girth at least five, no Section 7, no Lemma 5.5 and no Corollary 5.6, four cases
# in Section 9.
# Usage: python3 apply_girth_five.py <folder that contains exact-maximum.tex and sections/> [clean|lean]
#   clean (default): one lemma on pieces at girth five with the size C_1 k^7; no packing number in
#                    the statements.
#   lean:            Lemma 8.2 of the manuscript stays for pieces with many boundary vertices; a
#                    second lemma treats pieces with few boundary vertices at girth five; the
#                    blocks with a short cycle are counted as in apply_one_scale.py.
# Unchanged parts are copied from the present files by exact markers; a missing marker stops
# the script with exit code 1.  The script changes the copy only.
import sys, pathlib

root = pathlib.Path(sys.argv[1])
MODE = sys.argv[2] if len(sys.argv) > 2 else "clean"
if MODE not in ("clean", "lean"):
    print("FAILED: the mode is clean or lean"); sys.exit(1)

def fail(msg):
    print("FAILED:", msg); sys.exit(1)

def part(text, start, end, name):
    if text.count(start) != 1:
        fail(f"{name}: start has {text.count(start)} matches")
    i = text.index(start)
    j = text.index(end, i) + len(end)
    return text[i:j]

def sub(text, a, b, name):
    if text.count(a) != 1:
        fail(f"{name}: {text.count(a)} matches")
    return text.replace(a, b)

def cut(text, start, end, new, name):
    """Replace the part from `start` up to, and not including, `end`."""
    if text.count(start) != 1 or text.count(end) != 1:
        fail(f"{name}: {text.count(start)} and {text.count(end)} matches")
    i = text.index(start); j = text.index(end)
    if j < i:
        fail(f"{name}: wrong order")
    return text[:i] + new + text[j:]

# ---------------------------------------------------------------- large.tex
p = root / "sections" / "large.tex"
old = p.read_text()
NESTED = part(old, r"\begin{lemma}[Nested separators]\label{lem:nested}", r"of the sets $U_i$ by inclusion.", "nested")
FIGURE = part(old, r"\begin{figure}[ht]", r"\end{figure}", "figure")
FIGURE = sub(FIGURE, r"block end in its two end sets (proof of Proposition~\ref{prop:chain}).}",
             r"block end in its two end sets (Lemma~\ref{lem:blocks}).}", "figure caption")
i = old.index(r"\begin{lemma}[Two links]\label{lem:sep}")
j = old.index(r"\end{proof}", old.index(r"\begin{proof}", i)) + len(r"\end{proof}")
SEP = old[i:j]

new = r"""\section{Girth five outside a small set}\label{sec:half}

Recall that $q(G,P)$ is the probability that $\xi\cap E(G-P)$ is a forest.

\begin{theorem}\label{thm:half}
There is an integer $r_5$ with the following property. Let $G$ be a connected cubic multigraph of
rank $r\ge r_5$. Let $P$ be a nonempty set of at most $3\log r$ vertices such that $G[P]$ is
connected. If $G-P$ has girth at least five, then $q(G,P)<\frac25$.
\end{theorem}

\begin{idea}{outline of the proof}
A \emph{piece} is a large connected part of $G-P$ with a small boundary. A piece has a forest
proportion of less than $\frac35$, for every choice of the edges outside it
(Section~\ref{sec:affine}). The reason is this. A part with more forests is thin. A long thin
part contains a part in which every join is a forest. Such a part contains a ladder, and a ladder
has cycles of length four. Two disjoint pieces give $q(G,P)\le(\frac35)^{2}<\frac25$.

Suppose that $q(G,P)\ge\frac25$. Then a family of regions with a large total weight has many
pairs with exactly two links, by the second moment. These pairs give a long chain of nested
separators, and two pieces lie between them (Section~\ref{sec:heavy}). We use this for short
cycles (Section~\ref{sec:packing}) and for cycles of moderate length
(Section~\ref{sec:halfproof}).
\end{idea}

\subsection{Nested separators}\label{sec:separators}

""" + NESTED + r"""

""" + FIGURE + r"""

\begin{lemma}[Blocks]\label{lem:blocks}
Let $u$ and $p$ be two vertices of a connected graph $H$. Let $C_1<C_2<\dots<C_n$ be pairwise
disjoint connected sets that avoid $u$ and $p$ and separate $u$ from $p$, and let $w\ge1$ be an
integer. Then there are pairwise disjoint sets $Y_l\subseteq V(H)$, one for each integer $l\ge0$
with $(l+1)w\le n-1$, such that
\begin{enumerate}
\item[\textup{(i)}] $Y_l$ contains $w-1$ of the sets $C_i$;
\item[\textup{(ii)}] every edge of $H$ that leaves $Y_l$ ends in $C_{lw+1}$ or in $C_{(l+1)w+1}$;
\item[\textup{(iii)}] $Y_l$ lies in the component of $u$ in $H-C_{(l+1)w+1}$.
\end{enumerate}
\end{lemma}

\begin{proof}
Let $U_i$ be the vertex set of the component of $u$ in $H-C_i$. Then $U_i\cup C_i\subseteq U_j$
for $i<j$. For $i<j$ put $X_{ij}=U_j\sm(U_i\cup C_i)$. An edge of $H$ that leaves $U_j$ ends
in $C_j$, because $U_j$ is a component of $H-C_j$. No edge joins $X_{ij}$ to $U_i$: its end in
$X_{ij}$ would lie in the component $U_i$ of $H-C_i$. So every edge of $H$ that leaves $X_{ij}$
ends in $C_i$ or in $C_j$. If $i<l<j$, then $C_l\subseteq U_j$, and $C_l$ avoids
$U_i\cup C_i\subseteq U_l$; so $C_l\subseteq X_{ij}$. If $i<j\le i'<j'$, then
$X_{ij}\subseteq U_j\subseteq U_{i'}$ is disjoint from $X_{i'j'}$. So the sets
$Y_l=X_{lw+1,\,(l+1)w+1}$ have the three properties.
\end{proof}

\subsection{Joins}\label{sec:joinsfive}

Let $N$ be a connected subcubic multigraph. Its vertices of degree less than three are its
\emph{boundary vertices}, and its \emph{deficit} $d(N)$ is the sum of $3-\deg v$ over all
vertices $v$. A count of edge ends gives
\begin{equation}\label{eq:deficit}
  |V(N)|=2\beta(N)-2+d(N).
\end{equation}
Let $T$ be a set of boundary vertices of even size. A \emph{$T$-join} of $N$ is a set of edges in
which the vertices of $T$ have odd degree and all other vertices have even degree. There are
$2^{\beta(N)}$ of them. The \emph{forest proportion} of $T$ is the proportion of the $T$-joins
that are forests, and $T$ is \emph{rigid} if every $T$-join is a forest. A region $A$ of $N$ is
\emph{$T$-free} if it contains no vertex of $T$ and every component of $N-A$ contains an even
number of vertices of $T$.

\begin{lemma}[Free regions]\label{lem:free}
Let $J$ be a uniformly random $T$-join of $N$. For a region $A$ let $E_A$ be the event that
$J\cap\delta A=\emptyset$ and $J\cap E(N[A])\ne\emptyset$.
\begin{enumerate}
\item[\textup{(i)}] Let $A$ be a region without a vertex of $T$. Some $T$-join avoids $\delta A$
if and only if $A$ is $T$-free.
\item[\textup{(ii)}] If $A$ is $T$-free, then $E_A$ has the same probability as for a uniformly
random even subgraph of $N$.
\item[\textup{(iii)}] If $A$ and $B$ are disjoint $T$-free regions, then $E_A\cap E_B$ is empty,
or it has the same probability as for a uniformly random even subgraph of $N$.
\end{enumerate}
So the bound of Lemma~\ref{lem:smallcuts} holds for $J$ and pairwise disjoint $T$-free cyclic
regions: if there are $n$ of them, each with at most $d$ boundary edges, then the forest
proportion of $T$ is at most $\half+(d+1)2^{d-1}/n$.
\end{lemma}

\begin{proof}
(i) A $T$-join that avoids $\delta A$ has an even number of vertices of odd degree in each
component of $N-A$. In the other direction, each component $K$ of $N-A$ has a $(T\cap K)$-join if
$|T\cap K|$ is even. The union of these joins is a $T$-join $F$ without an edge that has an end
in $A$.

(ii) The map $J\mapsto J+F$ is a bijection from the $T$-joins to the even subgraphs of $N$, and
it keeps the edges that have an end in $A$. The event $E_A$ depends on these edges only.

(iii) Suppose that some $T$-join is in $E_A\cap E_B$. Delete its edges in $N[A]$ and in $N[B]$.
These form even subgraphs, so the result is a $T$-join $F'$ without an edge that has an end in
$A\cup B$. Use the map $J\mapsto J+F'$.

The proof of Lemma~\ref{lem:smallcuts} uses the probabilities of the events $E_i$ and upper
bounds for the probabilities of the events $E_i\cap E_j$. By (ii) and (iii) these hold for~$J$.
If $J$ is a forest, then no event $E_i$ occurs.
\end{proof}

\begin{lemma}[Product]\label{lem:product}
Let $N$ be a multigraph, and let $P$ and $T$ be sets of vertices such that $N$ has a $T$-join. Let
$U_1,\ldots,U_m\subseteq V(N)\sm(P\cup T)$ be pairwise disjoint sets of vertices of degree three
such that each $N[U_i]$ is connected. Let $f_1,\dots,f_m$ be numbers such that in $N[U_i]$ every
even set of boundary vertices has forest proportion at most $f_i$. Then $J\cap E(N-P)$ is a
forest for at most the proportion $f_1\cdots f_m$ of the $T$-joins $J$ of $N$. For a cubic
multigraph $G$ and $T=\emptyset$ this says that $q(G,P)\le f_1\cdots f_m$.
\end{lemma}

\begin{proof}
Let $E'$ consist of the edges that lie in none of the graphs $N[U_i]$, and let $J$ be a uniformly
random $T$-join. Fix a set $x\subseteq E'$ that extends to a $T$-join. For each $i$, let $T_i$ be
the set of the vertices of $U_i$ that are incident with an odd number of edges of $x$. The set
$U_i$ avoids $T$, so the parity equations say that $J\cap E(N[U_i])$ is a $T_i$-join. These
equations involve disjoint sets of edges, so the joins are independent and uniform, conditional on
$J\cap E'=x$. A vertex of degree three in $N[U_i]$ has no incident edge in $E'$. So $T_i$ is an
even set of boundary vertices. If $J\cap E(N-P)$ is a forest, its restriction to every $N[U_i]$
is a forest. The conditional probability is therefore at most $f_1\cdots f_m$. Average over $x$.
\end{proof}

The next two lemmas say that a multigraph of girth five with a rigid set is small. The ladder
shows that this is false for girth four: the two ends of one rail form a rigid set.

\begin{lemma}[Full pairs at girth five]\label{lem:fullfive}
Let $M$ be a connected subcubic multigraph of girth at least five. Let $x\ne y$ be vertices of
degree at most two such that every $\{x,y\}$-join of $M$ is a path. Then $|V(M)|<15\,d(M)$.
\end{lemma}

\begin{proof}
Put $d=d(M)$ and $b=\beta(M)$. If $b=0$, then $M$ is a tree and $|V(M)|=d-2$. Let $b\ge1$. Delete
a vertex of degree one other than $x$ and $y$, as long as there is one. If then $x$ has degree
one, delete $x$ and take its neighbour in the place of $x$; do the same for $y$; repeat. These
steps keep the rank, and every join is a path after each step. The two vertices stay distinct,
because $b\ge1$. The result $M_1$ is a pole in which the two vertices are ports and form a full
pair. A port of $M_1$ has degree two in $M$, or one of its edges in $M$ leads to a deleted tree,
and such a tree has a deficit of at least two. So $M_1$ has at most $d$ ports.

By Lemma~\ref{lem:reduction}, replace the other ports by edges. The result $M_1^{\circ}$
consists of bridges and of bridgeless $2$-poles $N_1,\dots,N_q$ with full pairs of ports, and
their ranks $b_i\ge1$ add up to $b$. An edge of $M_1^{\circ}$ is a path of $M_1$ whose inner
vertices are ports; call it \emph{plain} if this path has no inner vertex. At most $d-2$ edges
are not plain. A cycle of $M_1^{\circ}$ with at most four edges is not a cycle of $M$, so one of
its edges is not plain. By Lemma~\ref{lem:ladders}, $N_i$ is a pair of parallel edges, or a capped
ladder with some number $m$ of tiles. In the second case its rank is at most $2m+1$, and it
contains at least $m/3$ pairwise edge-disjoint cycles with at most four edges: the squares, pairs
of consecutive single rungs with the interface between them, and one cycle through a cap. So in
both cases at least $b_i/7$ edges of $N_i$ are not plain. Hence $b\le7(d-2)$,
and~\eqref{eq:deficit} gives $|V(M)|<15d$.
\end{proof}

\begin{lemma}[Rigid sets]\label{lem:rigidpiece}
Let $M$ be a connected subcubic multigraph of girth at least five with deficit $d$. Let
$\lambda\colon V(M)\to\mathbb Z$ be a map with $|\lambda(u)-\lambda(v)|\le1$ for every edge $uv$,
such that fewer than $W$ vertices have any given value. If some even set $U$ of boundary vertices
is rigid, then $|V(M)|\le500\,dW(W+d)$.
\end{lemma}

\begin{proof}
If $U=\emptyset$, then $M$ has no cycle, and $|V(M)|=d-2$. Let $U\ne\emptyset$. Let $S$ be a
connected subgraph of $M$ that contains $U$ and has as few edges as possible. It is a tree, and
its vertices of degree one are in $U$. Call a vertex of $S$ \emph{special} if it is in $U$ or has
degree three in $S$. There are at most $2|U|-2$ special vertices. A \emph{segment} is a path of
$S$ between two special vertices without a special inner vertex. The tree $S$ is the union of at
most $2|U|-3$ segments.

Put $\rho=30W+8d$ and $\ell_0=(2\rho+1)W+2$. Suppose that some segment $\sigma$ has at least
$2\ell_0$ edges, and let $z_0$ be a vertex of $\sigma$ with at least $\ell_0$ edges of $\sigma$
on each side. Let $B$ be the vertex set of the component of $z_0$ in the subgraph of $M$ induced
by the vertices $v$ with $|\lambda(v)-\lambda(z_0)|\le\rho$. Then $M[B]$ is connected, $B$ has
fewer than $(2\rho+1)W$ vertices, and it contains the $2\rho+1$ vertices of $\sigma$ nearest to
$z_0$.

\step{The tree meets $B$ in one part of $\sigma$.} Let $v$ be a vertex of $S$ in $B$, and let
$\pi$ be a path from $v$ to $z_0$ in $M[B]$. It has fewer than $\ell_0-2$ edges. If $v$ is not an
inner vertex of $\sigma$, or if $\sigma$ has more edges between $v$ and $z_0$ than $\pi$ has,
then $\pi$ can replace a part of $\sigma$ with more edges, and $S$ does not have the fewest
edges. So the vertices of $S$ in $B$ are inner vertices of $\sigma$, and $B$ contains no vertex
of $U$. Let $S^{-}$ and $S^{+}$ be the components of $S-B$ that contain the two ends of
$\sigma$. They are different, and every vertex of $U$ is in one of them. Let $x^{-}$ be the first
vertex of $\sigma$ in $B$, seen from the end in $S^{-}$, and let $x^{+}$ be the first one seen
from the other end. Then $x^{-}\ne x^{+}$, the vertex $x^{-}$ has a neighbour in $S^{-}$, and
$x^{+}$ has a neighbour in $S^{+}$. Let $K^{-}$ and $K^{+}$ be the components of $M-B$ that
contain $S^{-}$ and $S^{+}$, and put $U^{-}=U\cap V(S^{-})$.

\step{The set $B$ is small.} We claim that $|B|<15\,d(M[B])$. Suppose first that $K^{-}=K^{+}$
or that $|U^{-}|$ is even. Then $M-B$ contains a $U$-join. Its union with a cycle of $M[B]$ would
be a $U$-join that is not a forest. So $M[B]$ is a tree, and $|B|=d(M[B])-2$. Suppose now that
$K^{-}\ne K^{+}$ and that $|U^{-}|$ is odd. Let $J$ be an $\{x^{-},x^{+}\}$-join of $M[B]$. Add
an edge from $x^{-}$ to a neighbour $v^{-}$ in $K^{-}$, an edge from $x^{+}$ to a neighbour
$v^{+}$ in $K^{+}$, a join of $K^{-}$ for the set $U^{-}$ with $v^{-}$ added or removed, and a
join of $K^{+}$ for the set $U\sm U^{-}$ with $v^{+}$ added or removed. The result is a $U$-join
of $M$. So $J$ is a forest, and hence a path. The vertices $x^{-}$ and $x^{+}$ have degree at
most two in $M[B]$, and the claim is Lemma~\ref{lem:fullfive}.

An edge of $M$ that leaves $B$ starts in a vertex $v$ with $|\lambda(v)-\lambda(z_0)|=\rho$.
There are fewer than $2W$ such vertices, and each has at most two such edges. So
$d(M[B])<4W+d$, and the claim gives $|B|<60W+15d<2\rho+1$. This is a contradiction. So every
segment has fewer than $2\ell_0$ edges.

\step{The count.} So $S$ has fewer than $4|U|\,\ell_0\le4d\,\ell_0$ vertices. The set $V(S)$ is
connected and contains $U$. So $M-V(S)$ is a forest, as in the first case above. Let it have $f$
vertices. At most $|V(S)|+2$ edges join it to $S$, and a count of edge ends in the forest gives
$f\le|V(S)|+d$. Hence $|V(M)|\le8d\,\ell_0+d\le500\,dW(W+d)$.
\end{proof}

\subsection{Pieces with a small boundary}\label{sec:affine}

Put
\[
  R_{*}=R_{1/20},\qquad B=2R_{*}+2^{100}+1,
\]
with $R_{1/20}$ as in Section~\ref{sec:layers}. Then $\Theta_{1/20}(k)+k\le B(k+1)^{2}$ for all
$k\ge1$.

\begin{lemma}[Pieces]\label{lem:affine}
There is an absolute constant $C_1\ge2$ with the following property. Let $k\ge1$, and let $N$ be
a connected subcubic multigraph of girth at least five with at most $k$ boundary vertices and at
least $C_1k^{7}$ vertices. Then every set of boundary vertices of even size has forest proportion
less than $\frac35$.
\end{lemma}

\begin{proof}
For $k\ge1$ put $W_k=B(k+1)^{2}$, and let $s_k$ be the least integer with
$2^{s_k}>(2s_k+1)W_k$. Then $2^{s_k}\le2(2s_k+1)W_k$ and $s_k=O(\log k)$. Fix $k_0$ such that
$4s_k<k$ for all $k\ge k_0$. We define numbers $F(k)\ge2k$ below. Let $N$ have at most $k$ boundary
vertices, and let $T$ be an even set of boundary vertices with forest proportion at least
$\frac35$. We show by induction on $k$ that $N$ has fewer than $F(k)$ vertices. If $T$ is empty,
then $N$ has no cycle, and it has fewer than $2k$ vertices. So let $T$ be not empty. Fix a boundary vertex $o$, and call the set of the vertices at distance $j$ from $o$
the \emph{layer} $j$. Put $W=W_k$ and $s=s_k$.

\step{The layers are small.} Take a breadth-first tree of $N$ from $o$, and let $P$ be the union
of its paths from $o$ to the other boundary vertices. Then $N[P]$ is connected, every vertex
outside $P$ has degree three, and $P$ has at most $k$ vertices in each layer. The tree paths
inside $P$ contain a $T$-join $F_0$. The map $J\mapsto J+F_0$ is a bijection from the $T$-joins
of $N$ to the even subgraphs of $N$, and $J+F_0$ has the same edges in $N-P$ as $J$. So if $J$ is
a forest, then $J+F_0$ is a forest in $N-P$. Hence $q(N,P)\ge\frac35>\half+\frac1{20}$. The
distance from $o$ is a level function. By Lemma~\ref{lem:width} with $\delta=\frac1{20}$, each
layer has fewer than $\Theta_{1/20}(k)$ vertices outside $P$. So each layer has fewer than $W$
vertices.

\step{Few boundary vertices.} Let $k<k_0$. Put $h=10^{4}\,W^{3}$ and $F(k)=Wh\,(k+2^{Wh}+2)$, and
suppose that $N$ has at least $F(k)$ vertices. Then it has at least $h\,(k+2^{Wh}+2)$ layers.
Divide the layers $1,2,\dots$ into groups of $h$ consecutive layers. At least $2^{Wh}$ groups
contain no boundary vertex. In such a group let $M$ be a component of the subgraph induced by the
group that has a vertex $v$ in the last layer of the group. A shortest path from $o$ to $v$
shows that $M$ has a vertex in each layer of the group, so $|V(M)|\ge h$. The vertices of $M$
have degree three in $N$, and an edge that leaves $M$ starts in the first or in the last layer of
the group. So $d(M)<4W$, and the rank of $M$ is less than $Wh$. By
Lemma~\ref{lem:rigidpiece}, with the distance from $o$ in the place of $\lambda$, a rigid set of
$M$ would give $|V(M)|<500\cdot4W\cdot W\cdot5W=h$. So no even set of boundary vertices of $M$ is
rigid, and each of them has forest proportion at most $1-2^{-Wh}$. By Lemma~\ref{lem:product},
the forest proportion of $T$ is at most $(1-2^{-Wh})^{2^{Wh}}<\half$. This is a contradiction.

\step{Many boundary vertices.} Let $k\ge k_0$, and put $k'=4s$. Then $k'<k$. Put
\begin{gather*}
  w=\lceil k'F(k')/5\rceil+1,\qquad n_1=5(2s+1)\,2^{2s},\qquad n_2=k^{2}(k+2)\,w,\\
  F(k)=3\cdot2^{s}\bigl(k+2s\,(k+n_1+n_2+2)\bigr)+1 ,
\end{gather*}
and suppose that $N$ has at least $F(k)$ vertices. Call a cycle \emph{short} if its length is at
most $2s$. Let $\mathcal D$ be a maximal family of pairwise disjoint short cycles, and let $t$ be
their number. Let $w_0$ be a vertex, and let $W_0$ be the set of the vertices within distance $s$
of $w_0$. Suppose that $W_0$ contains no boundary vertex and no vertex of a cycle of
$\mathcal D$. Take a breadth-first tree from $w_0$. If some vertex at distance less than $s$ from
$w_0$ had fewer than two children in this tree, or $w_0$ fewer than three, then $N[W_0]$ would
contain a short cycle, and this cycle would meet a cycle of $\mathcal D$. So $|W_0|\ge2^{s}$.
But $W_0$ meets at most $2s+1$ layers, and $2^{s}/(2s+1)>W$. This contradicts the first step. A
ball of radius $s$ has at most $3\cdot2^{s}$ vertices. Hence $N$ has at most
$3\cdot2^{s}(k+2s\,t)$ vertices, and $t\ge k+n_1+n_2+2$.

At most $k$ cycles of $\mathcal D$ contain a boundary vertex. Each of the other cycles $Q$ has at
most $2s$ boundary edges, and $V(Q)$ contains no vertex of $T$. Call $Q$ \emph{free} if $V(Q)$
is $T$-free. So more than $n_1$ cycles are free, or more than $n_2$ cycles are not free. In the
first case Lemma~\ref{lem:free} with $d=2s$ shows that the forest proportion of $T$ is less than
$\half+(2s+1)\,2^{2s-1}/n_1=\frac35$. This is a contradiction.

In the second case let $Q$ be a cycle that is not free. Some component of $N-V(Q)$ contains an
odd number of vertices of $T$. The set $T$ is even and avoids $Q$. So $T$ has a vertex $a$ in
this component and a vertex $b$ in another component, and $V(Q)$ separates $a$ from $b$. There
are fewer than $k^{2}$ pairs $a,b$. So more than $(k+2)w$ of these cycles separate the same two
vertices $a$ and $b$. By Lemma~\ref{lem:nested} their vertex sets are linearly ordered, and
Lemma~\ref{lem:blocks} for $N$, $a$ and $b$ gives $k+2$ pairwise disjoint sets $Y_l$. At most
$k$ of them contain a boundary vertex of $N$. Let $Y_1$ and $Y_2$ be two of the others, and let
$i\in\{1,2\}$. The set $Y_i$ contains $w-1$ of the cycles, and each cycle has at least five
vertices. So $|Y_i|\ge5(w-1)\ge k'F(k')$. At most $2\cdot2s=k'$ edges leave $Y_i$, and every
component of $N[Y_i]$ has such an edge, because $b\notin Y_i$. So some component has a vertex set
$Y_i'$ with at least $F(k')$ vertices. The vertices of $Y_i$ have degree three in $N$, so
$N[Y_i']$ has at most $k'$ boundary vertices. By induction, every even set of boundary vertices
of $N[Y_i']$ has forest proportion less than $\frac35$. Lemma~\ref{lem:product}, for $N$, $T$,
$P=\emptyset$ and the disjoint sets $Y_1'$ and $Y_2'$, shows that the forest proportion of $T$
is at most $\frac9{25}$. This is a contradiction.

\step{The size of $F$.} We have $2^{s}=O(k^{2}\log k)$ and $s=O(\log k)$. So
$n_1=O(k^{4}\log^{3}k)$ and $n_2=O\bigl(k^{3}\log k\cdot F(4s_k)\bigr)$, and the definition gives
$F(k)=O\bigl(k^{6}\log^{5}k+k^{5}\log^{3}k\cdot F(4s_k)\bigr)$ for $k\ge k_0$. Hence
$F(k)\le C_1k^{7}$ for an absolute constant $C_1$, by induction on $k$.
\end{proof}

\subsection{Heavy families}\label{sec:heavy}

Let $C_1$ be as in Lemma~\ref{lem:affine}.

\begin{idea}{two links give a separator}
If two disjoint connected sets have exactly two links, then one of them separates a neighbour of
the other one from a fixed vertex $p$. Disjoint sets that separate the same two vertices are
nested, and the parts between them have small boundaries (Figure~\ref{fig:chain}). So a long
chain of such sets contains two pieces.
\end{idea}

\begin{proposition}[A long chain]\label{prop:chain}
Let $G$ be a connected cubic multigraph, and let $P$ be a nonempty set of vertices such that
$G[P]$ is connected and $G-P$ has girth at least five. Let $p\in P$, let $A$ be a region that
avoids $P$, and let $u\notin A$ be a vertex in the component of $p$ in $G-A$. Let $C_1,\dots,C_T$
be pairwise disjoint regions that avoid $P$, $A$ and $u$ and separate $u$ from $p$ in $G-A$. Let
$\Lambda\ge1$ be an integer and $m\ge1$ a number such that $A$ and every $C_i$ have at most
$\Lambda$ boundary edges, and every $C_i$ has at least $m$ vertices. If
\[
  T\;>\;(\Lambda+2)\bigl(\lceil2^{8}C_1\Lambda^{8}/m\rceil+1\bigr),
\]
then $q(G,P)\le\frac9{25}$.
\end{proposition}

\begin{proof}
Each $C_i$ is connected and separates $u$ from $p$ in $G-A$. So it lies in the component $H$ of
$G-A$ that contains $u$ and $p$. By Lemma~\ref{lem:nested} we may assume that
$C_1<C_2<\dots<C_T$. Put $w=\lceil2^{8}C_1\Lambda^{8}/m\rceil+1$. Lemma~\ref{lem:blocks} gives at
least $\Lambda+2$ pairwise disjoint sets $Y_l$. The set $P$ is connected, it contains $p$, and it
is disjoint from $A$ and from the sets $C_i$. So $P$ lies in the component of $p$ in $H-C_i$ for
every $i$, and every $Y_l$ avoids $P$. At most $\Lambda$ of the sets $Y_l$ contain a vertex with a
neighbour in $A$. Let $Y$ be one of the others. The edges of $G$ that leave $Y$ are edges of $H$,
so $|\delta Y|\le2\Lambda$, and $|Y|\ge(w-1)m\ge2\Lambda\cdot C_1(2\Lambda)^{7}$. Every component
of $G[Y]$ has an edge that leaves $Y$. So there are at most $2\Lambda$ components, and one of them
has a vertex set $Y'$ with at least $C_1(2\Lambda)^{7}$ vertices. A boundary vertex of $G[Y']$ is
an end of an edge of $\delta Y$, so there are at most $2\Lambda$ of them, and $G[Y']$ has girth at
least five. By Lemma~\ref{lem:affine}, every even set of boundary vertices of $G[Y']$ has forest
proportion less than $\frac35$. There are two sets $Y$, and Lemma~\ref{lem:product} for their two
sets $Y'$ gives $q(G,P)\le\frac9{25}$.
\end{proof}

""" + SEP + r"""

\begin{proposition}[Heavy families]\label{prop:heavy}
Let $G$ be a connected cubic multigraph, and let $P$ be a nonempty set of vertices such that
$G[P]$ is connected, $G-P$ has girth at least five, and $q(G,P)\ge\frac25$. Let $\mathcal A$ be a
finite family of regions that avoid $P$, with weights $w_A\ge0$ of total $\mu$, and let $W_2$ be
as in Lemma~\ref{lem:sep}. Let $\Lambda\ge1$ be an integer, and let $m\ge1$, $\kappa>0$ and
$K\ge0$ be numbers such that
\begin{enumerate}
\item[\textup{(a)}] every region of $\mathcal A$ has at most $\Lambda$ boundary edges and at
least $m$ vertices;
\item[\textup{(b)}] for every $A\in\mathcal A$, the regions of $\mathcal A$ that meet $A$ have
total weight at most $\kappa$;
\item[\textup{(c)}] some random variable $Z\ge0$ has $\EE Z=\mu$ and
$\EE Z^{2}\le\mu^{2}+W_2+K\mu$, and $Z=0$ whenever $\xi\cap E(G-P)$ is a forest.
\end{enumerate}
Then
\[
  \mu\;\le\;\tfrac32K+3\Lambda\kappa\,(\Lambda+3)\bigl(\lceil2^{8}C_1\Lambda^{8}/m\rceil+1\bigr).
\]
\end{proposition}

\begin{proof}
Put $w=\lceil2^{8}C_1\Lambda^{8}/m\rceil+1$. We may assume that $\mu>\frac32K+3\Lambda\kappa$.
By~(c), $\PP(Z\ne0)\le1-q(G,P)\le\frac35$, and the Cauchy--Schwarz inequality
$\mu^{2}\le\EE Z^{2}\cdot\PP(Z\ne0)$ gives $W_2\ge\frac23\mu^{2}-K\mu$.

Fix $p\in P$. We apply Lemma~\ref{lem:sep}. Let $A\in\mathcal A$. By~(a), at most $\Lambda$
vertices outside $A$ have a neighbour in $A$, and a region that is joined to $A$ by an edge
contains one of them. The regions of $\mathcal A$ that contain a given vertex all meet one of
them, so their total weight is at most $\kappa$ by~(b). Hence we may take $N=\Lambda$ and
$e=\Lambda\kappa$. The lemma gives a region $A\in\mathcal A$, a vertex $u\notin A$ in the
component of $p$ in $G-A$, and regions of $\mathcal A$ of total weight at least
$(\mu/3-K/2-\Lambda\kappa)/\Lambda$ that are disjoint from $A$, avoid $u$, and separate $u$ from
$p$ in $G-A$. Take a maximal family $C_1,\dots,C_T$ of pairwise disjoint regions among them. Each
of these regions meets some $C_i$, so their total weight is at most $T\kappa$ by~(b). As
$q(G,P)>\frac9{25}$, Proposition~\ref{prop:chain} gives $T\le(\Lambda+2)\,w$. So
$\mu/3-K/2-\Lambda\kappa\le\Lambda\kappa\,(\Lambda+2)\,w$, and the claim follows because $w\ge1$.
\end{proof}

\subsection{Packing of short cycles}\label{sec:packing}

\begin{idea}{the purpose of the packing bound}
The second-moment argument requires a graph of girth about $\log r$. So we delete a maximal
family of disjoint short cycles, and we need a bound for the size of this family.
Lemma~\ref{lem:smallcuts} gives such a bound only when the proportion of forests exceeds one half
by a fixed margin. Here the bound follows from Proposition~\ref{prop:heavy}.
\end{idea}

\begin{proposition}[Packing]\label{prop:packing}
Let $G$ be a connected cubic multigraph, and let $P$ be a nonempty set of vertices such that
$G[P]$ is connected. Suppose that $q(G,P)\ge\frac25$ and that $G-P$ has girth at least five.
Then, for every integer $d\ge5$, the multigraph $G-P$ has at most $2^{10}C_1\,2^{d}d^{10}$
pairwise disjoint cycles of length at most $d$.
\end{proposition}

\begin{proof}
Let $Q_1,\dots,Q_n$ be such cycles, and put $X_i=V(Q_i)$. Every vertex of $Q_i$ lies on exactly
one edge outside $Q_i$, and $Q_i$ has at least five vertices. So $X_i$ is a cyclic region with at
most $d$ boundary edges and at least five vertices. Let $E_i$ be the event that $\cO_{X_i}$
holds and $\xi\cap E(G[X_i])\ne\emptyset$. Put $p_i=\PP(E_i)$, let $Z$ be the number of the events
$E_i$ that occur, and put $\mu=\EE Z$. As in the proof of Lemma~\ref{lem:smallcuts}, we have
$p_i\ge2^{-d-1}$ and $\PP(E_i\cap E_j)=2^{\ell(X_i,X_j)-1}p_ip_j$ for $i\ne j$, and for each $i$
at most $d$ indices $j$ have $\ell(X_i,X_j)\ge3$. Let $W_2$ be the sum of $p_ip_j$ over the
ordered pairs $(i,j)$ with $\ell(X_i,X_j)=2$. Then $\EE Z^{2}\le\mu^{2}+W_2+(d+1)\mu$. If
$\xi\cap E(G-P)$ is a forest, then no event $E_i$ occurs, and $Z=0$.

So Proposition~\ref{prop:heavy} applies to the sets $X_i$ with the weights $p_i$, and with
$\Lambda=d$, $m=5$, $\kappa=1$ and $K=d+1$; property~(b) holds because the sets are pairwise
disjoint and $p_i\le1$. It gives
\[
  \mu\;\le\;\tfrac32(d+1)+3d\,(d+3)\bigl(\lceil2^{8}C_1d^{8}/5\rceil+1\bigr)\;\le\;2^{9}C_1\,d^{10},
\]
and $n\le2^{d+1}\mu$.
\end{proof}

\subsection{Proof of Theorem~\ref{thm:half}}\label{sec:halfproof}

Let $G$ and $P$ be as in the theorem, and suppose that $q(G,P)\ge\frac25$. We derive a
contradiction when $r$ is large. All limits below are for $r\to\infty$, and they are uniform in
$G$ and $P$. Put
\[
  x=\log r,\qquad A=6\,e^{124},\qquad L=\lfloor Ax\rfloor,\qquad D=\lceil x/16\rceil .
\]

\paragraph{Cycles of moderate length.}
Let $S$ be the union of the vertex sets of a maximal family of pairwise disjoint cycles of length
at most $D$ in $G-P$. By Proposition~\ref{prop:packing}, $|S|\le2^{10}C_1\,2^{D}D^{11}\le r/x^{2}$
for large $r$. We use Proposition~\ref{prop:loggirth} for $G$, $P$, $D$, $L$ and $S$. Its
hypotheses hold for large $r$: the set $P$ has at most $3x$ vertices and $G[P]$ is connected,
$x/16\le D\le x/8$, and $7x\le L\le x\sqrt{\log x}$. So we are in the setting of
Section~\ref{sec:moderate}, with $\Gamma=G$, $U=P\cup S$ and $J=G-U$. The set $\mathcal C$
consists of the cycles of $J$ of length at most $L$, and the numbers $s$, $a_C$, $\mu$ and $W_2$
and the random variable $Z$ are defined there. With $\eta=r^{-1/60}$ the proposition gives
\[
  L^{2}2^{-s}\le\eta,\qquad \mu\;\ge\;\frac14\ln\frac{L}{6x}-\frac1{\sqrt x}\;>\;30,\qquad
  \EE Z^{2}\;\le\;\mu^{2}+W_2+(1+\eta)\mu .
\]
The bound $\mu>30$ holds because $L/(6x)\ge e^{124}-1$.

\paragraph{The contradiction.}
We apply Proposition~\ref{prop:heavy} to the vertex sets of the cycles of $\mathcal C$, with the
weights $a_C$, and with $\Lambda=L$, $m=x/16$, $\kappa=\eta$ and $K=1+\eta$. A cycle
$C\in\mathcal C$ has at most $L$ vertices, each of them has one edge end outside $C$, and the
girth of $J$ is greater than $D\ge x/16$. So $V(C)$ has at most $L$ boundary edges and at least
$x/16$ vertices; this is~(a). A cycle of $\mathcal C$ that meets $C$ passes through one of the
at most $L$ vertices of $C$, so~(b) holds by~\eqref{eq:load}. If $\xi\cap E(G-P)$ is a forest,
then $\xi$ contains no cycle of $J$, and $Z=0$; this is~(c). So
\[
  \mu\;\le\;\tfrac32(1+\eta)+3L\eta\,(L+3)\bigl(\lceil2^{12}C_1L^{8}/x\rceil+1\bigr)
  \;=\;\tfrac32+o(1),
\]
because $L\le Ax$ and $\eta=r^{-1/60}$. This contradicts $\mu>30$, and
Theorem~\ref{thm:half} is proved. \qed
"""
CLEAN = new

# ---------------------------------------------------------------- the lean form of Section 8
AFFINE = part(old, r"\begin{lemma}[Forest proportions at large girth]\label{lem:affine}",
              "This is a contradiction.\n\\end{proof}", "lemma on large girth")
AFFINE = sub(AFFINE, r"There are absolute constants $C_0$ and $C_1\ge1$ with the following property.",
             r"There are absolute constants $C_0\ge1$ and $C_1\ge1$ with the following property.", "constants 1")
AFFINE = sub(AFFINE, r"constants $C_0$ and $C_1$ such that $2s<C_0\log(\Lambda+2)$",
             r"constants $C_0\ge1$ and $C_1\ge1$ such that $2s<C_0\log(\Lambda+2)$", "constants 2")
FIGURE0 = part(old, r"\begin{figure}[ht]", r"\end{figure}", "figure")
CHAINHEAD = part(old, r"Each $C_i$ is connected and separates $u$ from $p$ in $G-A$. So it lies in the component $H$ of",
                 r"$X_{ij}\subseteq U_j\subseteq U_{i'}$ is disjoint from $X_{i'j'}$.", "chain blocks")
PRODUCT = part(CLEAN, r"\begin{lemma}[Product]\label{lem:product}", "Average over $x$.\n\\end{proof}", "product")
FULLRIGID = part(CLEAN, r"\begin{lemma}[Full pairs at girth five]\label{lem:fullfive}",
                 "Hence $|V(M)|\\le8d\\,\\ell_0+d\\le500\\,dW(W+d)$.\n\\end{proof}", "full pairs and rigid sets")
THM5 = part(CLEAN, r"\begin{theorem}\label{thm:half}", r"\end{theorem}", "theorem")

LEAN = r"""\section{Girth five outside a small set}\label{sec:half}

Recall that $q(G,P)$ is the probability that $\xi\cap E(G-P)$ is a forest.

""" + THM5 + r"""

\begin{idea}{outline of the proof}
Suppose that $q(G,P)\ge\frac25$. We find two disjoint parts of $G-P$ that are large and have
small boundaries. Each of them has a forest proportion of at most $\frac35$, for every choice of
the edges outside it. This is a contradiction, because $(\frac35)^{2}<\frac25$. For a part with
many boundary vertices this needs that the part contains no short cycle. For a part with few
boundary vertices it needs girth five only, because a ladder has cycles of length four
(Section~\ref{sec:affine}). The parts come from a family of regions with a large total weight:
the second moment gives many pairs with exactly two links, and these pairs give nested separators
(Section~\ref{sec:separators}). We use this for short cycles (Section~\ref{sec:packing}) and
for cycles of moderate length (Section~\ref{sec:halfproof}).
\end{idea}

\subsection{Pieces with a small boundary}\label{sec:affine}

Let $N$ be a connected subcubic multigraph. Its vertices of degree less than three are its
\emph{boundary vertices}, and its \emph{deficit} $d(N)$ is the sum of $3-\deg v$ over all
vertices $v$. A count of edge ends gives
\begin{equation}\label{eq:deficit}
  |V(N)|=2\beta(N)-2+d(N).
\end{equation}
Let $T$ be a set of boundary vertices of even size. A \emph{$T$-join} of $N$ is a set of edges in
which the vertices of $T$ have odd degree and all other vertices have even degree. There are
$2^{\beta(N)}$ of them. The \emph{forest proportion} of $T$ is the proportion of the $T$-joins
that are forests, and $T$ is \emph{rigid} if every $T$-join is a forest. For $T=\emptyset$ the
$T$-joins are the even subgraphs, only the empty one is a forest, and the forest proportion is
$2^{-\beta(N)}$. Put
\[
  R_{*}=R_{1/20},\qquad B=2R_{*}+2^{100}+1,
\]
with $R_{1/20}$ as in Section~\ref{sec:layers}. Then $\Theta_{1/20}(k)+k\le B(k+1)^{2}$ for all
$k\ge1$.

""" + AFFINE + r"""

""" + PRODUCT + r"""

The next three lemmas treat a piece with few boundary vertices at girth five. The ladder shows
that girth four is not sufficient: the two ends of one rail form a rigid set.

""" + FULLRIGID + r"""

\begin{lemma}[Pieces at girth five]\label{lem:piecesfive}
For every integer $k\ge1$ there is a number $F_0(k)$ with the following property. Let $N$ be a
connected subcubic multigraph of girth at least five with at most $k$ boundary vertices and at
least $F_0(k)$ vertices. Then every set of boundary vertices of even size has forest proportion
less than $\frac35$.
\end{lemma}

\begin{proof}
Put $W=B(k+1)^{2}$, $h=10^{4}\,W^{3}$ and $F_0(k)=Wh\,(k+2^{Wh}+2)$. Suppose that some even set
$T$ of boundary vertices has forest proportion at least $\frac35$. If $T$ is empty, then $N$ has
no cycle and fewer than $2k$ vertices. In the other case fix a boundary vertex $o$, and define the
layers as in the proof of Lemma~\ref{lem:affine}. The step ``A marker'' of that proof uses no
girth, and it shows that each layer has fewer than $W$ vertices. So $N$ has at least
$h\,(k+2^{Wh}+2)$ layers. Divide the layers $1,2,\dots$ into groups of $h$ consecutive layers. At
least $2^{Wh}$ groups contain no boundary vertex. In such a group let $M$ be a component of the
subgraph induced by the group that has a vertex $v$ in the last layer of the group. A shortest
path from $o$ to $v$ shows that $M$ has a vertex in each layer of the group, so $|V(M)|\ge h$.
The vertices of $M$ have degree three in $N$, and an edge that leaves $M$ starts in the first or
in the last layer of the group. So $d(M)<4W$, and the rank of $M$ is less than $Wh$. By
Lemma~\ref{lem:rigidpiece}, with the distance from $o$ in the place of $\lambda$, a rigid set of
$M$ would give $|V(M)|<500\cdot4W\cdot W\cdot5W=h$. So no even set of boundary vertices of $M$ is
rigid, and each of them has forest proportion at most $1-2^{-Wh}$. By Lemma~\ref{lem:product},
the forest proportion of $T$ is at most $(1-2^{-Wh})^{2^{Wh}}<\half$. This is a contradiction.
\end{proof}

Let $C_0$ and $C_1$ be as in Lemma~\ref{lem:affine} and $F_0$ as in
Lemma~\ref{lem:piecesfive}. From now on $\Lambda_0\ge7$ is a fixed integer such that every integer
$d\ge\Lambda_0$ satisfies
\[
  \bigl(C_0\log(d+2)\bigr)^{C_0+9}\le d,\qquad (d+2)^{C_0}\le2\,d^{\,C_0},\qquad d^{2}\ge20\,C_1 .
\]
Then $C_0\log(d+2)\le d$. Let $C_2\ge4$ be a number with $C_2\ge F_0(2\Lambda)$ for
$4\le\Lambda<\Lambda_0$. For an integer $\Lambda\ge4$ put $\Phi(\Lambda)=C_1\Lambda^{4}$ if
$\Lambda\ge\Lambda_0$, and $\Phi(\Lambda)=C_2$ if $\Lambda<\Lambda_0$. Call a cycle
\emph{$\Lambda$-short} if $\Lambda\ge\Lambda_0$ and its length is less than
$C_0\log(\Lambda+2)$. For a multigraph $G$ and a set $P$ of vertices, let $\nu_\Lambda(G,P)$ be
the largest number of pairwise disjoint $\Lambda$-short cycles of $G-P$. By
Lemmas~\ref{lem:affine} and~\ref{lem:piecesfive}, a connected subcubic multigraph of girth at
least five with at most $2\Lambda$ boundary vertices, at least $\Phi(\Lambda)$ vertices and no
$\Lambda$-short cycle has a forest proportion of less than $\frac35$ for every even set of
boundary vertices.

\subsection{Separators}\label{sec:separators}

\begin{idea}{two links give a separator}
If two disjoint connected sets have exactly two links, then one of them separates a neighbour of
the other one from a fixed vertex $p$. Disjoint sets that separate the same two vertices are
nested, and the parts between them have small boundaries (Figure~\ref{fig:chain}). So a long
chain of such sets contains two pieces without a short cycle.
\end{idea}

""" + NESTED + r"""

""" + FIGURE0 + r"""

\begin{proposition}[A long chain]\label{prop:chain}
Let $G$ be a connected cubic multigraph, and let $P$ be a nonempty set of vertices such that
$G[P]$ is connected and $G-P$ has girth at least five. Let $p\in P$, let $A$ be a region that
avoids $P$, and let $u\notin A$ be a vertex in the component of $p$ in $G-A$. Let $C_1,\dots,C_T$
be pairwise disjoint regions that avoid $P$, $A$ and $u$ and separate $u$ from $p$ in $G-A$. Let
$\Lambda\ge4$ be an integer and $m\ge1$ a number such that $A$ and every $C_i$ have at most
$\Lambda$ boundary edges, and every $C_i$ has at least $m$ vertices. If
\[
  T\;>\;\bigl(\Lambda+\nu_\Lambda(G,P)+2\bigr)\bigl(\lceil2\Lambda\,\Phi(\Lambda)/m\rceil+1\bigr),
\]
then $q(G,P)\le\frac9{25}$.
\end{proposition}

\begin{proof}
""" + CHAINHEAD + r"""

Put $w=\lceil2\Lambda\,\Phi(\Lambda)/m\rceil+1$, and let $Y_l=X_{lw+1,\,(l+1)w+1}$ for
$l=0,1,\dots$ with $(l+1)w\le T-1$. These sets are pairwise disjoint, each contains $w-1$ of the
sets $C_i$, and every edge of $H$ that leaves $Y_l$ ends in one of its two end sets. So
$|Y_l|\ge(w-1)m\ge2\Lambda\,\Phi(\Lambda)$, and at most $2\Lambda$ edges of $H$ leave $Y_l$.

There are at least $\Lambda+\nu+2$ sets $Y_l$, where $\nu=\nu_\Lambda(G,P)$. The set $P$ is
connected, it contains $p$, and it is disjoint from $A$ and from the sets $C_i$. So $P$ lies in
the component of $p$ in $H-C_i$ for every $i$, and every $Y_l$ avoids $P$. Discard $Y_l$ if it
contains a vertex with a neighbour in $A$, or if $G[Y_l]$ contains a $\Lambda$-short cycle. The
sets $Y_l$ are pairwise disjoint, so this discards at most $\Lambda+\nu$ sets, and two sets
remain. Let $Y$ be one of them. The edges of $G$ that leave $Y$ are edges of $H$, so
$|\delta Y|\le2\Lambda$.

\step{Pieces.} Every component of $G[Y]$ has an edge that leaves $Y$. So there are at most
$2\Lambda$ components, and one of them has a vertex set $Y'$ with at least $\Phi(\Lambda)$
vertices. A boundary vertex of $G[Y']$ is an end of an edge of $\delta Y$, so there are at most
$2\Lambda$ of them, and $G[Y']$ has girth at least five and no $\Lambda$-short cycle. So every
even set of boundary vertices of $G[Y']$ has forest proportion less than $\frac35$.
Lemma~\ref{lem:product}, for the two sets $Y'$, gives $q(G,P)\le\frac9{25}$.
\end{proof}

""" + SEP + r"""

\begin{proposition}[Heavy families]\label{prop:heavy}
Let $G$ be a connected cubic multigraph, and let $P$ be a nonempty set of vertices such that
$G[P]$ is connected, $G-P$ has girth at least five, and $q(G,P)\ge\frac25$. Let $\mathcal A$ be a
finite family of regions that avoid $P$, with weights $w_A\ge0$ of total $\mu$, and let $W_2$ be
as in Lemma~\ref{lem:sep}. Let $\Lambda\ge4$ be an integer, and let $m\ge1$, $\kappa>0$ and
$K\ge0$ be numbers such that
\begin{enumerate}
\item[\textup{(a)}] every region of $\mathcal A$ has at most $\Lambda$ boundary edges and at
least $m$ vertices;
\item[\textup{(b)}] for every $A\in\mathcal A$, the regions of $\mathcal A$ that meet $A$ have
total weight at most $\kappa$;
\item[\textup{(c)}] some random variable $Z\ge0$ has $\EE Z=\mu$ and
$\EE Z^{2}\le\mu^{2}+W_2+K\mu$, and $Z=0$ whenever $\xi\cap E(G-P)$ is a forest.
\end{enumerate}
Then
\[
  \mu\;\le\;\tfrac32K+3\Lambda\kappa\,\bigl(\Lambda+\nu_\Lambda(G,P)+3\bigr)
  \bigl(\lceil2\Lambda\,\Phi(\Lambda)/m\rceil+1\bigr).
\]
\end{proposition}

\begin{proof}
Put $\nu=\nu_\Lambda(G,P)$ and $w=\lceil2\Lambda\,\Phi(\Lambda)/m\rceil+1$. We may assume that
$\mu>\frac32K+3\Lambda\kappa$. By~(c), $\PP(Z\ne0)\le1-q(G,P)\le\frac35$, and the Cauchy--Schwarz
inequality $\mu^{2}\le\EE Z^{2}\cdot\PP(Z\ne0)$ gives $W_2\ge\frac23\mu^{2}-K\mu$.

Fix $p\in P$. We apply Lemma~\ref{lem:sep}. Let $A\in\mathcal A$. By~(a), at most $\Lambda$
vertices outside $A$ have a neighbour in $A$, and a region that is joined to $A$ by an edge
contains one of them. The regions of $\mathcal A$ that contain a given vertex all meet one of
them, so their total weight is at most $\kappa$ by~(b). Hence we may take $N=\Lambda$ and
$e=\Lambda\kappa$. The lemma gives a region $A\in\mathcal A$, a vertex $u\notin A$ in the
component of $p$ in $G-A$, and regions of $\mathcal A$ of total weight at least
$(\mu/3-K/2-\Lambda\kappa)/\Lambda$ that are disjoint from $A$, avoid $u$, and separate $u$ from
$p$ in $G-A$. Take a maximal family $C_1,\dots,C_T$ of pairwise disjoint regions among them. Each
of these regions meets some $C_i$, so their total weight is at most $T\kappa$ by~(b). As
$q(G,P)>\frac9{25}$, Proposition~\ref{prop:chain} gives $T\le(\Lambda+\nu+2)\,w$. So
$\mu/3-K/2-\Lambda\kappa\le\Lambda\kappa\,(\Lambda+\nu+2)\,w$, and the claim follows because
$w\ge1$.
\end{proof}

\subsection{Packing of short cycles}\label{sec:packing}

\begin{idea}{the purpose of the packing bound}
The second-moment argument requires a graph of girth about $\log r$. So we delete a maximal
family of disjoint short cycles, and we need a bound for the size of this family.
Lemma~\ref{lem:smallcuts} gives such a bound only when the proportion of forests exceeds one half
by a fixed margin. Here Proposition~\ref{prop:heavy} gives a bound for the cycles of length at
most $d$. For large $d$ it contains the number of disjoint cycles of length about $\log d$, and
for this number we use induction.
\end{idea}

\begin{proposition}[Packing]\label{prop:packing}
Let $G$ be a connected cubic multigraph, and let $P$ be a nonempty set of vertices such that
$G[P]$ is connected. Suppose that $q(G,P)\ge\frac25$ and that $G-P$ has girth at least five. Let
$d\ge5$ be an integer, and put $C_3=8C_2$. Then
\begin{enumerate}
\item[\textup{(i)}] $G-P$ has at most $C_3\,2^{d}d^{\,C_0+9}$ pairwise disjoint cycles of length
at most $d$;
\item[\textup{(ii)}] $\nu_d(G,P)\le2\,C_3\,d^{\,C_0+1}$.
\end{enumerate}
\end{proposition}

\begin{proof}
We use induction on $d$. Suppose that~(i) holds for every smaller integer that is at least five.

\step{The shorter cycles.} If $d<\Lambda_0$, no cycle is $d$-short. Let $d\ge\Lambda_0$, and let
$g$ be the largest integer that is less than $C_0\log(d+2)$. Then $g<d$, and a cycle is $d$-short
if and only if its length is at most $g$. If $g<5$, then $G-P$ has no such cycle. Otherwise~(i)
for $g$ and the choice of $\Lambda_0$ give
\[
  \nu_d(G,P)\;\le\;C_3\,2^{g}g^{\,C_0+9}\;\le\;C_3\,(d+2)^{C_0}\bigl(C_0\log(d+2)\bigr)^{C_0+9}
  \;\le\;2\,C_3\,d^{\,C_0+1}.
\]
This is~(ii).

\step{The cycles of length at most $d$.} Let $Q_1,\dots,Q_n$ be pairwise disjoint cycles of
length at most $d$ in $G-P$, and put $X_i=V(Q_i)$. Every vertex of $Q_i$ lies on exactly one edge
outside $Q_i$, and $Q_i$ has at least five vertices. So $X_i$ is a cyclic region with at most $d$
boundary edges and at least five vertices. Let $E_i$ be the event that $\cO_{X_i}$ holds and
$\xi\cap E(G[X_i])\ne\emptyset$. Put $p_i=\PP(E_i)$, let $Z$ be the number of the events $E_i$
that occur, and put $\mu=\EE Z$. As in the proof of Lemma~\ref{lem:smallcuts}, we have
$p_i\ge2^{-d-1}$ and $\PP(E_i\cap E_j)=2^{\ell(X_i,X_j)-1}p_ip_j$ for $i\ne j$, and for each $i$
at most $d$ indices $j$ have $\ell(X_i,X_j)\ge3$. Let $W_2$ be the sum of $p_ip_j$ over the
ordered pairs $(i,j)$ with $\ell(X_i,X_j)=2$. Then $\EE Z^{2}\le\mu^{2}+W_2+(d+1)\mu$. If
$\xi\cap E(G-P)$ is a forest, then no event $E_i$ occurs, and $Z=0$.

So Proposition~\ref{prop:heavy} applies to the sets $X_i$ with the weights $p_i$, and with
$\Lambda=d$, $m=5$, $\kappa=1$ and $K=d+1$; property~(b) holds because the sets are pairwise
disjoint and $p_i\le1$. If $d<\Lambda_0$, then $\nu_d(G,P)=0$ and $\Phi(d)=C_2$, so
\[
  \mu\;\le\;\tfrac32(d+1)+3d\,(d+3)\bigl(\lceil2dC_2/5\rceil+1\bigr)\;\le\;4\,C_2\,d^{3},
\]
and $n\le2^{d+1}\mu\le C_3\,2^{d}d^{3}$. If $d\ge\Lambda_0$, then
$\lceil2C_1d^{5}/5\rceil+1\le C_1d^{5}$ and $d+3\le d^{\,C_0+1}$. With~(ii),
\[
  \mu\;\le\;\tfrac32(d+1)+3d\,\bigl(d+3+2\,C_3\,d^{\,C_0+1}\bigr)\,C_1d^{5}
  \;\le\;10\,C_1C_3\,d^{\,C_0+7}.
\]
Hence $n\le2^{d+1}\mu\le20\,C_1C_3\,2^{d}d^{\,C_0+7}\le C_3\,2^{d}d^{\,C_0+9}$, by the choice of
$\Lambda_0$. This is~(i).
\end{proof}

\subsection{Proof of Theorem~\ref{thm:half}}\label{sec:halfproof}

Let $G$ and $P$ be as in the theorem, and suppose that $q(G,P)\ge\frac25$. We derive a
contradiction when $r$ is large. All limits below are for $r\to\infty$, and they are uniform in
$G$ and $P$. Put
\[
  x=\log r,\qquad A=6\,e^{124},\qquad L=\lfloor Ax\rfloor,\qquad D=\lceil x/16\rceil .
\]

\paragraph{Cycles of moderate length.}
Let $S$ be the union of the vertex sets of a maximal family of pairwise disjoint cycles of length
at most $D$ in $G-P$. By Proposition~\ref{prop:packing}(i),
$|S|\le C_3\,2^{D}D^{\,C_0+10}\le r/x^{2}$ for large $r$. We use
Proposition~\ref{prop:loggirth} for $G$, $P$, $D$, $L$ and $S$. Its hypotheses hold for large
$r$: the set $P$ has at most $3x$ vertices and $G[P]$ is connected, $x/16\le D\le x/8$, and
$7x\le L\le x\sqrt{\log x}$. So we are in the setting of Section~\ref{sec:moderate}, with
$\Gamma=G$, $U=P\cup S$ and $J=G-U$. The set $\mathcal C$ consists of the cycles of $J$ of length
at most $L$, and the numbers $s$, $a_C$, $\mu$ and $W_2$ and the random variable $Z$ are defined
there. With $\eta=r^{-1/60}$ the proposition gives
\[
  L^{2}2^{-s}\le\eta,\qquad \mu\;\ge\;\frac14\ln\frac{L}{6x}-\frac1{\sqrt x}\;>\;30,\qquad
  \EE Z^{2}\;\le\;\mu^{2}+W_2+(1+\eta)\mu .
\]
The bound $\mu>30$ holds because $L/(6x)\ge e^{124}-1$.

\paragraph{The contradiction.}
We apply Proposition~\ref{prop:heavy} to the vertex sets of the cycles of $\mathcal C$, with the
weights $a_C$, and with $\Lambda=L$, $m=x/16$, $\kappa=\eta$ and $K=1+\eta$. A cycle
$C\in\mathcal C$ has at most $L$ vertices, each of them has one edge end outside $C$, and the
girth of $J$ is greater than $D\ge x/16$. So $V(C)$ has at most $L$ boundary edges and at least
$x/16$ vertices; this is~(a). A cycle of $\mathcal C$ that meets $C$ passes through one of the
at most $L$ vertices of $C$, so~(b) holds by~\eqref{eq:load}. If $\xi\cap E(G-P)$ is a forest,
then $\xi$ contains no cycle of $J$, and $Z=0$; this is~(c). For large $r$ we have
$\Phi(L)=C_1L^{4}$, and $\nu_L(G,P)\le2C_3L^{C_0+1}$ by Proposition~\ref{prop:packing}(ii). So
\[
  \mu\;\le\;\tfrac32(1+\eta)+3L\eta\,\bigl(L+2C_3L^{C_0+1}+3\bigr)
  \bigl(\lceil32C_1L^{5}/x\rceil+1\bigr)\;=\;\tfrac32+o(1),
\]
because $L\le Ax$ and $\eta=r^{-1/60}$. This contradicts $\mu>30$, and
Theorem~\ref{thm:half} is proved. \qed
"""

p.write_text(CLEAN if MODE == "clean" else LEAN)

# ---------------------------------------------------------------- poles.tex: no Lemma 5.5, no Corollary 5.6
p = root / "sections" / "poles.tex"
t = p.read_text()
t = cut(t, "A pole with many paths also has a short cycle:\n",
        r"\paragraph{Consequences of Theorem~\ref{thm:fewcycles}.}", "", "poles: lemma and corollary")
p.write_text(t)

# ---------------------------------------------------------------- layers.tex
p = root / "sections" / "layers.tex"
t = p.read_text()
t = sub(t, r"paths in Section~\ref{sec:poles} and for large girth in Section~\ref{sec:half}.",
           r"paths in Section~\ref{sec:poles} and for pieces in Section~\ref{sec:half}.", "layers idea")
p.write_text(t)

# ---------------------------------------------------------------- exact-maximum.tex
p = root / "exact-maximum.tex"
t = p.read_text()
t = sub(t, "\\input{sections/girth}\n", "", "no section 7")
t = sub(t, r"\fronthead{The proof in eight sentences}", r"\fronthead{The proof in seven sentences}", "seven sentences")
t = sub(t, r"""\item Without such a cut but with a short cycle, $G$ has fewer than $2^{r-1}$ cycles: sort the
cycles through an edge of a shortest cycle by the vertex where they leave it.
\item Without such a cut and with large girth, $G$ has fewer than $2^{r-1}$ cycles: by a
second-moment argument, $G$ contains two large pieces with small boundaries, and each piece has
a forest proportion of at most $\frac35$.""",
r"""\item Without such a cut, $G$ has girth at least five, and it has fewer than $2^{r-1}$ cycles:
by a second-moment argument, $G$ contains two large pieces with small boundaries, and each piece
has a forest proportion of at most $\frac35$.""", "sentences 6 and 7")
p.write_text(t)

# ---------------------------------------------------------------- proof.tex
p = root / "sections" / "proof.tex"
t = p.read_text()
t = sub(t, r"""Let $D_*$ be as in Theorem~\ref{thm:half} and $K_0$ as in Section~\ref{sec:poles}.
By~\eqref{eq:H},""", r"""Let $K_0$ be as in Section~\ref{sec:poles}. By~\eqref{eq:H},""", "proof start")
t = sub(t, r"""Choose $R\ge8$ so large that the following holds for every $r\ge R$:
Proposition~\ref{prop:threecut}, Theorem~\ref{thm:fourcut}, Theorem~\ref{thm:girth} with
$g_0=D_*-1$, and Theorem~\ref{thm:half} apply to the rank $r$; and $r-2>10K_0^{2}$.""",
r"""Choose $R\ge9$ so large that the following holds for every $r\ge R$:
Proposition~\ref{prop:threecut}, Theorem~\ref{thm:fourcut} and Theorem~\ref{thm:half} apply to
the rank $r$; and $r-2>10K_0^{2}$.""", "proof choice of R")
t = sub(t, r"""In the other cases $G$ has no loop and no cyclic cut of size at most four. Let $g$ be its girth.

\step{Case 4: $g<D_*$.} Then $c(G)<2^{r-1}$ by Theorem~\ref{thm:girth}.

\step{Case 5: $g\ge D_*$.} The graph $G$ has $2r-2\ge8$ vertices. Choose a set $P$ of eight
vertices such that $G[P]$ is connected. Then $|P|\le3\log r$, and $G-P$ has girth at least $D_*$.
So $q(G,P)<\frac25$ by Theorem~\ref{thm:half}.""",
r"""\step{Case 4: $G$ has no loop and no cyclic cut of size at most four.} Let $Z$ be a cycle with
at most four edges. Then at most four edges leave $V(Z)$, and at most eight edges have an end in
$V(Z)$. So $G-V(Z)$ has rank at least $r-8>0$, and $\delta V(Z)$ is a cyclic cut of size at most
four. Hence $G$ has girth at least five. The graph $G$ has $2r-2\ge8$ vertices. Choose a set $P$
of eight vertices such that $G[P]$ is connected. Then $|P|\le3\log r$, and $G-P$ has girth at
least five. So $q(G,P)<\frac25$ by Theorem~\ref{thm:half}.""", "proof cases")
p.write_text(t)

# ---------------------------------------------------------------- intro.tex
p = root / "sections" / "intro.tex"
t = p.read_text()
t = sub(t, r"\subsection{The five cases of the proof}", r"\subsection{The four cases of the proof}", "intro title")
t = sub(t, r"""For the upper bound there are five cases (Figure~\ref{fig:plan}). A \emph{cyclic cut} is a set of
edges whose deletion leaves two parts that each contain a cycle. The number $H(r)-2^{r-1}$ is of
order $r\,2^{r/2}$, so the five bounds give the theorem (Section~\ref{sec:proof}).""",
r"""For the upper bound there are four cases (Figure~\ref{fig:plan}). A \emph{cyclic cut} is a set of
edges whose deletion leaves two parts that each contain a cycle. The number $H(r)-2^{r-1}$ is of
order $r\,2^{r/2}$, so the four bounds give the theorem (Section~\ref{sec:proof}).""", "intro cases")
t = sub(t, r"""  \node[ask, below=of q3] (q4) {Does $G$ have a cycle of length less than $D_*$?};
""", "", "figure q4")
t = sub(t, r"""  \node[res, right=13mm of q4] (o4) {fewer than $2^{r-1}$ cycles\\ \textcolor{slate}{Theorem~\ref{thm:girth}}};
  \node[res, below=of q4, text width=4.6cm, align=center] (o5) {fewer than $2^{r-1}$ cycles\\ \textcolor{slate}{Theorem~\ref{thm:half}}};
  \foreach \a/\b in {q1/o1,q2/o2,q3/o3,q4/o4} \draw[ar] (\a) -- node[lab, above] {yes} (\b);
  \foreach \a/\b in {q1/q2,q2/q3,q3/q4,q4/o5} \draw[ar] (\a) -- node[lab, right] {no} (\b);""",
r"""  \node[res, below=of q3, text width=4.6cm, align=center] (o4) {girth at least five, and fewer than $2^{r-1}$ cycles\\ \textcolor{slate}{Theorem~\ref{thm:half}}};
  \foreach \a/\b in {q1/o1,q2/o2,q3/o3} \draw[ar] (\a) -- node[lab, above] {yes} (\b);
  \foreach \a/\b in {q1/q2,q2/q3,q3/o4} \draw[ar] (\a) -- node[lab, right] {no} (\b);""", "figure arrows")
t = sub(t, r"""\caption{The five cases for a connected cubic multigraph $G$ of large rank $r$. The number $D_*$
is an absolute constant.}""", r"""\caption{The four cases for a connected cubic multigraph $G$ of large rank $r$.}""", "figure caption")
t = sub(t, r"""In the cases 2, 3 and 4 a cycle consists of paths in the parts of $G$.""",
           r"""In the cases 2 and 3 a cycle consists of paths in the parts of $G$.""", "intro cases 2 3")
t = sub(t, r"""In the case 5 the
forest estimate is not sufficient, because we need a bound below $\half$ and its error term is
positive. In this case a second-moment argument gives two disjoint pieces of $G$ with small
boundaries and large girth, and each piece contributes a factor of at most $\frac35$ to the
proportion of forests (Section~\ref{sec:half}).""",
r"""In the case 4 the
forest estimate is not sufficient, because we need a bound below $\half$ and its error term is
positive. In this case a second-moment argument gives two disjoint pieces of $G$ with small
boundaries, and each piece contributes a factor of at most $\frac35$ to the proportion of
forests (Section~\ref{sec:half}).""", "intro case 4")
t = sub(t, r"""count for rings, the argument for bounded girth, and the packing bound and the two girth scales of
Section~\ref{sec:half}.""",
r"""count for rings, and the first proof for graphs without a small cyclic cut: an argument for
bounded girth, and a packing bound and two girth scales for large girth.""", "origins 1")
t = sub(t, r"""from the proof of Theorem~\ref{thm:fourcut}, and the marked set of Case~5 in
Section~\ref{sec:proof}.""", r"""from the proof of Theorem~\ref{thm:fourcut}, and the marked set of Case~4 in
Section~\ref{sec:proof}.""", "origins case")
t = sub(t, r"""Proposition~\ref{prop:loggirth} serves Sections~\ref{sec:forest} and~\ref{sec:half}; this made
Section~\ref{sec:half} shorter.""",
r"""Proposition~\ref{prop:loggirth} serves Sections~\ref{sec:forest} and~\ref{sec:half}, that
one girth scale is sufficient (Proposition~\ref{prop:heavy}), and that a large piece of girth
five has few forests (Lemma~\ref{PIECESLABEL}). So the argument for bounded girth is not
necessary.""".replace("PIECESLABEL", "lem:affine" if MODE == "clean" else "lem:piecesfive"), "origins 2")
t = sub(t, r"""Corollary~\ref{cor:nodense}, for the pole alone & \lean{EMS.cyclicShoreStatement}\\
Case 4: Theorem~\ref{thm:girth} & \lean{EM.shortCycleStatement}\\
Proposition~\ref{prop:packing} with the bound $150\,d^{3}(s+1)2^{d}$; Theorem~\ref{thm:half} & \lean{EMS.Shortening.ChainPacking.exists_cutoff}, \lean{EMS.Shortening.ChainForestProbability.exists_cutoff}\\
Case 5 (large girth) & \lean{EM.largeGirthStatement_chain}\\""",
r"""Case 4 for a graph with a cycle shorter than a number $D_*$ & \lean{EM.shortCycleStatement}, with \lean{EMS.cyclicShoreStatement}\\
Case 4 for girth at least $D_*$, with a packing bound $150\,d^{3}(s+1)2^{d}$ outside a deleted set of $s$ vertices & \lean{EMS.Shortening.ChainPacking.exists_cutoff}, \lean{EMS.Shortening.ChainForestProbability.exists_cutoff}, \lean{EM.largeGirthStatement_chain}\\""", "table rows")
t = sub(t, r"""this text, which had no cap, marked a shortest cycle in Case~5, and had another proof of
Proposition~\ref{prop:packing}.""", r"""this text, which had no cap, marked a shortest cycle in the last case, and had another proof of
the packing bound.""", "first formal proof")
t = sub(t, r"""paper. A formal proof can differ from the text. In four places the method is different. The""",
           r"""paper. A formal proof can differ from the text. In four places the method is different. The""", "four places")
t = sub(t, r"""a capped ladder. The formal proof of Lemma~\ref{lem:affine} first deletes the vertices of degree
one, and then a count of the vertices of a multigraph of large girth gives the large layer. In
other places the details differ. For example, the formal number $D_*$ is at least $256$, the
formal cap of Lemma~\ref{lem:cap} has a vertex in the middle of the edge $xy$, the formal proof
of Theorem~\ref{thm:fewcycles} calls a thin layer ordinary if at most one of its two vertices is
on a pair of parallel edges, and the formal proof of Theorem~\ref{thm:girth} allows $12g+2$
ports for the poles $K_p$. So""",
r"""a capped ladder. The largest difference is in Case~4. The formal proof has a number
$D_*\ge256$ and two cases. For a graph with a cycle shorter than $D_*$ it sorts the cycles
through an edge of a shortest cycle by the vertex where they leave it. For girth at least $D_*$
it uses pieces of large girth, and it raises the girth in stages by the deletion of maximal
families of short cycles. In other places the details differ. For example, the
formal cap of Lemma~\ref{lem:cap} has a vertex in the middle of the edge $xy$, and the formal
proof of Theorem~\ref{thm:fewcycles} calls a thin layer ordinary if at most one of its two
vertices is on a pair of parallel edges. So""", "differences")
p.write_text(t)
print("applied")
