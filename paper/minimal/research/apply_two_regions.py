# Writes the second form of Section 8 (pieces at a fixed girth, no packing number in the statements)
# into a copy of the manuscript.
# Usage: python3 apply_two_regions.py <folder that contains sections/large.tex and sections/intro.tex>
# Unchanged parts are copied from the present large.tex by exact markers; a missing marker stops
# the script with exit code 1.
import sys, pathlib

root = pathlib.Path(sys.argv[1])
p = root / "sections" / "large.tex"
old = p.read_text()

def part(start, end, name):
    if old.count(start) != 1:
        print(f"FAILED: {name}: start has {old.count(start)} matches"); sys.exit(1)
    i = old.index(start)
    j = old.index(end, i) + len(end)
    return old[i:j]

def sub(text, a, b, name):
    if text.count(a) != 1:
        print(f"FAILED: {name}: {text.count(a)} matches"); sys.exit(1)
    return text.replace(a, b)

THM = part(r"\begin{theorem}\label{thm:half}", r"\end{theorem}", "theorem")
PIECEDEF = part(r"Let $N$ be a connected subcubic multigraph. Its vertices of degree less than three are its",
                "$k\\ge1$.", "piece definitions")
NESTED = part(r"\begin{lemma}[Nested separators]\label{lem:nested}", r"of the sets $U_i$ by inclusion.", "nested")
FIGURE = part(r"\begin{figure}[ht]", r"\end{figure}", "figure")
FIGURE = sub(FIGURE, r"block end in its two end sets (proof of Proposition~\ref{prop:chain}).}",
             r"block end in its two end sets (Lemma~\ref{lem:blocks}).}", "figure caption")
MARKER = part(r"\step{A marker.} Suppose that some set $T$ of boundary vertices has forest proportion at least",
              r"$B(k+1)^{2}$ vertices.", "marker")
SEP = part(r"\begin{lemma}[Two links]\label{lem:sep}", r"\end{proof}", "two links")
# the proof of the two-links lemma is the first \end{proof} after its statement
i = old.index(r"\begin{lemma}[Two links]\label{lem:sep}")
j = old.index(r"\end{proof}", old.index(r"\begin{proof}", i)) + len(r"\end{proof}")
SEP = old[i:j]

new = r"""\section{Large girth outside a small set}\label{sec:half}

Recall that $q(G,P)$ is the probability that $\xi\cap E(G-P)$ is a forest.

""" + THM + r"""

\begin{idea}{outline of the proof}
A \emph{piece} is a large connected part of $G-P$ with a small boundary. A piece has a forest
proportion of less than $\frac35$, for every choice of the edges outside it
(Section~\ref{sec:affine}). So two disjoint pieces give $q(G,P)\le(\frac35)^{2}<\frac25$. Suppose
that $q(G,P)\ge\frac25$. Then a family of regions with a large total weight has many pairs with
exactly two links, by the second moment. These pairs give a long chain of nested separators, and
two pieces lie between them (Section~\ref{sec:heavy}). We use this for short cycles
(Section~\ref{sec:packing}) and for cycles of moderate length (Section~\ref{sec:halfproof}).
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

\subsection{Pieces with a small boundary}\label{sec:affine}

""" + PIECEDEF + r"""

\begin{lemma}[Product]\label{lem:product}
Let $N$ be a multigraph, and let $P$ and $T$ be sets of vertices such that $N$ has a $T$-join. Let
$U_1,\ldots,U_m\subseteq V(N)\sm(P\cup T)$ be pairwise disjoint sets of vertices of degree three
such that each $N[U_i]$ is connected. Suppose that in each $N[U_i]$ every even set of boundary
vertices has forest proportion at most $\frac35$. Then $J\cap E(N-P)$ is a forest for at most the
proportion $(3/5)^m$ of the $T$-joins $J$ of $N$. For a cubic multigraph $G$ and $T=\emptyset$
this says that $q(G,P)\le(3/5)^m$.
\end{lemma}

\begin{proof}
Let $E'$ consist of the edges that lie in none of the graphs $N[U_i]$, and let $J$ be a uniformly
random $T$-join. Fix a set $x\subseteq E'$ that extends to a $T$-join. For each $i$, let $T_i$ be
the set of the vertices of $U_i$ that are incident with an odd number of edges of $x$. The set
$U_i$ avoids $T$, so the parity equations say that $J\cap E(N[U_i])$ is a $T_i$-join. These
equations involve disjoint sets of edges, so the joins are independent and uniform, conditional on
$J\cap E'=x$. A vertex of degree three in $N[U_i]$ has no incident edge in $E'$. So $T_i$ is an
even set of boundary vertices. If $J\cap E(N-P)$ is a forest, its restriction to every $N[U_i]$
is a forest. The conditional probability is therefore at most $(3/5)^m$. Average over $x$. Edges
between the sets $U_i$ belong to $E'$, so adjacent sets cause no exception.
\end{proof}

\begin{lemma}[Pieces]\label{lem:affine}
There are an integer $D_*\ge7$ and an absolute constant $C_1\ge2$ with the following property. Let
$k\ge1$, and let $N$ be a connected subcubic multigraph of girth at least $D_*$ with at most $k$
boundary vertices and at least $C_1k^{7}$ vertices. Then every set of boundary vertices of even
size has forest proportion less than $\frac35$.
\end{lemma}

\begin{proof}
For $k\ge1$ let $s_k$ be the least integer with $2^{s_k}>(2s_k+1)B(k+1)^{2}$. Then
$2^{s_k}\le2(2s_k+1)B(k+1)^{2}$, the numbers $s_k$ do not decrease, and $s_k=O(\log k)$. Fix $k_0$
such that $4s_k<k$ for all $k\ge k_0$, and put $D_*=2s_{k_0}+1$. We define numbers $F(k)\ge2$
below, and we prove the lemma with $F(k)$ in the place of $C_1k^{7}$, by induction on $k$.

Let $N$ and $k$ be as in the lemma, with at least $F(k)$ vertices, and put $s=s_k$. If $N$ has at
most one boundary vertex, the only set is the empty one. Then $N$ contains a cycle, and the forest
proportion is at most $\half$. In the other case fix a boundary vertex $o$, and call the set of the
vertices at distance $j$ from $o$ the \emph{layer} $j$. Call a cycle \emph{short} if its length
is at most $2s$. Let $\mathcal D$ be a maximal family of pairwise disjoint short cycles of $N$,
and let $t$ be their number.

\step{A large layer.} Suppose that $N$ has more than $3\cdot2^{s}(k+2s\,t)$ vertices. A ball of
radius $s$ has at most $3\cdot2^{s}$ vertices. So some vertex $w$ has distance more than $s$ from
every boundary vertex and from every vertex of a cycle of $\mathcal D$. Let $W$ be the set of the
vertices within distance $s$ of $w$. They have degree three. Take a breadth-first tree from
$w$. Suppose that some vertex at distance less than $s$ from $w$ has fewer than two children in
this tree, or that $w$ has fewer than three. Then $N[W]$ contains a short cycle. This cycle meets
a cycle of $\mathcal D$, and this contradicts the choice of $w$. So $|W|\ge2^{s}$. The distances from $o$ to two vertices of $W$ differ by at most
$2s$. So $W$ meets at most $2s+1$ layers, and some layer has at least $2^{s}/(2s+1)>B(k+1)^{2}$
vertices.

""" + MARKER + r""" So $N$ has at most $3\cdot2^{s}(k+2s\,t)$ vertices, by the
first step.

If $k<k_0$, then $2s<D_*$ and $t=0$. So the lemma holds with $F(k)=3\cdot2^{s}k+1$.

\step{Many short cycles.} Let $k\ge k_0$, and put $k'=4s$. Then $k'<k$. Put
\begin{gather*}
  w=\lceil k'F(k')/D_*\rceil+1,\qquad n_1=5(2s+1)\,2^{2s},\qquad n_2=k^{2}(k+2)\,w,\\
  F(k)=3\cdot2^{s}\bigl(k+2s\,(k+n_1+n_2+2)\bigr)+1 .
\end{gather*}
By the first two steps we may assume that $t\ge k+n_1+n_2+2$. Let $T$ be an even set of boundary
vertices, and let $J$ be a uniformly random $T$-join. At most $k$ cycles of $\mathcal D$ contain a
boundary vertex. Call another cycle $Q\in\mathcal D$ \emph{free} if every component of $N-V(Q)$
contains an even number of vertices of $T$. So more than $n_1$ cycles are free, or more than $n_2$
cycles are not free.

\emph{More than $n_1$ free cycles.} If $Q$ is free, some $T$-join $F$ has no edge with an end on
$Q$. The map $J\mapsto J+F$ is a bijection from the $T$-joins to the even subgraphs of $N$, and it
keeps the edges with an end on $Q$. So the event that $J\cap\delta V(Q)=\emptyset$ and
$J\cap E(N[V(Q)])\ne\emptyset$ has the same probability as for a random even subgraph. For two
free cycles the two events exclude each other, or some $T$-join has no edge with an end on the two
cycles, and the same argument applies. So the proof of Lemma~\ref{lem:smallcuts} holds for $J$ and
the vertex sets of the free cycles, which have at most $2s$ boundary edges. Hence the forest
proportion of $T$ is less than $\half+(2s+1)\,2^{2s-1}/n_1=\frac35$.

\emph{More than $n_2$ cycles that are not free.} Let $Q$ be one of them. Some component of
$N-V(Q)$ contains an odd number of vertices of $T$. The set $T$ is even and avoids $Q$. So $T$ has
a vertex $a$ in this component and a vertex $b$ in another component, and $V(Q)$ separates $a$
from $b$. There are fewer than $k^{2}$ pairs $a,b$. So more than $(k+2)w$ of these cycles
separate the same two vertices $a$ and $b$. By Lemma~\ref{lem:nested} their vertex sets are
linearly ordered, and Lemma~\ref{lem:blocks} for $N$, $a$ and $b$ gives $k+2$ pairwise disjoint
sets $Y_l$. At most $k$ of them contain a boundary vertex of $N$. Let $Y_1$ and $Y_2$ be two of the
others, and let $i\in\{1,2\}$. The set $Y_i$ contains $w-1$ of the cycles, so
$|Y_i|\ge(w-1)D_*\ge k'F(k')$. At most $2\cdot2s=k'$ edges leave $Y_i$, and every component of
$N[Y_i]$ has such an edge, because $b\notin Y_i$. So some component has a vertex set $Y_i'$ with
at least $F(k')$ vertices. The vertices of $Y_i$ have degree three in $N$, so $N[Y_i']$ has at
most $k'$ boundary vertices. By induction, every even set of boundary vertices of $N[Y_i']$ has
forest proportion less than $\frac35$. Lemma~\ref{lem:product}, for $N$, $T$, $P=\emptyset$ and
the disjoint sets $Y_1'$ and $Y_2'$, shows that the forest proportion of $T$ is at most
$\frac9{25}$.

\emph{The size of $F$.} As $s_k=O(\log k)$, the definition gives
$F(k)=O\bigl(k^{6}\log^{5}k+k^{5}\log^{3}k\cdot F(4s_k)\bigr)$. So $F(k)\le C_1k^{7}$ for an
absolute constant $C_1$, by induction on $k$.
\end{proof}

\subsection{Heavy families}\label{sec:heavy}

\begin{idea}{two links give a separator}
If two disjoint connected sets have exactly two links, then one of them separates a neighbour of
the other one from a fixed vertex $p$. Disjoint sets that separate the same two vertices are
nested, and the parts between them have small boundaries (Figure~\ref{fig:chain}). So a long
chain of such sets contains two pieces.
\end{idea}

\begin{proposition}[A long chain]\label{prop:chain}
Let $G$ be a connected cubic multigraph, and let $P$ be a nonempty set of vertices such that
$G[P]$ is connected and $G-P$ has girth at least $D_*$. Let $p\in P$, let $A$ be a region that
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
least $D_*$. By Lemma~\ref{lem:affine}, every even set of boundary vertices of $G[Y']$ has forest
proportion less than $\frac35$. There are two sets $Y$, and Lemma~\ref{lem:product} for their
two sets $Y'$ gives $q(G,P)\le\frac9{25}$.
\end{proof}

""" + SEP + r"""

\begin{proposition}[Heavy families]\label{prop:heavy}
Let $G$ be a connected cubic multigraph, and let $P$ be a nonempty set of vertices such that
$G[P]$ is connected, $G-P$ has girth at least $D_*$, and $q(G,P)\ge\frac25$. Let $\mathcal A$ be a
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
$G[P]$ is connected. Suppose that $q(G,P)\ge\frac25$ and that $G-P$ has girth at least $D_*$.
Then, for every integer $d\ge D_*$, the multigraph $G-P$ has at most $2^{10}C_1\,2^{d}d^{10}$
pairwise disjoint cycles of length at most $d$.
\end{proposition}

\begin{proof}
Let $Q_1,\dots,Q_n$ be such cycles, and put $X_i=V(Q_i)$. Every vertex of $Q_i$ lies on exactly
one edge outside $Q_i$, and $Q_i$ has at least $D_*$ vertices. So $X_i$ is a cyclic region with at
most $d$ boundary edges and at least $D_*$ vertices. Let $E_i$ be the event that $\cO_{X_i}$
holds and $\xi\cap E(G[X_i])\ne\emptyset$. Put $p_i=\PP(E_i)$, let $Z$ be the number of the events
$E_i$ that occur, and put $\mu=\EE Z$. As in the proof of Lemma~\ref{lem:smallcuts}, we have
$p_i\ge2^{-d-1}$ and $\PP(E_i\cap E_j)=2^{\ell(X_i,X_j)-1}p_ip_j$ for $i\ne j$, and for each $i$
at most $d$ indices $j$ have $\ell(X_i,X_j)\ge3$. Let $W_2$ be the sum of $p_ip_j$ over the
ordered pairs $(i,j)$ with $\ell(X_i,X_j)=2$. Then $\EE Z^{2}\le\mu^{2}+W_2+(d+1)\mu$. If
$\xi\cap E(G-P)$ is a forest, then no event $E_i$ occurs, and $Z=0$.

So Proposition~\ref{prop:heavy} applies to the sets $X_i$ with the weights $p_i$, and with
$\Lambda=d$, $m=D_*$, $\kappa=1$ and $K=d+1$; property~(b) holds because the sets are pairwise
disjoint and $p_i\le1$. As $D_*\ge7$, it gives
\[
  \mu\;\le\;\tfrac32(d+1)+3d\,(d+3)\bigl(\lceil2^{8}C_1d^{8}/D_*\rceil+1\bigr)\;\le\;2^{9}C_1\,d^{10},
\]
and $n\le2^{d+1}\mu$.
\end{proof}

\subsection{Proof of Theorem~\ref{thm:half}}\label{sec:halfproof}

Let $D_*$ and $C_1$ be as in Lemma~\ref{lem:affine}. Let $G$ and $P$ be as in the theorem, and
suppose that $q(G,P)\ge\frac25$. We derive a contradiction when $r$ is large. All limits below are
for $r\to\infty$, and they are uniform in $G$ and $P$. Put
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
p.write_text(new)

# ---------------------------------------------------------------- intro.tex
p = root / "sections" / "intro.tex"
t = p.read_text()
t = sub(t, r"""count for rings, the argument for bounded girth, and the packing bound and the two girth scales of
Section~\ref{sec:half}.""",
r"""count for rings, the argument for bounded girth, and the first proof of
Section~\ref{sec:half}, with a packing bound and two girth scales.""", "origins 1")
t = sub(t, r"""Proposition~\ref{prop:loggirth} serves Sections~\ref{sec:forest} and~\ref{sec:half}; this made
Section~\ref{sec:half} shorter.""",
r"""Proposition~\ref{prop:loggirth} serves Sections~\ref{sec:forest} and~\ref{sec:half}, and that
one girth scale and pieces of a fixed girth are sufficient (Proposition~\ref{prop:heavy},
Lemma~\ref{lem:affine}).""", "origins 2")
t = sub(t, r"""Proposition~\ref{prop:packing} with the bound $150\,d^{3}(s+1)2^{d}$; Theorem~\ref{thm:half} &""",
r"""A packing bound $150\,d^{3}(s+1)2^{d}$ outside a deleted set of $s$ vertices; Theorem~\ref{thm:half} &""", "table row")
t = sub(t, r"""a capped ladder. The formal proof of Lemma~\ref{lem:affine} first deletes the vertices of degree
one, and then a count of the vertices of a multigraph of large girth gives the large layer. In
other places the details differ.""",
r"""a capped ladder. The formal proof of Theorem~\ref{thm:half} follows an earlier form of
Section~\ref{sec:half}: its pieces have a girth of about $\log\Lambda$ for $2\Lambda$ boundary
vertices, and it raises the girth in stages, by the deletion of maximal families of cycles of
length at most $D_*,2D_*,4D_*,\dots$ In
other places the details differ.""", "fourth place")
p.write_text(t)
print("applied")
