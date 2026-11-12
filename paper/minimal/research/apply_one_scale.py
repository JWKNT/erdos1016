# Applies the one-scale proof of Theorem 8.1 to a copy of the manuscript.
# Usage: python3 apply_one_scale.py <folder that contains sections/large.tex and sections/intro.tex>
# Every replacement must match exactly once; otherwise the script stops with exit code 1.
import sys, pathlib

root = pathlib.Path(sys.argv[1])

def sub(text, old, new, name):
    n = text.count(old)
    if n != 1:
        print(f"FAILED: {name}: {n} matches"); sys.exit(1)
    return text.replace(old, new)

def cut(text, start, end, new, name):
    """Replace the part from the first `start` up to and including the next `end`."""
    if text.count(start) != 1:
        print(f"FAILED: {name}: start has {text.count(start)} matches"); sys.exit(1)
    i = text.index(start)
    j = text.index(end, i) + len(end)
    return text[:i] + new + text[j:]

# ---------------------------------------------------------------- large.tex
p = root / "sections" / "large.tex"
t = p.read_text()

t = cut(t, r"\begin{idea}{outline of the proof}", r"\end{idea}", r"""\begin{idea}{outline of the proof}
Suppose that $q(G,P)\ge\frac25$. We find two disjoint parts of $G-P$ that are large, have small
boundaries and contain no short cycle. Each of them has a forest proportion of at most $\frac35$,
for every choice of the edges outside it. This is a contradiction, because
$(\frac35)^{2}<\frac25$. The parts come from a family of regions with a large total weight: the
second moment gives many pairs with exactly two links, and these pairs give nested separators
(Section~\ref{sec:separators}). We use this for short cycles (Section~\ref{sec:packing}) and
for cycles of moderate length (Section~\ref{sec:halfproof}).
\end{idea}""", "outline")

t = sub(t, r"There are absolute constants $C_0$ and $C_1\ge1$ with the following property.",
           r"There are absolute constants $C_0\ge1$ and $C_1\ge1$ with the following property.", "constants 1")
t = sub(t, r"constants $C_0$ and $C_1$ such that $2s<C_0\log(\Lambda+2)$",
           r"constants $C_0\ge1$ and $C_1\ge1$ such that $2s<C_0\log(\Lambda+2)$", "constants 2")

t = sub(t, r"From now on $D_{*}\ge7$ is a fixed integer such that $D\ge C_0\log(2D+2)$ for every $D\ge D_{*}$.",
r"""Call a cycle \emph{$\Lambda$-short} if its length is less than $C_0\log(\Lambda+2)$. For a
multigraph $G$ and a set $P$ of vertices, let $\nu_\Lambda(G,P)$ be the largest number of pairwise
disjoint $\Lambda$-short cycles of $G-P$. From now on $D_{*}\ge7$ is a fixed integer such that
every integer $d\ge D_{*}$ satisfies
\[
  \bigl(C_0\log(d+2)\bigr)^{C_0+9}\le d,\qquad (d+2)^{C_0}\le2\,d^{\,C_0},\qquad d^{2}\ge20\,C_1 .
\]
Then $C_0\log(d+2)\le d$.""", "D_*")

t = sub(t, r"""So a long
chain of such sets contains two pieces to which Lemma~\ref{lem:affine} applies. We use this for
short cycles in Section~\ref{sec:packing} and for cycles of moderate length in
Section~\ref{sec:halfproof}.""",
r"""So a long
chain of such sets contains two pieces without a short cycle, and Lemma~\ref{lem:affine} applies
to them.""", "separator idea")

t = cut(t, r"\begin{proposition}[A long chain]\label{prop:chain}", r"\end{proposition}",
r"""\begin{proposition}[A long chain]\label{prop:chain}
Let $G$ be a connected cubic multigraph, and let $P$ be a nonempty set of vertices such that
$G[P]$ is connected. Let $p\in P$, let $A$ be a region that avoids $P$, and let $u\notin A$ be a
vertex in the component of $p$ in $G-A$. Let $C_1,\dots,C_T$ be pairwise disjoint regions that
avoid $P$, $A$ and $u$ and separate $u$ from $p$ in $G-A$. Let $\Lambda\ge4$ be an integer and
$m\ge1$ a number such that $A$ and every $C_i$ have at most $\Lambda$ boundary edges, and every
$C_i$ has at least $m$ vertices. If
\[
  T\;>\;\bigl(\Lambda+\nu_\Lambda(G,P)+2\bigr)\bigl(\lceil2C_1\Lambda^{5}/m\rceil+1\bigr),
\]
then $q(G,P)\le\frac9{25}$.
\end{proposition}""", "chain statement")

t = cut(t, r"There are at least $\Lambda+|U\sm P|+2$ sets $Y_l$.", r"and $G[Y]$ has girth at least $D$.",
r"""There are at least $\Lambda+\nu+2$ sets $Y_l$, where $\nu=\nu_\Lambda(G,P)$. The set $P$ is
connected, it contains $p$, and it is disjoint from $A$ and from the sets $C_i$. So $P$ lies in
the component of $p$ in $H-C_i$ for every $i$, and every $Y_l$ avoids $P$. Discard $Y_l$ if it
contains a vertex with a neighbour in $A$, or if $G[Y_l]$ contains a $\Lambda$-short cycle. The
sets $Y_l$ are pairwise disjoint, so this discards at most $\Lambda+\nu$ sets, and two sets
remain. Let $Y$ be one of them. The edges of $G$ that leave $Y$ are edges of $H$, so
$|\delta Y|\le2\Lambda$, and $G[Y]$ has girth at least $C_0\log(\Lambda+2)$.""", "chain blocks")

t = sub(t, r"""Lemma~\ref{lem:product}, for the two sets $Y'$ and the
marked set $U$, gives $q(G,U)\le\frac9{25}$.""",
r"""Lemma~\ref{lem:product}, for the two sets $Y'$ and the
marked set $P$, gives $q(G,P)\le\frac9{25}$.""", "chain end")

i = t.index(r"\subsection{Packing of short cycles}\label{sec:packing}")
t = t[:i] + r"""\begin{proposition}[Heavy families]\label{prop:heavy}
Let $G$ be a connected cubic multigraph, and let $P$ be a nonempty set of vertices such that
$G[P]$ is connected and $q(G,P)\ge\frac25$. Let $\mathcal A$ be a finite family of regions that
avoid $P$, with weights $w_A\ge0$ of total $\mu$, and let $W_2$ be as in Lemma~\ref{lem:sep}. Let
$\Lambda\ge4$ be an integer, and let $m\ge1$, $\kappa>0$ and $K\ge0$ be numbers such that
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
  \bigl(\lceil2C_1\Lambda^{5}/m\rceil+1\bigr).
\]
\end{proposition}

\begin{proof}
Put $\nu=\nu_\Lambda(G,P)$ and $w=\lceil2C_1\Lambda^{5}/m\rceil+1$. We may assume that
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
most $d$. It contains the number of disjoint cycles of length about $\log d$, and for this
number we use induction.
\end{idea}

\begin{proposition}[Packing]\label{prop:packing}
Let $G$ be a connected cubic multigraph, and let $P$ be a nonempty set of vertices such that
$G[P]$ is connected. Suppose that $q(G,P)\ge\frac25$ and that $G-P$ has girth at least $D_*$.
Let $d\ge D_*$ be an integer. Then
\begin{enumerate}
\item[\textup{(i)}] $G-P$ has at most $2^{d}d^{\,C_0+9}$ pairwise disjoint cycles of length at
most $d$;
\item[\textup{(ii)}] $\nu_d(G,P)\le2\,d^{\,C_0+1}$.
\end{enumerate}
\end{proposition}

\begin{proof}
We use induction on $d$. Suppose that~(i) holds for every smaller integer that is at least
$D_*$.

\step{The shorter cycles.} Let $g$ be the largest integer that is less than $C_0\log(d+2)$. Then
$g<d$, and a cycle is $d$-short if and only if its length is at most $g$. If $g<D_*$, then
$G-P$ has no such cycle. Otherwise~(i) for $g$ and the choice of $D_*$ give
\[
  \nu_d(G,P)\;\le\;2^{g}g^{\,C_0+9}\;\le\;(d+2)^{C_0}\bigl(C_0\log(d+2)\bigr)^{C_0+9}
  \;\le\;2\,d^{\,C_0+1}.
\]
This is~(ii).

\step{The cycles of length at most $d$.} Let $Q_1,\dots,Q_n$ be pairwise disjoint cycles of
length at most $d$ in $G-P$, and put $X_i=V(Q_i)$. Every vertex of $Q_i$ lies on exactly one edge
outside $Q_i$, and $Q_i$ has at least $D_*$ vertices. So $X_i$ is a cyclic region with at most
$d$ boundary edges and at least $D_*$ vertices. Let $E_i$ be the event that $\cO_{X_i}$ holds and
$\xi\cap E(G[X_i])\ne\emptyset$. Put $p_i=\PP(E_i)$, let $Z$ be the number of the events $E_i$
that occur, and put $\mu=\EE Z$. As in the proof of Lemma~\ref{lem:smallcuts}, we have
$p_i\ge2^{-d-1}$ and $\PP(E_i\cap E_j)=2^{\ell(X_i,X_j)-1}p_ip_j$ for $i\ne j$, and for each $i$
at most $d$ indices $j$ have $\ell(X_i,X_j)\ge3$. Let $W_2$ be the sum of $p_ip_j$ over the
ordered pairs $(i,j)$ with $\ell(X_i,X_j)=2$. Then $\EE Z^{2}\le\mu^{2}+W_2+(d+1)\mu$. If
$\xi\cap E(G-P)$ is a forest, then no event $E_i$ occurs, and $Z=0$.

So Proposition~\ref{prop:heavy} applies to the sets $X_i$ with the weights $p_i$, and with
$\Lambda=d$, $m=D_*$, $\kappa=1$ and $K=d+1$; property~(b) holds because the sets are pairwise
disjoint and $p_i\le1$. We have $\lceil2C_1d^{5}/D_*\rceil+1\le C_1d^{5}$, because $D_*\ge7$, and
$d+3\le d^{\,C_0+1}$. With~(ii),
\[
  \mu\;\le\;\tfrac32(d+1)+3d\,\bigl(d+3+2\,d^{\,C_0+1}\bigr)\,C_1d^{5}\;\le\;10\,C_1\,d^{\,C_0+7}.
\]
Hence $n\le2^{d+1}\mu\le20\,C_1\,2^{d}d^{\,C_0+7}\le2^{d}d^{\,C_0+9}$, by the choice of $D_*$.
This is~(i).
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
at most $D$ in $G-P$. By Proposition~\ref{prop:packing}(i), $|S|\le2^{D}D^{\,C_0+10}\le r/x^{2}$
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
then $\xi$ contains no cycle of $J$, and $Z=0$; this is~(c). By
Proposition~\ref{prop:packing}(ii), $\nu_L(G,P)\le2L^{C_0+1}$. So
\[
  \mu\;\le\;\tfrac32(1+\eta)+3L\eta\,\bigl(L+2L^{C_0+1}+3\bigr)
  \bigl(\lceil32C_1L^{5}/x\rceil+1\bigr)\;=\;\tfrac32+o(1),
\]
because $L\le Ax$ and $\eta=r^{-1/60}$. This contradicts $\mu>30$, and
Theorem~\ref{thm:half} is proved. \qed
"""
p.write_text(t)

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
one girth scale is sufficient (Proposition~\ref{prop:heavy}); this made
Section~\ref{sec:half} shorter.""", "origins 2")
t = sub(t, r"""Proposition~\ref{prop:packing} with the bound $150\,d^{3}(s+1)2^{d}$; Theorem~\ref{thm:half} &""",
r"""A packing bound $150\,d^{3}(s+1)2^{d}$ outside a deleted set of $s$ vertices; Theorem~\ref{thm:half} &""", "table row")
t = sub(t, r"""A formal proof can differ from the text. In four places the method is different.""",
r"""A formal proof can differ from the text. In five places the method is different.""", "five places")
t = sub(t, r"""one, and then a count of the vertices of a multigraph of large girth gives the large layer. In
other places the details differ.""",
r"""one, and then a count of the vertices of a multigraph of large girth gives the large layer. The
formal proof of Theorem~\ref{thm:half} raises the girth in stages: it deletes maximal families
of cycles of length at most $D_*,2D_*,4D_*,\dots$ and uses two of these scales. In
other places the details differ.""", "fifth place")
p.write_text(t)
print("applied")
