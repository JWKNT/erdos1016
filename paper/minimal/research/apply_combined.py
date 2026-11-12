# Writes the combined form into a copy of the manuscript: the reductions of the three research
# notes together with the parts of Astra's notes of 12 November 2026 that passed the audit
# (research/astra-audit.pdf).
#
# Usage: python3 apply_combined.py <folder that contains exact-maximum.tex and sections/> [ab|caps] [blocks]
#   The folder is a copy that was changed by
#       python3 apply_girth_five.py <copy> lean
#       python3 apply_fewer_cases.py <copy> keepgap
#   ab (default): Proposition 6.3 keeps the proof of the manuscript (two cases by the number of
#                 paths in the larger side) and the constants 1/1000 and K_0.
#   caps:         Proposition 6.3 is proved with caps and the gap theorem, as Astra proposed; the
#                 bound is 2^(r-1) + 420 * 2^(r/2), and the constants 1/1000, K_0 are not used.
#   blocks:       the blocks of the chain proposition are connected by their construction.
#
# What the script writes:
#   Section 4: Step 2 of the lemma on layers with the threshold m^(3/4)          (Astra, 2)
#   Section 5: the lemma on a shortest path, without a hypothesis on paths       (Astra, 3)
#              few cycles from that lemma; no ordinary layers, no matchings      (Astra, 3)
#              the gap theorem as a corollary; no third port, no induction       (note 3; Astra, 4)
#              the three gadgets for every margin                                (Astra, 6.1)
#   Section 6: rigidity by a limit of states; three full pairs at a port give
#              a cyclic cut of size three; no lemma on a full star               (Astra, 6)
#              one cap in the theorem on a cycle of length four                  (note 3)
#   Section 7: two links as an upper bound for W_2; a shorter proof of nesting   (Astra, 7)
# Every replacement must match exactly once; a missing marker stops the script with exit code 1.
# The script changes the copy only.
import sys, pathlib

root = pathlib.Path(sys.argv[1])
OPTS = sys.argv[2:]
for o in OPTS:
    if o not in ("ab", "caps", "blocks"):
        print("FAILED: the options are ab, caps, blocks"); sys.exit(1)
CAPS = "caps" in OPTS
BLOCKS = "blocks" in OPTS

def fail(msg):
    print("FAILED:", msg); sys.exit(1)

def part(text, start, end, name):
    if text.count(start) != 1:
        fail(f"{name}: start has {text.count(start)} matches")
    i = text.index(start)
    if end not in text[i:]:
        fail(f"{name}: no end")
    j = text.index(end, i) + len(end)
    return text[i:j]

def sub(text, a, b, name):
    if text.count(a) != 1:
        fail(f"{name}: {text.count(a)} matches")
    return text.replace(a, b)

def cut(text, start, end, new, name):
    """Replace the part from `start` up to and including `end`."""
    old = part(text, start, end, name)
    return text.replace(old, new)

large0 = (root / "sections" / "large.tex").read_text()
cuts0 = (root / "sections" / "cuts.tex").read_text()
if r"\section{Girth five outside a small set}" not in large0 or r"\subsection{Cycles of length four}" not in cuts0 \
        or r"\begin{lemma}[A third port]" not in (root / "sections" / "poles.tex").read_text():
    fail("the copy is not in the form of apply_girth_five.py lean and apply_fewer_cases.py keepgap")

# ---------------------------------------------------------------- poles.tex
p = root / "sections" / "poles.tex"
t = p.read_text()

HEAD = t[:t.index(r"\subsection{The shape of a pole with many paths}\label{sec:shape}")]
HEAD = sub(HEAD, r"""then the part looks like a ladder, and it has few cycles (Theorem~\ref{thm:fewcycles}). Second,
the number of paths between two ends is the largest possible, or it is smaller by a fixed factor
(Theorem~\ref{thm:gap}).""", r"""then the part looks like a ladder, and it has few cycles (Theorem~\ref{thm:fewcycles}). Second,
the number of paths between two ends is the largest possible, or it is smaller by a fixed factor
(Theorem~\ref{thm:gap}): a part that is not a ladder has a short cycle away from a shortest
path between the two ends.""", "idea box of Section 5")
HEAD = sub(HEAD, r"""no path from $s$ to $t$, then $P_{st}(N)\le2^{b-1}$. If a cycle $Z$ of $N$ is disjoint from some
path from $s$ to $t$, and $N-E(Z)$ has $k$ components, then $P_{st}(N)\le2^{b}-2^{b-|Z|+k-1}$.""",
r"""no path from $s$ to $t$, then $P_{st}(N)\le2^{b-1}$. If a cycle $Z$ of $N$ is disjoint from some
path from $s$ to $t$, then $P_{st}(N)\le2^{b}-2^{b-|Z|}$.""", "joins statement")
HEAD = sub(HEAD, r"""$N-E(Z)$. So $N-E(Z)$ has $2^{\beta(N-E(Z))}$ such joins, and $\beta(N-E(Z))=b-|Z|+k-1$. The union""",
r"""$N-E(Z)$. So $N-E(Z)$ has $2^{\beta(N-E(Z))}$ such joins, and $\beta(N-E(Z))\ge b-|Z|$. The union""", "joins proof")

_i = t.index(r"\begin{figure}[ht]")                      # the first figure of the section
FIGLAYERS = t[_i:t.index(r"\end{figure}", _i) + len(r"\end{figure}")]
if r"\label{fig:layers}" not in FIGLAYERS:
    fail("figure of the layers")
FIGLAYERS = sub(FIGLAYERS, r"""is thin: it has one vertex of the shortest path $A$ and one vertex of $J$
(Proposition~\ref{prop:thin}).}""", r"""is thin: it has one vertex of the shortest path $A$ and one vertex of $J$
(Lemma~\ref{lem:path} and Proposition~\ref{prop:thin}).}""", "caption of the layers")
STEPS = part(t, r"\step{Step 1: the layers are small.}",
             "  C=C_\\varepsilon:=\\frac{40\\Theta\\,(20\\Theta+1)\\,2^{20\\Theta-1}}{\\varepsilon}.\n\\]\n", "steps 1 to 3")
STEPS = sub(STEPS, "2^{20\\Theta-1}}{\\varepsilon}.\n\\]\n", "2^{20\\Theta-1}}{\\varepsilon}.\\qedhere\n\\]\n", "end of step 3")
TILES = part(t, r"\subsection{Full pairs}\label{sec:full}", r"\end{figure}", "tiles")
LADDERTAIL = part(t, r"This means the following. Every layer $L_j$ with $0<j<b$ consists of $w_j$ and of one",
                  "interfaces and the edges at the caps.\n", "ladder step")
FOURPORTS = part(t, r"\begin{corollary}[Four ports]\label{cor:fourports}", "caps, this is a chain.\n\\end{proof}\n", "four ports")

FULLCLAUSE = r"""
If the pair $s,t$ is full, then $c(N)\le20\cdot2^{b/2}$.""" if CAPS else ""
FULLPROOF = r""" If the pair $s,t$ is full, then the pair of ports of every $N_i$ is
full. Then $J$ is a forest by Lemma~\ref{lem:joins}, and $c(N_i)\le10\cdot2^{b_i/2}$ by
Lemma~\ref{lem:path}(d).""" if CAPS else ""
GADGETB = r"""\item[\textup{(b)}] If $P_{ac}+P_{bc}\ge(1+2\varepsilon)2^{h}$, then $P_{ab}\le2K_\varepsilon\,2^{h/2}$.
If the pairs $a,c$ and $b,c$ are full, then $P_{ab}\le20\sqrt2\cdot2^{h/2}$.""" if CAPS else \
          r"""\item[\textup{(b)}] If $P_{ac}+P_{bc}\ge(1+2\varepsilon)2^{h}$, then $P_{ab}\le2K_\varepsilon\,2^{h/2}$."""
GADGETBPROOF = r""" If the pairs $a,c$ and $b,c$ are full, then the pair $z,c$ is full in $N'$, and
$c(N')\le20\cdot2^{(h+1)/2}$.""" if CAPS else ""
CONSTANTS = "" if CAPS else r"""
For Proposition~\ref{prop:threecut} we fix
\[
  \varepsilon_0=\tfrac1{1000},\qquad K_0=K_{\varepsilon_0},\qquad\kappa(h)=2K_0\,2^{-h/2}.
\]
"""

NEW = HEAD + r"""\subsection{A shortest path between the ports}\label{sec:shape}

Let $N$ be a bridgeless $2$-pole with ports $s,t$ and rank $b\ge2$. It has $2b$ vertices. It has no
cut vertex: a cut vertex of a subcubic multigraph is joined to some component by a single edge.
We use the following notation. The \emph{layer} $L_j$ is the set of vertices at distance $j$ from
$s$. Every edge joins vertices of the same layer or of consecutive layers. Let $\ell$ be the
distance from $s$ to $t$, let $A=w_0w_1\cdots w_\ell$ be a shortest path from $s$ to $t$, and put
\[
  J=N-V(A),\qquad\Delta=b-\ell .
\]
Then $w_j\in L_j$. Write $e_i$ for the edge $w_{i-1}w_i$ of $A$. A vertex of $A$ lies on two edges
of $A$, or on one if it is a port. So it has at most one \emph{further edge}. This edge leads to
$J$, or it is parallel to an edge of $A$, because $A$ is a shortest path. For $0<j<\ell$ the layer
$L_j$ separates $s$ from $t$, so $|L_j|\ge2$. Call $L_j$ \emph{thin} if $0<j<\ell$ and $|L_j|=2$.
A thin layer consists of $w_j$ and one vertex of $J$ (Figure~\ref{fig:layers}).

""" + FIGLAYERS + r"""

The first lemma has no hypothesis on the number of paths.

\begin{lemma}[A shortest path]\label{lem:path}
Let $N$ be a bridgeless $2$-pole of rank $b\ge2$. In the notation above,
\begin{enumerate}
\item[\textup{(a)}] $0\le\Delta\le\beta(J)$;
\item[\textup{(b)}] at most $2\Delta$ of the layers $L_j$ with $0<j<\ell$ are not thin, and at
most $4\Delta$ vertices of $J$ lie outside the thin layers;
\item[\textup{(c)}] every cycle of $J$ has at most $4\Delta+2$ vertices;
\item[\textup{(d)}] $c(N)\le10\cdot2^{\,5\beta(J)+b/2}$.
\end{enumerate}
\end{lemma}

\begin{proof}
(a) The layers $L_0,\dots,L_\ell$ contain at least $2\ell$ vertices, so $\ell\le b$. The graph $J$
has $2b-\ell-1\ge1$ vertices. The vertices of $A$ meet the $\ell$ edges of $A$ and at most
$\ell+1$ other edges, and $N$ has $3b-1$ edges. So $|E(J)|\ge(3b-1)-(2\ell+1)$, and
$\beta(J)\ge|E(J)|-|V(J)|+1\ge b-\ell$.

(b) Compare $N$ with a multigraph that has one vertex in $L_0$ and in $L_\ell$, two in each layer
between, and none beyond. Then $N$ has exactly $2\Delta$ vertices more. A layer between $L_0$ and
$L_\ell$ with $n\ge3$ vertices has $n-2$ vertices too many, and $n-1\le2(n-2)$ of its vertices are
in $J$. The vertices of $L_\ell$ other than $t$ and the vertices beyond $L_\ell$ are too many,
and they are in $J$. This gives~(b).

(c) Let $Z$ be a cycle of $J$, and let $L_i$ and $L_j$ be the first and the last layer that it
meets. A thin layer has one vertex of $J$. If $i<l<j$, the two paths of $Z$ between a vertex in
$L_i$ and a vertex in $L_j$ both have a vertex in $L_l$, so $L_l$ is not thin. Hence at most two
vertices of $Z$ are in thin layers, and~(b) gives~(c).

(d) An even subgraph of $N$ without an edge of $A$ has degree at most one at each vertex of $A$,
hence degree zero. So it is an even subgraph of $J$, and there are $2^{\beta(J)}$ of them. The sum
of two even subgraphs with the same edges in $A$ has no edge of $A$. So at most $2^{\beta(J)}$
cycles of $N$ have the same edges in $A$.

Let $Z$ be a cycle that contains an edge of $A$, and let $e_a$ and $e_z$ be the first and the
last edge of $A$ in $Z$.

\step{Two strands.} Let $L_l=\{w_l,y_l\}$ be a thin layer with $a\le l<z$. The cycle $Z$ contains
$w_{a-1}$ and $w_z$, so it has vertices before and after this layer. So it has at least two edges
from $L_{l-1}$ to $L_l$ and at least two edges from $L_l$ to $L_{l+1}$. The two vertices of $L_l$
have degree at most two in $Z$. So $Z$ has exactly two edges on each side of $L_l$. Suppose that
both edges from $L_{l-1}$ end in the same vertex of $L_l$. Then both edges to $L_{l+1}$ start in
the other vertex, and no edge of $Z$ joins the part of $Z$ before $L_l$ to the part after it.
This is impossible, because $Z$ is connected. So each vertex of $L_l$ has one edge of $Z$ to
$L_{l-1}$ and one to $L_{l+1}$.

\step{Free indices.} Call an index $i$ \emph{free} if the further edge of $w_{i-1}$ leads to
$L_i$ and the further edge of $w_i$ leads to $L_{i-1}$. Two consecutive indices are not both
free, because $w_i$ has one further edge at most. Let $a<i<z$, and suppose that the layers
$L_{i-1}$ and $L_i$ are thin and that $e_i$ is not in $Z$. By the last paragraph, $Z$ has an edge
from $w_{i-1}$ to $L_i$ and an edge from $w_i$ to $L_{i-1}$. These are further edges. So $i$ is
free.

\step{The count.} So the edges of $Z$ in $A$ are determined by $a$ and $z$ and by a choice for
each index $i$ with $a<i<z$ that is free, or for which $L_{i-1}$ or $L_i$ is not thin. At most
$(z-a)/2$ of the indices between $a$ and $z$ are free, and by~(b) at most $4\Delta$ indices are of
the second kind. So for given $a\le z$ there are at most $2^{4\Delta+(z-a)/2}$ possibilities.
With the first paragraph,
\[
  c(N)\;\le\;2^{\beta(J)}\Bigl(1+2^{4\Delta}\sum_{1\le a\le z\le\ell}2^{(z-a)/2}\Bigr)
  \;\le\;2^{\beta(J)}\bigl(1+9\cdot2^{4\Delta+\ell/2}\bigr)\;\le\;10\cdot2^{\,5\beta(J)+b/2}.
\]
Here the sum is at most $2^{\ell/2}\sum_{i\ge1}i\,2^{-i/2}=(4+3\sqrt2)\,2^{\ell/2}$, and we use
$\Delta\le\beta(J)$ and $\ell\le b$.
\end{proof}

\begin{idea}{outline of the proof of Proposition~\ref{prop:thin}}
Add the shortest path $A$ to a path from $s$ to $t$. The result is an even subgraph whose edges
away from $A$ form a forest. So the outside part is a forest for more than half of the even
subgraphs, and every layer is small by Lemma~\ref{lem:width}. By
Lemma~\ref{lem:smallcuts} there are few short cycles away from $A$. So the rank of $J$ is
bounded. By Lemma~\ref{lem:path}, almost every layer then has exactly two vertices, and $N$ has
few cycles.
\end{idea}

\begin{proposition}[Away from the shortest path]\label{prop:thin}
For every $\varepsilon\in(0,\half]$ there is a number $C=C_\varepsilon\ge1$ with the following
property. Let $N$ be a bridgeless $2$-pole of rank $b\ge2$ with ports $s,t$ and
$P_{st}(N)\ge(\half+\varepsilon)2^{b}$. Then $\beta(J)\le C$, in the notation above.
\end{proposition}

\begin{proof}
""" + STEPS + r"""\end{proof}

\begin{theorem}[Few cycles]\label{thm:fewcycles}
For every $\varepsilon\in(0,\half]$ there is a constant $K_\varepsilon$ with the following property.
Let $N$ be a pole of rank $b$, and let $s,t$ be two of its ports with
$P_{st}(N)\ge(\half+\varepsilon)2^{b}$. Then
\[
  c(N)\;\le\;K_\varepsilon\,2^{b/2}.
\]""" + FULLCLAUSE + r"""
\end{theorem}

\begin{proof}
In the notation of Lemma~\ref{lem:reduction}, $c(N)=\sum_ic(N_i)$, and each $N_i$ is a
bridgeless $2$-pole with at least $(\half+\varepsilon)2^{b_i}$ paths between its ports. If
$b_i=1$, then $c(N_i)=1$. If $b_i\ge2$, then $c(N_i)\le10\cdot2^{5C_\varepsilon}\,2^{b_i/2}$ by
Proposition~\ref{prop:thin} and Lemma~\ref{lem:path}(d). Also
$\sum_i2^{b_i/2}\le2^{b/2}+q-1\le2\cdot2^{b/2}$, because $x+y\le xy+1$ for $x,y\ge1$. So the
theorem holds with $K_\varepsilon=20\cdot2^{5C_\varepsilon}$.""" + FULLPROOF + r"""
\end{proof}

""" + TILES + r"""

\begin{lemma}[Ladders]\label{lem:ladders}
Let $N$ be a bridgeless $2$-pole with ports $s,t$ and rank $b$. If $b=1$, then $N$ consists of two
vertices and two parallel edges, and the pair $s,t$ is full. If $b\ge2$, the following statements
are equivalent, in the notation of Section~\ref{sec:shape}:
\begin{enumerate}
\item[\textup{(i)}] the pair $s,t$ is full;
\item[\textup{(ii)}] the graph $J$ is a forest;
\item[\textup{(iii)}] $N$ is a capped ladder whose caps are $s$ and $t$.
\end{enumerate}
\end{lemma}

\begin{proof}
If $b=1$, then $N$ has two vertices, and it is a cycle. Let $b\ge2$.

\step{From \textup{(i)} to \textup{(ii)}.} By Lemma~\ref{lem:joins}, every cycle meets the path
$A$.

\step{From \textup{(ii)} to \textup{(iii)}.} By Lemma~\ref{lem:path}(a), $b-\ell\le\beta(J)=0$.
So $\ell=b$, and equality holds in every estimate of the proof of Lemma~\ref{lem:path}(a).
""" + LADDERTAIL + r"""
\step{From \textup{(iii)} to \textup{(i)}.} Let the tiles have total weight $W$, so $b=W+1$. A path
from $s$ to $t$ passes the tiles in order. It enters a tile at a vertex of the left pair and
leaves it at a vertex of the right pair. In a square there are two paths to each vertex of the
right pair. In a single rung the path stays or crosses. So there are $2\cdot2^{W}=2^{b}$ paths.
\end{proof}

\begin{theorem}[Gap]\label{thm:gap}
There is a constant $\gamma_0\in(0,\frac14]$ with the following property. Let $N$ be a pole of
rank $b$, and let $s,t$ be two of its ports. Then
\[
  P_{st}(N)=2^{b}\qquad\text{or}\qquad P_{st}(N)\le(1-\gamma_0)\,2^{b}.
\]
\end{theorem}

\begin{proof}
Put $C=C_{1/4}$ and $\gamma_0=2^{-4C-2}$. Let $P_{st}(N)>(1-\gamma_0)2^{b}$. In the notation of
Lemma~\ref{lem:reduction}, the path counts of the bridgeless $2$-poles $N_1,\dots,N_q$ multiply,
and $P(N_i)>(1-\gamma_0)2^{b_i}$ for every $i$. So it suffices to show that the pair of ports of
each $N_i$ is full.

Let $N$ be one of them, with rank $b$. If $b=1$, the pair is full. Let $b\ge2$, and suppose that
$J$ contains a cycle $Z$. We have $P_{st}(N)\ge\frac34\,2^{b}$. So $\beta(J)\le C$ by
Proposition~\ref{prop:thin}, and $Z$ has at most $4C+2$ vertices by Lemma~\ref{lem:path}(a)
and~(c). The cycle $Z$ is disjoint from the path $A$. By Lemma~\ref{lem:joins},
$P_{st}(N)\le2^{b}-2^{b-|Z|}\le(1-\gamma_0)2^{b}$. This is a contradiction. So $J$ is a forest,
and the pair is full by Lemma~\ref{lem:ladders}.
\end{proof}

""" + FOURPORTS + r"""
\subsection{Three gadgets}\label{sec:gadgets}

For four distinct ports $a,b,c,d$ of a pole $N$ let $f_{ab|cd}(N)$ be the number of pairs of
vertex-disjoint paths of $N$, one from $a$ to $b$ and one from $c$ to $d$.

\begin{lemma}\label{lem:gadgets}
Let $\varepsilon\in(0,\half]$, and let $N$ be a pole of rank $h$. In each statement below, the
letters denote distinct ports of $N$. Write $P_{xy}$ for $P_{xy}(N)$ and $f$ for $f(N)$.
\begin{enumerate}
\item[\textup{(a)}] If $P_{ab}\ge(\half+\varepsilon)2^{h}$, then $c(N)\le K_\varepsilon\,2^{h/2}$.
""" + GADGETB + r"""
\item[\textup{(c)}] If $P_{ac}+P_{ad}+P_{bc}+P_{bd}\ge(2+4\varepsilon)2^{h}$, then
$f_{ac|bd}+f_{ad|bc}\le2K_\varepsilon\,2^{h/2}$.
\item[\textup{(d)}] If $P_{ab}+f_{ac|bd}+f_{ad|bc}\ge(1+2\varepsilon)2^{h}$, then
$P_{cd}\le2K_\varepsilon\,2^{h/2}$.
\end{enumerate}
\end{lemma}

\begin{proof}
(a) is Theorem~\ref{thm:fewcycles}. In each of the other cases we change $N$ into a pole $N'$ and
apply Theorem~\ref{thm:fewcycles} to two ports of $N'$.

(b) Add a new vertex $z$ and join it to $a$ and $b$. Then $N'$ has rank $h+1$, and
$P_{zc}(N')=P_{ac}+P_{bc}\ge(\half+\varepsilon)2^{h+1}$. The cycles of $N'$ through $z$
correspond to the paths of $N$ from $a$ to $b$. So
$P_{ab}\le c(N')\le K_\varepsilon\,2^{(h+1)/2}$.""" + GADGETBPROOF + r"""

(c) Add a new vertex $z$ joined to $a$ and $b$, and a new vertex $w$ joined to $c$ and $d$. Then
$N'$ has rank $h+2$, and $P_{zw}(N')$ is the sum of the four path counts. The cycles of $N'$
through $z$ and $w$ correspond to the pairs counted by $f_{ac|bd}+f_{ad|bc}$. So this sum is at
most $K_\varepsilon\,2^{(h+2)/2}$.

(d) Add an edge between $c$ and $d$. Then $N'$ has rank $h+1$. A path from $a$ to $b$ in $N'$
avoids the new edge, or it consists of the new edge and a pair counted by
$f_{ac|bd}+f_{ad|bc}$. So $P_{ab}(N')=P_{ab}+f_{ac|bd}+f_{ad|bc}$. The cycles of $N'$ through the
new edge correspond to the paths of $N$ from $c$ to $d$. So
$P_{cd}\le K_\varepsilon\,2^{(h+1)/2}$.
\end{proof}
""" + CONSTANTS
p.write_text(NEW)
print("poles.tex written")

# ---------------------------------------------------------------- cuts.tex
p = root / "sections" / "cuts.tex"
t = p.read_text()
t = sub(t, r"""length four and close the rest by a \emph{cap}, a small tree, in two ways
(Lemma~\ref{lem:cap}).""", r"""length four and close the rest by a \emph{cap}, a small tree
(Lemma~\ref{lem:cap}).""", "idea box of Section 6")
i3 = t.index(r"\subsection{Cuts of size at most three}")
i4 = t.index(r"\subsection{States of a pole with four ports}")
RINGS = t[:i3]
THREECUT = t[i3:i4]
CAPPROOF = part(t, r"Add two new vertices $x$ and $y$ and an edge between them, join $x$ to the",
                r"cycles of $Y$, these are $c(Y)+(S+F-u_\alpha)2^{h}$ distinct cycles of $\hat Y$.", "cap proof")

STATES = r"""Let $Y$ be a $4$-pole of rank $h$ with ports $1,2,3,4$. A \emph{pairing} is one of the three
partitions $12|34$, $13|24$, $14|23$ of the ports into two pairs; the two pairs of a pairing are
\emph{opposite}. For a pair $ij$ and a pairing $\alpha=ij|kl$ put
\[
  a_{ij}=2^{-h}P_{ij}(Y),\qquad u_\alpha=2^{-h}f_{ij|kl}(Y),\qquad
  S=\sum_{ij}a_{ij},\qquad F=\sum_\alpha u_\alpha .
\]
A pair of disjoint paths that joins the four ports is a join for the set of all four ports, and
there are $2^{h}$ such joins. So $a_{ij}\le1$ and $F\le1$.

"""

if CAPS:
    CAP = r"""\begin{lemma}[Cap]\label{lem:cap}
For every $\eta>0$ there is $h_1(\eta)$ with the following property. Let $Y$ be a pole of rank
$h\ge h_1(\eta)$ with two, three or four ports. Put $z=2^{-h}c(Y)$, and let $S$ be the sum of
the numbers $2^{-h}P_{ij}(Y)$ over the pairs $ij$ of ports. If $Y$ has two ports, then
$z+S\le1+\eta$. If $Y$ has three ports, then $z+S\le2+\eta$. If $Y$ has four ports, then
$z+S+F-u_\alpha\le4+\eta$ for every pairing $\alpha$.
\end{lemma}

\begin{proof}
Let $Y$ have four ports, and let $\alpha=ij|kl$. """ + CAPPROOF + r""" By
Corollary~\ref{cor:cycles}, $\hat Y$ has at most $(\half+\frac18\eta)\,2^{h+3}=(4+\eta)\,2^{h}$
cycles, when $h$ is large. If $Y$ has three ports, add one new vertex and join it to the three
ports. If $Y$ has two ports, add an edge between them. A path of $Y$ between two ports and the
new vertex or the new edge form a cycle. The new multigraph has rank $h+2$ or $h+1$, and
Corollary~\ref{cor:cycles} gives the claim in the same way.
\end{proof}

"""
else:
    CAP = r"""\begin{lemma}[Cap]\label{lem:cap}
For every $\eta>0$ there is $h_1(\eta)$ with the following property. Let $Y$ be a $4$-pole of
rank $h\ge h_1(\eta)$, and put $z=2^{-h}c(Y)$. Then, for every pairing $\alpha$,
\[
  z+S+F-u_\alpha\;\le\;4+\eta .
\]
\end{lemma}

\begin{proof}
Let $\alpha=ij|kl$. """ + CAPPROOF + r""" By
Corollary~\ref{cor:cycles}, $\hat Y$ has at most $(\half+\frac18\eta)\,2^{h+3}=(4+\eta)\,2^{h}$
cycles, when $h$ is large.
\end{proof}

"""

RIGID = r"""\begin{lemma}[Rigidity]\label{lem:rigid}
There are numbers $\rho_0\in(0,1)$ and $h_0$ with the following property. Let $Y$ be a $4$-pole
of rank $h\ge h_0$ with $S+F\ge4-\rho_0$. Then three pairs with a common port are full, or the
four pairs between two disjoint pairs of ports are full.
\end{lemma}

\begin{proof}
Suppose that this is false. Then there are $4$-poles $Y_1,Y_2,\dots$ whose ranks $h_n$ tend to
infinity, with $S(Y_n)+F(Y_n)\ge4-\frac1n$, such that no $Y_n$ has three full pairs with a common
port or four full pairs between two disjoint pairs of ports. The numbers $a_{ij}(Y_n)$ and
$u_\alpha(Y_n)$ lie in $[0,1]$. We take a subsequence in which each of these nine sequences
converges, and we write $a_{ij}$, $u_\alpha$, $S$ and $F$ for the limits. Then $F\le1$ and
$S+F\ge4$.

\step{Three implications.} For distinct ports $i,j,k,l$,
\begin{align}
  &a_{ik}+a_{jk}>1\ \Longrightarrow\ a_{ij}=0;\label{eq:T1}\\
  &a_{ik}+a_{il}+a_{jk}+a_{jl}>2\ \Longrightarrow\ u_{ik|jl}+u_{il|jk}=0;\label{eq:T2}\\
  &a_{kl}>0\ \Longrightarrow\ a_{ij}+F-u_{ij|kl}\le1.\label{eq:T3}
\end{align}
Indeed, let $a_{ik}+a_{jk}>1+2\varepsilon$ with $\varepsilon>0$. For large $n$,
Lemma~\ref{lem:gadgets}(b) gives $a_{ij}(Y_n)\le2K_\varepsilon\,2^{-h_n/2}$, and this tends to
$0$. In the same way~\eqref{eq:T2} follows from Lemma~\ref{lem:gadgets}(c). If
$a_{ij}+F-u_{ij|kl}>1$, then Lemma~\ref{lem:gadgets}(d) gives $a_{kl}=0$; this
is~\eqref{eq:T3}.

\step{The limit.} For a partition of the ports into two pairs, the \emph{cross sum} is the sum of
$a_{ij}$ over the four pairs $ij$ that are not pairs of the partition. Each pair occurs in two of
the three cross sums.

Suppose that some cross sum is larger than $2$, say the cross sum $X$ of $12|34$. Then
$a_{13}+a_{23}>1$ or $a_{14}+a_{24}>1$, so $a_{12}=0$ by~\eqref{eq:T1}. In the same way
$a_{34}=0$. By~\eqref{eq:T2}, $u_{13|24}=u_{14|23}=0$. Put $u=u_{12|34}$. Then $X+u=S+F\ge4$.
If one of the four numbers in $X$ is $0$, say $a_{24}$, then the other three and $u$ are equal
to $1$. This contradicts~\eqref{eq:T3} for $ij=14$, because $a_{23}>0$. So the four numbers are
positive, and~\eqref{eq:T3} gives $a_{ij}+u\le1$ for each of them. Hence $X+4u\le4$. With
$X+u\ge4$ this gives $u=0$ and $X=4$, so the four numbers are equal to $1$.

Suppose that no cross sum is larger than $2$. The three cross sums add up to $2S$, so $S\le3$.
Hence $S=3$ and $F=1$, every cross sum is $2$, and two opposite numbers add up to $1$. If all six
numbers are positive, then~\eqref{eq:T3} gives $u_\alpha\ge\max\{a_{ij},a_{kl}\}\ge\half$ for
every pairing $\alpha=ij|kl$, and this contradicts $F=1$. So one number is $0$, say $a_{34}$, and
$a_{12}=1$. If $a_{13}>0$, then $a_{23}=0$ by~\eqref{eq:T1}, so $a_{14}=1$; then $a_{24}=0$
by~\eqref{eq:T1}, so $a_{13}=1$. If $a_{13}=0$, then $a_{24}=1$; then $a_{14}=0$
by~\eqref{eq:T1}, so $a_{23}=1$. In both cases three numbers with a common port are equal
to $1$.

\step{The end.} So three numbers $a_{ij}$ with a common port, or the four numbers between two
disjoint pairs of ports, are equal to $1$. For large $n$ the corresponding numbers
$a_{ij}(Y_n)$ are larger than $1-\gamma_0$, and these pairs are full in $Y_n$ by
Theorem~\ref{thm:gap}. This is a contradiction.
\end{proof}

"""

FOUR = r"""\subsection{Cycles of length four}

\begin{figure}[ht]
\centering
\begin{tikzpicture}[x=1cm,y=1cm]
  \foreach \ox/\lab in {0/a,6.5/c}{
    \draw[region] (\ox,0) ellipse [x radius=1.0, y radius=1.5];
    \node[text=accent] at (\ox-0.4,0) {$Y$};
    \foreach \i/\y in {1/1.05,2/0.35,3/-0.35,4/-1.05}{
      \coordinate (\lab p\i) at (\ox+0.62,\y);
      \node[note, text=accent] at (\ox+0.3,\y) {\scriptsize\i};}
  }
  % the cycle C
  \foreach \i/\y in {1/1.05,2/0.35,3/-0.35,4/-1.05} \coordinate (c\i) at (2.1,\y);
  \draw[edge] (ap1)--(c1) (ap2)--(c2) (ap3)--(c3) (ap4)--(c4);
  \draw[cool] (c1)--(c2)--(c3)--(c4);
  \draw[cool] (c4) .. controls (3.1,-0.9) and (3.1,0.9) .. (c1);
  \foreach \i in {1,2,3,4} \node[vtx] at (c\i) {};
  \node[note, text=accent] at (2.45,0) {$C$};
  % the cap for 14|23
  \coordinate (x2) at (9.0,0);
  \coordinate (y2) at (8.0,0);
  \draw[hot] (cp1)--(x2)--(cp4) (cp2)--(y2)--(cp3) (x2)--(y2);
  \node[vtx] at (x2) {};
  \node[vtx] at (y2) {};
  \foreach \lab in {a,c} \foreach \i in {1,2,3,4} \node[port] at (\lab p\i) {};
  \node[note] at (1.1,-1.95) {the graph $G$};
  \node[note] at (7.6,-1.95) {the cap for $14|23$};
\end{tikzpicture}
\caption{A cycle $C$ of length four and the rest $Y$ of the graph, and the cap of
Lemma~\ref{lem:cap} for the pairing $14|23$. The number $a_{ij}$ counts the paths between the
ports $i$ and $j$ of $Y$, and $u_\alpha$ counts the pairs of disjoint paths for a pairing
$\alpha$ of the ports, both as a proportion of the largest possible number.}
\label{fig:glue}
\end{figure}

\begin{idea}{outline of the proof of Theorem~\ref{thm:fourcut}}
Let $C$ be a cycle of length four, and let $Y$ be the rest of the graph, of rank $k$. A cycle
that meets $C$ and $Y$ consists of paths of $Y$ and of paths of $C$. In units of $2^{k}$, the
number of these cycles is the sum of the numbers $S+F-u_\alpha$ for the two pairings $\alpha$
that pair the ports at neighbours on $C$. By the cap of Lemma~\ref{lem:cap}, one of these
numbers and the proportion of cycles of $Y$ are together at most $4+o(1)$, and $c(G)\ge2^{r-1}$
requires the sum $8$. So $S+F\ge4-o(1)$. By Lemma~\ref{lem:rigid} there are two possible shapes.
Three full pairs at one port give a cyclic cut of size three. If the four pairs between two
pairs of ports are full, then $Y$ is a chain of tiles, and $G$ is a ring.
\end{idea}

\begin{theorem}\label{thm:fourcut}
There is a constant $r_4$ with the following property. Let $G$ be a connected cubic multigraph
of rank $r\ge r_4$ that has no cyclic cut of size at most three and has a cycle of length four.
Then $G$ is a ring, or $c(G)<2^{r-1}$.
\end{theorem}

\begin{proof}
Let $C=c_1c_2c_3c_4$ be a cycle of length four, and put $Y=G-V(C)$ (Figure~\ref{fig:glue}). By
the remark at the start of the section, $G$ has no loop and no cut of size at most two, and
every cut of size three has a single vertex on one side. The graph has $2r-2$ vertices, so a set
of at most five vertices and its complement both have more than one vertex.

\step{The rest is a $4$-pole without bridge.} No edge outside $C$ joins two vertices of $C$:
such an edge and a path of $C$ form a cycle with at most three vertices, and the cut around
these vertices has size at most three. So exactly four edges leave $V(C)$, one at each vertex.
Let $c_i$ be joined to the vertex $i$ of $Y$. The vertices $1,2,3,4$ are distinct: if two of
them are one vertex $v$, the cut around $V(C)\cup\{v\}$ has size at most three. The multigraph
$Y$ is connected: otherwise some component of $Y$ is joined to $C$ by at most two edges, and
these form a cut. So $Y$ is a $4$-pole with the ports $1,2,3,4$. Let $k$ be its rank. Then
$r=k+4$.

Let $e$ be a bridge of $Y$, and let $A$ and $B$ be the vertex sets of the two components of
$Y-e$. In $G[A]$ every vertex has degree at least two, except the end of $e$, which has degree at
least one. A forest with an edge has two vertices of degree one, so $G[A]$ contains a cycle. The
same holds for $G[B]$. Each of the four edges between $C$ and $Y$ is in exactly one of the cuts
$\delta A$ and $\delta B$, and $e$ is in both. So $|\delta A|+|\delta B|=6$, and one of them is a
cyclic cut of size at most three. Hence $Y$ has no bridge.

\step{The count.} We use the notation of this section for $Y$, with $h=k$, and we put
$z=2^{-k}c(Y)$. A cycle of $G$ that is neither $C$ nor a cycle of $Y$ uses two or four of the
edges between $C$ and $Y$. With two, at $c_i$ and $c_j$, it consists of a path of $Y$ between the
ports $i$ and $j$ and of one of the two paths of $C$ between $c_i$ and $c_j$. With four, it
consists of a pair of disjoint paths of $Y$ and of two disjoint edges of $C$. The edges $c_1c_2$
and $c_3c_4$ close the pair to one cycle if and only if its pairing is not $12|34$. The edges
$c_1c_4$ and $c_2c_3$ do this if and only if its pairing is not $14|23$. Hence
\begin{equation}\label{eq:four}
  \frac{c(G)}{2^{k}}\;=\;2^{-k}+z+\bigl(S+F-u_{12|34}\bigr)+\bigl(S+F-u_{14|23}\bigr).
\end{equation}
Let $\rho_0$ and $h_0$ be as in Lemma~\ref{lem:rigid}, and let $r$ be so large that
$k\ge\max\{h_0,\,h_1(\rho_0/2),\,4\}$ and $2^{-k}\le\rho_0/2$. Suppose that
$c(G)\ge2^{r-1}=8\cdot2^{k}$. We show that $G$ is a ring. By Lemma~\ref{lem:cap} for the pairing
$14|23$, the term $z$ and the second bracket of~\eqref{eq:four} are together at most
$4+\rho_0/2$. So $S+F\ge S+F-u_{12|34}\ge4-\rho_0$, and Lemma~\ref{lem:rigid} applies to $Y$. It
gives two cases.

\step{Case 1: three pairs with a common port are full.} Let $p$ be the common port, and let $q$,
$v$ and $v'$ be the other ports. Replace $v$ and $v'$, each with its two edges, by one edge. By
Lemma~\ref{lem:reduction}(a) the result $Y^{\circ}$ is a $2$-pole of rank $k$ with the ports
$p,q$, and this pair is full. It has no bridge, because $Y$ has none. By
Lemma~\ref{lem:ladders}, $Y^{\circ}$ is a capped ladder with the caps $p$ and $q$. Its tiles
have total weight $k-1\ge3$, so there are at least two tiles. Let $X$ consist of $p$ and of the
vertices of the first tile, and let $Z$ be a cycle of $Y^{\circ}$ in the last tile and the cap
$q$. Then $Z$ avoids $X$, and $Y^{\circ}[X]$ is connected and contains a cycle.

Suppose that the edge of $Y^{\circ}$ that replaces $v$ has both ends in $X$. Then $Y$ has a path
from $p$ to $v$ whose other vertices are in $X\cup\{v'\}$. It is disjoint from the cycle of $Y$
that corresponds to $Z$. This contradicts Lemma~\ref{lem:joins} for the full pair $p,v$. The
same holds for $v'$. So the edges of $Y^{\circ}$ with both ends in $X$ are edges of $Y$, and
$G[X]$ contains a cycle. Three edges of $G$ leave $X$: the edge from $p$ to $C$, and one edge of
$Y$ for each of the two edges of $Y^{\circ}$ that leave $X$. The cycle $C$ is outside $X$. So
$\delta X$ is a cyclic cut of size three, and this case does not occur.

\step{Case 2: the four pairs between two disjoint pairs of ports are full.} The pole $Y$ has no
bridge. By Corollary~\ref{cor:fourports} it is a chain of tiles; one of the two pairs of ports
is the left pair of its first tile, and the other is the right pair of its last tile. If the
pairs are $1,3$ and $2,4$, then $C$ is a square with the pairs $c_1,c_3$ and $c_2,c_4$. In the
other case let the pairs be $1,2$ and $3,4$, by symmetry. Then the edges $c_1c_2$ and $c_3c_4$
are single rungs, and the edges $c_2c_3$ and $c_1c_4$ are the interface between them. In both
cases the edges between $C$ and $Y$ are two interfaces. So $G$ is a ring.
\end{proof}
"""

if CAPS:
    HEADPROOF = part(THREECUT, r"\subsection{Cuts of size at most three}",
                     r"There is one pair for $d=2$, and there are three pairs for $d=3$.", "head of the proof for small cuts")
    HEADPROOF = sub(HEADPROOF, r"  c(G)\;\le\;2^{r-1}+5K_0^{2}\,2^{r/2}.", r"  c(G)\;\le\;2^{r-1}+420\cdot2^{r/2}.", "statement for small cuts")
    THREECUT = HEADPROOF + r""" Let $r$ be large, and
suppose that $c(G)\ge2^{r-1}$. Put $z=2^{-b_2}c(T_2)$ and $\eta=\frac18\gamma_0$, with
$\gamma_0$ as in Theorem~\ref{thm:gap}. By~\eqref{eq:glue23}, and because $c(T_1)<2^{b_1}$ and
$b_1\ge1$,
\[
  2^{d-2}\;\le\;2^{-b_2}+\frac z2+\sum_jx_ja_j .
\]
The rank $b_2\ge(r-2)/2$ is large. So $2^{-b_2}\le\eta$, and Lemma~\ref{lem:cap} for $T_2$ gives
$z\le2^{d-2}+\eta-\sum_ja_j\le2^{d-2}+\eta-\sum_jx_ja_j$. Hence
\begin{equation}\label{eq:near}
  \sum_jx_ja_j\;\ge\;2^{d-2}-3\eta .
\end{equation}

Let $d=2$. Then $x_1a_1>1-\gamma_0$, so the pair of ports is full in both sides, by
Theorem~\ref{thm:gap}. By~\eqref{eq:glue23} and Theorem~\ref{thm:fewcycles},
$c(G)=2^{r-1}+c(T_1)+c(T_2)\le2^{r-1}+20\,(2^{b_1/2}+2^{b_2/2})\le2^{r-1}+20\cdot2^{r/2}$.

Let $d=3$, and number the pairs so that $a_1\ge a_2\ge a_3$. Any two pairs of ports of a $3$-pole
have one port in common. By~\eqref{eq:near}, $a_1+a_2\ge\frac23\sum_ja_j\ge\frac54$. So
$a_3\le2K_{1/8}\,2^{-b_2/2}\le\eta$ by Lemma~\ref{lem:gadgets}(b), and~\eqref{eq:near} gives
$x_1a_1+x_2a_2\ge2-4\eta$. So the numbers $a_1,a_2,x_1,x_2$ are larger than $1-\gamma_0$, and
the pairs $1$ and $2$ are full in both sides. By Lemma~\ref{lem:gadgets}(b),
$x_3\le20\sqrt2\cdot2^{-b_1/2}$ and $a_3\le20\sqrt2\cdot2^{-b_2/2}$, and
$c(T_i)\le20\cdot2^{b_i/2}$ by Theorem~\ref{thm:fewcycles}. Now~\eqref{eq:glue23} gives
\[
  c(G)\;\le\;20\,(2^{b_1/2}+2^{b_2/2})+2^{b_1+b_2}\bigl(2+800\cdot2^{-(b_1+b_2)/2}\bigr)
  \;\le\;2^{r-1}+420\cdot2^{r/2},
\]
because $r=b_1+b_2+2$ and $b_1,b_2\le r-3$.\qedhere
\end{proof}

"""
    t = (RINGS + r"\subsection{Caps}\label{sec:caps}" + "\n\n" + STATES + CAP + THREECUT
         + r"\subsection{A pole with four ports and many paths}" + "\n\n" + RIGID + FOUR)
else:
    t = RINGS + THREECUT + r"\subsection{A pole with four ports}" + "\n\n" + STATES + CAP + RIGID + FOUR
p.write_text(t)
print("cuts.tex written")

# ---------------------------------------------------------------- large.tex
p = root / "sections" / "large.tex"
t = p.read_text()
t = cut(t, r"The set $C_2$ is connected and disjoint from $C_1$, so it lies in one component of $H-C_1$.",
        r"$C_1\subseteq U_2$ and $U_2\subseteq U_1$ would give $C_1\subseteq U_1$.",
        r"""Let $W_i$ be the vertex set of the component of $p$ in $H-C_i$. Some edge joins $U_i$ to $C_i$,
and some edge joins $W_i$ to $C_i$, because $H$ is connected. The set $C_2$ is connected and
disjoint from $C_1$, so it lies in one component of $H-C_1$. If this component is not $U_1$, then
$U_1\cup C_1$ is a connected set that contains $u$ and avoids $C_2$, so $U_1\cup C_1\subseteq U_2$.
This is the first alternative. If $C_2\subseteq U_1$, then $W_1\cup C_1$ is a connected set that
contains $p$ and avoids $C_2$, so $W_1\cup C_1\subseteq W_2$. Then $U_2\cup C_2$ is a connected
set that contains $u$ and avoids $C_1$, so $U_2\cup C_2\subseteq U_1$. This is the second
alternative. The two alternatives exclude each other, because
$C_1\subseteq U_2$ and $U_2\subseteq U_1$ would give $C_1\subseteq U_1$.""", "proof of nesting")

t = cut(t, r"\begin{lemma}[Two links]\label{lem:sep}", r"\end{proof}", r"""\begin{lemma}[Two links]\label{lem:sep}
Let $G$ be a connected multigraph, and let $p$ be a vertex. Let $\mathcal A$ be a finite family of
regions that avoid $p$, with weights $w_A\ge0$ of total $\mu$. Let $W_2$ be the sum of
$w_Aw_{A'}$ over the ordered pairs $(A,A')$ of disjoint regions of $\mathcal A$ with
$\ell(A,A')=2$. Let $N$, $e$ and $M$ be numbers such that the following holds for every
$A\in\mathcal A$. At most $N$ vertices outside $A$ have a neighbour in $A$. The regions of
$\mathcal A$ that are disjoint from $A$ and joined to $A$ by an edge have total weight at most
$e$. For every vertex $u\notin A$ in the component of $p$ in $G-A$, the regions of $\mathcal A$
that are disjoint from $A$, avoid $u$, and separate $u$ from $p$ in $G-A$ have total weight at
most $M$. Then
\[
  W_2\;\le\;2\mu\,(e+NM).
\]
\end{lemma}

\begin{proof}
Let $A,A'\in\mathcal A$ be disjoint. Then $A'$ lies in the component of $p$ in $G-A$, or $A$ lies
in the component of $p$ in $G-A'$. Indeed, suppose that the first statement is false. A path from
$p$ to its first vertex in $A$ stays in the component of $p$ in $G-A$ before it ends, so it avoids
$A'$. As $A$ is connected and disjoint from $A'$, all of $A$ lies in the component of $p$ in
$G-A'$.

Call an ordered pair $(A,A')$ \emph{good} if the regions are disjoint, $\ell(A,A')=2$, no edge
joins them, and $A'$ lies in the component of $p$ in $G-A$. By the last paragraph, the pairs with
the first, the second and the fourth property have total weight at least $W_2/2$. The pairs that
are joined by an edge have total weight at most $e\mu$. So the good pairs have total weight at
least $W_2/2-e\mu$.

Let $(A,A')$ be good. No edge joins the two regions, so the two links are components $Y_1,Y_2$ of
$G-A-A'$ that are joined to both. The vertex $p$ lies in at most one of them. Let $Y$ be one that
avoids $p$, and let $u$ be a vertex of $Y$ with a neighbour in $A$. The set $Y$ is connected and
joined to $A'$, and $A'$ lies in the component of $p$ in $G-A$. So $u$ lies in that component as
well. And $Y$ is a component of $G-A-A'$ that contains $u$ and not $p$. So $A'$ avoids $u$ and
separates $u$ from $p$ in $G-A$. For a given $A$ there are at most $N$ vertices $u$ outside $A$
with a neighbour in $A$, and for each of them these regions $A'$ have total weight at most $M$.
So the good pairs have total weight at most $\mu NM$, and $W_2/2-e\mu\le\mu NM$.
\end{proof}""", "two links")

WDEF = r"\lceil\Phi(\Lambda)/m\rceil+1" if BLOCKS else r"\lceil2\Lambda\,\Phi(\Lambda)/m\rceil+1"
t = cut(t, r"Put $\nu=\nu_\Lambda(G,P)$ and $w=\lceil2\Lambda\,\Phi(\Lambda)/m\rceil+1$. We may assume that",
        "and the claim follows because\n$w\\ge1$.",
        r"""Put $\nu=\nu_\Lambda(G,P)$ and $w=WDEF$. Fix $p\in P$. We apply
Lemma~\ref{lem:sep}. Let $A\in\mathcal A$. By~(a), at most $\Lambda$ vertices outside $A$ have a
neighbour in $A$, and a region that is joined to $A$ by an edge contains one of them. The
regions of $\mathcal A$ that contain a given vertex all meet one of them, so their total weight
is at most $\kappa$ by~(b). Hence we may take $N=\Lambda$ and $e=\Lambda\kappa$. Let $u\notin A$
be a vertex in the component of $p$ in $G-A$, and consider the regions of $\mathcal A$ that are
disjoint from $A$, avoid $u$, and separate $u$ from $p$ in $G-A$. Take a maximal family
$C_1,\dots,C_T$ of pairwise disjoint regions among them. Each of these regions meets some $C_i$,
so their total weight is at most $T\kappa$ by~(b). As $q(G,P)>\frac9{25}$,
Proposition~\ref{prop:chain} gives $T\le(\Lambda+\nu+2)\,w$. So we may take
$M=(\Lambda+\nu+2)\,w\kappa$, and the lemma gives $W_2\le2\mu\Lambda\kappa\,(\Lambda+\nu+3)\,w$.

By~(c), $\PP(Z\ne0)\le1-q(G,P)\le\frac35$, and the Cauchy--Schwarz inequality
$\mu^{2}\le\EE Z^{2}\cdot\PP(Z\ne0)$ gives $\mu^{2}\le\frac35(\mu^{2}+W_2+K\mu)$. So
$\mu\le\frac32(K+W_2/\mu)$ if $\mu>0$, and this is the claim.""".replace("WDEF", WDEF), "proof for heavy families")

if BLOCKS:
    if t.count(r"\bigl(\lceil2\Lambda\,\Phi(\Lambda)/m\rceil+1\bigr)") != 2:
        fail("the two thresholds")
    t = t.replace(r"\bigl(\lceil2\Lambda\,\Phi(\Lambda)/m\rceil+1\bigr)", r"\bigl(\lceil\Phi(\Lambda)/m\rceil+1\bigr)")
    t = cut(t, r"\step{Blocks.} For $i<j$ put $X_{ij}=U_j\sm(U_i\cup C_i)$.",
            r"$X_{ij}\subseteq U_j\subseteq U_{i'}$ is disjoint from $X_{i'j'}$.",
            r"""\step{Blocks.} Let $j\ge i+2$. Take a path from $u$ to $p$ in $H$, let $x$ be its last vertex in
$C_i$, and let $y$ be its first vertex after $x$ in $C_j$; there is one, because $x\in U_j$ and
$p\notin U_j$. If $i<l<j$, then $x\in U_l$ and $y\notin U_l\cup C_l$, so the path meets $C_l$
between $x$ and $y$. Between $x$ and $y$ the path avoids $C_i$ and $C_j$. So the sets $C_l$ with
$i<l<j$ lie in one component of $H-(C_i\cup C_j)$. Let $B_{ij}$ be its vertex set. Every edge of
$H$ that leaves $B_{ij}$ ends in $C_i$ or in $C_j$. The set $B_{ij}$ is connected, and it
contains $C_{i+1}$, which lies in $U_j$ and outside $U_i\cup C_i$. So $B_{ij}\subseteq U_j$, and
$B_{ij}$ avoids $U_i\cup C_i$. Hence $B_{ij}$ and $B_{i'j'}$ are disjoint if $j\le i'$.""", "blocks")
    t = sub(t, r"""Put $w=\lceil2\Lambda\,\Phi(\Lambda)/m\rceil+1$, and let $Y_l=X_{lw+1,\,(l+1)w+1}$ for
$l=0,1,\dots$ with $(l+1)w\le T-1$. These sets are pairwise disjoint, each contains $w-1$ of the
sets $C_i$, and every edge of $H$ that leaves $Y_l$ ends in one of its two end sets. So
$|Y_l|\ge(w-1)m\ge2\Lambda\,\Phi(\Lambda)$, and at most $2\Lambda$ edges of $H$ leave $Y_l$.""",
r"""Put $w=\lceil\Phi(\Lambda)/m\rceil+1$, and let $Y_l=B_{lw+1,\,(l+1)w+1}$ for
$l=0,1,\dots$ with $(l+1)w\le T-1$. These sets are connected and pairwise disjoint, each contains
$w-1$ of the sets $C_i$, and every edge of $H$ that leaves $Y_l$ ends in one of its two end sets.
So $|Y_l|\ge(w-1)m\ge\Phi(\Lambda)$, and at most $2\Lambda$ edges of $H$ leave $Y_l$.""", "block width")
    t = cut(t, r"\step{Pieces.} Every component of $G[Y]$ has an edge that leaves $Y$.",
            r"Lemma~\ref{lem:product}, for the two sets $Y'$, gives $q(G,P)\le\frac9{25}$.",
            r"""\step{Pieces.} So $G[Y]$ is connected, it has at most $2\Lambda$ boundary vertices and at least
$\Phi(\Lambda)$ vertices, and it has girth at least five and no $\Lambda$-short cycle. So every
even set of boundary vertices of $G[Y]$ has forest proportion less than $\frac35$.
Lemma~\ref{lem:product}, for the two sets $Y$, gives $q(G,P)\le\frac9{25}$.""", "pieces")
    t = sub(t, r"block end in its two end sets (proof of Proposition~\ref{prop:chain}).}",
               r"block end in its two end sets (proof of Proposition~\ref{prop:chain}).}", "caption of the chain")
p.write_text(t)
print("large.tex written")

# ---------------------------------------------------------------- layers.tex
p = root / "sections" / "layers.tex"
t = p.read_text()
t = cut(t, r"Suppose that $m_j\ge\Theta$ for some $j$. Start with the window $i=i'=j$.",
        r"window contradicts Step~1.",
        r"""Suppose that $m_j\ge\Theta$ for some $j$. Start with the window $i=i'=j$. As long as a level next
to the window has more than $m^{3/4}$ vertices outside $P$, where $m=|X(i,i')|$ is the present
size, add that level to the window. The graph is finite, so this stops. A step increases
$m^{1/4}$ by more than $\frac16$, because $(t+\frac16)^{4}\le t^{4}+t^{3}$ for $t\ge1$. Let $\mu$
be the final size. Then there were fewer than $6\mu^{1/4}$ steps, and both levels next to the
final window have at most $\mu^{3/4}$ vertices outside $P$. We have $k\le\sqrt\mu$, because
$\mu\ge\Theta\ge2^{100}(k+1)^{2}$. By~\eqref{eq:window},
\[
  |\delta X(i,i')|\;\le\;6\mu^{3/4}+3k\bigl(6\mu^{1/4}+3\bigr)\;\le\;33\,\mu^{3/4}
  \;\le\;\frac{\mu}{4\log^{2}\mu}=\frac{\Phi(\mu)}4 .
\]
The last inequality says that $132\log^{2}\mu\le\mu^{1/4}$, and this holds for
$\mu\ge2^{100}$. So the final window contradicts Step~1.""", "the window")
p.write_text(t)
print("layers.tex written")

# ---------------------------------------------------------------- intro.tex
p = root / "sections" / "intro.tex"
t = p.read_text()
t = sub(t, r"""we also put a small tree, a \emph{cap}, in the place of the cycle of length four, in two ways,
and apply the bound $(\half+o(1))2^{r}$ to the two graphs that arise (Lemma~\ref{lem:cap}).""",
r"""we also put a small tree, a \emph{cap}, in the place of the cycle of length four,
and apply the bound $(\half+o(1))2^{r}$ to the graph that arises (Lemma~\ref{lem:cap}).""", "cases 1 and 2")
t = sub(t, r"""argument, the chain of nested cycles, the parallel-link lemma and Lemma~\ref{lem:star}. Astra found""",
           r"""argument, the chain of nested cycles and the parallel-link lemma. Astra found""", "origins 1")
t = sub(t, r"""necessary. Fable~5.2 also found the form of
Theorem~\ref{thm:fourcut} for a cycle of length four. The marked set also gives
Corollary~\ref{cor:cycles} (Lemma~\ref{lem:marked}); the first proof of this corollary was a
recursion over the edges of a shortest cycle, by Fable~5.2.""",
r"""necessary. Fable~5.2 also found the form of
Theorem~\ref{thm:fourcut} for a cycle of length four. In a last round the two models worked
apart. Each of them found that the marked set gives Corollary~\ref{cor:cycles}
(Lemma~\ref{lem:marked}), in the place of a recursion over the edges of a shortest cycle, and
that Theorem~\ref{thm:gap} follows from Proposition~\ref{prop:thin}, in the place of an
induction on the rank. Astra found Lemma~\ref{lem:path} with the count of the cycles by their
edges on a shortest path, the proof of Lemma~\ref{lem:rigid} by a limit, the cut of size three
in Case~1 of Theorem~\ref{thm:fourcut}, the upper bound of Lemma~\ref{lem:sep}, CAPSCREDITand the present
Step~2 of Lemma~\ref{lem:width}.""".replace("CAPSCREDIT", r"the proof of Proposition~\ref{prop:threecut} with caps, " if CAPS else ""), "origins 2")
t = sub(t, r"""Proposition~\ref{prop:thin}; Lemma~\ref{lem:gadgets} &""",
           r"""Proposition~\ref{prop:thin}; Lemma~\ref{lem:gadgets} for $\varepsilon=\frac1{1000}$ &""", "table gadgets")
t = sub(t, r"""Theorem~\ref{thm:gap} & \lean{EMS.gapStatement}\\""",
           r"""Theorem~\ref{thm:gap} with the constant $\frac1{16}$ & \lean{EMS.gapStatement}\\""", "table gap")
t = sub(t, r"""Lemma~\ref{lem:cap} & \lean{EMS.Shortening.TreeCapCycleBound.exists_thousandth_bound}\\""",
           r"""Lemma~\ref{lem:cap} for four ports and $\eta=\frac1{1000}$ & \lean{EMS.Shortening.TreeCapCycleBound.exists_thousandth_bound}\\""", "table cap")
t = sub(t, r"""Lemma~\ref{lem:star}; Lemma~\ref{lem:rigid} and the cases of a cut of size four, as arithmetic &""",
           r"""A pole with three full pairs at one port has at most half of the possible pairs of disjoint paths; Lemma~\ref{lem:rigid} with fixed numbers and the cases of a cut of size four, as arithmetic &""", "table rigid")
t = cut(t, r"The kernel check covers the formal statements, and no machine has checked the text of this",
        "These tests do not\nreplace a proof.",
        r"""The kernel check covers the formal statements, and no machine has checked the text of this
paper. A formal proof can differ from the text, and in the following places the method is
different. The formal proof of Theorem~\ref{thm:forest} bounds the links of two cycles, which is
Step~2 of Proposition~\ref{prop:loggirth}, with Lemma~\ref{lem:smallcuts}. The formal proof of
Corollary~\ref{cor:cycles} uses the forest estimate in its form for a simple graph, which is
in~\cite{Pan}, and a recursion over the edges of a shortest cycle. The formal proof of
Theorem~\ref{thm:fewcycles} counts the perfect matchings between consecutive thin layers. The
formal proof of Lemma~\ref{lem:ladders} uses two disjoint paths between the ports and exact
numbers of paths in a capped ladder. The formal proof of Theorem~\ref{thm:gap} is an induction
on the rank, with a lemma on a pole with a third port; it gives the constant $\frac1{16}$.
CAPSDIFFThe formal proof treats every cyclic cut of size four in a graph without a smaller cyclic cut.
It has a count for two arbitrary sides, a form of Lemma~\ref{lem:rigid} with fixed numbers, and
a bound for the pairs of disjoint paths in a pole with three full pairs at one port; the text
needs a cycle of length four only. The largest difference is in the last case. The
formal proof assumes that the graph has no cyclic cut of size at most four, and it has a number
$D_*\ge256$ and two cases. For a graph with a cycle shorter than $D_*$ it sorts the cycles
through an edge of a shortest cycle by the vertex where they leave it. For girth at least $D_*$
it uses pieces of large girth, and it raises the girth in stages by the deletion of maximal
families of short cycles. In other places the details differ. For example, the formal cap of
Lemma~\ref{lem:cap} has a vertex in the middle of the edge $xy$. So the text can contain errors
that the formal proof does not have. Fable~5.2 has read the whole text, Astra has read the
parts that it proposed, and no referee has read the text. Scripts in the repository test the
statements of Sections~\ref{sec:poles} and~\ref{sec:cuts} on small graphs. These tests do not
replace a proof.""".replace("CAPSDIFF", "The formal proof of Proposition~\\ref{prop:threecut} has two cases by the number of paths in\nthe larger side, and it uses no cap. " if CAPS else ""), "differences")
p.write_text(t)
print("intro.tex written")

# ---------------------------------------------------------------- proof.tex
if CAPS:
    p = root / "sections" / "proof.tex"
    t = p.read_text()
    t = sub(t, r"Let $K_0$ be as in Section~\ref{sec:poles}. By~\eqref{eq:H},", r"By~\eqref{eq:H},", "K_0")
    for a, b in ((r"5K_0^{2}\,2^{r/2}", r"420\cdot2^{r/2}"), (r"r-2>10K_0^{2}", r"r-2>840")):
        if t.count(a) != 2:
            fail(f"proof.tex: {a} has {t.count(a)} matches")
        t = t.replace(a, b)
    p.write_text(t)
    print("proof.tex written")
print("applied")
