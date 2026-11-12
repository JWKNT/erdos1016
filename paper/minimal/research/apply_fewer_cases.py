# Writes two reductions of Sections 5 and 6 into a copy of the manuscript.
#
#   1. The gap theorem (Theorem 5.10) becomes a consequence of the proof of Proposition 5.3 and of
#      Lemma 5.8.  The lemma on a third port (Lemma 5.9) and the induction on the rank are removed.
#      The gap constant is then a small number gamma_0, and Section 6 has eps_0 = gamma_0/20 in the
#      place of 1/1000.
#   2. Theorem 6.8 is stated for a cycle of length four in a graph without a cyclic cut of size at
#      most three.  The lemma on gluing (Lemma 6.4) is removed, and only one side is examined.
#      This form needs the last case in the form for girth five, so the copy must first be changed
#      by apply_girth_five.py (lean or clean).
#   3. A loop gives a cyclic cut of size one.  So the case of a loop is a part of Proposition 6.3,
#      and the proof of the main theorem has three cases.
#   4. The count with a marked set (the last case of Section 9) becomes Lemma 3.7.  It also gives
#      Corollary 3.7 (the leading term), so the edge recursion is removed.
#
# Usage: python3 apply_fewer_cases.py <folder that contains exact-maximum.tex and sections/> [all|keepgap]
#   all (default): the four reductions.
#   keepgap:       the reductions 2, 3 and 4 only.  The gap theorem keeps its proof by induction
#                  and the constant 1/16, Lemma 5.9 stays, and Section 6 keeps its numbers.
# The folder is a copy that apply_girth_five.py has changed.  Every replacement must match
# exactly once; a missing marker stops the script with exit code 1.  The script changes the copy
# only.
import sys, pathlib

root = pathlib.Path(sys.argv[1])
MODE = sys.argv[2] if len(sys.argv) > 2 else "all"
if MODE not in ("all", "keepgap"):
    print("FAILED: the mode is all or keepgap"); sys.exit(1)
GAP = (MODE == "all")

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

if r"\section{Girth five outside a small set}" not in (root / "sections" / "large.tex").read_text():
    fail("the copy does not have the last case in the form for girth five; run apply_girth_five.py first")

# ---------------------------------------------------------------- poles.tex
p = root / "sections" / "poles.tex"
t = p.read_text()

t = sub(t, r"""\item[\textup{(iii)}] at most $10C+2$ vertices of $N$ lie outside the ordinary layers.
\end{enumerate}""", r"""\item[\textup{(iii)}] at most $10C+2$ vertices of $N$ lie outside the ordinary layers;
\item[\textup{(iv)}] if $J$ contains a cycle, then it contains a cycle with at most
$20\,\Theta_{\varepsilon/2}(1)$ vertices.
\end{enumerate}""", "thin (iv)")
t = sub(t, r"""$\sigma\le10\Theta$ and $|R|\le20\Theta$.""",
           r"""$\sigma\le10\Theta$ and $|R|\le20\Theta$. For the interval of all indices this is~(iv).""", "thin step 2")

GADGETS = part(t, r"\paragraph{Consequences of Theorem~\ref{thm:fewcycles}.}",
               "new edge correspond to the paths of $N$ from $c$ to $d$. So $P_{cd}\\le K_0\\,2^{(h+1)/2}$.\n\\end{proof}\n", "gadgets")
TILES = part(t, r"\subsection{Full pairs}\label{sec:full}", r"\end{figure}", "tiles")
FOURPORTS = part(t, r"\begin{corollary}[Four ports]\label{cor:fourports}", "caps, this is a chain.\n\\end{proof}\n", "four ports")
LADDERSTEP = part(t, r"The count in Step~4 of the proof of", "interfaces and the edges at the caps.\n", "ladder step")
head = t[:t.index(r"\paragraph{Consequences of Theorem~\ref{thm:fewcycles}.}")]

G2 = GADGETS
G2 = sub(G2, r"\paragraph{Consequences of Theorem~\ref{thm:fewcycles}.}",
             r"\subsection{Constants}\label{sec:constants}" + "\n", "gadgets title")
G2 = sub(G2, r"""\[
  \varepsilon_0=\tfrac1{1000},\qquad K_0=K_{\varepsilon_0},\qquad\kappa(h)=2K_0\,2^{-h/2}.
\]""", r"""\[
  \varepsilon_0=\tfrac1{20}\,\gamma_0,\qquad K_0=K_{\varepsilon_0},\qquad\kappa(h)=2K_0\,2^{-h/2},
\]
with $\gamma_0$ as in Theorem~\ref{thm:gap} and $K_\varepsilon$ as in Theorem~\ref{thm:fewcycles}.
Then $\varepsilon_0\le\frac1{80}$.""", "constants")
G2 = sub(G2, r"If $P_{ab}\ge0.501\cdot2^{h}$,", r"If $P_{ab}\ge(\half+\varepsilon_0)2^{h}$,", "gadget a")
G2 = sub(G2, r"If $P_{ac}+P_{bc}\ge1.002\cdot2^{h}$,", r"If $P_{ac}+P_{bc}\ge(1+2\varepsilon_0)2^{h}$,", "gadget b")
G2 = sub(G2, r"If $P_{ac}+P_{ad}+P_{bc}+P_{bd}\ge2.004\cdot2^{h}$,",
             r"If $P_{ac}+P_{ad}+P_{bc}+P_{bd}\ge(2+4\varepsilon_0)2^{h}$,", "gadget c")
G2 = sub(G2, r"If $P_{ab}+f_{ac|bd}+f_{ad|bc}\ge1.002\cdot2^{h}$,",
             r"If $P_{ab}+f_{ac|bd}+f_{ad|bc}\ge(1+2\varepsilon_0)2^{h}$,", "gadget d")

LADDERS = r"""\begin{lemma}[Ladders]\label{lem:ladders}
Let $N$ be a bridgeless $2$-pole with ports $s,t$ and rank $b$. If $b=1$, then $N$ consists of two
vertices and two parallel edges, and the pair $s,t$ is full. If $b\ge2$, the following statements
are equivalent, in the notation of Section~\ref{sec:shape}:
\begin{enumerate}
\item[\textup{(i)}] the pair $s,t$ is full;
\item[\textup{(ii)}] the graph $J=N-V(A)$ is a forest;
\item[\textup{(iii)}] $N$ is a capped ladder whose caps are $s$ and $t$.
\end{enumerate}
\end{lemma}

\begin{proof}
If $b=1$, then $N$ has two vertices, and it is a cycle. Let $b\ge2$.

\step{From \textup{(i)} to \textup{(ii)}.} By Lemma~\ref{lem:joins}, every cycle meets the path
$A$.

\step{From \textup{(ii)} to \textup{(iii)}.} """ + LADDERSTEP + r"""
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
Put $\Theta=\Theta_{1/8}(1)$ and $\gamma_0=2^{-20\Theta}$. Let $P_{st}(N)>(1-\gamma_0)2^{b}$. In
the notation of Lemma~\ref{lem:reduction}, the path counts of the bridgeless $2$-poles
$N_1,\dots,N_q$ multiply, and $P(N_i)>(1-\gamma_0)2^{b_i}$ for every $i$. So it suffices to show
that the pair of ports of each $N_i$ is full.

Let $N$ be one of them, with rank $b$. If $b=1$, the pair is full. Let $b\ge2$, and use the
notation of Section~\ref{sec:shape}. Suppose that $J$ contains a cycle. We have
$P_{st}(N)\ge\frac34\,2^{b}$. So $J$ contains a cycle $Z$ with at most $20\Theta$ vertices, by
Proposition~\ref{prop:thin}(iv) with $\varepsilon=\frac14$. The cycle $Z$ is disjoint from the path
$A$. By Lemma~\ref{lem:joins}, $P_{st}(N)\le2^{b}-2^{b-|Z|}\le(1-\gamma_0)2^{b}$. This is a
contradiction. So $J$ is a forest, and the pair is full by Lemma~\ref{lem:ladders}.
\end{proof}

"""

t = head + TILES + "\n\n" + LADDERS + FOURPORTS + "\n" + G2
t = sub(t, r"""then the part looks like a ladder, and it has few cycles (Theorem~\ref{thm:fewcycles}). Second,
the number of paths between two ends is the largest possible, or it is smaller by a fixed factor
(Theorem~\ref{thm:gap}).""", r"""then the part looks like a ladder, and it has few cycles (Theorem~\ref{thm:fewcycles}). Second,
the number of paths between two ends is the largest possible, or it is smaller by a fixed factor
(Theorem~\ref{thm:gap}): a part that is not a ladder has a short cycle away from a shortest
path between the two ends.""", "idea box")
if GAP:
    p.write_text(t)
    print("poles.tex written")

# ---------------------------------------------------------------- cuts.tex
p = root / "sections" / "cuts.tex"
t = p.read_text()

t = sub(t, r"\section{Rings and cyclic cuts of size at most four}\label{sec:cuts}",
           r"\section{Rings, small cyclic cuts, and cycles of length four}\label{sec:cuts}", "title")
t = sub(t, r"""We count the cycles of the rings. Then we show that a graph of large rank with a cyclic cut of
size at most four is a ring, or it has at most $2^{r-1}+O(2^{r/2})$ cycles
(Proposition~\ref{prop:threecut} and Theorem~\ref{thm:fourcut}). The proof uses the gap of
Section~\ref{sec:poles}: a side of the cut has all possible paths between two ends, or a fixed
proportion of them is missing. For a cut of size four it also uses a \emph{cap}: a small tree
that closes the larger side of the cut (Lemma~\ref{lem:cap}).""",
r"""We count the cycles of the rings. Then we show that a graph of large rank with a cyclic cut of
size at most three has at most $2^{r-1}+O(2^{r/2})$ cycles (Proposition~\ref{prop:threecut}), and
that a graph without such a cut and with a cycle of length four is a ring, or it has fewer than
$2^{r-1}$ cycles (Theorem~\ref{thm:fourcut}). For the second statement we delete the cycle of
length four and close the rest by a \emph{cap}, a small tree, in two ways
(Lemma~\ref{lem:cap}). The proof uses the gap of Section~\ref{sec:poles}: a pole has all
possible paths between two ends, or a fixed proportion of them is missing.""", "idea box")

t = sub(t, r"In this section $G$ is a connected cubic multigraph without loops, of rank $r$.",
           r"In this section $G$ is a connected cubic multigraph of rank $r$.", "no loops 1")
t = sub(t, r"""Hence every cut of size at most two is cyclic, and a cut of size three is cyclic unless
one of its sides is a single vertex.""", r"""Hence every cut of size at most two is cyclic, and a cut of size three is cyclic unless
one of its sides is a single vertex. If $G$ has a loop at a vertex $v$ and $r\ge2$, the other
edge at $v$ is a cyclic cut of size one.""", "no loops 2")
t = sub(t, r"""There is a constant $r_3$ with the following property. Let $G$ be a connected cubic multigraph
without loops, of rank $r\ge r_3$, that has a cyclic cut of size at most three. Then""",
r"""There is a constant $r_3$ with the following property. Let $G$ be a connected cubic multigraph
of rank $r\ge r_3$ that has a cyclic cut of size at most three. Then""", "no loops 3")
t = sub(t, r"""Let $d\in\{2,3\}$. Then $T_1$ and $T_2$ are $d$-poles, and the cut edges match their ports. A cycle""",
r"""Let $d\in\{2,3\}$. Then $G$ has no loop, so $T_1$ and $T_2$ are $d$-poles, and the cut edges
match their ports. A cycle""", "no loops 4")
i = t.index(r"There is one pair for $d=2$, and there are three pairs for $d=3$. Let $r$ be large.")
j = t.index(r"\subsection{States of a pole with four ports}")
STAR = part(t, r"\begin{lemma}[Full star]\label{lem:star}", "$h-1$, and it has at most $2^{h-1}$ paths from $1$ to $j$ by~\\eqref{eq:joinbound}.\n\\end{proof}\n", "full star")
CAPPROOF = part(t, r"Let $\alpha=ij|kl$. Add two new vertices $x$ and $y$ and an edge between them, join $x$ to the",
                r"cycles of $Y$, these are $c(Y)+(S+F-u_\alpha)2^{h}$ distinct cycles of $\hat Y$.", "cap proof")

THREE = r"""There is one pair for $d=2$, and there are three pairs for $d=3$. Let $r$ be large. Then
$b_2\ge(r-2)/2$ is large, and $\kappa(b_2)\le\varepsilon_0$. We have $c(T_1)<2^{b_1}$.

\step{Case A: $a_j\le\half+\varepsilon_0$ for all $j$.} By Corollary~\ref{cor:cycles},
$c(T_2)\le\frac9{16}2^{b_2}\le\frac9{32}2^{b_1+b_2}$. So $c(G)\,2^{-b_1-b_2}$ is less than
$2^{-b_2}+\frac9{32}+\half+\varepsilon_0$ for $d=2$, and less than
$2^{-b_2}+\frac9{32}+\frac32+3\varepsilon_0$ for $d=3$. In both cases $c(G)<2^{r-1}$, because
$\varepsilon_0\le\frac1{80}$.

\step{Case B: $a_j>\half+\varepsilon_0$ for some $j$.} Then $c(T_2)\le K_0\,2^{b_2/2}$ by
Lemma~\ref{lem:gadgets}(a). So $c(T_1)+c(T_2)<2^{b_1}+K_0\,2^{b_2/2}\le\varepsilon_0\,2^{b_1+b_2}$.

Let $d=2$. If $x_1<\half+\varepsilon_0$, then $c(G)<(\half+2\varepsilon_0)\,2^{b_1+b_2}<2^{r-1}$
by~\eqref{eq:glue23}. Otherwise $c(T_1)\le K_0\,2^{b_1/2}$ by Lemma~\ref{lem:gadgets}(a), and
\[
  c(G)\;\le\;2^{r-1}+K_0\bigl(2^{b_1/2}+2^{b_2/2}\bigr)\;\le\;2^{r-1}+2K_0\,2^{r/2}.
\]

Let $d=3$, and number the pairs so that $a_1\ge a_2\ge a_3$. Any two pairs of ports of a $3$-pole
have one port in common. If $a_1+a_2<1+2\varepsilon_0$, then $\sum_jx_ja_j<\frac32+3\varepsilon_0$
and $c(G)<2^{r-1}$. Otherwise $a_3\le\kappa(b_2)$ by Lemma~\ref{lem:gadgets}(b). If
$x_1+x_2<1+2\varepsilon_0$, then $\sum_jx_ja_j<1+3\varepsilon_0$ and $c(G)<2^{r-1}$. Otherwise
$x_3\le\kappa(b_1)$ and $c(T_1)\le K_0\,2^{b_1/2}$ by Lemma~\ref{lem:gadgets}(b) and~(a).
Then~\eqref{eq:glue23} gives
\[
  c(G)\;\le\;2K_0\,2^{b_2/2}+2^{b_1+b_2}\bigl(2+\kappa(b_1)\kappa(b_2)\bigr)
  \;=\;2^{r-1}+2K_0\,2^{b_2/2}+4K_0^{2}\,2^{(b_1+b_2)/2}
  \;\le\;2^{r-1}+5K_0^{2}\,2^{r/2}.\qedhere
\]
\end{proof}

"""

STATES = r"""\subsection{States of a pole with four ports}

Let $Y$ be a $4$-pole of rank $h$ with ports $1,2,3,4$. A \emph{pairing} is one of the three
partitions $12|34$, $13|24$, $14|23$ of the ports into two pairs; the two pairs of a pairing are
\emph{opposite}. For a pair $ij$ and a pairing $\alpha=ij|kl$ put
\[
  a_{ij}=2^{-h}P_{ij}(Y),\qquad u_\alpha=2^{-h}f_{ij|kl}(Y),\qquad
  S=\sum_{ij}a_{ij},\qquad F=\sum_\alpha u_\alpha .
\]
A pair of disjoint paths that joins the four ports is a join for the set of all four ports, and
there are $2^{h}$ such joins. So $a_{ij}\le1$ and $F\le1$. In this notation
Lemma~\ref{lem:gadgets} reads as follows, for distinct ports $i,j,k,l$ and with
$\kappa=\kappa(h)$:
\begin{align}
  &a_{ik}+a_{jk}\ge1+2\varepsilon_0\ \Longrightarrow\ a_{ij}\le\kappa;\label{eq:T1}\\
  &a_{ik}+a_{il}+a_{jk}+a_{jl}\ge2+4\varepsilon_0\ \Longrightarrow\ u_{ik|jl}+u_{il|jk}\le\kappa;\label{eq:T2}\\
  &a_{kl}>\kappa\ \Longrightarrow\ a_{ij}+F-u_{ij|kl}<1+2\varepsilon_0.\label{eq:T3}
\end{align}
Fix $h_0$ such that $\kappa(h)\le\varepsilon_0$ for $h\ge h_0$.

\begin{lemma}[Cap]\label{lem:cap}
There is $h_1\ge h_0$ with the following property. Let $Y$ be a $4$-pole of rank $h\ge h_1$, and
put $z=2^{-h}c(Y)$. Then, for every pairing $\alpha$,
\[
  z+S+F-u_\alpha\;\le\;4+\varepsilon_0 .
\]
\end{lemma}

\begin{proof}
""" + CAPPROOF + r""" By
Corollary~\ref{cor:cycles}, $\hat Y$ has at most
$(\half+\frac18\varepsilon_0)\,2^{h+3}=(4+\varepsilon_0)\,2^{h}$ cycles, when $h$ is large.
\end{proof}

\begin{lemma}[Rigidity]\label{lem:rigid}
Let $Y$ be a $4$-pole of rank $h\ge h_0$ with $S+F\ge4-2\varepsilon_0$. Then three pairs with a
common port are full, or the four pairs between two disjoint pairs of ports are full.
\end{lemma}

\begin{proof}
Write $\eta$ for $\varepsilon_0$; then $\kappa\le\eta\le\frac1{80}$. For a partition of the ports
into two pairs, the \emph{cross sum} is the sum of $a_{ij}$ over the four pairs $ij$ that are not
pairs of the partition. Each pair $ij$ occurs in two of the three cross sums. We use
Theorem~\ref{thm:gap} in this form: if $a_{ij}>1-20\eta$, then $ij$ is full.

\step{Case 1: some cross sum is at least $2+4\eta$.} Let it be the cross sum $X$ of $12|34$. Then
$a_{13}+a_{23}\ge1+2\eta$ or $a_{14}+a_{24}\ge1+2\eta$, so $a_{12}\le\kappa$ by~\eqref{eq:T1}. In
the same way $a_{34}\le\kappa$. By~\eqref{eq:T2}, $u_{13|24}+u_{14|23}\le\kappa$. Put
$u=u_{12|34}$. Then
\[
  S+F\;\le\;X+u+3\kappa .
\]
At most one of the four numbers in $X$ is at most $\kappa$, because $X\ge2+4\eta$. Let $ij$ be one
of the four pairs, and $kl$ the opposite pair. If $a_{kl}>\kappa$, then~\eqref{eq:T3} gives
$u<1+2\eta-a_{ij}$.

Suppose that all four numbers are larger than $\kappa$. Then $u<1+2\eta-m$, where $m$ is the
largest of them. So $S+F$ is less than the sum of the three smallest of them plus $1+5\eta$. As
$S+F\ge4-2\eta$, each of the three is larger than $1-7\eta$. So all four pairs are full.

Suppose that one of the four numbers is at most $\kappa$, say $a_{24}$. Then
$u<1+2\eta-\max\{a_{14},a_{23}\}$, and
$S+F<a_{13}+\min\{a_{14},a_{23}\}+1+2\eta+4\kappa\le3+6\eta$. This contradicts $S+F\ge4-2\eta$.

\step{Case 2: all cross sums are less than $2+4\eta$.} Their sum is $2S$, so $S<3+6\eta$. Hence
$F>1-8\eta$ and $S\ge3-2\eta$, and the sum of two opposite numbers is more than $1-6\eta$.

Suppose that all six numbers are larger than $\kappa$. For a pairing $\alpha=ij|kl$,
\eqref{eq:T3} gives $\max\{a_{ij},a_{kl}\}+F-u_\alpha<1+2\eta$, and the maximum is at least
$\half-3\eta$. So $F-u_\alpha<\half+5\eta$. Adding this for the three pairings gives
$2F<\frac32+15\eta$, a contradiction.

So one number is at most $\kappa$, say $a_{34}$. Then $a_{12}>1-7\eta$, so $12$ is full.
By~\eqref{eq:T1}, $a_{13}<2\eta$ or $a_{23}\le\kappa$; also $a_{14}<2\eta$ or $a_{24}\le\kappa$.
If a number is less than $2\eta$, its opposite is more than $1-8\eta$, hence full. If
$a_{13}<2\eta$, then $24$ is full, so $a_{14}<2\eta$, and $23$ is full. Then the pairs
$12,23,24$ are full. If $a_{23}<2\eta$, then $14$ is full, so $a_{24}<2\eta$, and $13$ is full.
Then the pairs $12,13,14$ are full.
\end{proof}

""" + STAR

FOUR = r"""
\subsection{Cycles of length four}

\begin{figure}[ht]
\centering
\begin{tikzpicture}[x=1cm,y=1cm]
  \foreach \ox/\lab in {0/a,5/b,10/c}{
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
  % the cap for 12|34
  \coordinate (x1) at (7.0,0.7);
  \coordinate (y1) at (7.0,-0.7);
  \draw[hot] (bp1)--(x1)--(bp2) (bp3)--(y1)--(bp4) (x1)--(y1);
  \node[vtx] at (x1) {};
  \node[vtx] at (y1) {};
  % the cap for 14|23
  \coordinate (x2) at (12.5,0);
  \coordinate (y2) at (11.5,0);
  \draw[hot] (cp1)--(x2)--(cp4) (cp2)--(y2)--(cp3) (x2)--(y2);
  \node[vtx] at (x2) {};
  \node[vtx] at (y2) {};
  \foreach \lab in {a,b,c} \foreach \i in {1,2,3,4} \node[port] at (\lab p\i) {};
  \node[note] at (1.1,-1.95) {the graph $G$};
  \node[note] at (6.0,-1.95) {the cap for $12|34$};
  \node[note] at (11.1,-1.95) {the cap for $14|23$};
\end{tikzpicture}
\caption{A cycle $C$ of length four and the rest $Y$ of the graph, and the two caps of
Lemma~\ref{lem:cap} that take the place of $C$. The number $a_{ij}$ counts the paths between the
ports $i$ and $j$ of $Y$, and $u_\alpha$ counts the pairs of disjoint paths for a pairing
$\alpha$ of the ports, both as a proportion of the largest possible number.}
\label{fig:glue}
\end{figure}

\begin{idea}{outline of the proof of Theorem~\ref{thm:fourcut}}
Let $C$ be a cycle of length four, and let $Y$ be the rest of the graph, of rank $k$. A cycle
that meets $C$ and $Y$ consists of paths of $Y$ and of paths of $C$. In units of $2^{k}$, the
number of these cycles is the sum of the numbers $S+F-u_\alpha$ for the two pairings $\alpha$
that pair the ports at neighbours on $C$. By the cap of Lemma~\ref{lem:cap}, each of these
numbers and the proportion of cycles of $Y$ are together at most $4+\varepsilon_0$, and
$c(G)\ge2^{r-1}$ requires the sum $8$. So $Y$ has few cycles, and $S+F\ge4-2\varepsilon_0$. By
Lemma~\ref{lem:rigid} there are two possible shapes. Three full pairs at one port are impossible
by Lemma~\ref{lem:star}. If the four pairs between two pairs of ports are full, then $Y$ is a
chain of tiles, and $G$ is a ring.
\end{idea}

\begin{theorem}\label{thm:fourcut}
There is a constant $r_4$ with the following property. Let $G$ be a connected cubic multigraph
of rank $r\ge r_4$ that has no cyclic cut of size at most three and has a cycle of length four.
Then $G$ is a ring, or $c(G)<2^{r-1}$.
\end{theorem}

\begin{proof}
Let $C=c_1c_2c_3c_4$ be a cycle of length four, and put $Y=G-V(C)$. By the remark at the start
of the section, $G$ has no loop and no cut of size at most two, and every cut of size three has
a single vertex on one side. The graph has $2r-2$ vertices, so a set of at most five vertices and its
complement both have more than one vertex.

\step{The rest is a $4$-pole without bridge.} No edge outside $C$ joins two vertices of $C$:
such an edge and a path of $C$ form a cycle with at most three vertices, and the cut around
these vertices has size at most three. So exactly four edges leave $V(C)$, one at each vertex.
Let $c_i$ be joined to the vertex $i$ of $Y$. The vertices $1,2,3,4$ are distinct: if two of
them are one vertex $v$, the cut around $V(C)\cup\{v\}$ has size at most three. The multigraph
$Y$ is
connected: otherwise some component of $Y$ is joined to $C$ by at most two edges, and these
form a cut. So $Y$ is a $4$-pole with the ports $1,2,3,4$. Let $k$ be its rank. Then $r=k+4$.

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
Let $r$ be so large that $k\ge h_1$ and $2^{-k}\le\varepsilon_0$, with $h_1$ as in
Lemma~\ref{lem:cap}. Suppose that $c(G)\ge2^{r-1}=8\cdot2^{k}$. We show that $G$ is a ring. By
Lemma~\ref{lem:cap} for the pairing $14|23$, the term $z$ and the second bracket
of~\eqref{eq:four} are together at most $4+\varepsilon_0$. So
$S+F-u_{12|34}\ge4-2\varepsilon_0$. By Lemma~\ref{lem:cap} for the pairing $12|34$, this gives
$z\le3\varepsilon_0$. Also $S+F\ge4-2\varepsilon_0$, so Lemma~\ref{lem:rigid} applies to $Y$.
It gives two cases.

\step{Case 1: three pairs with a common port are full.} By~\eqref{eq:T1}, the other three numbers
$a_{ij}$ are at most $\kappa$, so $S\le3+3\kappa$. By Lemma~\ref{lem:star}, every number
$u_\alpha$ is at most $\half$. The sum of the two brackets in~\eqref{eq:four} is $2S+F+u_{13|24}$,
and this is at most $6+6\kappa+\frac32$. So $c(G)\,2^{-k}\le\frac{15}2+10\varepsilon_0<8$. This
case does not occur.

\step{Case 2: the four pairs between two disjoint pairs of ports are full.} The pole $Y$ has no
bridge. By Corollary~\ref{cor:fourports} it is a chain of tiles; one of the two pairs of ports
is the left pair of its first tile, and the other is the right pair of its last tile. If the
pairs are $1,3$ and $2,4$, then $C$ is a square with the pairs $c_1,c_3$ and $c_2,c_4$. In the
other case let the pairs be $1,2$ and $3,4$, by symmetry. Then the edges $c_1c_2$ and $c_3c_4$
are single rungs, and the edges $c_2c_3$ and $c_1c_4$ are the interface between them. In both
cases the edges between $C$ and $Y$ are two interfaces. So $G$ is a ring.
\end{proof}
"""

if GAP:
    t = t[:i] + THREE + STATES + FOUR
else:
    # the numbers of the manuscript: the cap gives 4.001, and the rigidity lemma needs 3.99
    for a, b, n in ((r"4+\varepsilon_0", "4.001", 2), (r"4-2\varepsilon_0", "3.998", 3),
                    (r"$2^{-k}\le\varepsilon_0$", r"$2^{-k}\le\frac1{1000}$", 1),
                    (r"$z\le3\varepsilon_0$. Also $S+F\ge3.998$, so", r"$z\le0.003$. Also $S+F\ge3.99$, so", 1),
                    (r"\frac{15}2+10\varepsilon_0", "7.51", 1)):
        if FOUR.count(a) != n:
            fail(f"numbers of the theorem: {a} has {FOUR.count(a)} matches")
        FOUR = FOUR.replace(a, b)
    k1 = t.index(r"\begin{figure}[ht]", j)
    k2 = t.index(r"\begin{lemma}[Cap]\label{lem:cap}")
    k3 = t.index(STAR) + len(STAR)
    states_old = sub(t[j:k1], "We write $a_{ij}(Y)$, $S(Y)$ and so on\nwhen several poles are present. ", "", "several poles")
    t = t[:j] + states_old + t[k2:k3] + FOUR
p.write_text(t)
print("cuts.tex written")

# ---------------------------------------------------------------- proof.tex
p = root / "sections" / "proof.tex"
t = p.read_text()
t = sub(t, r"""\step{Case 1: $G$ has a loop $e$.} Every cycle of $G$ other than $e$ is a cycle of $G-e$, which has
rank $r-1$. So $c(G)\le1+(2^{r-1}-1)$.

\step{Case 2: $G$ has no loop, and it has a cyclic cut of size at most three.} Then
$c(G)\le2^{r-1}+5K_0^{2}\,2^{r/2}$ by Proposition~\ref{prop:threecut}.

\step{Case 3: $G$ has no loop, it has a cyclic cut of size four, and it has no smaller cyclic
cut.} Then $G$ is a ring or $c(G)<2^{r-1}$, by Theorem~\ref{thm:fourcut}.

\step{Case 4: $G$ has no loop and no cyclic cut of size at most four.} Let $Z$ be a cycle with
at most four edges. Then at most four edges leave $V(Z)$, and at most eight edges have an end in
$V(Z)$. So $G-V(Z)$ has rank at least $r-8>0$, and $\delta V(Z)$ is a cyclic cut of size at most
four. Hence $G$ has girth at least five.""",
r"""\step{Case 1: $G$ has a cyclic cut of size at most three.} Then
$c(G)\le2^{r-1}+5K_0^{2}\,2^{r/2}$ by Proposition~\ref{prop:threecut}.

\step{Case 2: $G$ has no cyclic cut of size at most three, and it has a cycle of length four.}
Then $G$ is a ring or $c(G)<2^{r-1}$, by Theorem~\ref{thm:fourcut}.

\step{Case 3: $G$ has no cyclic cut of size at most three and no cycle of length four.} Let $Z$
be a cycle with at most three edges. Then at most three edges leave $V(Z)$, and
at most six edges have an end in $V(Z)$. So $G-V(Z)$ has rank at least $r-6>0$, and
$\delta V(Z)$ is a cyclic cut of size at most three. Hence $G$ has girth at least five.""", "cases")
p.write_text(t)
print("proof.tex written")

# ---------------------------------------------------------------- exact-maximum.tex
p = root / "exact-maximum.tex"
t = p.read_text()
t = sub(t, r"""\item A cut with at most four edges divides $G$ into two parts, and a cycle across the cut
consists of paths in the parts. A part with more than half of the possible paths between two
ends, by a fixed margin, is a ladder up to a bounded error, and it has few cycles.
\item So a graph with such a cut is a ring of copies of $K_{2,2}$ and of single edges, or it has
at most $2^{r-1}+O(2^{r/2})$ cycles.""",
r"""\item A cut with at most three edges, or a cycle of length four, divides $G$ into two parts,
and a cycle that meets both parts consists of paths in the parts. A part with more than half of
the possible paths between two ends, by a fixed margin, is a ladder up to a bounded error, and
it has few cycles.
\item So a graph with such a cut or such a cycle is a ring of copies of $K_{2,2}$ and of single
edges, or it has at most $2^{r-1}+O(2^{r/2})$ cycles.""", "front 3-4")
t = sub(t, r"""\item Without such a cut, $G$ has girth at least five, and it has fewer than $2^{r-1}$ cycles:""",
           r"""\item In the other case $G$ has girth at least five, and it has fewer than $2^{r-1}$ cycles:""", "front 6")
p.write_text(t)
print("exact-maximum.tex written")

# ---------------------------------------------------------------- intro.tex
p = root / "sections" / "intro.tex"
t = p.read_text()
t = sub(t, r"""\node[ask, below=of q2] (q3) {Does $G$ have a cyclic cut of four edges?};""",
           r"""\node[ask, below=of q2] (q3) {Does $G$ have a cycle of length four?};""", "figure question")
t = sub(t, r"""In the cases 2 and 3 a cycle consists of paths in the parts of $G$. By the forest estimate,
a part with more than half of the possible paths between two of its ends, by a fixed margin, is a
ladder up to a bounded error, and it has few cycles (Section~\ref{sec:poles}). In the case 3
we also close a part by a small tree, a \emph{cap}, and apply the bound $(\half+o(1))2^{r}$ to
the closed part (Lemma~\ref{lem:cap}).""",
r"""In the cases 1 and 2 a cycle consists of paths in the parts of $G$. By the forest estimate,
a part with more than half of the possible paths between two of its ends, by a fixed margin, is a
ladder up to a bounded error, and it has few cycles (Section~\ref{sec:poles}). In the case 2
we also put a small tree, a \emph{cap}, in the place of the cycle of length four, in two ways,
and apply the bound $(\half+o(1))2^{r}$ to the two graphs that arise (Lemma~\ref{lem:cap}).""", "cases 2 and 3")
t = sub(t, r"""(Lemma~\ref{lem:cap}). In the case 4 the""", r"""(Lemma~\ref{lem:cap}). In the case 3 the""", "case 4 forest")
t = sub(t, r"\subsection{The four cases of the proof}", r"\subsection{The three cases of the proof}", "title cases")
t = sub(t, r"For the upper bound there are four cases (Figure~\ref{fig:plan}).",
           r"For the upper bound there are three cases (Figure~\ref{fig:plan}).", "three cases")
t = sub(t, r"order $r\,2^{r/2}$, so the four bounds give the theorem (Section~\ref{sec:proof}).",
           r"order $r\,2^{r/2}$, so the three bounds give the theorem (Section~\ref{sec:proof}).", "three bounds")
t = sub(t, r"""  \node[ask] (q1) {Does $G$ have a loop?};
  \node[ask, below=of q1] (q2) {Does $G$ have a cyclic cut of at most three edges?};""",
           r"""  \node[ask] (q2) {Does $G$ have a cyclic cut of at most three edges?};""", "figure q1")
t = sub(t, r"""  \node[res, right=13mm of q1] (o1) {at most $2^{r-1}$ cycles\\ \textcolor{slate}{for a trivial reason}};
""", "", "figure o1")
t = sub(t, r"\foreach \a/\b in {q1/o1,q2/o2,q3/o3}", r"\foreach \a/\b in {q2/o2,q3/o3}", "figure arrows 1")
t = sub(t, r"\foreach \a/\b in {q1/q2,q2/q3,q3/o4}", r"\foreach \a/\b in {q2/q3,q3/o4}", "figure arrows 2")
t = sub(t, r"\caption{The four cases for a connected cubic multigraph $G$ of large rank $r$.}",
           r"\caption{The three cases for a connected cubic multigraph $G$ of large rank $r$.}", "figure caption")
t = sub(t, r"""from the proof of Theorem~\ref{thm:fourcut}, and the marked set of Case~4 in""",
           r"""from the proof of Theorem~\ref{thm:fourcut}, and the marked set of Case~3 in""", "marked set")
t = sub(t, r"Case 1 of Section~\ref{sec:proof} (a loop) &", r"Case 1 of Section~\ref{sec:proof}, for a graph with a loop &", "table loop")
t = sub(t, r"Case 2: Proposition~\ref{prop:threecut} with some constant &",
           r"Case 1 for a graph without loops: Proposition~\ref{prop:threecut} with some constant &", "table three cut")
PIECES = "lem:piecesfive" if "lem:piecesfive" in t else "lem:affine"
ALSO = (r"""Fable~5.2 also found the present proof of Theorem~\ref{thm:gap}, which uses
Proposition~\ref{prop:thin} in the place of an induction on the rank, and the form of
Theorem~\ref{thm:fourcut} for a cycle of length four.""" if GAP else
        r"""Fable~5.2 also found the form of
Theorem~\ref{thm:fourcut} for a cycle of length four.""")
t = sub(t, r"""five has few forests (Lemma~\ref{PIECES}). So the argument for bounded girth is not
necessary.""".replace("PIECES", PIECES), r"""five has few forests (Lemma~\ref{PIECES}). So the argument for bounded girth is not
necessary. """.replace("PIECES", PIECES) + ALSO, "origins")
t = sub(t, r"""Equation~\eqref{eq:glue23} and the count of Lemma~\ref{lem:glue4} &""",
           r"""Equation~\eqref{eq:glue23}, and the count of the cycles across a cut of size four &""", "table glue")
if GAP:
    t = sub(t, r"""Theorem~\ref{thm:fewcycles} for $\varepsilon=\frac1{1000}$, with Lemma~\ref{lem:reduction} and Proposition~\ref{prop:thin}; Lemma~\ref{lem:gadgets} &""",
               r"""Theorem~\ref{thm:fewcycles} for $\varepsilon=\frac1{1000}$, with Lemma~\ref{lem:reduction} and Proposition~\ref{prop:thin}; Lemma~\ref{lem:gadgets} with $\frac1{1000}$ in the place of $\varepsilon_0$ &""", "table gadgets")
    t = sub(t, r"""Theorem~\ref{thm:gap} & \lean{EMS.gapStatement}\\""",
               r"""Theorem~\ref{thm:gap} with the constant $\frac1{16}$ & \lean{EMS.gapStatement}\\""", "table gap")
    t = sub(t, r"""Lemma~\ref{lem:cap} & \lean{EMS.Shortening.TreeCapCycleBound.exists_thousandth_bound}\\""",
               r"""Lemma~\ref{lem:cap} with the bound $4.001$ & \lean{EMS.Shortening.TreeCapCycleBound.exists_thousandth_bound}\\""", "table cap")
t = sub(t, r"""Lemma~\ref{lem:star}; Lemma~\ref{lem:rigid} and the cases of Theorem~\ref{thm:fourcut}, as arithmetic &""",
           r"""Lemma~\ref{lem:star}; Lemma~\ref{lem:rigid} and the cases of a cut of size four, as arithmetic &""", "table rigid")
t = sub(t, r"""In Theorem~\ref{thm:fourcut}: the sides have no bridge; four full pairs in both sides give at most $H(r)$ cycles &""",
           r"""For a cyclic cut of size four and no smaller one: the sides have no bridge; four full pairs in both sides give at most $H(r)$ cycles &""", "table bridge")
t = sub(t, r"""Case 3: Theorem~\ref{thm:fourcut} with the rings &""",
           r"""A cyclic cut of size four and no smaller one, which includes Case 2: a ring or fewer than $2^{r-1}$ cycles &""", "table case 3")
t = sub(t, r"""Case 4 for a graph with a cycle shorter than a number $D_*$ &""",
           r"""No cyclic cut of size at most four, and a cycle shorter than a number $D_*$ &""", "table case 4a")
t = sub(t, r"""Case 4 for girth at least $D_*$, with a packing bound""",
           r"""No cyclic cut of size at most four, and girth at least $D_*$, with a packing bound""", "table case 4b")
t = sub(t, r"""paper. A formal proof can differ from the text. In four places the method is different. The""",
           r"""paper. A formal proof can differ from the text. In NUMBER places the method is different. The""".replace("NUMBER", "six" if GAP else "five"), "places")
t = sub(t, r"""estimate in its form for a simple graph, which is in~\cite{Pan}. The formal proofs of
Lemma~\ref{lem:ladders} and
Lemma~\ref{lem:thirdport} use two disjoint paths between the ports and exact numbers of paths in
a capped ladder. The largest difference is in Case~4. The formal proof has a number
$D_*\ge256$ and two cases.""",
(r"""estimate in its form for a simple graph, which is in~\cite{Pan}. The formal proof of
Lemma~\ref{lem:ladders} uses two disjoint paths between the ports and exact numbers of paths in
a capped ladder. The formal proof of Theorem~\ref{thm:gap} is an induction on the rank, with a
lemma on a pole with a third port; it gives the constant $\frac1{16}$, and the formal statements
have $\frac1{1000}$ in the place of $\varepsilon_0$.""" if GAP else
r"""estimate in its form for a simple graph, which is in~\cite{Pan}. The formal proofs of
Lemma~\ref{lem:ladders} and
Lemma~\ref{lem:thirdport} use two disjoint paths between the ports and exact numbers of paths in
a capped ladder.""") + r""" The formal proof treats every cyclic cut of
size four in a graph without a smaller cyclic cut, with a count for two arbitrary sides; the text
needs this for a cycle of length four only. The largest difference is in the last case. The
formal proof assumes that the graph has no cyclic cut of size at most four, and it has a number
$D_*\ge256$ and two cases.""", "differences")
p.write_text(t)
t = sub(t, r"""\begin{idea}{cycles and outside parts}
Let $W$ be a cycle, $e$ an edge of $W$, and $P=V(W)$. For every cycle $C$ through $e$, the even
subgraphs $C$ and $C+W$ have the same outside part, and it is a forest. By
the \emph{forest estimate} (Theorem~\ref{thm:forest}), the outside part is a forest for at most
$\half+o(1)$ of all even subgraphs when $P$ is small. An edge recursion then gives
$\psi(r)\le(\half+o(1))2^{r}$ (Corollary~\ref{cor:cycles}).
\end{idea}""", r"""\begin{idea}{cycles and outside parts}
Let $P$ be a small set of vertices such that $G[P]$ is connected. By the \emph{forest estimate}
(Theorem~\ref{thm:forest}), the outside part is a forest for at most $\half+o(1)$ of all even
subgraphs. So at most $(\half+o(1))2^{r}$ cycles meet $P$. A cycle that avoids $P$ is a cycle of
$G-P$, and if $G$ has no bridge, the rank of $G-P$ is at most $r-1-|P|/2$
(Lemma~\ref{lem:marked}). This gives $\psi(r)\le(\half+o(1))2^{r}$ (Corollary~\ref{cor:cycles}).
\end{idea}""", "idea outside")
t = sub(t, r"""\caption{A cycle $W$ and a cycle $C$ through an edge of $W$. The edges of $C$ with an end on $W$
are dashed. The other edges of $C$ form its outside part for $P=V(W)$, which is a forest. An even
subgraph whose outside part contains a cycle is not a cycle through $W$.}""",
r"""\caption{A cycle $W$ and a cycle $C$ that meets $W$. The edges of $C$ with an end on $W$
are dashed. The other edges of $C$ form its outside part for $P=V(W)$, which is a forest. An even
subgraph whose outside part contains a cycle is not a cycle that meets $W$.}""", "caption outside")
t = sub(t, r"""The parts have these origins. Fable~5.2 found the edge recursion, the localisation and layer
argument,""", r"""The parts have these origins. Fable~5.2 found the localisation and layer
argument,""", "origins recursion")
t = sub(t, r"""Theorem~\ref{thm:fourcut} for a cycle of length four.""",
r"""Theorem~\ref{thm:fourcut} for a cycle of length four. The marked set also gives
Corollary~\ref{cor:cycles} (Lemma~\ref{lem:marked}); the first proof of this corollary was a
recursion over the edges of a shortest cycle, by Fable~5.2.""", "origins marked")
t = sub(t, r"""The formal proof of Corollary~\ref{cor:cycles} uses the forest
estimate in its form for a simple graph, which is in~\cite{Pan}.""",
r"""The formal proof of Corollary~\ref{cor:cycles} uses the forest
estimate in its form for a simple graph, which is in~\cite{Pan}, and a recursion over the edges
of a shortest cycle.""", "difference recursion")
p.write_text(t)
print("intro.tex written")

# ---------------------------------------------------------------- the count with a marked set
p = root / "sections" / "forest.tex"
t = p.read_text()
i = t.index(r"\begin{corollary}[Leading term]\label{cor:cycles}")
t = t[:i] + r"""\begin{lemma}[Cycles and a marked set]\label{lem:marked}
Let $G$ be a connected cubic multigraph of rank $r$ without a bridge. Let $P$ be a set of $p$
vertices, not all vertices of $G$, such that $G[P]$ is connected. Then
\[
  c(G)\;\le\;q(G,P)\,2^{r}+2^{\,r-1-p/2}.
\]
\end{lemma}

\begin{proof}
Let $Z$ be a cycle of $G$ that meets $P$. Its edges in $G-P$ form a proper subset of $Z$, hence a
forest. So at most $q(G,P)\,2^{r}$ cycles meet $P$. The other cycles are cycles of $G-P$, and
there are at most $2^{\beta(G-P)}$ of them. Let $a$ be the number of edges of $G[P]$. Then $3p-2a$
edges leave $P$, and $G-P$ arises from $G$ by the deletion of $p$ vertices and $3p-a$ edges. So
$\beta(G-P)=r-1-2p+a+\comp(G-P)$. The graph $G$ has no bridge, so every component of $G-P$
contains the ends of at least two of the edges that leave $P$. Hence $\comp(G-P)\le(3p-2a)/2$ and
$\beta(G-P)\le r-1-p/2$.
\end{proof}

\begin{corollary}[Leading term]\label{cor:cycles}
There is $r_1$ such that every graph of rank $r\ge r_1$ has at most
$\bigl(\half+21/\lgk3r\bigr)2^{r}$ cycles. Consequently $\psi(r)\sim2^{r-1}$.
\end{corollary}

\begin{proof}
Let $r$ be large, and let $G$ be a connected cubic multigraph of rank $r$ with $\psi(r)$ cycles
(Lemma~\ref{lem:cubic}). Suppose first that $G$ has a bridge $e$, and let $b_1$ and $b_2$ be the
ranks of the two components of $G-e$. A component with $n$ vertices has $(3n-1)/2\ge n$ edges, so
$b_1,b_2\ge1$, and $b_1+b_2=r$. Every cycle lies in one component. So
$c(G)\le(2^{b_1}-1)+(2^{b_2}-1)\le2^{r-1}$.

In the other case choose a set $P$ of $\lceil4\log r\rceil$ vertices such that $G[P]$ is
connected. Then $|P|\le2r/\log^{2}r$. By Theorem~\ref{thm:forest} and Lemma~\ref{lem:marked},
\[
  c(G)\;\le\;\Bigl(\frac12+\frac{20}{\lgk3r}\Bigr)2^{r}+2^{\,r-1-2\log r}
  \;\le\;\Bigl(\frac12+\frac{21}{\lgk3r}\Bigr)2^{r}.
\]
Finally $\psi(r)>2^{r-1}$ for $r\ge3$~\cite{ES}; the rings of Section~\ref{sec:rings} also show this.
\end{proof}
"""
p.write_text(t)
print("forest.tex written")

p = root / "sections" / "tools.tex"
t = p.read_text()
t = sub(t, r"""\item $c(G)$ is the number of cycles of $G$, and $c_e(G)$ is the number of cycles through an edge
$e$. If we replace an edge by a path, the rank and the number of cycles do not change. So""",
r"""\item $c(G)$ is the number of cycles of $G$. If we replace an edge by a path, the rank and the
number of cycles do not change. So""", "notation")
p.write_text(t)
print("tools.tex written")

p = root / "sections" / "proof.tex"
t = p.read_text()
i = t.index(r"Let $Z$ be a cycle of $G$ that meets $P$.")
t = t[:i].rstrip() + r"""
The graph $G$ has no bridge, because a cut of size one is cyclic (Section~\ref{sec:cuts}). So
Lemma~\ref{lem:marked} gives $c(G)<\frac25\,2^{r}+2^{r-5}<2^{r-1}$. \qed
"""
p.write_text(t)
print("proof.tex written again")

p = root / "exact-maximum.tex"
t = p.read_text()
t = sub(t, r"""\item Fix a short cycle $W$ and an edge $e$ of $W$. For a cycle $C$ through $e$, the edges of
$C$ without an end on $W$ form a forest, and the same holds for $C+W$. By the \emph{forest
estimate}, at most $\half+o(1)$ of all even subgraphs have this property, so
$\psi(r)\le(\half+o(1))2^{r}$.""",
r"""\item Fix a small connected set $P$ of vertices. For a cycle that meets $P$, the edges without
an end in $P$ form a forest. By the \emph{forest estimate}, at most $\half+o(1)$ of all even
subgraphs have this property, and few cycles avoid $P$. So $\psi(r)\le(\half+o(1))2^{r}$.""", "front 2")
p.write_text(t)

p = root / "sections" / "poles.tex"
t = p.read_text()
t = sub(t, r"""no path from $s$ to $t$, then $P_{st}(N)\le2^{b-1}$. If a cycle $Z$ of $N$ is disjoint from some
path from $s$ to $t$, and $N-E(Z)$ has $k$ components, then $P_{st}(N)\le2^{b}-2^{b-|Z|+k-1}$.""",
r"""no path from $s$ to $t$, then $P_{st}(N)\le2^{b-1}$. If a cycle $Z$ of $N$ is disjoint from some
path from $s$ to $t$, then $P_{st}(N)\le2^{b}-2^{b-|Z|}$.""", "joins statement")
t = sub(t, r"""$N-E(Z)$. So $N-E(Z)$ has $2^{\beta(N-E(Z))}$ such joins, and $\beta(N-E(Z))=b-|Z|+k-1$. The union""",
r"""$N-E(Z)$. So $N-E(Z)$ has $2^{\beta(N-E(Z))}$ such joins, and $\beta(N-E(Z))\ge b-|Z|$. The union""", "joins proof")
if GAP:
    p.write_text(t)
    print("poles.tex written again")
print("applied")
