#!/usr/bin/env python3
r"""Apply the proof of Lemma 7.6 by slabs to a COPY of the maximum-cycles paper.

Usage:  python3 apply_slabs.py <folder that contains sections/large.tex> [rails]
        python3 apply_slabs.py --emit <folder>     (writes the new text for the note slabs.tex)

The folder is a copy of paper/minimal/exact-maximum in the state of 13 November 2026 (commit
805e2ba, 36 pages), with a copy of paper/minimal/style beside it. The manuscript is not changed
by this script.

Without the second argument (form "slabs"):
  * Lemma 7.5 (rigid sets), its figure and its proof are removed;
  * the proof of Lemma 7.6 (pieces at girth five) shows with slabs that the region of a group of
    layers has no rigid set; it uses Lemma 7.4 (full pairs at girth five) as before;
  * a figure of the slabs is added, and the outline box of Section 7.2 has two steps.

With the argument "rails" (form "slabs and rails"), in addition:
  * Lemma 7.4 is stated for a rigid pair, with the bound 133 d(M), and its proof is the count
    with a shortest path and the fact on seven positions; Lemmas 5.2 and 5.6 are not used in
    Section 7.

Every replacement must match exactly once; the script stops with exit code 1 if one does not.
"""
import sys
from pathlib import Path


def cut(text, start, end, new, what, include_end=False):
    """Replace the block from `start` up to `end` (`end` stays unless include_end)."""
    if text.count(start) != 1:
        sys.exit(f"apply_slabs: start marker of '{what}' occurs {text.count(start)} times")
    i = text.index(start)
    j = text.find(end, i + len(start))
    if j < 0:
        sys.exit(f"apply_slabs: end marker of '{what}' not found")
    if include_end:
        j += len(end)
    return text[:i] + new + text[j:]


def once(text, old, new, what):
    if text.count(old) != 1:
        sys.exit(f"apply_slabs: '{what}' occurs {text.count(old)} times")
    return text.replace(old, new)


IDEA_SLABS = r"""\begin{idea}{outline of Lemmas~\ref{lem:fullfive} and~\ref{lem:piecesfive}}
Lemma~\ref{lem:affine} needs a girth that grows with the number of boundary vertices. For a
bounded number of boundary vertices, girth five is sufficient. Girth four is not sufficient: in
a ladder, the two ends of one rail form a rigid set. The proof has two steps.
\begin{enumerate}[leftmargin=1.5em]
\item A multigraph of girth five with a full pair is small. It consists of capped ladders, and
a capped ladder has many cycles with at most four edges (Lemma~\ref{lem:fullfive}).
\item A large piece with a forest proportion of at least $\frac35$ is thin and long. So it
contains many disjoint parts that are thin and long. Such a part has many disjoint slabs. For
one of the slabs, a rigid set of the part would give a full pair in the slab. So the part has no
rigid set, and each part loses a fixed proportion of the forests
(Lemma~\ref{lem:piecesfive}, Figure~\ref{fig:slabs}).
\end{enumerate}
\end{idea}
"""

IDEA_RAILS = r"""\begin{idea}{outline of Lemmas~\ref{lem:fullfive} and~\ref{lem:piecesfive}}
Lemma~\ref{lem:affine} needs a girth that grows with the number of boundary vertices. For a
bounded number of boundary vertices, girth five is sufficient. Girth four is not sufficient: in
a ladder, the two ends of one rail form a rigid set. The proof has two steps.
\begin{enumerate}[leftmargin=1.5em]
\item A multigraph of girth five with a rigid set of two vertices is small. The vertices
outside a shortest path between the two vertices form a forest, and a path of seven of them
beside the shortest path would close a cycle with at most four edges
(Lemma~\ref{lem:fullfive}).
\item A large piece with a forest proportion of at least $\frac35$ is thin and long. So it
contains many disjoint parts that are thin and long. Such a part has many disjoint slabs. For
one of the slabs, a rigid set of the part would give a rigid set of two vertices in the slab.
So the part has no rigid set, and each part loses a fixed proportion of the forests
(Lemma~\ref{lem:piecesfive}, Figure~\ref{fig:slabs}).
\end{enumerate}
\end{idea}
"""

LEMMA_RAILS = r"""\begin{lemma}[Rigid pairs at girth five]\label{lem:fullfive}
Let $M$ be a connected subcubic multigraph of girth at least five. Let $x\ne y$ be vertices of
degree at most two such that every $\{x,y\}$-join of $M$ is a forest. Then $|V(M)|<133\,d(M)$.
\end{lemma}

\begin{proof}
Put $d=d(M)$. Let $A=a_0a_1\cdots a_\ell$ be a shortest path from $x$ to $y$, and put
$F=M-V(A)$. The edge set of $A$ is an $\{x,y\}$-join, and so is its union with a cycle of $F$. So
$F$ is a forest. A vertex of $F$ has at most one neighbour on $A$: two neighbours $a_i$ and
$a_j$ with $i<j$ give $j-i\le2$, because $A$ is a shortest path, and then a cycle with at most
four edges. For the same reasons an inner vertex of $A$ of degree three has a neighbour in $F$.

Call a vertex of $F$ \emph{plain} if it has degree three and a neighbour $a_p$ with $0<p<\ell$.
A plain vertex has exactly two neighbours in $F$. A vertex of $F$ that is not plain is a
boundary vertex, or it is adjacent to $x$ or $y$, or it has three neighbours in $F$. Let $n_0$,
$n_1$ and $n_3$ be the numbers of these vertices. Then $n_0\le d-2$ and $n_1\le2$, because $x$
and $y$ are boundary vertices. The forest $F$ has at most as many edges as vertices, so a count
of edge ends gives $3n_3+2(|F|-n_0-n_3)\le2|F|$, and $n_3\le2n_0$. So fewer than $3d$ vertices
of $F$ are not plain.

\step{No path of seven plain vertices.} Suppose that $v_0v_1\cdots v_6$ is a path of plain
vertices in $F$, and let $a_{p_k}$ be the neighbour of $v_k$ on $A$. Let $0\le k<l\le6$. Then
$p_k\ne p_l$, because $a_{p_k}$ has three neighbours only. Also $|p_k-p_l|\le l-k+2$, because
$A$ is a shortest path and $a_{p_k}v_k\cdots v_la_{p_l}$ is a path. And $|p_k-p_{k+1}|\ge2$,
because $M$ has no cycle with four edges. Put $s_k=p_{k+1}-p_k$ for $0\le k\le5$. Then $|s_k|$
is $2$ or~$3$, and $0<|s_k+s_{k+1}|\le4$. So two consecutive steps of the same sign are both
$2$ or both $-2$, and of two consecutive steps of different signs one has absolute value $2$
and the other has absolute value~$3$. No three consecutive steps have the same sign, because
$|p_{k+3}-p_k|\le5$.

If consecutive steps always have different signs, then $s_0=s_2=s_4$ and $s_1=s_3=s_5$. Then
$p_5-p_0=3s_0+2s_1=0$ if $|s_0|=2$, and $p_6-p_1=2s_0+3s_1=0$ if $|s_0|=3$. In the other case
let $s_k=s_{k+1}=2\varepsilon$ with $\varepsilon=\pm1$. Where these steps exist,
$s_{k-1}=s_{k+2}=-3\varepsilon$ and $s_{k-2}=s_{k+3}=2\varepsilon$. Then $p_{k-1}=p_{k+4}$ and
$p_{k-2}=p_{k+3}$, so in each of these two pairs one index is outside the range $0,\dots,6$.
This leaves $k=0$ and $k=4$. Let $k=0$; the case $k=4$ is the same with the order reversed. The
first four steps are $2\varepsilon,2\varepsilon,-3\varepsilon,2\varepsilon$. If
$s_4=-3\varepsilon$, then $p_5=p_0$. If $s_4=2\varepsilon$, then $s_5=-3\varepsilon$ and
$p_6=p_1$. So $F$ has no path of seven plain vertices.

\step{The count.} Let $w$ be a vertex of $F$ such that all vertices at distance at most three
from $w$ in $F$ are plain. Then $w$, its two neighbours in $F$, their other neighbours and the
next two vertices form a path of seven plain vertices, because $F$ is a forest. So every vertex
of $F$ is within distance three in $F$ of a vertex that is not plain, and $|F|<22\cdot3d$. An inner vertex of $A$ of
degree three has a neighbour in $F$, and a vertex of $F$ has at most one neighbour on $A$. So
$A$ has at most $|F|+d$ vertices, and $|V(M)|\le2|F|+d<133\,d$.
\end{proof}

"""

FIGURE = r"""\begin{figure}[ht]
\centering
\begin{tikzpicture}[x=1cm,y=1cm]
  \draw[draw=slate!70, fill=black!4, line width=0.6pt, rounded corners=6pt] (0,-1.25) rectangle (13.6,1.25);
  \foreach \a in {1.5,4.2,6.9,9.6} \draw[region] (\a,-0.62) rectangle (\a+1.9,0.95);
  % a branch from the slab B_j back to the first layer
  \draw[edge] (5.0,-0.62) .. controls (4.8,-0.95) and (4.4,-1.0) .. (3.8,-1.0) -- (1.2,-1.0)
    .. controls (0.75,-1.0) and (0.5,-0.85) .. (0.5,-0.55);
  % the path pi
  \draw[hot] (0.5,0) -- (13.1,0);
  \draw[edge] (0.5,0) -- (0.5,0.55) (13.1,0) -- (13.1,0.55) (13.1,0) -- (13.1,-0.55);
  \draw[edge] (7.45,0) -- (7.45,0.6) -- (8.25,0.6) -- (8.25,0);
  \foreach \p in {(5.0,-0.62),(3.8,-1.0),(2.5,-1.0),(1.2,-1.0),(7.45,0.6),(8.25,0.6),(7.45,0),(7.85,0),(8.25,0)}
    \node[vtx] at \p {};
  \foreach \p in {(0.5,0),(13.1,0),(6.55,0),(7.15,0),(8.55,0),(9.15,0)} \node[vtx] at \p {};
  \foreach \p in {(0.5,0.55),(0.5,-0.55),(13.1,0.55),(13.1,-0.55)} \node[port] at \p {};
  \node[note, text=accent] at (7.85,1.5) {the set $B=B_i$};
  \node[note, text=accent] at (5.15,1.5) {$B_j$};
  \node[note, text=accent] at (6.5,-0.3) {$s$};
  \node[note, text=accent] at (7.15,-0.3) {$x$};
  \node[note, text=accent] at (8.55,-0.3) {$y$};
  \node[note, text=accent] at (9.2,-0.3) {$t$};
  \node[note, text=warm] at (3.0,0.28) {$\pi$};
  \node[note, text=accent] at (0.22,-0.55) {$u$};
  \node[note] at (3.3,-1.55) {the component $K^{-}$ of $M-B$};
  \node[note] at (11.4,-1.55) {the component $K^{+}$ of $M-B$};
\end{tikzpicture}
\caption{The proof of Lemma~\ref{lem:piecesfive}. The part $M$ with the path $\pi$ (thick), four
of its slabs, and the vertices of $U$ (circles) in the first and in the last layer. The vertex
$u$ is in a side component of $M-B_j$; for the slab $B$ it is in $K^{-}$. If $K^{-}\ne K^{+}$
and each of them contains an odd number of vertices of $U$, then a $U$-join of $M$ meets $M[B]$
in an $\{x,y\}$-join.}
\label{fig:slabs}
\end{figure}

"""


def proof_pieces(tau_text, lemma_use):
    return r"""\begin{proof}
Put $W=B(k+1)^{2}$, """ + tau_text + r""", $h=2W\tau+2$ and $F_0(k)=Wh\,(k+2^{Wh}+2)$. Suppose that some
even set $T$ of boundary vertices has forest proportion at least $\frac35$. If $T$ is empty, then
$N$ has no cycle and fewer than $2k$ vertices. In the other case fix a boundary vertex $o$, and
define the layers as in the proof of Lemma~\ref{lem:affine}. The step ``A marker'' of that proof
uses no girth, and it shows that each layer has fewer than $W$ vertices. So $N$ has at least
$h\,(k+2^{Wh}+2)$ layers. Divide the layers $1,2,\dots$ into groups of $h$ consecutive layers. At
least $2^{Wh}$ groups contain no boundary vertex. In such a group let $M$ be a component of the
subgraph induced by the group that has a vertex $v$ in the last layer of the group. A shortest
path from $o$ to $v$ has one vertex in each layer of the group; let $\pi_j$ be its vertex in the
$j$th of these layers. The path $\pi=\pi_1\cdots\pi_h$ lies in $M$. The vertices of $M$ have
degree three in $N$, and an edge that leaves $M$ starts in the first or in the last layer of the
group. So the boundary vertices of $M$ are in these two layers, there are fewer than $2W$ of
them, and the rank of $M$ is less than $Wh$. We show that no even set of boundary vertices of
$M$ is rigid (Figure~\ref{fig:slabs}).

\step{Slabs.} For $1\le i\le2W$, the $i$th \emph{slab} consists of the layers
$2+(i-1)\tau,\dots,1+i\tau$ of the group. Let $B_i$ be the vertex set of the component of the
subgraph of $M$ induced by this slab that contains the $\tau$ vertices of $\pi$ in the slab. Let
$s_ix_i$ be the edge of $\pi$ that enters $B_i$ and $y_it_i$ the edge that leaves it, with
$x_i,y_i\in B_i$. The vertices of $B_i$ have degree three in $M$, and an edge of $M$ that leaves
$B_i$ starts in the first or in the last layer of the slab. So $d(M[B_i])<4W\le|B_i|$. Hence
$M[B_i]$ has a cycle, by~\eqref{eq:deficit}, and $x_i\ne y_i$ are boundary vertices of
$M[B_i]$. Call a component of $M-B_i$ a \emph{side component} if it contains neither $s_i$ nor
$t_i$. The vertices of $\pi$ outside $B_i$ are joined to $s_i$ or to $t_i$ in $\pi-B_i$. A set
$B_j$ with $j\ne i$ is connected, avoids $B_i$ and contains a vertex of $\pi$. So a side
component of $M-B_i$ meets no set $B_j$.

\step{Side components.} Let $K$ be a side component of $M-B_i$, and let $j\ne i$. Some
vertex of $K$ has a neighbour in $B_i$, because $M$ is connected. So $K\cup B_i$ is connected,
avoids $B_j$ and contains a vertex of $\pi$. Hence it lies in the component of $s_j$ or of
$t_j$ in $M-B_j$. So a vertex of $M$ is in a side component of $M-B_i$ for at most one~$i$.

\step{No rigid set.} Let $U$ be an even set of boundary vertices of $M$. It has fewer than $2W$
vertices, and none of them is in a slab. So there is an $i$ such that no vertex of $U$ is in a
side component of $M-B_i$. Write $B$, $s$, $x$, $y$, $t$ for $B_i$, $s_i$, $x_i$, $y_i$, $t_i$,
and let $K^{-}$ and $K^{+}$ be the components of $M-B$ that contain $s$ and $t$. Every vertex
of $U$ is in one of them. Put $U^{-}=U\cap V(K^{-})$. Suppose first that $K^{-}=K^{+}$ or that
$|U^{-}|$ is even. Then $M-B$ contains a $U$-join, and its union with a cycle of $M[B]$ is a
$U$-join that is not a forest. Suppose now that $K^{-}\ne K^{+}$ and that $|U^{-}|$ is odd, and
let $J$ be an $\{x,y\}$-join of $M[B]$. Add the edges $sx$ and $ty$, a join of $K^{-}$ for the
set $U^{-}$ with $s$ added or removed, and a join of $K^{+}$ for the set $U\sm U^{-}$ with $t$
added or removed. The result is a $U$-join of $M$. """ + lemma_use + r"""

So each even set of boundary vertices of $M$ has forest proportion at most $1-2^{-Wh}$. By
Lemma~\ref{lem:product}, the forest proportion of $T$ is at most
$(1-2^{-Wh})^{2^{Wh}}<\half$. This is a contradiction.
\end{proof}
"""


USE_FULL = (r"If $U$ is rigid, then $J$ is a forest, and hence a path. Then"
            "\n"
            r"Lemma~\ref{lem:fullfive} gives $|B|<15\,d(M[B])<60\,W=\tau$, and this is false.")
USE_RIGID = (r"If $U$ is rigid, then $J$ is a forest. Then"
             "\n"
             r"Lemma~\ref{lem:fullfive} gives $|B|<133\,d(M[B])<532\,W=\tau$, and this is false.")


def emit(folder):
    """Write the new text with the numbers of the present paper in the place of references."""
    numbers = {r"Lemma~\ref{lem:affine}": "Lemma~7.2", r"Lemma~\ref{lem:product}": "Lemma~7.3",
               r"Lemma~\ref{lem:fullfive}": "Lemma~7.4", r"Lemma~\ref{lem:piecesfive}": "Lemma~7.6",
               r"by~\eqref{eq:deficit}": "by~(7.1)"}

    def plain(text):
        for old, new in numbers.items():
            text = text.replace(old, new)
        for left in (r"\ref{lem:", r"\eqref{eq:"):
            if left in text:
                sys.exit("apply_slabs: a reference to the paper is left in the text for the note")
        return text

    out = Path(folder)
    (out / "slabs-figure.tex").write_text(plain(FIGURE))
    (out / "slabs-proof.tex").write_text(plain(proof_pieces(r"$\tau=60\,W$", USE_FULL)))
    rails = LEMMA_RAILS.replace(r"\label{lem:fullfive}", "")
    i = rails.index(r"\begin{proof}")
    (out / "slabs-rails-proof.tex").write_text(plain(rails[i:]))
    print("apply_slabs: wrote slabs-figure.tex, slabs-proof.tex, slabs-rails-proof.tex")


def main():
    if len(sys.argv) == 3 and sys.argv[1] == "--emit":
        emit(sys.argv[2])
        return
    if len(sys.argv) not in (2, 3) or (len(sys.argv) == 3 and sys.argv[2] != "rails"):
        sys.exit(__doc__)
    rails = len(sys.argv) == 3
    root = Path(sys.argv[1])
    large = root / "sections" / "large.tex"
    intro = root / "sections" / "intro.tex"
    t = large.read_text()

    # the outline box of Section 7.2
    t = cut(t, r"\begin{idea}{outline of Lemmas~\ref{lem:fullfive}, \ref{lem:rigidpiece} and~\ref{lem:piecesfive}}",
            "\\end{idea}\n", IDEA_RAILS if rails else IDEA_SLABS, "outline box", include_end=True)
    # Lemma 7.4
    if rails:
        t = cut(t, r"\begin{lemma}[Full pairs at girth five]\label{lem:fullfive}",
                r"\begin{lemma}[Rigid sets]\label{lem:rigidpiece}", LEMMA_RAILS, "Lemma 7.4")
        t = once(t, "many boundary vertices this needs that the part contains no short cycle\n"
                 "(Section~\\ref{sec:affine}). For a part with few boundary vertices it needs girth five only,\n"
                 "because a ladder has cycles of length four (Section~\\ref{sec:girthfive}). The parts",
                 "many boundary vertices this needs that the part contains no short cycle\n"
                 "(Section~\\ref{sec:affine}). For a part with few boundary vertices it needs girth five only\n"
                 "(Section~\\ref{sec:girthfive}). The parts", "outline of Section 7")
    # Lemma 7.5 with its figure and proof
    t = cut(t, r"\begin{lemma}[Rigid sets]\label{lem:rigidpiece}",
            r"\begin{lemma}[Pieces at girth five]\label{lem:piecesfive}", "", "Lemma 7.5")
    # the proof of Lemma 7.6, with the figure before it
    start = "\\begin{proof}\nPut $W=B(k+1)^{2}$, $h=10^{4}\\,W^{3}$"
    new_proof = proof_pieces(r"$\tau=532\,W$" if rails else r"$\tau=60\,W$",
                             USE_RIGID if rails else USE_FULL)
    t = cut(t, start, "\\end{proof}\n", FIGURE + new_proof, "proof of Lemma 7.6", include_end=True)
    for gone in ("lem:rigidpiece", "fig:rigid}"):
        if gone in t:
            sys.exit(f"apply_slabs: a reference to {gone} is left")
    large.write_text(t)

    # the sentence on the formal proof in Section 1.4
    s = intro.read_text()
    old = ("Theorem~\\ref{thm:half} at girth five. Some of its steps are not those of the text: a cut of\n"
           "size four has two arbitrary sides, Lemma~\\ref{lem:piecesfive} has a proof without rigid sets,\n"
           "and the end of the proof of Theorem~\\ref{thm:half} uses short cycles at many scales. So the\n"
           "kernel check\n")
    if rails:
        new = ("Theorem~\\ref{thm:half} at girth five. Some of its steps are not those of the text: a cut of\n"
               "size four has two arbitrary sides, and the end of the proof of Theorem~\\ref{thm:half} uses\n"
               "short cycles at many scales. So the kernel check\n")
    else:
        new = ("Theorem~\\ref{thm:half} at girth five. Some of its steps are not those of the text: a cut of\n"
               "size four has two arbitrary sides, Lemma~\\ref{lem:fullfive} has a proof without ladders,\n"
               "and the end of the proof of Theorem~\\ref{thm:half} uses short cycles at many scales. So the\n"
               "kernel check\n")
    s = once(s, old, new, "sentence on the formal proof")
    intro.write_text(s)
    print("apply_slabs: applied the form", "'slabs and rails'" if rails else "'slabs'")


if __name__ == "__main__":
    main()
