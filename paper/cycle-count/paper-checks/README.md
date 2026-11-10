# Tests on small graphs

These scripts test statements of `../pancyclic-paper.tex` on small graphs.
A passed test is evidence. It is not a proof.
Appendix B of the paper describes each test.

Run a script from this directory:

```sh
python3 check_chords.py
```

`check_nb.py` and `check_nb2.py` need NumPy and use floating point.
All other scripts use exact integer or rational arithmetic.
`lib.py` contains the shared graph functions.

| Script | Statement in the paper | Last line of output (10 November 2026) | Time |
|---|---|---|---|
| `check_examples.py` | The examples in Sections 2, 3 and 7 | `all assertions passed` | under 1 s |
| `check_chords.py` | Section 3: Lemmas 3.1 and 3.2 and the chord construction | `cases 857 - all assertions passed` | under 1 s |
| `check_counting.py` | Lemma 2.1, Proposition 7.2 | `tests 4000 nowaste 2027 viol 0` | 1 s |
| `nowaste_exh.py` | Proposition 7.2, exhaustive, 5 and 6 vertices | largest value 1 (triangle), 0 (four-cycle) | under 1 s |
| `nowaste_exh2.py` | Proposition 7.2, exhaustive, 7 and 8 vertices | `n 8 ... nowaste 0` | 4 min |
| `check_construction.py` | Proposition 5.1 | `checked 148 values of n; failures 0 ; max (chords - bound) = 0` | 3 s |
| `check_links.py` | Lemmas 6.2 and 6.3 | `pairs tested 5221 violations 0 ...` | under 1 s |
| `check_nb.py` | Lemmas 6.6 and 6.7 | `graphs tested 292 violations 0 ...` | 1 s |
| `check_nb2.py` | Lemma 6.6 on three cages | three lines, each ratio at most 1 | under 1 s |

`check_construction.py` lists 148 values of `n`, of which 145 are distinct.
`check_claim.py` tests a claim that only the first draft (`../drafts/pancyclic-paper-v1.tex`, Section 5) uses.
`check_defect.py` tests Proposition 7.4 of the second draft (`../drafts/pancyclic-paper-v2.tex`).
The current paper does not contain these statements.
