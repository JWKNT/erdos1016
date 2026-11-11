"""Exact certificates for the single-cycle/theta/K4 block-method barrier.

Default: verify saved rational inequalities using only the standard library.
--generate: use scipy to find multipliers, then verify each multiplier exactly
before saving it. Solver success alone never certifies an inequality.
"""
import argparse
from fractions import Fraction as F
import itertools
import json
from pathlib import Path

HERE = Path(__file__).resolve().parent
OUTPUT = HERE/'random-host-rank3-barrier-certificates.json'
K4 = [[1,1,0,1,0,0],[1,0,1,0,1,0],[0,1,1,0,0,1],
      [0,0,0,1,1,1],[1,0,1,1,0,1],[1,1,0,0,1,1],[0,1,1,1,1,0]]
THETA = [[1,1,0],[1,0,1],[0,1,1]]
SLOPE = [F(0),F(-1),F(-1,6),F(0)]
CONST = [F(1),F(4,3),F(1,2),F(0)]
LOW = [F(0),F(1,3),F(1),F(2)]
HIGH = [F(1,3),F(1),F(2),None]


def problem(kind, states):
    M = K4 if kind == 'K4' else THETA
    rank = 3 if kind == 'K4' else 2
    size = len(M[0])
    A = [[-1]*size]
    b = [F(-(rank-1))]
    if kind == 'K4':
        for edge in range(size):
            row = [-1]*size
            row[edge] = 0
            A.append(row);b.append(F(-1))
    c = [sum(SLOPE[s]*M[i][j] for i,s in enumerate(states)) for j in range(size)]
    constant = sum(CONST[s] for s in states)
    for i,s in enumerate(states):
        if LOW[s] > 0:
            A.append([-x for x in M[i]]);b.append(-LOW[s])
        if HIGH[s] is not None:
            A.append(M[i][:]);b.append(HIGH[s])
    return A,b,c,constant,rank


def verify(kind, states, sparse):
    A,b,c,constant,rank = problem(kind, states)
    y = [F(0)]*len(A)
    assert len(set(i for i,value in sparse)) == len(sparse)
    for i,value in sparse:
        assert 0 <= i < len(A)
        y[i] = F(value)
    assert min(y) >= 0
    assert all(sum(A[i][j]*y[i] for i in range(len(A))) >= c[j]
               for j in range(len(c))), (kind, states, 'coefficient')
    assert sum(b[i]*y[i] for i in range(len(A)))+constant <= rank, (kind,states,'bound')


def generate():
    import numpy as np
    from scipy.optimize import linprog
    certificate = {}
    for kind,M in [('theta',THETA),('K4',K4)]:
        rows = []
        for states in itertools.product(range(4),repeat=len(M)):
            A,b,c,constant,rank = problem(kind,states)
            AA = np.array(A,dtype=float);bb=np.array(b,dtype=float)
            constraints = np.vstack([-AA.T,bb])
            rhs = np.array([-float(x) for x in c]+[float(rank-constant)])
            result = linprog(np.zeros(len(A)),A_ub=constraints,b_ub=rhs,
                             bounds=(0,None),method='highs')
            assert result.success,(kind,states,result.message)
            sparse = [[i,str(F(float(value)).limit_denominator(100000))]
                      for i,value in enumerate(result.x) if abs(value)>1e-10]
            verify(kind,states,sparse)
            rows.append(sparse)
        certificate[kind]=rows
    OUTPUT.write_text(json.dumps(certificate,separators=(',',':'))+'\n')


def main():
    parser=argparse.ArgumentParser()
    parser.add_argument('--generate',action='store_true')
    args=parser.parse_args()
    if args.generate:generate()
    certificate=json.loads(OUTPUT.read_text())
    counts={}
    for kind,M in [('theta',THETA),('K4',K4)]:
        states=list(itertools.product(range(4),repeat=len(M)))
        rows=certificate[kind]
        assert len(rows)==len(states)
        for state,row in zip(states,rows):verify(kind,state,row)
        counts[kind]=len(rows)
    integral=F(1,3)+F(4,9)+F(1,4)
    assert integral==F(37,36)
    print(json.dumps({'status':'all exact dual inequalities passed',
                      'regions':counts,'integral':str(integral)},indent=2))

if __name__ == '__main__':main()
