"""Check the integer formulas in k4-random-host-blocks.tex."""
from itertools import combinations
from pathlib import Path
import json

EDGES = [(0,1),(0,2),(0,3),(1,2),(1,3),(2,3)]
CYCLES = [(0,1,3),(0,2,4),(1,2,5),(3,4,5),
          (0,2,3,5),(0,1,4,5),(1,2,3,4)]


def lengths(n, t, kind):
    if kind == 'A':
        return [8*n-2*t+3, 1, n-t+3, 2*n+2*t+3, n+t+3, 3*n-t+3]
    return [1, n-t+2, n-t+3, 3*n-t+3, 3*n+3*t+3, 6*n+3]


def hamilton_check(weights, kind):
    paths, edge_set, vertex_count = [], set(), 4
    for (u,v), length in zip(EDGES, weights):
        inner = list(range(vertex_count, vertex_count+length-1))
        vertex_count += length-1
        path = [u]+inner+[v]
        paths.append(path)
        edge_set.update(tuple(sorted(pair)) for pair in zip(path,path[1:]))
    if kind == 'A':
        omitted = [(0,2), (paths[0][-2],1), (paths[5][-2],3)]
    else:
        omitted = [(0,1), (paths[1][-2],2), (paths[4][-2],3)]
    for edge in omitted:
        edge_set.remove(tuple(sorted(edge)))
    adjacency = [[] for _ in range(vertex_count)]
    for u,v in edge_set:
        adjacency[u].append(v);adjacency[v].append(u)
    assert sum(len(neighbors)==1 for neighbors in adjacency) == 2
    assert all(len(neighbors) in (1,2) for neighbors in adjacency)
    seen = {0};stack=[0]
    while stack:
        for v in adjacency[stack.pop()]:
            if v not in seen:seen.add(v);stack.append(v)
    assert len(seen)==vertex_count
    assert len(edge_set)==vertex_count-1


def main():
    metric_cases = hamilton_cases = 0
    for n in range(1,101):
        covered = set()
        total_vertices = 0
        for t in range(n+1):
            for kind in 'AB':
                w = lengths(n,t,kind)
                assert min(w)>0
                cc = [sum(w[e] for e in cyc) for cyc in CYCLES]
                covered.update(cc)
                assert min(cc)>=2*n+6
                assert sum(w)>=14*n+15
                assert sum(w)-max(w)>=7*n+13
                assert sum(w)-2<=15*n+14
                total_vertices += sum(w)-2
                metric_cases += 1
                if n<=8:
                    hamilton_check(w,kind);hamilton_cases+=1
        missing = set(range(2*n+6,14*n+11))-covered
        assert missing <= {4*n+8},(n,missing)
        singles = list(range(3,2*n+6))+[4*n+8]
        covered.update(singles)
        assert set(range(3,14*n+11))<=covered
        assert 6*(n+1)+len(singles)==8*n+10
        total_vertices += sum(singles)
        assert 2*total_vertices == 61*n*n+141*n+94
    result={'status':'all checks passed','N_values':[1,100],
            'metric_cases':metric_cases,'explicit_Hamilton_path_cases':hamilton_cases}
    Path(__file__).with_name('k4-random-host-blocks-results.json').write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps(result,indent=2))

if __name__ == '__main__':main()
