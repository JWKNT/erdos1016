"""Independent finite checks for the analytic prism-blocker criterion."""
import itertools
import json
from pathlib import Path


def matchings(vertices):
    if not vertices:
        yield ()
        return
    a = vertices[0]
    for b in vertices[1:]:
        for rest in matchings(tuple(v for v in vertices[1:] if v != b)):
            yield ((a, b),) + rest


def main():
    vertices = tuple(range(6))
    edges = list(itertools.combinations(vertices, 2))
    edge_index = {e: i for i, e in enumerate(edges)}
    matching_masks = [sum(1 << edge_index[e] for e in M)
                      for M in matchings(vertices)]
    prisms = set()
    for beta, gamma in itertools.combinations(matching_masks, 2):
        if not beta & gamma:
            prisms.add(tuple(M for M in matching_masks
                             if not M & (beta | gamma)))
    assert len(prisms) == 60 and all(len(P) == 4 for P in prisms)
    partitions = []
    for left in itertools.combinations(vertices, 3):
        if 0 not in left:
            continue
        cross = sum(1 << i for i, (u, v) in enumerate(edges)
                    if (u in left) != (v in left))
        partitions.append(cross)
    bad = []
    for D in range(1 << 15):
        blocks_prism = any(all(D & M for M in P) for P in prisms)
        crosses_all = all(D & cut for cut in partitions)
        assert blocks_prism == crosses_all
        if not blocks_prism:
            bad.append(D)
    bad_set = set(bad)
    maximal_bad = [D for D in bad
                   if all((D | (1 << e)) not in bad_set
                          for e in range(15) if not (D >> e) & 1)]
    all_edges = (1 << 15) - 1
    assert set(maximal_bad) == {all_edges ^ cut for cut in partitions}
    output = {
        "status": "PASS",
        "edge_subsets_checked": 1 << 15,
        "distinct_prisms": len(prisms),
        "balanced_partitions": len(partitions),
        "nonblocking_subsets": len(bad),
        "maximal_nonblocking_subsets": len(maximal_bad),
        "maximal_nonblocking_shape": "two disjoint triangles",
    }
    Path(__file__).with_name("random-seven-prism-blocker-checks.json").write_text(
        json.dumps(output, indent=2) + "\n")
    print(json.dumps(output))


if __name__ == "__main__":
    main()
