#!/usr/bin/env python3
"""Explore two disjoint fractional triangle covers on five vertices.

This numerical search is exploratory.  It does not certify a graph theorem.
"""

import json
from itertools import combinations
from pathlib import Path


def main():
    import networkx as nx
    import numpy as np
    from scipy.optimize import Bounds, LinearConstraint, milp

    records = []
    for graph in nx.graph_atlas_g():
        if len(graph) != 5:
            continue
        edges = list(graph.edges())
        count = len(edges)
        if not count:
            records.append({"edges": [], "minimum": 0, "claimed_lower": -10})
            continue
        edge_id = {tuple(sorted(edge)): index for index, edge in enumerate(edges)}
        rows, lower, upper = [], [], []

        def constraint(values, lo, hi):
            row = np.zeros(3 * count)
            for index, value in values.items():
                row[index] = value
            rows.append(row)
            lower.append(lo)
            upper.append(hi)

        for index in range(count):
            constraint({index: 1, 2 * count + index: -1}, -np.inf, 0)
            constraint({count + index: 1, 2 * count + index: 1}, -np.inf, 1)
        triangles = []
        for vertices in combinations(range(5), 3):
            pairs = [tuple(sorted(pair)) for pair in combinations(vertices, 2)]
            if not all(pair in edge_id for pair in pairs):
                continue
            triangle = [edge_id[pair] for pair in pairs]
            triangles.append(triangle)
            constraint({index: 1 for index in triangle}, 1, np.inf)
            constraint({count + index: 1 for index in triangle}, 1, np.inf)
        cost = np.zeros(3 * count)
        cost[:2 * count] = 1
        integer = np.zeros(3 * count)
        integer[2 * count:] = 1
        result = milp(cost, integrality=integer, bounds=Bounds(0, 1),
                      constraints=LinearConstraint(np.array(rows), lower, upper),
                      options={"mip_rel_gap": 0})
        if not result.success:
            raise RuntimeError((edges, result.message))
        records.append({
            "edges": edges,
            "triangles": triangles,
            "minimum": float(result.fun),
            "claimed_lower": 2 * count - 10,
            "x": result.x[:count].tolist(),
            "y": result.x[count:2 * count].tolist(),
        })

    path = Path(__file__).with_name("path-six-seven-local-star-results.json")
    path.write_text(json.dumps(records, indent=2) + "\n")
    print(json.dumps({
        "graphs": len(records),
        "minimum_margin": min(r["minimum"] - r["claimed_lower"] for r in records),
        "min_by_edges": {
            str(m): min(r["minimum"] for r in records if len(r["edges"]) == m)
            for m in range(11)
        },
        "counterexamples": [r for r in records if r["minimum"] < r["claimed_lower"] - 1e-7],
    }, indent=2))


if __name__ == "__main__":
    main()
