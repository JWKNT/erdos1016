"""Exact terminal-path means from cubic cycle spaces; exploratory checks only."""

import json
import subprocess
from pathlib import Path

import networkx as nx


def cycle_masks(graph):
    edges = sorted(tuple(sorted(e)) for e in graph.edges())
    index = {e: i for i, e in enumerate(edges)}
    basis = []
    for cyc in nx.cycle_basis(graph):
        mask = 0
        for a, b in zip(cyc, cyc[1:] + cyc[:1]):
            mask ^= 1 << index[tuple(sorted((a, b)))]
        basis.append(mask)
    mask = 0
    for i in range(1, 1 << len(basis)):
        mask ^= basis[(i & -i).bit_length() - 1]
        chosen = [edges[j] for j in range(len(edges)) if mask >> j & 1]
        adjacency = {}
        for a, b in chosen:
            adjacency.setdefault(a, []).append(b)
            adjacency.setdefault(b, []).append(a)
        if any(len(v) != 2 for v in adjacency.values()):
            continue
        seen, stack = set(), [next(iter(adjacency))]
        while stack:
            v = stack.pop()
            if v in seen:
                continue
            seen.add(v)
            stack.extend(adjacency[v])
        if len(seen) == len(adjacency):
            yield adjacency, len(chosen)


def main():
    output = {"graphs_checked": 0, "first_pair_failure": None,
              "first_all_pair_failure": None, "records": []}
    for n in [10, 12, 14, 16, 18]:
        command = ["/tmp/nauty2_8_9/geng", "-q", "-c", "-t", "-f",
                   "-d3", "-D3", str(n)]
        data = subprocess.check_output(command).splitlines()
        for encoded in data:
            graph = nx.from_graph6_bytes(encoded)
            if nx.edge_connectivity(graph) < 3:
                continue
            output["graphs_checked"] += 1
            counts = {v: {} for v in graph}
            cycle_count = length_sum = 0
            for adjacency, length in cycle_masks(graph):
                cycle_count += 1
                length_sum += length
                for v, neighbors in adjacency.items():
                    pair = tuple(sorted(neighbors))
                    c, total = counts[v].get(pair, (0, 0))
                    counts[v][pair] = c + 1, total + length - 2
            for v in graph:
                failures = [list(pair) for pair, (c, total) in counts[v].items()
                            if 4 * total > (3 * n - 7) * c]
                record = {"graph6": encoded.decode(), "n": n, "deleted": v,
                          "edges": sorted([list(e) for e in graph.edges()]),
                          "path_counts_and_lengths": [
                              {"pair": list(pair), "count": c, "length_sum": total,
                               "fourfold_excess": 4 * total - (3 * n - 7) * c}
                              for pair, (c, total) in sorted(counts[v].items())],
                          "cycle_count": cycle_count, "cycle_length_sum": length_sum}
                if failures and output["first_pair_failure"] is None:
                    output["first_pair_failure"] = record
                    print("First pair failure", json.dumps(record), flush=True)
                if len(failures) == 3 and output["first_all_pair_failure"] is None:
                    output["first_all_pair_failure"] = record
                    print("First all-pair failure", json.dumps(record), flush=True)
            output["records"].append({"n": n, "graph6": encoded.decode(),
                                      "cycle_count": cycle_count,
                                      "cycle_length_sum": length_sum})
        print("Completed", n, "graphs checked", output["graphs_checked"], flush=True)
        Path(__file__).with_suffix(".json").write_text(json.dumps(output, indent=2) + "\n")


if __name__ == "__main__":
    main()
