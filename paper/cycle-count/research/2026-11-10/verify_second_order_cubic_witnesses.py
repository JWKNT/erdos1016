"""Independent path and cycle DFS checks for the exact cubic catalogue maxima.

The catalogue enumerator uses binary cycle-space states in C++.
This verifier uses Fable's independent vertex-path DFS and cycle DFS.
The graph6 parser comes from the separate exponential-cut checker.
"""
import json
from pathlib import Path

from check_exponential_small_cuts import graph6_edges
from fable_check_blocking import cycles_of
from fable_check_tools import count_paths


def main():
    data = json.loads(Path('second-order-cubic-catalog-results.json').read_text())
    checked = []
    for record in data:
        entry = {'order': record['order'], 'checks': []}
        for key in ['max_cycles_graph6', 'max_min_edge_graph6', 'nonfull_graph6']:
            encoded = record[key]
            if not encoded:
                continue
            n, edges = graph6_edges(encoded.encode('ascii'))
            cycles = cycles_of(n, edges)
            frequency = [sum((edge_mask >> i) & 1 for _, edge_mask in cycles)
                         for i in range(len(edges))]
            for i, (u, v) in enumerate(edges):
                paths = count_paths(n, edges[:i] + edges[i + 1:], u, v)
                assert paths == frequency[i], (n, key, i, paths, frequency[i])
            if key == 'max_cycles_graph6':
                assert len(cycles) == record['max_cycles']
            elif key == 'max_min_edge_graph6':
                assert min(frequency) == record['max_min_edge_count']
            else:
                # Different graph6 parsers may order the edges differently.
                nonfull = [x for x in frequency if x < record['nonfull_denominator']]
                assert max(nonfull) == record['max_nonfull_edge_count']
                assert 16 * max(nonfull) <= 15 * record['nonfull_denominator']
            entry['checks'].append({'kind': key, 'cycles': len(cycles),
                                    'edge_path_checks': len(edges)})
        checked.append(entry)
    Path('second-order-cubic-witness-audit.json').write_text(json.dumps(checked, indent=2) + '\n')
    print(json.dumps({'orders': len(checked),
                      'witnesses': sum(len(x['checks']) for x in checked),
                      'edge_path_checks': sum(y['edge_path_checks'] for x in checked for y in x['checks'])}))


if __name__ == '__main__':
    main()
