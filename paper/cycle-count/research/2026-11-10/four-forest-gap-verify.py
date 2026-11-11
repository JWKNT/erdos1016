#!/usr/bin/env python3
"""Independent exact audit of switch-search witnesses; no optimization claims."""
import json
from pathlib import Path
from check_second_order_four_terminal_forests import enumerate_joins, attach_diamond

FOLDER = Path(__file__).resolve().parent


def main():
    checks = []
    best = None
    for rank in (8, 10, 12):
        source = FOLDER / f'four-forest-gap-switch-rank{rank}.jsonl'
        for row in map(json.loads, source.read_text().splitlines()):
            if 'edges' not in row:
                continue
            n, edges, terminals = row['vertices'], row['edges'], row['terminals']
            degree = [0] * n
            assert len({tuple(sorted(e)) for e in edges}) == len(edges)
            for u, v in edges:
                assert u != v
                degree[u] += 1
                degree[v] += 1
            assert all(degree[v] == (2 if v in terminals else 3) for v in range(n))
            forests, examples = enumerate_joins(n, edges, terminals)
            assert 2**rank - forests == row['bad']
            checks.append(dict(rank=rank, forests=forests, total=2**rank,
                               bad=row['bad'], bad_examples=examples))
            if rank == 8 and row['bad'] == 1:
                best = row
    assert best is not None
    n, edges, terminals = best['vertices'], best['edges'], best['terminals']
    seed = [f'{n} {len(edges)} {len(terminals)}', ' '.join(map(str, terminals))]
    seed += [' '.join(map(str, e)) for e in edges]
    (FOLDER / 'four-forest-gap-rank8-seed.txt').write_text('\n'.join(seed)+'\n')
    extensions = []
    for _ in range(3):
        n, edges, terminals = attach_diamond(n, edges, terminals)
        rank = len(edges)-n+1
        forests, _ = enumerate_joins(n, edges, terminals)
        assert 256*forests == 255*2**rank
        extensions.append(dict(rank=rank, forests=forests, total=2**rank))
    result = dict(status='All exact checks passed', scope='Witnesses only; no uniform gap proved',
                  switch_witness_checks=checks, constant_density_extensions=extensions)
    (FOLDER / 'four-forest-gap-independent-checks.json').write_text(json.dumps(result, indent=2)+'\n')
    print(json.dumps(dict(status=result['status'], witnesses=len(checks), best_density='255/256')))


if __name__ == '__main__':
    main()
