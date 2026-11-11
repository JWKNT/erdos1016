"""Complete small-core certificate for the four-regular theorem.

Run after building geng 2.8.9 and check_four_regular_finite.cpp.
This runner uses no analytic upper-bound file: every instance is counted
both by the C++ path enumeration and by an independent binary cycle space.
"""
import argparse
import hashlib
import json
from pathlib import Path
import subprocess
import time

from run_four_regular_finite import graph6, matchings, cycle_space_histogram

HERE = Path(__file__).resolve().parent


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('--geng', default='/tmp/nauty2_8_9/geng')
    ap.add_argument('--checker', default='/tmp/check_four_regular_finite')
    ap.add_argument('--max-n', type=int, default=10)
    ap.add_argument('--output', type=Path, default=HERE/'four-regular-theorem-certificate.json')
    args = ap.parse_args()
    start = time.time()
    report = {'status': 'in progress', 'nauty_version': '2.8.9',
              'nauty_source_url': 'https://pallini.di.uniroma1.it/nauty2_8_9.tar.gz',
              'nauty_archive_sha256': 'c97ab42bf48796a86a598bce3e9269047ca2b32c14fc23e07208a244fe52c4ee',
              'max_n': args.max_n, 'classes': [], 'source_sha256': {}}
    for p in [Path(args.geng), Path(args.checker), Path(__file__),
              HERE/'check_four_regular_finite.cpp', HERE/'run_four_regular_finite.py']:
        report['source_sha256'][p.name] = hashlib.sha256(p.read_bytes()).hexdigest()
    instances = 0
    for n in range(4, args.max_n + 1):
        for k in range(3):
            if 2*n-k > n*(n-1)//2:
                continue
            cmd = [args.geng, '-c', '-d3', '-D4', str(n), str(2*n-k)]
            generated = subprocess.run(cmd, capture_output=True, check=True)
            counted = subprocess.run([args.checker, '-', '--emit'], input=generated.stdout,
                                     capture_output=True, check=True)
            row = json.loads(counted.stdout)
            assert (row['n'], row['k']) == (n, k)
            checked = 0
            maximum = 0
            above_half = []
            equality = []
            for line in counted.stderr.decode().splitlines():
                tag, g6, mi, *counts = line.split()
                assert tag == 'CHECK'
                nn, edges = graph6(g6)
                pairs = matchings(nn, edges)[int(mi)]
                actual = cycle_space_histogram(nn, edges + pairs)
                assert actual == list(map(int, counts)), (g6, pairs, actual, counts)
                total = sum(actual)
                assert total <= 2**n+n, (g6, pairs, total)
                maximum = max(maximum, total)
                specimen = {'graph6': g6, 'doubled_pairs': pairs,
                            'cycles': total, 'cycles_by_length_2_to_n': actual}
                if total > 2**n:
                    assert (n,k) in [(4,2),(5,0)], specimen
                    above_half.append(specimen)
                if total == 2**n+n:
                    assert (n,k) == (5,0), specimen
                    equality.append(specimen)
                checked += 1
            assert checked == row['multigraph_instances'] == row['full_cycle_counts']
            assert maximum == row['maximum_full_count']
            row.update({'independent_cycle_space_checks': checked,
                        'above_half_instances': above_half, 'equality_instances': equality,
                        'generator_command': cmd,
                        'generator_report': generated.stderr.decode(),
                        'graph6_stream_sha256': hashlib.sha256(generated.stdout).hexdigest()})
            report['classes'].append(row)
            instances += checked
            args.output.write_text(json.dumps(report, indent=2)+'\n')
    report.update({'status': 'all exact counts agree; bound and exception classification passed',
                   'total_instances': instances,
                   'total_underlying_graphs': sum(r['underlying_graphs'] for r in report['classes']),
                   'total_seconds': time.time()-start})
    args.output.write_text(json.dumps(report, indent=2)+'\n')
    print(json.dumps({k:v for k,v in report.items() if k not in ['classes','source_sha256']}, indent=2))


if __name__ == '__main__':
    main()
