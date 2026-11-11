#!/usr/bin/env python3
"""Exact six-matching blocker audit for the critical seven-shore relaxation."""
import itertools
import json
from pathlib import Path
from random_seven_cycle_dual import matchings


def main():
    vertices=tuple(range(6))
    all_pairs=tuple(itertools.combinations(vertices,2))
    all_matchings=tuple(matchings(vertices))
    checks=0
    blocker_types={}
    for beta in all_matchings:
        for gamma in all_matchings:
            if not set(beta).isdisjoint(gamma):
                continue
            common=[alpha for alpha in all_matchings
                    if set(alpha).isdisjoint(beta) and set(alpha).isdisjoint(gamma)]
            assert len(common)==4
            assert len(set().union(*map(set,common)))==9
            assert all(any(set(pair).isdisjoint(alpha) for alpha in common)
                       for pair in itertools.combinations(all_pairs,2))
            blockers=[selected for selected in itertools.combinations(all_pairs,3)
                      if all(not set(selected).isdisjoint(alpha) for alpha in common)]
            assert blockers
            for selected in blockers:
                degree=[sum(v in e for e in selected) for v in vertices]
                key=','.join(map(str,sorted(degree,reverse=True)))
                blocker_types[key]=blocker_types.get(key,0)+1
            checks+=1
    result=dict(status='All exact checks passed',compatible_ordered_pairs=checks,
                common_matching_count=4,minimum_blocker_size=3,
                minimum_blocker_degree_histogram=blocker_types,
                consequence='Each active six-sector needs at least three inactive contained four-sectors.')
    Path(__file__).with_name('four-seven-prism-cuts.json').write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps(result))


if __name__=='__main__':main()
