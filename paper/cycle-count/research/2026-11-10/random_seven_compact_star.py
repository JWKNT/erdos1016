"""Exploratory compact Boolean seven-cut relaxation; no solver claim is a proof."""
import argparse
import itertools
import json
import time
from pathlib import Path


def build():
    import numpy as np
    from scipy.sparse import coo_matrix
    here = Path(__file__).parent
    table = json.loads((here / "root-exact-star-cover-table.json").read_text())
    costs = table["minimum_mass_times_two"]
    local_edges = [tuple(e) for e in table["edge_order"]]
    max_loss = max(costs[mask] - costs[mask ^ (1 << e)]
                   for mask in range(1024) for e in range(10)
                   if mask >> e & 1)
    assert max_loss == 8
    ports = tuple(range(7))
    fours = list(itertools.combinations(ports, 4))
    sixes = list(itertools.combinations(ports, 6))
    slots = []
    for S in fours:
        a, b, c, d = S
        slots.extend([(S, ((a, b), (c, d))),
                      (S, ((a, c), (b, d))),
                      (S, ((a, d), (b, c)))])
    ti = {slot: i for i, slot in enumerate(slots)}
    z4 = {S: len(ti) + i for i, S in enumerate(fours)}
    z6 = {S: len(ti) + len(z4) + i for i, S in enumerate(sixes)}
    n = len(ti) + len(z4) + len(z6)
    ii, jj, vv, lower, upper, labels = [], [], [], [], [], []

    def add(row, lo=-np.inf, hi=np.inf, label=None):
        j = len(lower)
        for i, v in row.items():
            if v:
                ii.append(j)
                jj.append(i)
                vv.append(v)
        lower.append(lo)
        upper.append(hi)
        labels.append(label)

    for S in fours:
        row = {ti[slot]: 1 for slot in slots if slot[0] == S}
        row[z4[S]] = -2
        add(row, 0, 0, ("sector", S))
    add({i: 1 for i in list(z4.values()) + list(z6.values())},
        32, 32, ("critical",))
    for S in sixes:
        row = {z4[Q]: 1 for Q in fours if set(Q) <= set(S)}
        row[z6[S]] = 3
        add(row, hi=15, label=("prism", S))
        for left in itertools.combinations(S, 3):
            if S[0] not in left:
                continue
            right = [v for v in S if v not in left]
            row = {}
            for a in left:
                for b in right:
                    Q = tuple(v for v in S if v not in (a, b))
                    row[z4[Q]] = 1
            row[z6[S]] = 1
            add(row, hi=9, label=("balanced_prism", S, left))
    for e in itertools.combinations(ports, 2):
        remaining = [v for v in ports if v not in e]
        local_slots = []
        for a, b in local_edges:
            f = (remaining[a], remaining[b])
            S = tuple(sorted(e + f))
            pairing = tuple(sorted((e, f)))
            local_slots.append((ti[S, pairing], z4[S]))
        for mask, cost in enumerate(costs):
            if cost == 0:
                continue
            row = {}
            size = mask.bit_count()
            for i, (it, iz) in enumerate(local_slots):
                if mask >> i & 1:
                    row[it] = row.get(it, 0) + 2
                    row[iz] = row.get(iz, 0) - 8
            add(row, lo=cost - 8 * size, label=("star", e, mask))
    A = coo_matrix((vv, (ii, jj)), shape=(len(lower), n)).tocsc()
    return A, np.array(lower), np.array(upper), slots, z4, z6, labels, max_loss


def main():
    import numpy as np
    from scipy.optimize import Bounds, LinearConstraint, milp
    ap = argparse.ArgumentParser()
    ap.add_argument("--six-active", type=int, required=True)
    ap.add_argument("--seconds", type=int, default=60)
    args = ap.parse_args()
    A, lower, upper, slots, z4, z6, labels, max_loss = build()
    n = A.shape[1]
    lb, ub = np.zeros(n), np.ones(n)
    for i, (S, j) in enumerate(z6.items()):
        lb[j] = ub[j] = int(i < args.six_active)
    integrality = np.zeros(n)
    integrality[len(slots):] = 1
    started = time.time()
    result = milp(np.zeros(n), integrality=integrality,
                  bounds=Bounds(lb, ub),
                  constraints=LinearConstraint(A, lower, upper),
                  options={"time_limit": args.seconds, "disp": False})
    out = {"six_active": args.six_active, "status": int(result.status),
           "message": result.message, "seconds": time.time() - started,
           "variables": n, "constraints": A.shape[0],
           "max_deletion_cost_times_two": max_loss,
           "scope": "Numerical relaxation only; no graph realization or exact infeasibility proof"}
    if result.x is not None:
        x = result.x
        out["missing_four_sectors"] = [S for S, j in z4.items() if x[j] < .5]
        out["active_six_sectors"] = [S for S, j in z6.items() if x[j] > .5]
        out["nonzero_slots"] = [{"sector": S, "pairing": pairing, "value": float(x[j])}
                                for j, (S, pairing) in enumerate(slots) if x[j] > 1e-8]
        ax = A @ x
        out["max_constraint_violation"] = max(float(np.max(lower - ax)),
                                              float(np.max(ax - upper)), 0.)
    path = Path(__file__).with_name(f"random-seven-compact-star-m{args.six_active}.json")
    path.write_text(json.dumps(out, indent=2) + "\n")
    print(json.dumps({k: v for k, v in out.items() if k != "nonzero_slots"}))


if __name__ == "__main__":
    main()
