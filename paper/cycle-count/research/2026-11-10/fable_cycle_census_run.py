"""Run the cycle census of connected cubic graphs in parallel (Fable 5.2).

For each even order n in the given range, the script splits the generation of
nauty's geng into `jobs` parts (geng's res/mod argument), pipes each part into
the compiled census program, and merges the JSON summaries.

  python3 fable_cycle_census_run.py --geng /path/to/geng --census /path/to/fable_cycle_census \
          --orders 4 6 8 10 12 14 16 18 20 22 --jobs 10 --out fable-cycle-census-results.json

Build the census program first:  cc -O2 -o fable_cycle_census fable_cycle_census.c
The geng binary used for the recorded results is nauty 2.8.9, built by Astra.
Extra geng flags go in --flags, written with an equals sign, for example --flags=-tf
(triangle-free and square-free, that is, girth at least five).
"""
import argparse
import json
import subprocess
import time


def merge(parts):
    parts = [p for p in parts if p["graphs"] > 0]
    out = {"n": parts[0]["n"], "rank": parts[0]["rank"],
           "graphs": sum(p["graphs"] for p in parts)}
    out["max_cycles"] = max(p["max_cycles"] for p in parts)
    out["extremal"] = [e for p in parts if p["max_cycles"] == out["max_cycles"]
                       for e in p["extremal"]]
    girths = sorted({g for p in parts for g in p["by_girth"]}, key=int)
    out["by_girth"] = {
        g: {"graphs": sum(p["by_girth"].get(g, {"graphs": 0})["graphs"] for p in parts),
            "max_cycles": max(p["by_girth"][g]["max_cycles"] for p in parts if g in p["by_girth"])}
        for g in girths}
    best = max(parts, key=lambda p: p["max_min_edge"])
    for key in ("max_min_edge", "max_min_edge_cycles", "max_min_edge_g6"):
        out[key] = best[key]
    low = min(parts, key=lambda p: p["min_gap"])
    out["min_gap"], out["min_gap_g6"] = low["min_gap"], low["min_gap_g6"]
    out["edge_half_violations"] = [g for p in parts for g in p["edge_half_violations"]]
    out["vertex_half_violation_count"] = sum(p.get("vertex_half_violation_count", 0) for p in parts)
    out["vertex_half_violations"] = [g for p in parts for g in p.get("vertex_half_violations", [])][:64]
    return out


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--geng", required=True)
    ap.add_argument("--census", required=True)
    ap.add_argument("--orders", type=int, nargs="+", required=True)
    ap.add_argument("--jobs", type=int, default=8)
    ap.add_argument("--out", required=True)
    ap.add_argument("--flags", default="")
    args = ap.parse_args()
    results = {}
    for n in args.orders:
        start = time.time()
        jobs = args.jobs if n >= 18 else 1
        procs = []
        for res in range(jobs):
            cmd = [args.geng, "-c", "-d3", "-D3", "-q"] + args.flags.split() + [str(n)]
            if jobs > 1:
                cmd.append(f"{res}/{jobs}")
            gen = subprocess.Popen(cmd, stdout=subprocess.PIPE)
            cen = subprocess.Popen([args.census], stdin=gen.stdout, stdout=subprocess.PIPE)
            gen.stdout.close()
            procs.append((gen, cen))
        parts = []
        for gen, cen in procs:
            text = cen.communicate()[0].decode()
            assert gen.wait() == 0 and cen.returncode == 0
            parts.append(json.loads(text))
        merged = merge(parts)
        merged["seconds"] = round(time.time() - start, 1)
        merged["geng_flags"] = "-c -d3 -D3 " + args.flags
        results[str(n)] = merged
        print(n, merged["graphs"], merged["max_cycles"], merged["by_girth"],
              "max min edge", merged["max_min_edge"], "violations", merged["edge_half_violations"],
              "vertex violations", merged["vertex_half_violation_count"],
              "gap", merged["min_gap"], f"{merged['seconds']} s", flush=True)
        with open(args.out, "w") as fh:
            json.dump(results, fh, indent=1)


if __name__ == "__main__":
    main()
