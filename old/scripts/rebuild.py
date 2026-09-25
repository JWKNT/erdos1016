#!/usr/bin/env python3
"""Plan or rebuild the proof with bounded parallelism on Lean 4.19 Lake.

By default this writes a plan only. Use --run to execute it, and --fresh to
move the root package's previous .lake/build aside before rebuilding. Pinned
dependency caches must already be current; they are checked without building.
"""
from __future__ import annotations

import argparse
from concurrent.futures import FIRST_COMPLETED, ThreadPoolExecutor, wait
from datetime import datetime, timezone
import json
import os
from pathlib import Path
import subprocess
from typing import Callable

from project_inventory import ROOT, closure, inventory


def build_dag(order: list[str], dependencies: dict[str, set[str]], jobs: int,
              build: Callable[[str], int], completed: Callable[[str, int], None]) -> bool:
    """Build ready modules only; after a failure, finish running jobs and stop.

    Dependencies outside ``order`` must have passed the cache preflight. Each
    local dependency is completed before Lake sees an importing module, so
    Lake cannot create a second layer of local compilation parallelism.
    """
    if jobs < 1:
        raise ValueError("jobs must be positive")
    pending = list(order)
    done: set[str] = set()
    failed = False
    with ThreadPoolExecutor(max_workers=jobs) as executor:
        running = {}
        while pending or running:
            if not failed:
                ready = [name for name in pending if dependencies[name] <= done]
                for name in ready[:jobs - len(running)]:
                    pending.remove(name)
                    running[executor.submit(build, name)] = name
            if not running:
                if failed:
                    break
                raise ValueError("local dependency graph contains a cycle or a missing dependency")
            finished, _ = wait(running, return_when=FIRST_COMPLETED)
            for future in finished:
                name = running.pop(future)
                code = future.result()
                completed(name, code)
                if code:
                    failed = True
                else:
                    done.add(name)
    return not failed


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--root", type=Path, default=ROOT)
    parser.add_argument("--entry", action="append", dest="entries",
                        help="entry module (repeatable); default: Erdos1016")
    parser.add_argument("--all", action="store_true", help="include all current library sources")
    parser.add_argument("--jobs", type=int, default=2, help="maximum simultaneous Lean builds (default: 2)")
    parser.add_argument("--run", action="store_true", help="execute the plan")
    parser.add_argument("--fresh", action="store_true", help="move root .lake/build aside before building")
    parser.add_argument("--output", type=Path, help="logs and status directory; default: .verification/build")
    args = parser.parse_args()
    if args.jobs < 1:
        parser.error("--jobs must be positive")
    root = args.root.resolve()
    output = (args.output or root / ".verification/build").resolve()
    report = inventory(root)
    if not report["all_sources_structural_checks_passed"]:
        raise SystemExit("Source inventory has errors; run the source audit before rebuilding.")
    modules = report["modules"]
    graph = {name: data["imports"] for name, data in modules.items()}
    entries = args.entries or ["Erdos1016"]
    for name in entries:
        if name not in modules:
            raise SystemExit(f"Entry module is missing: {name}")
    keep = set(modules) if args.all else set().union(*(closure(graph, name) for name in entries))
    order = [name for name in report["all_modules_topological_order"] if name in keep]
    external = sorted({dep for name in keep for dep in graph[name] if dep not in modules})
    dependencies = {name: set(graph[name]) & keep for name in keep}
    plan = {
        "entries": entries, "all_sources": args.all, "fresh": args.fresh, "jobs": args.jobs,
        "source_set_sha256": report["source_set_sha256"], "local_module_count": len(order),
        "local_lines": sum(modules[name]["lines"] for name in keep),
        "external_imports": external, "topological_order": order,
        "state": "planned", "completed": [], "failures": [],
    }
    output.mkdir(parents=True, exist_ok=True)
    status = output / "status.json"

    def save() -> None:
        status.write_text(json.dumps(plan, indent=2) + "\n")

    def run(command: list[str], log_name: str) -> int:
        with (output / (log_name + ".log")).open("w") as log:
            try:
                result = subprocess.run(command, cwd=root, env=env, stdout=log,
                                        stderr=subprocess.STDOUT, check=False)
                return result.returncode
            except OSError as error:
                log.write(str(error) + "\n")
                return 127

    save()
    (output / "modules.txt").write_text("\n".join(order) + "\n")
    print(f"{len(order)} local modules, {plan['local_lines']} lines; {len(external)} external roots.")
    print(f"Plan: {status}")
    if not args.run:
        return 0
    env = dict(os.environ, ELAN_TOOLCHAIN=(root / "lean-toolchain").read_text().strip())
    # --no-build exits if anything is missing or stale, without launching any
    # dependency compiler. Do this before moving the current root artifacts.
    import sys
    checks = [([sys.executable, "scripts/check_pinned_environment.py"], "pinned-environment")]
    if external:
        checks.append((["lake", "--no-cache", "--no-build", "build",
                        *["+" + dep + ":olean" for dep in external]], "external-cache-check"))
    for command, name in checks:
        code = run(command, name)
        if code:
            plan.update(state="failed", failed_step=name, returncode=code)
            save()
            print(f"{name} failed; see {output / (name + '.log')}")
            return code
    if args.fresh:
        current = root / ".lake/build"
        if current.exists():
            stamp = datetime.now(timezone.utc).strftime("%Y%m%dT%H%M%S%fZ")
            backup = root / (".lake/build-before-rebuild-" + stamp)
            current.rename(backup)
            plan["previous_build_backup"] = str(backup)
    plan["state"] = "building"
    save()
    indexes = {name: index for index, name in enumerate(order, 1)}

    def build(name: str) -> int:
        print(f"[{indexes[name]}/{len(order)}] {name}", flush=True)
        return run(["lake", "--no-cache", "build", "+" + name + ":olean"],
                   f"{indexes[name]:04d}-{name}")

    def completed(name: str, code: int) -> None:
        plan["failures" if code else "completed"].append(
            {"module": name, "returncode": code} if code else name)
        save()

    success = build_dag(order, dependencies, args.jobs, build, completed)
    after = inventory(root)["source_set_sha256"]
    plan["final_source_set_sha256"] = after
    plan["state"] = "failed" if not success else (
        "passed" if after == plan["source_set_sha256"] else "sources_changed")
    save()
    if plan["state"] != "passed":
        print(f"Rebuild {plan['state']}; inspect {status}.")
        return 1
    print("Bounded rebuild passed. Run the final statement and axiom audit separately.")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
