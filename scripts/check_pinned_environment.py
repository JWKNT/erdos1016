#!/usr/bin/env python3
"""Read-only dependency preflight. Never downloads or updates dependencies."""
from __future__ import annotations

import hashlib
import json
from pathlib import Path
import re
import shutil
import subprocess
import sys

ROOT = Path(__file__).resolve().parents[1]


def main() -> int:
    errors: list[str] = []
    toolchain = (ROOT / "lean-toolchain").read_text().strip()
    manifest_path = ROOT / "lake-manifest.json"
    if not manifest_path.exists():
        print("Missing lake-manifest.json; pinned dependencies must be restored before building.", file=sys.stderr)
        return 1
    manifest = json.loads(manifest_path.read_text())
    config = (ROOT / "lakefile.lean").read_text()
    pin = re.search(r'require\s+mathlib\s+from\s+git\s+"([^"]+)"\s*@\s*"([^"]+)"', config)
    mathlib = [item for item in manifest["packages"] if item["name"] == "mathlib"]
    if not pin or len(mathlib) != 1 or (mathlib[0]["url"], mathlib[0]["rev"]) != pin.groups():
        errors.append("lakefile.lean mathlib pin does not match lake-manifest.json")
    for command in ("elan", "lake", "git"):
        if shutil.which(command) is None:
            errors.append(f"{command} is not installed")
    if shutil.which("elan"):
        installed = subprocess.run(["elan", "toolchain", "list"], capture_output=True, text=True, check=False)
        if installed.returncode or toolchain not in {line.split()[0] for line in installed.stdout.splitlines() if line}:
            errors.append(f"Pinned toolchain {toolchain} is not installed; no download was attempted")
    packages = []
    if shutil.which("git"):
        for item in manifest["packages"]:
            path = ROOT / manifest.get("packagesDir", ".lake/packages") / item["name"]
            if item["type"] != "git":
                errors.append(f"Cannot verify non-git dependency {item['name']}")
                continue
            if not path.is_dir():
                errors.append(f"Missing pinned dependency {item['name']}; no download was attempted")
                continue
            head = subprocess.run(["git", "-C", str(path), "rev-parse", "HEAD"],
                                  capture_output=True, text=True, check=False)
            dirty = subprocess.run(["git", "-C", str(path), "status", "--porcelain", "--untracked-files=no"],
                                   capture_output=True, text=True, check=False)
            matches = head.returncode == 0 and head.stdout.strip() == item["rev"]
            clean = dirty.returncode == 0 and not dirty.stdout.strip()
            packages.append({"name": item["name"], "pinned_revision": item["rev"],
                             "head_matches": matches, "tracked_files_clean": clean})
            if not matches:
                errors.append(f"{item['name']}: checkout does not match pinned revision {item['rev']}")
            if not clean:
                errors.append(f"{item['name']}: tracked dependency files have changes or cannot be checked")
    print(json.dumps({"passed": not errors, "toolchain": toolchain,
                      "manifest_sha256": hashlib.sha256(manifest_path.read_bytes()).hexdigest(),
                      "network_actions": [], "packages": packages, "errors": errors}, indent=2))
    return 0 if not errors else 1


if __name__ == "__main__":
    raise SystemExit(main())
