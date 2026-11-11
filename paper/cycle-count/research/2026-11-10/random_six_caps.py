#!/usr/bin/env python3
"""Exploratory universal six-cut relaxation with star and binary tree caps."""
import json
from explore_six_cut_augmentation import solve

if __name__ == '__main__':
    print(json.dumps(solve(time_limit=300, extra_caps=True), indent=2), flush=True)
